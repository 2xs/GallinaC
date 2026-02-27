From Stdlib Require Import PArith NArith Arith.

From compcert.lib Require Import Maps.

From Utils Require Import ListExt.

From Imp Require Import Uint32 Uintptr.

From Compiler.Common Require Import Ctxt Value Types Expr.
From Compiler.IR Require Import Cmd Prog.

(* TODO find a way to guarantee have a somewhat usable progress implied by wt_cmd *)
(* TODO previous effort added an output context, but failed at the if *)
Inductive wt_cmd: ctxt (type * bool) Empty_set fundef vardef -> cmd -> type -> Prop :=
| wt_ret : forall ty_ctxt e t
                  (Hwt_expr: wt_expr ty_ctxt.(ctxt_pure) e t),
    wt_cmd ty_ctxt (c_ret e t) t
| wt_bind : forall {ty_ctxt id_b t_b c_b c_c t_c}
                   (Hbind_target_unbound: get_pure id_b ty_ctxt = Some (t_b, false))
                   (Hwt_cmd_bind: wt_cmd ty_ctxt c_b t_b)
                   (Hwt_cmd_cont: wt_cmd (set_pure id_b (t_b, true) ty_ctxt) c_c t_c),
    wt_cmd ty_ctxt (c_bind id_b t_b c_b c_c t_c) t_c
| wt_if : forall ty_ctxt e c1 c2 t,
    wt_expr ty_ctxt.(ctxt_pure) e t_bool -> wt_cmd ty_ctxt c1 t -> wt_cmd ty_ctxt c2 t ->
    wt_cmd ty_ctxt (c_if e c1 c2 t) t
| wt_while: forall {ty_ctxt c_cond c_body id_cond id_body},
    wt_cmd ty_ctxt c_cond t_bool -> wt_cmd ty_ctxt c_cond t_unit -> wt_cmd ty_ctxt (c_while c_cond id_cond c_body id_body) t_unit
| wt_read_var : forall ty_ctxt n t,
    ground t ->
    wt_cmd ty_ctxt (c_read_var n t) t
| wt_write_var : forall ty_ctxt n e t,
    wt_expr ty_ctxt.(ctxt_pure) e t -> ground t ->
    wt_cmd ty_ctxt (c_write_var n t e) t_unit
| wt_alloc_ptr : forall {ty_ctxt n t e id_ptr id_init},
    wt_expr ty_ctxt.(ctxt_pure) e t -> ground t ->
    wt_cmd ty_ctxt (c_alloc_ptr n t e id_ptr id_init) t_ptr
| wt_read_ptr : forall ty_ctxt t p,
    wt_expr ty_ctxt.(ctxt_pure) p t_ptr -> ground t ->
    wt_cmd ty_ctxt (c_read_ptr p t) t
| wt_write_ptr : forall ty_ctxt p t e,
    wt_expr ty_ctxt.(ctxt_pure) p t_ptr -> wt_expr ty_ctxt e t ->
    ground t ->
    wt_cmd ty_ctxt (c_write_ptr p t e) t_unit
| wt_free_ptr : forall ty_ctxt p,
    wt_expr ty_ctxt.(ctxt_pure) p t_ptr ->
    wt_cmd ty_ctxt (c_free_ptr p) t_unit
| wt_shift_fw_ptr: forall ty_ctxt p n,
    wt_expr ty_ctxt.(ctxt_pure) p t_ptr -> wt_expr ty_ctxt n t_ofst ->
    wt_cmd ty_ctxt (c_shift_fw_ptr p n) t_ptr
| wt_shift_bw_ptr: forall {ty_ctxt p n},
    wt_expr ty_ctxt.(ctxt_pure) p t_ptr -> wt_expr ty_ctxt n t_ofst ->
    wt_cmd ty_ctxt (c_shift_bw_ptr p n) t_ptr
| wt_ptr_eq: forall ty_ctxt p1 p2,
    wt_expr ty_ctxt.(ctxt_pure) p1 t_ptr -> wt_expr ty_ctxt p2 t_ptr ->
    wt_cmd ty_ctxt (c_ptr_eq p1 p2) t_bool
| wt_app : forall
    {ty_ctxt f_id args fn}
    (Hfind_fn: Ctxt.get_global f_id ty_ctxt = Some (AST.Gfun (AST.Internal fn)))
    (Hreturn_ground: ground fn.(fn_return))
    (Et_args: List.map snd fn.(fn_params) = List.map snd args)
    (WT_args: List.Forall2 (wt_expr ty_ctxt) (List.map fst args) (List.map snd args)),
    wt_cmd ty_ctxt (c_app f_id fn.(fn_return) args) fn.(fn_return)
.

Definition wt_f_extra (f_extra: f_extra): Prop := f_extra.(fn_stackspace) <= Unsigned.max_unsigned.

Record wt_p_extra (p: program): Prop :=
  {
    wt_prog_malloc: forall id, p.(prog_extra).(prog_malloc) = Some id -> In (id, AST.Gfun (AST.External AST.EF_malloc)) p.(prog_defs);
    wt_prog_free: forall id, p.(prog_extra).(prog_free) = Some id -> In (id, AST.Gfun (AST.External AST.EF_malloc)) p.(prog_defs);
  }.

Definition wt_function := wt_function f_extra wt_f_extra wt_cmd.

Definition wt_fundef := wt_fundef f_extra wt_f_extra wt_cmd.

Definition wt_fundef_call := wt_fundef_call cmd f_extra.

Definition wt_globvar := wt_globvar cmd f_extra.

Definition wt_globdef := wt_globdef f_extra wt_f_extra wt_cmd.

Definition wt_program := wt_program wt_f_extra wt_cmd wt_p_extra.
