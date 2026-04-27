From Stdlib Require Import PArith NArith Arith.

From compcert.lib Require Import Maps.

From GallinaC.Imp Require Import Uint32 Uintptr.

From GallinaC.Compiler.Common Require Import Ctxt Value Types Expr.
From GallinaC.Compiler.Deep Require Import Cmd Prog.

Fixpoint type_cmd (ty_ctxt: ctxt (type * bool) Empty_set fundef vardef) c: option type :=
  match c with
  | c_ret e => type_expr ty_ctxt e
  | c_bind b_id t_b c_b c_c =>
      match get_pure b_id ty_ctxt with
      | Some (t1, false) =>
          match type_cmd ty_ctxt c_b with
          | Some t_b' =>
              if type_eqb t_b t_b' then
                match type_cmd (set_pure b_id (t_b, true) ty_ctxt) c_c with
                | Some t_c => Some (t_c)
                | None => None
                end
              else
                None
          | None => None
          end
      | _ => None
      end
  | c_if e_i c_t c_e =>
      match type_expr ty_ctxt e_i with
      | Some t_bool =>
          match type_cmd ty_ctxt c_t, type_cmd ty_ctxt c_e with
          | Some t_t, Some t_e =>
              if type_eqb t_t t_e then
                Some t_t
              else
                None
          | _, _ => None
          end
      | _ => None
      end
  | c_while c_cond c_body =>
      match type_cmd ty_ctxt c_cond, type_cmd ty_ctxt c_body with
      | Some t_bool, Some t_unit => Some t_unit
      | _, _ => None
      end
  | c_with_var t_v e_v c_c =>
      match type_expr ty_ctxt e_v, type_cmd ty_ctxt c_c with
      | Some t_v', Some t_c =>
          if type_eqb t_v t_v' then Some t_c else None
      | _, _ => None
      end
  | c_read_var n t => Some t
  | c_write_var n t e =>
      match type_expr ty_ctxt e with
      | Some t' => if type_eqb t t' then Some t_unit else None
      | None => None
      end
  | c_alloc_ptr e_size t t_init =>
      match type_expr ty_ctxt e_size, type_expr ty_ctxt t_init with
      | Some t_ofst, Some t' => if type_eqb t t' then Some t_ptr else None
      | _, _ => None
      end
  | c_read_ptr e_ptr t =>
      match type_expr ty_ctxt e_ptr with
      | Some t_ptr => Some t
      | _ => None
      end
  | c_write_ptr e_ptr t e_val =>
      match type_expr ty_ctxt e_ptr, type_expr ty_ctxt e_val with
      | Some t_ptr, Some t' => if type_eqb t t' then Some t_unit else None
      | _, _ => None
      end
  | c_free_ptr e_ptr =>
      match type_expr ty_ctxt e_ptr with
      | Some t_ptr => Some t_unit
      | _ => None
      end
  | c_shift_fw_ptr e_ptr e_shift | c_shift_bw_ptr e_ptr e_shift =>
                                     match type_expr ty_ctxt e_ptr, type_expr ty_ctxt e_shift with
                                     | Some t_ptr, Some t_ofst => Some t_ptr
                                     | _, _ => None
                                     end
  | c_ptr_eq e_ptr_l e_ptr_r =>
      match type_expr ty_ctxt e_ptr_l, type_expr ty_ctxt e_ptr_r with
      | Some t_ptr, Some t_ptr => Some t_ptr
      | _, _ => None
      end
  | c_app f_id args =>
      match Ctxt.get_global f_id ty_ctxt, ListExt.map_opt (type_expr ty_ctxt) args with
      | Some (AST.Gfun (AST.Internal fn)), Some t_args =>
          if ListExt.forall2 type_eqb t_args (List.map snd fn.(fn_params)) then
            Some fn.(fn_return)
          else
            None
      | _, _ => None
      end
  end.

(* TODO find a way to guarantee have a somewhat usable progress implied by wt_cmd *)
(* TODO previous effort added an output context, but failed at the if *)
Inductive wt_cmd: ctxt (type * bool) Empty_set fundef vardef -> cmd -> type -> Prop :=
| wt_ret : forall ty_ctxt e t
                  (Hwt_expr: wt_expr ty_ctxt.(ctxt_pure) e t),
    wt_cmd ty_ctxt (c_ret e) t
| wt_bind : forall ty_ctxt x c1 c2 t1 t2
                   (Hbind_target_unbound: get_pure x ty_ctxt = Some (t1, false))
                   (Hwt_cmd_bind: wt_cmd ty_ctxt c1 t1)
                   (Hwt_cmd_cont: wt_cmd (set_pure x (t1, true) ty_ctxt) c2 t2),
    wt_cmd ty_ctxt (c_bind x t1 c1 c2) t2
| wt_if : forall ty_ctxt e c1 c2 t,
    wt_expr ty_ctxt.(ctxt_pure) e t_bool -> wt_cmd ty_ctxt c1 t -> wt_cmd ty_ctxt c2 t ->
    wt_cmd ty_ctxt (c_if e c1 c2) t
| wt_while: forall {ty_ctxt c_cond c_body},
    wt_cmd ty_ctxt c_cond t_bool -> wt_cmd ty_ctxt c_cond t_unit -> wt_cmd ty_ctxt (c_while c_cond c_body) t_unit
| wt_with_var: forall {ty_ctxt t_v e_v c_c t_c},
    wt_expr ty_ctxt.(ctxt_pure) e_v t_v -> wt_cmd ty_ctxt c_c t_c -> wt_cmd ty_ctxt (c_with_var t_v e_v c_c) t_c
| wt_read_var : forall ty_ctxt n t,
    ground t ->
    wt_cmd ty_ctxt (c_read_var n t) t
| wt_write_var : forall ty_ctxt n e t,
    wt_expr ty_ctxt.(ctxt_pure) e t -> ground t ->
    wt_cmd ty_ctxt (c_write_var n t e) t_unit
| wt_alloc_ptr : forall ty_ctxt n t e,
    wt_expr ty_ctxt.(ctxt_pure) n t_ofst ->
    wt_expr ty_ctxt.(ctxt_pure) e t -> ground t ->
    wt_cmd ty_ctxt (c_alloc_ptr n t e) t_ptr
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
    (WT_args: List.Forall2 (wt_expr ty_ctxt) args (List.map snd fn.(fn_params))),
    wt_cmd ty_ctxt (c_app f_id args) fn.(fn_return)
.

Lemma type_cmd_spec: forall ty_ctxt c t, wt_cmd ty_ctxt c t <-> type_cmd ty_ctxt c = Some t.
Proof.
  split; [ intros WT | intros EQ ].
  - revert ty_ctxt t WT.
    induction c; cbn; intros; inversion WT; subst; admit.
  - revert ty_ctxt t EQ.
    induction c; cbn; intros; admit.
Admitted.

Definition wt_f_extra (f_extra: f_extra): Prop := True.

Definition wt_p_extra (p_extra: program): Prop := True.

Definition wt_function := wt_function f_extra wt_f_extra wt_cmd.

Definition wt_fundef := wt_fundef f_extra wt_f_extra wt_cmd.

Definition wt_fundef_call := wt_fundef_call cmd f_extra.

Definition wt_globvar := wt_globvar cmd f_extra.

Definition wt_globdef := wt_globdef f_extra wt_f_extra wt_cmd.

Definition wt_program := wt_program wt_f_extra wt_cmd wt_p_extra.
