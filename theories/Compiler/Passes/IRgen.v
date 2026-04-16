From Stdlib Require Import Strings.String PArith Arith NArith Psatz.

From compcert.common Require Import Errors.
From compcert.lib Require Maps.

From GallinaC.Utils Require Import ListExt.

From GallinaC.Imp Require Import Heap Store.

From GallinaC.Compiler.Deep Require Import Cmd Prog.
From GallinaC.Compiler.IR Require Prog Cmd.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Local Notation "'do' 'assertion' A ; B" := (if A then B else assertion_failed)
                                             (at level 200, A at level 100, B at level 200)
    : error_monad_scope.

Local Notation "'do' ' p <- A ; B " := (bind A (fun ' p => B))
                                         (at level 200, p pattern, A at level 100, B at level 200)
    : error_monad_scope.

(* Import Decimal. *)

(* Fixpoint string_of_uint (d: Decimal.uint): String.string := *)
(*   match d with *)
(*   | Nil => "" *)
(*   | D0 d => "0" ++ (string_of_uint d) *)
(*   | D1 d => "1" ++ (string_of_uint d) *)
(*   | D2 d => "2" ++ (string_of_uint d) *)
(*   | D3 d => "3" ++ (string_of_uint d) *)
(*   | D4 d => "4" ++ (string_of_uint d) *)
(*   | D5 d => "5" ++ (string_of_uint d) *)
(*   | D6 d => "6" ++ (string_of_uint d) *)
(*   | D7 d => "7" ++ (string_of_uint d) *)
(*   | D8 d => "8" ++ (string_of_uint d) *)
(*   | D9 d => "9" ++ (string_of_uint d) *)
(*   end. *)

(* Definition string_of_nat (n: nat): String.string := *)
(*   string_of_uint (Nat.to_uint n). *)

(* Definition string_of_pos (p: positive): String.string := *)
(*   string_of_uint (Pos.to_uint p). *)

(* Definition string_of_N (n: N): String.string := *)
(*   string_of_uint (N.to_uint n). *)

(* Definition string_of_type (t: type): String.string := *)
(*   match t with *)
(*   | t_unit => "t_unit" *)
(*   | t_bool => "t_bool" *)
(*   | t_nat => "t_nat" *)
(*   | t_ofst => "t_ofst" *)
(*   | t_ptr => "t_ptr" *)
(*   | t_fun _ _ => "t_fun" *)
(*   end. *)

(* Fixpoint string_of_expr (e: expr): String.string := *)
(*   match e with *)
(*   | e_var id => "e_var " ++ (string_of_pos id) *)
(*   | e_tt => "e_tt" *)
(*   | e_bool true => "e_bool true" *)
(*   | e_bool false => "e_bool false" *)
(*   | e_nat n => "e_nat " ++ (string_of_nat n) *)
(*   | e_ofst o => "e_ofst " ++ (string_of_N o) *)
(*   | e_nullptr => "e_nullptr" *)
(*   | e_neg e => "e_neg (" ++ string_of_expr e ++ ")" *)
(*   | e_plus l r => "e_plus (" ++ string_of_expr l ++ ") (" ++ string_of_expr r ++ ")" *)
(*   | e_nat_eq l r => "e_nat_eq (" ++ string_of_expr l ++ ") (" ++ string_of_expr r ++ ")" *)
(*   end. *)

Record compilenv P S GF GV :=
  mkcompilenv
    {
      next_id: AST.ident;
      uses_malloc: option AST.ident;
      uses_free: option AST.ident;
      cenv_ctxt: ctxt P S GF GV;
    }.
Arguments next_id [P S GF GV].
Arguments uses_malloc [P S GF GV].
Arguments uses_free [P S GF GV].
Arguments cenv_ctxt [P S GF GV].

Definition cenv_add_bind [P S GF GV] b t (cenv: compilenv (P * bool) S GF GV) :=
  {| cenv_ctxt := Ctxt.set_pure b (t, true) cenv.(cenv_ctxt); next_id := cenv.(next_id); uses_malloc := cenv.(uses_malloc); uses_free := cenv.(uses_free); |}.

Definition cenv_push_stack [P GF GV] (cenv: compilenv P unit GF GV) :=
  {|
    cenv_ctxt := {| ctxt_pure := cenv.(cenv_ctxt).(ctxt_pure); ctxt_stack := cenv.(cenv_ctxt).(ctxt_stack) ++ [tt]; ctxt_global := cenv.(cenv_ctxt).(ctxt_global); |};
    next_id := cenv.(next_id);
    uses_malloc := cenv.(uses_malloc);
    uses_free := cenv.(uses_free);
  |}.

Definition cenv_add_fun [P S GF GV] b_f f (cenv: compilenv P S GF GV): compilenv P S GF GV :=
  {|
    cenv_ctxt := {| ctxt_pure := cenv.(cenv_ctxt).(ctxt_pure); ctxt_stack := cenv.(cenv_ctxt).(ctxt_stack); ctxt_global := Globalenvs.Genv.add_global cenv.(cenv_ctxt).(ctxt_global) (b_f, AST.Gfun f) |};
    next_id := cenv.(next_id);
    uses_malloc := cenv.(uses_malloc);
    uses_free := cenv.(uses_free);
  |}.

Definition cenv_get_next_id [P S GF GV] (cenv: compilenv P S GF GV): AST.ident * compilenv P S GF GV :=
  (cenv.(next_id), {| next_id := Pos.succ cenv.(next_id); uses_malloc := cenv.(uses_malloc); uses_free := cenv.(uses_free); cenv_ctxt := cenv.(cenv_ctxt); |}).

Definition cenv_new_temp [P S GF GV] t_temp (cenv: compilenv (P*bool) S GF GV): AST.ident * compilenv (P*bool) S GF GV :=
  let '(id_temp, cenv) := cenv_get_next_id cenv in
  (id_temp, {|
              cenv_ctxt := Ctxt.set_pure id_temp (t_temp, false) cenv.(cenv_ctxt);
              next_id := cenv.(next_id);
              uses_malloc := cenv.(uses_malloc);
              uses_free := cenv.(uses_free);
            |}).

Definition set_malloc [P S GF GV] (cenv: compilenv P S GF GV): compilenv P S GF GV :=
  match cenv.(uses_malloc) with
  | Some id_malloc => cenv
  | None =>
      let (id_malloc, cenv) := cenv_get_next_id cenv in
      {|
        next_id := cenv.(next_id);
        uses_malloc := Some id_malloc;
        uses_free := cenv.(uses_free);
        cenv_ctxt := cenv.(cenv_ctxt);
      |}
  end.

Definition set_free [P S GF GV] (cenv: compilenv P S GF GV): compilenv P S GF GV :=
  match cenv.(uses_free) with
  | Some id_free => cenv
  | None =>
      let (id_free, cenv) := cenv_get_next_id cenv in
      {|
        next_id := cenv.(next_id);
        uses_malloc := cenv.(uses_malloc);
        uses_free := Some id_free;
        cenv_ctxt := cenv.(cenv_ctxt);
      |}
  end.

Definition cmd_compilenv := compilenv (type * bool) unit IR.Prog.fundef vardef.
Definition prog_compilenv := compilenv Empty_set Empty_set IR.Prog.fundef vardef.

Definition mk_cmd_compilenv (cenv: prog_compilenv) (args: list (AST.ident * type)) : cmd_compilenv  :=
  {|
    next_id := cenv.(next_id);
    uses_malloc := cenv.(uses_malloc);
    uses_free := cenv.(uses_free);
    cenv_ctxt := Ctxt.with_pure (Maps.PTree_Properties.of_list (List.map (fun '(id_arg, t_arg) => (id_arg, (t_arg, true))) args))
                   (Ctxt.with_stack [] cenv.(cenv_ctxt));
  |}.

Definition mk_prog_compilenv (cenv: cmd_compilenv) : prog_compilenv :=
  {|
    next_id := cenv.(next_id);
    uses_malloc := cenv.(uses_malloc);
    uses_free := cenv.(uses_free);
    cenv_ctxt := Ctxt.with_pure (Maps.PTree.empty _) (Ctxt.with_stack [] cenv.(cenv_ctxt));
  |}.

Section State.
  Context {St: Store}.
  Context {Hp: Heap}.

  Fixpoint transl_cmd (cenv: cmd_compilenv) (c: cmd) {struct c}: res (IR.Cmd.cmd * type * cmd_compilenv) :=
    match c with
    | c_ret e =>
        match type_expr cenv.(cenv_ctxt) e with
        | Some t => OK (IR.Cmd.c_ret e t, t, cenv)
        | None => Error [MSG "IRGen.transl_cmd: c_ret type error"]
        end
    | c_bind b_id t_b c_b c_c =>
        do ' (tc_b, t_b', cenv) <- transl_cmd cenv c_b;
        do ' (tc_c, t_c, cenv) <- transl_cmd (cenv_add_bind b_id t_b cenv) c_c;
        OK (IR.Cmd.c_bind b_id t_b tc_b tc_c t_c, t_c, cenv)
    | c_if e_i c_t c_e =>
        do ' (tc_t, t_t, cenv) <- transl_cmd cenv c_t;
        do ' (tc_e, t_e, cenv) <- transl_cmd cenv c_e;
        do assertion type_eqb t_t t_e;
        OK (IR.Cmd.c_if e_i tc_t tc_e t_t, t_t, cenv)
    | c_while c_cond c_body =>
        do ' (tc_cond, t_cond, cenv) <- transl_cmd cenv c_cond;
        do ' (tc_body, t_body, cenv) <- transl_cmd cenv c_body;
        do assertion type_eqb t_cond t_bool;
        do assertion type_eqb t_body t_unit;
        let '(id_cond, cenv) := cenv_get_next_id cenv in
        let '(id_body, cenv) := cenv_get_next_id cenv in
        OK (IR.Cmd.c_while tc_cond id_cond tc_body id_body, t_unit, cenv)
    | c_with_var t_v e_v c_c =>
        let tc_write := IR.Cmd.c_write_var (List.length (ctxt_stack (cenv.(cenv_ctxt)))) t_v e_v in
        let '(id_var, cenv) := cenv_new_temp t_v cenv in
        do ' (tc_c, t, cenv) <- transl_cmd (cenv_add_bind id_var t_v (cenv_push_stack cenv)) c_c;
        OK (IR.Cmd.c_bind id_var t_unit tc_write tc_c t, t, cenv)
    | c_read_var n t =>
        OK (IR.Cmd.c_read_var n t, t, cenv)
    | c_write_var n t e =>
        OK (IR.Cmd.c_write_var n t e, t_unit, cenv)
    | c_alloc_ptr e_size t e_init =>
        let '(id1, cenv) := cenv_get_next_id cenv in
        let '(id2, cenv) := cenv_get_next_id cenv in
        let cenv := set_malloc cenv in
        OK (IR.Cmd.c_alloc_ptr e_size t e_init id1 id2, t_ptr, cenv)
    | c_read_ptr e_ptr t =>
        OK (IR.Cmd.c_read_ptr e_ptr t, t, cenv)
    | c_write_ptr e_ptr t e_val =>
        OK (IR.Cmd.c_write_ptr e_ptr t e_val, t_unit, cenv)
    | c_free_ptr e_ptr =>
        let cenv := set_free cenv in
        OK (IR.Cmd.c_free_ptr e_ptr, t_unit, cenv)
    | c_shift_fw_ptr e_ptr e_shift =>
        OK (IR.Cmd.c_shift_fw_ptr e_ptr e_shift, t_ptr, cenv)
    | c_shift_bw_ptr e_ptr e_shift =>
        OK (IR.Cmd.c_shift_bw_ptr e_ptr e_shift, t_ptr, cenv)
    | c_ptr_eq e_ptr_l e_ptr_r =>
        OK (IR.Cmd.c_ptr_eq e_ptr_l e_ptr_r, t_bool, cenv)
    | c_app id_f args =>
        match Globalenvs.Genv.find_symbol cenv.(cenv_ctxt).(ctxt_global) id_f with
        | Some b =>
            match Globalenvs.Genv.find_funct_ptr cenv.(cenv_ctxt).(ctxt_global) b, ListExt.map_opt (type_expr cenv.(cenv_ctxt)) args with
            | Some (AST.Internal fn), Some t_args =>
                if ListExt.forall2 type_eqb t_args (List.map snd fn.(fn_params)) then
                  OK (IR.Cmd.c_app id_f fn.(fn_return) (List.combine args t_args), fn.(fn_return), cenv)
                else
                  Error ([MSG "Arguments and signature do not match"])
                           (* ::(MSG (string_of_nat (List.length args))) *)
                           (* ::(MSG (string_of_nat (List.length t_args))) *)
                           (* ::(MSG (string_of_nat (List.length fn.(fn_params)))) *)
                           (* ::(List.map (fun '((arg, t_arg), (id_param, t_param)) => MSG (string_of_expr arg ++ " " ++ string_of_type t_arg ++ " " ++ string_of_type t_param)) (List.combine (List.combine args t_args) fn.(fn_params))) )*)
            | _, _ => Error [MSG "A"]
            end
        | None => Error [ MSG "B"]
        end
    end.

  Fixpoint stack_usage (c: cmd): nat :=
    match c with
    | c_ret _
    | c_read_var _ _ | c_write_var _ _ _
    | c_alloc_ptr _ _ _ | c_read_ptr _ _
    | c_write_ptr _ _ _ | c_free_ptr _
    | c_shift_fw_ptr _ _ | c_shift_bw_ptr _ _
    | c_ptr_eq _ _
    | c_app _ _
                       => 0
    | c_bind _ _ c_b c_c =>
        Nat.max (stack_usage c_b) (stack_usage c_c)
    | c_if _ c_then c_else =>
        Nat.max (stack_usage c_then) (stack_usage c_else)
    | c_while c_cond c_body =>
        Nat.max (stack_usage c_cond) (stack_usage c_body)
    | c_with_var _ _ c_c =>
        S (stack_usage c_c)
  end.

  Definition transl_fundef (cenv: prog_compilenv) (fd: fundef) : res (IR.Prog.fundef * prog_compilenv) :=
    match fd with
    | AST.External ef =>
        OK (AST.External ef, cenv)
    | AST.Internal fn =>
        do ' (body, t_body, cenv) <- transl_cmd (mk_cmd_compilenv cenv fn.(fn_params)) fn.(fn_body);
        OK ((AST.Internal
               {|fn_return := fn.(fn_return);
                 fn_params := fn.(fn_params);
                 fn_temps := List.map (fun '(id, (t, _)) => (id, t)) (Maps.PTree.elements cenv.(cenv_ctxt).(ctxt_pure));
                 fn_body := body;
                 fn_extra := {| IR.Prog.fn_stackspace := stack_usage fn.(fn_body); |};
               |}),
            mk_prog_compilenv cenv)
    end.

  Fixpoint transl_globdefs (cenv: prog_compilenv) (gdefs: list (AST.ident * globdef)): res (list (AST.ident * IR.Prog.globdef) * prog_compilenv) :=
    match gdefs with
    | [] =>
        let gdefs := [] in
        let gdefs :=
          match cenv.(uses_malloc) with
          | Some id_malloc => [(id_malloc, AST.Gfun (AST.External AST.EF_malloc))]
          | None => gdefs
          end
        in
        let gdefs :=
          match cenv.(uses_free) with
          | Some id_free => (gdefs ++ [(id_free, AST.Gfun (AST.External AST.EF_free))])%list
          | None => gdefs
          end
        in
        OK(gdefs, cenv)
    | (g_id, AST.Gvar var_info)::gdefs =>
        do ' (gdefs, cenv) <- transl_globdefs cenv gdefs;
        OK((g_id, AST.Gvar var_info)::gdefs, cenv)
    | (g_id, AST.Gfun fd)::gdefs =>
        do ' (tfd, cenv) <- transl_fundef cenv fd;
        let cenv := cenv_add_fun g_id tfd cenv in
        do ' (gdefs, cenv) <- transl_globdefs cenv gdefs;
        OK ((g_id, AST.Gfun tfd)::gdefs, cenv)
    end.

  Definition transl_program (p: program) : res (IR.Prog.program) :=
    do ' (tgl', cenv) <- transl_globdefs {| next_id := p.(prog_extra).(prog_next_id); uses_malloc := None; uses_free := None; cenv_ctxt := ctxt_emp _ _ _ _ (List.map fst p.(prog_defs)) |} p.(prog_defs);
    OK {| prog_defs := tgl'; prog_public := p.(prog_public); prog_main := p.(prog_main); prog_extra := {| Prog.prog_malloc := None; Prog.prog_free := None; |} |}.

End State.
