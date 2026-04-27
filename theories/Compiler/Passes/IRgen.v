From Stdlib Require Import Strings.String PArith Arith NArith ZArith Psatz.

From compcert.common Require Import Errors.
From compcert.backend Require Import SplitLong(sig_f_l, sig_l_f, sig_l_s, sig_ll_l, sig_li_l).
From compcert.lib Require Maps.

From GallinaC.Utils Require Import ListExt.

From GallinaC.Imp Require Import Heap Store.

From GallinaC.Compiler.Deep Require Import Cmd Prog.
From GallinaC.Compiler.IR Require Prog Cmd.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Local Notation "'do' 'assert' A ; B" := (if A then B else assertion_failed)
                                             (at level 200, A at level 100, B at level 200)
    : error_monad_scope.

Local Notation "'do' ' p <- A ; B " := (bind A (fun ' p => B))
                                         (at level 200, p pattern, A at level 100, B at level 200)
    : error_monad_scope.

Record compilenv P S GF GV T :=
  mkcompilenv
    {
      next_id: AST.ident;
      new_temps: list T;
      cenv_ctxt: ctxt P S GF GV;
    }.
Arguments next_id [P S GF GV T].
Arguments cenv_ctxt [P S GF GV T].
Arguments new_temps [P S GF GV T].

Definition cenv_add_bind [P S GF GV T] b t (cenv: compilenv (P * bool) S GF GV T) :=
  {| cenv_ctxt := Ctxt.set_pure b (t, true) cenv.(cenv_ctxt); next_id := cenv.(next_id); new_temps := cenv.(new_temps); |}.

Definition cenv_push_stack [P GF GV T] (cenv: compilenv P unit GF GV T) :=
  {|
    cenv_ctxt := {| ctxt_pure := cenv.(cenv_ctxt).(ctxt_pure); ctxt_stack := cenv.(cenv_ctxt).(ctxt_stack) ++ [tt]; ctxt_global := cenv.(cenv_ctxt).(ctxt_global); |};
    next_id := cenv.(next_id);
    new_temps := cenv.(new_temps);
  |}.

Definition cenv_add_fun [P S GF GV T] b_f f (cenv: compilenv P S GF GV T): compilenv P S GF GV T :=
  {|
    cenv_ctxt := {| ctxt_pure := cenv.(cenv_ctxt).(ctxt_pure); ctxt_stack := cenv.(cenv_ctxt).(ctxt_stack); ctxt_global := Globalenvs.Genv.add_global cenv.(cenv_ctxt).(ctxt_global) (b_f, AST.Gfun f) |};
    next_id := cenv.(next_id);
    new_temps := cenv.(new_temps);
  |}.

Definition cenv_get_next_id [P S GF GV T] (cenv: compilenv P S GF GV T): AST.ident * compilenv P S GF GV T :=
  (cenv.(next_id), {| next_id := Pos.succ cenv.(next_id); new_temps := cenv.(new_temps); cenv_ctxt := cenv.(cenv_ctxt); |}).

Definition cenv_new_temp [P S GF GV] t_temp (cenv: compilenv (P*bool) S GF GV (AST.ident * P)): AST.ident * compilenv (P*bool) S GF GV (AST.ident * P) :=
  let '(id_temp, cenv) := cenv_get_next_id cenv in
  (id_temp, {|
              cenv_ctxt := Ctxt.set_pure id_temp (t_temp, false) cenv.(cenv_ctxt);
              next_id := cenv.(next_id);
              new_temps := (id_temp, t_temp)::cenv.(new_temps);
            |}).

Definition cmd_compilenv := compilenv (type * bool) unit IR.Prog.fundef vardef (AST.ident * type).
Definition prog_compilenv := compilenv Empty_set Empty_set IR.Prog.fundef vardef Empty_set.

Definition mk_cmd_compilenv (cenv: prog_compilenv) (args: list (AST.ident * type)) : cmd_compilenv  :=
  {|
    next_id := cenv.(next_id);
    new_temps := [];
    cenv_ctxt := Ctxt.with_pure (Maps.PTree_Properties.of_list (List.map (fun '(id_arg, t_arg) => (id_arg, (t_arg, true))) args))
                   (Ctxt.with_stack [] cenv.(cenv_ctxt));
  |}.

Definition mk_prog_compilenv (cenv: cmd_compilenv) : prog_compilenv :=
  {|
    next_id := cenv.(next_id);
    new_temps := [];
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
        do assert type_eqb t_t t_e;
        OK (IR.Cmd.c_if e_i tc_t tc_e t_t, t_t, cenv)

    | c_while c_cond c_body =>
        do ' (tc_cond, t_cond, cenv) <- transl_cmd cenv c_cond;
        do ' (tc_body, t_body, cenv) <- transl_cmd cenv c_body;
        do assert type_eqb t_cond t_bool;
        do assert type_eqb t_body t_unit;
        let '(id_cond, cenv) := cenv_new_temp t_bool cenv in
        let '(id_body, cenv) := cenv_new_temp t_unit cenv in
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
        let '(id1, cenv) := cenv_new_temp t_ptr cenv in
        let '(id2, cenv) := cenv_new_temp t cenv in
        OK (IR.Cmd.c_alloc_ptr e_size t e_init id1 id2, t_ptr, cenv)
    | c_read_ptr e_ptr t =>
        OK (IR.Cmd.c_read_ptr e_ptr t, t, cenv)
    | c_write_ptr e_ptr t e_val =>
        OK (IR.Cmd.c_write_ptr e_ptr t e_val, t_unit, cenv)
    | c_free_ptr e_ptr =>
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
            | Some (AST.External (AST.EF_external nm {| AST.sig_args := [xt_arg]; AST.sig_res := AST.Xvoid; AST.sig_cc := cc |})), Some [t_arg] =>
                if ssrfun.Option.apply (type_eqb t_arg) false (CCInj.xtype_to_type xt_arg) then
                  OK (IR.Cmd.c_app id_f t_unit (List.combine args [t_arg]), t_unit, cenv)
                else
                  Error [MSG "Unsound external function call"]
            | _, _ => Error [MSG "Unsupported function call"]
            end
        | None => Error [ MSG "B"]
        end
    end.

  Fixpoint stack_usage (c: cmd): Z :=
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
        Z.max (stack_usage c_b) (stack_usage c_c)
    | c_if _ c_then c_else =>
        Z.max (stack_usage c_then) (stack_usage c_else)
    | c_while c_cond c_body =>
        Z.max (stack_usage c_cond) (stack_usage c_body)
    | c_with_var _ _ c_c =>
        Z.succ (stack_usage c_c)
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
                 fn_temps := List.rev_append fn.(fn_temps) cenv.(new_temps);
                 fn_body := body;
                 fn_extra := {| IR.Prog.fn_stackspace := stack_usage fn.(fn_body); |};
               |}),
            mk_prog_compilenv cenv)
    end.

  Fixpoint transl_globdefs (cenv: prog_compilenv) (gdefs: list (AST.ident * globdef)) (acc: list (AST.ident * IR.Prog.globdef)): res (list (AST.ident * IR.Prog.globdef) * prog_compilenv) :=
    match gdefs with
    | [] =>
        let '(cenv, gdefs) :=
          List.fold_left
            (fun '(cenv, gdefs) '(name, sig) =>
               let '(next_id, cenv) := cenv_get_next_id cenv in
               (cenv, (next_id, AST.Gfun (AST.External (AST.EF_runtime name sig)))::gdefs))
            [
              ("__compcert_i64_dtos", sig_f_l);
              ("__compcert_i64_dtou", sig_f_l);
              ("__compcert_i64_stod", sig_l_f);
              ("__compcert_i64_utod", sig_l_f);
              ("__compcert_i64_stof", sig_l_s);
              ("__compcert_i64_utof", sig_l_s);
              ("__compcert_i64_sdiv", sig_ll_l);
              ("__compcert_i64_udiv", sig_ll_l);
              ("__compcert_i64_smod", sig_ll_l);
              ("__compcert_i64_umod", sig_ll_l);
              ("__compcert_i64_shl", sig_li_l);
              ("__compcert_i64_shr", sig_li_l);
              ("__compcert_i64_sar", sig_li_l);
              ("__compcert_i64_umulh", sig_ll_l);
              ("__compcert_i64_smulh", sig_ll_l)
            ]
            (cenv, [])
        in

        OK(List.rev_append acc gdefs, cenv)
    | (g_id, AST.Gvar var_info)::gdefs =>
        transl_globdefs cenv gdefs ((g_id, AST.Gvar var_info)::acc)
    | (g_id, AST.Gfun fd)::gdefs =>
        do ' (tfd, cenv) <- transl_fundef cenv fd;
        let cenv := cenv_add_fun g_id tfd cenv in
        transl_globdefs cenv gdefs ((g_id, AST.Gfun tfd)::acc)
    end.

  Definition transl_program (p: program) : res (IR.Prog.program) :=
    do (tgl', cenv) <-
         transl_globdefs
           {|
             next_id := p.(prog_extra).(prog_next_id);
             new_temps := [];
             cenv_ctxt := ctxt_emp _ _ _ _ (List.map fst p.(prog_defs))
           |}
           p.(prog_defs) [];
    OK
      {|
        prog_defs := tgl';
        prog_public := p.(prog_public);
        prog_main := p.(prog_main);
        prog_extra :=
          {|
            Prog.prog_malloc := Some 1%positive;
            Prog.prog_free := Some 2%positive;
          |}
      |}.

End State.
