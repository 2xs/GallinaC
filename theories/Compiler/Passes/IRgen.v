(*
GallinaC: Unifying Verification and Certified Compilation of System Programs in Rocq
Copyright (C) 2023-2026 GallinaC contributors (see CONTRIBUTORS.md)

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with this program. If not, see <https://www.gnu.org/licenses/>.
*)

From Stdlib Require Import Strings.String PArith Arith NArith ZArith Psatz Bool.

From compcert.common Require Import Errors.
From compcert.lib Require Maps.

From GallinaC.Utils Require Import ListExt CompCertExt Algebra.

From GallinaC.Compiler.IR Require Typing.
From GallinaC.Compiler.IR Require Import Prog Cmd.
From GallinaC.Compiler.Deep Require Import Cmd Prog.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Local Notation "'do' 'assert' A ; B" := (if A then B else assertion_failed)
                                             (at level 200, A at level 100, B at level 200)
    : error_monad_scope.

Local Notation "'do' ' p <- A ; B " := (bind A (fun ' p => B))
                                         (at level 200, p pattern, A at level 100, B at level 200)
    : error_monad_scope.

Record compilenv Pu Iu Sa GF GV T :=
  mkcompilenv
    {
      next_id: AST.ident;
      new_temps: list T;
      new_internals: list T;
      cenv_ctxt: ctxt Pu Iu Sa GF GV;
    }.
Arguments next_id [Pu Iu Sa GF GV T].
Arguments cenv_ctxt [Pu Iu Sa GF GV T].
Arguments new_temps [Pu Iu Sa GF GV T].
Arguments new_internals [Pu Iu Sa GF GV T].

Definition cenv_add_bind [Pu Iu Sa GF GV T] b t (cenv: compilenv (Pu * bool) Iu Sa GF GV T) :=
  {| cenv_ctxt := Ctxt.set_pure b (t, true) cenv.(cenv_ctxt); next_id := cenv.(next_id); new_temps := cenv.(new_temps); new_internals := cenv.(new_internals); |}.

Definition cenv_push_stack [Pu Iu GF GV T] (cenv: compilenv Pu Iu unit GF GV T) :=
  {|
    cenv_ctxt := {| ctxt_pure := cenv.(cenv_ctxt).(ctxt_pure); ctxt_internal := cenv.(cenv_ctxt).(ctxt_internal); ctxt_stack := cenv.(cenv_ctxt).(ctxt_stack) ++ [tt]; ctxt_global := cenv.(cenv_ctxt).(ctxt_global); |};
    next_id := cenv.(next_id);
    new_temps := cenv.(new_temps);
    new_internals := cenv.(new_internals);
  |}.

Definition cenv_pop_stack [Pu Iu GF GV T] (cenv: compilenv Pu Iu unit GF GV T) :=
  {|
    cenv_ctxt := {| ctxt_pure := cenv.(cenv_ctxt).(ctxt_pure); ctxt_internal := cenv.(cenv_ctxt).(ctxt_internal); ctxt_stack := List.removelast cenv.(cenv_ctxt).(ctxt_stack); ctxt_global := cenv.(cenv_ctxt).(ctxt_global); |};
    next_id := cenv.(next_id);
    new_temps := cenv.(new_temps);
    new_internals := cenv.(new_internals);
  |}.

Definition cenv_add_fun [Pu Iu Sa GF GV T] b_f f (cenv: compilenv Pu Iu Sa GF GV T): compilenv Pu Iu Sa GF GV T :=
  {|
    cenv_ctxt := {| ctxt_pure := cenv.(cenv_ctxt).(ctxt_pure); ctxt_internal := cenv.(cenv_ctxt).(ctxt_internal); ctxt_stack := cenv.(cenv_ctxt).(ctxt_stack); ctxt_global := Globalenvs.Genv.add_global cenv.(cenv_ctxt).(ctxt_global) (b_f, AST.Gfun f) |};
    next_id := cenv.(next_id);
    new_temps := cenv.(new_temps);
    new_internals := cenv.(new_internals);
  |}.

Definition cenv_get_next_id [Pu Iu Sa GF GV T] (cenv: compilenv Pu Iu Sa GF GV T): AST.ident * compilenv Pu Iu Sa GF GV T :=
  (cenv.(next_id), {| next_id := Pos.succ cenv.(next_id); new_temps := cenv.(new_temps); new_internals := cenv.(new_internals); cenv_ctxt := cenv.(cenv_ctxt); |}).

Definition cenv_new_temp [Pu Iu Sa GF GV] t_temp (cenv: compilenv (Pu*bool) Iu Sa GF GV (AST.ident * Pu)): AST.ident * compilenv (Pu*bool) Iu Sa GF GV (AST.ident * Pu) :=
  let '(id_temp, cenv) := cenv_get_next_id cenv in
  (id_temp, {|
              cenv_ctxt := Ctxt.set_pure id_temp (t_temp, false) cenv.(cenv_ctxt);
              next_id := cenv.(next_id);
              new_temps := (id_temp, t_temp)::cenv.(new_temps);
              new_internals := cenv.(new_internals);
            |}).

Definition cenv_new_internal [Pu Iu Sa GF GV] t_int (cenv: compilenv (Pu*bool) Iu Sa GF GV (AST.ident * Pu)): AST.ident * compilenv (Pu*bool) Iu Sa GF GV (AST.ident * Pu) :=
  let '(id_int, cenv) := cenv_get_next_id cenv in
  (id_int, {|
             cenv_ctxt := cenv.(cenv_ctxt);
             next_id := cenv.(next_id);
             new_temps := cenv.(new_temps);
             new_internals := (id_int, t_int)::cenv.(new_internals);
           |}).

Definition cmd_compilenv := compilenv (type * bool) (type * bool) unit IR.Prog.fundef vardef (AST.ident * type).
Definition prog_compilenv := compilenv Empty_set Empty_set Empty_set IR.Prog.fundef vardef Empty_set.

Definition mk_cmd_compilenv (cenv: prog_compilenv) (args: list (AST.ident * type)) : cmd_compilenv  :=
  {|
    next_id := cenv.(next_id);
    new_temps := [];
    new_internals := [];
    cenv_ctxt := Ctxt.with_internal (Maps.PTree.empty _)
                   (Ctxt.with_pure (Maps.PTree_Properties.of_list (List.map (fun '(id_arg, t_arg) => (id_arg, (t_arg, true))) args))
                      (Ctxt.with_stack [] cenv.(cenv_ctxt)));
  |}.

Definition mk_prog_compilenv (cenv: cmd_compilenv) : prog_compilenv :=
  {|
    next_id := cenv.(next_id);
    new_temps := [];
    new_internals := [];
    cenv_ctxt := Ctxt.to_glob_ctxt (cenv.(cenv_ctxt));
  |}.

Fixpoint transl_cmd (cenv: cmd_compilenv) (tail: bool) (c: cmd) {struct c}: res (IR.Cmd.cmd * type * cmd_compilenv) :=
  match c with
  | c_ret e =>
      match type_expr cenv.(cenv_ctxt).(ctxt_pure) e with
      | Some t => OK (IR.Cmd.c_ret e t, t, cenv)
      | None => Error [MSG "IRGen.transl_cmd: c_ret type error"]
      end
  | c_bind b_id t_b c_b c_c =>
      do ' (tc_b, t_b', cenv) <- transl_cmd cenv false c_b;
      do assert type_eqb t_b t_b';
      do ' (tc_c, t_c, cenv) <- transl_cmd (cenv_add_bind b_id t_b cenv) tail c_c;
      OK (IR.Cmd.c_bind b_id t_b tc_b tc_c t_c, t_c, cenv)
  | c_if e_i c_t c_e =>
      do ' (tc_t, t_t, cenv) <- transl_cmd cenv tail c_t;
      do ' (tc_e, t_e, cenv) <- transl_cmd cenv tail c_e;
      do assert type_eqb t_t t_e;
      OK (IR.Cmd.c_if e_i tc_t tc_e t_t, t_t, cenv)

  | c_while c_cond c_body =>
      do ' (tc_cond, t_cond, cenv) <- transl_cmd cenv false c_cond;
      do ' (tc_body, t_body, cenv) <- transl_cmd cenv false c_body;
      do assert type_eqb t_cond t_bool;
      do assert type_eqb t_body t_unit;
      let '(id_cond, cenv) := cenv_new_internal t_bool cenv in
      let '(id_body, cenv) := cenv_new_internal t_unit cenv in
      OK (IR.Cmd.c_while tc_cond id_cond tc_body id_body, t_unit, cenv)
  | c_with_var t_v e_v c_c =>
      let tc_write := IR.Cmd.c_write_var (List.length (ctxt_stack (cenv.(cenv_ctxt)))) t_v e_v in
      let '(id_var, cenv) := cenv_new_temp t_unit cenv in
      do ' (tc_c, t, cenv) <- transl_cmd (cenv_add_bind id_var t_unit (cenv_push_stack cenv)) tail c_c;
      OK (IR.Cmd.c_bind id_var t_unit tc_write tc_c t, t, cenv_pop_stack cenv)
  | c_read_var n t =>
      OK (IR.Cmd.c_read_var n t, t, cenv)
  | c_write_var n t e =>
      OK (IR.Cmd.c_write_var n t e, t_unit, cenv)
  | c_alloc_ptr e_size t e_init =>
      let '(id_ptr, cenv) := cenv_new_internal t_ptr cenv in
      let '(id_count, cenv) := cenv_new_internal t_ofst cenv in
      let '(id_init, cenv) := cenv_new_internal t cenv in
      OK (IR.Cmd.c_alloc_ptr e_size t e_init id_ptr id_count id_init, t_ptr, cenv)
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
      do assert (negb tail);
      match Globalenvs.Genv.find_symbol cenv.(cenv_ctxt).(ctxt_global) id_f with
      | Some b =>
          match Globalenvs.Genv.find_funct_ptr cenv.(cenv_ctxt).(ctxt_global) b, ListExt.map_opt (type_expr cenv.(cenv_ctxt).(ctxt_pure)) args with
          | Some (AST.Internal fn), Some t_args =>
              if ListExt.forall2b type_eqb t_args (List.map snd fn.(fn_params)) then
                OK (IR.Cmd.c_app id_f fn.(fn_return) (List.combine args t_args), fn.(fn_return), cenv)
              else
                Error ([MSG "Arguments and signature do not match"])
          | Some (AST.External (AST.EF_external nm sg)), Some t_args =>
              match Facts.ef_sig_dec (AST.EF_external nm sg) with
              | Some sig =>
                  if ListExt.forall2b type_eqb t_args sig.(sig_args) then
                    OK (IR.Cmd.c_app id_f sig.(sig_res) (List.combine args t_args), sig.(sig_res), cenv)
                  else
                    Error [MSG "Unsound external function call"]
              | None => Error [MSG "Unsound external function call"]
              end
          | _, _ => Error [MSG "Unsupported function call"]
          end
      | None => Error [ MSG "B"]
      end
  | c_div e_l e_r => OK (IR.Cmd.c_div e_l e_r, t_nat, cenv)
  | c_mod e_l e_r => OK (IR.Cmd.c_mod e_l e_r, t_nat, cenv)
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
  | c_div _ _ | c_mod _ _
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
      do assert (sbinds Pos.eqb (fn.(fn_params) ++ Deep.Cmd.cmd_temps fn.(fn_body)));
      do assert (forallb (fun '(id, _) => Pos.ltb id cenv.(next_id))
                   (fn.(fn_params) ++ fn.(fn_temps) ++ Deep.Cmd.cmd_temps fn.(fn_body)));
      do ' (body, t_body, cenv) <- transl_cmd (mk_cmd_compilenv cenv fn.(fn_params)) true fn.(fn_body);
      do assert (type_eqb t_body fn.(fn_return));
      do assert (IR.Typing.type_f_extra {| IR.Prog.fn_stackspace := stack_usage fn.(fn_body); |});
      OK ((AST.Internal
             {|fn_return := fn.(fn_return);
               fn_params := fn.(fn_params);
               fn_temps := List.rev_append fn.(fn_temps) cenv.(new_temps);
               fn_internals := cenv.(new_internals);
               fn_body := body;
               fn_extra := {| IR.Prog.fn_stackspace := stack_usage fn.(fn_body); |};
             |}),
          mk_prog_compilenv cenv)
  end.

Fixpoint transl_globdefs (cenv: prog_compilenv) (gdefs: list (AST.ident * globdef)) (acc: list (AST.ident * IR.Prog.globdef)): res (list (AST.ident * IR.Prog.globdef) * prog_compilenv) :=
  match gdefs with
  | [] =>
      OK (List.rev acc, cenv)
  | (g_id, AST.Gvar var_info)::gdefs =>
      do assert (type_init_data var_info.(AST.gvar_init)
                                           var_info.(AST.gvar_info).(var_type)
                 && negb var_info.(AST.gvar_readonly)
                 && negb var_info.(AST.gvar_volatile));
      transl_globdefs cenv gdefs ((g_id, AST.Gvar var_info)::acc)
  | (g_id, AST.Gfun fd)::gdefs =>
      do ' (tfd, cenv) <- transl_fundef cenv fd;
      let cenv := cenv_add_fun g_id tfd cenv in
      transl_globdefs cenv gdefs ((g_id, AST.Gfun tfd)::acc)
  end.

Definition transl_program (p: program) : res (IR.Prog.program) :=
  do assert (forallb (fun '(id, _) => Pos.ltb id p.(prog_extra).(prog_next_id))
               p.(prog_defs));
  do ' (tgl', cenv) <-
       transl_globdefs
         {|
           next_id := p.(prog_extra).(prog_next_id);
           new_temps := [];
           new_internals := [];
           cenv_ctxt := ctxt_emp _ _ _ _ _ (List.map fst p.(prog_defs))
         |}
         p.(prog_defs) [];
  OK
    {|
      prog_defs := tgl';
      prog_public := p.(prog_public);
      prog_main := p.(prog_main);
      prog_extra := tt
    |}.
