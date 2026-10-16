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

From Stdlib Require Import PArith Arith.

From MetaRocq.Template Require Import All.

From GallinaC.Utils Require Import ListExt.

From GallinaC.Compiler.Deep Require Import Prog.
From GallinaC.Compiler.Reify Require Export Common Types Env Expr Cmd.

Import MonadNotation.
Local Open Scope bs_scope.

Polymorphic Fixpoint allocate_args_id renv (args: list (string * type)): TemplateMonad (list (string * (AST.ident * type)) * reify_program_env) :=
  match args with
  | [] => tmReturn ([], renv)
  | (mr_id, t_arg)::args =>
      cc_id <- tmEval cbv renv.(next_id);;
      renv <- tmEval cbv {| next_id := Pos.succ renv.(next_id); funs := renv.(funs); current_module := renv.(current_module); |};;
      '(args, renv) <- allocate_args_id renv args;;
      tmEval cbv ((mr_id, (cc_id, t_arg))::args, renv)
  end.

Polymorphic Definition mk_reify_funbody_stack (args: list (string * (AST.ident * type))): list binding :=
  List.map (fun '(mr_id, (cc_id, t_arg)) => Param mr_id cc_id t_arg) (List.rev args).

Polymorphic Definition mk_reify_funbody_env (renv: reify_program_env) (args: list (string * (AST.ident * type))) (model: ModelRef) : TemplateMonad (reify_funbody_env) :=
  tmEval cbv {| prog_renv := renv; stack := mk_reify_funbody_stack args; stack_depth := 0; temps := []; model := model; |}.

Polymorphic Fixpoint translate_funbody (renv: reify_funbody_env) (body : term) : TemplateMonad (cmd * reify_funbody_env) :=
  match body with
  | tLam _ _ body =>
      translate_funbody renv body
  | body =>
      translate_cmd true renv body
  end.

Polymorphic Definition translate_function (renv: reify_program_env) (mr_id: kername) (args: list (string * type)) (t_out: type) (model: ModelRef) (body : term) : TemplateMonad reify_program_env :=
  '(params, renv) <- allocate_args_id renv args;;
  params <- tmEval cbv params;;
  renv <- mk_reify_funbody_env renv params model;;
  '(body, renv) <- translate_funbody renv body;;
  tfunction <- tmEval cbv
                 (AST.Internal
                    {|
                      fn_return := t_out;
                      fn_params := List.map snd params;
                      fn_temps := renv.(temps);
                      fn_internals := nil;
                      fn_body := body;
                      fn_extra := tt;
                    |});;
  tmEval cbv (push_fun renv mr_id tfunction).

Polymorphic Fixpoint translate_module (renv: reify_program_env) (module: list global_reference): TemplateMonad reify_program_env :=
  match module with
  | ConstRef kname::module =>
      tm <- tmUnquote (tConst kname []);;
      f_sig <- tmEval cbn tm.(my_projT1);;
      f_sig <- tmQuote f_sig;;
      '(args, t_out, model) <- translate_signature f_sig;;
      body <- tmEval cbn tm.(my_projT2);;
      body <- tmEval (unfold kname) body;;
      body <- tmQuote body;;
      renv <- translate_function renv kname args t_out model body;;
      translate_module renv module
  | [] => tmReturn renv
  | gref::_ => tmMsg "translate_module: Unsupported global reference";; tmPrint gref;; tmFail ""
  end.

Polymorphic Definition reify_program (module main boundname: qualid): TemplateMonad program :=
  path <- tmLocateModule1 module;;
  M <- tmQuoteModule module;;
  renv <- translate_module (init_reify_env path) M;;
  gref_main <- tmLocate1 main;;
  match gref_main with
  | ConstRef kn_main =>
      match List.find (fun '(mr_id, _) => Kernames.eq_constant mr_id kn_main) renv.(funs) with
      | Some (_, (id_main, _)) =>
      prog <-
        tmEval cbv
               {|
                 prog_defs := List.rev (List.map (fun '(_, (gc_id, f)) => (gc_id, AST.Gfun f)) renv.(funs));
                 prog_public := List.rev (List.map (fun x => fst (snd x)) renv.(funs));
                 prog_main := id_main;
                 prog_extra := {| prog_next_id := renv.(next_id); |};
               |};;
      tmDefinition boundname prog;;
      symbols <- tmEval cbv
                   (List.map
                      (fun '((_, mr_id), (cc_id, _)) => (String.to_string mr_id, cc_id))
                      renv.(funs));;
      tmDefinition (boundname ++ "_symbols") symbols;;
      tmReturn prog
      | None => tmFail "Unable to find main function"
      end
  | _ => tmMsg "Provided main: ";; tmPrint main;;
         tmMsg "Inferred global reference: ";; tmPrint gref_main;;
         tmFail "Unhandled case"
  end.
