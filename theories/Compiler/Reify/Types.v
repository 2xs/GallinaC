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

From MetaRocq.Template Require Import All.

From Stdlib Require Import PArith.

From GallinaC.Utils Require Import ListExt.

From GallinaC.Compiler.Common Require Export Types.
From GallinaC.Compiler.Reify Require Export Common.

Import MonadNotation.
Local Open Scope bs_scope.

Polymorphic Definition translate_storable (tm: term): TemplateMonad type :=
  match resolve_storable tm with
  | Some s => tmEval cbv (resolve_storable_type s)
  | None => tmPrint tm;; tmFail "Error in translate_storable"
  end.

Polymorphic Definition translate_type (tm : term) : TemplateMonad type :=
  match resolve_prim_type tm with
  | Some t => tmEval cbv t
  | None => tmPrint tm;; tmFail "Error in translate_type"
  end.

Polymorphic Fixpoint translate_signature (sig: term): TemplateMonad (list (string * type) * type * ModelRef) :=
  match sig with
  | tApp (tConst (modpath, "program") []) [State; t_out] =>
      t_out <- translate_type t_out;;
      tmReturn ([], t_out, model_of_state State)
  | tPro arg t_arg sig =>
      if is_state_structure t_arg then
        '(args, t_out, _) <- translate_signature sig;;
        tmEval cbv (args, t_out, ModelParam)
      else
        t_arg <- translate_type t_arg;;
        '(args, t_out, model) <- translate_signature sig;;
        tmEval cbv ((arg, t_arg)::args, t_out, model)
  | _ =>
      tmPrint sig;;
      tmFail "translate_signature: not a signature"
  end.

Polymorphic Definition introduce_new_external (renv: reify_funbody_env) (nm: kername): TemplateMonad (AST.ident * AST.external_function * reify_funbody_env) :=
  let new_id: AST.ident := renv.(next_id) in
  tm <- tmUnquote (tConst nm []);;
  sig <- tmEval cbn tm.(my_projT1);;
  sig <- tmQuote sig;;
  '(args, t_out, _) <- translate_signature sig;;
  (if List.existsb (fun '(_, t) => type_eqb t t_unit) args
   then tmFail "External functions with unit arguments have unstable ABI"
   else tmReturn tt);;
  let new_external: AST.external_function :=
    AST.EF_external
      (String.to_string (snd nm))
      (Prog.signature_of_signature (Prog.mk_signature (List.map snd args) t_out))
  in
  let renv: reify_funbody_env :=
    {|
      prog_renv :=
        {|
          next_id := Pos.succ renv.(next_id);
          funs := (nm, (renv.(next_id), AST.External new_external))::renv.(funs);
          current_module := renv.(current_module);
        |};
      stack := renv.(stack);
      stack_depth := renv.(stack_depth);
      temps := renv.(temps);
      model := renv.(model);
    |}
  in
  tmEval cbv (new_id, new_external, renv).
