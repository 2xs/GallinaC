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

From GallinaC.Compiler.Common Require Export Expr.
From GallinaC.Compiler.Reify Require Export Common Types Env.

Import MonadNotation.
Local Open Scope bs_scope.

Polymorphic Definition translate_named_var (renv: reify_funbody_env) (x: ident): option expr :=
  match resolve_named_temp renv x with
  | Some i => Some (e_var i)
  | None => None
  end.

Fixpoint translate_expr (renv: reify_funbody_env) (tm : term) : TemplateMonad expr :=
  match tm with
  | tRel i =>
      e <-
        match resolve_rel_temp renv i with
        | Some i => tmReturn (e_var i)
        | None => tmFail "Unbound rel variable"
        end
      ;;
      tmEval cbv e
  | tConst kname _ =>
      match resolve_expr kname with
      | Some NullPtr => tmReturn e_nullptr
      | _ =>
          match translate_named_var renv (snd kname) with
          | Some e => tmEval cbv e
          | None =>
              tmPrint tm;;
              tmFail "Unknow expression"
          end
      end
  | tConstruct ind n _ =>
      match resolve_prim_inductive ind with
      | Some t_unit => tmReturn e_tt
      | Some t_bool =>
          b <- tmEval cbv (Nat.eqb n 0);; tmReturn (e_bool b)
      | Some t_nat =>
          n <- tmUnquoteTyped nat tm;; tmReturn (e_nat n)
      | Some t_ofst =>
          n <- tmUnquoteTyped N tm;; tmReturn (e_ofst n)
      | Some t_ptr | None =>
          tmBind (tmPrint tm)
            (fun _ => tmFail "Error in reify_expr: not an expression")
      end
  | tApp f args =>
      match f with
      | tConstruct ind _ _ =>
          match resolve_prim_inductive ind with
          | Some t_nat =>
              n <- tmUnquoteTyped nat tm;; tmReturn (e_nat n)
          | Some t_ofst =>
              n <- tmUnquoteTyped N tm;; tmReturn (e_ofst n)
          | _ =>
              tmBind (tmPrint tm)
                (fun _ => tmFail "Error in reify_expr: not an expression")
          end
      | tConst kname [] =>
          match resolve_expr kname, args with
          | Some NullPtr, [_; _] => tmReturn e_nullptr
          | Some Negb, [tm'] =>
              e <- translate_expr renv tm';;
              tmReturn (e_neg e)
          | Some Add, [kint; tm1; tm2] =>
              match resolve_int kint with
              | Some U32 =>
                  e1 <- translate_expr renv tm1;;
                  e2 <- translate_expr renv tm2;;
                  tmReturn (e_add e1 e2)
              | _ => tmPrint tm;; tmFail "Error in reify_expr: not a registered integer"
              end
          | Some Eqb, [kint; tm1; tm2] =>
              match resolve_int kint with
              | Some U32 =>
                  e1 <- translate_expr renv tm1;;
                  e2 <- translate_expr renv tm2;;
                  tmReturn (e_eqb e1 e2)
              | _ => tmPrint tm;; tmFail "Error in reify_expr: not a registered integer"
              end
          | Some Mul, [kint; tm1; tm2] =>
              match resolve_int kint with
              | Some U32 =>
                  e1 <- translate_expr renv tm1;;
                  e2 <- translate_expr renv tm2;;
                  tmReturn (e_mul e1 e2)
              | _ => tmPrint tm;; tmFail "Error in reify_expr: not a registered integer"
              end
          | _, _ =>
              tmBind (tmPrint tm)
                (fun _ => tmFail "Error in reify_expr: not an expression")
          end
      | _ =>
          tmBind (tmPrint tm)
            (fun _ => tmFail "Error in reify_expr: not an expression")
      end
  | _ =>
      tmBind
        (tmPrint tm)
        (fun _ => tmFail "Error in reify_expr: not an expression")
  end.
