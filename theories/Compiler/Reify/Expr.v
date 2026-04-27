From Stdlib Require Import PArith Arith.

From MetaRocq.Template Require Import All.

From GallinaC.Utils Require Import ListExt.

From GallinaC.Compiler.Common Require Export Expr.
From GallinaC.Compiler.Reify Require Export Types Env.

Import MonadNotation.
Local Open Scope bs_scope.

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
  | tConst (MPdot _ "Pointer", "NULL") _ => tmReturn e_nullptr
  | tConst (_, x) _  =>
      e <-
        match resolve_named_temp renv x with
        | Some i =>
            tmReturn (e_var i)
        | None => tmFail "Unbound named variable"
        end
      ;;
      tmEval cbv e
  | tConstruct {| inductive_mind := (_, "unit") |} _ _ => tmReturn e_tt
  | tConstruct {| inductive_mind := (_, "bool") |} n [] =>
      b <- tmEval cbv (Nat.eqb n 0);; tmReturn (e_bool b)
  | tConstruct {| inductive_mind := (_, "nat") |} _ _ =>
      n <- tmUnquoteTyped nat tm ;;
      tmReturn (e_nat n)
  | tApp (tConstruct {| inductive_mind := (_, "nat") |} _ _) _ =>
      n <- tmUnquoteTyped nat tm ;;
      tmReturn (e_nat n)
  | tConstruct {| inductive_mind := (_, "N") |} _ _ =>
      n <- tmUnquoteTyped N tm ;;
      tmReturn (e_ofst n)
  | tApp (tConstruct {| inductive_mind := (_, "N") |} _ _) _ =>
      n <- tmUnquoteTyped N tm ;;
      tmReturn (e_ofst n)
  (* | tApp (tConst (_, "of_num_uint") []) _ => *)
  (*     n <- tmUnquoteTyped nat tm ;; *)
  (*     tmReturn (e_nat n) *)
  | tApp (tConst (_, "negb") []) [tm'] =>
      e <- translate_expr renv tm' ;;
      tmReturn (e_neg e)
  | tApp (tConst (_, "add") []) [tm1; tm2] =>
      e1 <- translate_expr renv tm1 ;;
      e2 <- translate_expr renv tm2 ;;
      tmReturn (e_plus e1 e2)
  | tApp (tConst (_, "eqb") []) [tm1; tm2] =>
      e1 <- translate_expr renv tm1 ;;
      e2 <- translate_expr renv tm2 ;;
      tmReturn (e_nat_eq e1 e2)
  | _ =>
      tmBind
        (tmPrint tm)
        (fun _ => tmFail "Error in reify_expr: not an expression")
  end.
