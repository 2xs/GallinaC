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
      match resolve_expr renv kname with
      | Some NullPtrConst => tmReturn e_nullptr
      | _ =>
          match translate_named_var renv (snd kname) with
          | Some e => tmEval cbv e
          | None =>
              tmPrint tm;;
              tmFail "Unknow expression"
          end
      end
  | tConstruct ind n _ =>
      match resolve_expr_inductive ind with
      | Some TUnit => tmReturn e_tt
      | Some TBool =>
          b <- tmEval cbv (Nat.eqb n 0);; tmReturn (e_bool b)
      | Some TNat =>
          n <- tmUnquoteTyped nat tm;; tmReturn (e_nat n)
      | Some TN =>
          n <- tmUnquoteTyped N tm;; tmReturn (e_ofst n)
      | None =>
          tmBind (tmPrint tm)
            (fun _ => tmFail "Error in reify_expr: not an expression")
      end
  | tApp f args =>
      match f with
      | tConstruct ind _ _ =>
          match resolve_expr_inductive ind with
          | Some TNat =>
              n <- tmUnquoteTyped nat tm;; tmReturn (e_nat n)
          | Some TN =>
              n <- tmUnquoteTyped N tm;; tmReturn (e_ofst n)
          | _ =>
              tmBind (tmPrint tm)
                (fun _ => tmFail "Error in reify_expr: not an expression")
          end
      | tConst kname [] =>
          match resolve_expr renv kname, args with
          | Some Negb, [tm'] =>
              e <- translate_expr renv tm';;
              tmReturn (e_neg e)
          | Some NatAdd, [tm1; tm2] =>
              e1 <- translate_expr renv tm1;;
              e2 <- translate_expr renv tm2;;
              tmReturn (e_plus e1 e2)
          | Some NatEqb, [tm1; tm2] =>
              e1 <- translate_expr renv tm1;;
              e2 <- translate_expr renv tm2;;
              tmReturn (e_nat_eq e1 e2)
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
