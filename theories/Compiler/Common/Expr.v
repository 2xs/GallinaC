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

From Stdlib Require Import ZArith NArith Arith Psatz ssreflect.

From compcert.common Require AST.
From compcert.lib Require Import Maps Integers.

From HB Require Import structures.

From GallinaC Require Import ListExt.

From GallinaC.Utils Require Import Algebra BoolExt PosExt NatExt NExt.
From GallinaC.Imp Require Import Intops Uint32 Uintptr.
From GallinaC.Imp Require Import Heap.

From GallinaC.Compiler.Common Require Import Ctxt Value CCInj Types.
From GallinaC.Compiler.Common Require Export Types(type, t_unit, t_bool, t_nat, t_ofst, t_ptr).

Inductive expr: Set :=
| e_var: AST.ident -> expr
| e_tt : expr
| e_bool : bool -> expr
| e_nat : nat -> expr
| e_ofst: forall (ofst: N.t), expr
| e_nullptr: expr
| e_neg: expr -> expr
| e_add: expr -> expr -> expr
| e_mul: expr -> expr -> expr
| e_eqb: expr -> expr -> expr
.

Inductive expr_of_value {Ad: Addr.type} {Pt: Ptr.type Ad}: value Pt -> expr -> Prop :=
| eov_tt: expr_of_value v_tt e_tt
| eov_bool: forall b, expr_of_value (v_bool b) (e_bool b)
| eov_nat: forall n, expr_of_value (v_nat n) (e_nat n)
| eov_ofst: forall n, expr_of_value (v_ofst n) (e_ofst n)
| eov_nullptr: expr_of_value (v_ptr (null: Pt)) e_nullptr
.

Fixpoint expr_eqb (e1 e2: expr): bool :=
  match e1, e2 with
  | e_var v1, e_var v2 => Pos.eqb v1 v2
  | e_tt, e_tt => true
  | e_bool b1, e_bool b2 => Bool.eqb b1 b2
  | e_nat n1, e_nat n2 => Nat.eqb n1 n2
  | e_ofst n1, e_ofst n2 => N.eqb n1 n2
  | e_nullptr, e_nullptr => true
  | e_neg e1, e_neg e2 => expr_eqb e1 e2
  | e_add l1 r1, e_add l2 r2 => expr_eqb l1 l2 && expr_eqb r1 r2
  | e_mul l1 r1, e_mul l2 r2 => expr_eqb l1 l2 && expr_eqb r1 r2
  | e_eqb l1 r1, e_eqb l2 r2 => expr_eqb l1 l2 && expr_eqb r1 r2
  | _,_ => false
  end.

Lemma expr_eqb_spec: forall x y, Bool.reflect (x = y) (expr_eqb x y).
Proof.
  induction x;
    destruct y; cbn;
    (try (right; now congruence));
    (try (left; now congruence)).
  - destruct (Pos.eqb i i0) eqn:H.
    left; apply Pos.eqb_eq in H; congruence.
    right; apply Pos.eqb_neq in H; congruence.
  - destruct (Bool.eqb_spec b b0); subst; constructor; congruence.
  - destruct (Nat.eqb_spec n n0); subst; constructor; congruence.
  - destruct (N.eqb_spec ofst ofst0); subst; constructor; congruence.
  - destruct (IHx y) as [ EQ | NE ];
      subst; constructor; congruence.
  - destruct (IHx1 y1), (IHx2 y2); subst; constructor; congruence.
  - destruct (IHx1 y1), (IHx2 y2); subst; constructor; congruence.
  - destruct (IHx1 y1), (IHx2 y2); subst; constructor; congruence.
Qed.

HB.instance Definition _ := hasEqDec.Build expr expr_eqb expr_eqb_spec.

Fixpoint eval [Ad: Addr.type] [Pt: Ptr.type Ad] (e: expr) (env: Maps.PTree.t (value Pt)): option (value Pt) :=
  match e with
  | e_var id => Maps.PTree.get id env
  | e_tt => Some v_tt
  | e_bool b => Some (v_bool b)
  | e_nat n => Some (v_nat n)
  | e_ofst o => Some (v_ofst o)
  | e_nullptr => Some (v_ptr (null: Pt))
  | e_neg e =>
      match eval e env with
      | Some (v_bool b) => Some (v_bool (negb b))
      | _ => None
      end
  | e_add e_l e_r =>
      match eval e_l env, eval e_r env with
      | Some (v_nat v_l), Some (v_nat v_r) =>
          Some (v_nat (Unsigned.add v_l v_r))
      | _, _ => None
      end
  | e_mul e_l e_r =>
      match eval e_l env, eval e_r env with
      | Some (v_nat v_l), Some (v_nat v_r) =>
          Some (v_nat (Unsigned.mul v_l v_r))
      | _, _ => None
      end
  | e_eqb e_l e_r =>
      match eval e_l env, eval e_r env with
      | Some (v_nat v_l), Some (v_nat v_r) =>
          Some (v_bool (Unsigned.eqb v_l v_r))
      | _, _ => None
      end
  end.

Inductive wt_expr (ctxt : Maps.PTree.t (type * bool)) : expr -> type -> Prop :=
| wt_var : forall var_id t
                  (GET: PTree.get var_id ctxt = Some (t,true)),
    wt_expr ctxt (e_var var_id) t
| wt_tt : wt_expr ctxt e_tt t_unit
| wt_bool : forall b, wt_expr ctxt (e_bool b) t_bool
| wt_nat : forall (n: nat) (BOUNDED: Intops.Unsigned.Bounded n), wt_expr ctxt (e_nat n) t_nat
| wt_ofst : forall (n: N) (BOUNDED: Intops.Unsigned.Bounded n), wt_expr ctxt (e_ofst n) t_ofst
| wt_nullptr : wt_expr ctxt e_nullptr t_ptr
| wt_neg : forall b (WTb: wt_expr ctxt b t_bool), wt_expr ctxt (e_neg b) t_bool
| wt_add : forall l r
                   (WTl: wt_expr ctxt l t_nat)
                   (WTr: wt_expr ctxt r t_nat),
    wt_expr ctxt (e_add l r) t_nat
| wt_mul : forall l r
                   (WTl: wt_expr ctxt l t_nat)
                   (WTr: wt_expr ctxt r t_nat),
    wt_expr ctxt (e_mul l r) t_nat
| wt_eqb : forall l r
                     (WTl: wt_expr ctxt l t_nat)
                     (WTr: wt_expr ctxt r t_nat),
    wt_expr ctxt (e_eqb l r) t_bool
.
Arguments wt_var {_} _ _ _.
Arguments wt_tt {_}.
Arguments wt_bool {_} _.
Arguments wt_nat {_} _ _.
Arguments wt_ofst {_} _ _.
Arguments wt_nullptr {_}.
Arguments wt_neg {_ _} _.
Arguments wt_add {_ _ _} _ _.
Arguments wt_mul {_ _ _} _ _.
Arguments wt_eqb {_ _ _} _ _.

Fixpoint type_expr (env: Maps.PTree.t (type * bool)) (e: expr): option type :=
  match e with
  | e_var var_id =>
      match Maps.PTree.get var_id env with
      | Some ((t_unit|t_bool|t_nat|t_ofst|t_ptr) as t, true) => Some t
      | _ => None
      end
  | e_tt => Some t_unit
  | e_bool _ => Some t_bool
  | e_nat n =>
      if Z.leb (Z.of_nat n) (Unsigned.max_unsigned nat_uint32_t) then
        Some t_nat
      else
        None
  | e_ofst o =>
      if Z.leb (Z.of_N o) (Unsigned.max_unsigned n_ofst_t) then
        Some t_ofst
      else
        None
  | e_nullptr => Some t_ptr
  | e_neg e =>
      match type_expr env e with
      | Some t_bool => Some t_bool
      | _ => None
      end
  | e_add l r =>
      match type_expr env l, type_expr env r with
      | Some t_nat, Some t_nat => Some t_nat
      | _, _ => None
      end
  | e_mul l r =>
      match type_expr env l, type_expr env r with
      | Some t_nat, Some t_nat => Some t_nat
      | _, _ => None
      end
  | e_eqb l r =>
      match type_expr env l, type_expr env r with
      | Some t_nat, Some t_nat => Some t_bool
      | _, _ => None
      end
  end.

Module Facts.

  Lemma expr_of_value_fun [Ad] [Pt: Ptr.type Ad] [v: value Pt] [e1 e2]
    (EOV1: expr_of_value v e1) (EOV2: expr_of_value v e2): e2 = e1.
  Proof.
    inversion EOV1; subst; inversion EOV2; subst; reflexivity.
  Qed.
  #[global] Hint Resolve expr_of_value_fun: deep_gallinac.

  Lemma type_expr_correct [env e t] (WT: wt_expr env e t): type_expr env e = Some t.
  Proof.
    induction WT; cbn;
      first
        [ by rewrite IHWT
        | by rewrite IHWT1 IHWT2
        | auto ].
    - by rewrite GET; destruct t.
    - inversion BOUNDED; subst.
      change (IntCarrier.to_Z n) with (Z.of_nat n) in *.
      destruct (Z.leb_spec (Z.of_nat n) (Unsigned.max_unsigned nat_uint32_t)); auto.
      lia.
    - destruct (Z.leb_spec (Z.of_N n) (Unsigned.max_unsigned n_ofst_t)); auto.
      inversion BOUNDED.
      change (IntCarrier.to_Z n) with (Z.of_N n) in *; lia.
  Qed.

  Lemma type_expr_complete [env e t] (EQ: type_expr env e = Some t): wt_expr env e t.
  Proof.
    revert env t EQ.
    induction e; cbn; intros;
      try (now inversion EQ; subst; constructor).
    - destruct (env ! i) as [ [ [ | | | | ] [ | ] ] | ] eqn:GET;
        inversion EQ; subst; clear EQ;
        constructor; auto; constructor.
    - destruct (Z.leb (Z.of_nat n) (Unsigned.max_unsigned nat_uint32_t)) eqn:LEB;
        inversion EQ; subst; clear EQ.
      constructor; split.
      apply Nat2Z.is_nonneg.
      apply Z.leb_le, LEB.
    - destruct (Z.leb (Z.of_N ofst) (Unsigned.max_unsigned n_ofst_t)) eqn:LEB;
        inversion EQ; subst; clear EQ.
      constructor; split; [ apply N2Z.is_nonneg | apply Z.leb_le, LEB].
    - destruct (type_expr env e) as [ [ | | | | ] | ] eqn:EQ';
        inversion EQ; subst; clear EQ.
      apply wt_neg, IHe, EQ'.
    - destruct (type_expr env e1) as [ [ | | | | ] | ] eqn:EQ1;
        try discriminate;
        destruct (type_expr env e2) as [ [ | | | | ] | ] eqn:EQ2;
        try discriminate;
        inversion EQ; subst; clear EQ.
      auto using wt_add.
    - destruct (type_expr env e1) as [ [ | | | | ] | ] eqn:EQ1;
        try discriminate;
        destruct (type_expr env e2) as [ [ | | | | ] | ] eqn:EQ2;
        try discriminate;
        inversion EQ; subst; clear EQ.
      auto using wt_mul.
    - destruct (type_expr env e1) as [ [ | | | | ] | ] eqn:EQ1;
        try discriminate;
        destruct (type_expr env e2) as [ [ | | | | ] | ] eqn:EQ2;
        try discriminate;
        inversion EQ; subst; clear EQ.
      auto using wt_eqb.
  Qed.

  Lemma type_expr_incl [ctx1 ctx2: Maps.PTree.t (type * bool)] [e t]
    (INCL: forall id ty, Maps.PTree.get id ctx1 = Some (ty, true) ->
                         Maps.PTree.get id ctx2 = Some (ty, true))
    (TE: type_expr ctx1 e = Some t):
    type_expr ctx2 e = Some t.
  Proof.
    revert t TE.
    induction e; intros t' TE; cbn in TE |- *; try exact TE.
    - destruct (Maps.PTree.get i ctx1) as [ [ ty b ] | ] eqn:EG1; [ | discriminate ].
      destruct b, ty; cbn in TE; try discriminate;
        rewrite (INCL _ _ EG1); exact TE.
    - destruct (type_expr ctx1 e) as [ ty | ]; [ | discriminate ].
      rewrite (IHe _ eq_refl); exact TE.
    - destruct (type_expr ctx1 e1) as [ ty1 | ]; [ | discriminate ].
      destruct (type_expr ctx1 e2) as [ ty2 | ]; [ | destruct ty1; discriminate ].
      rewrite (IHe1 _ eq_refl); rewrite (IHe2 _ eq_refl); exact TE.
    - destruct (type_expr ctx1 e1) as [ ty1 | ]; [ | discriminate ].
      destruct (type_expr ctx1 e2) as [ ty2 | ]; [ | destruct ty1; discriminate ].
      rewrite (IHe1 _ eq_refl); rewrite (IHe2 _ eq_refl); exact TE.
    - destruct (type_expr ctx1 e1) as [ ty1 | ]; [ | discriminate ].
      destruct (type_expr ctx1 e2) as [ ty2 | ]; [ | destruct ty1; discriminate ].
      rewrite (IHe1 _ eq_refl); rewrite (IHe2 _ eq_refl); exact TE.
  Qed.

  Lemma map_opt_type_expr_incl [ctx1 ctx2: Maps.PTree.t (type * bool)] [args ts]
    (INCL: forall id ty, Maps.PTree.get id ctx1 = Some (ty, true) ->
                         Maps.PTree.get id ctx2 = Some (ty, true))
    (TE: ListExt.map_opt (type_expr ctx1) args = Some ts):
    ListExt.map_opt (type_expr ctx2) args = Some ts.
  Proof.
    refine (ListExt.map_opt_Forall2 (R := fun a t => type_expr ctx1 a = Some t) _ _).
    - intros a t TEa; exact (type_expr_incl INCL TEa).
    - exact (ListExt.map_opt_Forall2_inv (fun _ _ TEa => TEa) TE).
  Qed.

  Lemma wt_expr_true_incl [ctx1 ctx2: Maps.PTree.t (type * bool)] [e t]
    (INCL: forall id ty, Maps.PTree.get id ctx1 = Some (ty, true) ->
                         Maps.PTree.get id ctx2 = Some (ty, true))
    (WT: wt_expr ctx1 e t):
    wt_expr ctx2 e t.
  Proof.
    exact (type_expr_complete (type_expr_incl INCL (type_expr_correct WT))).
  Qed.

  Lemma eval_preservation [Ad] [Pt: Ptr.type Ad] [ctx e t env] [v: value Pt]
    (WTe: wt_expr ctx e t)
    (ENV: forall id t', Maps.PTree.get id ctx = Some (t', true) ->
          exists2 v', Maps.PTree.get id env = Some v' & wt_value v' t')
    (EVAL: eval e env = Some v) :
    wt_value v t.
  Proof.
    revert v EVAL.
    induction WTe; intros v EVAL.
    - cbn [eval] in EVAL.
      destruct (ENV var_id t GET) as [v' GETv WT].
      rewrite GETv in EVAL; inversion EVAL; subst.
      exact WT.
    - cbn [eval] in EVAL; inversion EVAL; subst; constructor.
    - cbn [eval] in EVAL; inversion EVAL; subst; constructor.
    - cbn [eval] in EVAL; inversion EVAL; subst; constructor.
    - cbn [eval] in EVAL; inversion EVAL; subst; constructor.
    - cbn [eval] in EVAL; inversion EVAL; subst; constructor.
    - cbn in EVAL.
      destruct (eval b env) as [[|vb| | |]|]; try discriminate.
      injection EVAL as <-.
      constructor.
    - cbn in EVAL.
      destruct (eval l env) as [ [| | vnatl | | ] | ]; try discriminate.
      destruct (eval r env) as [ [| | vnatr | | ] | ]; try discriminate.
      injection EVAL as <-.
      constructor.
    - cbn in EVAL.
      destruct (eval l env) as [ [| | vnatl | | ] | ]; try discriminate.
      destruct (eval r env) as [ [| | vnatr | | ] | ]; try discriminate.
      injection EVAL as <-.
      constructor.
    - cbn in EVAL.
      destruct (eval l env) as [ [| | vnatl | | ] | ]; try discriminate.
      destruct (eval r env) as [ [| | vnatr | | ] | ]; try discriminate.
      injection EVAL as <-.
      constructor.
  Qed.
  #[global] Hint Resolve eval_preservation: deep_gallinac.

  Lemma wt_value_expr_agree [Ad] [Pt: Ptr.type Ad] [ctx] [v: value Pt] [e t_v t_e]
    (EOV: expr_of_value v e) (WTval: wt_value v t_v) (WTexpr: wt_expr ctx e t_e)
    : t_v = t_e.
  Proof.
    inversion EOV; subst;
      inversion WTval; subst;
      inversion WTexpr; subst;
      reflexivity.
  Qed.
  #[global] Hint Resolve wt_value_expr_agree: deep_gallinac.

  Lemma wt_expr_fun [ctx e t1 t2]
    (WT1: wt_expr ctx e t1) (WT2: wt_expr ctx e t2)
    : t1 = t2.
  Proof.
    inversion WT1; subst; inversion WT2; subst; congruence.
  Qed.
  #[global] Hint Resolve wt_expr_fun: deep_gallinac.

  Lemma forall2_wt_expr_forall2b_type_expr [ctx e_args t_args]
  (FORALL2: Forall2 (wt_expr ctx) e_args t_args):
  ListExt.forall2b
    (fun e t => match type_expr ctx e with
                | Some t' => eqb t' t
                | None => false
                end)
    e_args t_args = true.
Proof.
  induction FORALL2 as [ | e t es ts WT WTA IH ]; [ reflexivity | cbn [forall2b] ].
  by rewrite (Expr.Facts.type_expr_correct WT) (ReflectExt.reflect_refl eqb_spec _).
Qed.

Lemma forall2b_type_expr_forall2_wt_expr [ctx e_args t_args]
  (EQtype: ListExt.forall2b
          (fun e t => match type_expr ctx e with
                      | Some t' => type_eqb t' t
                      | None => false
                      end)
          e_args t_args = true)
  : Forall2 (wt_expr ctx) e_args t_args.
Proof.
  revert t_args EQtype; induction e_args as [ | e es IH ]; intros [ | t ts ] CHK;
    cbn in CHK; try discriminate CHK.
  - constructor.
  - destruct (type_expr ctx) as [t'|] eqn:TYP; [| discriminate CHK].
    destruct (type_eqb_spec t' t); [| discriminate CHK]; subst t'.
    constructor.
    + exact (Expr.Facts.type_expr_complete TYP).
    + exact (IH _ CHK).
Qed.


End Facts.
