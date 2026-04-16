From Stdlib Require Import ZArith NArith Arith Psatz.

From compcert.common Require AST.
From compcert.lib Require Import Maps Integers.

From GallinaC.Imp Require Import Pointer Intops Uint32 Uintptr.

From GallinaC.Compiler.Common Require Import Ctxt Value CCInj.
From GallinaC.Compiler.Common Require Export Types(type, t_unit, t_bool, t_nat, t_ofst, t_ptr, t_fun, ground).

Inductive expr: Type :=
| e_var: AST.ident -> expr
| e_tt : expr
| e_bool : bool -> expr
| e_nat : nat -> expr
| e_ofst: forall (ofst: N.t), expr
| e_nullptr: expr
| e_neg: expr -> expr
| e_plus: expr -> expr -> expr
| e_nat_eq: expr -> expr -> expr
.

Inductive expr_of_value: Value.value -> expr -> Prop :=
| eov_tt: expr_of_value v_tt e_tt
| eov_bool: forall b, expr_of_value (v_bool b) (e_bool b)
| eov_nat: forall n, expr_of_value (v_nat n) (e_nat n)
| eov_ofst: forall n, expr_of_value (v_ofst n) (e_ofst n)
| eov_nullptr: expr_of_value (v_ptr Pointer.NULL) e_nullptr
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
  | e_plus l1 r1, e_plus l2 r2 => expr_eqb l1 l2 && expr_eqb r1 r2
  | e_nat_eq l1 r1, e_nat_eq l2 r2 => expr_eqb l1 l2 && expr_eqb r1 r2
  | _,_ => false
  end.

Lemma expr_eq_dec: forall (x y: expr), { x = y } + { x <> y }.
Proof.
  induction x.
  - destruct y; try (constructor; discriminate).
    destruct (Pos.eq_dec i i0) as [ Heq | ]; constructor; congruence.
  - destruct y; constructor; congruence.
  - destruct y; try (constructor; discriminate); destruct (Bool.eqb_spec b b0); constructor; congruence.
  - destruct y; try (constructor; discriminate).
    destruct (Nat.eq_dec n n0) as [ Heq | ]; constructor; congruence.
  - destruct y; try (constructor; discriminate).
    destruct (N.eq_dec ofst ofst0); constructor; congruence.
  - destruct y; (constructor; congruence).
  - destruct y; try (constructor; discriminate).
    destruct (IHx y); constructor; congruence.
  - destruct y; try (constructor; discriminate).
    destruct (IHx1 y1); [ subst | right; congruence ].
    destruct (IHx2 y2); subst; constructor; congruence.
  - destruct y; try (constructor; discriminate).
    destruct (IHx1 y1); [ subst | right; congruence ].
    destruct (IHx2 y2); subst; constructor; congruence.
Qed.

Lemma expr_eqb_refl: forall e, expr_eqb e e = true.
Proof.
  induction e; (try reflexivity);
    cbn; auto;
    auto using andb_true_intro, Bool.eqb_reflx,
    N.eqb_refl, Nat.eqb_refl, Pos.eqb_refl,
    Pointer.eqb_refl.
Qed.
#[global] Hint Immediate expr_eqb_refl: deep_gallinac.
#[global] Hint Rewrite expr_eqb_refl: deep_gallinac.

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
  - destruct (IHx y) as [ Heq | Hneq ];
      subst; constructor; congruence.
  - destruct (IHx1 y1), (IHx2 y2); subst; constructor; congruence.
  - destruct (IHx1 y1), (IHx2 y2); subst; constructor; congruence.
Qed.

Lemma expr_eqb_eq: forall x y, expr_eqb x y = true <-> x = y.
Proof.
  intros x y; split; intros H.
  - destruct (expr_eqb_spec x y); congruence.
  - subst. apply expr_eqb_refl.
Qed.
#[global] Hint Resolve expr_eqb_eq: deep_gallinac.

Lemma expr_eqb_neq: forall x y, expr_eqb x y = false <-> x <> y.
Proof.
  intros x y; split; intros H.
  - intros contra; subst.
    rewrite expr_eqb_refl in H.
    discriminate.
  - destruct (expr_eqb_spec x y); congruence.
Qed.
#[global] Hint Resolve expr_eqb_neq: deep_gallinac.

Fixpoint eval (e: expr) (env: map_ctxt value): option value :=
  match e with
  | e_var id => Maps.PTree.get id env
  | e_tt => Some v_tt
  | e_bool b => Some (v_bool b)
  | e_nat n => Some (v_nat n)
  | e_ofst o => Some (v_ofst o)
  | e_nullptr => Some (v_ptr Pointer.NULL)
  | e_neg e =>
      match eval e env with
      | Some (v_bool b) => Some (v_bool (negb b))
      | _ => None
      end
  | e_plus e_l e_r =>
      match eval e_l env, eval e_r env with
      | Some (v_nat v_l), Some (v_nat v_r) =>
          Some (v_nat (Unsigned.add v_l v_r))
      | _, _ => None
      end
  | e_nat_eq e_l e_r =>
      match eval e_l env, eval e_r env with
      | Some (v_nat v_l), Some (v_nat v_r) =>
          Some (v_bool (Unsigned.eqb v_l v_r))
      | _, _ => None
      end
  end.

Inductive wt_expr (ctxt : map_ctxt (type * bool)) : expr -> type -> Prop :=
| wt_var : forall var_id t
                  (Hget_env: PTree.get var_id ctxt = Some (t,true))
                  (Hground: ground t),
    wt_expr ctxt (e_var var_id) t
| wt_tt : wt_expr ctxt e_tt t_unit
| wt_bool : forall b, wt_expr ctxt (e_bool b) t_bool
| wt_nat : forall (n: nat) (Hbounded: Intops.Unsigned.Bounded n), wt_expr ctxt (e_nat n) t_nat
| wt_ofst : forall (n: N) (Hbounded: Intops.Unsigned.Bounded n), wt_expr ctxt (e_ofst n) t_ofst
| wt_nullptr : wt_expr ctxt e_nullptr t_ptr
| wt_neg : forall b (Hwt_expr_b: wt_expr ctxt b t_bool), wt_expr ctxt (e_neg b) t_bool
| wt_plus : forall l r
                   (Hwt_expr_l: wt_expr ctxt l t_nat)
                   (Hwt_expr_r: wt_expr ctxt r t_nat),
    wt_expr ctxt (e_plus l r) t_nat
| wt_nat_eq : forall l r
                     (Hwt_expr_l: wt_expr ctxt l t_nat)
                     (Hwt_expr_r: wt_expr ctxt r t_nat),
    wt_expr ctxt (e_nat_eq l r) t_bool
.

Fixpoint type_expr (env: map_ctxt (type * bool)) (e: expr): option type :=
  match e with
  | e_var var_id =>
      match Maps.PTree.get var_id env with
      | Some ((t_unit|t_bool|t_nat|t_ofst|t_ptr) as t, true) => Some t
      | _ => None
      end
  | e_tt => Some t_unit
  | e_bool _ => Some t_bool
  | e_nat n =>
      if Nat.leb n Unsigned.max_unsigned then
        Some t_nat
      else
        None
  | e_ofst o =>
      if N.leb o Unsigned.max_unsigned then
        Some t_ofst
      else
        None
  | e_nullptr => Some t_ptr
  | e_neg e =>
      match type_expr env e with
      | Some t_bool => Some t_bool
      | _ => None
      end
  | e_plus l r =>
      match type_expr env l, type_expr env r with
      | Some t_nat, Some t_nat => Some t_nat
      | _, _ => None
      end
  | e_nat_eq l r =>
      match type_expr env l, type_expr env r with
      | Some t_nat, Some t_nat => Some t_bool
      | _, _ => None
      end
  end.

Module Facts.

  Lemma expr_of_value_fun v e1 e2 (Heov1: expr_of_value v e1) (Heov2: expr_of_value v e2): e2 = e1.
  Proof.
    inversion Heov1; subst; inversion Heov2; subst; reflexivity.
  Qed.
  #[global] Hint Resolve expr_of_value_fun: deep_gallinac.

  Lemma expr_eqb_correct: forall e1 e2, e1 = e2 -> expr_eqb e1 e2 = true.
  Proof.
    apply expr_eqb_eq.
  Qed.
  #[global] Hint Resolve expr_eqb_correct: deep_gallinac.

  Lemma expr_eqb_complete: forall e1 e2, expr_eqb e1 e2 = true -> e1 = e2.
  Proof.
    apply expr_eqb_eq.
  Qed.
  #[global] Hint Resolve expr_eqb_complete: deep_gallinac.

  Lemma expr_eqb_neq_correct: forall e1 e2, e1 <> e2 -> expr_eqb e1 e2 = false.
  Proof.
    apply expr_eqb_neq.
  Qed.
  #[global] Hint Resolve expr_eqb_neq_correct: deep_gallinac.

  Lemma expr_eqb_neq_complete: forall e1 e2, expr_eqb e1 e2 = false -> e1 <> e2.
  Proof.
    apply expr_eqb_neq.
  Qed.
  #[global] Hint Resolve expr_eqb_complete: deep_gallinac.

  Lemma type_expr_spec: forall env e t, wt_expr env e t <-> type_expr env e = Some t.
  Proof.
    split; [ intros WT | intros EQ ].
    - revert t WT.
      induction e; intros; cbn;
        (try (now inversion WT; subst)).
      + now inversion WT; subst;
          inversion Hground; subst;
          rewrite Hget_env.
      + inversion WT as [ | | |?n [_ LE]| | | | | ]; subst;
          rewrite Uint32.Facts.LE in LE;
          destruct (Nat.leb_spec n Unsigned.max_unsigned); [ easy | lia ].
      + inversion WT as [ | | | | ?o [_ LE]| | | | ]; subst.
        destruct (N.leb_spec ofst Unsigned.max_unsigned); [ easy | assert ((ofst <= Unsigned.max_unsigned)%N) by apply LE; lia ].
      + now inversion WT; subst; rewrite (IHe _ Hwt_expr_b).
      + now inversion WT; subst;
          rewrite (IHe1 _ Hwt_expr_l), (IHe2 _ Hwt_expr_r).
      + now inversion WT; subst;
          rewrite (IHe1 _ Hwt_expr_l), (IHe2 _ Hwt_expr_r).
    - revert t EQ.
      induction e; cbn; intros;
        (try (now inversion EQ; subst; constructor)).
      + constructor;
          destruct (env ! i) as [[[] []] | ] eqn:Eget;
          try congruence; inversion EQ; subst; constructor.
      + destruct (Nat.leb_spec n Unsigned.max_unsigned); inversion EQ; subst; clear EQ.
        constructor.
        constructor; [ apply Nat.le_0_l | apply H ].
      + destruct (N.leb_spec ofst Unsigned.max_unsigned); inversion EQ; subst; clear EQ.
        constructor.
        constructor; [ apply N.le_0_l | apply H].
      + destruct (type_expr env e) as [[]|]; try discriminate.
        inversion EQ; subst.
        constructor.
        now apply IHe.
      + destruct (type_expr env e1) as [[]|]; try discriminate.
        destruct (type_expr env e2) as [[]|]; try discriminate.
        inversion EQ; subst; clear EQ.
        constructor. now apply IHe1. now apply IHe2.
      + destruct (type_expr env e1) as [[]|]; try discriminate.
        destruct (type_expr env e2) as [[]|]; try discriminate.
        inversion EQ; subst; constructor.
        now apply IHe1.
        now apply IHe2.
  Qed.

  Lemma wt_value_expr_agree: forall ctxt v e t_v t_e, expr_of_value v e -> wt_value v t_v -> wt_expr ctxt e t_e -> t_v = t_e.
  Proof.
    intros pctxt v e t_v t_e eov wt_v wt_e;
      inversion eov; subst;
      inversion wt_v; subst;
      inversion wt_e; subst;
      reflexivity.
  Qed.
  #[global] Hint Resolve wt_value_expr_agree: deep_gallinac.

  Lemma wt_expr_fun: forall ctxt e t1 t2,
      wt_expr ctxt e t1 -> wt_expr ctxt e t2 -> t1 = t2.
  Proof.
    intros ctxt e t1 t2 Hwt1 Hwt2.
    inversion Hwt1; subst; inversion Hwt2; subst; congruence.
  Qed.
  #[global] Hint Resolve wt_expr_fun: deep_gallinac.

  Lemma wt_expr_ground: forall ctxt e t,
      wt_expr ctxt e t -> ground t.
  Proof.
    intros ctxt e t Hwt.
    induction Hwt; auto; constructor.
  Qed.
  #[global] Hint Resolve wt_expr_ground: deep_gallinac.

  Lemma wt_expr_not_nonground: forall ctxt e t,
      wt_expr ctxt e t -> Types.nonground t -> False.
  Proof.
    intros ctxt e t Hwt Hnonground.
    assert (Hground: ground t) by apply (wt_expr_ground _ _ _ Hwt).
    apply (Types.ground_nonground_exclude _ Hground Hnonground).
  Qed.
  #[global] Hint Resolve wt_expr_not_nonground: deep_gallinac.

End Facts.
