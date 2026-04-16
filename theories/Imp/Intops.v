From Stdlib Require Import PArith Arith.

From GallinaC.Utils Require Import ReflectExt.

Declare Scope int_scope.
Local Open Scope int_scope.
Delimit Scope int_scope with int.

Create HintDb ints.

(* Types which are well-adapted to implement C integers *)
Module IntCarrier.

  Structure IntCarrier :=
    {
      carrier :> Type;

      zero: carrier;
      succ: carrier -> carrier;
      pred: carrier -> carrier;

      inj_pos: positive -> carrier;

      le: carrier -> carrier -> Prop;

      add: carrier -> carrier -> carrier;
      sub: carrier -> carrier -> carrier;
      mul: carrier -> carrier -> carrier;
      pow: carrier -> carrier -> carrier;
      modulo: carrier -> carrier -> carrier;
      eqb: carrier -> carrier -> bool;

      succ_inj: forall (a b: carrier), succ a = succ b -> a = b;
      succ_induction: forall (A : carrier -> Prop), A zero -> (forall a, A a -> A (succ a)) -> forall a, A a;

      pred_succ: forall (a: carrier), pred (succ a) = a;
      succ_pred: forall (a: carrier) (Hpos: le (succ zero) a), succ (pred a) = a;

      le_refl: forall (a : carrier), le a a;
      le_succ: forall (a b : carrier), le a b -> le a (succ b);
      le_trans: forall (a b c : carrier), le a b -> le b c -> le a c;
      le_ind: forall (a : carrier) (P : carrier -> Prop), P a -> (forall b, le a b -> P b -> P (succ b)) -> forall c, le a c -> P c;

      add_comm: forall (a b: carrier), add a b = add b a;
      add_assoc: forall (a b c: carrier), add (add a b) c = add a (add b c);
      add_0_l: forall (a: carrier), add zero a = a;
      add_S_l: forall (a b: carrier), add (succ a) b = succ (add a b);

      sub_0_r: forall (a: carrier), sub a zero = a;
      sub_S_r: forall (a b: carrier), sub a (succ b) = pred (sub a b);

      mul_comm: forall (a b: carrier), mul a b = mul b a;
      mul_assoc: forall (a b c: carrier), mul (mul a b) c = mul a (mul b c);
      mul_0_l: forall (a: carrier), mul zero a = zero;
      mul_S_l: forall (a b: carrier), mul (succ a) b = add (mul a b) b;

      add_mul_dist: forall (a b c: carrier), mul a (add b c) = add (mul a b) (mul a c);

      pow_0_r: forall (a : carrier), pow a zero = succ zero;
      pow_S_r: forall (a b: carrier), pow a (succ b) = mul (pow a b) a;

      mod_le: forall (a b: carrier), le (succ zero) b -> le (succ (modulo a b)) b;
      mod_small: forall (a b: carrier), le (succ zero) b -> le (succ a) b -> modulo a b = a;

      eqb_spec: forall (a b: carrier), reflect (a = b) (eqb a b);

      inj_pos_inj: forall (p q: positive), inj_pos p = inj_pos q -> p = q;
      inj_pos_xO: forall (p: positive), inj_pos (p~0) = mul (succ (succ zero)) (inj_pos p);
      inj_pos_xI: forall (p: positive), inj_pos (p~1) = succ (mul (succ (succ zero)) (inj_pos p));
      inj_pos_one: inj_pos 1%positive = succ zero;
      inj_pos_succ: forall (p: positive), inj_pos (Pos.succ p) = succ (inj_pos p);
      inj_pos_add: forall (p q: positive), inj_pos (p + q)%positive = add (inj_pos p) (inj_pos q);
      inj_pos_mul: forall (p q : positive), inj_pos (p * q)%positive = mul (inj_pos p) (inj_pos q);
    }.

  Arguments carrier IC: rename, simpl never.
  Arguments zero IC: rename, simpl never.
  Arguments succ {IC} a: rename, simpl never.
  Arguments pred {IC} a: rename, simpl never.
  Arguments inj_pos {IC} p: rename, simpl never.
  Arguments le {IC} a b: rename, simpl never.
  Arguments add {IC} a b: rename, simpl never.
  Arguments sub {IC} a b: rename, simpl never.
  Arguments mul {IC} a b: rename, simpl never.
  Arguments pow {IC} a b: rename, simpl never.
  Arguments modulo {IC} a b: rename, simpl never.
  Arguments eqb {IC} a b: rename, simpl never.
  Arguments succ_inj {IC} a b: rename, simpl never.
  Arguments succ_induction IC a: rename, simpl never.
  Arguments pred_succ {IC} a: rename, simpl never.
  Arguments succ_pred {IC} a: rename, simpl never.
  Arguments le_refl {IC} a: rename, simpl never.
  Arguments le_succ {IC} a b: rename, simpl never.
  Arguments le_trans {IC} a b c Hltab Hltbc: rename, simpl never.
  Arguments le_ind IC: rename, simpl never.
  Arguments add_comm {IC} a b: rename, simpl never.
  Arguments add_assoc {IC} a b c: rename, simpl never.
  Arguments add_0_l {IC} a: rename, simpl never.
  Arguments add_S_l {IC} a b: rename, simpl never.
  Arguments sub_0_r {IC} a: rename, simpl never.
  Arguments sub_S_r {IC} a b: rename, simpl never.
  Arguments mul_comm {IC} a b: rename, simpl never.
  Arguments mul_assoc {IC} a b c: rename, simpl never.
  Arguments mul_0_l {IC} a: rename, simpl never.
  Arguments mul_S_l {IC} a b: rename, simpl never.
  Arguments add_mul_dist {IC} a b c: rename, simpl never.
  Arguments pow_0_r {IC} a: rename, simpl never.
  Arguments pow_S_r {IC} a b: rename, simpl never.
  Arguments mod_le {IC} a b Hmodpos: rename, simpl never.
  Arguments mod_small {IC} a b Hmodpos Hltab: rename, simpl never.
  Arguments eqb_spec {IC} a b: rename, simpl never.
  Arguments inj_pos_inj {IC} p q Heq: rename, simpl never.
  Arguments inj_pos_xO {IC} p: rename, simpl never.
  Arguments inj_pos_xI {IC} p: rename, simpl never.
  Arguments inj_pos_one {IC}: rename, simpl never.
  Arguments inj_pos_succ {IC} p: rename, simpl never.
  Arguments inj_pos_add {IC} p q: rename, simpl never.
  Arguments inj_pos_mul {IC} p q: rename, simpl never.

  #[global] Hint Resolve
    succ_inj pred_succ succ_pred
    le_refl le_succ le_trans
    add_comm add_assoc add_0_l add_S_l
    mul_comm mul_assoc mul_0_l mul_S_l
    add_mul_dist
    pow_0_r pow_S_r
    mod_le mod_small
    inj_pos_inj inj_pos_xO inj_pos_xI inj_pos_one inj_pos_succ inj_pos_add inj_pos_mul: ints.

  #[global] Hint Rewrite
    @pred_succ @succ_pred
    @add_0_l @add_S_l @mul_0_l
    @mod_small: ints.

  Module Facts.

    Definition one (IC: IntCarrier) := succ (zero IC).
    #[global] Hint Unfold one: ints.

    Definition two (IC: IntCarrier) := succ (succ (zero IC)).
    #[global] Hint Unfold two: ints.

    Definition lt {IC: IntCarrier} (a b: carrier IC) := le (succ a) b.
    #[global] Hint Unfold lt: ints.

    Lemma lt_0 {IC: IntCarrier} (a: carrier IC): lt a (succ a).
    Proof.
      eauto with ints.
    Qed.
    #[global] Hint Resolve lt_0: ints.

    Lemma lt_S {IC: IntCarrier} (a b: carrier IC) (Hlt: lt a b): lt a (succ b).
    Proof.
      eauto with ints.
    Qed.
    #[global] Hint Resolve lt_S: ints.

    Lemma le_0 {IC: IntCarrier} (a: carrier IC): le (zero IC) a.
    Proof.
      induction a using succ_induction; eauto with ints.
    Qed.
    #[global] Hint Resolve le_0: ints.

    Lemma le_0_S {IC: IntCarrier} (a: carrier IC): le (zero _) (succ a).
    Proof.
      induction a using @succ_induction;
        eauto with ints.
    Qed.
    #[global] Hint Resolve le_0_S: ints.

    Lemma lt_0_S {IC: IntCarrier} (a: carrier IC): lt (zero _) (succ a).
    Proof.
      induction a using (@succ_induction IC); eauto with ints.
    Qed.
    #[global] Hint Resolve lt_0_S: ints.

    Lemma lt_S_r {IC: IntCarrier} (a b: carrier IC): lt a b -> lt a (succ b).
    Proof.
      eauto with ints.
    Qed.
    #[global] Hint Resolve lt_S_r: ints.

    Lemma le_n_S {IC: IntCarrier} (a b: carrier IC) (Hle: le a b): le (succ a) (succ b).
    Proof.
      induction Hle using le_ind; eauto with ints.
    Qed.
    #[global] Hint Resolve le_n_S: ints.

    Lemma le_S_lt {IC: IntCarrier} (a b: carrier IC) (Hle: le a b): lt a (succ b).
    Proof.
      eauto with ints.
    Qed.
    #[global] Hint Resolve le_S_lt: ints.

    Lemma lt_S_le {IC: IntCarrier} (a b: carrier IC): lt a (succ b) -> le a b.
    Proof.
      intros Hlt.
      remember (succ b) as sb eqn:Heq.
      induction Hlt using le_ind;
        apply succ_inj in Heq; subst; eauto with ints.
    Qed.
    #[global] Hint Resolve lt_S_le: ints.

    Lemma lt_pred_pos {IC: IntCarrier} (a: carrier IC) (Hlt: lt (zero IC) a): lt (pred a) a.
    Proof.
      induction Hlt using le_ind;
        rewrite pred_succ; eauto with ints.
    Qed.
    #[global] Hint Resolve lt_pred_pos: ints.

    Lemma le_a_S {IC: IntCarrier} (a b: carrier IC) (Hle: le a b): le (succ a) (succ b).
    Proof.
      induction Hle using le_ind; eauto with ints.
    Qed.
    #[global] Hint Resolve le_a_S: ints.

    Lemma succ_of_pos {IC: IntCarrier} (a: carrier IC) (Hpos: lt (zero IC) a): exists b, a = succ b.
    Proof.
      remember (zero IC) as Z eqn:Heq.
      induction Hpos using le_ind; subst;
        eexists; auto.
    Qed.
    #[global] Hint Resolve succ_of_pos: ints.

    Lemma pred_sub {IC: IntCarrier} (a: carrier IC): pred a = sub a (one _).
    Proof.
      now unfold one; rewrite sub_S_r, sub_0_r.
    Qed.
    #[global] Hint Resolve pred_sub: ints.

    Lemma add_0_r {IC: IntCarrier} (a: carrier IC): add a (zero _) = a.
    Proof.
      rewrite add_comm; now apply add_0_l.
    Qed.
    #[global] Hint Resolve add_0_r: ints.
    #[global] Hint Rewrite @add_0_r: ints.

    Lemma add_S_r {IC: IntCarrier} (a b: IC): add a (succ b) = succ (add a b).
    Proof.
      rewrite (add_comm a (succ b)), (add_comm a b); now apply add_S_l.
    Qed.
    #[global] Hint Resolve add_S_r: ints.
    #[global] Hint Rewrite @add_S_r: ints.

    Lemma mul_0_r {IC: IntCarrier} (a: carrier IC): mul a (zero _) = zero _.
    Proof.
      rewrite mul_comm; now apply mul_0_l.
    Qed.
    #[global] Hint Resolve mul_0_r: ints.
    #[global] Hint Rewrite @mul_0_r: ints.

    Lemma mul_S_r {IC: IntCarrier} (a b: carrier IC): mul a (succ b) = add (mul a b) a.
    Proof.
      rewrite (mul_comm a (succ b)), (mul_comm a b); now apply mul_S_l.
    Qed.
    #[global] Hint Resolve mul_S_r: ints.

    Lemma pow_0_l {IC: IntCarrier} (a: carrier IC) (Hnonzero: lt (zero IC) a): pow (zero IC) a = zero IC.
    Proof.
      remember (zero IC) as Z eqn:Heq.
      induction Hnonzero using le_ind; subst;
      now rewrite pow_S_r, mul_0_r.
    Qed.
    #[global] Hint Resolve pow_0_l: ints.
    #[global] Hint Rewrite @pow_0_l: ints.

    Lemma pow_1_l {IC: IntCarrier} (a: carrier IC): pow (one IC) a = one IC.
    Proof.
      induction a using (@succ_induction IC).
      now rewrite pow_0_r.
      rewrite pow_S_r.
      unfold one at 2.
      now rewrite mul_S_r, mul_0_r, add_0_l, IHa.
    Qed.
    #[global] Hint Resolve pow_1_l: ints.
    #[global] Hint Rewrite @pow_1_l: ints.

    Lemma pow_add_r {IC: IntCarrier} (a b c: carrier IC): pow a (add b c) = mul (pow a b) (pow a c).
    Proof.
      revert a c.
      induction b using (@succ_induction IC);
        intros.
      - now rewrite add_0_l, pow_0_r, mul_S_l, mul_0_l, add_0_l.
      - rewrite add_S_l.
        repeat (rewrite pow_S_r).
        rewrite (mul_comm (pow a b) a).
        specialize (IHb a c).
        rewrite mul_assoc.
        rewrite mul_comm.
        f_equal.
        apply IHb.
    Qed.
    #[global] Hint Resolve pow_add_r: ints.

    Lemma add_nonneg_nonneg_nonneg {IC: IntCarrier} (a b: carrier IC)
      (Hnonnega: le (zero _) a) (Hnonnegb: le (zero _) b)
      : le (zero _) (add a b).
    Proof.
      revert a b Hnonnega Hnonnegb.
      eauto with ints.
    Qed.
    #[global] Hint Resolve add_nonneg_nonneg_nonneg: ints.

    Lemma add_pos_pos_pos {IC: IntCarrier} (a b: carrier IC)
      (Hlta: lt (zero _) a) (Hltb: lt (zero _) b):
      lt (zero _) (add a b).
    Proof.
      revert a b Hlta Hltb.
      induction a using (@succ_induction IC);
        intros.
      now rewrite add_0_l.
      rewrite add_S_l; apply lt_0_S.
    Qed.
    #[global] Hint Resolve add_pos_pos_pos: ints.

    Lemma add_nonneg_pos_pos {IC: IntCarrier} (a b: carrier IC)
      (Hnonnega: le (zero _) a) (Hposb: lt (zero _) b)
      : lt (zero _) (add a b).
    Proof.
      remember (zero IC) as Z eqn:Heq.
      induction Hnonnega using le_ind; subst.
      now rewrite add_0_l.
      eauto with ints.
    Qed.

    Lemma inj_pos_pos {IC: IntCarrier} (p: positive): lt (zero IC) (inj_pos p).
    Proof.
      induction p.
      - rewrite inj_pos_xI.
        apply lt_0_S.
      - rewrite inj_pos_xO.
        repeat (rewrite mul_S_l); rewrite mul_0_l.
        rewrite add_0_l.
        apply add_pos_pos_pos; auto.
      - rewrite inj_pos_one; apply lt_0_S.
    Qed.
    #[global] Hint Resolve inj_pos_pos: ints.

    Lemma mul_pos_pos_pos {IC: IntCarrier} (a b: carrier IC)
      (Hposa: lt (zero _) a) (Hposb: lt (zero _) b)
      : lt (zero _) (mul a b).
    Proof.
      revert b Hposb.
      induction Hposa using le_ind; intros.
      now rewrite mul_S_l, mul_0_l, add_0_l.
      rewrite mul_S_l. eauto with ints.
    Qed.
    #[global] Hint Resolve mul_pos_pos_pos: ints.

    Lemma pow_pos_pos_pos {IC: IntCarrier} (a b: carrier IC)
      (Hposa: lt (zero _) a) (Hposb: lt (zero _) b)
      : lt (zero _) (pow a b).
    Proof.
      remember (zero IC) as Z eqn:Heq.
      revert a Hposa.
      induction Hposb using le_ind; subst; intros.
      now rewrite pow_S_r, pow_0_r, mul_S_l, mul_0_l, add_0_l.
      rewrite pow_S_r. eauto with ints.
    Qed.
    #[global] Hint Resolve pow_pos_pos_pos: ints.

    Lemma mod_mod {IC: IntCarrier} (a n: carrier IC)
      (LEn: le (succ (zero IC)) n)
      : modulo (modulo a n) n = modulo a n.
    Proof.
      eauto with ints.
    Qed.
    #[global] Hint Resolve mod_mod: ints.

    Lemma eqb_refl {IC: IntCarrier} (a: carrier IC)
      : eqb a a = true.
    Proof.
      destruct (eqb_spec a a); congruence.
    Qed.
    #[global] Hint Resolve eqb_refl: ints.

    Lemma eqb_symm {IC: IntCarrier} (a b: carrier IC)
      : eqb a b = eqb b a.
    Proof.
      destruct (eqb_spec a b), (eqb_spec b a); congruence.
    Qed.
    #[global] Hint Resolve eqb_symm: ints.

  End Facts.

  Module Notations.

    Import Facts.

    Notation ":0" := (zero _) (at level 0): int_scope.
    Notation ":1" := (one _) (at level 0): int_scope.
    Notation ":2" := (two _) (at level 0): int_scope.

    Notation "a < b" := (lt a b): int_scope.
    Notation "a <= b" := (le a b): int_scope.
    Notation "a < b < c" := (lt a b /\ lt b c): int_scope.
    Notation "a < b <= c" := (lt a b /\ le b c): int_scope.
    Notation "a <= b < c" := (le a b /\ lt b c): int_scope.
    Notation "a <= b <= c" := (le a b /\ le b c): int_scope.

    Notation "a :+: b" := (add a b) (at level 50): int_scope.
    Notation "a :*: b" := (mul a b) (at level 50): int_scope.
    Notation "a :^: b" := (pow a b) (at level 50): int_scope.
    Notation "a :%: b" := (modulo a b) (at level 50): int_scope.

    Notation "a :=?: b" := (eqb a b) (at level 70): int_scope.

  End Notations.

End IntCarrier.

(* How to implement an unsigned integer from an IntCarrier *)
Module Unsigned.

  Import IntCarrier IntCarrier.Notations IntCarrier.Facts.

  Structure Unsigned :=
    {
      carrier :> IntCarrier.IntCarrier;
      BW: positive;
    }.

  Arguments carrier UInt: rename, simpl never.
  Arguments BW UInt: rename, simpl never.

  Definition min_unsigned {UInt: Unsigned}: carrier UInt := zero _.
  Definition max_unsigned {UInt: Unsigned}: carrier UInt := pred (pow (Facts.two _) (inj_pos (BW UInt))).
  Definition modulus {UInt: Unsigned}: carrier UInt := pow (two _) (inj_pos (BW UInt)).

  Definition Bounded {UInt: Unsigned} (n: UInt): Prop := min_unsigned <= n <= max_unsigned.

  Definition add {UInt: Unsigned} (l r: UInt) := (l :+: r) :%: modulus.

  Definition eqb {UInt: Unsigned} (l r: UInt) := (l :%: modulus) :=?: (r :%: modulus).

  Arguments Bounded {UInt} n: rename, simpl never.
  Arguments add {UInt} l r: rename, simpl never.
  Arguments eqb {UInt} l r: rename, simpl never.

  Module Notations.

    Export IntCarrier.Notations.

    Notation "a + b" := (add a b): int_scope.
    Notation "a =? b" := (eqb a b): int_scope.

  End Notations.

  Module Facts.

    Remark modulus_pos {UInt: Unsigned}: one UInt <= modulus.
    Proof.
      unfold modulus.
      apply pow_pos_pos_pos;
        eauto with ints.
    Qed.
    #[global] Hint Resolve modulus_pos: ints.

    Lemma bounded_lt_modulus {UInt: Unsigned}: forall (n: UInt), Bounded n -> n < modulus.
    Proof.
      intros n [ _ Hle ].
      revert Hle.
      unfold max_unsigned, modulus.
      specialize (@succ_of_pos UInt (:2 :^: inj_pos (BW UInt)) ltac:(eauto with ints)) as (m & Heqm).
      rewrite Heqm.
      intros.
      rewrite pred_succ in Hle.
      unfold lt.
      now apply le_n_S.
    Qed.

    Theorem add_bounded {UInt: Unsigned} (l r: carrier UInt): Bounded (add l r).
    Proof.
      split.
      eapply le_0.
      unfold add, max_unsigned, modulus.
      specialize (mod_le (l :+: r) (:2 :^: inj_pos (BW UInt)) ltac:(eauto with ints)) as H.
      fold (lt ( (l :+: r) :%: (:2 :^: inj_pos (BW UInt))) (pow :2 (inj_pos (BW UInt)))) in H.
      eapply lt_S_le.
      rewrite succ_pred; eauto with ints.
    Qed.
    #[global] Hint Resolve add_bounded: ints.

    Theorem add_bounded_transparent {UInt: Unsigned} (l r: carrier UInt) (HBoundedAdd: Bounded ((IntCarrier.add) l r)): add l r = IntCarrier.add l r.
    Proof.
      unfold add, modulus.
      destruct HBoundedAdd as [ _ Hle ].
      unfold max_unsigned in Hle.
     apply mod_small; eauto with ints.
      specialize (@succ_of_pos UInt (:2 :^: inj_pos (BW UInt)) ltac:(eauto with ints)) as (m & Heqm).
      rewrite Heqm in Hle; rewrite Heqm.
      rewrite pred_succ in Hle.
      now apply le_n_S.
    Qed.
    #[global] Hint Resolve add_bounded_transparent: ints.

    Theorem eqb_refl {UInt: Unsigned} (a: carrier UInt):
      eqb a a = true.
    Proof.
      unfold eqb; eauto with ints.
    Qed.
    #[global] Hint Resolve eqb_refl: ints.

    Theorem eqb_symm {UInt: Unsigned} (l r: carrier UInt):
      eqb l r = eqb r l.
    Proof.
      unfold eqb; eauto with ints.
    Qed.
    #[global] Hint Resolve eqb_symm: ints.

    Theorem eqb_bounded {UInt: Unsigned} (l r: carrier UInt) (LB: Bounded l) (RB: Bounded r):
      eqb l r = IntCarrier.eqb l r.
    Proof.
      unfold eqb, modulus.
      destruct LB as [ _ LEl ].
      destruct RB as [ _ LEr ].
      unfold max_unsigned in *.
      specialize (@succ_of_pos UInt (:2 :^: inj_pos (BW UInt)) ltac:(eauto with ints)) as (m & Heqm).
      rewrite Heqm in LEl, LEr; rewrite Heqm.
      rewrite pred_succ in LEl, LEr.
      rewrite (mod_small l _), (mod_small r _); eauto with ints.
    Qed.
    #[global] Hint Resolve eqb_bounded: ints.

    Theorem eqb_bounded_transparent_l {UInt: Unsigned} (l r: carrier UInt): eqb (l :%: modulus) r = eqb l r.
    Proof.
      unfold eqb, modulus.
      rewrite mod_mod; eauto with ints.
    Qed.
    #[global] Hint Resolve eqb_bounded_transparent_l: ints.

    Theorem eqb_bounded_transparent_r {UInt: Unsigned} (l r: carrier UInt): eqb l (r :%: modulus) = eqb l r.
    Proof.
      rewrite (eqb_symm l (r :%: _)), (eqb_symm l r).
      apply eqb_bounded_transparent_l.
    Qed.
    #[global] Hint Resolve eqb_bounded_transparent_r: ints.

    Theorem bounded_mod_eq {UInt: Unsigned} (x: UInt): Bounded x -> x :%: modulus = x.
    Proof.
      intros [ _ Hle ].
      unfold max_unsigned in Hle.
      unfold modulus.
      specialize (@succ_of_pos UInt (:2 :^: inj_pos (BW UInt)) ltac:(eauto with ints)) as (m & Heqm).
      rewrite Heqm; rewrite Heqm in Hle.
      rewrite pred_succ in Hle.
      apply mod_small; eauto with ints.
    Qed.
    #[global] Hint Resolve bounded_mod_eq: ints.

  End Facts.

End Unsigned.
