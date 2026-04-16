From Stdlib Require Export Arith Psatz.

Lemma interval_split:
  forall (P: _ -> Prop) lo mid hi,
    (lo <= mid < hi) ->
    (forall n, (lo <= n < mid) -> P n) ->
    (forall n, (mid <= n < hi) -> P n) ->
    forall n, (lo <= n < hi) -> P n.
Proof.
  intros P lo mid hi [ Hloltmid Hmidlthi ] Hfirst Hsecond z [ Hlolez Hzlthi ].
  destruct (Nat.lt_trichotomy z mid) as [ Hlt | [ Heq | Hgt ] ];
    subst.
  now apply Hfirst.
  now apply Hsecond.
  apply Hsecond.
  lia.
Qed.

Lemma mod_add_sub: forall a b c, (0 < c -> a < c -> b < c -> c < a + b -> (a + b) mod c = a + b - c)%nat.
Proof.
  induction a.
  - cbn. intros b c H0ltc _ Hbltc Hcltb.
    lia.
  - cbn.
    intros b c H0ltc HSaltc Hbltc HcltSab.
    destruct c; try (lia).
    destruct (Nat.ltb_spec (S b) (S c)).
    + specialize (IHa (S b) (S c) ltac:(assumption) ltac:(lia) ltac:(assumption) ltac:(lia) ).
      rewrite Nat.add_succ_r, Nat.sub_succ in IHa.
      apply IHa.
    + assert (Hcltb: (c <= b)%nat) by lia.
      assert (b = c) by lia; subst.
      rewrite Nat.add_sub, <- Nat.add_succ_r.
      rewrite <- Nat.Div0.add_mod_idemp_r, Nat.Div0.mod_same, Nat.add_0_r.
      apply Nat.mod_small.
      lia.
Qed.

Lemma nat_ind2 (P : nat -> Prop) :
  P 0 -> P 1 ->
  (forall n, P n -> P (S n) -> P (S (S n))) ->
  forall n, P n.
Proof.
  intros H0 H1 Hstep n.
  enough (P n /\ P (S n)) by (now eauto).
  now induction n as [ | n [ IHn IHSn ] ]; eauto.
Qed.

Fixpoint iter_opt [A: Type] (f: A -> option A) (n: nat) (a: A): option A :=
  match n with
  | 0 => Some a
  | S n =>
      match f a with
      | Some a => iter_opt f n a
      | None => None
      end
  end.
