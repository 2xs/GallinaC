From Stdlib Require Export NArith Psatz.

Local Open Scope N_scope.

Lemma interval_split:
  forall (P: _ -> Prop) lo mid hi,
    (lo <= mid < hi) ->
    (forall n, (lo <= n < mid) -> P n) ->
    (forall n, (mid <= n < hi) -> P n) ->
    forall n, (lo <= n < hi) -> P n.
Proof.
  intros P lo mid hi [ Hloltmid Hmidlthi ] Hfirst Hsecond z [ Hlolez Hzlthi ].
  destruct (N.lt_trichotomy z mid) as [ Hlt | [ Heq | Hgt ] ];
    subst.
  now apply Hfirst.
  now apply Hsecond.
  apply Hsecond.
  lia.
Qed.

Lemma mod_add_sub: forall a b c, (0 < c -> a < c -> b < c -> c < a + b -> (a + b) mod c = a + b - c)%N.
Proof.
  induction a using N.peano_ind.
  - cbn. intros b c H0ltc _ Hbltc Hcltb.
    lia.
  - intros b c. cbn.
    repeat (rewrite N.add_succ_l).
    intros H0ltc HSaltc Hbltc HcltSab.
    destruct (N.zero_or_succ c) as [ Heq | ( c' & Heqc ) ]; try (lia); subst.
    destruct (N.ltb_spec (N.succ b) (N.succ c')).
    + specialize (IHa (N.succ b) (N.succ c') ltac:(assumption) ltac:(lia) ltac:(assumption) ltac:(lia) ).
      rewrite N.add_succ_r, N.sub_succ in IHa.
      rewrite N.sub_succ.
      apply IHa.
    + assert (Hcltb: (c' <= b)) by lia.
      assert (b = c') by lia; subst.
      rewrite N.sub_succ.
      rewrite N.add_sub, <- N.add_succ_r.
      rewrite <- N.Div0.add_mod_idemp_r, N.Div0.mod_same, N.add_0_r.
      apply N.mod_small.
      lia.
Qed.
