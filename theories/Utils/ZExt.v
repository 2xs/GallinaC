From Stdlib Require Export ZArith Psatz.

Local Open Scope Z_scope.

Lemma interval_split:
  forall (P: _ -> Prop) lo mid hi,
    (lo <= mid < hi)%Z ->
    (forall z, (lo <= z < mid)%Z -> P z) ->
    (forall z, (mid <= z < hi)%Z -> P z) ->
    forall z, (lo <= z < hi) -> P z.
Proof.
  intros P lo mid hi [ Hloltmid Hmidlthi ] Hfirst Hsecond z [ Hlolez Hzlthi ].
  destruct (Z.lt_trichotomy z mid) as [ Hlt | [ Heq | Hgt ] ];
    subst.
  - now apply Hfirst.
  - now apply Hsecond.
  - apply Hsecond.
    lia.
Qed.
