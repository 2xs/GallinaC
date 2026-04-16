From MetaRocq.Utils Require Export bytestring.

Open Scope bs_scope.

Lemma byte_eqb_eq (b1 b2 : Byte.byte) :
ByteCompare.eqb b1 b2 = true <-> b1 = b2.
Proof.
rewrite ByteCompareSpec.eqb_compare.
destruct (ByteCompare.compare b1 b2) eqn: Heq.
- apply ByteCompareSpec.compare_eq in Heq.
  tauto.
- split; [intros [=] | ].
  intro Heq'; subst b2.
  rewrite ByteCompareSpec.compare_eq_refl in Heq.
  discriminate.
- split; [intros [=] | ].
  intro Heq'; subst b2.
  rewrite ByteCompareSpec.compare_eq_refl in Heq.
  discriminate.
Qed.

Lemma byte_eqb_neq (b1 b2 : Byte.byte) :
ByteCompare.eqb b1 b2 = false <-> b1 <> b2.
Proof.
rewrite ByteCompareSpec.eqb_compare.
destruct (ByteCompare.compare b1 b2) eqn: Heq.
- apply ByteCompareSpec.compare_eq in Heq.
  split; [intros [=] | ].
  contradiction.
- split; [intros _ | trivial].
  contradict Heq.
  subst b2.
  rewrite ByteCompareSpec.compare_eq_refl.
  discriminate.
- split; [intros _ | trivial].
  contradict Heq.
  subst b2.
  rewrite ByteCompareSpec.compare_eq_refl.
  discriminate.
Qed.

Lemma bs_eqb_eq (s1 s2 : string) : String.eqb s1 s2 = true <-> s1 = s2.
Proof.
revert s2.
induction s1 as [ | b1 s1' IH]; intros [ | b2 s2']; cbn.
- tauto.
- split; discriminate.
- split; discriminate.
- destruct (ByteCompare.eqb b1 b2) eqn: Heq.
  + apply byte_eqb_eq in Heq.
    rewrite Heq, IH.
    split; [congruence | ].
    intros [=]; assumption.
  + apply byte_eqb_neq in Heq.
    split; [intros [=] | ].
    intros [=]; contradiction.
Qed.

Lemma bs_eqb_neq (s1 s2 : string) : String.eqb s1 s2 = false <-> s1 <> s2.
Proof.
revert s2.
induction s1 as [ | b1 s1' IH]; intros [ | b2 s2']; cbn.
- split; [intros [=] | ].
  intros [].
  reflexivity.
- split; congruence.
- split; congruence.
- destruct (ByteCompare.eqb b1 b2) eqn: Heq.
  + apply byte_eqb_eq in Heq.
    rewrite Heq, IH.
    split; congruence.
  + apply byte_eqb_neq in Heq.
    split; congruence.
Qed.

Lemma bs_eqb_refl (s : String.t) : String.eqb s s = true.
Proof.
  apply bs_eqb_eq; auto.
Qed.
