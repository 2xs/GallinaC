From Stdlib Require Import PArith.

From compcert.lib Require Import Maps.

From GallinaC.Utils Require Import ListExt.

Lemma ptree_elements_remove_hd [A: Type] [p a elems] [tree: Maps.PTree.t A] (EQ: (p,a)::elems = Maps.PTree.elements tree): elems = Maps.PTree.elements (Maps.PTree.remove p tree).
Proof.
  destruct (Maps.PTree.elements_remove p (v := a) tree) as (l1 & l2 & EQ1 & EQ2).
  eapply Maps.PTree.elements_complete.
  rewrite <- EQ.
  now left.
  rewrite <- EQ in *.
  specialize (Maps.PTree.elements_keys_norepet tree) as NDup.
  apply list_no_repet_NoDup in NDup.
  apply NoDup_SBinds in NDup.
  assert (forall [A B: Type] [l: list (A * B)] [a b] (SBINDS: SBinds ((a,b)::l)) [l1 l2], (a, b) :: l = l1 ++ (a, b) :: l2 -> l1 = []).
  {
    clear; intros.
    revert l a b SBINDS l2 H.
    induction l1 as [ | [ a' b' ] l1 ]; [ reflexivity | intros ].
    inversion H; subst.
    inversion SBINDS; subst.
    exfalso; eapply AbsBind_In_False.
    apply H2.
    apply in_elt.
  }
  rewrite <- EQ in NDup.
  specialize (H _ _ _ _ _ NDup _ _ EQ1) as EQ'.
  subst; cbn in *.
  inversion EQ1; subst; clear EQ1.
  reflexivity.
Qed.

Lemma ptree_elements_nil [A: Type] [tree: PTree.t A] (EQ: PTree.elements tree = []): tree = PTree.empty A.
Proof.
  change (PTree.elements tree) with (PTree.xelements tree xH) in EQ.
  revert EQ.
  destruct tree; [ reflexivity |  ].
  cbn.
  generalize 1%positive as k.
  generalize ([]: list (positive * A)) at 1 as l.
  intros.
  exfalso.
  revert l k EQ.
  induction t; cbn; intros;
    first
      [ now eapply IHt, EQ
      | discriminate
      | auto ].
  - eapply IHt1, EQ.
  - eapply IHt1, EQ.
Qed.
