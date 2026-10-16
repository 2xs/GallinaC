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

From Stdlib Require Import PArith.

From compcert.lib Require Import Maps.

From HB Require Import structures.

From GallinaC.Utils Require Import Algebra ListExt ReflectExt.

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

Lemma ptree_beq_spec [A: Type] [eqb: A -> A -> bool]
  (eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y))
  (m1 m2: Maps.PTree.t A) : Bool.reflect (m1 = m2) (Maps.PTree.beq eqb m1 m2).
Proof.
  destruct (Maps.PTree.beq eqb m1 m2) eqn:E; constructor.
  - apply Maps.PTree.extensionality. intro x.
    pose proof (proj1 (Maps.PTree.beq_correct eqb m1 m2) E x) as Ex.
    destruct (Maps.PTree.get x m1) as [y1|], (Maps.PTree.get x m2) as [y2|];
      try contradiction.
    + f_equal. destruct (eqb_spec y1 y2); [assumption | discriminate Ex].
    + reflexivity.
  - intro Heq; subst m2.
    enough (Maps.PTree.beq eqb m1 m1 = true) by congruence.
    apply Maps.PTree.beq_correct. intro x.
    destruct (Maps.PTree.get x m1); [apply (reflect_refl eqb_spec) | exact I].
Qed.

HB.instance Definition _ (A: EqDec.type) :=
  hasEqDec.Build (Maps.PTree.t A) (Maps.PTree.beq (@Algebra.eqb A)) (ptree_beq_spec (@Algebra.eqb_spec A)).

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

Lemma pure_set_true_incl [A: Type] (pm: Maps.PTree.t (A * bool)) id (ty: A) b
  (GET: Maps.PTree.get id pm = Some (ty, b)):
  forall id' ty', Maps.PTree.get id' pm = Some (ty', true) ->
                  Maps.PTree.get id' (Maps.PTree.set id (ty, true) pm) = Some (ty', true).
Proof.
  intros id' ty' GET'.
  destruct (Coqlib.peq id' id) as [ -> | NE ].
  - rewrite GET in GET'; injection GET' as <- <-.
    apply Maps.PTree.gss.
  - rewrite Maps.PTree.gso by assumption; exact GET'.
Qed.
