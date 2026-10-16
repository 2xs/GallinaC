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

From MetaRocq.Utils Require Export bytestring.
From MetaRocq.Common Require Kernames.
From HB Require Import structures.

From GallinaC.Utils Require Import Algebra.

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

Lemma bs_eqb_spec (s1 s2 : string) : Bool.reflect (s1 = s2) (String.eqb s1 s2).
Proof.
  apply Bool.iff_reflect, iff_sym, bs_eqb_eq.
Qed.

HB.instance Definition _ := hasEqDec.Build string String.eqb bs_eqb_spec.

Lemma kername_eqb_spec (k1 k2 : Kernames.kername)
  : Bool.reflect (k1 = k2) (Kernames.Kername.eqb k1 k2).
Proof.
  unfold Kernames.Kername.eqb.
  destruct (Kernames.Kername.compare k1 k2) eqn:E; constructor.
  - exact (proj1 (Kernames.Kername.compare_eq _ _) E).
  - intro EQ; rewrite (proj2 (Kernames.Kername.compare_eq _ _) EQ) in E; discriminate.
  - intro EQ; rewrite (proj2 (Kernames.Kername.compare_eq _ _) EQ) in E; discriminate.
Qed.

HB.instance Definition _ :=
  hasEqDec.Build Kernames.kername Kernames.Kername.eqb kername_eqb_spec.
