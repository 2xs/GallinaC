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

From Corelib Require Import ssreflect ssrfun ssrbool.
Import ssrfun.Option.
From HB Require Import structures.

From GallinaC.Utils Require Export Algebra.
From GallinaC.Utils Require Import ReflectExt.

Local Open Scope separation_scope.

Definition unit_eqb (x y: unit): bool := true.

Lemma unit_eqb_spec: forall x y, Bool.reflect (x = y) (unit_eqb x y).
Proof.
  by case; case; constructor.
Qed.

Definition unit_sum (x y: unit): option unit := Some tt.

Lemma unit_sum_comm: forall x y, unit_sum x y = unit_sum y x.
Proof.
  reflexivity.
Qed.

Definition unit_sum_id_e: unit := tt.

Lemma unit_sum_id_l: forall x, unit_sum unit_sum_id_e x = Some x.
Proof.
  by case.
Qed.

Lemma unit_sum_id_r: forall x, unit_sum x unit_sum_id_e = Some x.
Proof.
  by case.
Qed.

Lemma unit_sum_assc: forall x y z, bind (Basics.flip unit_sum z) (unit_sum x y) = bind (unit_sum x) (unit_sum y z).
Proof.
  by repeat case.
Qed.

Lemma unit_sum_cancel_l: forall x y z w, unit_sum x y = Some w -> unit_sum x z = Some w -> y = z.
Proof.
  by repeat case.
Qed.

Lemma unit_sum_cancel_r: forall x y z w, unit_sum y x = Some w -> unit_sum z x = Some w -> y = z.
Proof.
  by repeat case.
Qed.

Lemma unit_sum_cross_split: forall a b c d z,
    unit_sum a b = Some z -> unit_sum c d = Some z ->
    exists ac ad bc bd,
      unit_sum ac ad = Some a /\ unit_sum bc bd = Some b /\
      unit_sum ac bc = Some c /\ unit_sum ad bd = Some d.
Proof.
  by move=> [] [] [] [] _ _ _; exists tt, tt, tt, tt.
Qed.

HB.instance Definition _ := isNonEmpty.Build unit tt.
HB.instance Definition _ := hasEqDec.Build unit unit_eqb unit_eqb_spec.
HB.instance Definition _ := hasOp.Build unit unit_sum.
HB.instance Definition _ := hasComm.Build unit unit_sum_comm.
HB.instance Definition _ := hasIdentity.Build unit unit_sum_id_e unit_sum_id_l unit_sum_id_r.
HB.instance Definition _ := hasAssc.Build unit unit_sum_assc.
HB.instance Definition _ := hasCancel.Build unit unit_sum_cancel_l unit_sum_cancel_r.
HB.instance Definition _ := hasCrossSplit.Build unit unit_sum_cross_split.
