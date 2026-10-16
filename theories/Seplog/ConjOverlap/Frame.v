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
From HB Require Import structures.

From GallinaC.Imp Require Import State.
From GallinaC.Seplog.Forall Require Import Forall.
From GallinaC.Seplog Require Import Hoare.
From GallinaC.Seplog.Star Require Import Star.
From GallinaC.Seplog.Wand Require Import Wand.
From GallinaC.Seplog.ConjOverlap Require Import ConjOverlap.
From GallinaC.Seplog Require Import Frame Ramify.

Local Open Scope separation_scope.

Section Frame.

  Context [Sm: State.type].

  Lemma conj_overlap_frame_law (total: bool) A (P: Pred Sm) (Q: A -> Pred Sm) (R: Pred Sm) (R': A -> Pred Sm) (c: program Sm A):
    (action_local_strong c /\ |- P *& R ===> P ** (Forall v, Q v -* (Q v *& R' v))) ->
    hoare total P c Q -> hoare total (P *& R) c (fun v => Q v *& R' v).
  Proof using Type.
    move=> [ LOCAL RAM ] TRIPLE.
    exact: (ramify LOCAL TRIPLE RAM).
  Qed.

  HB.instance Definition conj_overlap_framing :=
    isFraming.Build Sm (@conj_overlap Sm)
      (fun A P Q R R' c => action_local_strong c /\ |- P *& R ===> P ** (Forall v, Q v -* (Q v *& R' v)))
      conj_overlap_frame_law.

End Frame.

Arguments conj_overlap_framing {Sm}.
