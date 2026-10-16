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
From GallinaC.Seplog Require Import Hoare.
From GallinaC.Seplog.Star Require Import Star.
From GallinaC.Seplog Require Import Frame.

Local Open Scope separation_scope.

Section Frame.

  Context [Sm: State.type].

  Lemma star_frame_law:
    forall (total: bool) A (P: Pred Sm) (Q: A -> Pred Sm) (R: Pred Sm) (R': A -> Pred Sm) (c: program Sm A),
      (action_local_strong c /\ forall v, |- R ===> R' v) ->
      hoare total P c Q -> hoare total (P ** R) c (fun v => Q v ** R' v).
  Proof using Type.
    move=> total A P Q R R' c [LOCAL IMPL] TRIPLE.
    apply: (strengthen (Q := fun v => Q v ** R)).
    - move=> s [sp [sr [EQs [Psp Rsr] ] ] ].
      move: (TRIPLE sp Psp) (action_local_of_strong c LOCAL sp s sr EQs).
      case: (c sp) => [ [ [v sp'] | ] | ] TR AL.
      + case: AL => s' [EQs' ->].
        by exists sp', sr.
      + by [].
      + by rewrite AL.
    - move=> v.
      apply: (_: |- _ ===> _).
      f_equiv.
      exact: IMPL.
  Qed.

  HB.instance Definition star_framing :=
    isFraming.Build Sm (@star Sm)
      (fun A P Q R R' c => action_local_strong c /\ forall v, |- R ===> R' v)
      star_frame_law.

End Frame.

Arguments star_framing {Sm}.
