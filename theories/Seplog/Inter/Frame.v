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

From GallinaC.Seplog.Inter Require Import Inter.
From GallinaC.Seplog Require Import Hoare Frame.

Local Open Scope separation_scope.

Section Frame.

  Context [S: Type].

  Lemma inter_frame_law (total: bool) A (P: Pred S) (Q: A -> Pred S) (R: Pred S) (R': A -> Pred S) (c: program S A):
    (preserves R c /\ forall v, |- R ===> R' v) ->
    hoare total P c Q -> hoare total (P && R) c (fun v => Q v && R' v).
  Proof using Type.
    move=> [ PRES IMPL ] TRIPLE s [ Ps Rs ].
    move: (TRIPLE s Ps) (PRES s).
    case: (c s) => [ [ [ v s' ] | ] | ] //= Qvs' PRESs.
    split; first exact: Qvs'.
    apply: (IMPL v s').
    exact: (PRESs v s' Rs eq_refl).
  Qed.

  HB.instance Definition inter_framing :=
    isFraming.Build S (@inter S)
      (fun A P Q R R' c => preserves R c /\ forall v, |- R ===> R' v)
      inter_frame_law.

End Frame.

Arguments inter_framing {S}.
