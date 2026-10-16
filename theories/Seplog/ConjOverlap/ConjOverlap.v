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

From GallinaC.Utils Require Import Algebra.
From GallinaC.Seplog Require Import Pred.

Local Open Scope separation_scope.

Section ConjOverlap.

  Context [S: Separation.type].

  Definition conj_overlap (P Q: Pred S): Pred S :=
    fun s => exists s1 s2 s3 sp sq,
        s1 $+ s2 = Some sp /\ s2 $+ s3 = Some sq /\ sp $+ s3 = Some s
        /\ P sp /\ Q sq.

  Local Infix "*&" := conj_overlap (at level 40, left associativity): separation_scope.

  #[global] Instance conj_overlap_proper:
    Proper (pointwise_relation S iff ==> pointwise_relation S iff ==> pointwise_relation S iff) conj_overlap.
  Proof using Type.
    move=> P P' EQP R R' EQR s.
    by split=> -[ s1 [ s2 [ s3 [ sp [ sr [ EQsp [ EQsr [ EQs [ /EQP Psp /EQR Rsr ] ] ] ] ] ] ] ] ];
      exists s1, s2, s3, sp, sr.
  Qed.

  #[global] Instance conj_overlap_proper_app:
    Proper (pointwise_relation S iff ==> pointwise_relation S iff ==> eq ==> iff) conj_overlap.
  Proof using Type.
    move=> P P' EQP R R' EQR s _ <-.
    exact: conj_overlap_proper P P' EQP R R' EQR s.
  Qed.

  #[global] Instance conj_overlap_mono_proper:
    Proper (pointwise_relation S Basics.impl ==> pointwise_relation S Basics.impl ==> pointwise_relation S Basics.impl) conj_overlap.
  Proof using Type.
    move=> P P' IMPP R R' IMPR s [ s1 [ s2 [ s3 [ sp [ sr [ EQsp [ EQsr [ EQs [ /IMPP Psp /IMPR Rsr ] ] ] ] ] ] ] ] ].
    by exists s1, s2, s3, sp, sr.
  Qed.

  #[global] Instance conj_overlap_mono_proper_app:
    Proper (pointwise_relation S Basics.impl ==> pointwise_relation S Basics.impl ==> eq ==> Basics.impl) conj_overlap.
  Proof using Type.
    move=> P P' IMPP R R' IMPR s _ <-.
    exact: conj_overlap_mono_proper P P' IMPP R R' IMPR s.
  Qed.

End ConjOverlap.

Arguments conj_overlap_proper {S}.
Arguments conj_overlap_proper_app {S}.
Arguments conj_overlap_mono_proper {S}.
Arguments conj_overlap_mono_proper_app {S}.

Infix "*&" := conj_overlap (at level 40, left associativity): separation_scope.
