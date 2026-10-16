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

Section Star.

  Context [S: Separation.type].

  Definition star (P Q: Pred S) : Pred S :=
    fun s => exists s1 s2, s1 $+ s2 = Some s /\ P s1 /\ Q s2.

  Local Infix "**" := star (at level 40, left associativity): separation_scope.

  #[global] Instance star_proper:
    Proper (pointwise_relation S iff ==> pointwise_relation S iff ==> pointwise_relation S iff) star.
  Proof using Type.
    move=> P P' EQP R R' EQR s.
    by split=> -[ sp [ sr [ EQs [ /EQP Psp /EQR Rsr ] ] ] ]; exists sp, sr.
  Qed.

  #[global] Instance star_proper_app:
    Proper (pointwise_relation S iff ==> pointwise_relation S iff ==> eq ==> iff) star.
  Proof using Type.
    move=> P P' EQP R R' EQR s _ <-.
    exact: star_proper P P' EQP R R' EQR s.
  Qed.

  #[global] Instance star_mono_proper:
    Proper (pointwise_relation S Basics.impl ==> pointwise_relation S Basics.impl ==> pointwise_relation S Basics.impl) star.
  Proof using Type.
    move=> P P' IMPP R R' IMPR s [ sp [ sr [ EQs [ /IMPP Psp /IMPR Rsr ] ] ] ].
    by exists sp, sr.
  Qed.

  #[global] Instance star_mono_proper_app:
    Proper (pointwise_relation S Basics.impl ==> pointwise_relation S Basics.impl ==> eq ==> Basics.impl) star.
  Proof using Type.
    move=> P P' IMPP R R' IMPR s _ <-.
    exact: star_mono_proper P P' IMPP R R' IMPR s.
  Qed.

End Star.

Arguments star_proper {S}.
Arguments star_proper_app {S}.
Arguments star_mono_proper {S}.
Arguments star_mono_proper_app {S}.

Infix "**" := star (at level 40, left associativity): separation_scope.
