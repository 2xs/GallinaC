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

Section Wand.

  Context [S: Separation.type].

  Definition wand (P Q : Pred S) : Pred S :=
    fun s => forall sp sq, P sp -> s $+ sp = Some sq -> Q sq.

  Local Infix "-*" := wand (at level 70, right associativity): separation_scope.

  #[global] Instance wand_proper:
    Proper (pointwise_relation S iff ==> pointwise_relation S iff ==> pointwise_relation S iff) wand.
  Proof using Type.
    move=> P P' EQP R R' EQR s.
    split=> WAND sp sr /EQP Psp EQsr; apply/EQR; exact: WAND sp sr Psp EQsr.
  Qed.

  #[global] Instance wand_proper_app:
    Proper (pointwise_relation S iff ==> pointwise_relation S iff ==> eq ==> iff) wand.
  Proof using Type.
    move=> P P' EQP R R' EQR s _ <-.
    exact: wand_proper P P' EQP R R' EQR s.
  Qed.

  #[global] Instance wand_mono_proper:
    Proper (pointwise_relation S Basics.impl --> pointwise_relation S Basics.impl ==> pointwise_relation S Basics.impl) wand.
  Proof using Type.
    move=> P P' IMPP R R' IMPR s WAND sp sr /IMPP Psp EQsr.
    apply/IMPR; exact: WAND sp sr Psp EQsr.
  Qed.

  #[global] Instance wand_mono_proper_app:
    Proper (pointwise_relation S Basics.impl --> pointwise_relation S Basics.impl ==> eq ==> Basics.impl) wand.
  Proof using Type.
    move=> P P' IMPP R R' IMPR s _ <-.
    exact: wand_mono_proper P P' IMPP R R' IMPR s.
  Qed.

End Wand.

Arguments wand_proper {S}.
Arguments wand_proper_app {S}.
Arguments wand_mono_proper {S}.
Arguments wand_mono_proper_app {S}.

Infix "-*" := wand (at level 70, right associativity): separation_scope.
