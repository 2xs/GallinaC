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

Section Carve.

  Context [S: Separation.type].

  Definition carve (P R: Pred S): Pred S :=
    fun s => forall sr sp, P sp -> sr $+ sp = Some s -> R sr.

  #[global] Instance carve_proper:
    Proper (pointwise_relation S iff ==> pointwise_relation S iff ==> pointwise_relation S iff) carve.
  Proof using Type.
    move=> P P' EQP R R' EQR s.
    split=> CARVE sr sp /EQP Psp EQs; apply/EQR; exact: CARVE sr sp Psp EQs.
  Qed.

  #[global] Instance carve_proper_app:
    Proper (pointwise_relation S iff ==> pointwise_relation S iff ==> eq ==> iff) carve.
  Proof using Type.
    move=> P P' EQP R R' EQR s _ <-.
    exact: carve_proper P P' EQP R R' EQR s.
  Qed.

  #[global] Instance carve_mono_proper:
    Proper (pointwise_relation S Basics.impl --> pointwise_relation S Basics.impl ==> pointwise_relation S Basics.impl) carve.
  Proof using Type.
    move=> P P' IMPP R R' IMPR s CARVE sr sp /IMPP Psp EQs.
    apply/IMPR; exact: CARVE sr sp Psp EQs.
  Qed.

  #[global] Instance carve_mono_proper_app:
    Proper (pointwise_relation S Basics.impl --> pointwise_relation S Basics.impl ==> eq ==> Basics.impl) carve.
  Proof using Type.
    move=> P P' IMPP R R' IMPR s _ <-.
    exact: carve_mono_proper P P' IMPP R R' IMPR s.
  Qed.

End Carve.

Arguments carve_proper {S}.
Arguments carve_proper_app {S}.
Arguments carve_mono_proper {S}.
Arguments carve_mono_proper_app {S}.
