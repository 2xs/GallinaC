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
From GallinaC.Seplog.Star Require Import Star.

Local Open Scope separation_scope.

Section Upclose.

  Context [S: Separation.type].

  Definition upclose (P: Pred S): Pred S := P ** top.

  #[global] Instance upclose_proper:
    Proper (pointwise_relation S iff ==> pointwise_relation S iff) upclose.
  Proof using Type.
    move=> P P' EQP s.
    exact: star_proper P P' EQP top top (fun _ => iff_refl True) s.
  Qed.

  #[global] Instance upclose_proper_app:
    Proper (pointwise_relation S iff ==> eq ==> iff) upclose.
  Proof using Type.
    move=> P P' EQP s _ <-.
    exact: upclose_proper P P' EQP s.
  Qed.

  #[global] Instance upclose_mono_proper:
    Proper (pointwise_relation S Basics.impl ==> pointwise_relation S Basics.impl) upclose.
  Proof using Type.
    move=> P P' IMPP s.
    exact: star_mono_proper P P' IMPP top top (impl_refl_taut top) s.
  Qed.

  #[global] Instance upclose_mono_proper_app:
    Proper (pointwise_relation S Basics.impl ==> eq ==> Basics.impl) upclose.
  Proof using Type.
    move=> P P' IMPP s _ <-.
    exact: upclose_mono_proper P P' IMPP s.
  Qed.

End Upclose.

Arguments upclose_proper {S}.
Arguments upclose_proper_app {S}.
Arguments upclose_mono_proper {S}.
Arguments upclose_mono_proper_app {S}.
