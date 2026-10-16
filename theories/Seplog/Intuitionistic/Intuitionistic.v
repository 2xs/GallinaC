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

Section Intuitionistic.

  Context [S: Separation.type].

  Definition intuitionistic (P: Pred S): Prop := |- P ** top <==> P.

  #[global] Instance intuitionistic_proper:
    Proper (pointwise_relation S iff ==> iff) intuitionistic.
  Proof using Type.
    move=> P P' EQP.
    by rewrite /intuitionistic EQP.
  Qed.

End Intuitionistic.

Arguments intuitionistic_proper {S}.
