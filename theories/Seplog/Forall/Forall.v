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

From GallinaC.Seplog Require Import Pred.

Local Open Scope separation_scope.

(* Universal quantification *)
Definition Univ [A B: Type] (P: A -> Pred B): Pred B := fun s => forall x, P x s.
Notation "'Forall' x .. y , p" :=
  (Univ (fun x => .. (Univ (fun y => p)) ..))
    (at level 200, x closed binder, y closed binder, right associativity): separation_scope.

#[global] Instance Univ_proper (A B: Type):
  Proper (pointwise_relation A (pointwise_relation B iff) ==> pointwise_relation B iff) (@Univ A B).
Proof.
  move=> P P' EQP s.
  split=> FPs x; apply/(EQP x s); exact: FPs.
Qed.

#[global] Instance Univ_mono_proper (A B: Type):
  Proper (pointwise_relation A (pointwise_relation B Basics.impl) ==> pointwise_relation B Basics.impl) (@Univ A B).
Proof.
  move=> P P' IMPP s FPs x.
  apply/(IMPP x s); exact: FPs.
Qed.

#[global] Instance Univ_mono_proper_app (A B: Type):
  Proper (pointwise_relation A (pointwise_relation B Basics.impl) ==> eq ==> Basics.impl) (@Univ A B).
Proof.
  move=> P P' IMPP s _ <-.
  exact: Univ_mono_proper A B P P' IMPP s.
Qed.
