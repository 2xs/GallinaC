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
From GallinaC.Seplog.Exists Require Import Exists.
From GallinaC.Seplog.Forall Require Import Forall.

Local Open Scope separation_scope.

Lemma Univ_elim [A B: Type] (P: A -> Pred B) (x: A):
  |- (Forall y, P y) ===> P x.
Proof.
  move=> s FPs; exact: FPs x.
Qed.
#[global] Hint Resolve Univ_elim: seplog.

Lemma Univ_intro [A B: Type] (P: A -> Pred B) (R: Pred B):
  (forall x, |- R ===> P x) -> |- R ===> Forall x, P x.
Proof.
  move=> IMP s Rs x; exact: IMP x s Rs.
Qed.
#[global] Hint Resolve Univ_intro: seplog.

Lemma Exists_Univ [A B C: Type] (P: A -> B -> Pred C):
  |- (Exists x, Forall y, P x y) ===> (Forall y, Exists x, P x y).
Proof.
  move=> s [x FPxs] y; exists x; exact: FPxs y.
Qed.
#[global] Hint Resolve Exists_Univ: seplog.
