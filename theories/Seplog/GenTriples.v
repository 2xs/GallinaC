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
From GallinaC.Seplog Require Import Hoare.
From GallinaC.Seplog.Lift Require Import Lift.
From GallinaC.Seplog.Star Require Import Star.

Local Open Scope separation_scope.

Lemma fail_triple [S A: Type] [total: bool] [P: A -> Pred S]:
  hoare total (fun _ => False) fail P.
Proof.
  by move=> x [].
Qed.
#[global] Hint Resolve fail_triple: seplog.

Lemma get_triple [S: Type] [total: bool] [P: S -> Pred S]:
  hoare total (fun s => P s s) get P.
Proof.
  by move=> s PRE.
Qed.
#[global] Hint Resolve get_triple: seplog.

Lemma put_triple [S: Type] [total: bool] [s: S] [P: unit -> Pred S]:
  hoare total (fun _ => P tt s) (put s) P.
Proof.
  by move=> s' PRE.
Qed.
#[global] Hint Resolve put_triple: seplog.

Lemma lift_pre [S: Separation.type] [total: bool] [A: Type] [p: Prop] [P: Pred S] [c: program S A] [Q: A -> Pred S]:
  (p -> hoare total P c Q) -> hoare total ([| p |] ** P) c Q.
Proof.
  move=> TRIPLE s [ ? [ sp [ EQs [ [ Hp EMP ] Psp ] ] ] ].
  move: EMP EQs => -> EQs.
  move/partition_emp_l: EQs Psp => -> Ps.
  exact: (TRIPLE Hp s Ps).
Qed.
