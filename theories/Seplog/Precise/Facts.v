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
From GallinaC.Seplog.Emp Require Import Emp.
From GallinaC.Seplog.Precise Require Import Precise.

Local Open Scope separation_scope.

Section Facts.

  Context [S: Separation.type].

  Lemma precise_Emp: precise (S:=S) $$0.
  Proof using Type.
    move=> s s1 s2 EMP1 EMP2 _ _.
    rewrite /Emp in EMP1 EMP2.
    by rewrite EMP1 EMP2.
  Qed.

End Facts.

Arguments precise_Emp {S}.
