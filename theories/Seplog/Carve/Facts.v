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
From GallinaC.Seplog.Septract Require Import Septract.
From GallinaC.Seplog.Carve Require Import Carve.

Local Open Scope separation_scope.

Section Facts.

  Context [S: Separation.type].

  Lemma septract_carve (P Q R: Pred S):
    (|- (P -** Q) ===> R) <-> (|- Q ===> carve P R).
  Proof using Type.
    split.
    - move=> IMP sq Qsq sr sp Psp EQsq.
      apply: IMP.
      by exists sp, sq.
    - move=> IMP s [ sp [ sq [ Psp [ EQsq Qsq ] ] ] ].
      exact: (IMP sq Qsq s sp Psp EQsq).
  Qed.

End Facts.
