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
From GallinaC.Seplog.Emp Require Import Emp.
From GallinaC.Seplog.Stateless Require Import Stateless.
From GallinaC.Seplog.Lift Require Import Lift.

Local Open Scope separation_scope.

Section Facts.

  Context [S: Separation.type].

  Lemma ex_falso (P: Pred S):
    |- [| False |] ===> P.
  Proof using Type.
    by move=> s [ ].
  Qed.

  Lemma Emp_lift_True: |- Emp (S:=S) <==> [| True |].
  Proof using Type.
    move=> s.
    split=> [ EMP | [ _ EMP ] ].
    - by split.
    - exact: EMP.
  Qed.

  Lemma stateless_lift (P: Prop): stateless ([| P |]: Pred S).
  Proof using Type.
    by move=> s [ HP EMP ].
  Qed.

End Facts.

Arguments Emp_lift_True {S}.
