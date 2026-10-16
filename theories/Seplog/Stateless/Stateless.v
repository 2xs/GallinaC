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

From GallinaC.Utils Require Import Algebra.
From GallinaC.Seplog Require Import Pred.
From GallinaC.Seplog.Emp Require Import Emp.

Local Open Scope separation_scope.

Section Stateless.

  Context [S: Separation.type].

  Definition stateless (P: Pred S) : Prop :=
    |- P ===> $$0.

End Stateless.
