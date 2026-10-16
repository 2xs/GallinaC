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

From GallinaC Require Import Programming Imp.PrimitivesProp.
From GallinaC.Models Require Import BlockMemory.

From GallinaC.Examples.Collatz Require Import Collatz.
Import Collatz.
Import List ListNotations.

Definition init_state: GCModel := emp_state.

Definition final_state: GCModel :=
  {| smem := MEmpty (Owned 2); hmem := MEmpty (Owned 0) |}.

Example collatz_execution:
  main init_state = Some (Success (12, final_state)).
Proof.
  cbv beta delta [main].
  now repeat reduce.
Qed.
