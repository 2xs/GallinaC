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

From GallinaC.Examples.Reverse Require Import Reverse.
Import Reverse.
Import List ListNotations.

(* Supplying the reverse example with a concrete model allows to execute it like
   any other Rocq definition *)

Definition node_prov (b: nat): Provenance.t :=
  Provenance.Allocation b 0%N 2%N 0%N 2%N Permission.Free.

Definition node_ptr (b: nat): Pointer.t :=
  Some (mkAddr b 0%N, node_prov b).

Definition init_state: GCModel := emp_state.

Definition node_block (n: nat) (p: Pointer.t): block :=
  BCons (Owned (v_nat n)) (BTail (v_ptr p)).

Definition post_prelude_state: GCModel :=
  {| smem := MEmpty (Owned 0);
     hmem := MLive
               (M'Cons (Some (node_block 3 null))
               (M'Cons (Some (node_block 2 (node_ptr 0)))
               (M'Tail (node_block 1 (node_ptr 1)) (Owned 0)))) |}.

Definition post_reverse_state: GCModel :=
  {| smem := MEmpty (Owned 2);
     hmem := MLive
               (M'Cons (Some (node_block 3 (node_ptr 1)))
               (M'Cons (Some (node_block 2 (node_ptr 2)))
               (M'Tail (node_block 1 null) (Owned 0)))) |}.

(* Programs without while can be reduced using the classical tactics without issue *)
Example prelude_execution:
  allocate init_state = Some (Success (node_ptr 2, post_prelude_state)).
Proof.
  reflexivity.
Qed.

(* Using the [reduce] tactic, we rewrite the term step-wise until reaching the desired state.
 * See PrimitivesProp.v for the definition of the reduce tactic.
 *)
Example reverse_execution:
  main init_state = Some (Success (0, post_reverse_state)).
Proof.
  cbv beta delta [main print_ll allocate reverse].
  now repeat reduce.
Qed.
