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

From Stdlib Require Import ZArith.

From GallinaC.Utils Require Import ListExt OptionExt PosExt.
From GallinaC Require Import Programming.
From GallinaC.Compiler.Deep Require Import OpSem Cmd Prog.
From GallinaC.Examples.Collatz Require Import CollatzReify CollatzExecution.

Definition fundef_main: fundef :=
  Eval compute in
    match ListExt.sfind deep_collatz.(prog_main) deep_collatz.(prog_defs) with
    | Some (AST.Gfun fd) => fd
    | _ => AST.External (AST.EF_external Strings.String.EmptyString AST.signature_main)
    end.

Definition init_state: @state GCModel :=
  Callstate fundef_main [] Kstop CollatzExecution.init_state.

Lemma init_state_initial: initial_state deep_collatz init_state.
Proof.
  assert (DEF: Maps.PTree.get (AST.prog_main deep_collatz) (AST.prog_defmap deep_collatz) =
                 Some (AST.Gfun fundef_main)) by reflexivity.
  destruct (proj1 (Globalenvs.Genv.find_def_symbol _ _ _) DEF) as (b & SYMB & FDEF).
  econstructor.
  - now eapply Bool.reflect_iff;[ eapply Typing.type_program_spec | ].
  - reflexivity.
  - exact SYMB.
  - exact (proj2 (Globalenvs.Genv.find_funct_ptr_iff _ _ _) FDEF).
  - now constructor.
Qed.

Definition final_state: @state GCModel :=
  Returnstate (Value.v_nat 12) Kstop CollatzExecution.final_state.

Lemma final_state_final: OpSem.final_state final_state (Integers.Int.repr 12%Z).
Proof.
  now constructor.
Qed.

Example collatz_execution:
  Smallstep.star (@OpSem.step GCModel) (Globalenvs.Genv.globalenv deep_collatz) init_state Events.E0 final_state.
Proof.
  now repeat one_step.
Qed.
