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

From Stdlib Require Import PArith List.
Import ListNotations.

From GallinaC.Utils Require Import OptionExt PosExt.
From GallinaC.Imp Require Import PrimitivesProp.
From GallinaC.Models Require Import GCModel.
From GallinaC.Compiler Require Import Denotation Agree.
From GallinaC.Compiler.Deep Require Import Cmd Prog Typing.
From GallinaC.Examples.Collatz Require Import Collatz CollatzExecution CollatzReify CollatzOpSem.

Definition collatz_program_typed : type_program deep_collatz = true := eq_refl.

Definition collatz_fn : function :=
  Eval compute in
    match ListExt.sfind deep_collatz.(prog_main) deep_collatz.(prog_defs) with
    | Some (AST.Gfun (AST.Internal fn)) => fn
    | _ => {| fn_return := t_unit; fn_params := []; fn_temps := []; fn_internals := []; fn_body := c_ret e_tt; fn_extra := tt |}
    end.

Definition collatz_glob :=
  @denote_glob_ctxt_of_program GCModel empty_exfs deep_collatz collatz_program_typed.

Definition collatz_fd_typed : type_fundef (mk_glob_ctxt deep_collatz) (AST.Internal collatz_fn) = true :=
  eq_refl.

Definition collatz_sig_typed : type_funsig (AST.Internal collatz_fn) = Some (mk_signature [] t_nat) :=
  eq_refl.

(* The denotation of the call to main is trivially equal to the call of the shallow main *)
Lemma collatz_d_main :
  denote_fundef_call empty_exfs collatz_fd_typed collatz_sig_typed collatz_glob [] = Collatz.main.
Proof.
  reflexivity.
Qed.

(* We can then execute the denotation and obtain the same result *)
Example collatz_denotes :
  denote_fundef_call empty_exfs collatz_fd_typed collatz_sig_typed collatz_glob [] CollatzExecution.init_state
  = Some (Monad.Success (12%nat, CollatzExecution.final_state)).
Proof.
  rewrite collatz_d_main.
  cbv beta delta [Collatz.main].
  now repeat reduce.
Qed.

Definition collatz_GET : get_global (prog_main deep_collatz) (mk_glob_ctxt deep_collatz)
                         = Some (AST.Gfun (AST.Internal collatz_fn)) := eq_refl.

Example collatz_adequacy :
  exists n : nat,
    denote_fundef_call empty_exfs collatz_fd_typed collatz_sig_typed collatz_glob [] CollatzExecution.init_state
    = Some (Monad.Success (n, OpSem.state_of_state CollatzOpSem.final_state)).
Proof.
  edestruct (denote_initial_final empty_exfs deep_collatz _ _ _ _ init_state_initial CollatzOpSem.collatz_execution
               final_state_final)
    as (n & f' & WTp' & WTFD & SIG & RES & GET & EVAL).
  assert (f' = AST.Internal collatz_fn) as ->
      by (rewrite collatz_GET in GET; congruence).
  assert (WTp' = collatz_program_typed) as -> by (apply Eqdep_dec.UIP_dec, Bool.bool_dec).
  assert (WTFD = collatz_fd_typed) as -> by (apply Eqdep_dec.UIP_dec, Bool.bool_dec).
  assert (SIG = collatz_sig_typed) as -> by (apply Eqdep_dec.UIP_dec, (ReflectExt.sumbool_of_reflect Algebra.eqb_spec)).
  exists n.
  exact EVAL.
Qed.
