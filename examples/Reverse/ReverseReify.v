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

From GallinaC.Examples.Reverse Require Import Reverse.
From GallinaC Require Import Compiler.

(* It is possible to reify individual commands, but this requires importing additional modules *)
(* From MetaRocq.Template Require Import All. *)
(* Import MRMonadNotation. *)

(* MetaRocq Quote Definition mr_prelude := *)
(*   Eval cbv zeta delta [prelude] in prelude. *)

(* MetaRocq Run *)
(*   ('(c, renv) <- translate_cmd' {| prog_renv := {| next_id := 1; funs := []; current_module := MPfile []; |}; stack := []; stack_depth := 0; temps := []; |} mr_prelude ;; *)
(*    tmDefinition "c_prelude" c). *)

(* Print c_prelude. *)

(* Full program reification is done by reifying a module *)

MetaRocq Run (reify_program "Reverse.Reverse" "main" "deep_reverse_prog").

(* Uncomment this to print the reified program *)
(* As can be seen, the function outside the module is not extracted, but kept "opaque" *)
(* This enables to have different functions between the Rocq model and the actual C code *)
(* From Stdlib.Strings Require Import String. *)

(* Local Open Scope char_scope. *)
(* Local Open Scope string_scope. *)

(* Print deep_reverse_prog. *)
