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
