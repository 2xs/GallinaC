From GallinaC.Examples.Reverse Require Import ReverseReify ReverseExecution.

From GallinaC.Utils Require Import ListExt OptionExt.
From GallinaC.Imp Require Import Model.
From GallinaC.Compiler.Deep Require Import OpSem Cmd Prog.

From Stdlib Require Import PArith.

Definition fundef_main: fundef :=
  Eval compute in
    match ListExt.sfind Pos.eq_dec deep_reverse_prog.(prog_main) deep_reverse_prog.(prog_defs) with
    | Some (AST.Gfun fd) => fd
    | _ => AST.External (AST.EF_external Strings.String.EmptyString AST.signature_main)
    end.

(* States from ReverseExecution adapted for deep semantics *)
Definition init_state := Callstate fundef_main [] (@Kstop _) ReverseExecution.init_state.

Definition final_state := Returnstate (Value.v_nat 0) (@Kstop _) ReverseExecution.post_reverse_state.

Example reverse_execution:
  Smallstep.star (@OpSem.step _ _) (Globalenvs.Genv.globalenv deep_reverse_prog) init_state Events.E0 final_state.
Proof.
  repeat one_step.
Qed.
