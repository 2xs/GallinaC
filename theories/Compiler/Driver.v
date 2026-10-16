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

From Stdlib Require Import String.

From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Linking Smallstep.
From compcert.backend Require Cminor.
From compcert.driver Require Import Compiler.

From GallinaC.Utils Require Import ListExt.
From GallinaC.Imp Require Import State.
From GallinaC.Compiler.Deep Require Import Prog Lemmas.
From GallinaC.Compiler.Passes Require TCO TCOproof DeepTypecheck.
From GallinaC.Compiler.Passes Require Import IRgen Cminorgen IRgenproof Cminorgenproof.

Definition transf_rtl_program (f: RTL.program) : res Asm.program :=
   OK f
   @@ print (print_RTL 0)
   @@ total_if Compopts.optim_tailcalls (time "Tail calls" Tailcall.transf_program)
   @@ print (print_RTL 1)
  @@@ time "Inlining" Inlining.transf_program
   @@ print (print_RTL 2)
   @@ time "Renumbering" Renumber.transf_program
   @@ print (print_RTL 3)
   @@ total_if Compopts.optim_constprop (time "Constant propagation" Constprop.transf_program)
   @@ print (print_RTL 4)
   @@ total_if Compopts.optim_constprop (time "Renumbering" Renumber.transf_program)
   @@ print (print_RTL 5)
  @@@ partial_if Compopts.optim_CSE (time "CSE" CSE.transf_program)
   @@ print (print_RTL 6)
  @@@ partial_if Compopts.optim_redundancy (time "Redundancy elimination" Deadcode.transf_program)
   @@ print (print_RTL 7)
  @@@ time "Unused globals" Unusedglob.transform_program
   @@ print (print_RTL 8)
  @@@ time "Register allocation" Allocation.transf_program
   @@ print print_LTL
   @@ time "Branch tunneling" Tunneling.tunnel_program
  @@@ time "CFG linearization" Linearize.transf_program
   @@ time "Label cleanup" CleanupLabels.transf_program
  @@@ partial_if Compopts.debug (time "Debugging info for local variables" Debugvar.transf_program)
  @@@ time "Mach generation" Stacking.transf_program
   @@ print print_Mach
  @@@ time "Asm generation" Asmgen.transf_program.

Definition transf_cminor_program (p: Cminor.program) : res Asm.program :=
   OK p
   @@ print print_Cminor
  @@@ time "Instruction selection" Selection.sel_program
  @@@ time "RTL generation" RTLgen.transl_program
  @@@ transf_rtl_program.

Definition transf_gc_program (p: program): res Asm.program :=
  Errors.OK p
    @@@ time "Deep type checking" DeepTypecheck.transf_program
    @@@ time "IR generation" IRgen.transl_program
     @@ time "Tail-call optimization" TCO.transf_program
    @@@ time "Cminor generation" Cminorgen.transl_program
    @@@ transf_cminor_program.

Local Open Scope linking_scope.

Definition GallinaC_passes :=
  mkpass DeepTypecheck.match_prog
    ::: mkpass Passes.IRgenproof.match_prog
    ::: mkpass Passes.TCOproof.match_prog
    ::: mkpass Passes.Cminorgenproof.match_prog
    ::: mkpass Selectionproof.match_prog
    ::: mkpass RTLgenproof.match_prog
    ::: mkpass (match_if Compopts.optim_tailcalls Tailcallproof.match_prog)
    ::: mkpass Inliningproof.match_prog
    ::: mkpass Renumberproof.match_prog
    ::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
    ::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
    ::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
    ::: mkpass (match_if Compopts.optim_redundancy Deadcodeproof.match_prog)
    ::: mkpass Unusedglobproof.match_prog
    ::: mkpass Allocproof.match_prog
    ::: mkpass Tunnelingproof.match_prog
    ::: mkpass Linearizeproof.match_prog
    ::: mkpass CleanupLabelsproof.match_prog
    ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
    ::: mkpass Stackingproof.match_prog
    ::: mkpass Asmgenproof.match_prog
    ::: pass_nil Asm.program.

Definition match_prog : Deep.Prog.program -> Asm.program -> Prop :=
  pass_match (compose_passes GallinaC_passes).

Theorem transf_gc_program_match p tp:
    transf_gc_program p = OK tp ->
    match_prog p tp.
Proof.
  intros T.
  unfold transf_gc_program, time in T.
  simpl in T.
  destruct (DeepTypecheck.transf_program p) as [ p0 | e ] eqn:P0; simpl in T; try discriminate.
  destruct (IRgen.transl_program p0) as [ p1 | e ] eqn:P1; simpl in T; try discriminate.
  set (p2 := TCO.transf_program p1) in *.
  destruct (Cminorgen.transl_program p2) as [p4|e] eqn:P4; simpl in T; try discriminate.
  (** Copied from CompCert Compiler.v **)
  unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  set (p7 := total_if Compopts.optim_tailcalls Tailcall.transf_program p6) in *.
  destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate.
  set (p9 := Renumber.transf_program p8) in *.
  set (p10 := total_if Compopts.optim_constprop Constprop.transf_program p9) in *.
  set (p11 := total_if Compopts.optim_constprop Renumber.transf_program p10) in *.
  destruct (partial_if Compopts.optim_CSE CSE.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
  destruct (partial_if Compopts.optim_redundancy Deadcode.transf_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
  destruct (Unusedglob.transform_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate.
  destruct (Allocation.transf_program p14) as [p15|e] eqn:P15; simpl in T; try discriminate.
  set (p16 := Tunneling.tunnel_program p15) in *.
  destruct (Linearize.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
  set (p18 := CleanupLabels.transf_program p17) in *.
  destruct (partial_if Compopts.debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
  destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
  unfold match_prog; simpl.

  exists p0; split. apply DeepTypecheck.transf_program_match; auto.
  exists p1; split. apply @IRgenproof.transf_program_match; auto.
  exists p2; split. apply TCOproof.transf_program_match.
  exists p4; split. apply Cminorgenproof.transf_program_match; auto.
  exists p5; split. apply Selectionproof.transf_program_match; auto.
  exists p6; split. apply RTLgenproof.transf_program_match; auto.
  exists p7; split. apply total_if_match. apply Tailcallproof.transf_program_match.
  exists p8; split. apply Inliningproof.transf_program_match; auto.
  exists p9; split. apply Renumberproof.transf_program_match; auto.
  exists p10; split. apply total_if_match. apply Constpropproof.transf_program_match.
  exists p11; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p12; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
  exists p13; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
  exists p14; split. apply Unusedglobproof.transf_program_match; auto.
  exists p15; split. apply Allocproof.transf_program_match; auto.
  exists p16; split. apply Tunnelingproof.transf_program_match.
  exists p17; split. apply Linearizeproof.transf_program_match; auto.
  exists p18; split. apply CleanupLabelsproof.transf_program_match; auto.
  exists p19; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
  exists p20; split. apply Stackingproof.transf_program_match; auto.
  exists tp; split. apply Asmgenproof.transf_program_match; auto.
  reflexivity.
Qed.

Theorem gc_semantic_preservation {Sm: State.type} p tp:
  match_prog p tp ->
  forward_simulation (@Deep.OpSem.semantics Sm p) (Asm.semantics tp)
  /\ backward_simulation (@Deep.OpSem.semantics Sm p) (Asm.semantics tp).
Proof.
  unfold match_prog, pass_match; simpl.
  intros M.
  Ltac DestructM :=
    match goal with
      [ H: exists p, _ /\ _ |- _ ] =>
        let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
                                                    destruct H as (p & M & MM); clear H
    end.
  repeat (DestructM); subst tp.
  assert (F: forward_simulation (@Deep.OpSem.semantics Sm p) (Asm.semantics p21)).
  {
    eapply compose_forward_simulations.
    eapply DeepTypecheck.transf_program_correct; eassumption.
    eapply compose_forward_simulations.
    eapply Passes.IRgenproof.transl_program_correct; eassumption.
    eapply compose_forward_simulations.
    eapply Passes.TCOproof.transf_program_correct; eassumption.
    eapply compose_forward_simulations.
    eapply Passes.Cminorgenproof.transl_program_correct; eassumption.
    eapply compose_forward_simulations.
    eapply Selectionproof.transf_program_correct; eassumption.
    eapply compose_forward_simulations.
    eapply RTLgenproof.transf_program_correct; eassumption.
    eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Tailcallproof.transf_program_correct.
    eapply compose_forward_simulations.
    eapply Inliningproof.transf_program_correct; eassumption.
    eapply compose_forward_simulations. eapply Renumberproof.transf_program_correct; eassumption.
    eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Constpropproof.transf_program_correct.
    eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Renumberproof.transf_program_correct.
    eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact CSEproof.transf_program_correct.
    eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Deadcodeproof.transf_program_correct; eassumption.
    eapply compose_forward_simulations.
    eapply Unusedglobproof.transf_program_correct; eassumption.
    eapply compose_forward_simulations.
    eapply Allocproof.transf_program_correct; eassumption.
    eapply compose_forward_simulations.
    eapply Tunnelingproof.transf_program_correct; eassumption.
    eapply compose_forward_simulations.
    eapply Linearizeproof.transf_program_correct; eassumption.
    eapply compose_forward_simulations.
    eapply CleanupLabelsproof.transf_program_correct; eassumption.
    eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Debugvarproof.transf_program_correct.
    eapply compose_forward_simulations.
    eapply Stackingproof.transf_program_correct with (return_address_offset := Asmgenproof0.return_address_offset).
    exact Asmgenproof.return_address_exists.
    eassumption.
    eapply Asmgenproof.transf_program_correct; eassumption.
  }
  split; auto.
  apply forward_to_backward_simulation; auto.
  apply Deep.Lemmas.receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem transf_gc_program_correct {Sm: State.type} p tp:
  transf_gc_program p = OK tp ->
  backward_simulation (@Deep.OpSem.semantics Sm p) (Asm.semantics tp).
Proof.
  intros T.
  now specialize (@gc_semantic_preservation Sm p tp (transf_gc_program_match p tp T)) as (FW & BW).
Qed.

Theorem separate_transf_gc_program_correct {Sm: State.type} c_units asm_units gc_program:
  nlist_forall2 (fun cu tcu => transf_gc_program cu = OK tcu) c_units asm_units ->
  link_list c_units = Some gc_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
   /\ backward_simulation (@Deep.OpSem.semantics Sm gc_program) (Asm.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_gc_program_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog gc_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply gc_semantic_preservation; auto.
Qed.
