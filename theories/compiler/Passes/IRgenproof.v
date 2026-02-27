From Stdlib Require Import ZArith List Arith.
From Stdlib Require Import String.
Import ListNotations.

From compcert.common Require Linking Values.
From compcert.common Require Import Errors Globalenvs.
From compcert.lib Require Import Coqlib Integers Maps.
From compcert.backend Require Cminor.

From Imp Require Import Store Heap Intops Uint32 Uintptr.

From Compiler.Common Require Import Types(t_nat).
From Compiler.Common Require CCInj Value.
Import CCInj.Facts Value.Facts.
From Compiler.Passes Require Import IRgen.
From Compiler.Common Require Import Expr Ctxt.
From Compiler.Deep Require Import Cmd OpSem Typing Prog Linker.
From Compiler.IR Require Semantics.
From Compiler.IR Require Import Linker.

Section Match.

  Definition match_fundef (p: program) : Deep.Prog.fundef -> IR.Prog.fundef -> Prop := fun _ _ => True.
  (* | match_fundef_internal: forall fn tfn, *)
  (*     transl_fundef p.(prog_extra).(prog_malloc) p.(prog_extra).(Prog.prog_free) fn = OK tfn -> *)
  (*     match_fundef p (AST.Internal fn) (AST.Internal tfn) *)
  (* | match_fundef_external: forall ef, *)
  (*     match_fundef p (AST.External ef) (AST.External ef) *)
  (* . *)

  Definition match_varinfo: vardef -> vardef -> Prop := eq.

  Definition match_prog (p: program) (tp: IR.Prog.program) :=
    (* Matching succeeds, if *)
    Linking.match_program_gen
      match_fundef
      match_varinfo
      p
      (Prog.program_of_program p)
      (program_of_program tp)
  .

  Lemma transf_program_match:
    forall p tp, transl_program p = OK tp -> match_prog p tp.
  Proof.
    unfold transl_program.
    intros p tp Htransl.
  Admitted.

  Lemma match_program_main {p tp}:
    match_prog p tp -> AST.prog_main tp = Prog.prog_main p.
  Proof.
    intros Hmatch_prog.
    destruct Hmatch_prog as ( _ & Hmain & _ ).
    auto.
  Qed.

End Match.

Section TRANSLATION.

  Context {St: Store}.
  Context {Hp: Heap}.
  Variable prog: program.
  Variable tprog: IR.Prog.program.
  Hypothesis TRANSL: match_prog prog tprog.

  Theorem transl_program_correct:
    Smallstep.forward_simulation (@OpSem.semantics St Hp prog) (Semantics.semantics (St := St) (Hp := Hp) tprog).
  Proof using TRANSL.
  Admitted.

End TRANSLATION.

Global Instance TransfCminorgenLink: TransfLink match_prog.
Proof.
Admitted.
