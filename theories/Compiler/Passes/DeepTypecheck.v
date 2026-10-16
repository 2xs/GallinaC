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

From compcert.common Require Import Errors Linking Smallstep.
From compcert.driver Require Compiler.

From GallinaC.Imp Require Import State.
From GallinaC.Compiler.Deep Require Typing OpSem Linker.
From GallinaC.Compiler.Deep Require Import Prog.

Definition transf_program (p: program) : res program :=
  if Deep.Typing.type_program p then OK p
  else Error (msg "Deep type checking: the program is ill-typed").

Definition match_prog (p tp: program) : Prop := tp = p.

Lemma transf_program_match p tp:
  transf_program p = OK tp -> match_prog p tp.
Proof.
  unfold transf_program, match_prog.
  destruct (Deep.Typing.type_program p); intros CHECK; [ | discriminate CHECK ].
  injection CHECK as <-; reflexivity.
Qed.

Global Instance TransfDeepTypecheckLink: TransfLink match_prog.
Proof.
  intros p1 p2 tp1 tp2 p LINK MATCH1 MATCH2.
  unfold match_prog in MATCH1, MATCH2; subst tp1 tp2.
  exists p; split; [ exact LINK | reflexivity ].
Qed.

Lemma transf_program_correct [Sm: State.type] p tp:
  match_prog p tp ->
  forward_simulation (@Deep.OpSem.semantics Sm p) (@Deep.OpSem.semantics Sm tp).
Proof.
  intros MATCH; unfold match_prog in MATCH; subst tp.
  apply Compiler.forward_simulation_identity.
Qed.
