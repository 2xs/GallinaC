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

From Stdlib Require Import Arith BinPos.

From compcert.common Require Export Linking.
From compcert.cfrontend Require Ctypes.

From GallinaC.Compiler.Common Require Import Linker.

From GallinaC.Compiler.IR Require Import Prog.

Local Obligation Tactic := cbn.

Definition link_fundef (fd1 fd2: fundef) :=
  match fd1, fd2 with
  | AST.Internal _, AST.Internal _ => None
  | AST.External ef1, AST.External ef2 =>
      if AST.external_function_eq ef1 ef2 then Some (AST.External ef1) else None
  | AST.Internal f, AST.External ef =>
      match ef with AST.EF_external id sg => Some (AST.Internal f) | _ => None end
  | AST.External ef, AST.Internal f =>
      match ef with AST.EF_external id sg => Some (AST.Internal f) | _ => None end
  end.

Inductive linkorder_fundef: fundef -> fundef -> Prop :=
| linkorder_fundef_refl: forall fd, linkorder_fundef fd fd
| linkorder_fundef_exf_int: forall id sg f,
  linkorder_fundef (AST.External (AST.EF_external id sg)) (AST.Internal f)
.

Global Program Instance Linker_fundef: Linker fundef := {
    link := link_fundef;
    linkorder := linkorder_fundef;
  }.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  intros.
  inversion H; subst; inversion H0; subst; constructor.
Qed.
Next Obligation.
  intros.
  destruct x, y; cbn in H.
  discriminate.
  destruct e; inversion H; subst; now repeat constructor.
  destruct e; inversion H; subst; now repeat constructor.
  destruct (AST.external_function_eq e e0); [ inversion H; subst; split; constructor | discriminate ].
Qed.

Lemma link_fundef_either: forall (fd1 fd2 fd: fundef), link fd1 fd2 = Some fd -> fd = fd1 \/ fd = fd2.
Proof.
  cbn; unfold link, link_fundef; intros.
  destruct fd1, fd2.
  discriminate.
  destruct e; inversion H; subst; auto.
  destruct e; inversion H; subst; auto.
  destruct (AST.external_function_eq e e0); subst; inversion H; auto.
Qed.

Global Opaque Linker_fundef.

Definition link_program (p1 p2: program): option program :=
  match link (program_of_program p1) (program_of_program p2) with
  | None => None
  | Some p =>
      Some
        {|
          prog_defs := p.(AST.prog_defs);
          prog_public := p.(AST.prog_public);
          prog_main := p.(AST.prog_main);
          prog_extra := tt
        |}
  end.

Definition linkorder_program (p1 p2: program) : Prop :=
  linkorder (program_of_program p1) (program_of_program p2).

Lemma link_program_inv [p1 p2 p: program] (LINK: link_program p1 p2 = Some p)
  : link (program_of_program p1) (program_of_program p2) = Some (program_of_program p).
Proof.
  unfold link_program in LINK.
  destruct (link (program_of_program p1) (program_of_program p2)) as [ p' | ]; [ | discriminate ].
  injection LINK as <-.
  destruct p' as [ defs public main ]; reflexivity.
Qed.

Global Program Instance Linker_program: Linker program := {
  link := link_program;
  linkorder := linkorder_program
}.
Next Obligation.
  intros x; exact (linkorder_refl (program_of_program x)).
Defined.

Next Obligation.
  unfold linkorder_program.
  intros x y z LOxy LOyz.
  eapply linkorder_trans; eauto.
Defined.

Next Obligation.
  intros x y z EQ.
  exact (link_linkorder _ _ _ (link_program_inv EQ)).
Defined.

Global Opaque Linker_program.

Section LINKORDER.

  Local Transparent Linker_fundef Linking.Linker_def.

  Lemma exf_declared_linkorder [p p': AST.program fundef vardef] [id ef]
    (NOTEXF: forall nm sg, ef <> AST.EF_external nm sg)
    (DECL: exf_declared p id ef) (LO: Linking.linkorder p p')
    : exf_declared p' id ef.
  Proof.
    destruct (Linking.prog_defmap_linkorder _ _ _ _ LO DECL) as ( gd & GET & LOgd ).
    unfold exf_declared; rewrite GET.
    inversion LOgd as [ fd1 fd2 LOfd | ]; subst.
    inversion LOfd; subst; [ reflexivity | ].
    exfalso; eapply NOTEXF; reflexivity.
  Qed.

End LINKORDER.
