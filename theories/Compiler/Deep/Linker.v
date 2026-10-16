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

From GallinaC.Compiler.Deep Require Typing.
From GallinaC.Compiler.Deep Require Import Prog.

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
  intros x y z LINK.
  destruct x as [ f1 | ef1 ], y as [ f2 | ef2 ].
  - discriminate LINK.
  - destruct ef2; try discriminate LINK.
    injection LINK as <-; split; constructor.
  - destruct ef1; try discriminate LINK.
    injection LINK as <-; split; constructor.
  - cbn in LINK.
    destruct (AST.external_function_eq ef1 ef2) as [ <- | ]; [ | discriminate LINK ].
    injection LINK as <-; split; constructor.
Qed.

Lemma link_fundef_either: forall (fd1 fd2 fd: fundef), link fd1 fd2 = Some fd -> fd = fd1 \/ fd = fd2.
Proof.
  cbn; unfold link; intros fd1 fd2 fd LINK.
  destruct fd1 as [ f1 | ef1 ], fd2 as [ f2 | ef2 ].
  - discriminate LINK.
  - destruct ef2; try discriminate LINK.
    injection LINK as <-; left; reflexivity.
  - destruct ef1; try discriminate LINK.
    injection LINK as <-; right; reflexivity.
  - cbn in LINK.
    destruct (AST.external_function_eq ef1 ef2) as [ <- | ]; [ | discriminate LINK ].
    injection LINK as <-; left; reflexivity.
Qed.

Global Opaque Linker_fundef.

Definition link_program (p1 p2: program): option program :=
  match link (program_of_program p1) (program_of_program p2) with
  | None => None
  | Some p =>
      let extra :=
        if (p1.(prog_extra).(prog_next_id) =? p2.(prog_extra).(prog_next_id))%positive then
          Some {| prog_next_id := p1.(prog_extra).(prog_next_id) |}
        else
          None
      in
      match extra with
      | Some extra =>
          let p :=
            {|
              prog_defs := p.(AST.prog_defs);
              prog_public := p.(AST.prog_public);
              prog_main := p.(AST.prog_main);
              prog_extra := extra
            |}
          in
          if Typing.type_program p then Some p else None
      | _ => None
      end
  end.

Definition linkorder_program (p1 p2: program) : Prop :=
     linkorder (program_of_program p1) (program_of_program p2)
  /\ (p1.(prog_extra).(prog_next_id) = p2.(prog_extra).(prog_next_id)).

Lemma link_program_inv [p1 p2 p: program] (LINK: link_program p1 p2 = Some p)
  : link (program_of_program p1) (program_of_program p2) = Some (program_of_program p)
    /\ p1.(prog_extra).(prog_next_id) = p2.(prog_extra).(prog_next_id)
    /\ p.(prog_extra).(prog_next_id) = p1.(prog_extra).(prog_next_id)
    /\ Typing.type_program p = true.
Proof.
  unfold link_program in LINK.
  destruct (link (program_of_program p1) (program_of_program p2)) as [ [ defs public main ] | ];
    [ | discriminate ].
  destruct (Pos.eqb_spec (prog_next_id (prog_extra p1)) (prog_next_id (prog_extra p2)))
    as [ EQ | ]; [ | discriminate ].
  destruct (Typing.type_program _) eqn:WTp; [ | discriminate LINK ].
  injection LINK as <-.
  repeat split; [ exact EQ | exact WTp ].
Qed.

Global Program Instance Linker_program: Linker program := {
  link := link_program;
  linkorder := linkorder_program
}.
Next Obligation.
  split. apply linkorder_refl. auto.
Defined.

Next Obligation.
  unfold linkorder_program.
  intros x y z [ LOxy H_x_y ] [ LOyz H_y_z ].
  split; [ | congruence ].
  eapply linkorder_trans; eauto.
Defined.

Next Obligation.
  intros x y z LINK.
  destruct (link_program_inv LINK) as ( LINKp & EQxy & EQz & _ ).
  apply link_linkorder in LINKp as [ LOx LOy ].
  split; split; congruence.
Defined.

Lemma linkorder_program_next_id (p1 p2: program) (LINKORDER: linkorder p1 p2)
  : p1.(prog_extra).(prog_next_id) = p2.(prog_extra).(prog_next_id).
Proof.
  now inversion LINKORDER.
Qed.

Lemma linkorder_program_free (p1 p2: program) (LINKORDER: linkorder p1 p2)
  : p1.(prog_extra).(prog_next_id) = p2.(prog_extra).(prog_next_id).
Proof.
  now inversion LINKORDER.
Qed.

Lemma link_program_wt (p1 p2 p: program) (LINK: link_program p1 p2 = Some p)
  : Typing.wt_program p.
Proof.
  destruct (link_program_inv LINK) as ( _ & _ & _ & WTp ).
  exact (proj2 (Bool.reflect_iff _ _ (Typing.type_program_spec _)) WTp).
Qed.


Global Opaque Linker_program.
