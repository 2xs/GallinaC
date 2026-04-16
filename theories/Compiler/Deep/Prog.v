From Stdlib Require Import PArith.

From GallinaC.Compiler.Common Require Export Prog.
From GallinaC.Compiler.Deep Require Import Cmd.

Definition f_extra: Set := unit.

Definition function: Set := function cmd f_extra.

Definition fundef: Set := fundef cmd f_extra.

Definition globdef: Set := globdef cmd f_extra.

Record p_extra: Set :=
  {
    prog_next_id: positive;
  }.

Definition program: Set := program cmd f_extra p_extra.

Definition genv := genv cmd f_extra.
