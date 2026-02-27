From Stdlib Require Import PArith ZArith.

From compcert.common Require AST.

From Compiler.Common Require Export Prog.
From Compiler.IR Require Import Cmd.

Record f_extra : Set :=
  {
    (* Stack usage in GallinaC memory words *)
    fn_stackspace: nat;
  }.

Definition function: Set := function cmd f_extra.

Definition fundef := fundef cmd f_extra.

Definition globdef: Set := globdef cmd f_extra.

Record p_extra: Set :=
  {
    prog_malloc: option AST.ident;
    prog_free: option AST.ident;
  }.

Definition program: Set := program cmd f_extra p_extra.

Definition genv := genv cmd f_extra.
