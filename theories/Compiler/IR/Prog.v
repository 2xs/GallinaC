From Stdlib Require Import ZArith.

From compcert.common Require AST.

From GallinaC.Compiler.Common Require Export Prog.
From GallinaC.Compiler.IR Require Import Cmd.

Record f_extra : Set :=
  {
    (* Stack usage in GallinaC memory words *)
    fn_stackspace: Z;
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
