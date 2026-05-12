From Stdlib Require Import String PArith.

From GallinaC.Examples.Reverse Require Import ReverseReify ReverseExecution.

From GallinaC.Utils Require Import ListExt OptionExt.
From GallinaC.Imp Require Import Model.
From GallinaC.Compiler.Deep Require Import Denotation Cmd Prog.

Local Open Scope string_scope.

Definition deep_allocate: fundef :=
  Eval compute in
    match ListExt.sfind string_dec "allocate" deep_reverse_prog_symbols with
    | Some id =>
        match ListExt.sfind Pos.eq_dec id deep_reverse_prog.(prog_defs) with
        | Some (AST.Gfun fd) => fd
        | _ => AST.External AST.EF_free
        end
    | None => AST.External AST.EF_free
    end.

Definition wt_allocate: Typing.wt_fundef {| ctxt_pure := Maps.PTree.empty _; ctxt_stack := []; ctxt_global := Globalenvs.Genv.globalenv deep_reverse_prog |} deep_allocate := ltac:(now repeat constructor).
