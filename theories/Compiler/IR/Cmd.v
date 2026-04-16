From Stdlib Require Import Arith PArith.

From GallinaC.Compiler.Common Require Export Types Ctxt Expr.

Inductive cmd : Type :=
| c_ret : expr -> type -> cmd
| c_bind : AST.ident -> type -> cmd -> cmd -> type -> cmd
| c_if : expr -> cmd -> cmd -> type -> cmd
| c_while : cmd -> AST.ident -> cmd -> AST.ident -> cmd
(* Store commands *)
| c_read_var : nat -> type -> cmd
| c_write_var : nat -> type -> expr -> cmd
(* Heap commands *)
| c_alloc_ptr : expr -> type -> expr -> AST.ident -> AST.ident -> cmd
| c_read_ptr : expr -> type -> cmd
| c_write_ptr : expr -> type -> expr -> cmd
| c_free_ptr : expr -> cmd
(* Pointer commands *)
| c_shift_fw_ptr : expr -> expr -> cmd
| c_shift_bw_ptr : expr -> expr -> cmd
| c_ptr_eq : expr -> expr -> cmd
| c_app : AST.ident -> type -> list (expr * type) -> cmd
.
