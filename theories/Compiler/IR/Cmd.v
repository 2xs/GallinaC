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

From Corelib Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

From Stdlib Require Import Arith PArith.

From GallinaC.Utils Require Import PosExt NatExt ProdExt ListExt.

From GallinaC.Compiler.Common Require Export Types Ctxt Expr.

Inductive cmd : Set :=
| c_ret : expr -> type -> cmd
| c_bind : AST.ident -> type -> cmd -> cmd -> type -> cmd
| c_if : expr -> cmd -> cmd -> type -> cmd
| c_while : cmd -> AST.ident -> cmd -> AST.ident -> cmd
(* Store commands *)
| c_read_var : nat -> type -> cmd
| c_write_var : nat -> type -> expr -> cmd
(* Heap commands *)
| c_alloc_ptr : expr -> type -> expr -> AST.ident -> AST.ident -> AST.ident -> cmd
| c_read_ptr : expr -> type -> cmd
| c_write_ptr : expr -> type -> expr -> cmd
| c_free_ptr : expr -> cmd
(* Pointer commands *)
| c_shift_fw_ptr : expr -> expr -> cmd
| c_shift_bw_ptr : expr -> expr -> cmd
| c_ptr_eq : expr -> expr -> cmd
| c_app : AST.ident -> type -> list (expr * type) -> cmd
(* Numeric commands *)
| c_div : expr -> expr -> cmd
| c_mod : expr -> expr -> cmd
.

Fixpoint cmd_eqb (c1 c2: cmd): bool :=
  match c1, c2 with
  | c_ret e1 t1, c_ret e2 t2 => eqb e1 e2 && eqb t1 t2
  | c_bind id1 t_b1 c_b1 c_c1 t_c1, c_bind id2 t_b2 c_b2 c_c2 t_c2 =>
      eqb id1 id2 && eqb t_b1 t_b2
      && cmd_eqb c_b1 c_b2 && cmd_eqb c_c1 c_c2 && eqb t_c1 t_c2
  | c_if e1 c_t1 c_e1 t1, c_if e2 c_t2 c_e2 t2 =>
      eqb e1 e2 && cmd_eqb c_t1 c_t2 && cmd_eqb c_e1 c_e2 && eqb t1 t2
  | c_while cond1 id_cond1 body1 id_body1, c_while cond2 id_cond2 body2 id_body2 =>
      cmd_eqb cond1 cond2 && eqb id_cond1 id_cond2
      && cmd_eqb body1 body2 && eqb id_body1 id_body2
  | c_read_var o1 t1, c_read_var o2 t2 => eqb o1 o2 && eqb t1 t2
  | c_write_var o1 t1 e1, c_write_var o2 t2 e2 =>
      eqb o1 o2 && eqb t1 t2 && eqb e1 e2
  | c_alloc_ptr e_size1 t1 e_init1 id_p1 id_c1 id_i1,
    c_alloc_ptr e_size2 t2 e_init2 id_p2 id_c2 id_i2 =>
      eqb e_size1 e_size2 && eqb t1 t2 && eqb e_init1 e_init2
      && eqb id_p1 id_p2 && eqb id_c1 id_c2 && eqb id_i1 id_i2
  | c_read_ptr p1 t1, c_read_ptr p2 t2 => eqb p1 p2 && eqb t1 t2
  | c_write_ptr p1 t1 e1, c_write_ptr p2 t2 e2 =>
      eqb p1 p2 && eqb t1 t2 && eqb e1 e2
  | c_free_ptr p1, c_free_ptr p2 => eqb p1 p2
  | c_shift_fw_ptr p1 o1, c_shift_fw_ptr p2 o2 => eqb p1 p2 && eqb o1 o2
  | c_shift_bw_ptr p1 o1, c_shift_bw_ptr p2 o2 => eqb p1 p2 && eqb o1 o2
  | c_ptr_eq l1 r1, c_ptr_eq l2 r2 => eqb l1 l2 && eqb r1 r2
  | c_app f1 t1 args1, c_app f2 t2 args2 =>
      eqb f1 f2 && eqb t1 t2 && eqb args1 args2
  | c_div l1 r1, c_div l2 r2 => eqb l1 l2 && eqb r1 r2
  | c_mod l1 r1, c_mod l2 r2 => eqb l1 l2 && eqb r1 r2
  | _, _ => false
  end.

Lemma cmd_eqb_spec: forall x y, Bool.reflect (x = y) (cmd_eqb x y).
Proof.
  induction x; destruct y; cbn -[eqb];
    repeat
      match goal with
      | IH: forall y, Bool.reflect (?c = y) (cmd_eqb ?c y) |- context [ cmd_eqb ?c ?y' ] =>
          destruct (IH y')
      | |- context [ @eqb ?A ?l ?r ] => destruct (@eqb_spec A l r)
      end;
    subst; constructor; congruence.
Qed.

HB.instance Definition _ := hasEqDec.Build cmd cmd_eqb cmd_eqb_spec.

Fixpoint cmd_temps (c: cmd): list (AST.ident * type) :=
  match c with
  | c_bind id_b t_b c_b c_c _ => (id_b, t_b) :: cmd_temps c_b ++ cmd_temps c_c
  | c_if _ c_then c_else _ => cmd_temps c_then ++ cmd_temps c_else
  | c_while c_cond _ c_body _ => cmd_temps c_cond ++ cmd_temps c_body
  | c_ret _ _
  | c_read_var _ _ | c_write_var _ _ _
  | c_alloc_ptr _ _ _ _ _ _ | c_read_ptr _ _
  | c_write_ptr _ _ _ | c_free_ptr _
  | c_shift_fw_ptr _ _ | c_shift_bw_ptr _ _
  | c_ptr_eq _ _
  | c_app _ _ _
  | c_div _ _ | c_mod _ _
                         => []
  end.

Fixpoint cmd_internals (c: cmd): list (AST.ident * type) :=
  match c with
  | c_bind _ _ c_b c_c _ => cmd_internals c_b ++ cmd_internals c_c
  | c_if _ c_then c_else _ => cmd_internals c_then ++ cmd_internals c_else
  | c_while c_cond id_cond c_body id_body =>
      (id_cond, t_bool) :: (id_body, t_unit) :: cmd_internals c_cond ++ cmd_internals c_body
  | c_alloc_ptr _ t _ id_ptr id_count id_init =>
      [(id_ptr, t_ptr); (id_count, t_ofst); (id_init, t)]
  | c_ret _ _
  | c_read_var _ _ | c_write_var _ _ _
  | c_read_ptr _ _
  | c_write_ptr _ _ _ | c_free_ptr _
  | c_shift_fw_ptr _ _ | c_shift_bw_ptr _ _
  | c_ptr_eq _ _
  | c_app _ _ _
  | c_div _ _ | c_mod _ _
                         => []
  end.
