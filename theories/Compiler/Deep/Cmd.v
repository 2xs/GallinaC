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

From Stdlib Require Import Arith PArith.

From HB Require Import structures.

From GallinaC.Utils Require Import Algebra ListExt.
From GallinaC.Compiler.Common Require Export Types Ctxt Expr.

Inductive cmd : Set :=
| c_ret : forall (e: expr), cmd
| c_bind : forall (id_b: AST.ident) (t_b: type) (c_b c_c: cmd), cmd
| c_if : forall (e_if: expr) (c_then c_else: cmd), cmd
| c_while : forall (c_cond c_body: cmd), cmd
(* Store commands *)
| c_with_var : forall (t_v: type) (e_v: expr) (c_c: cmd), cmd
| c_read_var : forall (o_v: nat) (t_v: type), cmd
| c_write_var : forall (o_v: nat) (t_v: type) (e_v: expr), cmd
(* Heap commands *)
| c_alloc_ptr : forall (e_size: expr) (t_init: type) (e_init: expr), cmd
| c_read_ptr : forall (e_ptr: expr) (t_val: type), cmd
| c_write_ptr : forall (e_ptr: expr) (t_val: type) (e_val: expr), cmd
| c_free_ptr : forall (e_ptr: expr), cmd
(* Pointer commands *)
| c_shift_fw_ptr : forall (e_ptr e_ofst: expr), cmd
| c_shift_bw_ptr : forall (e_ptr e_ofst: expr), cmd
| c_ptr_eq : forall (e_ptr_l e_ptr_r: expr), cmd
| c_app : forall (f_id: AST.ident) (args: list expr), cmd
(* Numeric commands *)
| c_div : forall (e_l e_r: expr), cmd
| c_mod: forall (e_l e_r: expr), cmd
.

Fixpoint cmd_eqb (c1 c2: cmd): bool :=
  match c1, c2 with
  | c_ret e1, c_ret e2 => expr_eqb e1 e2
  | c_bind i1 t_b1 c_b1 c_c1, c_bind i2 t_b2 c_b2 c_c2 =>
      (Pos.eqb i1 i2 &&
         type_eqb t_b1 t_b2 &&
         cmd_eqb c_b1 c_b2 &&
         cmd_eqb c_c1 c_c2)
  | c_if i1 t1 e1, c_if i2 t2 e2 =>
      (expr_eqb i1 i2 &&
         cmd_eqb t1 t2 &&
         cmd_eqb e1 e2)%bool
  | c_while cond1 body1, c_while cond2 body2 =>
      (cmd_eqb cond1 cond2 &&
         cmd_eqb body1 body2)%bool
  | c_with_var t1 e_v1 c_c1, c_with_var t2 e_v2 c_c2 =>
      (type_eqb t1 t2 && expr_eqb e_v1 e_v2 && cmd_eqb c_c1 c_c2)
  | c_read_var v1 t1, c_read_var v2 t2 => (Nat.eqb v1 v2 && type_eqb t1 t2)
  | c_write_var v1 t1 e1, c_write_var v2 t2 e2 =>
      (Nat.eqb v1 v2 && type_eqb t1 t2 && expr_eqb e1 e2)
  | c_alloc_ptr e_size1 t1 e_init1, c_alloc_ptr e_size2 t2 e_init2 =>
      expr_eqb e_size1 e_size2 && type_eqb t1 t2 && expr_eqb e_init1 e_init2
  | c_read_ptr p1 t1, c_read_ptr p2 t2 => (type_eqb t1 t2 && expr_eqb p1 p2)%bool
  | c_write_ptr p1 t1 e1, c_write_ptr p2 t2 e2 =>
      (type_eqb t1 t2 && expr_eqb p1 p2 && expr_eqb e1 e2)%bool
  | c_free_ptr p1, c_free_ptr p2 => expr_eqb p1 p2
  | c_shift_fw_ptr e_ptr_l1 e_ptr_r1, c_shift_fw_ptr e_ptr_l2 e_ptr_r2 =>
      (expr_eqb e_ptr_l1 e_ptr_l2 && expr_eqb e_ptr_r1 e_ptr_r2)%bool
  | c_shift_bw_ptr e_ptr_l1 e_ptr_r1, c_shift_bw_ptr e_ptr_l2 e_ptr_r2 =>
      (expr_eqb e_ptr_l1 e_ptr_l2 && expr_eqb e_ptr_r1 e_ptr_r2)%bool
  | c_ptr_eq l1 r1, c_ptr_eq l2 r2 =>
      (expr_eqb l1 l2 && expr_eqb r1 r2)
  | c_app f1 args1, c_app f2 args2 =>
      (Pos.eqb f1 f2 && ListExt.list_eqb expr_eqb args1 args2)%bool
  | c_div l1 r1, c_div l2 r2 =>
      (expr_eqb l1 l2 && expr_eqb r1 r2)%bool
  | c_mod l1 r1, c_mod l2 r2 =>
      (expr_eqb l1 l2 && expr_eqb r1 r2)%bool
  | _, _ => false
  end.

Lemma cmd_eqb_spec: forall x y, Bool.reflect (x = y) (cmd_eqb x y).
Proof.
  induction x;
    destruct y;
    cbn;
    (try (constructor; congruence));
    (try (destruct (expr_eqb_spec e e0); constructor; congruence)).
  - destruct (Pos.eqb_spec id_b id_b0);
      destruct (type_eqb_spec t_b t_b0);
      destruct (IHx1 y1);
      destruct (IHx2 y2);
      subst; constructor; congruence.
  - destruct (expr_eqb_spec e_if e_if0);
      destruct (IHx1 y1);
      destruct (IHx2 y2);
      subst; constructor; congruence.
  - destruct (IHx1 y1);
      destruct (IHx2 y2);
      subst; constructor; congruence.
  - destruct (type_eqb_spec t_v t_v0); [ subst; cbn | constructor; congruence ].
    destruct (expr_eqb_spec e_v e_v0); [ subst; cbn | constructor; congruence ].
    destruct (IHx y); constructor; congruence.
  - destruct (Nat.eqb_spec o_v o_v0);
      destruct (type_eqb_spec t_v t_v0);
      constructor; congruence.
  - destruct (Nat.eqb_spec o_v o_v0);
      destruct (type_eqb_spec t_v t_v0);
      destruct (expr_eqb_spec e_v e_v0);
      subst; constructor; congruence.
  - destruct (expr_eqb_spec e_size e_size0);
      destruct (type_eqb_spec t_init t_init0);
      destruct (expr_eqb_spec e_init e_init0);
      subst; constructor; congruence.
  - destruct (expr_eqb_spec e_ptr e_ptr0);
      destruct (type_eqb_spec t_val t_val0);
      constructor; congruence.
  - destruct (expr_eqb_spec e_ptr e_ptr0);
      destruct (type_eqb_spec t_val t_val0);
      destruct (expr_eqb_spec e_val e_val0);
      subst; constructor; congruence.
  - destruct (expr_eqb_spec e_ptr e_ptr0); constructor; congruence.
  - destruct (expr_eqb_spec e_ptr e_ptr0);
      destruct (expr_eqb_spec e_ofst e_ofst0);
      constructor; congruence.
  - destruct (expr_eqb_spec e_ptr e_ptr0);
      destruct (expr_eqb_spec e_ofst e_ofst0);
      constructor; congruence.
  - destruct (expr_eqb_spec e_ptr_l e_ptr_l0);
      destruct (expr_eqb_spec e_ptr_r e_ptr_r0);
      constructor; congruence.
  - destruct (Pos.eqb_spec f_id f_id0);
      destruct (ListExt.list_eqb_spec _ args args0 expr_eqb_spec);
      cbn; subst; constructor; congruence.
  - destruct (expr_eqb_spec e_l e_l0);
      destruct (expr_eqb_spec e_r e_r0);
      cbn; subst; constructor; congruence.
  - destruct (expr_eqb_spec e_l e_l0);
      destruct (expr_eqb_spec e_r e_r0);
      cbn; subst; constructor; congruence.
Qed.

HB.instance Definition _ := hasEqDec.Build cmd cmd_eqb cmd_eqb_spec.

Definition cmd_eqb_refl: forall c, cmd_eqb c c = true :=
  ReflectExt.reflect_refl cmd_eqb_spec.
#[global] Hint Resolve cmd_eqb_refl: deep_gallinac.
#[global] Hint Rewrite cmd_eqb_refl: deep_gallinac.

Fixpoint cmd_temps (c: cmd): list (AST.ident * type) :=
  match c with
  | c_bind b_id t_b c_b c_c => (b_id, t_b) :: cmd_temps c_b ++ cmd_temps c_c
  | c_if _ c_then c_else => cmd_temps c_then ++ cmd_temps c_else
  | c_while c_cond c_body => cmd_temps c_cond ++ cmd_temps c_body
  | c_with_var _ _ c_c => cmd_temps c_c
  | c_ret _
  | c_read_var _ _ | c_write_var _ _ _
  | c_alloc_ptr _ _ _ | c_read_ptr _ _
  | c_write_ptr _ _ _ | c_free_ptr _
  | c_shift_fw_ptr _ _ | c_shift_bw_ptr _ _
  | c_ptr_eq _ _
  | c_app _ _
  | c_div _ _ | c_mod _ _
                => []
  end.

Lemma cmd_temps_bind b_id t_b c_b c_c:
  cmd_temps (c_bind b_id t_b c_b c_c)
  = (b_id, t_b) :: cmd_temps c_b ++ cmd_temps c_c.
Proof. reflexivity. Qed.

Lemma cmd_temps_if e c_t c_e:
  cmd_temps (c_if e c_t c_e) = cmd_temps c_t ++ cmd_temps c_e.
Proof. reflexivity. Qed.

Lemma cmd_temps_while c_cond c_body:
  cmd_temps (c_while c_cond c_body)
  = cmd_temps c_cond ++ cmd_temps c_body.
Proof. reflexivity. Qed.

Lemma cmd_temps_with_var t_v e_v c_c:
  cmd_temps (c_with_var t_v e_v c_c) = cmd_temps c_c.
Proof. reflexivity. Qed.
