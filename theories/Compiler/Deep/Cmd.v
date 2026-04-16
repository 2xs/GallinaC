From Stdlib Require Import Arith PArith.

From GallinaC.Compiler.Common Require Export Types Ctxt Expr.

Inductive cmd : Type :=
| c_ret : expr -> cmd
| c_bind : AST.ident -> type -> cmd -> cmd -> cmd
| c_if : expr -> cmd -> cmd -> cmd
| c_while : cmd -> cmd -> cmd
(* Store commands *)
| c_with_var : type -> expr -> cmd -> cmd
| c_read_var : nat -> type -> cmd
| c_write_var : nat -> type -> expr -> cmd
(* Heap commands *)
| c_alloc_ptr : expr -> type -> expr -> cmd
| c_read_ptr : expr -> type -> cmd
| c_write_ptr : expr -> type -> expr -> cmd
| c_free_ptr : expr -> cmd
(* Pointer commands *)
| c_shift_fw_ptr : expr -> expr -> cmd
| c_shift_bw_ptr : expr -> expr -> cmd
| c_ptr_eq : expr -> expr -> cmd
| c_app : AST.ident -> list expr -> cmd
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
  | _, _ => false
  end.

Lemma cmd_eq_dec: forall (x y: cmd), { x = y } + { x <> y }.
Proof.
  induction x;
    destruct y;
    (try (constructor; congruence));
    (try (destruct (expr_eq_dec e0 e); constructor; congruence)).
  - destruct (IHx1 y1); [ subst | right; congruence ].
    destruct (IHx2 y2); [ subst | right; congruence ].
    destruct (Pos.eq_dec i i0); [ subst | right; congruence ].
    destruct (type_eq_dec t t0);
      subst; constructor; congruence.
  - destruct (IHx1 y1); [ subst | right; congruence ].
    destruct (IHx2 y2); [ subst | right; congruence ].
    destruct (expr_eq_dec e e0); constructor; congruence.
  - destruct (IHx1 y1); [ subst | constructor; congruence ].
    destruct (IHx2 y2); constructor; congruence.
  - destruct (expr_eq_dec e e0); [ subst | right; congruence ].
    destruct (IHx y); [ subst | right; congruence ].
    destruct (type_eq_dec t t0); constructor; congruence.
  - destruct (Nat.eq_dec n n0); [ subst | constructor; congruence ].
    destruct (type_eq_dec t t0); constructor; congruence.
  - destruct (Nat.eq_dec n n0); [ subst | constructor; congruence ].
    destruct (type_eq_dec t t0); [ subst | constructor; congruence ].
    destruct (expr_eq_dec e e0); constructor; congruence.
  - destruct (expr_eq_dec e e1); [ subst | constructor; congruence ].
    destruct (type_eq_dec t t0); [ subst | constructor; congruence ].
    destruct (expr_eq_dec e0 e2); constructor; congruence.
  - destruct (expr_eq_dec e e0); [ subst | constructor; congruence ].
    destruct (type_eq_dec t t0); constructor; congruence.
  - destruct (expr_eq_dec e e1); [ subst | constructor; congruence ].
    destruct (type_eq_dec t t0); [ subst | constructor; congruence ].
    destruct (expr_eq_dec e0 e2); constructor; congruence.
  - destruct (expr_eq_dec e e1); [ subst | right; congruence ].
    destruct (expr_eq_dec e0 e2); subst; constructor; congruence.
  - destruct (expr_eq_dec e e1); [ subst | right; congruence ].
    destruct (expr_eq_dec e0 e2); subst; constructor; congruence.
  - destruct (expr_eq_dec e e1); [ subst | right; congruence ].
    destruct (expr_eq_dec e0 e2); subst; constructor; congruence.
  - destruct (Pos.eq_dec i i0); [ subst | constructor; congruence ].
    destruct (List.list_eq_dec expr_eq_dec l l0); constructor; congruence.
Qed.

Lemma cmd_eqb_refl: forall c, cmd_eqb c c = true.
Proof.
  induction c;
    cbn;
    repeat
      first
      [ apply andb_true_intro
      | split
      | apply Nat.eqb_refl
      | apply Pos.eqb_refl
      | apply expr_eqb_refl
      | apply expr_eqb_spec
      | apply type_eqb_refl
      | apply type_eqb_spec
      | apply ReflectExt.eq_dec_refl_if
      | apply ReflectExt.pair_eqb_refl
      | apply ReflectExt.pair_eqb_spec
      | apply ListExt.list_eqb_refl
      | assumption
      | reflexivity
      ].
Qed.

Lemma cmd_eqb_spec: forall x y, Bool.reflect (x = y) (cmd_eqb x y).
Proof.
  induction x;
    destruct y;
    cbn;
    (try (constructor; now congruence));
    (try (destruct (expr_eqb_spec e e0); constructor; congruence)).
  - destruct (Pos.eqb_spec i i0);
      destruct (type_eqb_spec t t0);
      destruct (IHx1 y1);
      destruct (IHx2 y2);
      subst; constructor; congruence.
  - destruct (expr_eqb_spec e e0); [ subst; cbn | constructor; congruence ].
    destruct (IHx1 y1); [ subst; cbn | constructor; congruence ].
    destruct (IHx2 y2); constructor; congruence.
  - destruct (IHx1 y1);
      destruct (IHx2 y2);
      constructor;
      congruence.
  - destruct (type_eqb_spec t t0); [ subst; cbn | constructor; congruence ].
    destruct (expr_eqb_spec e e0); [ subst; cbn | constructor; congruence ].
    destruct (IHx y); constructor; congruence.
  - destruct (Nat.eqb_spec n n0);
      destruct (type_eqb_spec t t0);
      constructor; congruence.
  - destruct (Nat.eqb_spec n n0);
      destruct (type_eqb_spec t t0);
      destruct (expr_eqb_spec e e0);
      subst; constructor; congruence.
  - destruct (expr_eqb_spec e e1);
      destruct (expr_eqb_spec e0 e2);
      destruct (type_eqb_spec t t0);
      constructor; congruence.
  - destruct (expr_eqb_spec e e0);
      destruct (type_eqb_spec t t0);
      constructor; congruence.
  - destruct (type_eqb_spec t t0);
      destruct (expr_eqb_spec e e1);
      destruct (expr_eqb_spec e0 e2);
      constructor;
      congruence.
  - destruct (expr_eqb_spec e e1);
      destruct (expr_eqb_spec e0 e2);
      constructor; congruence.
  - destruct (expr_eqb_spec e e1);
      destruct (expr_eqb_spec e0 e2);
      constructor; congruence.
  - destruct (expr_eqb_spec e e1);
      destruct (expr_eqb_spec e0 e2);
      constructor; congruence.
  - destruct (Pos.eqb_spec i i0);
      destruct (ListExt.list_eqb_spec _ l l0 expr_eqb_spec);
      cbn; subst; constructor; congruence.
Qed.
#[global] Hint Resolve cmd_eqb_refl: deep_gallinac.
#[global] Hint Rewrite cmd_eqb_refl: deep_gallinac.
