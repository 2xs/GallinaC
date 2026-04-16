From Stdlib Require Import Psatz Arith NArith.

From GallinaC.Utils Require Import ListExt.
From GallinaC.Imp Require Export Monad Primitives Pointer.
From GallinaC.Compiler.Common Require Export Types Ctxt.

Local Open Scope program_scope.

Local Obligation Tactic := idtac.

Fixpoint type_depth (t: type): nat :=
  match t with
  | t_unit => 1
  | t_bool => 1
  | t_nat => 1
  | t_ofst => 1
  | t_ptr => 1
  | t_fun t_args t_out =>
      S ((List.fold_right Nat.add 0 (List.map type_depth t_args)) + (type_depth t_out))
  end.

Lemma type_depth_pos: forall t, 1 <= type_depth t.
Proof.
  induction t; cbn; lia.
Qed.

Section State.
  Context [St: Store.Store].
  Context [Hp: Heap.Heap].

  Program Fixpoint denote_type (t: type) {measure (type_depth t)} : Type :=
    match t with
    | t_unit => unit
    | t_bool => bool
    | t_nat => nat
    | t_ofst => N.t
    | t_ptr => Pointer.t
    | t_fun [] t_out => program (State St Hp) (denote_type t_out)
    | t_fun (t_arg::t_args) t_out => (denote_type t_arg) -> (denote_type (t_fun t_args t_out))
    end.

  Next Obligation.
    intros; subst; cbn; lia.
  Defined.

  Next Obligation.
    intros; subst; cbn; lia.
  Defined.

  Next Obligation.
    intros; subst; cbn;
      specialize (type_depth_pos t_arg);
      lia.
  Defined.

  Next Obligation.
    apply well_founded_ltof.
  Defined.

End State.
