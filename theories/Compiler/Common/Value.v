From Stdlib Require Import Arith ZArith List SetoidList.

From GallinaC.Imp Require Import Heap Store Pointer Intops.
From GallinaC.Compiler.Common Require Import Types.

Inductive value :=
| v_tt   : value
| v_bool : bool -> value
| v_nat  : forall (n: nat), value
| v_ofst : forall (n: N.t), value
| v_ptr  : Pointer.t -> value
.

Inductive sized: value -> Prop :=
| sized_bool: forall b, sized (v_bool b)
| sized_nat: forall n, sized (v_nat n)
| sized_ofst: forall n, sized (v_ofst n)
| sized_ptr: forall p, sized (v_ptr p)
.

Inductive value_memval: value -> memval -> Prop :=
| value_memval_unit: value_memval v_tt VUnit
| value_memval_bool: forall b, value_memval (v_bool b) (VBool b)
| value_memval_nat: forall n, value_memval (v_nat n) (VInt n)
| value_memval_ofst: forall n, value_memval (v_ofst n) (VOfst n)
| value_memval_ptr: forall p, value_memval (v_ptr p) (VPtr p)
.

Inductive wt_value: value -> type -> Prop :=
| wt_v_tt: wt_value v_tt t_unit
| wt_v_bool: forall b, wt_value (v_bool b) t_bool
| wt_v_nat: forall n, wt_value (v_nat n) t_nat
| wt_v_ofst: forall n, wt_value (v_ofst n) t_ofst
| wt_v_ptr: forall p, wt_value (v_ptr p) t_ptr
.

Definition value_of_memval (v: memval): value :=
  match v with
  | VUnit => v_tt
  | VInt i => v_nat i
  | VOfst o => v_ofst o
  | VPtr p => v_ptr p
  | VBool b => v_bool b
  end.

Definition memval_of_value (v: value): memval :=
  match v with
  | v_tt => VUnit
  | v_bool b => VBool b
  | v_nat n => VInt n
  | v_ofst o => VOfst o
  | v_ptr p => VPtr p
  end.

Module Facts.

  Lemma value_of_memval_spec: forall v v', value_memval v v' <-> value_of_memval v' = v.
  Proof.
    intros v v'.
    split.
    - intros H; inversion H; subst; reflexivity.
    - intros H;
        destruct v';
        cbn in H; subst;
        constructor.
  Qed.

  Lemma memval_of_value_spec: forall v v', value_memval v v' <-> memval_of_value v = v'.
  Proof.
    intros v v'; split.
    - intros H; inversion H; subst; reflexivity.
    - destruct v; intros H; subst; constructor.
  Qed.

  Lemma value_sized_memval [v] (Hsized: sized v): exists v', value_memval v v'.
  Proof.
    destruct Hsized;
      (try (eexists; now econstructor)).
  Qed.

  Lemma value_memval_fun_l: forall [v1 v2 v'], value_memval v1 v' -> value_memval v2 v' -> v2 = v1.
  Proof.
    intros v1 v2 v' H H'.
    inversion H; subst; inversion H'; now subst.
  Qed.
  Hint Resolve value_memval_fun_l: deep_gallinac.
  Hint Rewrite value_memval_fun_l: deep_gallinac.

  Lemma value_memval_fun_r: forall [v v1 v2], value_memval v v1 -> value_memval v v2 -> v2 = v1.
  Proof.
    intros v v1 v2 H H'.
    inversion H; subst; inversion H'; now subst.
  Qed.
  Hint Resolve value_memval_fun_r: deep_gallinac.
  Hint Rewrite value_memval_fun_r: deep_gallinac.

  Lemma sized_or_unit_dec: forall v, { sized v /\ v <> v_tt } + { v = v_tt }.
  Proof.
    destruct v;
      (try now constructor);
      left; (split; [ constructor | discriminate ]).
    Qed.

  Lemma wt_value_fun: forall {v t1 t2}, wt_value v t1 -> wt_value v t2 -> t2 = t1.
  Proof.
    intros v t1 t2 Hwt_v1 Hwt_v2.
    inversion Hwt_v1; subst;
      inversion Hwt_v2; subst;
      congruence.
  Qed.
  #[global] Hint Resolve wt_value_fun: deep_gallinac.

  Lemma wt_value_sized v t (WT: wt_value v t) (SIZED: Value.sized v): Types.sized t.
  Proof.
    destruct WT; inversion SIZED; constructor.
  Qed.
  #[global] Hint Resolve wt_value_sized: deep_gallinac.

End Facts.
