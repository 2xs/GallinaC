From Stdlib Require Import PArith NArith Arith List.
Import ListNotations.
From MetaRocq.Utils Require Export bytestring.

From compcert.common Require AST.

From GallinaC.Utils Require ListExt ReflectExt.

Create HintDb deep_gallinac.

Inductive type: Type :=
| t_unit
| t_bool
| t_nat
| t_ofst
| t_ptr
| t_fun : forall (ti: list type) (to: type), type
.

Fixpoint type_eqb (t1 t2: type): bool :=
  match t1, t2 with
  | t_unit, t_unit => true
  | t_bool, t_bool => true
  | t_nat, t_nat => true
  | t_ofst, t_ofst => true
  | t_ptr, t_ptr => true
  | t_fun ti1 to1, t_fun ti2 to2 =>
      (ListExt.list_eqb type_eqb ti1 ti2 && type_eqb to1 to2)%bool
  | _,_ => false
  end.

Lemma type_eqb_spec: forall (x y: type), Bool.reflect (x = y) (type_eqb x y).
Proof.
  fix IH 1.
  destruct x as [ | | | | | ti1 to1 ];
    destruct y as [ | | | | | ti2 to2 ];
    (try (constructor; congruence));
    cbn.
  destruct (IH to1 to2); [ subst to2; rewrite Bool.andb_true_r | rewrite Bool.andb_false_r; constructor; congruence ].
  assert (HProof: Bool.reflect (ti1 = ti2) (ListExt.list_eqb type_eqb ti1 ti2) -> Bool.reflect (t_fun ti1 to1 = t_fun ti2 to1) (ListExt.list_eqb type_eqb ti1 ti2))
    by (intros HProof; destruct HProof; constructor; congruence);
    apply HProof; clear HProof.
  revert ti2.
  induction ti1 as [ | ti1 tis1 ]; destruct ti2 as [ | ti2 tis2 ];
    (try (constructor; congruence)).
  cbn.
  destruct (IH ti1 ti2); cbn; try (constructor; congruence).
  fold (ListExt.list_eqb type_eqb tis1 tis2).
  destruct (IHtis1 tis2); [ subst tis2 | ];
    constructor; congruence.
Qed.

Definition type_eq_dec: forall (x y: type), { x = y } + { x <> y } := ReflectExt.eq_dec_of_reflect type_eqb_spec.

Definition type_eqb_refl: forall t, type_eqb t t = true := ReflectExt.reflect_refl type_eqb_spec.
Hint Resolve type_eqb_refl: deep_gallinac.
Hint Rewrite type_eqb_refl: deep_gallinac.

Lemma type_eqb_eq: forall x y, type_eqb x y = true <-> x = y.
Proof.
  intros x y; split; intros H.
  - destruct (type_eqb_spec x y); congruence.
  - subst; apply type_eqb_refl.
Qed.
Hint Resolve type_eqb_eq: deep_gallinac.

Lemma type_eqb_neq: forall x y, type_eqb x y = false <-> x <> y.
Proof.
  intros x y; split; intros H.
  - intros contra; subst; rewrite type_eqb_refl in H; congruence.
  - destruct (type_eqb_spec x y); congruence.
Qed.
Hint Resolve type_eqb_neq: deep_gallinac.

Inductive ground: type -> Prop :=
| ground_unit: ground t_unit
| ground_bool: ground t_bool
| ground_nat : ground t_nat
| ground_ofst: ground t_ofst
| ground_ptr : ground t_ptr
.
Hint Constructors ground: deep_gallinac.

Inductive nonground: type -> Prop :=
| nonground_t_fun: forall ti to, nonground (t_fun ti to)
.
Hint Constructors nonground: deep_gallinac.

Inductive Sized: type -> Prop :=
| sized_bool: Sized t_bool
| sized_nat: Sized t_nat
| sized_ofst: Sized t_ofst
| sized_ptr: Sized t_ptr
.
Hint Constructors Sized: deep_gallinac.

Definition sized (t: type): bool :=
  match t with
  | t_unit => false
  | t_bool => true
  | t_nat => true
  | t_ofst => true
  | t_ptr => true
  | t_fun _ _ => false
  end.

Definition ground_dec_total (t : type) : (ground t) + (nonground t).
Proof.
  destruct t; now repeat constructor.
Defined.

Lemma ground_nonground_exclude: forall t, ground t -> nonground t -> False.
Proof.
  intros t Hground Hnonground;
    destruct t;
    try now inversion Hground;
    try now inversion Hnonground.
Qed.
Hint Resolve ground_nonground_exclude: deep_gallinac.

Lemma sized_spec: forall t, Bool.reflect (Sized t) (sized t).
Proof.
  destruct t; constructor; try constructor; intros contra; inversion contra.
Qed.

Lemma sized_ground: forall t, Sized t -> ground t.
Proof.
  intros t H; destruct H; constructor.
Qed.
Hint Resolve sized_ground: deep_gallinac.

Lemma is_t_fun_dec: forall t, { targ : list type & { to : type & t = t_fun targ to } } + { forall targs to, t <> t_fun targs to }.
Proof.
  induction t;
    try (constructor; congruence).
  now repeat econstructor.
Qed.
