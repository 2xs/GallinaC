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

From Corelib.Setoids Require Import Setoid.
From Corelib Require Import ssreflect ssrfun ssrbool.
Import ssrfun.Option.
From HB Require Import structures.

Create HintDb seplog.
Create HintDb seplog_search.
Ltac seplog_search_auto := solve [eauto 60 with nocore seplog_search].

Declare Scope separation_scope.
Delimit Scope separation_scope with sep.
Local Open Scope separation_scope.

(* Non-empty types *)
HB.mixin Record isNonEmpty (T: Type) :=
  {
    non_empty_witness: T;
  }.
HB.structure Definition NonEmpty := { T of isNonEmpty T }.

(* An arbitrary relation *)
HB.mixin Record isRelation (T: Type) (R: T -> T -> Prop).
HB.structure Definition Relation (T: Type) := { R of isRelation T R }.

(* A relation is decidable, if a bool valued function reflects it *)
HB.mixin Record isDecRel (T: Type) (R: T -> T -> Prop) of isRelation T R :=
  {
    relb: T -> T -> bool;
    relb_spec: forall x y: T, reflect (R x y) (relb x y);
  }.
HB.structure Definition DecRel (T: Type) := { R of Relation T R & isDecRel T R }.

HB.mixin Record isReflRel  (T: Type) (R: T -> T -> Prop) of isRelation T R :=
  {
    rel_refl: forall x: T, R x x;
  }.
HB.structure Definition ReflRelation (T: Type) := { R of Relation T R & isReflRel T R }.

HB.mixin Record isSymmRel (T: Type) (R: T -> T -> Prop) of isRelation T R :=
  {
    rel_symm: forall x y: T, R x y -> R y x;
  }.
HB.structure Definition SymmRelation (T: Type) := { R of Relation T R & isSymmRel T R }.

HB.mixin Record isTranRel (T: Type) (R: T -> T -> Prop) of isRelation T R :=
  {
    rel_tran: forall x y z: T, R x y -> R y z -> R x z;
  }.
HB.structure Definition TranRelation (T: Type) := { R of Relation T R & isTranRel T R }.

#[global] Instance hb_Reflexive (T: Type) (R: ReflRelation.type T)
  : RelationClasses.Reflexive R := @rel_refl T R.
#[global] Instance hb_Symmetric (T: Type) (R: SymmRelation.type T)
  : RelationClasses.Symmetric R := @rel_symm T R.
#[global] Instance hb_Transitive (T: Type) (R: TranRelation.type T)
  : RelationClasses.Transitive R := @rel_tran T R.
(* If fails
Hint Extern 0 (RelationClasses.Reflexive _) => apply: rel_refl : typeclass_instances. *)

(* The relation mixins are indexed by the relation, not the type. The following
mixin allows to bridge the gap for mixins indexed on a type and wanting decidable equality *)

HB.mixin Record hasEqDec T :=
  {
    eqb: T -> T -> bool;
    eqb_spec: forall x y: T, reflect (x = y) (eqb x y);
  }.
HB.structure Definition EqDec := { T of hasEqDec T }.
HB.instance Definition _ (T: EqDec.type) := isRelation.Build T (@eq T).
HB.instance Definition _ (T: EqDec.type) :=
  isDecRel.Build T (@eq T) (@eqb T) (@eqb_spec T).
Notation "x =? y" := (eqb x y) (at level 70, no associativity): separation_scope.

(* A magma is an algebra without additional laws *)
HB.mixin Record hasOp (T: Type) :=
  {
    op: T -> T -> option T;
  }.
HB.structure Definition Magma := {T of hasOp T}.

(* Commutative algebras allow to swap the order of their operands *)
HB.mixin Record hasComm T of hasOp T :=
  {
    op_comm: forall x y: T, op x y = op y x;
  }.

(* Unital algebras posses an identity element which doesn't alter the result *)
HB.mixin Record hasIdentity T of hasOp T :=
  {
    id_e: T;
    op_id_l: forall x : T, op id_e x = Some x;
    op_id_r: forall x : T, op x id_e = Some x;
  }.

(* Associative algebras allow rearranging parantheses without changing the result *)
HB.mixin Record hasAssc T of hasOp T :=
  {
    op_assc: forall x y z : T, bind (Basics.flip (@op T) z) ((@op T) x y) = bind ((@op T) x) ((@op T) y z);
  }.

(* Cancelativity generalizes divisibility by not relying on an inverse element *)
HB.mixin Record hasCancel T of hasOp T :=
  {
    op_cancel_l: forall x y z w: T, op x y = Some w -> op x z = Some w -> y = z;
    op_cancel_r: forall x y z w: T, op y x = Some w -> op z x = Some w -> y = z;
  }.

(* Assume you have two operator applications yielding the same value.

   Cross split guarantees us that we can split the first operator's arguments to
   obtain the second operator's arguments. *)
HB.mixin Record hasCrossSplit T of hasOp T :=
  {
    op_cross_split: forall a b c d z: T,
      op a b = Some z -> op c d = Some z ->
      exists ac ad bc bd: T,
        op ac ad = Some a /\ op bc bd = Some b /\ op ac bc = Some c /\ op ad bd = Some d;
  }.

(* Some standard algebraic structures *)
HB.structure Definition CommMagma := {T of Magma T & hasComm T }.
HB.structure Definition UnitalMagma := {T of Magma T & hasIdentity T }.
HB.structure Definition Semigroup := { T of Magma T & hasAssc T }.
HB.structure Definition CommSemigroup := { T of Semigroup T & hasComm T }.
HB.structure Definition CancCommSemigroup := { T of CommSemigroup T & hasCancel T }.
HB.structure Definition Monoid := { T of Semigroup T & hasIdentity T }.
HB.structure Definition CommMonoid := { T of Monoid T & hasComm T }.

(** A separation algebra is a partial cancellative commutative monoid with cross split
    The monoid's operation is the union of separate states, hence it fails if states are not truly separate
 *)
HB.structure Definition Separation := { T of CommMonoid T & hasCancel T & hasCrossSplit T }.

Notation "$0" := (@id_e _) (at level 0, no associativity): separation_scope.
Notation "x $+ y" := (@op _ x y) (at level 50, no associativity): separation_scope.

#[global] Hint Resolve op_comm op_assc op_id_l op_id_r op_cancel_l op_cancel_r: seplog.
#[global] Hint Rewrite @op_id_l @op_id_r: seplog.

(** Interpretation of separation logic on top of a separation algebra
    - Disjointness [a $/= b] is a proof that separate parts can be combined
    - A substate-relation [a $<= b] is a proof that [a] could be extended to obtain [b]
 *)
Definition Separate [Sep: Magma.type] (a b: Sep) := exists c, a $+ b = Some c.
Definition Substate [Sep: Magma.type] (a c: Sep) := exists b, a $+ b = Some c.
Notation "a $/= b" := (Separate a b) (at level 75, no associativity): separation_scope.
Notation "a $<= c" := (Substate a c) (at level 75, no associativity): separation_scope.

Lemma separate_symm [T: CommMagma.type] (a b: T)
  (SEP: a $/= b)
  : b $/= a.
Proof.
  now unfold Separate; rewrite op_comm.
Qed.
#[global] Hint Resolve separate_symm: seplog.

Definition separateb [T: Magma.type] (a b: T): bool := isSome (a $+ b).

Lemma separateb_spec [T: Magma.type] (a b: T): reflect (a $/= b) (separateb a b).
Proof.
  rewrite /separateb /Separate.
  case E: (a $+ b) => [c|] /=; constructor.
  - now exists c.
  - by move=> [c].
Qed.

HB.instance Definition _ (T: Magma.type) := isRelation.Build T (@Separate T).
HB.instance Definition _ (T: CommMagma.type) :=
  isSymmRel.Build T (@Separate T) (@separate_symm T).
HB.instance Definition _ (T: Magma.type) :=
  isDecRel.Build T (@Separate T) (@separateb T) (@separateb_spec T).

Lemma substate_refl [T: UnitalMagma.type] (a: T)
  : a $<= a.
Proof.
  now unfold Substate;
    exists $0;
    apply @op_id_r.
Qed.
#[global] Hint Resolve substate_refl: seplog.

Lemma substate_tran [T: Semigroup.type] (a b c: T)
  (SUBab: a $<= b) (SUBbc: b $<= c)
  : a $<= c.
Proof.
  unfold Substate in *.
  destruct SUBab as (ab & EQab).
  destruct SUBbc as (bc & EQbc).
  specialize (@op_assc T a ab bc) as EQ.
  rewrite EQab in EQ; cbn in EQ.
  unfold Basics.flip in EQ.
  rewrite EQbc in EQ.
  assert (EQabbc: exists d, ab $+ bc = Some d).
  { destruct (ab $+ bc) as [abbc|] eqn:E.
    - exists abbc. reflexivity.
    - rewrite E in EQ. unfold bind in EQ. simpl in EQ. discriminate. }
  destruct EQabbc as [ d EQabbc ].
  exists d.
  now rewrite EQ; rewrite EQabbc.
Qed.
#[global] Hint Resolve substate_tran: seplog.

HB.instance Definition _ (T: Magma.type) := isRelation.Build T (@Substate T).
HB.instance Definition _ (T: Monoid.type) :=
  isReflRel.Build T (@Substate T) (@substate_refl T).
HB.instance Definition _ (T: Monoid.type) :=
  isTranRel.Build T (@Substate T) (@substate_tran T).

Lemma partition_separate [T: Magma.type] [a b c: T]
  (PART: a $+ b = Some c)
  : a $/= b.
Proof.
  now exists c.
Qed.
#[global] Hint Resolve partition_separate: seplog.

Lemma substate_of_partition_l [T: Magma.type] [a b c: T]
  (PART: a $+ b = Some c)
  : a $<= c.
Proof.
  now exists b.
Qed.
#[global] Hint Resolve substate_of_partition_l: seplog.

Lemma substate_of_partition_r [T: CommMagma.type] [a b c: T]
  (PART: a $+ b = Some c)
   : b $<= c.
Proof.
  rewrite op_comm in PART.
  eapply substate_of_partition_l, PART.
Qed.
#[global] Hint Resolve substate_of_partition_r: seplog.

Lemma separate_from_substate [T: Semigroup.type] [a b c: T]
  (SEP: a $/= b)
  (SUB: c $<= b)
  : a $/= c.
Proof.
  destruct SEP as (ab & SEP).
  destruct SUB as (d & SUB).
  specialize (@op_assc T a c d).
  rewrite SUB /= SEP.
  case (a $+ c) as [ac|] eqn:Eac.
  - rewrite Eac//=/Basics.flip/Separate.
    by exists ac.
  - by rewrite Eac.
Qed.
#[global] Hint Resolve separate_from_substate: seplog.

Lemma separate_emp_l [T: UnitalMagma.type] (a: T): $0 $/= a.
Proof.
  unfold Separate.
  exists a.
  by apply: op_id_l.
Qed.
#[global] Hint Resolve separate_emp_l: seplog.

Lemma separate_emp_r [T: UnitalMagma.type] (a: T): a $/= $0.
Proof.
  by eauto with seplog.
Qed.
#[global] Hint Resolve separate_emp_r: seplog.

Lemma op_swap [T: CommSemigroup.type] (x y z w v: T)
  (E1: x $+ y = Some w) (E2: w $+ z = Some v)
  : exists u, x $+ z = Some u /\ u $+ y = Some v.
Proof.
  have A1 := op_assc x y z.
  rewrite E1 /Basics.flip /= E2 in A1.
  have A2 := op_assc x z y.
  rewrite (op_comm z y) -A1 /Basics.flip /= in A2.
  case Exz: (x $+ z) => [u| ]; rewrite Exz /= in A2.
  - by exists u; split; [ | exact: A2 ].
  - by discriminate A2.
Qed.

Lemma partition_comm [T: CommMagma.type] [a b c: T]
  (EQ: a $+ b = Some c): b $+ a = Some c.
Proof.
  by etransitivity; [ apply: op_comm | exact: EQ ].
Qed.

Lemma partition_emp_l [T: UnitalMagma.type] [a b: T]
  (EQ: $0 $+ a = Some b): a = b.
Proof.
  have EQa := op_id_l a.
  have EQa': Some a = Some b := eq_trans (eq_sym EQa) EQ.
  by move: EQa' => [ -> ].
Qed.

Lemma partition_emp_r [T: UnitalMagma.type] [a b: T]
  (EQ: a $+ $0 = Some b): a = b.
Proof.
  have EQa := op_id_r a.
  have EQa': Some a = Some b := eq_trans (eq_sym EQa) EQ.
  by move: EQa' => [ -> ].
Qed.

Lemma partition_assoc [T: Separation.type] [a b c ab abc: T]
  (EQab: a $+ b = Some ab) (EQabc: ab $+ c = Some abc)
  : exists bc, b $+ c = Some bc /\ a $+ bc = Some abc.
Proof.
  have ASSC := op_assc a b c.
  have ASSC': ssrfun.Option.bind (Basics.flip op c) (Some ab)
              = ssrfun.Option.bind (op a) (b $+ c)
    := eq_trans (eq_sym (f_equal (ssrfun.Option.bind (Basics.flip op c)) EQab)) ASSC.
  cbn in ASSC'.
  rewrite /Basics.flip in ASSC'.
  have EQabc': ssrfun.Option.bind (op a) (b $+ c) = Some abc
    := eq_trans (eq_sym ASSC') EQabc.
  destruct (b $+ c) as [ bc | ] eqn:E; cbn in EQabc'; last by [].
  exists bc.
  by split.
Qed.

Lemma partition_assoc_rev [T: Separation.type] [a b c bc abc: T]
  (EQbc: b $+ c = Some bc) (EQabc: a $+ bc = Some abc)
  : exists ab, a $+ b = Some ab /\ ab $+ c = Some abc.
Proof.
  move/partition_comm: EQbc => EQbc.
  move/partition_comm: EQabc => EQabc.
  case: (partition_assoc EQbc EQabc) => ba [ EQba EQfull ].
  move/partition_comm: EQba => EQba.
  move/partition_comm: EQfull => EQfull.
  case: (partition_assoc EQba EQfull) => ab [ EQab EQfin ].
  by eauto.
Qed.

Lemma partition_swap4 [T: Separation.type] [a b c d ab cd z: T]
  (Eab: a $+ b = Some ab) (Ecd: c $+ d = Some cd) (Ez: ab $+ cd = Some z)
  : exists ac bd, a $+ c = Some ac /\ b $+ d = Some bd /\ ac $+ bd = Some z.
Proof.
  case: (partition_assoc Eab Ez) => bcd [ Ebcd Eabcd ].
  move/partition_comm: Ecd => Edc.
  case: (partition_assoc_rev Edc Ebcd) => bd [ Ebd Ebdc ].
  move/partition_comm: Ebdc => Ecbd.
  case: (partition_assoc_rev Ecbd Eabcd) => ac [ Eac Eacbd ].
  by exists ac, bd.
Qed.
