From Stdlib Require ssrfun Basics.
Import ssrfun.Option.

Create HintDb seplog.

Declare Scope separation_scope.
Local Open Scope separation_scope.
Delimit Scope separation_scope with sep.

(** A spearation algebra is a partial commutative monoid
    The monoid's operation is the union of separate states, hence it fails if states are not truly separate
 *)
Record Separation: Type :=
  {
    carrier :> Type;
    op: carrier -> carrier -> option carrier;
    id_e: carrier;
    op_comm: forall x y: carrier, op x y = op y x;
    op_assc: forall x y z, bind (Basics.flip op z) (op x y) = bind (op x) (op y z);
    op_id_l: forall x, op id_e x = Some x;
    op_id_r: forall x, op x id_e = Some x;
  }.
Arguments carrier Sep: rename, simpl never.
Arguments op [Sep] x y: rename, simpl never.
Arguments id_e {Sep}: rename, simpl never.
Arguments op_comm [Sep] x y: rename, simpl never.
Arguments op_assc [Sep] x y z: rename, simpl never.
Arguments op_id_l [Sep] x: rename, simpl never.
Arguments op_id_r [Sep] x: rename, simpl never.

Notation "$0" := (@id_e _) (at level 0, no associativity): separation_scope.
Notation "x $+ y" := (@op _ x y) (at level 50, no associativity): separation_scope.

Hint Resolve op_comm op_assc op_id_l op_id_r: seplog.
Hint Rewrite op_id_l op_id_r: seplog.

(** Interpretation of separation logic on top of a separation algebra

    - Disjointness [a $/= b] is a proof that separate parts can be combined
    - A substate-relation [a $<= b] is a proof that [a] could be extended to obtain [c]
    - A partitioning [c $= a $++ b] is a proof that [c] could be divided into [a] and [b]
 *)
Definition Separate [Sep: Separation] (a b: Sep) := exists c, a $+ b = Some c.
Definition Substate [Sep: Separation] (a c: Sep) := exists b, a $+ b = Some c.
Notation "a $/= b" := (Separate a b) (at level 75, no associativity): separation_scope.
Notation "a $<= c" := (Substate a c) (at level 75, no associativity): separation_scope.

From Corelib.Setoids Require Import Setoid.

Lemma separate_symm [Sep: Separation] (a b: Sep)
  (SEP: a $/= b)
  : b $/= a.
Proof.
  now unfold Separate; rewrite op_comm.
Qed.
Hint Resolve separate_symm: seplog.

Add Parametric Relation (Sep: Separation) : (carrier Sep) (@Separate Sep)
    symmetry proved by (@separate_symm Sep)
    as separate_rel.

Lemma substate_refl [Sep: Separation] (a: Sep)
  : a $<= a.
Proof.
  exists $0.
  now apply op_id_r.
Qed.
Hint Resolve substate_refl: seplog.

Lemma substate_tran [Sep: Separation] (a b c: Sep)
  (SUBab: a $<= b) (SUBbc: b $<= c)
  : a $<= c.
Proof.
  unfold Substate in *.
  destruct SUBab as (ab & EQab).
  destruct SUBbc as (bc & EQbc).
  specialize (op_assc a ab bc) as EQ.
  rewrite EQab in EQ; cbn in EQ.
  unfold Basics.flip in EQ.
  rewrite EQbc in EQ.
  assert (EQabbc: exists d, ab $+ bc = Some d) by
    (destruct (ab $+ bc) as [abbc|]; [ now exists abbc | discriminate ]).
  destruct EQabbc as [ d EQabbc ].
  exists d.
  now rewrite EQ, EQabbc.
Qed.
Hint Resolve substate_tran: seplog.

Add Parametric Relation (Sep: Separation) : (carrier Sep) (@Substate Sep)
    reflexivity proved by (@substate_refl Sep)
    transitivity proved by (@substate_tran Sep)
    as substate_rel.

Lemma partition_separate [Sep: Separation] [a b c: Sep]
  (PART: a $+ b = Some c)
  : a $/= b.
Proof.
  now exists c.
Qed.
Hint Resolve partition_separate: seplog.

Lemma substate_of_partition_l [Sep: Separation] [a b c: Sep]
  (PART: a $+ b = Some c)
  : a $<= c.
Proof.
  now exists b.
Qed.
Hint Resolve substate_of_partition_l: seplog.

Lemma substate_of_partition_r [Sep: Separation] [a b c: Sep]
  (PART: a $+ b = Some c)
  : b $<= c.
Proof.
  rewrite op_comm in PART;
    eapply substate_of_partition_l, PART.
Qed.
Hint Resolve substate_of_partition_r: seplog.

Lemma separate_from_substate [Sep: Separation] [a b c: Sep]
  (SEP: a $/= b)
  (SUB: c $<= b)
  : a $/= c.
Proof.
  destruct SEP as (ab & SEP).
  destruct SUB as (cb & SUB).
  specialize (op_assc a c cb).
  rewrite SUB; cbn.
  rewrite SEP; cbn.
  destruct (a $+ c) as [ac|] eqn:Eac; [ cbn | discriminate].
  now exists ac.
Qed.
Hint Resolve separate_from_substate: seplog.

Lemma separate_emp_l [Sep: Separation] (a: Sep): $0 $/= a.
Proof.
  exists a; auto with seplog.
Qed.
Hint Resolve separate_emp_l: seplog.

Lemma separate_emp_r [Sep: Separation] (a: Sep): a $/= $0.
Proof.
  auto with seplog.
Qed.
Hint Resolve separate_emp_r: seplog.
