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

From Stdlib Require Import NArith Arith Lia.

From GallinaC.Utils Require Export Algebra.
From GallinaC.Utils Require Export Counter.
From GallinaC.Utils Require Import ReflectExt.
From GallinaC.Utils Require Import ListExt.
From GallinaC.Imp Require Export Addr.

Local Open Scope separation_scope.

Declare Scope mem_scope.
Delimit Scope mem_scope with mem.
Local Open Scope mem_scope.

(** * Memory

    Memory is a mapping from addresses to memory values, it is not associated
    with semantics.

    A memory extends a separation algebra with specific axioms.

    All previous properties and notations of separation algebras hold:
    - [ $0 ] is the empty memory
    - [ m1 $+ m2 ] is the partial union of memories [m1] and [m2] (fails on duplicate bindings)
    - [ m1 $/= m2 ] denotes disjoint memories, etc.

    In addition, it introduces the constructor [one a v] with notation (a |-> v). It denotes a singleton memory containing only value [v] at address [a].
 *)

HB.mixin Record isMemory (Ad: Type) (Vl: Type) T of Separation T := {
    (* Constructors *)
    one: Ad -> Vl -> T;

    (* one axioms *)
    one_similar: forall a v m, (exists v', one a v' $<= m) <-> (one a v) $+ m = None;
    one_min: forall m a v, m $<= one a v -> m = $0 \/ m = one a v;
    one_discriminate: forall m a v m'
                             (EQ: one a v $+ m = Some m')
                             a' v'
                             (SUB: one a' v' $<= m'),
      (a' = a /\ v' = v) \/ (a' <> a /\ one a' v' $<= m);

    (* General axioms *)
    mem_sep: forall m1 m2
                    (ONES: forall a1 a2 v1 v2 (SUB1: one a1 v1 $<= m1) (SUB2: one a2 v2 $<= m2), one a1 v1 $/= one a2 v2),
      m1 $/= m2;
    mem_ext: forall m1 m2, (forall a v, one a v $<= m1 <-> one a v $<= m2) -> m1 = m2;
  }.
HB.structure Definition Memory Ad Vl := { T of Separation T & isMemory Ad Vl T }.

Arguments one_discriminate [Ad Vl s m a v m'] EQ a' v'.

Notation "a |-> v" := (one a v) (at level 5, no associativity): mem_scope.

#[global] Hint Resolve one_min one_discriminate mem_sep: seplog.
#[global] Hint Resolve -> one_similar: seplog.
#[global] Hint Resolve <- one_similar: seplog.
#[global] Hint Resolve mem_ext | 20 : seplog.

(** Mixin laws as equivalences *)

Lemma one_min_iff [Ad Vl] [Mm: Memory.type Ad Vl] (m: Mm) a v
  : m $<= one a v <-> m = $0 \/ m = one a v.
Proof.
  split; [exact: one_min|].
  move=> [-> | ->].
  - exists (a |-> v); exact: op_id_l.
  - exact: substate_refl.
Qed.
#[global] Hint Resolve <- one_min_iff: seplog.

Lemma one_discriminate_iff [Ad Vl] [Mm: Memory.type Ad Vl]
  [m: Mm] [a v m'] (EQ: one a v $+ m = Some m') a' v'
  : one a' v' $<= m' <-> ((a' = a /\ v' = v) \/ (a' <> a /\ one a' v' $<= m)).
Proof.
  split; [exact: (one_discriminate EQ a' v')|].
  move=> [[-> ->] | [_ SUB]].
  - exact: (substate_of_partition_l EQ).
  - exact: (substate_tran _ _ _ SUB (substate_of_partition_r EQ)).
Qed.
#[global] Hint Resolve <- one_discriminate_iff: seplog.

Lemma mem_sep_iff [Ad Vl] [Mm: Memory.type Ad Vl] (m1 m2: Mm)
  : (forall a1 a2 v1 v2 (SUB1: one a1 v1 $<= m1) (SUB2: one a2 v2 $<= m2), one (s:=Mm) a1 v1 $/= one a2 v2) <-> m1 $/= m2.
Proof.
  split; [exact: mem_sep|].
  move=> SEP a1 a2 v1 v2 SUB1 SUB2.
  apply: separate_symm.
  apply: (separate_from_substate _ SUB1).
  apply: separate_symm.
  exact: (separate_from_substate SEP SUB2).
Qed.
#[global] Hint Resolve <- mem_sep_iff: seplog.

(** [one a v] is never the substate of an empty memory *)
Lemma emp_no_sub [Ad Vl] [Mm: Memory.type Ad Vl] a v
  : ~(one (s := Mm) a v $<= $0).
Proof.
  intros contra.
  specialize ((proj1 (one_similar (s:=Mm) a v $0) (ex_intro _ v contra))).
  by rewrite op_id_r.
Qed.
#[global] Hint Resolve emp_no_sub: seplog.

Lemma sub_one_neq_emp [Ad Vl] [Mm: Memory.type Ad Vl] (m: Mm) a v
  (SUB: (a |-> v) $<= m): m <> $0.
Proof. move=> E; rewrite E in SUB; exact: (emp_no_sub a v SUB). Qed.
#[global] Hint Resolve sub_one_neq_emp : seplog.

(** The only [one] that is a substate of a [one] is itself *)
Lemma sub_one_iff [Ad Vl] [Mm: Memory.type Ad Vl] a a' v v'
  : one (s:=Mm) a' v' $<= a |-> v <-> a' = a /\ v' = v.
Proof.
  split.
  - move=> SUB.
    case: (one_discriminate (op_id_r (a |-> v)) a' v' SUB).
    + move=> [EQa EQv]; by split.
    + move=> [_ SUB0]; by case: (emp_no_sub a' v' SUB0).
  - move=> [-> ->]; exact: substate_refl.
Qed.
#[global] Hint Resolve -> sub_one_iff: seplog.
#[global] Hint Resolve <- sub_one_iff: seplog.

(** [one] is injective *)
Lemma one_inj [Ad Vl] [Mm: Memory.type Ad Vl] a a' v v'
  : one (s:=Mm) a v = one a' v' <-> a = a' /\ v = v'.
Proof.
  split.
  - move=> EQ.
    apply (proj1 (sub_one_iff (Mm:=Mm) a' a v' v)).
    rewrite EQ; exact: substate_refl.
  - by move=> [-> ->].
Qed.
#[global] Hint Resolve -> one_inj: seplog.
#[global] Hint Resolve <- one_inj: seplog.

(** Memories hold at most one value at an address *)
Lemma one_fun [Ad Vl] [Mm: Memory.type Ad Vl] a v1 v2 (m: Mm)
  (SUB1: a |-> v1 $<= m) (SUB2: a |-> v2 $<= m)
  : v1 = v2.
Proof.
  case: SUB1 => b EQ.
  case: (one_discriminate EQ a v2 SUB2).
  - by move=> [_ ->].
  - by move=> [NE _]; exfalso; apply: NE.
Qed.
#[global] Hint Resolve one_fun | 10 : seplog.

(** Two [one] with different addresses are necessarily separate *)
Lemma one_ne_addr [Ad Vl] [Mm: Memory.type Ad Vl] a a' v v'
  : a <> a' <-> one (s:=Mm) a v $/= one a' v'.
Proof.
  split.
  - move=> NE.
    case E: (a |-> v $+ a' |-> v') => [w|].
    + by exists w.
    + exfalso.
      case: (proj2 (one_similar a v (a' |-> v')) E) => v'' SUB.
      case: (proj1 (sub_one_iff a' a v' v'') SUB) => EQ _.
      exact: (NE EQ).
  - move=> SEP contra; subst a'.
    case: SEP => w EW.
    have H := proj1 (one_similar a v (a |-> v'))
                (ex_intro _ v' (substate_refl _)).
    by rewrite H in EW.
Qed.
#[global] Hint Resolve -> one_ne_addr: seplog.
#[global] Hint Resolve <- one_ne_addr: seplog.

(** Two [one] at the same address are never separate *)
Lemma one_eq_addr [Ad Vl: Type] [Mm: Memory.type Ad Vl] (a: Ad) (v v': Vl)
  : (one (s:=Mm) a v) $+ (a |-> v') = None.
Proof.
  case E: (a |-> v $+ a |-> v') => [m|] //.
  by case: (proj2 (one_ne_addr a a v v') (ex_intro _ m E)).
Qed.
#[global] Hint Resolve one_eq_addr : seplog.

Lemma one_sum_not_sub [Ad Vl] [Mm: Memory.type Ad Vl] [a v] [m m': Mm]
  (SUM: one a v $+ m = Some m') w
  : ~ (one (s:=Mm) a w $<= m).
Proof.
  move=> SUB.
  exact: (proj2 (one_ne_addr a a v w) (separate_from_substate (ex_intro _ m' SUM) SUB) eq_refl).
Qed.
#[global] Hint Resolve one_sum_not_sub : seplog.

(** A [one a v] is separate from an arbitrary memory [m] iff any substate
    [one a' v'] is separate from [one a v] *)
Lemma one_sep [Ad Vl] [Mm: Memory.type Ad Vl] a v (m: Mm)
  : (forall a' v', one (s:=Mm) a' v' $<= m -> one (s:=Mm) a v $/= one a' v') <-> one a v $/= m.
Proof.
  split.
  - move=> H.
    apply (mem_sep (a |-> v) m).
    move=> a1 a2 v1 v2 SUB1 SUB2.
    case: (proj1 (sub_one_iff a a1 v v1) SUB1) => EQa EQv; subst a1 v1.
    exact: (H a2 v2 SUB2).
  - move=> SEP a' v' SUB.
    exact: (separate_from_substate SEP SUB).
Qed.
#[global] Hint Resolve -> one_sep: seplog.

(** A singleton is a substate of a partition iff it is a substate of one of its parts *)
Lemma sub_sum_split_iff [Ad Vl] [Mm: Memory.type Ad Vl] (m1 m2 m: Mm)
  (EQ: m1 $+ m2 = Some m) a v
  : (a |-> v) $<= m <-> ((a |-> v) $<= m1 \/ (a |-> v) $<= m2).
Proof.
  split; last first.
  { case=> SUB.
    - exact: (substate_tran _ _ _ SUB (substate_of_partition_l EQ)).
    - exact: (substate_tran _ _ _ SUB (substate_of_partition_r EQ)). }
  move=> SUB.
  have OCC: forall mi: Mm, mi $<= m -> (exists v', (a |-> v') $<= mi) -> (a |-> v) $<= mi.
  { move=> mi SUBi [v' SUBv'].
    have SUBv'm: (a |-> v') $<= m := substate_tran _ _ _ SUBv' SUBi.
    by rewrite (one_fun a v' v m SUBv'm SUB) in SUBv'. }
  case E1: ((a |-> v) $+ m1) => [x|]; last first.
  { left; apply: OCC;
      [exact: (substate_of_partition_l EQ) | exact: (proj2 (one_similar a v m1) E1)]. }
  have AM: (a |-> v) $+ m = None
    by apply: (proj1 (one_similar a v m)); exists v.
  have ASSC: x $+ m2 = None.
  { apply: (eq_trans _ AM).
    exact: (eq_trans (eq_sym (f_equal (ssrfun.Option.bind (Basics.flip op m2)) E1))
              (eq_trans (op_assc (a |-> v) m1 m2)
                 (f_equal (ssrfun.Option.bind (op (a |-> v))) EQ))). }
  case E2: ((a |-> v) $+ m2) => [y|]; last first.
  { right; apply: OCC;
      [exact: (substate_of_partition_r EQ) | exact: (proj2 (one_similar a v m2) E2)]. }
  exfalso.
  have SEPa2: (a |-> v) $/= m2 by exists y.
  have SEP: x $/= m2.
  { apply: mem_sep => b1 b2 w1 w2 SUB1 SUB2.
    case: (one_discriminate E1 b1 w1 SUB1) => [[-> ->]|[_ SUBm1]].
    - exact: (separate_from_substate SEPa2 SUB2).
    - have SEP12: m1 $/= m2 by exists m.
      exact: (proj2 (mem_sep_iff m1 m2) SEP12 b1 b2 w1 w2 SUBm1 SUB2). }
  case: SEP => c Ec.
  by rewrite Ec in ASSC.
Qed.
#[global] Hint Resolve -> sub_sum_split_iff : seplog.
#[global] Hint Resolve <- sub_sum_split_iff : seplog.

Lemma sum_eq_char [Ad Vl] [Mm: Memory.type Ad Vl] (m1 m2 m: Mm)
  (SEP: m1 $/= m2)
  (CHAR: forall a v, (a |-> v) $<= m <-> ((a |-> v) $<= m1 \/ (a |-> v) $<= m2))
  : m1 $+ m2 = Some m.
Proof.
  case: SEP => c Ec.
  rewrite Ec; congr Some.
  apply: mem_ext => a v; split=> H.
  - exact: (proj2 (CHAR a v) (proj1 (sub_sum_split_iff m1 m2 c Ec a v) H)).
  - exact: (proj2 (sub_sum_split_iff m1 m2 c Ec a v) (proj1 (CHAR a v) H)).
Qed.

Lemma absent_of_separate [Ad Vl] [Mm: Memory.type Ad Vl] (m f: Mm) a v
  (SEP: m $/= f) (SUB: (a |-> v) $<= m)
  : forall w, ~ ((a |-> w) $<= f).
Proof.
  move=> w SUBw.
  exact: (proj2 (one_ne_addr a a v w)
            (proj2 (mem_sep_iff m f) SEP a a v w SUB SUBw) erefl).
Qed.

(** [with_one m a v] decides whether a singleton [a |-> v] is a substate of [m]

    Inferred for memories where [Substate] is decidable.

    Because of how canonical structure resolution functions, it has to be
    defined as a notation where we resolve and repackage the canonical instances

    To implement it for a type T:
    1. Instantiate [DecRel] for [Substate] for [T]
    2. Optionally, implement concrete [T_with_one] and [T_with_one_spec] if you want to partially apply them or be able to find them using e.g. [Search]
 *)
Notation with_one m a v :=
  (@relb _ (DecRel.clone _ (@Substate _) _) (a |-> v) m).

Notation with_one_spec m a v :=
  (@relb_spec _ (DecRel.clone _ (@Substate _) _) (a |-> v) m).

(** Whether a memory contains a value at an address or not *)
Definition contains [Ad] [Vl: NonEmpty.type] [Mm: Memory.type Ad Vl]
  (m: Mm) (a: Ad): bool :=
  ~~ separateb (a |-> non_empty_witness) m.

Lemma contains_spec [Ad] [Vl: NonEmpty.type] [Mm: Memory.type Ad Vl]
  (m: Mm) (a: Ad)
  : Bool.reflect (exists v, one a v $<= m) (contains m a).
Proof.
  rewrite /contains /separateb.
  case E: (a |-> non_empty_witness $+ m) => [c|] /=; constructor.
  - move=> EX.
    rewrite (proj1 (one_similar a non_empty_witness m) EX) in E.
    discriminate.
  - exact: (proj2 (one_similar a non_empty_witness m) E).
Qed.

HB.mixin Record hasBlockBound (Ad: Addr.type) (Vl: Type) T of Memory Ad Vl T := {
    bbound: T -> nat;
    bbound_ub: forall (m: T) a v, (a |-> v) $<= m -> block a < bbound m;
    bbound_tight: forall (m: T), bbound m = 0
                    \/ exists a v, (a |-> v) $<= m /\ S (block a) = bbound m;
  }.
HB.structure Definition BoundedMemory (Ad: Addr.type) (Vl: Type) :=
  { T of Memory Ad Vl T & hasBlockBound Ad Vl T }.

#[global] Hint Resolve bbound_ub bbound_tight: seplog.

Definition dominates [Ad: Addr.type] [Vl] [Mm: Memory.type Ad Vl] [Cn: Counter.type]
  (m: Mm) (c: Cn): Prop :=
  forall a v bid (SUB: (a |-> v) $<= m) (EQ: cget c = Some bid), block a < bid.

Definition domain_preserved [Ad: Addr.type] [Vl] [Mm: Memory.type Ad Vl] (m m': Mm): Prop :=
  forall a w, (a |-> w) $<= m -> exists w', (a |-> w') $<= m'.

Definition domain_equal [Ad: Addr.type] [Vl] [Mm: Memory.type Ad Vl] (m m': Mm): Prop :=
  forall a, (exists v, (a |-> v) $<= m) <-> (exists v', (a |-> v') $<= m').

Section DomainEqual.
  Context [Ad: Addr.type] [Vl: Type] [Mm: Memory.type Ad Vl].

  Lemma domain_equal_refl (m: Mm): domain_equal m m.
  Proof. by move=> a. Qed.

  Lemma domain_equal_symm (m m': Mm): domain_equal m m' -> domain_equal m' m.
  Proof. by move=> H a; exact: (iff_sym (H a)). Qed.

  Lemma domain_equal_tran (m1 m2 m3: Mm)
    : domain_equal m1 m2 -> domain_equal m2 m3 -> domain_equal m1 m3.
  Proof. by move=> H1 H2 a; exact: (iff_trans (H1 a) (H2 a)). Qed.

  HB.instance Definition _ := isRelation.Build Mm (@domain_equal Ad Vl Mm).
  HB.instance Definition _ :=
    isReflRel.Build Mm (@domain_equal Ad Vl Mm) domain_equal_refl.
  HB.instance Definition _ :=
    isSymmRel.Build Mm (@domain_equal Ad Vl Mm) domain_equal_symm.
  HB.instance Definition _ :=
    isTranRel.Build Mm (@domain_equal Ad Vl Mm) domain_equal_tran.

  Lemma domain_equal_fw (m m': Mm): domain_equal m m' -> domain_preserved m m'.
  Proof. by move=> H a w SUB; apply: (proj1 (H a)); exists w. Qed.

  Lemma domain_equal_bw (m m': Mm): domain_equal m m' -> domain_preserved m' m.
  Proof. by move=> H a w SUB; apply: (proj2 (H a)); exists w. Qed.

  Lemma domain_equal_of_preserved (m m': Mm)
    : domain_preserved m m' -> domain_preserved m' m -> domain_equal m m'.
  Proof.
    by move=> H1 H2 a; split=> -[w SUB]; [exact: (H1 a w SUB) | exact: (H2 a w SUB)].
  Qed.

  Lemma domain_equal_of_eq (m m': Mm): m = m' -> domain_equal m m'.
  Proof. by move=> ->. Qed.
End DomainEqual.

Lemma separate_domain_preserved [Ad: Addr.type] [Vl] [Mm: Memory.type Ad Vl]
  [m1 m1' m2: Mm]
  (DOM: domain_preserved m1' m1) (SEP: m1 $/= m2):
  m1' $/= m2.
Proof.
  apply (mem_sep m1' m2); intros a1 a2 v1 v2 SUB1 SUB2.
  destruct (DOM a1 v1 SUB1) as ( w & SUBw ).
  apply (proj1 (one_ne_addr a1 a2 v1 v2)).
  intros EAD; subst a2.
  exact (proj2 (one_ne_addr a1 a1 w v2)
           (proj2 (mem_sep_iff m1 m2) SEP a1 a1 w v2 SUBw SUB2) eq_refl).
Qed.

#[global] Hint Resolve domain_equal_refl domain_equal_of_eq domain_equal_fw domain_equal_bw
  : seplog seplog_search.

Definition dominatesb [Ad: Addr.type] [Vl] [Bm: BoundedMemory.type Ad Vl] [Cn: Counter.type]
  (m: Bm) (c: Cn): bool :=
  match cget c with
  | None => true
  | Some bid => Nat.leb (bbound m) bid
  end.

Lemma dominatesb_spec [Ad: Addr.type] [Vl] [Bm: BoundedMemory.type Ad Vl] [Cn: Counter.type]
  (m: Bm) (c: Cn)
  : reflect (dominates m c) (dominatesb m c).
Proof.
  rewrite /dominatesb.
  case EG: (cget c) => [bid|]; last (constructor => a v bid SUB EQ; congruence).
  case EL: (Nat.leb (bbound m) bid); constructor.
  - move: EL => /Nat.leb_le LE a v bid' SUB EQ.
    have Eb: bid' = bid by congruence.
    have UB := bbound_ub m a v SUB.
    lia.
  - move: EL => /Nat.leb_gt GT DOM.
    case: (bbound_tight m) => [Z|[a [v [SUB EQb]]]]; first by lia.
    have := DOM a v bid SUB EG.
    lia.
Qed.

Lemma dominates_sub_mem [Ad: Addr.type] [Vl] [Mm: Memory.type Ad Vl] [Cn: Counter.type]
  (m m': Mm) (c: Cn)
  (SUB: m' $<= m) (DOM: dominates m c)
  : dominates m' c.
Proof.
  move=> a v bid SUBa EQg.
  exact: (DOM a v bid (substate_tran _ _ _ SUBa SUB) EQg).
Qed.
#[global] Hint Resolve dominates_sub_mem: seplog.

Lemma dominates_sub_cnt [Ad: Addr.type] [Vl] [Mm: Memory.type Ad Vl] [Cn: Counter.type]
  (m: Mm) (c c': excl Cn)
  (SUB: c' $<= c) (DOM: dominates m c)
  : dominates m c'.
Proof.
  move=> a v bid' SUBa EQg.
  case: (cget_sub c' c SUB bid' EQg) => bid [EQb LE].
  have := DOM a v bid SUBa EQb.
  lia.
Qed.
#[global] Hint Resolve dominates_sub_cnt: seplog.

Lemma dominates_emp [Ad: Addr.type] [Vl] [Mm: Memory.type Ad Vl] [Cn: Counter.type] (c: Cn)
  : dominates ($0: Mm) c.
Proof.
  move=> a v bid SUBa _.
  contradiction (emp_no_sub a v SUBa).
Qed.
#[global] Hint Resolve dominates_emp: seplog.

Lemma dominates_emp_cnt [Ad: Addr.type] [Vl] [Mm: Memory.type Ad Vl] [Cn: Counter.type] (m: Mm)
  : dominates m ($0: excl Cn).
Proof.
  move=> a v bid _ EQ.
  by rewrite cget_emp in EQ.
Qed.
#[global] Hint Resolve dominates_emp_cnt: seplog.

Lemma dominates_block_lt [Ad: Addr.type] [Vl] [Mm: Memory.type Ad Vl]
  [Cn: Counter.type] [m: Mm] [c: Cn] [k: nat] [a: Ad]
  (CGET: cget c = Some k) (DOM: dominates m c) (EAD: block a = k)
  (a': Ad) (w: Vl) (CELL: (a' |-> w) $<= m):
  (block a' < block a)%nat.
Proof.
  rewrite EAD; exact (DOM a' w k CELL CGET).
Qed.

Section OfList.
  Context [Ad: Addr.type] [Vl: Type] [Mm: Memory.type Ad Vl].

  #[local] Fixpoint of_listi (m: Mm) (addr: Ad) (vs: list Vl): option Mm :=
    match vs with
    | [] => Some m
    | v::vs =>
        match (addr |-> v) $+ m with
        | Some m =>
            of_listi m (shift_fw addr 1%N) vs
        | None => None
        end
    end.

  #[local] Lemma of_listi_sub (vs: list Vl):
    forall (m: Mm) addr m'
           (EQ: of_listi m addr vs = Some m'),
      m $<= m'.
  Proof using Type.
    induction vs as [|v vs IH]; intros; cbn in EQ.
    - inversion EQ; subst m'; exact: substate_refl.
    - destruct (addr |-> v $+ m) as [m1|] eqn:Esum; [| discriminate].
      eapply substate_tran; [| exact: (IH _ _ _ EQ)].
      exact: (substate_of_partition_r Esum).
  Qed.

  #[local] Lemma of_listi_lt_step
    (m m1: Mm) (addr: Ad) v
    (Esum: addr |-> v $+ m = Some m1)
    (LT: forall a v', (a |-> v') $<= m -> (block a <> block addr \/ offset a < offset addr)%N)
    : forall a v', (a |-> v') $<= m1 ->
                   (block a <> block (shift_fw addr 1%N) \/ offset a < offset (shift_fw addr 1%N))%N.
  Proof using Type.
    intros a v' SUB.
    specialize (one_discriminate Esum a v' SUB) as [ [ -> -> ] | [ NE SUB' ] ].
    - right; rewrite shift_fw_offset; lia.
    - specialize (LT _ _ SUB') as [ NEb | LTo ];
        [ left; rewrite shift_fw_block // | right; rewrite shift_fw_offset; lia ].
  Qed.

  #[local] Lemma of_listi_some:
    forall (m: Mm) addr vs
           (LT: forall a v, (a |-> v) $<= m -> (block a <> block addr \/ offset a < offset addr)%N),
      exists m', of_listi m addr vs = Some m'.
  Proof using Type.
    intros m addr vs.
    revert m addr.
    induction vs as [|v vs IHvs]; intros; [ now exists m | cbn ].
    destruct (addr |-> v $+ m) as [m'|] eqn:Esum.
    - exact: (IHvs m' (shift_fw addr 1%N) (of_listi_lt_step _ _ _ _ Esum LT)).
    - destruct (proj1 (one_sep addr v m)) as [ m' EQ ].
      + intros a_any v_any SUB.
        apply one_ne_addr.
        specialize (LT a_any v_any SUB) as [ NEb | LTo ]; intros contra; subst a_any;
          [ congruence | lia ].
      + congruence.
  Qed.

  #[local] Lemma of_listi_emp_some addr vs
    : exists m', of_listi $0 addr vs = Some m'.
  Proof using Type.
    apply of_listi_some.
    intros a v contra.
    now apply emp_no_sub in contra.
  Qed.

  #[local] Lemma of_listi_spec (vs: list Vl):
    forall (m: Mm) addr
           (LT: forall a v, (a |-> v) $<= m -> (block a <> block addr \/ offset a < offset addr)%N)
           n v m'
           (EQ: of_listi m addr vs = Some m'),
      List.nth_error vs n = Some v <-> (shift_fw addr (N.of_nat n)) |-> v $<= m'.
  Proof using Type.
    induction vs as [| v0 vs IH]; intros.
    - cbn in EQ; inversion EQ; subst m'; clear EQ.
      split; [ by destruct n | ].
      intros SUB.
      specialize (LT _ _ SUB) as [ contra | contra ];
        [ by rewrite shift_fw_block in contra
        | by rewrite shift_fw_offset in contra; lia ].
    - cbn in EQ.
      destruct (addr |-> v0 $+ m) as [m1|] eqn:Esum; [| discriminate].
      destruct n as [|n].
      + change (N.of_nat 0) with 0%N.
        rewrite shift_fw_0.
        have SUB0: (addr |-> v0) $<= m'.
        { eapply substate_tran;
            [ exact: (substate_of_partition_l Esum) | exact: (of_listi_sub _ _ _ _ EQ) ]. }
        split.
        * by move=> [<-].
        * intros SUB.
          cbn; f_equal.
          exact: (one_fun _ _ _ _ SUB0 SUB).
      + replace (N.of_nat (S n)) with (1 + N.of_nat n)%N by lia.
        rewrite -shift_fw_twice.
        exact: (IH m1 (shift_fw addr 1%N) (of_listi_lt_step _ _ _ _ Esum LT) n v m' EQ).
  Qed.

  Definition of_list addr vs :=
    match of_listi $0 addr vs with
    | Some m => m
    | None => $0
    end.

  Lemma of_list_spec addr vs
    n v
    : List.nth_error vs n = Some v <-> (shift_fw addr (N.of_nat n)) |-> v $<= (of_list addr vs).
  Proof using Type.
    unfold of_list.
    destruct (of_listi_emp_some addr vs) as (m' & EQ).
    rewrite EQ.
    eapply of_listi_spec; [ now intros a' v' contra; apply emp_no_sub in contra | apply EQ].
  Qed.

End OfList.
