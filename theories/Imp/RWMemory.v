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

From GallinaC.Utils Require Export Algebra.
From GallinaC.Imp Require Export Memory.

Local Open Scope separation_scope.
Local Open Scope mem_scope.

Module Operation.

  Inductive t: Set := Cmp | Read | Write | Free.

  Definition eqb (x y: t): bool :=
    match x, y with
    | Cmp, Cmp
    | Read, Read
    | Write, Write
    | Free, Free
      => true
    | _, _ => false
    end.

  Lemma eqb_spec x y
    : Bool.reflect (x = y) (eqb x y).
  Proof.
    destruct x, y; constructor; congruence.
  Qed.

  Inductive le: t -> t -> Prop :=
  | le_refl: forall op, le op op
  | le_free: forall op, le op Free
  | le_cmp_read: le Cmp Read
  | le_cmp_write: le Cmp Write
  | le_read_write: le Read Write.

  Definition leb (x y: t): bool :=
    match x, y with
    | _, Free
    | Cmp, Cmp | Cmp, Read | Cmp, Write
    | Read, Read | Read, Write
    | Write, Write
      => true
    | _, _ => false
    end.

  Lemma leb_spec x y
    : Bool.reflect (le x y) (leb x y).
  Proof.
    destruct x, y; constructor; try by constructor.
    all: by move=> H; inversion H.
  Qed.

End Operation.

HB.instance Definition _ := hasEqDec.Build Operation.t Operation.eqb Operation.eqb_spec.
HB.instance Definition _ := isRelation.Build Operation.t Operation.le.
HB.instance Definition _ :=
  isDecRel.Build Operation.t Operation.le Operation.leb Operation.leb_spec.

#[global] Hint Resolve Operation.eqb_spec: seplog.
#[global] Hint Resolve Operation.leb_spec: seplog.

(** * References

References are the actual objects manipulated by programs to access memory.

To accomodate for the existence of NULL references, unwrapping the contained
address might fail.

In addition, references might be restricted such that they may be used for only
a subset of operations, e.g. a global variable might be only read from or
written to, but it may not be freed.

 *)

HB.mixin Record isRef (Ad: Type) Ref := {
    ref_addr: Ref -> option Ad;

    allows: Ref -> Operation.t -> bool;
    allows_le: forall r op1 op2,
        Operation.le op1 op2 -> is_true (allows r op2) -> is_true (allows r op1);
}.
HB.structure Definition Ref (Ad: Type) := { R of isRef Ad R }.

Notation Allows r op := (is_true (allows r op)).
Notation References r addr := (ref_addr r = Some addr).

Definition ref_addr_inb [Ad: Addr.type] [Nm: Ref.type Ad] (locals: list Nm) (a: Ad): bool :=
  List.existsb (fun nm: Nm => match (ref_addr nm: option Ad) with
                              | Some a' => eqb a a'
                              | None => false
                              end) locals.

Lemma ref_addr_inb_intro [Ad: Addr.type] [Nm: Ref.type Ad] [locals: list Nm] [i nm] [a: Ad]
  (NTH: List.nth_error locals i = Some nm) (REF: References nm a)
  : ref_addr_inb locals a = true.
Proof using Type.
  unfold ref_addr_inb.
  revert i NTH; induction locals as [ | x l IH ]; intros i NTH;
    [ destruct i; discriminate NTH | ].
  cbn [List.existsb].
  destruct i as [ | i ]; cbn [List.nth_error] in NTH.
  - assert (EX: x = nm) by (injection NTH as E; exact E).
    subst x; rewrite REF.
    destruct (eqb_spec a a) as [ _ | NE ]; [ reflexivity | now contradiction NE ].
  - rewrite (IH i NTH); apply Bool.orb_true_r.
Qed.

Lemma ref_addr_inb_elim [Ad: Addr.type] [Nm: Ref.type Ad] [locals: list Nm] [a: Ad]
  (IN: ref_addr_inb locals a = true)
  : exists i nm, List.nth_error locals i = Some nm /\ References nm a.
Proof using Type.
  unfold ref_addr_inb in IN.
  induction locals as [ | x l IH ]; [ discriminate IN | ].
  cbn [List.existsb] in IN.
  assert (STEP: (exists i nm, List.nth_error l i = Some nm /\ References nm a) ->
                exists i nm, List.nth_error (x :: l) i = Some nm /\ References nm a).
  { intros ( i & nm & NTH & R ); exists (S i), nm; split; [ exact NTH | exact R ]. }
  revert IN; destruct (ref_addr x: option Ad) as [ ax | ] eqn:REF;
    cbn [orb]; intros IN; [ | exact (STEP (IH IN)) ].
  revert IN; destruct (eqb a ax) eqn:EB; cbn [orb]; intros IN;
    [ | exact (STEP (IH IN)) ].
  assert (EA: a = ax).
  { generalize EB; destruct (eqb_spec a ax) as [ E | _ ];
      [ intros _; exact E | discriminate ]. }
  subst ax; exists 0%nat, x; split; [ reflexivity | exact REF ].
Qed.

(** * RWMemory

A [RWMemory] extends a [Memory] with [lookup] and [mutate] operations.

[lookup m r] fetches a value from memory [m] using reference [r].
It succeeds returning a value [v] iff
- Reference [r] references an address [a]
- Reference [r] allows [Read] operations
- [a |-> v] is a substate of [m]

[mutate m r v] updates the memory using reference [r] and value [v].
It success returning a new memory [m'] iff
- Reference [r] references an address [a]
- Reference [r] allows [Write] operations
- [a |-> v0] is a substate of [m]

When [mutate m r v = Some m'] with [r] referencing [a], [a' |-> v' $<= m'] iff either
- [a' |-> v'] is the mutated substate ([a' = a /\ v' = v])
- [a' |-> v'] is a disjoint and untouched memory substate ([a' <> a /\ a' |-> v' $<= m])

Note that there is still no primitive to introduce or dispose of memory
regions. Structures built on top of [RWMemory] will introduce the required
primitives.
*)
HB.mixin Record isRWMemory (Ad: Type) (Nm: Ref.type Ad) (Vl: Type) T of Memory Ad Vl T :=
  {
    lookup: T -> Nm -> option Vl;
    mutate: T -> Nm -> Vl -> option T;

    lookup_iff: forall (m: T) (r: Nm) (v: Vl),
      (exists a, References r a /\ Allows r Operation.Read /\ a |-> v $<= m)
      <-> lookup m r = Some v;

    mutate_some_iff: forall (m: T) (r: Nm) (v: Vl),
        (exists a v0, References r a /\ Allows r Operation.Write /\ a |-> v0 $<= m)
        <-> (exists m', mutate m r v = Some m');

    mutate_mem_iff: forall (m: T) (r: Nm) (v: Vl) (m': T) (a: Ad)
                           (REF: References r a)
                           (EQ: mutate m r v = Some m')
                           a' v',
        a' |-> v' $<= m' <-> ((a' = a /\ v' = v) \/ (a' <> a /\ a' |-> v' $<= m));
}.
HB.structure Definition RWMemory (Ad: Type) (Nm: Ref.type Ad) (Vl: Type) :=
  { T of Memory Ad Vl T & isRWMemory Ad Nm Vl T }.

(* Reference [r] points to a value [v] in memory [m] *)
Notation "r |~> v @ m" := (exists a, References r a /\ a |-> v $<= m)
    (at level 75): mem_scope.

Lemma dominates_mutate [Ad: Addr.type] [Nm: Ref.type Ad] [Vl] [RW: RWMemory.type Ad Nm Vl]
  [Cn: Counter.type] (m m': RW) (r: Nm) (v: Vl) (c: Cn)
  (EQ: mutate m r v = Some m') (DOM: dominates m c)
  : dominates m' c.
Proof.
  case: (proj2 (mutate_some_iff m r v) (ex_intro _ m' EQ)) => a0 [v0 [REF [_ SUB0]]].
  move=> a1 v1 bid SUBa EQg.
  case: (proj1 (mutate_mem_iff m r v m' a0 REF EQ a1 v1) SUBa) => [[-> _]|[_ SUBh]].
  - exact: (DOM a0 v0 bid SUB0 EQg).
  - exact: (DOM a1 v1 bid SUBh EQg).
Qed.

#[global] Hint Resolve dominates_mutate: seplog.

Lemma mutate_dom [Ad: Addr.type] [Nm: Ref.type Ad] [Vl] [RW: RWMemory.type Ad Nm Vl]
  (m m': RW) (r: Nm) (v: Vl) (EQ: mutate m r v = Some m')
  : domain_preserved m m'.
Proof.
  move=> a w SUB.
  case: (proj2 (mutate_some_iff m r v) (ex_intro _ m' EQ)) => a0 [v0 [REF _]].
  case: (eqb_spec a a0) => [E|NE].
  - subst a0; exists v.
    by apply: (proj2 (mutate_mem_iff m r v m' a REF EQ a v)); left.
  - exists w.
    by apply: (proj2 (mutate_mem_iff m r v m' a0 REF EQ a w)); right.
Qed.

Lemma mutate_dom_bw [Ad: Addr.type] [Nm: Ref.type Ad] [Vl] [RW: RWMemory.type Ad Nm Vl]
  (m m': RW) (r: Nm) (v: Vl) (EQ: mutate m r v = Some m')
  : domain_preserved m' m.
Proof.
  move=> a w SUB.
  case: (proj2 (mutate_some_iff m r v) (ex_intro _ m' EQ)) => a0 [v0 [REF [_ SUB0]]].
  case: (proj1 (mutate_mem_iff m r v m' a0 REF EQ a w) SUB) => [[-> _]|[_ SUBm]].
  - by exists v0.
  - by exists w.
Qed.

Lemma mutate_dom_eq [Ad: Addr.type] [Nm: Ref.type Ad] [Vl] [RW: RWMemory.type Ad Nm Vl]
  (m m': RW) (r: Nm) (v: Vl) (EQ: mutate m r v = Some m')
  : domain_equal m m'.
Proof.
  exact: (domain_equal_of_preserved m m' (mutate_dom m m' r v EQ) (mutate_dom_bw m m' r v EQ)).
Qed.

#[global] Hint Resolve mutate_dom_eq: seplog seplog_search.

Lemma lookup_mono [Ad: Addr.type] [Nm: Ref.type Ad] [Vl] [RW: RWMemory.type Ad Nm Vl]
  [m m': RW] [r: Nm] [a: Ad] [v: Vl]
  (SUB: m $<= m') (REF: References r a) (CELL: (a |-> v) $<= m):
  lookup m' r = lookup m r.
Proof.
  destruct (lookup m r) as [ w | ] eqn:EQ.
  - destruct (proj2 (lookup_iff m r w) EQ) as ( a0 & REF0 & RD & CELL0 ).
    assert (EAD: a0 = a) by congruence; subst a0.
    apply (proj1 (lookup_iff m' r w)).
    exists a; split; [ exact REF | split; [ exact RD | ] ].
    exact (substate_tran _ _ _ CELL0 SUB).
  - destruct (lookup m' r) as [ w | ] eqn:EQ'; [ | reflexivity ].
    exfalso.
    destruct (proj2 (lookup_iff m' r w) EQ') as ( a0 & REF0 & RD & _ ).
    assert (EAD: a0 = a) by congruence; subst a0.
    assert (SOME: lookup m r = Some v).
    { apply (proj1 (lookup_iff m r v)).
      exists a; split; [ exact REF | split; [ exact RD | exact CELL ] ]. }
    rewrite EQ in SOME; discriminate.
Qed.

Lemma lookup_mutate_self [Ad: Addr.type] [Nm: Ref.type Ad] [Vl]
  [RW: RWMemory.type Ad Nm Vl] [m m': RW] [r: Nm] [v: Vl]
  (MUT: mutate m r v = Some m') (RD: Allows r Operation.Read):
  lookup m' r = Some v.
Proof.
  destruct (proj2 (mutate_some_iff m r v) (ex_intro _ m' MUT))
    as ( a & v0 & REF & _ & _ ).
  apply (proj1 (lookup_iff m' r v)).
  exists a; split; [ exact REF | split; [ exact RD | ] ].
  apply (proj2 (mutate_mem_iff m r v m' a REF MUT a v)).
  left; split; reflexivity.
Qed.

Lemma lookup_mutate_other [Ad: Addr.type] [Nm: Ref.type Ad] [Vl]
  [RW: RWMemory.type Ad Nm Vl] [m m': RW] [r r0: Nm] [a a0: Ad] [v: Vl]
  (MUT: mutate m r v = Some m') (REF: References r a) (REF0: References r0 a0)
  (NE: a0 <> a):
  lookup m' r0 = lookup m r0.
Proof.
  destruct (lookup m r0) as [ w | ] eqn:EQ.
  - destruct (proj2 (lookup_iff m r0 w) EQ) as ( a1 & REF1 & RD & CELL ).
    assert (EAD: a1 = a0) by congruence; subst a1.
    apply (proj1 (lookup_iff m' r0 w)).
    exists a0; split; [ exact REF0 | split; [ exact RD | ] ].
    apply (proj2 (mutate_mem_iff m r v m' a REF MUT a0 w)).
    right; split; [ exact NE | exact CELL ].
  - destruct (lookup m' r0) as [ w | ] eqn:EQ'; [ | reflexivity ].
    exfalso.
    destruct (proj2 (lookup_iff m' r0 w) EQ') as ( a1 & REF1 & RD & CELL ).
    assert (EAD: a1 = a0) by congruence; subst a1.
    destruct (proj1 (mutate_mem_iff m r v m' a REF MUT a0 w) CELL)
      as [ ( EAD0 & _ ) | ( _ & CELLm ) ]; [ exact (NE EAD0) | ].
    assert (SOME: lookup m r0 = Some w).
    { apply (proj1 (lookup_iff m r0 w)).
      exists a0; split; [ exact REF0 | split; [ exact RD | exact CELLm ] ]. }
    rewrite EQ in SOME; discriminate.
Qed.

Lemma mutate_one [Ad: Addr.type] [Nm: Ref.type Ad] [Vl] [RW: RWMemory.type Ad Nm Vl]
  [r: Nm] [a: Ad]
  (REF: References r a) (WRT: Allows r Operation.Write) (v mv: Vl):
  mutate ((a |-> v): RW) r mv = Some (a |-> mv).
Proof.
  destruct (proj1 (mutate_some_iff ((a |-> v): RW) r mv)
              (ex_intro _ a (ex_intro _ v
                 (conj REF (conj WRT (substate_refl ((a |-> v): RW)))))))
    as ( m' & MUT ).
  rewrite MUT; f_equal.
  apply (mem_ext m' ((a |-> mv): RW)); intros a' w; split.
  - intros SUB.
    destruct (proj1 (mutate_mem_iff ((a |-> v): RW) r mv m' a REF MUT a' w) SUB)
      as [ ( EAD & EVL ) | ( NEAD & SUBo ) ].
    + subst a' w; exact (substate_refl _).
    + exfalso.
      destruct (proj1 (sub_one_iff a a' v w) SUBo) as ( EAD & _ ).
      exact (NEAD EAD).
  - intros SUB.
    destruct (proj1 (sub_one_iff a a' mv w) SUB) as ( EAD & EVL ); subst a' w.
    apply (proj2 (mutate_mem_iff ((a |-> v): RW) r mv m' a REF MUT a mv)).
    left; split; reflexivity.
Qed.

Lemma mutate_partition [Ad: Addr.type] [Nm: Ref.type Ad] [Vl]
  [RW: RWMemory.type Ad Nm Vl] [m1 m2 m m1': RW] [r: Nm] [v: Vl]
  (SUM: m1 $+ m2 = Some m) (MUT1: mutate m1 r v = Some m1'):
  exists m', mutate m r v = Some m' /\ m1' $+ m2 = Some m'.
Proof.
  destruct (proj2 (mutate_some_iff m1 r v) (ex_intro _ m1' MUT1))
    as ( a & v0 & REF & WRT & CELL1 ).
  assert (CELL: (a |-> v0) $<= m)
    by exact (substate_tran _ _ _ CELL1 (substate_of_partition_l SUM)).
  destruct (proj1 (mutate_some_iff m r v)
              (ex_intro _ a (ex_intro _ v0 (conj REF (conj WRT CELL)))))
    as ( m' & MUT ).
  exists m'; split; [ exact MUT | ].
  assert (SEP0: m1 $/= m2) by exact (partition_separate SUM).
  assert (ABS: forall w, ~ ((a |-> w) $<= m2))
    by exact (absent_of_separate m1 m2 a v0 SEP0 CELL1).
  apply (sum_eq_char m1' m2 m').
  - exact (separate_domain_preserved (mutate_dom_bw m1 m1' r v MUT1) SEP0).
  - intros a' w; split.
    + intros SUB.
      destruct (proj1 (mutate_mem_iff m r v m' a REF MUT a' w) SUB)
        as [ ( EAD & EVL ) | ( NEAD & SUBm ) ].
      * subst a' w; left.
        apply (proj2 (mutate_mem_iff m1 r v m1' a REF MUT1 a v)).
        left; split; reflexivity.
      * destruct (proj1 (sub_sum_split_iff m1 m2 m SUM a' w) SUBm) as [ S1 | S2 ].
        -- left.
           apply (proj2 (mutate_mem_iff m1 r v m1' a REF MUT1 a' w)).
           right; split; [ exact NEAD | exact S1 ].
        -- right; exact S2.
    + intros [ S1 | S2 ].
      * destruct (proj1 (mutate_mem_iff m1 r v m1' a REF MUT1 a' w) S1)
          as [ ( EAD & EVL ) | ( NEAD & SUBm1 ) ].
        -- subst a' w.
           apply (proj2 (mutate_mem_iff m r v m' a REF MUT a v)).
           left; split; reflexivity.
        -- apply (proj2 (mutate_mem_iff m r v m' a REF MUT a' w)).
           right; split; [ exact NEAD | ].
           exact (substate_tran _ _ _ SUBm1 (substate_of_partition_l SUM)).
      * apply (proj2 (mutate_mem_iff m r v m' a REF MUT a' w)).
        right; split.
        -- intros EAD'; subst a'; exact (ABS w S2).
        -- exact (substate_tran _ _ _ S2 (substate_of_partition_r SUM)).
Qed.
