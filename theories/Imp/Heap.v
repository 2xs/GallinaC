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

From Stdlib Require Import NArith Psatz.

From GallinaC.Utils Require Import OptionExt ListExt Counter.
From GallinaC.Utils Require Export Algebra.
From GallinaC.Imp Require Export Addr RWMemory.

Local Open Scope separation_scope.
Local Open Scope mem_scope.

HB.mixin Record isPtr (Ad: Addr.type) R of Ref Ad R :=
  {
    reaches: R -> Ad -> bool;

    null: R;
    null_addr: forall r, ref_addr r = None <-> r = null;
    null_cmp: forall op, Allows null op <-> op = Operation.Cmp;
    null_reaches: forall a, ~ is_true (reaches null a);

    reaches_block: forall p a a',
        is_true (reaches p a) -> is_true (reaches p a') -> block a = block a';

    allows_reaches: forall p op a,
        Allows p op -> Operation.le Operation.Read op -> References p a ->
        is_true (reaches p a) /\ is_true (reaches p (shift_fw a 1%N));
    free_base: forall p a a',
        Allows p Operation.Free -> References p a -> is_true (reaches p a') ->
        (offset a <= offset a')%N;

    ptr_shift_fw: R -> N.t -> option R;
    ptr_shift_bw: R -> N.t -> option R;
    ptr_shift_fw_references: forall p s p'
                                    (EQ: ptr_shift_fw p s = Some p')
                                    a (REF: References p a),
        References p' (shift_fw a s);
    ptr_shift_bw_references: forall p s p'
                                    (EQ: ptr_shift_bw p s = Some p')
                                    a (REF: References p a),
        exists a', shift_bw a s = Some a' /\ References p' a';
    ptr_shift_fw_some: forall p s,
        (exists a, References p a
                   /\ is_true (reaches p a)
                   /\ is_true (reaches p (shift_fw a s)))
        <-> (exists p', ptr_shift_fw p s = Some p');
    ptr_shift_bw_some: forall p s,
        (exists a a', References p a
                      /\ is_true (reaches p a)
                      /\ shift_bw a s = Some a'
                      /\ is_true (reaches p a'))
        <-> (exists p', ptr_shift_bw p s = Some p');
    ptr_shift_fw_reaches: forall p s p'
                                 (EQ: ptr_shift_fw p s = Some p')
                                 a,
        is_true (reaches p' a) <-> is_true (reaches p a);
    ptr_shift_bw_reaches: forall p s p'
                                 (EQ: ptr_shift_bw p s = Some p')
                                 a,
        is_true (reaches p' a) <-> is_true (reaches p a);
    ptr_shift_fw_allows: forall p s p' a' op
                                (EQ: ptr_shift_fw p s = Some p')
                                (REF: References p' a')
                                (REACH: is_true (reaches p' (shift_fw a' 1%N)))
                                (LE: Operation.le op Operation.Write),
        Allows p op -> Allows p' op;
    ptr_shift_bw_allows: forall p s p' a' op
                                (EQ: ptr_shift_bw p s = Some p')
                                (REF: References p' a')
                                (REACH: is_true (reaches p' (shift_fw a' 1%N)))
                                (LE: Operation.le op Operation.Write),
        Allows p op -> Allows p' op;
  }.
HB.structure Definition Ptr (Ad: Addr.type) := { R of Ref Ad R & isPtr Ad R & hasEqDec R }.

Notation Reaches p a := (is_true (reaches p a)).

Definition ptr_addr_eqb [Ad: Addr.type] [Pt: Ptr.type Ad] (p1 p2: Pt): bool :=
  match ref_addr p1, ref_addr p2 with
  | Some a1, Some a2 => eqb a1 a2
  | None, None => true
  | _, _ => false
  end.

Definition cmp [Ad] [Pt: Ptr.type Ad] (p1 p2: Pt): option bool :=
  if (allows p1 Operation.Cmp && allows p2 Operation.Cmp)%bool then Some (ptr_addr_eqb p1 p2) else None.

Lemma cmp_spec [Ad: Addr.type] [Pt: Ptr.type Ad] (x y: Pt):
  (Allows x Operation.Cmp /\ Allows y Operation.Cmp) <-> cmp x y = Some (ptr_addr_eqb x y).
Proof.
  rewrite /cmp; split.
  - by move=> [-> ->].
  - by case: (allows x Operation.Cmp); case: (allows y Operation.Cmp).
Qed.
#[global] Hint Resolve -> cmp_spec: seplog.
#[global] Hint Resolve <- cmp_spec: seplog.

Lemma ptr_addr_eqb_mkAddr [Ad: Addr.type] [Pt: Ptr.type Ad] [pl pr: Pt] [bl br ofstl ofstr]
  (REFl: References pl (mkAddr bl ofstl)) (REFr: References pr (mkAddr br ofstr))
  : ptr_addr_eqb pl pr = (Nat.eqb bl br && N.eqb ofstl ofstr)%bool.
Proof.
  rewrite /ptr_addr_eqb REFl REFr.
  case: (eqb_spec (mkAddr bl ofstl) (mkAddr br ofstr)) => [EF|NEF].
  - by case: (mkAddr_inj _ _ _ _ EF) => [-> ->]; rewrite PeanoNat.Nat.eqb_refl N.eqb_refl.
  - case: (PeanoNat.Nat.eqb_spec bl br) => [Eb|//]; subst br.
    by case: (N.eqb_spec ofstl ofstr) => [Eo|//]; subst ofstr; have := NEF erefl.
Qed.

Lemma read_null_ptr [Ad: Addr.type] [Pt: Ptr.type Ad] [Vl] [RW: RWMemory.type Ad Pt Vl]
  [m: RW] [v: Vl] (LOOKUP: lookup m (null: Pt) = Some v): False.
Proof using Type.
  destruct (proj2 (lookup_iff m (null: Pt) v) LOOKUP) as ( a & REF & _ & _ ).
  assert (NONE: Some a = None)
    by (etransitivity;
        [ symmetry; exact REF | exact (proj2 (null_addr (null: Pt)) eq_refl) ]).
  discriminate NONE.
Qed.

Lemma mutate_null_heap [Ad: Addr.type] [Pt: Ptr.type Ad] [Vl] [RW: RWMemory.type Ad Pt Vl]
  [m: RW] [v: Vl] [m'] (MUTATE: mutate m (null: Pt) v = Some m'): False.
Proof using Type.
  destruct (proj2 (mutate_some_iff m (null: Pt) v) (ex_intro _ m' MUTATE))
    as ( a & v0 & REF & _ & _ ).
  assert (NONE: Some a = None)
    by (etransitivity;
        [ symmetry; exact REF | exact (proj2 (null_addr (null: Pt)) eq_refl) ]).
  discriminate NONE.
Qed.

Lemma ptr_shift_bw_null [Ad: Addr.type] [Pt: Ptr.type Ad] [p': Pt] [nn]
  (SHIFT: ptr_shift_bw (null: Pt) nn = Some p'): False.
Proof using Type.
  destruct (proj2 (ptr_shift_bw_some (null: Pt) nn) (ex_intro _ p' SHIFT))
    as ( a & a' & REF & _ ).
  now rewrite (proj2 (null_addr (null: Pt)) eq_refl) in REF.
Qed.

Lemma ptr_shift_fw_null [Ad: Addr.type] [Pt: Ptr.type Ad] [p': Pt] [nn]
  (SHIFT: ptr_shift_fw (null: Pt) nn = Some p'): False.
Proof using Type.
  destruct (proj2 (ptr_shift_fw_some (null: Pt) nn) (ex_intro _ p' SHIFT))
    as ( a & REF & _ ).
  now rewrite (proj2 (null_addr (null: Pt)) eq_refl) in REF.
Qed.

(** * Heaps

    A heap extends a [RWMemory] by equiping it [alloc] and [free] primitives

 *)

HB.mixin Record isHeap (Ad: Addr.type) (Pt: Ptr.type Ad) (Vl: Type) T of
                            RWMemory Ad Pt Vl T := {

    heap_alc: Counter.type;

    (* Primitive Operations *)
    alloc: T -> excl heap_alc -> N.t -> Vl -> option (T * excl heap_alc * Pt);
    free: T -> Pt -> option (T);

    (* Specification of operations *)
    (* alloc *)
    alloc_some: forall h alc sz v,
        (exists bid, cget alc = Some bid /\ 0 < sz
                     /\ forall o v', ~ ((mkAddr bid o) |-> v' $<= h))%N
        <-> exists h' alc' p, alloc h alc sz v = Some (h', alc', p);
    alloc_references: forall h alc sz v h' alc' p bid,
        alloc h alc sz v = Some (h', alc', p) -> cget alc = Some bid ->
            References p (mkAddr bid 0%N);
    alloc_allows: forall h alc sz v h' alc' p bid,
        alloc h alc sz v = Some (h', alc', p) ->
            cget alc = Some bid ->
                Allows p Operation.Free;
    alloc_reaches: forall h alc sz v h' alc' p bid,
        alloc h alc sz v = Some (h', alc', p) ->
            cget alc = Some bid ->
                forall sz', (sz' <= sz)%N <-> Reaches p (mkAddr bid sz');
    alloc_mem: forall h alc sz v h' alc' p,
        alloc h alc sz v = Some (h', alc', p) ->
            forall a' v', (a' |-> v') $<= h'
            <-> ((Reaches p a' /\ Reaches p (shift_fw a' 1%N) /\ v' = v)
                 \/ (~(Reaches p a' /\ Reaches p (shift_fw a' 1%N)) /\ (a' |-> v') $<= h));
    alloc_alc: forall h alc sz v h' alc' p,
        alloc h alc sz v = Some (h', alc', p) ->
            alc' = cnext alc;
    alloc_det: forall h1 h2 alc sz v1 v2 h1' h2' alc1' alc2' p1 p2,
        alloc h1 alc sz v1 = Some (h1', alc1', p1) ->
        alloc h2 alc sz v2 = Some (h2', alc2', p2) ->
            p1 = p2;

    (* free *)
    free_some: forall h p,
        (Allows p Operation.Free
         /\ (forall a, Reaches p a -> Reaches p (shift_fw a 1%N) -> exists v, (a |-> v) $<= h))
        <-> exists h', free h p = Some h';
    free_mem: forall h p h',
        free h p = Some h' ->
        forall a, (((Reaches p a /\ Reaches p (shift_fw a 1%N)) /\ ~(exists v, a |-> v $<= h'))
                   \/ (~(Reaches p a /\ Reaches p (shift_fw a 1%N))
                       /\ (forall v, a |-> v $<= h <-> a |-> v $<= h')));
}.
HB.structure Definition Heap (Ad: Addr.type) (Pt: Ptr.type Ad) (Vl: Type) :=
  { T of RWMemory Ad Pt Vl T & hasBlockBound Ad Vl T & isHeap Ad Pt Vl T }.

#[global] Hint Resolve
  alloc_references alloc_allows alloc_alc alloc_det
  free_mem
  : seplog.
#[global] Hint Resolve -> alloc_reaches: seplog.
#[global] Hint Resolve <- alloc_reaches: seplog.
#[global] Hint Resolve -> alloc_mem: seplog.
#[global] Hint Resolve <- alloc_mem: seplog.
#[global] Hint Resolve -> free_some: seplog.
#[global] Hint Resolve <- free_some: seplog.

Lemma alloc_absent [Ad: Addr.type] [Pt: Ptr.type Ad] [Vl] [Hp: Heap.type Ad Pt Vl]
  (h: Hp) alc sz v h' alc' (p: Pt)
  (EQ: alloc h alc sz v = Some (h', alc', p))
  : forall a, Reaches p a -> ~ exists v_old, (a |-> v_old) $<= h.
Proof.
  intros a RCH (v_old & SUB).
  destruct (proj2 (alloc_some h alc sz v)
              (ex_intro _ h' (ex_intro _ alc' (ex_intro _ p EQ))))
    as (bid & GET & SZ & ABS).
  have R0: Reaches p (mkAddr bid 0%N).
  { apply (proj1 (alloc_reaches _ _ _ _ _ _ _ _ EQ GET 0%N)); lia. }
  have BLK: block a = block (mkAddr (s:=Ad) bid 0%N)
    := reaches_block p a _ RCH R0.
  rewrite mkAddr_block in BLK.
  apply (ABS (offset a) v_old).
  have Ea: mkAddr bid (offset a) = a
    by rewrite -BLK mkAddr_ext.
  by rewrite Ea.
Qed.

#[global] Hint Resolve alloc_absent: seplog.

Section Extent.
  Context [Ad: Addr.type] [Pt: Ptr.type Ad].

  Definition Extent (p: Pt) (b: nat) (sz: N): Prop :=
    forall o, Reaches p (mkAddr b o) <-> (o <= sz)%N.

  Lemma Extent_sz_fun p b sz sz' (E: Extent p b sz) (E': Extent p b sz'): sz = sz'.
  Proof using Type.
    have R : Reaches p (mkAddr b sz) by apply: (proj2 (E sz)); lia.
    have R' : Reaches p (mkAddr b sz') by apply: (proj2 (E' sz')); lia.
    have L := proj1 (E' sz) R.
    have L' := proj1 (E sz') R'.
    lia.
  Qed.

  Lemma Extent_b_fun p b b' sz sz' (E: Extent p b sz) (E': Extent p b' sz'): b = b'.
  Proof using Type.
    have R : Reaches p (mkAddr b 0) by apply: (proj2 (E 0%N)); lia.
    have R' : Reaches p (mkAddr b' 0) by apply: (proj2 (E' 0%N)); lia.
    have := reaches_block p _ _ R R'.
    by rewrite !mkAddr_block.
  Qed.

  Lemma Extent_block p b sz (E: Extent p b sz) a (R: Reaches p a): block a = b.
  Proof using Type.
    have R0 : Reaches p (mkAddr b 0) by apply: (proj2 (E 0%N)); lia.
    have := reaches_block p _ _ R R0.
    by rewrite mkAddr_block.
  Qed.

  Lemma Extent_free_offset p b sz a
    (E: Extent p b sz) (AF: Allows p Operation.Free) (REF: References p a)
    : offset a = 0%N.
  Proof using Type.
    have R0 : Reaches p (mkAddr b 0) by apply: (proj2 (E 0%N)); lia.
    have := free_base p a _ AF REF R0.
    rewrite mkAddr_offset; lia.
  Qed.

  Lemma Extent_free_pos p b sz
    (E: Extent p b sz) (AF: Allows p Operation.Free)
    : (0 < sz)%N.
  Proof using Type.
    case RA: (ref_addr p) => [a|]; last first.
    - have Ep := proj1 (null_addr p) RA; subst p.
      by have := proj1 (null_cmp Operation.Free) AF.
    - have [R R1] := allows_reaches p _ a AF (Operation.le_free _) RA.
      have Eb := Extent_block p b sz E a R.
      move: R1; rewrite /shift_fw Eb => /(proj1 (E _)); lia.
  Qed.

  Lemma Extent_cell (p: Pt) (b: nat) (sz: N) (EXT: Extent p b sz) (a: Ad):
    (Reaches p a /\ Reaches p (shift_fw a 1%N)) <-> (block a = b /\ (offset a < sz)%N).
  Proof using Type.
    split.
    - move=> [ R R1 ].
      have EB := Extent_block p b sz EXT a R.
      split; first exact: EB.
      move: R1; rewrite /shift_fw EB => /(proj1 (EXT _)).
      lia.
    - move=> [ EB LT ].
      rewrite -(mkAddr_ext a) EB /shift_fw mkAddr_block mkAddr_offset.
      split; apply: (proj2 (EXT _)); lia.
  Qed.

  Lemma alloc_Extent [Vl] [Hp: Heap.type Ad Pt Vl] (h: Hp) alc sz v h' alc' p bid
    (EQ: alloc h alc sz v = Some (h', alc', p)) (G: cget alc = Some bid)
    : Extent p bid sz.
  Proof using Type. move=> o; symmetry; exact: (alloc_reaches h alc sz v h' alc' p bid EQ G o). Qed.

  Lemma free_interval [Vl] [Hp: Heap.type Ad Pt Vl] (h h': Hp) (p: Pt) b sz
    (FREE: free h p = Some h') (E: Extent p b sz)
    : (forall o, (o < sz)%N -> ~ exists v, (mkAddr b o) |-> v $<= h')
      /\ (forall a, (block a <> b \/ (sz <= offset a)%N) ->
            forall v, a |-> v $<= h <-> a |-> v $<= h').
  Proof using Type.
    split.
    - move=> o LT.
      case: (free_mem h p h' FREE (mkAddr b o)) => [[_ NEX]|[NR PRES]] //.
      exfalso; apply: NR; split.
      + apply: (proj2 (E o)); lia.
      + rewrite /shift_fw mkAddr_block mkAddr_offset.
        apply: (proj2 (E (o + 1)%N)); lia.
    - move=> a HA v.
      case: (free_mem h p h' FREE a) => [[[R R1] _]|[_ PRES]]; last exact: PRES.
      exfalso; case: HA => HA.
      + exact: HA (Extent_block p b sz E a R).
      + have Eb := Extent_block p b sz E a R.
        move: R1; rewrite /shift_fw Eb => /(proj1 (E _)); lia.
  Qed.

  Lemma free_interval_lo [Vl] [Hp: Heap.type Ad Pt Vl] (h h': Hp) (p: Pt) b sz
    (FREE: free h p = Some h') (E: Extent p b sz) (POS: (0 < sz)%N)
    : ~ exists v, (mkAddr b 0) |-> v $<= h'.
  Proof using Type. by case: (free_interval h h' p b sz FREE E) => X _; apply: X. Qed.

End Extent.

Lemma dominates_free [Ad: Addr.type] [Pt: Ptr.type Ad] [Vl] [Hp: Heap.type Ad Pt Vl]
  (h h': Hp) (p: Pt) (c: excl (@heap_alc Ad Pt Vl Hp))
  (EQ: free h p = Some h') (DOM: dominates h c)
  : dominates h' c.
Proof.
  move=> a1 v1 bid SUBa EQg.
  case: (free_mem h p h' EQ a1) => [[_ NB]|[_ IFF]].
  - exfalso; apply: NB; by exists v1.
  - exact: (DOM a1 v1 bid (proj2 (IFF v1) SUBa) EQg).
Qed.
#[global] Hint Resolve dominates_free: seplog.

Lemma free_null_heap [Ad: Addr.type] [Pt: Ptr.type Ad] [Vl] [Hp: Heap.type Ad Pt Vl]
  [hp hp': Hp] (FREE: free hp (null: Pt) = Some hp')
  : False.
Proof using Type.
  destruct (proj2 (free_some hp (null: Pt)) (ex_intro _ hp' FREE))
    as ( AF & _ ).
  now specialize (proj1 (null_cmp Operation.Free) AF).
Qed.

Lemma free_heap_cell_sub [Ad: Addr.type] [Pt: Ptr.type Ad] [Vl] [Hp: Heap.type Ad Pt Vl]
  [hp hp': Hp] [p: Pt]
  (FREE: free hp p = Some hp')
  [a: Ad] [v: Vl] (SUB: (((a |-> v)%mem) $<= hp')%sep)
  : (((a |-> v)%mem) $<= hp)%sep.
Proof using Type.
  destruct (free_mem hp p hp' FREE a) as [ ( _ & NEX ) | ( _ & IFF ) ];
    [ exfalso; exact (NEX (ex_intro _ v SUB)) | exact (proj2 (IFF v) SUB) ].
Qed.

Lemma dominates_alloc [Ad: Addr.type] [Pt: Ptr.type Ad] [Vl] [Hp: Heap.type Ad Pt Vl]
  (h h': Hp) (alc alc': excl (@heap_alc Ad Pt Vl Hp)) (sz: N.t) (v: Vl) (p: Pt)
  (EQ: alloc h alc sz v = Some (h', alc', p)) (DOM: dominates h alc)
  : dominates h' alc'.
Proof.
  move=> a1 v1 id1 SUBa EQg.
  rewrite (alloc_alc h alc sz v h' alc' p EQ) in EQg.
  case: (cget_next_bw_some alc id1 EQg) => bid EQ0.
  have LT: bid < id1 := cnext_lt alc bid id1 EQ0 EQg.
  case: (proj1 (alloc_mem h alc sz v h' alc' p EQ a1 v1) SUBa) => [[RCH _]|[_ SUBh]].
  - have R0: Reaches p (mkAddr bid 0%N)
      by apply: (proj1 (alloc_reaches _ _ _ _ _ _ _ _ EQ EQ0 0%N)); lia.
    have BLK := reaches_block p a1 _ RCH R0.
    rewrite mkAddr_block in BLK.
    lia.
  - have := DOM a1 v1 bid SUBh EQ0.
    lia.
Qed.
#[global] Hint Resolve dominates_alloc: seplog.

Section Validity.
  Context [Ad: Addr.type] [Pt: Ptr.type Ad].

  Definition Valid [Vl] [Hp: Heap.type Ad Pt Vl] (hp: Hp) (ptr: Pt) :=
    exists addr v, References ptr addr /\ (addr |-> v) $<= hp.

  Definition POValid [Vl] [Hp: Heap.type Ad Pt Vl] (hp: Hp) (ptr: Pt) :=
    exists addr addr' v, References ptr addr' /\ Shift addr 1 addr' /\ (addr |-> v) $<= hp.

  Definition WValid [Vl] [Hp: Heap.type Ad Pt Vl] (hp: Hp) (ptr: Pt) :=
    Valid hp ptr \/ POValid hp ptr \/ ptr = null.

  Definition valid [Vl: NonEmpty.type] [Hp: Heap.type Ad Pt Vl] (hp: Hp) (ptr: Pt): bool :=
    match ref_addr ptr with
    | Some addr => contains hp addr
    | None => false
    end.

  Definition valid_past_one [Vl: NonEmpty.type] [Hp: Heap.type Ad Pt Vl] (hp: Hp) (ptr: Pt): bool :=
    match ref_addr ptr with
    | Some addr =>
        match shift_bw addr 1 with
        | Some addr => contains hp addr
        | None => false
        end
    | None => false
    end.

  Definition weakly_valid [Vl: NonEmpty.type] [Hp: Heap.type Ad Pt Vl] (hp: Hp) (ptr: Pt): bool :=
    valid hp ptr || valid_past_one hp ptr || negb (isSome (ref_addr ptr)).

  Lemma valid_spec [Vl: NonEmpty.type] [Hp: Heap.type Ad Pt Vl] (hp: Hp) (ptr: Pt)
    : reflect (Valid hp ptr) (valid hp ptr).
  Proof using Type.
    rewrite /Valid /valid.
    case E: (ref_addr ptr) => [addr|]; last first.
    { constructor => -[addr [v [REF _]]]; congruence. }
    case: (contains_spec hp addr) => H; constructor.
    - case: H => v SUB.
      exists addr, v.
      by split.
    - move=> [addr' [v [REF SUB]]].
      have ?: addr' = addr by congruence.
      subst addr'.
      apply: H.
      by exists v.
  Qed.

  Lemma valid_past_one_spec [Vl: NonEmpty.type] [Hp: Heap.type Ad Pt Vl] (hp: Hp) (ptr: Pt)
    : reflect (POValid hp ptr) (valid_past_one hp ptr).
  Proof using Type.
    rewrite /POValid /valid_past_one.
    case E: (ref_addr ptr) => [addr|]; last first.
    { constructor => -[a [a' [v [REF _]]]]; congruence. }
    case E2: (shift_bw addr 1) => [addr0|]; last first.
    { constructor => -[a [a' [v [REF [SHIFT SUB]]]]].
      have ?: a' = addr by congruence.
      subst a'.
      have := proj1 (shift_bw_spec addr 1 a) SHIFT.
      congruence. }
    case: (contains_spec hp addr0) => H; constructor.
    - case: H => v SUB.
      exists addr0, addr, v.
      split=> //.
      split=> //.
      exact: (proj2 (shift_bw_spec addr 1 addr0) E2).
    - move=> [a [a' [v [REF [SHIFT SUB]]]]].
      have ?: a' = addr by congruence.
      subst a'.
      have ?: a = addr0
        by apply: (Shift_inj addr0 a 1 addr (proj2 (shift_bw_spec addr 1 addr0) E2) SHIFT).
      subst a.
      apply: H.
      by exists v.
  Qed.

  Lemma weakly_valid_spec [Vl: NonEmpty.type] [Hp: Heap.type Ad Pt Vl] (hp: Hp) (ptr: Pt)
    : reflect (WValid hp ptr) (weakly_valid hp ptr).
  Proof using Type.
    rewrite /WValid /weakly_valid.
    case: (valid_spec hp ptr) => [V|NV] /=; [by constructor; left|].
    case: (valid_past_one_spec hp ptr) => [V|NV2] /=; [by constructor; right; left|].
    case E: (ref_addr ptr) => [a|] /=; constructor.
    - move=> [contra|[contra|contra]] //.
      subst ptr.
      by rewrite (proj2 (null_addr null) erefl) in E.
    - right; right.
      exact: (proj1 (null_addr ptr) E).
  Qed.

  Lemma weakly_valid_mono [Vl: NonEmpty.type] [Hp: Heap.type Ad Pt Vl]
    (hp hp': Hp) (ptr: Pt)
    (SUB: hp $<= hp')
    (WV: weakly_valid hp ptr = true)
    : weakly_valid hp' ptr = true.
  Proof using Type.
    have W: WValid hp ptr by case: (weakly_valid_spec hp ptr) WV.
    case: (weakly_valid_spec hp' ptr) => [_|NW] //.
    exfalso; apply: NW.
    case: W => [[a [v [REF SUBav]]]|[[a [a' [v [REF [SH SUBav]]]]]|ISNULL]].
    - by left; exists a, v; split; [ | exact: (substate_tran _ _ _ SUBav SUB)].
    - right; left; exists a, a', v.
      by split; [ | split; [ | exact: (substate_tran _ _ _ SUBav SUB)]].
    - by right; right.
  Qed.

  Lemma valid_mono [Vl: NonEmpty.type] [Hp: Heap.type Ad Pt Vl]
    (hp hp': Hp) (ptr: Pt)
    (SUB: hp $<= hp')
    (V: valid hp ptr = true)
    : valid hp' ptr = true.
  Proof using Type.
    have V0: Valid hp ptr by case: (valid_spec hp ptr) V.
    case: (valid_spec hp' ptr) => [_|NV] //.
    exfalso; apply: NV.
    case: V0 => [a [v [REF SUBav]]].
    by exists a, v; split; [ | etransitivity; eassumption ].
  Qed.

  Definition CmpValid [Vl] [Hp: Heap.type Ad Pt Vl] (hp: Hp) (l r: Pt): Prop :=
    WValid hp l /\ WValid hp r
    /\ (forall a_l a_r, References l a_l -> References r a_r ->
                        block a_l <> block a_r -> Valid hp l /\ Valid hp r).

  Definition cmp_valid [Vl: NonEmpty.type] [Hp: Heap.type Ad Pt Vl] (hp: Hp) (l r: Pt): bool :=
    (weakly_valid hp l && weakly_valid hp r &&
       match ref_addr l, ref_addr r with
       | Some a_l, Some a_r => Nat.eqb (block a_l) (block a_r) || (valid hp l && valid hp r)
       | _, _ => true
       end)%bool.

  Lemma cmp_valid_spec [Vl: NonEmpty.type] [Hp: Heap.type Ad Pt Vl] (hp: Hp) (l r: Pt)
    : reflect (CmpValid hp l r) (cmp_valid hp l r).
  Proof using Type.
    rewrite /CmpValid /cmp_valid.
    case WL: (weakly_valid hp l); last first.
    { have NWL: ~ WValid hp l by case: (weakly_valid_spec hp l) WL.
      by constructor => -[W _]; exact: NWL W. }
    have WVL: WValid hp l by case: (weakly_valid_spec hp l) WL.
    case WR: (weakly_valid hp r); last first.
    { have NWR: ~ WValid hp r by case: (weakly_valid_spec hp r) WR.
      by constructor => -[_ [W _]]; exact: NWR W. }
    have WVR: WValid hp r by case: (weakly_valid_spec hp r) WR.
    case EL: (ref_addr l) => [a_l|]; last first.
    { by constructor;
         split; [exact WVL | split; [exact WVR | move=> a a' REFL; congruence]]. }
    case ER: (ref_addr r) => [a_r|]; last first.
    { by constructor;
         split; [exact WVL | split; [exact WVR | move=> a a' _ REFR; congruence]]. }
    case: (PeanoNat.Nat.eqb_spec (block a_l) (block a_r)) => [EQB|NEQB].
    - constructor; split; [exact WVL | split; [exact WVR | ]].
      move=> a a' REFL REFR NE.
      have ?: a = a_l by congruence.
      have ?: a' = a_r by congruence.
      by subst.
    - case VL: (valid hp l); last first.
      { have NVL: ~ Valid hp l by case: (valid_spec hp l) VL.
        by constructor => -[_ [_ CV]]; exact (NVL (proj1 (CV a_l a_r erefl erefl NEQB))). }
      have VVL: Valid hp l by case: (valid_spec hp l) VL.
      case VR: (valid hp r); last first.
      { have NVR: ~ Valid hp r by case: (valid_spec hp r) VR.
        by constructor => -[_ [_ CV]]; exact (NVR (proj2 (CV a_l a_r erefl erefl NEQB))). }
      have VVR: Valid hp r by case: (valid_spec hp r) VR.
      by constructor; split; [exact WVL | split; [exact WVR | ]].
  Qed.

  Lemma cmp_valid_mono [Vl: NonEmpty.type] [Hp: Heap.type Ad Pt Vl]
    (hp hp': Hp) (l r: Pt)
    (SUB: hp $<= hp')
    (CV: cmp_valid hp l r = true)
    : cmp_valid hp' l r = true.
  Proof using Type.
    move: CV; rewrite /cmp_valid.
    case WL: (weakly_valid hp l); last by [].
    case WR: (weakly_valid hp r); last by [].
    rewrite (weakly_valid_mono _ _ _ SUB WL) (weakly_valid_mono _ _ _ SUB WR).
    case: (ref_addr l) => [a_l|]; last by [].
    case: (ref_addr r) => [a_r|]; last by [].
    case: (Nat.eqb (block a_l) (block a_r)); first by [].
    case VL: (valid hp l); last by [].
    case VR: (valid hp r); last by [].
    move=> _.
    by rewrite (valid_mono _ _ _ SUB VL) (valid_mono _ _ _ SUB VR).
  Qed.

  Lemma weakly_valid_of_referenced_one [Vl: NonEmpty.type] [Hp: Heap.type Ad Pt Vl]
    (hp: Hp) (p: Pt) (a: Ad) (v: Vl)
    (REF: References p a) (SUB: (a |-> v) $<= hp)
    : weakly_valid hp p = true.
  Proof using Type.
    destruct (weakly_valid_spec hp p) as [_|NW]; [reflexivity|].
    exfalso; apply NW.
    left.
    exists a, v.
    split; [exact REF | exact SUB].
  Qed.


End Validity.
