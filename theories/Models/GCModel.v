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

From GallinaC.Utils Require Import ListExt Algebra Counter OptionExt ProdExt.
From GallinaC.Imp Require Import Monad Storable Heap Store While.
From GallinaC.Imp Require Export State.
From GallinaC.Models Require Import BlockMemory.
From GallinaC.Models Require Export Pointer ListStore ListHeap.

Local Open Scope separation_scope.
Local Open Scope program_scope.

Local Notation Ad := Addr.t.
Local Notation Pt := Pointer.t.
Local Notation St := (mem unit: Store.type Addr.t Pointer.t (value Pointer.t)).
Local Notation Hp := (mem unit: Heap.type Addr.t Pointer.t (value Pointer.t)).

Structure GCModel: Type :=
  mkState
    {
      smem: mem (excl nat);
      hmem: mem (excl nat);
    }.

Definition store (s: GCModel): St := to_mem (smem s).

Definition scnt (s: GCModel): excl (@store_cnt Ad Pt (value Pt) St) :=
  excl_map mkNatCnt (to_tail (smem s)).

Definition heap (s: GCModel): Hp := to_mem (hmem s).

Definition alc (s: GCModel): excl (@heap_alc Ad Pt (value Pt) Hp) :=
  excl_map mkNatCnt (to_tail (hmem s)).

Fixpoint mem_of' (m: mem' unit) (bid: nat): mem' (excl nat) :=
  match m with
  | M'Tail b _ => M'Tail b (Owned (Nat.pred bid))
  | M'Cons o m => M'Cons o (mem_of' m (Nat.pred bid))
  end.

Definition mem_of (m: mem unit) (c: excl nat_cnt): mem (excl nat) :=
  match c with
  | Owned k =>
      match m with
      | MEmpty _ => MEmpty (Owned (nat_cnt_current k))
      | MLive m' => MLive (mem_of' m' (nat_cnt_current k))
      end
  | Unowned => mem_map (fun _ => Unowned) m
  end.

Lemma mem'_map_map_tt [A: Type] (f: unit -> A) (m: mem' unit):
  mem'_map (fun _ => tt) (mem'_map f m) = m.
Proof using Type.
  by elim: m => [b []|o m IH] //=; rewrite IH.
Qed.

Lemma mem_of'_map (m: mem' unit): forall bid,
    mem'_map (fun _ => tt) (mem_of' m bid) = m.
Proof using Type.
  by elim: m => [b []|o m IH] bid //=; rewrite IH.
Qed.

Lemma to_mem_mem_of (m: mem unit) (c: excl nat_cnt):
  to_mem (mem_of m c) = m.
Proof using Type.
  case: c => [|k]; case: m => [a|m] //=.
  - by case: a.
  - by rewrite /to_mem /= mem'_map_map_tt.
  - by case: a.
  - by rewrite /to_mem /= mem_of'_map.
Qed.

Lemma to_tail'_map_unowned (m: mem' unit):
  to_tail' (mem'_map (fun _ => Unowned) m) = Unowned.
Proof using Type.
  by elim: m => [b a|o m IH] //=; rewrite IH.
Qed.

Lemma to_tail_mem_of_unowned (m: mem unit):
  to_tail (mem_of m Unowned) = Unowned.
Proof using Type.
  by case: m => [a|m] //=; rewrite to_tail'_map_unowned.
Qed.

Lemma to_tail'_mem_of' (m: mem' unit): forall bid,
    (mem'_nblocks m <= bid)%nat ->
    to_tail' (mem_of' m bid) = Owned (Nat.pred bid).
Proof using Type.
  elim: m => [b a|o m IH] bid LE //=.
  rewrite IH.
  - move: LE => /=; lia.
  - rewrite /runshift /=.
    congr Owned.
    move: (mem'_nblocks_pos m) LE => /=; lia.
Qed.

Lemma to_tail_mem_of (m: mem unit) (k: nat_cnt)
  (LE: (nblocks m <= nat_cnt_current k)%nat):
  to_tail (mem_of m (Owned k)) = Owned (nat_cnt_current k).
Proof using Type.
  case: m LE => [a|m] LE //=.
  rewrite to_tail'_mem_of' //= /runshift /=.
  congr Owned.
  move: (mem'_nblocks_pos m) LE => /=; lia.
Qed.

Lemma mem_of'_to_mem' (m: mem' (excl nat)): forall j,
    to_tail' m = Owned j ->
    mem_of' (mem'_map (fun _ => tt) m) (S j) = m.
Proof using Type.
  elim: m => [b a|o m IH] j /=.
  - by move=> ->.
  - case E: (to_tail' m) => [|j'] //= [Ej].
    subst j.
    by rewrite (IH j' E).
Qed.

Lemma mem_of'_to_mem'_unowned (m: mem' (excl nat)):
    to_tail' m = Unowned ->
    mem'_map (fun _ => Unowned) (mem'_map (fun _ => tt) m) = m.
Proof using Type.
  elim: m => [b a|o m IH] /=.
  - by move=> ->.
  - case E: (to_tail' m) => [|j'] //= _.
    by rewrite (IH E).
Qed.

Lemma mem_of_to_mem (m: mem (excl nat)):
  mem_of (to_mem m) (excl_map mkNatCnt (to_tail m)) = m.
Proof using Type.
  case: m => [a|m].
  - by case: a.
  - rewrite /to_mem /=.
    case E: (to_tail' m) => [|j] /=.
    + by rewrite (mem_of'_to_mem'_unowned m E).
    + by rewrite (mem_of'_to_mem' m j E).
Qed.

Lemma mem'_nblocks_map [A B: Type] (f: A -> B) (m: mem' A):
  mem'_nblocks (mem'_map f m) = mem'_nblocks m.
Proof using Type.
  by elim: m => [b a|o m IH] //=; rewrite IH.
Qed.

Lemma nblocks_to_mem (m: mem (excl nat)): nblocks (to_mem m) = nblocks m.
Proof using Type.
  case: m => [a|m] //=.
  exact: mem'_nblocks_map.
Qed.

Lemma excl_sum_map_mkNatCnt (x y z: excl nat) (EQ: x $+ y = Some z):
  excl_map mkNatCnt x $+ excl_map mkNatCnt y
  = Some (excl_map mkNatCnt z).
Proof using Type.
  by case: x y EQ => [|a] [|b] //= [<-].
Qed.

Lemma excl_map_mkNatCnt_sum (x y z: excl nat)
  (EQ: excl_map mkNatCnt x $+ excl_map mkNatCnt y
       = Some (excl_map mkNatCnt z)):
  x $+ y = Some z.
Proof using Type.
  case: x y z EQ => [|a] [|b] [|c] //= EQ; try discriminate EQ; try by [];
    by injection EQ => ->.
Qed.

Lemma get_to_tail_lt (m: mem (excl nat)) (bi o: nat) (v: value Pt) (k: nat)
  (GET: get m bi o = Some v) (EQ: to_tail m = Owned k): (bi < k)%nat.
Proof using Type.
  have LE := to_tail_nblocks_alloc m k EQ.
  case: (Nat.le_gt_cases (nblocks m) bi) => [GE|LT]; last by lia.
  by rewrite (get_nblocks_ge m bi o GE) in GET.
Qed.

Lemma dominates_to_mem_store (m: mem (excl nat)):
  dominates (to_mem m: St) (excl_map mkNatCnt (to_tail m)).
Proof using Type.
  move=> a v bid SUB EQ.
  case E: (to_tail m) EQ => [|j] //= [<-].
  have GET: get m (Imp.Addr.block a) (N.to_nat (offset a)) = Some v.
  { have A := proj1 (aone_sub_noalloc a v (to_mem m)) SUB.
    by rewrite /aget get_to_mem in A. }
  exact: (get_to_tail_lt m _ _ v j GET E).
Qed.

Lemma dominates_to_mem_heap (m: mem (excl nat)):
  dominates (to_mem m: Hp) (excl_map mkNatCnt (to_tail m)).
Proof using Type.
  move=> a v bid SUB EQ.
  case E: (to_tail m) EQ => [|j] //= [<-].
  have GET: get m (Imp.Addr.block a) (N.to_nat (offset a)) = Some v.
  { have A := proj1 (aone_sub_noalloc a v (to_mem m)) SUB.
    by rewrite /aget get_to_mem in A. }
  exact: (get_to_tail_lt m _ _ v j GET E).
Qed.

(* Extract [dominates] for [heap] and [alc] from a [GCModel] *)
Lemma state_heap_dominates (s: GCModel): dominates (heap s) (alc s).
Proof using Type. exact: dominates_to_mem_heap. Qed.

(* Extract [dominates] for [store] and [scnt] from a [GCModel] *)
Lemma state_store_dominates (s: GCModel): dominates (store s) (scnt s).
Proof using Type. exact: dominates_to_mem_store. Qed.

Lemma state_eq_raw (s1 s2: GCModel)
  (EQsm: smem s1 = smem s2)
  (EQhm: hmem s1 = hmem s2)
  : s1 = s2.
Proof using Type.
  case: s1 EQsm EQhm => sm1 hm1.
  by case: s2 => sm2 hm2 /= -> ->.
Qed.

(* GCModel extensionality *)
Lemma state_ext (s1 s2: GCModel)
  (EQst: store s1 = store s2)
  (EQsg: scnt s1 = scnt s2)
  (EQhp: heap s1 = heap s2)
  (EQalc: alc s1 = alc s2)
  : s1 = s2.
Proof using Type.
  apply: state_eq_raw.
  - rewrite -(mem_of_to_mem (smem s1)) -(mem_of_to_mem (smem s2)).
    move: EQst EQsg; rewrite /store /scnt => EQst EQsg.
    by rewrite EQst EQsg.
  - rewrite -(mem_of_to_mem (hmem s1)) -(mem_of_to_mem (hmem s2)).
    move: EQhp EQalc; rewrite /heap /alc => EQhp EQalc.
    by rewrite EQhp EQalc.
Qed.

(** * Constructing a heap *)

Lemma dominates_nblocks_store (st: St) (k: nat_cnt)
  (DOM: dominates st (Owned k: excl (@store_cnt Ad Pt (value Pt) St))):
  (nblocks st <= nat_cnt_current k)%nat.
Proof using Type.
  case: (bbound_tight_noalloc st) => [-> |[a [v [SUB EB]]]]; first by lia.
  rewrite -EB.
  exact: (DOM a v (nat_cnt_current k) SUB erefl).
Qed.

Lemma dominates_nblocks_heap (h: Hp) (k: nat_cnt)
  (DOM: dominates h (Owned k: excl (@heap_alc Ad Pt (value Pt) Hp))):
  (nblocks h <= nat_cnt_current k)%nat.
Proof using Type.
  case: (bbound_tight_noalloc h) => [-> |[a [v [SUB EB]]]]; first by lia.
  rewrite -EB.
  exact: (DOM a v (nat_cnt_current k) SUB erefl).
Qed.

Lemma scnt_mem_of (st: St) (sc: excl (@store_cnt Ad Pt (value Pt) St))
  (DOM: dominates st sc):
  excl_map mkNatCnt (to_tail (mem_of st sc)) = sc.
Proof using Type.
  case: sc DOM => [|k] DOM.
  - by rewrite to_tail_mem_of_unowned.
  - rewrite (to_tail_mem_of _ _ (dominates_nblocks_store st k DOM)) /=.
    clear DOM.
    by case: k.
Qed.

Lemma alc_mem_of (h: Hp) (c: excl (@heap_alc Ad Pt (value Pt) Hp))
  (DOM: dominates h c):
  excl_map mkNatCnt (to_tail (mem_of h c)) = c.
Proof using Type.
  case: c DOM => [|k] DOM.
  - by rewrite to_tail_mem_of_unowned.
  - rewrite (to_tail_mem_of _ _ (dominates_nblocks_heap h k DOM)) /=.
    clear DOM.
    by case: k.
Qed.

(** Constructs it from individual [dominates] proofs *)
Definition mk_state (st: St) (sc: excl (@store_cnt Ad Pt (value Pt) St))
  (h: Hp) (c: excl (@heap_alc Ad Pt (value Pt) Hp))
  (DOMs: dominates st sc) (DOMh: dominates h c): GCModel :=
  mkState (mem_of st sc) (mem_of h c).

Lemma store_mk_state (st: St) (sc: excl (@store_cnt Ad Pt (value Pt) St))
  (h: Hp) (c: excl (@heap_alc Ad Pt (value Pt) Hp))
  (DOMs: dominates st sc) (DOMh: dominates h c)
  : store (mk_state st sc h c DOMs DOMh) = st.
Proof using Type. exact: to_mem_mem_of. Qed.

Lemma scnt_mk_state (st: St) (sc: excl (@store_cnt Ad Pt (value Pt) St))
  (h: Hp) (c: excl (@heap_alc Ad Pt (value Pt) Hp))
  (DOMs: dominates st sc) (DOMh: dominates h c)
  : scnt (mk_state st sc h c DOMs DOMh) = sc.
Proof using Type. exact: (scnt_mem_of st sc DOMs). Qed.

Lemma heap_mk_state (st: St) (sc: excl (@store_cnt Ad Pt (value Pt) St))
  (h: Hp) (c: excl (@heap_alc Ad Pt (value Pt) Hp))
  (DOMs: dominates st sc) (DOMh: dominates h c)
  : heap (mk_state st sc h c DOMs DOMh) = h.
Proof using Type. exact: to_mem_mem_of. Qed.

Lemma alc_mk_state (st: St) (sc: excl (@store_cnt Ad Pt (value Pt) St))
  (h: Hp) (c: excl (@heap_alc Ad Pt (value Pt) Hp))
  (DOMs: dominates st sc) (DOMh: dominates h c)
  : alc (mk_state st sc h c DOMs DOMh) = c.
Proof using Type. exact: (alc_mem_of h c DOMh). Qed.

(** Tries to construct a [GCModel] from individual components, reconstructing proofs. May fail. *)
Definition mk_state_opt (st: St) (sc: excl (@store_cnt Ad Pt (value Pt) St))
  (h: Hp) (c: excl (@heap_alc Ad Pt (value Pt) Hp)): option GCModel :=
  if (dominatesb st sc && dominatesb h c)%bool
  then Some (mkState (mem_of st sc) (mem_of h c))
  else None.

(** when [mk_state_opt] succeeds, the components are the correct ones *)
Lemma mk_state_opt_some (st: St) (sc: excl (@store_cnt Ad Pt (value Pt) St))
  (h: Hp) (c: excl (@heap_alc Ad Pt (value Pt) Hp)) (s: GCModel):
  mk_state_opt st sc h c = Some s
  <-> (store s = st /\ scnt s = sc /\ heap s = h /\ alc s = c).
Proof using Type.
  rewrite /mk_state_opt.
  split.
  - case Es: (dominatesb st sc) => //=.
    case Eh: (dominatesb h c) => //=.
    move=> [<-].
    split; [exact: to_mem_mem_of |].
    split; [exact: (scnt_mem_of st sc (elimT (dominatesb_spec st sc) Es)) |].
    split; [exact: to_mem_mem_of |].
    exact: (alc_mem_of h c (elimT (dominatesb_spec h c) Eh)).
  - move=> [E1 [E2 [E3 E4]]]; subst.
    rewrite (introT (dominatesb_spec (store s) (scnt s)) (state_store_dominates s)).
    rewrite (introT (dominatesb_spec (heap s) (alc s)) (state_heap_dominates s)).
    congr Some.
    apply: state_eq_raw => /=.
    + exact: (mem_of_to_mem (smem s)).
    + exact: (mem_of_to_mem (hmem s)).
Qed.

Local Notation SCnt := (excl (@store_cnt Ad Pt (value Pt) St)).
Local Notation Alc := (excl (@heap_alc Ad Pt (value Pt) Hp)).

Lemma noalloc_sum_nblocks_r (x y z: mem unit)
  (EQ: mem_sum x y = Some z):
  (nblocks y <= nblocks z)%nat.
Proof using Type.
  case POS: (nblocks y) => [|n]; first by lia.
  have POS': (0 < nblocks y)%nat by lia.
  case: (mem_last_bound y POS') => [o [v Ev]].
  have SG := sum_get x y z EQ (Nat.pred (nblocks y)) o.
  rewrite Ev in SG.
  case LE: (Nat.leb (nblocks z) (Nat.pred (nblocks y))).
  - move/Nat.leb_le in LE.
    rewrite (get_nblocks_ge z _ o LE) in SG.
    move: SG.
    by case: (get x (Nat.pred (nblocks y)) o) => [w|] //=.
  - move/Nat.leb_gt in LE; lia.
Qed.

Lemma mem_sum_split (m1 m2 m3: mem (excl nat)):
  mem_sum m1 m2 = Some m3
  <-> (mem_sum (to_mem m1) (to_mem m2) = Some (to_mem m3)
       /\ to_tail m1 $+ to_tail m2 = Some (to_tail m3)).
Proof using Type.
  split.
  - move=> EQ; split.
    + exact: (to_mem_sum m1 m2 m3 EQ).
    + exact: (sum_to_tail m1 m2 m3 EQ).
  - move=> [EU Ea].
    have CELLS: forall bi o, osum vclash (get m1 bi o) (get m2 bi o) <> None.
    { move=> bi o.
      have := sum_get _ _ _ EU bi o.
      by rewrite !get_to_mem => ->. }
    have ALC: to_tail m1 $+ to_tail m2 <> None
      by rewrite Ea.
    have DOM1: forall B, to_tail m1 = Owned B -> (nblocks m2 <= B)%nat.
    { move=> B E1.
      rewrite E1 in Ea.
      case E2: (to_tail m2) Ea => [|j] //= Ea.
      case: Ea => Ea.
      have H1 := noalloc_sum_nblocks_r (to_mem m1) (to_mem m2) (to_mem m3) EU.
      have H2 := to_tail_nblocks_alloc m3 B (esym Ea).
      rewrite !nblocks_to_mem in H1.
      lia. }
    have DOM2: forall B, to_tail m2 = Owned B -> (nblocks m1 <= B)%nat.
    { move=> B E2.
      rewrite E2 in Ea.
      case E1: (to_tail m1) Ea => [|j] //= Ea.
      case: Ea => Ea.
      have EU': mem_sum (to_mem m2) (to_mem m1) = Some (to_mem m3)
        by rewrite mem_sum_comm.
      have H1 := noalloc_sum_nblocks_r (to_mem m2) (to_mem m1) (to_mem m3) EU'.
      have H2 := to_tail_nblocks_alloc m3 B (esym Ea).
      rewrite !nblocks_to_mem in H1.
      lia. }
    case: (proj1 (sum_defined_alloc m1 m2) (conj CELLS (conj ALC (conj DOM1 DOM2))))
      => [m EQm].
    have Em: m = m3.
    { apply: ext_tail.
      - move=> bi o.
        have S1 := sum_get m1 m2 m EQm bi o.
        have S2 := sum_get _ _ _ EU bi o.
        rewrite !get_to_mem in S2.
        rewrite S2 in S1.
        by case: S1.
      - have A1: to_tail m1 $+ to_tail m2 = Some (to_tail m)
          := sum_to_tail m1 m2 m EQm.
        rewrite Ea in A1.
        by case: A1. }
    by rewrite -Em.
Qed.

Definition state_pair (s: GCModel): mem (excl nat) * mem (excl nat) :=
  (smem s, hmem s).

Definition state_of_pair (p: mem (excl nat) * mem (excl nat)): GCModel :=
  mkState p.1 p.2.

Lemma state_pair_of_pair (p: mem (excl nat) * mem (excl nat)):
  state_pair (state_of_pair p) = p.
Proof using Type. by case: p. Qed.

Lemma state_of_pair_pair (s: GCModel): state_of_pair (state_pair s) = s.
Proof using Type. by case: s. Qed.

Lemma state_pair_inj (s1 s2: GCModel) (EQ: state_pair s1 = state_pair s2): s1 = s2.
Proof using Type.
  by rewrite -(state_of_pair_pair s1) -(state_of_pair_pair s2) EQ.
Qed.

(** Definition of the Separtation algebra *)
Definition state_sum (s1 s2: GCModel): option GCModel :=
  option_map state_of_pair (state_pair s1 $+ state_pair s2).

Lemma state_sum_pair (s1 s2 s: GCModel):
  state_sum s1 s2 = Some s <-> state_pair s1 $+ state_pair s2 = Some (state_pair s).
Proof using Type.
  rewrite /state_sum.
  case E: (state_pair s1 $+ state_pair s2) => [p|] //=.
  split.
  - by move=> [<-]; rewrite state_pair_of_pair.
  - by move=> [->]; rewrite state_of_pair_pair.
Qed.

Lemma state_sum_spec (s1 s2 s: GCModel):
  state_sum s1 s2 = Some s <->
    (store s1 $+ store s2 = Some (store s) /\
       scnt s1 $+ scnt s2 = Some (scnt s) /\
       heap s1 $+ heap s2 = Some (heap s) /\
       alc s1 $+ alc s2 = Some (alc s)).
Proof using Type.
  rewrite state_sum_pair prod_sum_spec /= !mem_sum_split.
  rewrite /store /scnt /heap /alc.
  split.
  - move=> [[H1 H2] [H3 H4]].
    split; [exact: H1 |].
    split; [exact: (excl_sum_map_mkNatCnt _ _ _ H2) |].
    split; [exact: H3 |].
    exact: (excl_sum_map_mkNatCnt _ _ _ H4).
  - move=> [H1 [H2 [H3 H4]]].
    split; split.
    + exact: H1.
    + exact: (excl_map_mkNatCnt_sum _ _ _ H2).
    + exact: H3.
    + exact: (excl_map_mkNatCnt_sum _ _ _ H4).
Qed.

Lemma state_sum_comm (s1 s2: GCModel): state_sum s1 s2 = state_sum s2 s1.
Proof using Type.
  by rewrite /state_sum op_comm.
Qed.

Definition emp: GCModel :=
  mk_state $0 $0 $0 $0 (dominates_emp _) (dominates_emp _).

Lemma state_pair_emp: state_pair emp = $0.
Proof using Type. reflexivity. Qed.

Lemma state_sum_id_l (s: GCModel): state_sum emp s = Some s.
Proof using Type.
  by rewrite /state_sum state_pair_emp op_id_l /= state_of_pair_pair.
Qed.

Lemma state_sum_id_r (s: GCModel): state_sum s emp = Some s.
Proof using Type.
  by rewrite /state_sum state_pair_emp op_id_r /= state_of_pair_pair.
Qed.

Lemma state_sum_cancel_l (x y z w: GCModel)
  (EQ1: state_sum x y = Some w) (EQ2: state_sum x z = Some w)
  : y = z.
Proof using Type.
  move: EQ1 EQ2 => /state_sum_pair EQ1 /state_sum_pair EQ2.
  exact: (state_pair_inj _ _ (op_cancel_l _ _ _ _ EQ1 EQ2)).
Qed.

Lemma state_sum_cancel_r (x y z w: GCModel)
  (EQ1: state_sum y x = Some w) (EQ2: state_sum z x = Some w)
  : y = z.
Proof using Type.
  move: EQ1 EQ2 => /state_sum_pair EQ1 /state_sum_pair EQ2.
  exact: (state_pair_inj _ _ (op_cancel_r _ _ _ _ EQ1 EQ2)).
Qed.

Lemma state_sum_assc (s1 s2 s3: GCModel):
  Option.bind (Basics.flip state_sum s3) (state_sum s1 s2)
  = Option.bind (state_sum s1) (state_sum s2 s3).
Proof using Type.
  have := op_assc (state_pair s1) (state_pair s2) (state_pair s3).
  rewrite /state_sum.
  case: (state_pair s1 $+ state_pair s2) => [p12|];
    case: (state_pair s2 $+ state_pair s3) => [p23|] //=;
    rewrite /Basics.flip /= ?state_pair_of_pair.
  - by move=> ->.
  - by move=> ->.
  - by move=> <-.
Qed.

Lemma state_sum_cross_split (a b c d z: GCModel)
  (EQ1: state_sum a b = Some z) (EQ2: state_sum c d = Some z)
  : exists ac ad bc bd: GCModel,
      state_sum ac ad = Some a /\ state_sum bc bd = Some b /\
      state_sum ac bc = Some c /\ state_sum ad bd = Some d.
Proof using Type.
  move: EQ1 EQ2 => /state_sum_pair E1 /state_sum_pair E2.
  case: (op_cross_split _ _ _ _ _ E1 E2) => ac [ad [bc [bd [EQa [EQb [EQc EQd]]]]]].
  exists (state_of_pair ac), (state_of_pair ad), (state_of_pair bc), (state_of_pair bd).
  by split; [|split; [|split]]; apply/state_sum_pair; rewrite !state_pair_of_pair.
Qed.

HB.instance Definition _ := hasOp.Build GCModel state_sum.
HB.instance Definition _ := hasComm.Build GCModel state_sum_comm.
HB.instance Definition _ := hasIdentity.Build GCModel emp state_sum_id_l state_sum_id_r.
HB.instance Definition _ := hasAssc.Build GCModel state_sum_assc.
HB.instance Definition _ := hasCancel.Build GCModel state_sum_cancel_l state_sum_cancel_r.
HB.instance Definition _ := hasCrossSplit.Build GCModel state_sum_cross_split.

Lemma state_emp: ($0: GCModel)
                 = mk_state $0 $0 $0 $0
                     (dominates_emp ($0: SCnt)) (dominates_emp ($0: Alc)).
Proof using Type. reflexivity. Qed.

HB.instance Definition _ :=
  isState.Build GCModel Ad Pt Pt St Hp
    store scnt heap alc
    mk_state mk_state_opt
    state_store_dominates state_heap_dominates
    state_ext
    store_mk_state scnt_mk_state
    heap_mk_state alc_mk_state
    mk_state_opt_some state_sum_spec
    state_emp.
