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

From Stdlib Require Import Arith NArith Lia Bool.
From Corelib Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

From GallinaC.Utils Require Import Algebra Counter OptionExt.
From GallinaC.Utils Require Export Excl.
From GallinaC.Imp Require Import Addr RWMemory Heap.
From GallinaC.Imp Require Import Value.
From GallinaC.Models Require Import Pointer.
From GallinaC.Models Require Import BlockMemory.

Local Open Scope separation_scope.
Local Open Scope mem_scope.

(** * List heap

Model of [Heap]
 *)

(* isPtr instance on Pointer.t moved to Pointer.v *)

(* Allocation and deallocation *)

Definition list_heap_alloc (h: mem unit) (alc: excl nat_cnt) (sz: N) (v: value Pointer.t)
  : option (mem unit * excl nat_cnt * Pointer.t) :=
  match eget alc with
  | Some bid =>
      if ((0 <? sz)%N && block_vacant h bid)%bool then
        match mem_sum h (full_at bid (N.to_nat sz - 1) v) with
        | Some m' =>
            Some (m', enext alc,
                  Some (Addr.mkAddr bid 0%N,
                        Provenance.Allocation bid 0%N sz 0%N sz Permission.Free))
        | None => None
        end
      else None
  | None => None
  end.

Definition list_heap_free (h: mem unit) (p: Pointer.t): option (mem unit) :=
  match p with
  | Some (a, prov) =>
      if Pointer.allows p Operation.Free then
        if mcovers h (Provenance.prov_block prov)
             (N.to_nat (Provenance.prov_eofst prov) - 1)
        then Some (mdiff_noalloc h
                     (full_at (Provenance.prov_block prov)
                        (N.to_nat (Provenance.prov_eofst prov) - 1) (v_tt: value Pointer.t)))
        else None
      else None
  | None => None
  end.

(* Reach of an allocation-shaped provenance *)
Lemma provenance_within_iff: forall b eo (a: Addr.t),
    Provenance.within a (Provenance.Allocation b 0%N eo 0%N eo Permission.Free) = true
    <-> (Imp.Addr.block a = b /\ (offset a <= eo)%N).
Proof.
  move=> b eo [ba o].
  rewrite /= N.leb_refl.
  split.
  - move=> /andP [/andP [/andP [H1 H2] H3] H4].
    split; [ by apply/Nat.eqb_eq | by apply/N.leb_le ].
  - move=> [HB HO]; subst b.
    rewrite Nat.eqb_refl.
    have H3: (0 <=? o)%N = true by apply/N.leb_le; apply: N.le_0_l.
    have H4: (o <=? eo)%N = true by apply/N.leb_le.
    by rewrite H3 H4.
Qed.

Lemma provenance_reach_strict_iff: forall b eo (a: Addr.t),
    (Provenance.within a (Provenance.Allocation b 0%N eo 0%N eo Permission.Free) = true
     /\ Provenance.within ((shift_fw a 1%N): Addr.t)
          (Provenance.Allocation b 0%N eo 0%N eo Permission.Free) = true)
    <-> (Imp.Addr.block a = b /\ (offset a < eo)%N).
Proof.
  move=> b eo a.
  rewrite !provenance_within_iff shift_fw_block shift_fw_offset.
  split.
  - move=> [[HB _] [_ HO]].
    split; [ exact: HB | lia ].
  - move=> [HB HO].
    repeat split; try exact: HB; lia.
Qed.

Lemma list_heap_alloc_eq: forall h alc sz v h' alc' p
    (EQ: list_heap_alloc h alc sz v = Some (h', alc', p)),
    exists bid,
      eget alc = Some bid
      /\ (0 <? sz)%N = true
      /\ block_vacant h bid = true
      /\ mem_sum h (full_at bid (N.to_nat sz - 1) v) = Some h'
      /\ alc' = enext alc
      /\ p = Some (Addr.mkAddr bid 0%N,
                   Provenance.Allocation bid 0%N sz 0%N sz Permission.Free).
Proof.
  move=> h alc sz v h' alc' p EQ.
  move: EQ; rewrite /list_heap_alloc.
  case G: (eget alc) => [bid|] //.
  case C: ((0 <? sz)%N && block_vacant h bid)%bool => //.
  move: C => /andP [C1 C2].
  case Em: (mem_sum h (full_at bid (N.to_nat sz - 1) v)) => [m'|] //.
  move=> EQ.
  injection EQ as E1 E2 E3.
  subst m' alc' p.
  exists bid.
  by repeat split.
Qed.

Lemma list_heap_alloc_some: forall (h: mem unit) (alc: excl nat_cnt) (sz: N) (v: value Pointer.t),
    (exists bid, eget alc = Some bid /\ (0 < sz)%N
                 /\ forall (o: N) (v': value Pointer.t), ~ (aone ((mkAddr bid o): Addr.t) v' $<= h))
    <-> exists h' alc' p, list_heap_alloc h alc sz v = Some (h', alc', p).
Proof.
  move=> mm alc sz v.
  split.
  - move=> [bid [G [SZ FRESH]]].
    have V: block_vacant mm bid = true by exact: (proj1 (block_fresh_iff mm bid) FRESH).
    have SZ2: (0 <? sz)%N = true by apply/N.ltb_lt.
    have [m' Em]: exists m, mem_sum mm (full_at bid (N.to_nat sz - 1) v) = Some m.
    { apply: (proj1 (sum_defined_noalloc mm (full_at bid (N.to_nat sz - 1) v))).
      move=> bi o.
      rewrite get_full_at.
      case Eb: (Nat.eqb bi bid) => /=; last by case: (get mm bi o).
      case Eo: (Nat.leb o (N.to_nat sz - 1)) => /=; last by case: (get mm bi o).
      move: Eb => /Nat.eqb_eq Eb; subst bi.
      case: (block_vacant_spec mm bid) V => [NB|NV] V; last by [].
      case Ew: (get mm bid o) => [w|].
      - by exfalso; exact: (NB o w Ew).
      - by []. }
    exists m', (enext alc),
      (Some (Addr.mkAddr bid 0%N, Provenance.Allocation bid 0%N sz 0%N sz Permission.Free)).
    rewrite /list_heap_alloc G SZ2 V /=.
    by rewrite Em.
  - move=> [h' [alc' [p EQ]]].
    case: (list_heap_alloc_eq _ _ _ _ _ _ _ EQ) => [bid [G [SZ [V _]]]].
    exists bid.
    split; [ exact: G | ].
    split; [ by apply/N.ltb_lt | ].
    apply: (proj2 (block_fresh_iff mm bid)).
    exact: V.
Qed.

Lemma list_heap_alloc_references: forall h alc sz v h' alc' p bid,
    list_heap_alloc h alc sz v = Some (h', alc', p) ->
    eget alc = Some bid ->
    References p ((mkAddr bid 0%N): Addr.t).
Proof.
  move=> h alc sz v h' alc' p bid EQ G.
  case: (list_heap_alloc_eq _ _ _ _ _ _ _ EQ)
    => [bid' [G' [_ [_ [_ [_ ->]]]]]].
  rewrite G in G'; injection G' as G'; subst bid'.
  by [].
Qed.

Lemma list_heap_alloc_allows: forall h alc sz v h' alc' p bid,
    list_heap_alloc h alc sz v = Some (h', alc', p) ->
    eget alc = Some bid ->
    Allows p Operation.Free.
Proof.
  move=> h alc sz v h' alc' p bid EQ G.
  case: (list_heap_alloc_eq _ _ _ _ _ _ _ EQ)
    => [bid' [G' [SZ [_ [_ [_ ->]]]]]].
  have GOAL: Provenance.allows (Addr.mkAddr bid' 0%N) Operation.Free
                  (Provenance.Allocation bid' 0%N sz 0%N sz Permission.Free) = true.
  { rewrite /= Nat.eqb_refl N.eqb_refl /=.
    exact: SZ. }
  exact: GOAL.
Qed.

Lemma list_heap_alloc_reaches: forall h alc sz v h' alc' p bid,
    list_heap_alloc h alc sz v = Some (h', alc', p) ->
    eget alc = Some bid ->
    forall sz', (sz' <= sz)%N <-> Reaches p ((mkAddr bid sz'): Addr.t).
Proof.
  move=> h alc sz v h' alc' p bid EQ G sz'.
  case: (list_heap_alloc_eq _ _ _ _ _ _ _ EQ)
    => [bid' [G' [_ [_ [_ [_ ->]]]]]].
  rewrite G in G'; injection G' as G'; subst bid'.
  split.
  - move=> LE.
    have W: Provenance.within ((mkAddr bid sz'): Addr.t)
                 (Provenance.Allocation bid 0%N sz 0%N sz Permission.Free) = true.
    { apply: (proj2 (provenance_within_iff bid sz ((mkAddr bid sz'): Addr.t))).
      rewrite mkAddr_block mkAddr_offset.
      by split. }
    exact: W.
  - move=> R.
    have W: Provenance.within ((mkAddr bid sz'): Addr.t)
                 (Provenance.Allocation bid 0%N sz 0%N sz Permission.Free) = true
      by exact: R.
    case: (proj1 (provenance_within_iff bid sz ((mkAddr bid sz'): Addr.t)) W) => [_ HO].
    rewrite mkAddr_offset in HO.
    exact: HO.
Qed.

Lemma list_heap_alloc_mem: forall h alc sz v h' alc' p,
    list_heap_alloc h alc sz v = Some (h', alc', p) ->
    forall (a': Addr.t) (v': value Pointer.t),
      (aone a' v') $<= h'
      <-> ((Reaches p a' /\ Reaches p ((shift_fw a' 1%N): Addr.t) /\ v' = v)
           \/ (~(Reaches p a' /\ Reaches p ((shift_fw a' 1%N): Addr.t))
               /\ (aone a' v') $<= h)).
Proof.
  move=> mm alc sz v h' alc' p EQ a' v'.
  case: (list_heap_alloc_eq _ _ _ _ _ _ _ EQ)
    => [bid [G [SZ [V [Em [Ealc Ep]]]]]].
  subst alc' p.
  have SZpos: (0 < sz)%N by apply/N.ltb_lt.
  have SIFF: (Reaches ((Some (Addr.mkAddr bid 0%N,
                                 Provenance.Allocation bid 0%N sz 0%N sz Permission.Free)): Pointer.t) a'
                 /\ Reaches ((Some (Addr.mkAddr bid 0%N,
                                   Provenance.Allocation bid 0%N sz 0%N sz Permission.Free)): Pointer.t)
                      ((shift_fw a' 1%N): Addr.t))
                <-> (Imp.Addr.block a' = bid /\ (offset a' < sz)%N).
  { split.
    - move=> [R1 R2].
      apply: (proj1 (provenance_reach_strict_iff bid sz a')).
      by split.
    - move=> H.
      by case: (proj2 (provenance_reach_strict_iff bid sz a') H) => [W1 W2]; split. }
  have S := sum_get _ _ _ Em (Imp.Addr.block a') (N.to_nat (offset a')).
  have F: get (full_at (A:=unit) bid (N.to_nat sz - 1) v) (Imp.Addr.block a') (N.to_nat (offset a'))
             = if (Nat.eqb (Imp.Addr.block a') bid && Nat.leb (N.to_nat (offset a')) (N.to_nat sz - 1))%bool
               then Some v else None
    by apply: get_full_at.
  have V2: block_vacant mm bid = true by exact: V.
  case: (block_vacant_spec mm bid) V2 => [NB|NV] V2; last by [].
  split.
  - move=> SUB.
    have GG := proj1 (aone_sub_noalloc a' v' h') SUB.
    have GG2: get h' (Imp.Addr.block a') (N.to_nat (offset a')) = Some v' by exact: GG.
    rewrite GG2 in S.
    case Eb: (Nat.eqb (Imp.Addr.block a') bid).
    + case Eo: (Nat.leb (N.to_nat (offset a')) (N.to_nat sz - 1)).
      * left.
        rewrite F Eb Eo /= in S.
        case Ew: (get mm (Imp.Addr.block a') (N.to_nat (offset a'))) => [w|]; rewrite Ew /= in S.
        -- exfalso.
           move: Eb => /Nat.eqb_eq Eb.
           rewrite Eb in Ew.
           exact: (NB _ _ Ew).
        -- injection S as S2.
           subst v'.
           have STRICT: Imp.Addr.block a' = bid /\ (offset a' < sz)%N.
           { split; [ by apply/Nat.eqb_eq | ].
             move: Eo => /Nat.leb_le Eo.
             lia. }
           case: (proj2 SIFF STRICT) => [R1 R2].
           by split; [ | split ].
      * right.
        rewrite F Eb Eo /= in S.
        have NR: ~ (Reaches ((Some (Addr.mkAddr bid 0%N,
                                       Provenance.Allocation bid 0%N sz 0%N sz Permission.Free)): Pointer.t) a'
                       /\ Reaches ((Some (Addr.mkAddr bid 0%N,
                                         Provenance.Allocation bid 0%N sz 0%N sz Permission.Free)): Pointer.t)
                            ((shift_fw a' 1%N): Addr.t)).
        { move=> RR.
          case: (proj1 SIFF RR) => [_ HO].
          move: Eo => /Nat.leb_gt Eo.
          lia. }
        split; [ exact: NR | ].
        case Ew: (get mm (Imp.Addr.block a') (N.to_nat (offset a'))) => [w|]; rewrite Ew /= in S.
        -- injection S as S2.
           subst w.
           apply: (proj2 (aone_sub_noalloc a' v' mm)).
           exact: Ew.
        -- by [].
    + right.
      rewrite F Eb /= in S.
      have NR: ~ (Reaches ((Some (Addr.mkAddr bid 0%N,
                                     Provenance.Allocation bid 0%N sz 0%N sz Permission.Free)): Pointer.t) a'
                     /\ Reaches ((Some (Addr.mkAddr bid 0%N,
                                       Provenance.Allocation bid 0%N sz 0%N sz Permission.Free)): Pointer.t)
                          ((shift_fw a' 1%N): Addr.t)).
      { move=> RR.
        case: (proj1 SIFF RR) => [HB _].
        by rewrite HB Nat.eqb_refl in Eb. }
      split; [ exact: NR | ].
      case Ew: (get mm (Imp.Addr.block a') (N.to_nat (offset a'))) => [w|]; rewrite Ew /= in S.
      * injection S as S2.
        subst w.
        apply: (proj2 (aone_sub_noalloc a' v' mm)).
        exact: Ew.
      * by [].
  - move=> [[R1 [R2 ->]] | [NR SUB]].
    + case: (proj1 SIFF (conj R1 R2)) => [HB HO].
      apply: (proj2 (aone_sub_noalloc a' v h')).
      have EbT: Nat.eqb (Imp.Addr.block a') bid = true by apply/Nat.eqb_eq.
      have EoT: Nat.leb (N.to_nat (offset a')) (N.to_nat sz - 1) = true
        by apply/Nat.leb_le; lia.
      rewrite F EbT EoT /= in S.
      case Ew: (get mm (Imp.Addr.block a') (N.to_nat (offset a'))) => [w|]; rewrite Ew /= in S.
      * exfalso.
        rewrite HB in Ew.
        exact: (NB _ _ Ew).
      * injection S as S2.
        symmetry; exact: S2.
    + apply: (proj2 (aone_sub_noalloc a' v' h')).
      have GG := proj1 (aone_sub_noalloc a' v' mm) SUB.
      have GG2: get mm (Imp.Addr.block a') (N.to_nat (offset a')) = Some v' by exact: GG.
      have FN: get (full_at (A:=unit) bid (N.to_nat sz - 1) v) (Imp.Addr.block a') (N.to_nat (offset a')) = None.
      { rewrite F.
        case EbT: (Nat.eqb (Imp.Addr.block a') bid) => /=; last by [].
        case EoT: (Nat.leb (N.to_nat (offset a')) (N.to_nat sz - 1)); last by [].
        exfalso; apply: NR.
        apply: (proj2 SIFF).
        split; [ by apply/Nat.eqb_eq | ].
        move: EoT => /Nat.leb_le EoT.
        lia. }
      rewrite GG2 FN /= in S.
      injection S as S2.
      symmetry; exact: S2.
Qed.


Lemma list_heap_alloc_alc: forall h alc sz v h' alc' p,
    list_heap_alloc h alc sz v = Some (h', alc', p) ->
    alc' = enext alc.
Proof.
  move=> h alc sz v h' alc' p EQ.
  case: (list_heap_alloc_eq _ _ _ _ _ _ _ EQ)
    => [bid [_ [_ [_ [_ [-> _]]]]]].
  by [].
Qed.

Lemma list_heap_alloc_det: forall h1 h2 alc sz v1 v2 h1' h2' alc1' alc2' p1 p2,
    list_heap_alloc h1 alc sz v1 = Some (h1', alc1', p1) ->
    list_heap_alloc h2 alc sz v2 = Some (h2', alc2', p2) ->
    p1 = p2.
Proof.
  move=> h1 h2 alc sz v1 v2 h1' h2' alc1' alc2' p1 p2 EQ1 EQ2.
  case: (list_heap_alloc_eq _ _ _ _ _ _ _ EQ1)
    => [bid1 [G1 [_ [_ [_ [_ ->]]]]]].
  case: (list_heap_alloc_eq _ _ _ _ _ _ _ EQ2)
    => [bid2 [G2 [_ [_ [_ [_ ->]]]]]].
  rewrite G1 in G2.
  congruence.
Qed.

Lemma list_heap_free_eq: forall h p h'
    (EQ: list_heap_free h p = Some h'),
    exists b eo,
      p = Some (Addr.mkAddr b 0%N, Provenance.Allocation b 0%N eo 0%N eo Permission.Free)
      /\ (0 < eo)%N
      /\ mcovers h b (N.to_nat eo - 1) = true
      /\ h' = mdiff_noalloc h (full_at b (N.to_nat eo - 1) (v_tt: value Pointer.t)).
Proof.
  move=> h p h' EQ.
  move: EQ; rewrite /list_heap_free.
  case: p => [[a prov]|] //.
  case ALW: (Pointer.allows (Some (a, prov)) Operation.Free) => //.
  move=> EQ.
  case: (pointer_allows_free_inv a prov ALW) => [b [eo [Ea [Ep POS]]]].
  subst a prov.
  move: EQ.
  cbn [Provenance.prov_block Provenance.prov_eofst].
  case C: (mcovers h b (N.to_nat eo - 1)) => //.
  move=> [<-].
  exists b, eo.
  by repeat split.
Qed.

Lemma list_heap_free_some: forall (h: mem unit) (p: Pointer.t),
    (Allows p Operation.Free
     /\ (forall a, Reaches p a -> Reaches p ((shift_fw a 1%N): Addr.t)
                   -> exists v, (aone a v) $<= h))
    <-> exists h', list_heap_free h p = Some h'.
Proof.
  move=> mm p.
  split.
  - move=> [ALW COV].
    case: p ALW COV => [[a prov]|] ALW COV; last by [].
    have ALW2: Pointer.allows (Some (a, prov)) Operation.Free = true by exact: ALW.
    case: (pointer_allows_free_inv a prov ALW2) => [b [eo [Ea [Ep POS]]]].
    subst a prov.
    have COV0: forall o: nat, o <= N.to_nat eo - 1 ->
                  exists v, (aone ((mkAddr b (N.of_nat o)): Addr.t) v) $<= mm.
    { move=> o LE.
      apply: (COV ((mkAddr b (N.of_nat o)): Addr.t)).
      - have W: Provenance.within ((mkAddr b (N.of_nat o)): Addr.t)
                     (Provenance.Allocation b 0%N eo 0%N eo Permission.Free) = true.
        { apply: (proj2 (provenance_within_iff b eo _)).
          rewrite mkAddr_block mkAddr_offset.
          split; [ by [] | lia ]. }
        exact: W.
      - have W: Provenance.within ((shift_fw ((mkAddr b (N.of_nat o)): Addr.t) 1%N): Addr.t)
                     (Provenance.Allocation b 0%N eo 0%N eo Permission.Free) = true.
        { apply: (proj2 (provenance_within_iff b eo _)).
          rewrite shift_fw_block shift_fw_offset mkAddr_block mkAddr_offset.
          split; [ by [] | lia ]. }
        exact: W. }
    have C: mcovers mm b (N.to_nat eo - 1) = true.
    { case: (mcovers_spec mm b (N.to_nat eo - 1)) => [CC|NC] //.
      exfalso; apply: NC.
      move=> o LE.
      case: (COV0 o LE) => [v SUB].
      have G := proj1 (aone_sub_noalloc _ v mm) SUB.
      exists v.
      move: G.
      by rewrite /aget mkAddr_block mkAddr_offset Nat2N.id. }
    eexists.
    rewrite /list_heap_free ALW2.
    cbn [Provenance.prov_block Provenance.prov_eofst].
    by rewrite C.
  - move=> [h' EQ].
    case: (list_heap_free_eq _ _ _ EQ)
      => [b [eo [-> [POS [C _]]]]].
    split.
    + have ALW: Provenance.allows (Addr.mkAddr b 0%N) Operation.Free
                     (Provenance.Allocation b 0%N eo 0%N eo Permission.Free) = true.
      { rewrite /= Nat.eqb_refl N.eqb_refl /=.
        by apply/N.ltb_lt. }
      exact: ALW.
    + move=> a R1 R2.
      have W1: Provenance.within a (Provenance.Allocation b 0%N eo 0%N eo Permission.Free) = true
        by exact: R1.
      have W2: Provenance.within ((shift_fw a 1%N): Addr.t)
                    (Provenance.Allocation b 0%N eo 0%N eo Permission.Free) = true
        by exact: R2.
      case: (proj1 (provenance_reach_strict_iff b eo a) (conj W1 W2)) => [HB HO].
      case: (mcovers_spec mm b (N.to_nat eo - 1)) C => [CC|NC] C; last by [].
      case: (CC (N.to_nat (offset a)) ltac:(lia)) => [v Ev].
      exists v.
      apply: (proj2 (aone_sub_noalloc a v mm)).
      rewrite /aget HB.
      exact: Ev.
Qed.

Lemma list_heap_free_mem: forall (h: mem unit) (p: Pointer.t) (h': mem unit),
    list_heap_free h p = Some h' ->
    forall a: Addr.t,
      (((Reaches p a /\ Reaches p ((shift_fw a 1%N): Addr.t))
        /\ ~(exists v, (aone a v) $<= h'))
       \/ (~(Reaches p a /\ Reaches p ((shift_fw a 1%N): Addr.t))
           /\ (forall v, (aone a v) $<= h <-> (aone a v) $<= h'))).
Proof.
  move=> mm p h' EQ a.
  case: (list_heap_free_eq _ _ _ EQ)
    => [b [eo [-> [POS [C ->]]]]].
  case W: (Provenance.within a (Provenance.Allocation b 0%N eo 0%N eo Permission.Free)
            && Provenance.within ((shift_fw a 1%N): Addr.t)
                 (Provenance.Allocation b 0%N eo 0%N eo Permission.Free))%bool.
  - move: W => /andP [W1 W2].
    left.
    split; [ by split | ].
    move=> [v SUB].
    case: (proj1 (provenance_reach_strict_iff b eo a) (conj W1 W2)) => [HB HO].
    have G := proj1 (aone_sub_noalloc a v _) SUB.
    have G2: get (mdiff_noalloc mm (full_at b (N.to_nat eo - 1) (v_tt: value Pointer.t)))
                  (Imp.Addr.block a) (N.to_nat (offset a)) = Some v by exact: G.
    rewrite mdiff_get_noalloc get_full_at in G2.
    have EbT: Nat.eqb (Imp.Addr.block a) b = true by apply/Nat.eqb_eq.
    have EoT: Nat.leb (N.to_nat (offset a)) (N.to_nat eo - 1) = true
      by apply/Nat.leb_le; lia.
    by rewrite EbT EoT /= in G2.
  - right.
    split.
    { move=> [R1 R2].
      have W1: Provenance.within a (Provenance.Allocation b 0%N eo 0%N eo Permission.Free) = true
        by exact: R1.
      have W2: Provenance.within ((shift_fw a 1%N): Addr.t)
                    (Provenance.Allocation b 0%N eo 0%N eo Permission.Free) = true
        by exact: R2.
      by rewrite W1 W2 in W. }
    move=> v.
    have FN: get (full_at (A:=unit) b (N.to_nat eo - 1) (v_tt: value Pointer.t)) (Imp.Addr.block a) (N.to_nat (offset a)) = None.
    { rewrite get_full_at.
      case EbT: (Nat.eqb (Imp.Addr.block a) b) => /=; last by [].
      case EoT: (Nat.leb (N.to_nat (offset a)) (N.to_nat eo - 1)); last by [].
      exfalso.
      have HB: Imp.Addr.block a = b by apply/Nat.eqb_eq.
      have HO: (offset a < eo)%N by move: EoT => /Nat.leb_le EoT; lia.
      case: (proj2 (provenance_reach_strict_iff b eo a) (conj HB HO)) => [W1 W2].
      by rewrite W1 W2 in W. }
    split.
    + move=> SUB.
      have G := proj1 (aone_sub_noalloc a v _) SUB.
      apply: (proj2 (aone_sub_noalloc a v _)).
      have G2: get (mdiff_noalloc mm (full_at b (N.to_nat eo - 1) (v_tt: value Pointer.t)))
                    (Imp.Addr.block a) (N.to_nat (offset a)) = Some v.
      { rewrite mdiff_get_noalloc FN.
        exact: G. }
      exact: G2.
    + move=> SUB.
      have G := proj1 (aone_sub_noalloc a v _) SUB.
      apply: (proj2 (aone_sub_noalloc a v _)).
      have G2: get (mdiff_noalloc mm (full_at b (N.to_nat eo - 1) (v_tt: value Pointer.t)))
                    (Imp.Addr.block a) (N.to_nat (offset a)) = Some v by exact: G.
      rewrite mdiff_get_noalloc FN in G2.
      exact: G2.
Qed.

HB.instance Definition _ :=
  isHeap.Build Addr.t Pointer.t (value Pointer.t) (mem unit)
    nat_cnt
    list_heap_alloc
    list_heap_free
    list_heap_alloc_some
    list_heap_alloc_references
    list_heap_alloc_allows
    list_heap_alloc_reaches
    list_heap_alloc_mem
    list_heap_alloc_alc
    list_heap_alloc_det
    list_heap_free_some
    list_heap_free_mem.

Theorem freeable_Extent (addr: Addr.t) (prov: Provenance.t)
  (FREEABLE: Allows (Some (addr, prov): Pointer.t) Operation.Free)
  : Extent (Some (addr, prov): Pointer.t)
           (Addr.block addr)
           (Provenance.prov_meofst prov)
    /\ Provenance.prov_eofst prov = Provenance.prov_meofst prov
    /\ Addr.offset addr = 0%N.
Proof.
  move: FREEABLE.
  rewrite /allows /=.
  case: addr => [b o]; case: prov => [pb bofst eofst mbofst meofst perm].
  case: o => [|o] //=; case: bofst => [|bofst] //=;
    case: mbofst => [|mbofst] //=; case: perm => //=.
  move=> /andP [/andP [/Nat.eqb_eq -> /N.eqb_eq EQe] /N.ltb_lt POS].
  subst eofst.
  split; last (split; [reflexivity|reflexivity]).
  move=> o'.
  rewrite /reaches /= /Provenance.within /Provenance.wf /=.
  split.
  - by move=> /andP [_ /N.leb_le].
  - move=> LE.
    apply/andP; split; last by apply/N.leb_le.
    apply/andP; split; last by apply/N.leb_le; lia.
    apply/andP; split; [by apply/Nat.eqb_eq | by apply/N.leb_le; lia].
Qed.
