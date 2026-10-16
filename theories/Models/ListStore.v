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

From Stdlib Require Import Arith NArith Lia.
From Corelib Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

From GallinaC.Utils Require Import Algebra.
From GallinaC.Imp Require Import Addr RWMemory Store Heap.
From GallinaC.Imp Require Import Value.
From GallinaC.Models Require Import Pointer.
From GallinaC.Models Require Import BlockMemory.

Local Open Scope separation_scope.
Local Open Scope mem_scope.

(** * List store

Model of [Store]: a canonical block memory of [(value Pointer.t)]s. Under the hood, it allocates a memory block for each variable and pointers serve as references to them. Provenance prevents abuse.
 *)

(* Names *)

Definition list_store_ref (k: nat): Pointer.t :=
  Some (Addr.mkAddr k 0%N, Provenance.Allocation k 0%N 1%N 0%N 1%N Permission.Write).

Lemma list_store_ref_allows_write: forall k, Allows (list_store_ref k) Operation.Write.
Proof.
  move=> k.
  have GOAL: Provenance.allows (Addr.mkAddr k 0%N) Operation.Write
               (Provenance.Allocation k 0%N 1%N 0%N 1%N Permission.Write) = true
    by rewrite /= Nat.eqb_refl.
  exact: GOAL.
Qed.

(* Push and pop *)

Definition list_store_push (s: mem unit) (g: excl nat_cnt) (v: value Pointer.t)
  : option (mem unit * excl nat_cnt * Pointer.t) :=
  match eget g with
  | Some k =>
      if block_vacant s k then
        match mem_sum s (one_at k 0 v) with
        | Some m' => Some (m', enext g, list_store_ref k)
        | None => None
        end
      else None
  | None => None
  end.

Lemma list_store_push_eq: forall s g v s' g' n
    (EQ: list_store_push s g v = Some (s', g', n)),
    exists k,
      eget g = Some k
      /\ block_vacant s k = true
      /\ mem_sum s (one_at k 0 v) = Some s'
      /\ g' = enext g /\ n = list_store_ref k.
Proof.
  move=> s g v s' g' n EQ.
  rewrite /list_store_push in EQ.
  move: EQ.
  case Eg: (eget g) => [k|] //.
  case Ev: (block_vacant s k) => //.
  case Em: (mem_sum s (one_at k 0 v)) => [m'|] //.
  case=> E1 E2 E3; subst.
  by exists k.
Qed.

Lemma list_store_push_some: forall (s: mem unit) (g: excl nat_cnt) (v: value Pointer.t),
    (exists nm, eget g = Some nm
                /\ forall (o: N) v', ~ ((aone ((mkAddr nm o): Addr.t) v') $<= s))
    <-> exists s' g' n, list_store_push s g v = Some (s', g', n).
Proof.
  move=> mm g v.
  split.
  - case=> [nm [Eg FRESH]].
    have V: block_vacant mm nm = true
      by exact: (proj1 (block_fresh_iff mm nm) FRESH).
    have NB: forall o w, get mm nm o <> Some w.
    { case: (block_vacant_spec mm nm) V => [NB|NV] V; [ exact: NB | discriminate V ]. }
    have [m' Em]: exists m', mem_sum mm (one_at nm 0 v) = Some m'.
    { apply: (sum_one_fresh_at_noalloc mm nm 0 v).
      move=> o'.
      case Eo: (get mm nm o') => [w|] //.
      exfalso; exact: (NB o' w Eo). }
    exists m', (enext g), (list_store_ref nm).
    rewrite /list_store_push.
    by rewrite Eg V Em.
  - case=> [s' [g' [n EQ]]].
    case: (list_store_push_eq _ _ _ _ _ _ EQ) => [k [Eg [V _]]].
    exists k; split; [ exact: Eg | ].
    apply: (proj2 (block_fresh_iff mm k)).
    exact: V.
Qed.

Lemma list_store_push_mem: forall (s: mem unit) (g: excl nat_cnt) (v: value Pointer.t)
    (s': mem unit) (g': excl nat_cnt) (n: Pointer.t) (nm: nat)
    (EQ: list_store_push s g v = Some (s', g', n))
    (GET: eget g = Some nm),
    References n ((mkAddr nm 0%N): Addr.t)
    /\ Allows n Operation.Write
    /\ (aone ((mkAddr nm 0%N): Addr.t) v) $+ s = Some s'.
Proof.
  move=> s g v s' g' n nm EQ GET.
  case: (list_store_push_eq _ _ _ _ _ _ EQ) => [k [Eg [V [Em [Eg' ->]]]]].
  have Ek: k = nm by congruence.
  subst k.
  split; [ by [] | ].
  split; [ exact: list_store_ref_allows_write | ].
  have G: mem_sum (aone ((mkAddr nm 0%N): Addr.t) v) s = Some s'.
  { rewrite aone_mkAddr mem_sum_comm.
    change (N.to_nat 0%N) with 0.
    by rewrite Em. }
  exact: G.
Qed.

Lemma list_store_push_cnt: forall (s: mem unit) (g: excl nat_cnt) (v: value Pointer.t)
    (s': mem unit) (g': excl nat_cnt) (n: Pointer.t)
    (EQ: list_store_push s g v = Some (s', g', n)),
    g' = enext g.
Proof.
  move=> s g v s' g' n EQ.
  by case: (list_store_push_eq _ _ _ _ _ _ EQ)
    => [k [Eg [V [Em [-> En]]]]].
Qed.

Lemma list_store_push_det: forall (s1 s2: mem unit) (g: excl nat_cnt) (v1 v2: value Pointer.t)
    s1' s2' g1' g2' n1 n2
    (EQ1: list_store_push s1 g v1 = Some (s1', g1', n1))
    (EQ2: list_store_push s2 g v2 = Some (s2', g2', n2)),
    n1 = n2.
Proof.
  move=> s1 s2 g v1 v2 s1' s2' g1' g2' n1 n2 EQ1 EQ2.
  case: (list_store_push_eq _ _ _ _ _ _ EQ1)
    => [k1 [E1 [Va [Ema [Ega ->]]]]].
  case: (list_store_push_eq _ _ _ _ _ _ EQ2)
    => [k2 [E2 [Vb [Emb [Egb ->]]]]].
  have Ek: k1 = k2 by congruence.
  by rewrite Ek.
Qed.

Lemma list_store_pop_emp: mpop ($0: mem unit) = None.
Proof. by []. Qed.

Lemma list_store_pop_some: forall (s: mem unit) (NEMP: s <> $0),
    exists s', mpop s = Some s'.
Proof.
  move=> s NEMP.
  apply: mpop_some.
  move=> [] Es; subst s.
  by apply: NEMP.
Qed.

Lemma list_store_pop_mem: forall (s s': mem unit) (EQ: mpop s = Some s'),
    exists bl bi,
      s' $+ bl = Some s
      /\ (exists (a: Addr.t) (v: value Pointer.t), (aone a v) $<= bl)
      /\ (forall (a: Addr.t) (v: value Pointer.t), (aone a v) $<= bl -> Imp.Addr.block a = bi)
      /\ (forall (a: Addr.t) (v: value Pointer.t), (aone a v) $<= s' -> Imp.Addr.block a < bi).
Proof.
  move=> s s' EQ.
  case: s EQ => [[]|m] EQ.
  { change (None = Some s') in EQ; discriminate EQ. }
  have [mp Emp]: exists m', mpop (MLive m) = Some m'.
  { by apply: mpop_some. }
  have Es': s' = mp.
  { rewrite Emp in EQ.
    congruence. }
  subst s'.
  have MG := mpop_get (MLive m) mp Emp.

  have INCL: forall bi o v, get mp bi o = Some v -> get (MLive m) bi o = Some v.
  { move=> bi o v G.
    rewrite MG in G.
    move: G.
    by case: (Nat.eqb (S bi) (nblocks (MLive m))). }
  have [m3 [Esum Gm3raw]]: exists m3,
      mem_sum mp m3 = Some (MLive m)
      /\ (forall bi o, get m3 bi o = match get mp bi o with
                                     | Some _ => None
                                     | None => get (MLive m) bi o
                                     end).
  { exists (mdiff_noalloc (MLive m) mp).
    split.
    - exact: (sum_complement_noalloc mp (MLive m) INCL).
    - move=> bi o.
      exact: mdiff_get_noalloc. }

  have Gm3: forall bi o,
      get m3 bi o = if Nat.eqb (S bi) (nblocks (MLive m))
                    then get (MLive m) bi o
                    else None.
  { move=> bi o.
    rewrite Gm3raw MG.
    case Eb: (Nat.eqb (S bi) (nblocks (MLive m))) => //.
    by case: (get (MLive m) bi o). }

  have POS: 1 <= nblocks (MLive m) := mem'_nblocks_pos m.
  have Etop: Nat.eqb (S (Nat.pred (nblocks (MLive m)))) (nblocks (MLive m)) = true.
  { apply/Nat.eqb_eq; lia. }

  exists m3, (Nat.pred (nblocks (MLive m))).
  split; [ | split; [ | split ] ].

  - exact: Esum.

  - case: (mem_last_bound (MLive m) POS) => [o [v EGET]].
    exists ((mkAddr (Nat.pred (nblocks (MLive m))) (N.of_nat o)): Addr.t), v.
    apply: (proj2 (aone_sub_noalloc _ v m3)).
    change (get m3 (Imp.Addr.block ((mkAddr (Nat.pred (nblocks (MLive m))) (N.of_nat o)): Addr.t))
              (N.to_nat (offset ((mkAddr (Nat.pred (nblocks (MLive m))) (N.of_nat o)): Addr.t)))
            = Some v).
    rewrite mkAddr_block mkAddr_offset Nat2N.id Gm3 Etop.
    exact: EGET.

  - move=> a v SUB.
    have G := proj1 (aone_sub_noalloc a v m3) SUB.
    change (get m3 (Imp.Addr.block a) (N.to_nat (offset a)) = Some v) in G.
    rewrite Gm3 in G.
    move: G.
    case Eb: (Nat.eqb (S (Imp.Addr.block a)) (nblocks (MLive m))) => //.
    move=> _.
    move/Nat.eqb_eq in Eb; lia.

  - move=> a v SUB.
    have G := proj1 (aone_sub_noalloc a v mp) SUB.
    change (get mp (Imp.Addr.block a) (N.to_nat (offset a)) = Some v) in G.
    rewrite MG in G.
    move: G.
    case Eb: (Nat.eqb (S (Imp.Addr.block a)) (nblocks (MLive m))) => //.
    move=> G.
    have NE: S (Imp.Addr.block a) <> nblocks (MLive m).
    { by move/Nat.eqb_neq in Eb. }
    have LT: Imp.Addr.block a < nblocks (MLive m).
    { case El: (Nat.ltb (Imp.Addr.block a) (nblocks (MLive m))).
      - by move/Nat.ltb_lt in El.
      - exfalso.
        move/Nat.ltb_ge in El.
        rewrite (get_nblocks_ge (MLive m) (Imp.Addr.block a) (N.to_nat (offset a)) El) in G.
        discriminate G. }
    lia.
Qed.

HB.instance Definition _ :=
  isStore.Build Addr.t Pointer.t (value Pointer.t) (mem unit)
    nat_cnt
    list_store_push
    (mpop (A:=unit))
    list_store_push_some
    list_store_push_mem
    list_store_push_cnt
    list_store_push_det
    list_store_pop_emp
    list_store_pop_some
    list_store_pop_mem.
