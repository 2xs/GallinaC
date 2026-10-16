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

From Stdlib Require Import Lia NArith.

From GallinaC.Utils Require Import ListExt OptionExt.
From GallinaC.Imp Require Import Store State.
From GallinaC.Seplog Require Import Pred.
From GallinaC.Seplog.Exists Require Import Exists.
From GallinaC.Seplog.Emp Require Import Emp.
From GallinaC.Seplog.Lift Require Import Lift.
From GallinaC.Seplog.Precise Require Import Precise.
From GallinaC.Seplog.Star Require Import Star.
From GallinaC.Seplog.Upclose Require Import Upclose.
From GallinaC.Seplog.IterStar Require Import IterStar.
From GallinaC.Seplog.State Require Import EmpHeap.
From GallinaC.Seplog.Indep Require Import Indep Facts.

Local Open Scope mem_scope.
Local Open Scope separation_scope.

Section Atoms.

  Context [Sm: State.type].
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation Hp := (@m_hp Sm).

  Definition own_scnt (c: SCnt Sm): Pred Sm :=
    fun s => store s = $0 /\ scnt s = c /\ heap s = $0 /\ alc s = $0.

  Lemma indep_heap_upclose_own_scnt (c: SCnt Sm): indep_heap (upclose (own_scnt c)).
  Proof using Type.
    apply: indep_heap_upclose => s [ _ [ _ [ EQhp EQalc ] ] ].
    by split.
  Qed.

  Lemma precise_own_scnt (c: SCnt Sm): precise (own_scnt c).
  Proof using Type.
    move=> s s1 s2 [ EQst1 [ EQsg1 [ EQhp1 EQalc1 ] ] ] [ EQst2 [ EQsg2 [ EQhp2 EQalc2 ] ] ] _ _.
    by apply: state_ext; congruence.
  Qed.

  Definition own_alc (c: Alc Sm): Pred Sm :=
    fun s => store s = $0 /\ scnt s = $0 /\ heap s = $0 /\ alc s = c.

  Lemma indep_cnt_upclose_own_alc (c: Alc Sm): indep_cnt (upclose (own_alc c)).
  Proof using Type.
    apply: indep_cnt_upclose => s [ _ [ EQsg _ ] ].
    exact: EQsg.
  Qed.

  Lemma indep_store_upclose_own_alc (c: Alc Sm): indep_store (upclose (own_alc c)).
  Proof using Type.
    apply: indep_store_upclose => s [ EQst [ EQsg _ ] ].
    by split.
  Qed.

  Lemma precise_own_alc (c: Alc Sm): precise (own_alc c).
  Proof using Type.
    move=> s s1 s2 [ EQst1 [ EQsg1 [ EQhp1 EQalc1 ] ] ] [ EQst2 [ EQsg2 [ EQhp2 EQalc2 ] ] ] _ _.
    by apply: state_ext; congruence.
  Qed.

  Definition own_heap (h: Hp): Pred Sm :=
    fun s => store s = $0 /\ scnt s = $0 /\ heap s = h /\ alc s = $0.

  Local Notation "a ||~> v" := (own_heap (a |-> v)) (at level 35, no associativity): separation_scope.

  Lemma indep_cnt_upclose_own_heap (h: Hp): indep_cnt (upclose (own_heap h)).
  Proof using Type.
    apply: indep_cnt_upclose => s [ _ [ EQsg _ ] ].
    exact: EQsg.
  Qed.

  Lemma indep_store_upclose_own_heap (h: Hp): indep_store (upclose (own_heap h)).
  Proof using Type.
    apply: indep_store_upclose => s [ EQst [ EQsg _ ] ].
    by split.
  Qed.

  Lemma precise_own_heap (h: Hp): precise (own_heap h).
  Proof using Type.
    move=> s s1 s2 [ EQst1 [ EQsg1 [ EQhp1 EQalc1 ] ] ] [ EQst2 [ EQsg2 [ EQhp2 EQalc2 ] ] ] _ _.
    by apply: state_ext; congruence.
  Qed.

  Lemma iter_star_own_heap_intro (b k n: nat) (v: Vl) (s: Sm)
    (EQst: store s = $0) (EQsg: scnt s = $0) (EQalc: alc s = $0)
    (CHAR: forall (a: Ad) (w: Vl), (((a |-> w): Hp) $<= heap s) <->
             (block a = b /\ (N.of_nat k <= offset a < N.of_nat (k + n))%N) /\ w = v)
    : (Iter o in seq k n, mkAddr b (N.of_nat o) ||~> v) s.
  Proof using Type.
    elim: n k s EQst EQsg EQalc CHAR => [ | n IH ] k s EQst EQsg EQalc CHAR /=.
    - rewrite /Emp.
      apply: state_ext; rewrite ?store_emp ?scnt_emp ?alc_emp ?heap_emp //.
      apply: mem_ext => a w.
      split => SUB; last by case: (emp_no_sub a w SUB).
      case: (proj1 (CHAR a w) SUB) => [ [ _ RNG ] _ ].
      lia.
    - set a0 := mkAddr b (N.of_nat k).
      have SUB0: ((a0 |-> v): Hp) $<= heap s.
      { apply/CHAR.
        rewrite /a0 mkAddr_block mkAddr_offset.
        split; last by [].
        split; first by [].
        lia. }
      case: SUB0 => h2 EQhp.
      exists (mk_state $0 $0 (a0 |-> v) $0 (dominates_emp_cnt _) (dominates_emp_cnt _)),
        (mk_state $0 $0 h2 $0 (dominates_emp_cnt _) (dominates_emp_cnt _)).
      split.
      { apply: state_hp_ext_intro.
        - rewrite !store_mk_state EQst.
          exact: op_id_l.
        - rewrite !scnt_mk_state EQsg.
          exact: op_id_l.
        - rewrite !heap_mk_state.
          exact: EQhp.
        - rewrite !alc_mk_state EQalc.
          exact: op_id_l. }
      split.
      { by rewrite /own_heap store_mk_state scnt_mk_state heap_mk_state alc_mk_state. }
      apply: IH.
      + exact: store_mk_state.
      + exact: scnt_mk_state.
      + exact: alc_mk_state.
      + move=> a w.
        rewrite heap_mk_state.
        split.
        * move=> SUB.
          have SUBs: ((a |-> w): Hp) $<= heap s := substate_tran _ _ _ SUB (substate_of_partition_r EQhp).
          case: (proj1 (CHAR a w) SUBs) => [ [ EQb RNG ] EQw ].
          have NE: offset a <> N.of_nat k.
          { move=> EQk.
            apply: (one_sum_not_sub EQhp w).
            have ->: a0 = a by apply: addr_ext; rewrite /a0 ?mkAddr_block ?mkAddr_offset.
            exact: SUB. }
          split; last exact: EQw.
          split; first exact: EQb.
          lia.
        * move=> [ [ EQb RNG ] EQw ].
          have SUBs: ((a |-> w): Hp) $<= heap s.
          { apply/CHAR.
            split; last exact: EQw.
            split; first exact: EQb.
            lia. }
          case: (proj1 (one_discriminate_iff EQhp a w) SUBs) => [ [ EQa _ ] | [ _ SUB2 ] ]; last exact: SUB2.
          move: RNG.
          rewrite EQa /a0 mkAddr_offset.
          lia.
  Qed.

  Lemma iter_star_own_heap_elim (b k n: nat) (s: Sm)
    (CELLS: (Iter o in seq k n, Exists v, mkAddr b (N.of_nat o) ||~> v) s)
    : store s = $0 /\ scnt s = $0 /\ alc s = $0
      /\ forall (a: Ad), (exists w: Vl, ((a |-> w): Hp) $<= heap s) <->
                         (block a = b /\ (N.of_nat k <= offset a < N.of_nat (k + n))%N).
  Proof using Type.
    elim: n k s CELLS => [ | n IH ] k s /=.
    - rewrite /Emp => ->.
      rewrite store_emp scnt_emp alc_emp heap_emp.
      split; first by [].
      split; first by [].
      split; first by [].
      move=> a.
      split.
      + by move=> [ w SUB ]; case: (emp_no_sub a w SUB).
      + move=> [ _ RNG ].
        lia.
    - move=> [ s1 [ s2 [ EQs [ [ v [ EQst1 [ EQsg1 [ EQhp1 EQalc1 ] ] ] ] CELLS2 ] ] ] ].
      case: (IH (S k) s2 CELLS2) => EQst2 [ EQsg2 [ EQalc2 CHAR2 ] ].
      case/state_sum_spec: EQs => EQst [ EQsg [ EQhp EQalc ] ].
      move: EQst1 EQst2 EQst => -> -> EQst.
      move: EQsg1 EQsg2 EQsg => -> -> EQsg.
      move: EQalc1 EQalc2 EQalc => -> -> EQalc.
      move: EQhp1 EQhp => -> EQhp.
      split; first by rewrite -(partition_emp_l EQst).
      split; first by rewrite -(partition_emp_l EQsg).
      split; first by rewrite -(partition_emp_l EQalc).
      move=> a.
      split.
      + move=> [ w SUB ].
        case: (proj1 (sub_sum_split_iff _ _ _ EQhp a w) SUB) => [ SUB1 | SUB2 ].
        * case: (proj1 (sub_one_iff _ _ _ _) SUB1) => EQa _.
          rewrite EQa mkAddr_block mkAddr_offset.
          split; first by [].
          lia.
        * case: (proj1 (CHAR2 a) (ex_intro _ w SUB2)) => EQb RNG.
          split; first exact: EQb.
          lia.
      + move=> [ EQb RNG ].
        case: (N.eq_dec (offset a) (N.of_nat k)) => [ EQk | NE ].
        * exists v.
          have ->: a = mkAddr b (N.of_nat k) by apply: addr_ext; rewrite ?mkAddr_block ?mkAddr_offset.
          exact: (substate_of_partition_l EQhp).
        * have RNG2: (N.of_nat (S k) <= offset a < N.of_nat (S k + n))%N by lia.
          case: (proj2 (CHAR2 a) (conj EQb RNG2)) => w SUB2.
          exists w.
          exact: (substate_tran _ _ _ SUB2 (substate_of_partition_r EQhp)).
  Qed.

  Lemma own_heap_emp: |- own_heap $0 <==> $$0.
  Proof using Type.
    apply: impl_antisym_taut.
    - move=> s [ EQst [ EQsg [ EQhp EQalc ] ] ].
      rewrite /Emp.
      by apply: state_ext; rewrite ?store_emp ?scnt_emp ?heap_emp ?alc_emp.
    - rewrite /Emp => s ->.
      by rewrite /own_heap store_emp scnt_emp heap_emp alc_emp.
  Qed.

  Lemma own_heap_star (h1 h2: Hp):
    |- own_heap h1 ** own_heap h2 <==> Exists h, [| h1 $+ h2 = Some h |] ** own_heap h.
  Proof using Type.
    apply: impl_antisym_taut.
    - move=> s [ s1 [ s2 [ EQs [ [ EQst1 [ EQsg1 [ EQhp1 EQalc1 ] ] ] [ EQst2 [ EQsg2 [ EQhp2 EQalc2 ] ] ] ] ] ] ].
      case/state_sum_spec: EQs => EQst [ EQsg [ EQhp EQalc ] ].
      move: EQst1 EQst2 EQst => -> -> EQst.
      move: EQsg1 EQsg2 EQsg => -> -> EQsg.
      move: EQhp1 EQhp2 EQhp => -> -> EQhp.
      move: EQalc1 EQalc2 EQalc => -> -> EQalc.
      exists (heap s), $0, s.
      split; first exact: op_id_l.
      split; first by split.
      split; first by rewrite -(partition_emp_l EQst).
      split; first by rewrite -(partition_emp_l EQsg).
      split; first by [].
      by rewrite -(partition_emp_l EQalc).
    - move=> s [ h [ ? [ s1 [ EQs [ [ EQh EMP ] [ EQst1 [ EQsg1 [ EQhp1 EQalc1 ] ] ] ] ] ] ] ].
      move: EMP EQs => -> /partition_emp_l EQs.
      move: EQs EQst1 EQsg1 EQhp1 EQalc1 => -> EQst EQsg EQhp EQalc.
      exists (mk_state $0 $0 h1 $0 (dominates_emp_cnt _) (dominates_emp_cnt _)),
        (mk_state $0 $0 h2 $0 (dominates_emp_cnt _) (dominates_emp_cnt _)).
      split.
      { apply: state_hp_ext_intro.
        - rewrite !store_mk_state EQst.
          exact: op_id_l.
        - rewrite !scnt_mk_state EQsg.
          exact: op_id_l.
        - rewrite !heap_mk_state EQhp.
          exact: EQh.
        - rewrite !alc_mk_state EQalc.
          exact: op_id_l. }
      by split; rewrite /own_heap store_mk_state scnt_mk_state heap_mk_state alc_mk_state.
  Qed.

  Lemma own_heap_join (h1 h2 h: Hp) (SUM: h1 $+ h2 = Some h):
    |- own_heap h1 ** own_heap h2 <==> own_heap h.
  Proof using Type.
    move=> s.
    rewrite (own_heap_star h1 h2 s).
    split.
    - move=> [ h' [ ? [ s1 [ EQs [ [ EQh' EMP ] HEAP ] ] ] ] ].
      move: EMP EQs => -> /partition_emp_l EQs.
      move: EQs HEAP => -> HEAP.
      by rewrite (Some_congr SUM EQh').
    - move=> HEAP.
      exists h, $0, s.
      split; first exact: op_id_l.
      by split; first by split.
  Qed.

  Definition var_pt (n: Nm) (v: Vl): Pred Sm :=
    fun s => (exists a, References n a /\ store s = (a |-> v)) /\ scnt s = $0 /\ heap s = $0 /\ alc s = $0.

  Lemma indep_cnt_upclose_var_pt (n: Nm) (v: Vl): indep_cnt (upclose (var_pt n v)).
  Proof using Type.
    apply: indep_cnt_upclose => s [ _ [ EQsg _ ] ].
    exact: EQsg.
  Qed.

  Lemma indep_heap_upclose_var_pt (n: Nm) (v: Vl): indep_heap (upclose (var_pt n v)).
  Proof using Type.
    apply: indep_heap_upclose => s [ _ [ _ [ EQhp EQalc ] ] ].
    by split.
  Qed.

  Lemma indep_store_replace_upclose_var_pt (n: Nm) (v: Vl):
    indep_store_replace (upclose (var_pt n v)) [n].
  Proof using Type.
    move=> s1 s2 [ s3 [ s4 [ EQs1 [ VPT _ ] ] ] ] SPE EQsg2 EQhp2 EQalc2.
    case: (VPT) => [ [ a [ REF EQst3 ] ] [ EQsg3 _ ] ].
    case/state_sum_spec: EQs1 => EQst1 [ _ [ EQhp1 EQalc1 ] ].
    have PT1: n |~> v @ store s1.
    { exists a; split; first exact: REF.
      rewrite -EQst3.
      exact: (substate_of_partition_l EQst1). }
    case: (proj1 (SPE n v (or_introl eq_refl)) PT1) => a' [ REF' [ r EQst2 ] ].
    have EQa': a' = a by congruence.
    move: EQa' EQst2 => -> EQst2.
    have DOM: dominates r (scnt s2).
    { apply: (dominates_sub_mem (store s2) r (scnt s2)); last exact: state_store_dominates.
      exact: (substate_of_partition_r EQst2). }
    exists s3, (mk_state r (scnt s2) (heap s4) (alc s4) DOM (state_heap_dominates s4)).
    split; [ | split; [ exact: VPT | exact: I ] ].
    apply/state_sum_spec.
    rewrite store_mk_state scnt_mk_state heap_mk_state alc_mk_state EQst3 EQsg3 EQhp2 EQalc2.
    split; first exact: EQst2.
    split; first exact: (op_id_l _).
    by split.
  Qed.

  Lemma precise_var_pt (n: Nm) (v: Vl): precise (var_pt n v).
  Proof using Type.
    move=> s s1 s2 [ [ a1 [ REF1 EQst1 ] ] [ EQsg1 [ EQhp1 EQalc1 ] ] ] [ [ a2 [ REF2 EQst2 ] ] [ EQsg2 [ EQhp2 EQalc2 ] ] ] _ _.
    have EQa2: a2 = a1 by congruence.
    by apply: state_ext; congruence.
  Qed.

  Definition lift_store (P: Prop): Pred Sm :=
    fun s => P /\ Emp_heap s.

  Lemma indep_cnt_lift_store (p: Prop): indep_cnt (lift_store p).
  Proof using Type.
    by move=> s s' _ EQhp' EQalc' [ HP [ EQhp EQalc ] ]; split; [ | rewrite /Emp_heap -EQhp' -EQalc' ].
  Qed.

  Lemma indep_store_lift_store (P: Prop):
    indep_store (lift_store P).
  Proof using Type.
    move=> s1 s2 EQhp2 EQalc2 [ HP [ EQhp1 EQalc1 ] ].
    split; [ exact: HP | ].
    by split; [ rewrite -EQhp2 | rewrite -EQalc2 ].
  Qed.

  Lemma indep_store_replace_lift_store (p: Prop):
    indep_store_replace (lift_store p: Pred Sm) [].
  Proof using Type.
    move=> s1 s2 [ HP [ EQhp1 EQalc1 ] ] _ _ EQhp2 EQalc2.
    by split; [ | split; [ rewrite EQhp2 | rewrite EQalc2 ] ].
  Qed.

End Atoms.

Arguments own_heap_emp {Sm}.

Notation "a ||~> v" := (own_heap (a |-> v)) (at level 35, no associativity): separation_scope.

#[global] Hint Resolve indep_heap_upclose_own_scnt indep_cnt_upclose_own_alc
  indep_cnt_upclose_var_pt indep_heap_upclose_var_pt
  precise_own_scnt precise_own_alc precise_var_pt : seplog.
#[global] Hint Resolve indep_store_upclose_own_alc : seplog seplog_search.
#[global] Hint Resolve indep_store_replace_upclose_var_pt : seplog_search.
#[global] Hint Resolve indep_heap_upclose_own_scnt indep_heap_upclose_var_pt : seplog_search.
#[global] Hint Resolve indep_cnt_upclose_own_heap precise_own_heap : seplog.
#[global] Hint Resolve indep_store_upclose_own_heap : seplog seplog_search.
#[global] Hint Resolve indep_cnt_lift_store : seplog.
#[global] Hint Resolve indep_store_lift_store : seplog seplog_search.
#[global] Hint Resolve indep_store_replace_lift_store : seplog_search.
