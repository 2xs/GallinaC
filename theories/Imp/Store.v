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

From HB Require Import structures.
From Stdlib Require Import Arith NArith Lia List.
Import ListNotations.
Require Import ssr.ssreflect.

From GallinaC.Utils Require ListExt NExt.
From GallinaC.Utils Require Export Algebra Counter.
From GallinaC.Imp Require Export RWMemory.

Local Open Scope separation_scope.
Local Open Scope mem_scope.

Declare Scope store_scope.
Delimit Scope store_scope with store.

HB.mixin Record isStore (Ad: Addr.type) (Nm: Ref.type Ad) (Vl: Type)
  T of RWMemory Ad Nm Vl T :=
  {
    store_cnt: Counter.type;

    push: T -> excl store_cnt -> Vl -> option (T * excl store_cnt * Nm);
    pop: T -> option T;

    push_some: forall s c v,
        (exists nm, cget c = Some nm
                    /\ forall o v', ~ ((mkAddr nm o) |-> v' $<= s))
        <-> exists s' c' n, push s c v = Some (s', c', n);
    push_mem: forall s c v s' c' n nm,
        push s c v = Some (s', c', n) -> cget c = Some nm ->
          References n (mkAddr nm 0%N)
          /\ Allows n Operation.Write
          /\ ((mkAddr nm 0%N) |-> v) $+ s = Some s';
    push_cnt: forall s c v s' c' n,
        push s c v = Some (s', c', n) -> c' = cnext c;
    push_det: forall s1 s2 c v1 v2 s1' s2' c1' c2' n1 n2,
        push s1 c v1 = Some (s1', c1', n1) ->
        push s2 c v2 = Some (s2', c2', n2) -> n1 = n2;

    pop_emp: pop $0 = None;
    pop_some: forall s (NEMP: s <> $0), exists s', pop s = Some s';
    pop_mem: forall s s' (EQ: pop s = Some s'),
        exists bl bi,
          s' $+ bl = Some s
          /\ (exists a v, (a |-> v) $<= bl)
          /\ (forall a v, (a |-> v) $<= bl -> block a = bi)
          /\ (forall a v, (a |-> v) $<= s' -> block a < bi);
  }.
HB.structure Definition Store (Ad: Addr.type) (Nm: Ref.type Ad) (Vl: Type) :=
  { T of RWMemory Ad Nm Vl T & hasBlockBound Ad Vl T & isStore Ad Nm Vl T }.

#[global] Hint Resolve push_mem push_cnt push_det
  pop_emp pop_some pop_mem: seplog.
#[global] Hint Resolve -> push_some: seplog.
#[global] Hint Resolve <- push_some: seplog.
#[global] Hint Rewrite @pop_emp: seplog.

Lemma push_fresh [Ad: Addr.type] [Nm: Ref.type Ad] [Vl] [St: Store.type Ad Nm Vl]
  (s s': St) (c c': excl (@store_cnt Ad Nm Vl St)) (v: Vl) (n: Nm)
  (EQ: push s c v = Some (s', c', n))
  : lookup s n = None.
Proof.
  case: (proj2 (push_some s c v) (ex_intro _ s' (ex_intro _ c' (ex_intro _ n EQ))))
    => nm [GET _].
  case: (push_mem s c v s' c' n nm EQ GET) => REF [ALW SUM].
  case E: (lookup s n) => [v'|] //.
  exfalso.
  case: (proj2 (lookup_iff s n v') E) => a' [REF' [_ SUB]].
  rewrite REF in REF'; case: REF' => ?; subst a'.
  by rewrite (proj1 (one_similar _ v s) (ex_intro _ v' SUB)) in SUM.
Qed.
#[global] Hint Resolve push_fresh: seplog.

Lemma push_lookup_fresh [Ad: Addr.type] [Nm: Ref.type Ad] [Vl] [St: Store.type Ad Nm Vl]
  (s s': St) (c c': excl (@store_cnt Ad Nm Vl St)) (v: Vl) (n: Nm)
  (EQ: push s c v = Some (s', c', n))
  : lookup s' n = Some v.
Proof.
  case: (proj2 (push_some s c v) (ex_intro _ s' (ex_intro _ c' (ex_intro _ n EQ))))
    => nm [GET _].
  case: (push_mem s c v s' c' n nm EQ GET) => REF [ALW SUM].
  apply (proj1 (lookup_iff s' n v)).
  exists (mkAddr nm 0%N); split; [exact: REF | split].
  - exact: (allows_le n Operation.Read Operation.Write Operation.le_read_write ALW).
  - exact: (substate_of_partition_l SUM).
Qed.
#[global] Hint Resolve push_lookup_fresh: seplog.

Lemma push_lookup_old [Ad: Addr.type] [Nm: Ref.type Ad] [Vl] [St: Store.type Ad Nm Vl]
  (s s': St) (c c': excl (@store_cnt Ad Nm Vl St)) (v: Vl) (n: Nm) (a0: Ad)
  (EQ: push s c v = Some (s', c', n))
  (REF: References n a0)
  a (NE: a <> a0) w
  : (a |-> w) $<= s' <-> (a |-> w) $<= s.
Proof.
  case: (proj2 (push_some s c v) (ex_intro _ s' (ex_intro _ c' (ex_intro _ n EQ))))
    => nm [GET _].
  case: (push_mem s c v s' c' n nm EQ GET) => REF0 [_ SUM].
  have Ea0: a0 = mkAddr nm 0%N by congruence.
  split.
  - move=> SUB.
    case: (one_discriminate SUM a w SUB) => [[Ea _]|[_ SUBs]]; last exact: SUBs.
    by case: NE; rewrite Ea Ea0.
  - move=> SUB.
    exact: (substate_tran _ _ _ SUB (substate_of_partition_r SUM)).
Qed.
#[global] Hint Resolve -> push_lookup_old: seplog.
#[global] Hint Resolve <- push_lookup_old: seplog.

Lemma dominates_push [Ad: Addr.type] [Nm: Ref.type Ad] [Vl] [St: Store.type Ad Nm Vl]
  (s s': St) (c c': excl (@store_cnt Ad Nm Vl St)) (v: Vl) (n: Nm)
  (EQ: push s c v = Some (s', c', n)) (DOM: dominates s c)
  : dominates s' c'.
Proof.
  move=> a1 v1 id1 SUBa EQg.
  rewrite (push_cnt s c v s' c' n EQ) in EQg.
  case: (cget_next_bw_some c id1 EQg) => nm EQ0.
  have LT: nm < id1 := cnext_lt c nm id1 EQ0 EQg.
  case: (push_mem s c v s' c' n nm EQ EQ0) => _ [_ SUM].
  case: (one_discriminate SUM a1 v1 SUBa) => [[-> _]|[_ SUBs]].
  - rewrite mkAddr_block; exact: LT.
  - have := DOM a1 v1 nm SUBs EQ0. lia.
Qed.
#[global] Hint Resolve dominates_push: seplog.

Lemma dominates_pop [Ad: Addr.type] [Nm: Ref.type Ad] [Vl] [St: Store.type Ad Nm Vl]
  (s s': St) (c: excl (@store_cnt Ad Nm Vl St))
  (EQ: pop s = Some s') (DOM: dominates s c)
  : dominates s' c.
Proof.
  case: (pop_mem s s' EQ) => bl [bi [SUM _]].
  exact: (dominates_sub_mem s s' c (substate_of_partition_l SUM) DOM).
Qed.
#[global] Hint Resolve dominates_pop: seplog.

Lemma pop_sub [Ad: Addr.type] [Nm: Ref.type Ad] [Vl] [St: Store.type Ad Nm Vl]
  [s s': St] (POP: pop s = Some s'):
  s' $<= s.
Proof.
  destruct (pop_mem s s' POP) as ( bl & bi & SUM & _ ).
  exact (substate_of_partition_l SUM).
Qed.

Lemma dominates_iter_opt_pop [Ad: Addr.type] [Nm: Ref.type Ad] [Vl]
  [St: Store.type Ad Nm Vl]
  (n: N) (s s': St) (c: excl (@store_cnt Ad Nm Vl St))
  (POP: NExt.iter_opt (fun x => pop x) n s = Some s')
  (DOM: dominates s c):
  dominates s' c.
Proof.
  revert s' POP.
  induction n as [ | n IH ] using N.peano_ind; intros s' POP.
  - rewrite NExt.iter_opt_0 in POP; injection POP as <-; exact DOM.
  - rewrite NExt.iter_opt_succ in POP.
    destruct (NExt.iter_opt (fun x => pop x) n s) as [ s0 | ] eqn:E;
      [ | discriminate POP ].
    exact (dominates_pop s0 s' c POP (IH _ eq_refl)).
Qed.

Lemma push_of_dominates [Ad: Addr.type] [Nm: Ref.type Ad] [Vl]
  [St: Store.type Ad Nm Vl]
  [s: St] [c: excl (@store_cnt Ad Nm Vl St)] [k: nat] (v: Vl)
  (CGET: cget c = Some k) (DOM: dominates s c):
  exists s' c' n, push s c v = Some (s', c', n).
Proof.
  apply (proj1 (push_some s c v)).
  exists k; split; [ exact CGET | ].
  intros o v' SUB.
  pose proof (DOM _ _ _ SUB CGET) as LTB.
  rewrite mkAddr_block in LTB; lia.
Qed.

Lemma push_sub [Ad: Addr.type] [Nm: Ref.type Ad] [Vl] [St: Store.type Ad Nm Vl]
  [st_s st_t st_s': St] [c c': excl (@store_cnt Ad Nm Vl St)] [v: Vl] [nm: Nm]
  (SUB: st_t $<= st_s)
  (PUSH: push st_s c v = Some (st_s', c', nm)):
  exists st_t', push st_t c v = Some (st_t', c', nm) /\ st_t' $<= st_s'.
Proof.
  destruct (proj2 (push_some st_s c v)
              (ex_intro _ st_s' (ex_intro _ c' (ex_intro _ nm PUSH))))
    as ( k & CGET & FRESH ).
  destruct (proj1 (push_some st_t c v)) as ( st_t' & c_t' & nm_t & PUSHT ).
  { exists k; split; [ exact CGET | ].
    intros o v' CELL.
    exact (FRESH o v' (substate_tran _ _ _ CELL SUB)). }
  assert (ECNT: c_t' = c')
    by (rewrite (push_cnt _ _ _ _ _ _ PUSHT) (push_cnt _ _ _ _ _ _ PUSH); reflexivity).
  assert (ENM: nm_t = nm) by exact (push_det _ _ _ _ _ _ _ _ _ _ _ PUSHT PUSH).
  subst c_t' nm_t.
  exists st_t'; split; [ exact PUSHT | ].
  destruct (push_mem _ _ _ _ _ _ _ PUSH CGET) as ( _ & _ & SUMS ).
  destruct (push_mem _ _ _ _ _ _ _ PUSHT CGET) as ( _ & _ & SUMT ).
  destruct SUB as ( d & SUMD ).
  pose proof (eq_trans (op_comm st_s (((mkAddr k 0%N) |-> v): St)) SUMS) as SUMS'.
  pose proof (eq_trans (op_comm st_t (((mkAddr k 0%N) |-> v): St)) SUMT) as SUMT'.
  destruct (op_swap _ _ _ _ _ SUMD SUMS') as ( u & SUMU & SUMUD ).
  pose proof (eq_trans (eq_sym SUMU) SUMT') as EU.
  injection EU as EU; subst u.
  by exists d.
Qed.

Lemma pop_char [Ad: Addr.type] [Nm: Ref.type Ad] [Vl] [St: Store.type Ad Nm Vl]
  (s s' bl: St) (bi: nat)
  (SUM: s' $+ bl = Some s)
  (NE: exists a v, (a |-> v) $<= bl)
  (BLK: forall a v, (a |-> v) $<= bl -> block a = bi)
  (LT: forall a v, (a |-> v) $<= s' -> block a < bi)
  : pop s = Some s'.
Proof.
  case: NE => a1 [v1 SUB1].
  have SUB1s: (a1 |-> v1) $<= s
    := substate_tran _ _ _ SUB1 (substate_of_partition_r SUM).
  case: (pop_some s (sub_one_neq_emp s a1 v1 SUB1s)) => t POP.
  case: (pop_mem s t POP) => bl2 [bi2 [SUM2 [NE2 [BLK2 LT2]]]].
  case: NE2 => a2 [v2 SUB2].
  have SUB2s: (a2 |-> v2) $<= s
    := substate_tran _ _ _ SUB2 (substate_of_partition_r SUM2).
  have LE12: (bi <= bi2)%nat.
  { rewrite -(BLK _ _ SUB1).
    case: (proj1 (sub_sum_split_iff t bl2 s SUM2 a1 v1) SUB1s) => [X|X].
    - have := LT2 _ _ X; lia.
    - rewrite (BLK2 _ _ X); lia. }
  have LE21: (bi2 <= bi)%nat.
  { rewrite -(BLK2 _ _ SUB2).
    case: (proj1 (sub_sum_split_iff s' bl s SUM a2 v2) SUB2s) => [X|X].
    - have := LT _ _ X; lia.
    - rewrite (BLK _ _ X); lia. }
  have Ebi: bi2 = bi by lia.
  subst bi2.
  have EBL: bl2 = bl.
  { apply: mem_ext => a w; split.
    - move=> SUBx.
      have SUBs: (a |-> w) $<= s
        := substate_tran _ _ _ SUBx (substate_of_partition_r SUM2).
      case: (proj1 (sub_sum_split_iff s' bl s SUM a w) SUBs) => [X|X] //.
      exfalso; have := LT _ _ X; rewrite (BLK2 _ _ SUBx); lia.
    - move=> SUBx.
      have SUBs: (a |-> w) $<= s
        := substate_tran _ _ _ SUBx (substate_of_partition_r SUM).
      case: (proj1 (sub_sum_split_iff t bl2 s SUM2 a w) SUBs) => [X|X] //.
      exfalso; have := LT2 _ _ X; rewrite (BLK _ _ SUBx); lia. }
  subst bl2.
  rewrite POP; congr Some.
  exact: (op_cancel_r bl t s' s SUM2 SUM).
Qed.

Lemma push_pop [Ad: Addr.type] [Nm: Ref.type Ad] [Vl] [St: Store.type Ad Nm Vl]
  (s s': St) (c c': excl (@store_cnt Ad Nm Vl St)) (v: Vl) (n: Nm)
  (EQ: push s c v = Some (s', c', n))
  (DOM: dominates s c)
  : pop s' = Some s.
Proof.
  case: (proj2 (push_some s c v) (ex_intro _ s' (ex_intro _ c' (ex_intro _ n EQ))))
    => nm [GET _].
  case: (push_mem s c v s' c' n nm EQ GET) => _ [_ PUSH].
  pose a0: Ad := mkAddr nm 0%N.
  have BLKa0: block a0 = nm by rewrite /a0 mkAddr_block.
  have DOM': forall a w, (a |-> w) $<= s -> block a < nm
    by move=> a w SUB; exact: (DOM a w nm SUB GET).
  have SUB0: (a0 |-> v) $<= s' := substate_of_partition_l PUSH.
  case: (pop_some s' (sub_one_neq_emp s' a0 v SUB0)) => s'' POP.
  case: (pop_mem s' s'' POP) => bl [bi [SUM [NE [BLK LT]]]].
  have ONLY: forall a w, (a |-> w) $<= bl -> a = a0 /\ w = v.
  { move=> a w SUBbl.
    have SUBs': (a |-> w) $<= s'
      := substate_tran _ _ _ SUBbl (substate_of_partition_r SUM).
    case: (one_discriminate PUSH a w SUBs') => [[-> ->]|[NE0 SUBs]];
      [ by split | ].
    exfalso.
    have LTa := DOM' _ _ SUBs.
    have Eabi := BLK _ _ SUBbl.
    case: (proj1 (sub_sum_split_iff s'' bl s' SUM a0 v) SUB0) => [X|X].
    - have := LT _ _ X; rewrite BLKa0 -Eabi; lia.
    - have := BLK _ _ X; rewrite BLKa0 -Eabi; lia. }
  have Ebi: bi = nm.
  { case: NE => a1 [w1 SUBbl1].
    have Ea1 := BLK _ _ SUBbl1.
    case: (ONLY _ _ SUBbl1) => Ea _.
    rewrite Ea BLKa0 in Ea1.
    by rewrite -Ea1. }
  have IN0: (a0 |-> v) $<= bl.
  { case: (proj1 (sub_sum_split_iff s'' bl s' SUM a0 v) SUB0) => [X|X].
    - exfalso; have := LT _ _ X; rewrite BLKa0 Ebi; lia.
    - exact: X. }
  have EBL: bl = (a0 |-> v).
  { apply: mem_ext => a w; split.
    - move=> SUBbl.
      case: (ONLY _ _ SUBbl) => -> ->.
      exact: substate_refl.
    - move=> SUBone.
      case: (proj1 (sub_one_iff a0 a v w) SUBone) => -> ->.
      exact: IN0. }
  rewrite EBL in SUM.
  have PUSH': s $+ (a0 |-> v) = Some s'.
  { have C := op_comm (a0 |-> v) s. by rewrite -C. }
  rewrite POP.
  congr Some.
  exact: (op_cancel_r (a0 |-> v) s'' s s' SUM PUSH').
Qed.
#[global] Hint Resolve push_pop: seplog.

Section Layered.

  Context [Ad: Addr.type] [Nm: Ref.type Ad] [Vl: Type] [St: Store.type Ad Nm Vl].

  Inductive layered (base: St): list Nm -> St -> Prop :=
  | layered_nil:
    layered base [] base
  | layered_snoc: forall nms (st: St) (nm: Nm) (a: Ad) (v: Vl) (st': St)
                         (LOW: layered base nms st)
                         (REF: References nm a)
                         (WRT: Allows nm Operation.Write)
                         (BLK: forall a' v', (a' |-> v') $<= st -> (block a' < block a)%nat)
                         (SUM: (a |-> v) $+ st = Some st'),
      layered base (nms ++ [nm]) st'.

  Lemma layered_sub [base nms st] (LAYERED: layered base nms st): base $<= st.
  Proof using Type.
    induction LAYERED as [ | nms st nm a v st' LOW IH REF WRT BLK SUM ].
    - exact (substate_refl _).
    - exact (substate_tran _ _ _ IH (substate_of_partition_r SUM)).
  Qed.

  Lemma layered_nth [base nms st] (LAYERED: layered base nms st):
    forall n nm (NTH: List.nth_error nms n = Some nm),
    exists a v, References nm a /\ Allows nm Operation.Write /\ (a |-> v) $<= st.
  Proof using Type.
    induction LAYERED as [ | nms st nm0 a0 v0 st' LOW IH REF0 WRT0 BLK0 SUM0 ];
      intros n nm NTH.
    - destruct n; discriminate.
    - destruct (ListExt.nth_error_snoc_inv NTH) as [ INl | ( ELEN & ENM ) ].
      + destruct (IH n nm INl) as ( a & v & REF & WRT & CELL ).
        exists a, v; split; [ exact REF | split; [ exact WRT | ] ].
        exact (substate_tran _ _ _ CELL (substate_of_partition_r SUM0)).
      + subst nm.
        exists a0, v0; split; [ exact REF0 | split; [ exact WRT0 | ] ].
        exact (substate_of_partition_l SUM0).
  Qed.

  Lemma layered_block_lt [base nms st] (LAYERED: layered base nms st):
    forall n1 nm1 a1 n2 nm2 a2
           (NTH1: List.nth_error nms n1 = Some nm1) (REF1: References nm1 a1)
           (NTH2: List.nth_error nms n2 = Some nm2) (REF2: References nm2 a2)
           (LT: (n1 < n2)%nat),
      (block a1 < block a2)%nat.
  Proof using Type.
    induction LAYERED as [ | nms st nm0 a0 v0 st' LOW IH REF0 WRT0 BLK0 SUM0 ];
      intros n1 nm1 a1 n2 nm2 a2 NTH1 REF1 NTH2 REF2 LT.
    - destruct n1; discriminate.
    - destruct (ListExt.nth_error_snoc_inv NTH2) as [ IN2 | ( ELEN2 & ENM2 ) ].
      + assert (LT2: (n2 < List.length nms)%nat)
          by (apply (proj1 (List.nth_error_Some _ _)); rewrite IN2; discriminate).
        destruct (ListExt.nth_error_snoc_inv NTH1) as [ IN1 | ( ELEN1 & _ ) ];
          [ exact (IH n1 nm1 a1 n2 nm2 a2 IN1 REF1 IN2 REF2 LT) | lia ].
      + subst nm2.
        assert (EAD: a2 = a0) by congruence; subst a2.
        destruct (ListExt.nth_error_snoc_inv NTH1) as [ IN1 | ( ELEN1 & _ ) ];
          [ | lia ].
        destruct (layered_nth LOW n1 nm1 IN1) as ( a & v & REF & _ & CELL ).
        assert (EAD1: a = a1) by congruence; subst a.
        exact (BLK0 _ _ CELL).
  Qed.

  Lemma layered_addr_neq [base nms st] (LAYERED: layered base nms st)
    [n1 nm1 a1 n2 nm2 a2]
    (NTH1: List.nth_error nms n1 = Some nm1) (REF1: References nm1 a1)
    (NTH2: List.nth_error nms n2 = Some nm2) (REF2: References nm2 a2)
    (NE: n1 <> n2):
    a1 <> a2.
  Proof using Type.
    intros EAD; subst a2.
    destruct (Nat.lt_trichotomy n1 n2) as [ LT | [ EPOS | GT ] ].
    - pose proof (layered_block_lt LAYERED n1 nm1 a1 n2 nm2 a1 NTH1 REF1 NTH2 REF2 LT)
        as LTb; lia.
    - exact (NE EPOS).
    - pose proof (layered_block_lt LAYERED n2 nm2 a1 n1 nm1 a1 NTH2 REF2 NTH1 REF1 GT)
        as LTb; lia.
  Qed.

  Lemma layered_base_addr_neq [base: St] [nms: list Nm] [st: St]
    (LAYERED: layered base nms st)
    [a': Ad] [w: Vl] (CELL: (((a' |-> w)%mem) $<= base)%sep)
    [n nm a] (NTH: List.nth_error nms n = Some nm) (REF: References nm a)
    : a' <> a.
  Proof using Type.
    revert n nm a NTH REF.
    induction LAYERED as [ | nms st nm0 a0 v0 st' LOW IH REF0 WRT0 BLK0 SUM0 ];
      intros n nm a NTH REF.
    - destruct n; discriminate.
    - destruct (ListExt.nth_error_snoc_inv NTH) as [ INl | ( ELEN & ENM ) ].
      + exact (IH n nm a INl REF).
      + subst nm.
        assert (EA: a = a0) by congruence; subst a.
        intros EQ; subst a'.
        specialize (BLK0 a0 w (substate_tran _ _ _ CELL (layered_sub LOW))); lia.
  Qed.

  Lemma layered_replace [base nms st] (LAYERED: layered base nms st):
    forall n nm (NTH: List.nth_error nms n = Some nm) (mv: Vl),
    exists st', mutate st nm mv = Some st' /\ layered base nms st'.
  Proof using Type.
    induction LAYERED as [ | nms st nm0 a0 v0 st' LOW IH REF0 WRT0 BLK0 SUM0 ];
      intros n nm NTH mv.
    - destruct n; discriminate.
    - destruct (ListExt.nth_error_snoc_inv NTH) as [ INl | ( ELEN & ENM ) ].
      + destruct (IH n nm INl mv) as ( st1 & MUT1 & LAYERED1 ).
        assert (SUM1: st $+ (a0 |-> v0) = Some st')
          by exact (eq_trans (op_comm st ((a0 |-> v0): St)) SUM0).
        destruct (mutate_partition SUM1 MUT1) as ( st2 & MUT2 & SUM2 ).
        exists st2; split; [ exact MUT2 | ].
        refine (layered_snoc base nms st1 nm0 a0 v0 st2 LAYERED1 REF0 WRT0 _ _).
        * intros a' v' CELL.
          destruct (mutate_dom_bw st st1 nm mv MUT1 a' v' CELL) as ( v'' & CELL' ).
          exact (BLK0 _ _ CELL').
        * exact (eq_trans (op_comm ((a0 |-> v0): St) st1) SUM2).
      + subst nm.
        destruct (mutate_partition SUM0 (mutate_one REF0 WRT0 v0 mv))
          as ( st2 & MUT2 & SUM2 ).
        exists st2; split; [ exact MUT2 | ].
        exact (layered_snoc base nms st nm0 a0 mv st2 LOW REF0 WRT0 BLK0 SUM2).
  Qed.

  Lemma layered_mutate [base nms st] (LAYERED: layered base nms st)
    [n nm] (NTH: List.nth_error nms n = Some nm) [mv: Vl] [st']
    (MUTATE: mutate st nm mv = Some st')
    : layered base nms st'.
  Proof using Type.
    destruct (layered_replace LAYERED n nm NTH mv) as ( st2 & MUT2 & LAYERED2 ).
    assert (EST: st2 = st') by congruence; subst st2.
    exact LAYERED2.
  Qed.

  Lemma layered_nil_inv [base nms st] (LAYERED: layered base nms st):
    nms = [] -> st = base.
  Proof using Type.
    destruct LAYERED as [ | nms0 st0 nm a v st' LOW REF WRT BLK SUM ]; intros ENIL.
    - reflexivity.
    - exfalso; exact (app_cons_not_nil nms0 [] nm (eq_sym ENIL)).
  Qed.

  Lemma layered_pop [base nms0 st] (LAYERED: layered base nms0 st):
    forall nms nm (EQsnoc: nms0 = nms ++ [nm]),
    exists st', pop st = Some st' /\ layered base nms st'.
  Proof using Type.
    destruct LAYERED as [ | nms1 st1 nm1 a v st' LOW REF WRT BLK SUM ];
      intros nms nm EQsnoc.
    - exfalso; exact (app_cons_not_nil nms [] nm EQsnoc).
    - destruct (app_inj_tail nms1 nms nm1 nm EQsnoc) as ( ENMS & ENM ).
      subst nms1 nm1.
      exists st1; split; [ | exact LOW ].
      apply (pop_char st' st1 ((a |-> v): St) (block a)).
      + exact (eq_trans (op_comm st1 ((a |-> v): St)) SUM).
      + exists a, v; exact (substate_refl _).
      + intros a' v' SUB.
        destruct (proj1 (sub_one_iff a a' v v') SUB) as ( EAD & _ ); subst a'.
        reflexivity.
      + exact BLK.
  Qed.

  Lemma layered_pop_n [base: St]:
    forall n nms (st: St) (LAYERED: layered base nms st)
           (LE: (n <= List.length nms)%nat),
    exists st',
      NExt.iter_opt (fun st => pop st) (N.of_nat n) st = Some st'
      /\ layered base (ListExt.removelast_n n nms) st'
      /\ st' $<= st.
  Proof using Type.
    induction n as [ | n IH ]; intros nms st LAYERED LE.
    - exists st; split; [ exact (NExt.iter_opt_0 _ _) | split; [ exact LAYERED | ] ].
      exact (substate_refl _).
    - assert (NENIL: nms <> []) by (intros ENIL; subst nms; cbn in LE; lia).
      destruct (exists_last NENIL) as ( nms' & ( nm & EQsnoc ) ).
      destruct (layered_pop LAYERED nms' nm EQsnoc) as ( st1 & POP & LAYERED1 ).
      assert (LE1: (n <= List.length nms')%nat).
      { rewrite EQsnoc in LE; rewrite length_app in LE;
        cbn [List.length] in LE; lia. }
      destruct (IH nms' st1 LAYERED1 LE1) as ( st' & POPn & LAYERED' & SUB' ).
      exists st'; split; [ | split ].
      + by rewrite Nat2N.inj_succ NExt.iter_opt_succ_r POP.
      + by rewrite EQsnoc ListExt.removelast_n_snoc.
      + exact (substate_tran _ _ _ SUB' (pop_sub POP)).
  Qed.

  Lemma layered_pop_all [base: St] [nms st] (LAYERED: layered base nms st):
    NExt.iter_opt (fun st => pop st) (N.of_nat (List.length nms)) st = Some base.
  Proof using Type.
    destruct (layered_pop_n (List.length nms) nms st LAYERED (Nat.le_refl _))
      as ( st' & POP & LAYERED' & _ ).
    rewrite POP; f_equal.
    exact (layered_nil_inv LAYERED' (ListExt.removelast_n_app_length [] nms)).
  Qed.

End Layered.
