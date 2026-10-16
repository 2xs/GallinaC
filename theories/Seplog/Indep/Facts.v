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

From GallinaC.Utils Require Import ListExt.
From GallinaC.Imp Require Import Store State.
From GallinaC.Seplog Require Import Pred.
From GallinaC.Seplog.Inter Require Import Inter.
From GallinaC.Seplog.Exists Require Import Exists.
From GallinaC.Seplog.Lift Require Import Lift.
From GallinaC.Seplog.Star Require Import Star.
From GallinaC.Seplog.Upclose Require Import Upclose.
From GallinaC.Seplog.ConjOverlap Require Import ConjOverlap.
From GallinaC.Seplog.State Require Import EmpHeap.
From GallinaC.Seplog.Indep Require Import Indep.
From GallinaC.Seplog.ConjOverlapStore Require Import ConjOverlapStore Facts.

Local Open Scope separation_scope.
Local Open Scope mem_scope.

Section Facts.

  Context [Sm: State.type].
  Local Notation Nm := (@var_name Sm).

  Lemma indep_store_star (P Q: Pred Sm):
      indep_store P -> indep_store Q -> indep_store (P ** Q).
  Proof using Type.
    move=> INDEPP INDEPQ s s' EQhp' EQalc' [ sp [ sq [ EQs [ Psp Qsq ] ] ] ].
    case/state_sum_spec: EQs => EQst [ EQsg [ EQhp EQalc ] ].
    exists (set_store sp s'), (set_store sq ($0: Sm)).
    split.
    - apply/state_sum_spec; rewrite ?store_set_store ?scnt_set_store ?heap_set_store ?alc_set_store ?store_emp ?scnt_emp ?heap_emp ?alc_emp.
      split; [ exact: (op_id_r _) | ].
      split; [ exact: (op_id_r _) | ].
      split; [ by rewrite EQhp EQhp' | ].
      by rewrite EQalc EQalc'.
    - split.
      + by apply: (INDEPP sp); rewrite ?heap_set_store ?alc_set_store.
      + by apply: (INDEPQ sq); rewrite ?heap_set_store ?alc_set_store.
  Qed.

  Lemma indep_store_upclose (P: Pred Sm) (EMP: forall s, P s -> store s = $0 /\ scnt s = $0):
    indep_store (upclose P).
  Proof using Type.
    move=> s1 s2 EQhp2 EQalc2 [ sp [ s3 [ EQs1 [ Psp _ ] ] ] ].
    case: (EMP sp Psp) => EQstp EQsgp.
    case/state_sum_spec: EQs1 => _ [ _ [ EQhp1 EQalc1 ] ].
    exists sp, (mk_state (store s2) (scnt s2) (heap s3) (alc s3) (state_store_dominates s2) (state_heap_dominates s3)).
    split; [ | split; [ exact: Psp | exact: I ] ].
    apply/state_sum_spec.
    rewrite store_mk_state scnt_mk_state heap_mk_state alc_mk_state EQstp EQsgp -EQhp2 -EQalc2.
    split; first exact: (op_id_l _).
    split; first exact: (op_id_l _).
    by split.
  Qed.

  Lemma indep_store_conj_overlap (P Q: Pred Sm):
    indep_store P -> indep_store Q -> indep_store (P *& Q).
  Proof using Type.
    move=> INDEPP INDEPQ s s' EQhp' EQalc'
      [ s1 [ s2 [ s3 [ sp [ sq [ EQsp [ EQsq [ EQs [ Psp Qsq ] ] ] ] ] ] ] ] ].
    move/state_sum_spec: EQsp => EQsp.
    move/state_sum_spec: EQsq => EQsq.
    move/state_sum_spec: EQs => EQs.
    case: EQsp => _ [ _ [ EQhpp EQalcp ] ].
    case: EQsq => _ [ _ [ EQhpq EQalcq ] ].
    case: EQs => _ [ _ [ EQhp EQalc ] ].
    exists (set_store s1 s'), (set_store s2 ($0: Sm)), (set_store s3 ($0: Sm)),
      (set_store sp s'), (set_store sq ($0: Sm)).
    split; first by apply/state_sum_spec; rewrite ?store_set_store ?scnt_set_store ?heap_set_store ?alc_set_store ?store_emp ?scnt_emp ?heap_emp ?alc_emp;
      split; [ exact: (op_id_r _) | ]; split; [ exact: (op_id_r _) | ]; split.
    split; first by apply/state_sum_spec; rewrite ?store_set_store ?scnt_set_store ?heap_set_store ?alc_set_store ?store_emp ?scnt_emp ?heap_emp ?alc_emp;
      split; [ exact: (op_id_l _) | ]; split; [ exact: (op_id_l _) | ]; split.
    split; first by apply/state_sum_spec; rewrite ?store_set_store ?scnt_set_store ?heap_set_store ?alc_set_store ?store_emp ?scnt_emp ?heap_emp ?alc_emp;
      split; [ exact: (op_id_r _) | ]; split; [ exact: (op_id_r _) | ];
      split; [ rewrite EQhp EQhp' | rewrite EQalc EQalc' ].
    split; first by apply: (INDEPP sp); rewrite ?heap_set_store ?alc_set_store.
    by apply: (INDEPQ sq); rewrite ?heap_set_store ?alc_set_store.
  Qed.

  Lemma indep_store_conj_overlap_store (P Q: Pred Sm):
    indep_store P -> indep_store Q -> indep_store (P *&s Q).
  Proof using Type.
    move=> INDEPP INDEPQ s s' EQhp' EQalc'
      [ sp [ sq [ EQstp [ EQstq [ EQsg [ EQhp [ EQalc [ Psp Qsq ] ] ] ] ] ] ] ].
    pose (sp' := mk_state (store s') $0 (heap sp) (alc sp)
                  (dominates_emp_cnt (store s')) (state_heap_dominates sp)).
    have EQstp': store sp' = store s' := store_mk_state _ _ _ _ _ _.
    have EQsgp': scnt sp' = $0 := scnt_mk_state _ _ _ _ _ _.
    have EQhpp': heap sp' = heap sp := heap_mk_state _ _ _ _ _ _.
    have EQalcp': alc sp' = alc sp := alc_mk_state _ _ _ _ _ _.
    apply: (conj_overlap_store_intro _ _ s' sp' (set_store sq s')).
    - exact: EQstp'.
    - exact: (store_set_store sq s').
    - by rewrite EQsgp' scnt_set_store; exact: (op_id_l _).
    - by rewrite EQhpp' heap_set_store EQhp EQhp'.
    - by rewrite EQalcp' alc_set_store EQalc EQalc'.
    - by apply: (INDEPP sp); rewrite ?EQhpp' ?EQalcp'.
    - by apply: (INDEPQ sq); rewrite ?heap_set_store ?alc_set_store.
  Qed.

  Lemma indep_cnt_inter (P Q: Pred Sm) (INDEPP: indep_cnt P) (INDEPQ: indep_cnt Q):
    indep_cnt (P && Q).
  Proof using Type.
    move=> s1 s2 EQst2 EQhp2 EQalc2 [ Ps1 Qs1 ].
    by split; [ exact: (INDEPP s1 s2 EQst2 EQhp2 EQalc2 Ps1) | exact: (INDEPQ s1 s2 EQst2 EQhp2 EQalc2 Qs1) ].
  Qed.

  Lemma indep_cnt_Exis [A] (P: A -> Pred Sm) (INDEP: forall x, indep_cnt (P x)):
    indep_cnt (Exis P).
  Proof using Type.
    by move=> s1 s2 EQst2 EQhp2 EQalc2 [ x Pxs1 ]; exists x; exact: (INDEP x s1 s2 EQst2 EQhp2 EQalc2 Pxs1).
  Qed.

  Lemma indep_cnt_star (P Q: Pred Sm) (INDEPP: indep_cnt P) (INDEPQ: indep_cnt Q):
    indep_cnt (P ** Q).
  Proof using Type.
    move=> s s' EQst' EQhp' EQalc' [ sp [ sq [ EQs [ Psp Qsq ] ] ] ].
    case/state_sum_spec: EQs => EQst [ EQsg [ EQhp EQalc ] ].
    have Dp': dominates (store sp) (scnt s').
    { apply: (dominates_sub_mem (store s') (store sp) (scnt s')).
      - by rewrite -EQst'; exact: (substate_of_partition_l EQst).
      - exact: (state_store_dominates s'). }
    pose sp' := mk_state (store sp) (scnt s') (heap sp) (alc sp) Dp' (state_heap_dominates sp).
    pose sq' := mk_state (store sq) $0 (heap sq) (alc sq)
                 (dominates_emp_cnt (store sq)) (state_heap_dominates sq).
    exists sp', sq'.
    split.
    { apply/state_sum_spec.
      rewrite !store_mk_state !scnt_mk_state !heap_mk_state !alc_mk_state.
      split; [ by rewrite -EQst' | ].
      split; [ exact: (op_id_r _) | ].
      by split; [ rewrite -EQhp' | rewrite -EQalc' ]. }
    split.
    - by apply: (INDEPP sp sp') => //; rewrite ?store_mk_state ?heap_mk_state ?alc_mk_state.
    - by apply: (INDEPQ sq sq') => //; rewrite ?store_mk_state ?heap_mk_state ?alc_mk_state.
  Qed.

  Lemma indep_cnt_star_lift_l (p: Prop) (Q: Pred Sm) (INDEPQ: indep_cnt Q):
    indep_cnt ([| p |] ** Q).
  Proof using Type.
    move=> s s' EQst' EQhp' EQalc' [ ? [ sq [ EQs [ [ Hp EMP ] Qsq ] ] ] ].
    move: EMP EQs => -> EQs.
    have EQsq: sq = s by move: EQs; rewrite (op_id_l _) => -[].
    move: EQsq Qsq => -> Qs.
    exists ($0: Sm), s'.
    split; first exact: (op_id_l _).
    split; first by split.
    exact: (INDEPQ s s' EQst' EQhp' EQalc' Qs).
  Qed.

  Lemma indep_cnt_upclose (P: Pred Sm) (EMP: forall s, P s -> scnt s = $0):
    indep_cnt (upclose P).
  Proof using Type.
    move=> s1 s2 EQst2 EQhp2 EQalc2 [ sp [ s3 [ EQs1 [ Psp _ ] ] ] ].
    case/state_sum_spec: EQs1 => EQst1 [ EQsg1 [ EQhp1 EQalc1 ] ].
    have DOM: dominates (store s3) (scnt s2).
    { apply: (dominates_sub_mem (store s2) (store s3) (scnt s2)); last exact: state_store_dominates.
      rewrite -EQst2.
      exact: (substate_of_partition_r EQst1). }
    exists sp, (mk_state (store s3) (scnt s2) (heap s3) (alc s3) DOM (state_heap_dominates s3)).
    split; [ | split; [ exact: Psp | exact: I ] ].
    apply/state_sum_spec.
    rewrite store_mk_state scnt_mk_state heap_mk_state alc_mk_state (EMP sp Psp) -EQst2 -EQhp2 -EQalc2.
    split; first exact: EQst1.
    split; first exact: (op_id_l _).
    by split.
  Qed.

  Lemma indep_cnt_Emp_heap: indep_cnt (Sm:=Sm) Emp_heap.
  Proof using Type. by move=> s1 s2 _ EQhp2 EQalc2 [ EQhp1 EQalc1 ]; rewrite /Emp_heap -EQhp2 -EQalc2. Qed.

  Lemma indep_cnt_conj_overlap_store (R1 R2: Pred Sm)
    (INDEPR1: indep_cnt R1) (INDEPR2: indep_cnt R2)
    : indep_cnt (R1 *&s R2).
  Proof using Type.
    move=> s s' EQst' EQhp' EQalc'
      [ sr1 [ sr2 [ EQstr1 [ EQstr2 [ EQsg [ EQhp [ EQalc [ R1sr1 R2sr2 ] ] ] ] ] ] ] ].
    have Dr1': dominates (store sr1) (scnt s')
      by rewrite EQstr1 EQst'; exact: (state_store_dominates s').
    pose sr1' := mk_state (store sr1) (scnt s') (heap sr1) (alc sr1)
                 Dr1' (state_heap_dominates sr1).
    pose sr2' := mk_state (store sr2) $0 (heap sr2) (alc sr2)
                 (dominates_emp_cnt (store sr2)) (state_heap_dominates sr2).
    apply: (conj_overlap_store_intro R1 R2 s' sr1' sr2').
    - by rewrite (store_mk_state _ _ _ _ _ _) EQstr1 EQst'.
    - by rewrite (store_mk_state _ _ _ _ _ _) EQstr2 EQst'.
    - by rewrite (scnt_mk_state _ _ _ _ _ _) (scnt_mk_state _ _ _ _ _ _); exact: (op_id_r _).
    - by rewrite (heap_mk_state _ _ _ _ _ _) (heap_mk_state _ _ _ _ _ _) -EQhp'.
    - by rewrite (alc_mk_state _ _ _ _ _ _) (alc_mk_state _ _ _ _ _ _) -EQalc'.
    - apply: (INDEPR1 sr1 sr1') => //.
      + by rewrite (store_mk_state _ _ _ _ _ _).
      + by rewrite (heap_mk_state _ _ _ _ _ _).
      + by rewrite (alc_mk_state _ _ _ _ _ _).
    - apply: (INDEPR2 sr2 sr2') => //.
      + by rewrite (store_mk_state _ _ _ _ _ _).
      + by rewrite (heap_mk_state _ _ _ _ _ _).
      + by rewrite (alc_mk_state _ _ _ _ _ _).
  Qed.

  Lemma indep_store_replace_inter (R1 R2: Pred Sm) (n1 n2: list Nm)
    (INDEPR1: indep_store_replace R1 n1) (INDEPR2: indep_store_replace R2 n2)
    : indep_store_replace (R1 && R2) (n1 ++ n2).
  Proof using Type.
    move=> s1 s2 [ R1s1 R2s1 ] SPE EQsg2 EQhp2 EQalc2.
    split.
    - apply: (indep_store_replace_incl R1 n1 (n1 ++ n2) _ INDEPR1 s1 s2 R1s1 SPE EQsg2 EQhp2 EQalc2).
      by move=> x INx; apply/in_or_app; left.
    - apply: (indep_store_replace_incl R2 n2 (n1 ++ n2) _ INDEPR2 s1 s2 R2s1 SPE EQsg2 EQhp2 EQalc2).
      by move=> x INx; apply/in_or_app; right.
  Qed.

  Lemma indep_heap_inter (P Q: Pred Sm) (INDEPP: indep_heap P) (INDEPQ: indep_heap Q):
    indep_heap (P && Q).
  Proof using Type.
    move=> s1 s2 EQst2 EQsg2 [ Ps1 Qs1 ].
    by split; [ exact: (INDEPP s1 s2 EQst2 EQsg2 Ps1) | exact: (INDEPQ s1 s2 EQst2 EQsg2 Qs1) ].
  Qed.

  Lemma indep_heap_Exis [A] (P: A -> Pred Sm) (INDEP: forall x, indep_heap (P x)):
    indep_heap (Exis P).
  Proof using Type.
    by move=> s1 s2 EQst2 EQsg2 [ x Pxs1 ]; exists x; exact: (INDEP x s1 s2 EQst2 EQsg2 Pxs1).
  Qed.

  Lemma indep_heap_upclose (P: Pred Sm) (EMP: forall s, P s -> heap s = $0 /\ alc s = $0):
    indep_heap (upclose P).
  Proof using Type.
    move=> s1 s2 EQst2 EQsg2 [ sp [ s3 [ EQs1 [ Psp _ ] ] ] ].
    case: (EMP sp Psp) => EQhpp EQalcp.
    case/state_sum_spec: EQs1 => EQst1 [ EQsg1 _ ].
    exists sp, (mk_state (store s3) (scnt s3) (heap s2) (alc s2) (state_store_dominates s3) (state_heap_dominates s2)).
    split; [ | split; [ exact: Psp | exact: I ] ].
    apply/state_sum_spec.
    rewrite store_mk_state scnt_mk_state heap_mk_state alc_mk_state EQhpp EQalcp -EQst2 -EQsg2.
    split; first exact: EQst1.
    split; first exact: EQsg1.
    by split; exact: (op_id_l _).
  Qed.

  Lemma indep_heap_star (P Q: Pred Sm):
      indep_heap P -> indep_heap Q -> indep_heap (P ** Q).
  Proof using Type.
    move=> INDEPP INDEPQ s s' EQst' EQsg' [ sp [ sq [ EQs [ Psp Qsq ] ] ] ].
    case/state_sum_spec: EQs => EQst [ EQsg [ EQhp EQalc ] ].
    exists (set_store s' sp), (set_store ($0: Sm) sq).
    split.
    - apply/state_sum_spec; rewrite ?store_set_store ?scnt_set_store ?heap_set_store ?alc_set_store ?store_emp ?scnt_emp ?heap_emp ?alc_emp.
      split; [ by rewrite -EQst' | ].
      split; [ by rewrite -EQsg' | ].
      split; [ exact: (op_id_r _) | ].
      exact: (op_id_r _).
    - split.
      + by apply: (INDEPP sp); rewrite ?store_set_store ?scnt_set_store.
      + by apply: (INDEPQ sq); rewrite ?store_set_store ?scnt_set_store.
  Qed.

End Facts.

Arguments indep_cnt_Emp_heap {Sm}.

#[global] Hint Resolve indep_store_star
  : seplog seplog_search.
#[global] Hint Resolve indep_store_conj_overlap indep_store_conj_overlap_store
  : seplog seplog_search.
#[global] Hint Resolve indep_cnt_inter indep_cnt_Exis
  indep_cnt_Emp_heap : seplog.
#[global] Hint Resolve indep_cnt_star indep_cnt_star_lift_l
  : seplog.
#[global] Hint Resolve indep_cnt_conj_overlap_store : seplog.
#[global] Hint Resolve indep_store_replace_inter : seplog_search.
#[global] Hint Resolve indep_heap_inter indep_heap_Exis indep_heap_star : seplog seplog_search.
