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

From GallinaC.Imp Require Import Store State.
From GallinaC.Seplog Require Import Pred.
From GallinaC.Seplog.Exists Require Import Exists.
From GallinaC.Seplog.Emp Require Import Emp.
From GallinaC.Seplog.Lift Require Import Lift.
From GallinaC.Seplog.ConjOverlap Require Import ConjOverlap.
From GallinaC.Seplog.State Require Import EmpHeap.
From GallinaC.Seplog.ConjOverlapStore Require Import ConjOverlapStore.

Local Open Scope separation_scope.

Section Facts.

  Context [Sm: State.type].

  Lemma conj_overlap_store_conj_overlap (P Q: Pred Sm):
    |- P *&s Q ===> P *& Q.
  Proof using Type.
    move=> s [ sp [ sq [ EQstp [ EQstq [ EQsg [ EQhp [ EQalc [ Psp Qsq ] ] ] ] ] ] ] ].
    case: (state_store_only_proj s) => Ost [ Osg [ Ohp Oalc ] ].
    case: (state_store_free_proj sp) => Fpst [ Fpsg [ Fphp Fpalc ] ].
    case: (state_store_free_proj sq) => Fqst [ Fqsg [ Fqhp Fqalc ] ].
    exists (state_store_free sp), (state_store_only s),
      (state_store_free sq), sp, sq.
    split.
    - apply/state_sum_spec.
      rewrite Fpst Fpsg Fphp Fpalc Ost Osg Ohp Oalc.
      split; [ rewrite EQstp; exact: (op_id_l _) | ].
      split; [ exact: (op_id_r _) | ].
      by split; [ exact: (op_id_r _) | exact: (op_id_r _) ].
    - split.
      + apply/state_sum_spec.
        rewrite Fqst Fqsg Fqhp Fqalc Ost Osg Ohp Oalc.
        split; [ rewrite EQstq; exact: (op_id_r _) | ].
        split; [ exact: (op_id_l _) | ].
        by split; [ exact: (op_id_l _) | exact: (op_id_l _) ].
      + split.
        * apply/state_sum_spec.
          rewrite Fqst Fqsg Fqhp Fqalc.
          split; [ rewrite EQstp; exact: (op_id_r _) | ].
          by split; [ exact: EQsg | split ].
        * by split.
  Qed.

  Lemma conj_overlap_store_intro (P Q: Pred Sm) (s s1 s2: Sm)
    (EQst1: store s1 = store s) (EQst2: store s2 = store s)
    (EQsg: scnt s1 $+ scnt s2 = Some (scnt s))
    (EQhp: heap s1 $+ heap s2 = Some (heap s))
    (EQalc: alc s1 $+ alc s2 = Some (alc s))
    (Ps1: P s1) (Qs2: Q s2)
    : (P *&s Q) s.
  Proof using Type.
    exists s1, s2.
    split; [ exact: EQst1 | ].
    split; [ exact: EQst2 | ].
    split; [ exact: EQsg | ].
    split; [ exact: EQhp | ].
    split; [ exact: EQalc | ].
    by split.
  Qed.

  Lemma conj_overlap_store_comm (P Q: Pred Sm):
    |- P *&s Q <==> Q *&s P.
  Proof using Type.
    move=> s.
    have SWAP: forall (X Y: Pred Sm), (X *&s Y) s -> (Y *&s X) s.
    { move=> X Y [ sx [ sy [ EQstx [ EQsty [ EQsg [ EQhp [ EQalc [ Xsx Ysy ] ] ] ] ] ] ] ].
      exact: (conj_overlap_store_intro Y X s sy sx EQsty EQstx
               (partition_comm EQsg) (partition_comm EQhp) (partition_comm EQalc)
               Ysy Xsx). }
    by split; apply: SWAP.
  Qed.

  Lemma conj_overlap_store_substate_l (P Q: Pred Sm) (s: Sm):
    (P *&s Q) s -> exists s1, store s1 = store s /\ s1 $<= s /\ P s1.
  Proof using Type.
    move=> [ sp [ sq [ EQstp [ EQstq [ EQsg [ EQhp [ EQalc [ Psp Qsq ] ] ] ] ] ] ] ].
    case: (state_store_free_proj sq) => Fqst [ Fqsg [ Fqhp Fqalc ] ].
    exists sp.
    split; [ exact: EQstp | ].
    split; last exact: Psp.
    exists (state_store_free sq).
    apply/state_sum_spec.
    rewrite Fqst Fqsg Fqhp Fqalc.
    split; [ rewrite EQstp; exact: (op_id_r _) | ].
    by split; [ exact: EQsg | split ].
  Qed.

  Lemma conj_overlap_store_substate_r (P Q: Pred Sm) (s: Sm):
    (P *&s Q) s -> exists s2, store s2 = store s /\ s2 $<= s /\ Q s2.
  Proof using Type.
    move=> PQs.
    apply: (conj_overlap_store_substate_l Q P).
    by apply/conj_overlap_store_comm.
  Qed.

  Lemma Emp_heap_conj_overlap_store (P Q: Pred Sm):
    (|- P ===> Emp_heap) -> (|- Q ===> Emp_heap) ->
      |- P *&s Q ===> Emp_heap.
  Proof using Type.
    move=> EMP1 EMP2 s
      [ sp [ sq [ EQstp [ EQstq [ EQsg [ EQhp [ EQalc [ Psp Qsq ] ] ] ] ] ] ] ].
    case: (EMP1 sp Psp) => EQhpp EQalcp.
    case: (EMP2 sq Qsq) => EQhpq EQalcq.
    move: EQhpp EQhpq EQhp => -> -> EQhp.
    move: EQalcp EQalcq EQalc => -> -> EQalc.
    move/partition_emp_l: EQhp => EQhp.
    move/partition_emp_l: EQalc => EQalc.
    by split; [ rewrite -EQhp | rewrite -EQalc ].
  Qed.

  Lemma conj_overlap_store_weaken_l (P Q R: Pred Sm):
    (|- Q ===> Emp_heap_cnt) ->
      |- P ===> R -> |- Q *&s P ===> R.
  Proof using Type.
    move=> EMP IMP s
      [ sq [ sp [ EQstq [ EQstp [ EQsg [ EQhp [ EQalc [ Qsq Psp ] ] ] ] ] ] ] ].
    case: (EMP sq Qsq) => EQsgq [ EQhpq EQalcq ].
    move: EQsgq EQhpq EQalcq EQsg EQhp EQalc => -> -> -> EQsg EQhp EQalc.
    move/partition_emp_l: EQsg => EQsg.
    move/partition_emp_l: EQhp => EQhp.
    move/partition_emp_l: EQalc => EQalc.
    apply: IMP.
    by rewrite -(state_ext sp s EQstp EQsg EQhp EQalc).
  Qed.

  Lemma conj_overlap_store_weaken_r (P Q R: Pred Sm):
    (|- Q ===> Emp_heap_cnt) ->
      |- P ===> R -> |- P *&s Q ===> R.
  Proof using Type.
    move=> EMP IMP s PQs.
    apply: (conj_overlap_store_weaken_l P Q R EMP IMP).
    by apply/conj_overlap_store_comm.
  Qed.

  Lemma Emp_heap_cnt_neutral_conj_overlap_store_l (Q: Pred Sm):
    |- Emp_heap_cnt *&s Q <==> Q.
  Proof using Type.
    apply: impl_antisym_taut.
    - move=> s
        [ s1 [ sq [ EQst1 [ EQstq [ EQsg [ EQhp [ EQalc [ [ EQsg1 [ EQhp1 EQalc1 ] ] Qsq ] ] ] ] ] ] ] ].
      move: EQsg1 EQhp1 EQalc1 EQsg EQhp EQalc => -> -> -> EQsg EQhp EQalc.
      move/partition_emp_l: EQsg => EQsg.
      move/partition_emp_l: EQhp => EQhp.
      move/partition_emp_l: EQalc => EQalc.
      by rewrite -(state_ext sq s EQstq EQsg EQhp EQalc).
    - move=> s Qs.
      case: (state_store_only_proj s) => Ost [ Osg [ Ohp Oalc ] ].
      apply: (conj_overlap_store_intro _ _ s (state_store_only s) s).
      + exact: Ost.
      + by [].
      + by rewrite Osg; exact: (op_id_l _).
      + by rewrite Ohp; exact: (op_id_l _).
      + by rewrite Oalc; exact: (op_id_l _).
      + by split; [ exact: Osg | split ].
      + exact: Qs.
  Qed.

  Lemma Emp_heap_cnt_neutral_conj_overlap_store_r (Q: Pred Sm):
    |- Q *&s Emp_heap_cnt <==> Q.
  Proof using Type.
    move=> s; split=> [ QEhcs | Qs ].
    - apply/Emp_heap_cnt_neutral_conj_overlap_store_l.
      by apply/conj_overlap_store_comm.
    - apply/conj_overlap_store_comm.
      by apply/Emp_heap_cnt_neutral_conj_overlap_store_l.
  Qed.

  Lemma conj_overlap_store_assoc (P Q R: Pred Sm):
    |- (P *&s Q) *&s R <==> P *&s (Q *&s R).
  Proof using Type.
    apply: impl_antisym_taut.
    - move=> s
        [ spq [ sr [ EQstpq [ EQstr [ EQsg [ EQhp [ EQalc
        [ [ sp [ sq [ EQstp [ EQstq [ EQsgpq [ EQhppq [ EQalcpq [ Psp Qsq ] ] ] ] ] ] ] ]
          Rsr ] ] ] ] ] ] ] ].
      case: (partition_assoc EQsgpq EQsg) => sgqr [ EQsgqr EQsg' ].
      case: (partition_assoc EQhppq EQhp) => hpqr [ EQhpqr EQhp' ].
      case: (partition_assoc EQalcpq EQalc) => alcqr [ EQalcqr EQalc' ].
      have DOMc: dominates (store s) sgqr
        := dominates_sub_cnt (store s) (scnt s) sgqr
             (ex_intro _ (scnt sp) (partition_comm EQsg')) (state_store_dominates s).
      have DOMh: dominates hpqr (alc s)
        := dominates_sub_mem (heap s) hpqr (alc s)
             (ex_intro _ (heap sp) (partition_comm EQhp')) (state_heap_dominates s).
      have DOM: dominates hpqr alcqr
        := dominates_sub_cnt hpqr (alc s) alcqr
             (ex_intro _ (alc sp) (partition_comm EQalc')) DOMh.
      pose sqr := mk_state (store s) sgqr hpqr alcqr DOMc DOM.
      have EQstqr: store sqr = store s := store_mk_state _ _ _ _ _ _.
      have EQsgqr': scnt sqr = sgqr := scnt_mk_state _ _ _ _ _ _.
      have EQhpqr': heap sqr = hpqr := heap_mk_state _ _ _ _ _ _.
      have EQalcqr': alc sqr = alcqr := alc_mk_state _ _ _ _ _ _.
      apply: (conj_overlap_store_intro _ _ s sp sqr).
      + by rewrite EQstp.
      + exact: EQstqr.
      + by rewrite EQsgqr'; exact: EQsg'.
      + by rewrite EQhpqr'.
      + by rewrite EQalcqr'.
      + exact: Psp.
      + apply: (conj_overlap_store_intro _ _ sqr sq sr).
        * by rewrite EQstqr EQstq.
        * by rewrite EQstqr; exact: EQstr.
        * by rewrite EQsgqr'; exact: EQsgqr.
        * by rewrite EQhpqr'.
        * by rewrite EQalcqr'.
        * exact: Qsq.
        * exact: Rsr.
    - move=> s
        [ sp [ sqr [ EQstp [ EQstqr [ EQsg [ EQhp [ EQalc [ Psp
        [ sq [ sr [ EQstq [ EQstr [ EQsgqr [ EQhpqr [ EQalcqr [ Qsq Rsr ] ] ] ] ] ] ] ]
          ] ] ] ] ] ] ] ].
      case: (partition_assoc_rev EQsgqr EQsg) => sgpq [ EQsgpq EQsg' ].
      case: (partition_assoc_rev EQhpqr EQhp) => hppq [ EQhppq EQhp' ].
      case: (partition_assoc_rev EQalcqr EQalc) => alcpq [ EQalcpq EQalc' ].
      have DOMc: dominates (store s) sgpq
        := dominates_sub_cnt (store s) (scnt s) sgpq
             (ex_intro _ (scnt sr) EQsg') (state_store_dominates s).
      have DOMh: dominates hppq (alc s)
        := dominates_sub_mem (heap s) hppq (alc s)
             (ex_intro _ (heap sr) EQhp') (state_heap_dominates s).
      have DOM: dominates hppq alcpq
        := dominates_sub_cnt hppq (alc s) alcpq
             (ex_intro _ (alc sr) EQalc') DOMh.
      pose spq := mk_state (store s) sgpq hppq alcpq DOMc DOM.
      have EQstpq: store spq = store s := store_mk_state _ _ _ _ _ _.
      have EQsgpq': scnt spq = sgpq := scnt_mk_state _ _ _ _ _ _.
      have EQhppq': heap spq = hppq := heap_mk_state _ _ _ _ _ _.
      have EQalcpq': alc spq = alcpq := alc_mk_state _ _ _ _ _ _.
      apply: (conj_overlap_store_intro _ _ s spq sr).
      + exact: EQstpq.
      + by rewrite EQstr; exact: EQstqr.
      + by rewrite EQsgpq'; exact: EQsg'.
      + by rewrite EQhppq'; exact: EQhp'.
      + by rewrite EQalcpq'; exact: EQalc'.
      + apply: (conj_overlap_store_intro _ _ spq sp sq).
        * by rewrite EQstpq; exact: EQstp.
        * by rewrite EQstpq EQstq; exact: EQstqr.
        * by rewrite EQsgpq'; exact: EQsgpq.
        * by rewrite EQhppq'; exact: EQhppq.
        * by rewrite EQalcpq'; exact: EQalcpq.
        * exact: Psp.
        * exact: Qsq.
      + exact: Rsr.
  Qed.

  Lemma Exists_conj_overlap_store_left [A: Type] (P: A -> Pred Sm) (Q: Pred Sm):
    |- (Exists (x:A), ((P x) *&s Q)) <==> (Exists (x:A), P x) *&s Q.
  Proof using Type.
    apply: impl_antisym_taut; move=> s PQs.
    - case: PQs
        => x [ sp [ sq [ EQstp [ EQstq [ EQsg [ EQhp [ EQalc [ Pxsp Qsq ] ] ] ] ] ] ] ].
      apply: (conj_overlap_store_intro _ _ s sp sq) => //.
      by exists x.
    - case: PQs
        => sp [ sq [ EQstp [ EQstq [ EQsg [ EQhp [ EQalc [ [ x Pxsp ] Qsq ] ] ] ] ] ] ].
      exists x.
      by apply: (conj_overlap_store_intro _ _ s sp sq).
  Qed.

  Lemma Exists_conj_overlap_store_right [A: Type] (P: Pred Sm) (Q: A -> Pred Sm):
    |- (Exists (x:A), (P *&s (Q x))) <==> P *&s (Exists (x:A), Q x).
  Proof using Type.
    apply: impl_antisym_taut; move=> s PQs.
    - case: PQs
        => x [ sp [ sq [ EQstp [ EQstq [ EQsg [ EQhp [ EQalc [ Psp Qxsq ] ] ] ] ] ] ] ].
      apply: (conj_overlap_store_intro _ _ s sp sq) => //.
      by exists x.
    - case: PQs
        => sp [ sq [ EQstp [ EQstq [ EQsg [ EQhp [ EQalc [ Psp [ x Qxsq ] ] ] ] ] ] ] ].
      exists x.
      by apply: (conj_overlap_store_intro _ _ s sp sq).
  Qed.

  Lemma Emp_conj_overlap_store_l (Q: Pred Sm) (s: Sm):
    ($$0 *&s Q) s <-> (store s = $0 /\ Q s).
  Proof using Type.
    split.
    - move=> [ ? [ sq [ EQst0 [ EQstq [ EQsg [ EQhp [ EQalc [ EMP Qsq ] ] ] ] ] ] ] ].
      move: EMP EQst0 EQsg EQhp EQalc => -> EQst0 EQsg EQhp EQalc.
      case: (@emp_proj Sm) => EQst0' [ EQsg0 [ EQhp0 EQalc0 ] ].
      move: EQsg0 EQhp0 EQalc0 EQsg EQhp EQalc => -> -> -> EQsg EQhp EQalc.
      move/partition_emp_l: EQsg => EQsg.
      move/partition_emp_l: EQhp => EQhp.
      move/partition_emp_l: EQalc => EQalc.
      split; first by rewrite -EQst0.
      by rewrite -(state_ext sq s EQstq EQsg EQhp EQalc).
    - move=> [ EQst Qs ].
      case: (@emp_proj Sm) => EQst0 [ EQsg0 [ EQhp0 EQalc0 ] ].
      apply: (conj_overlap_store_intro _ _ s ($0: Sm) s).
      + by rewrite EQst0.
      + by [].
      + by rewrite EQsg0; exact: (op_id_l _).
      + by rewrite EQhp0; exact: (op_id_l _).
      + by rewrite EQalc0; exact: (op_id_l _).
      + by [].
      + exact: Qs.
  Qed.

  Lemma lift_conj_overlap_store_l (P: Prop) (Q: Pred Sm) (s: Sm):
    ([| P |] *&s Q) s <-> (P /\ store s = $0 /\ Q s).
  Proof using Type.
    split.
    - move=> [ sp [ sq [ EQstp [ EQstq [ EQsg [ EQhp [ EQalc [ [ HP EMP ] Qsq ] ] ] ] ] ] ] ].
      split; [ exact: HP | ].
      apply/Emp_conj_overlap_store_l.
      exists sp, sq.
      split; [ exact: EQstp | ].
      split; [ exact: EQstq | ].
      split; [ exact: EQsg | ].
      split; [ exact: EQhp | ].
      split; [ exact: EQalc | ].
      by split; [ exact: EMP | exact: Qsq ].
    - move=> [ HP [ EQst Qs ] ].
      case: (proj2 (Emp_conj_overlap_store_l Q s) (conj EQst Qs))
        => sp [ sq [ EQstp [ EQstq [ EQsg [ EQhp [ EQalc [ EMP Qsq ] ] ] ] ] ] ].
      exists sp, sq.
      split; [ exact: EQstp | ].
      split; [ exact: EQstq | ].
      split; [ exact: EQsg | ].
      split; [ exact: EQhp | ].
      split; [ exact: EQalc | ].
      by split; [ split; [ exact: HP | exact: EMP ] | exact: Qsq ].
  Qed.

End Facts.
