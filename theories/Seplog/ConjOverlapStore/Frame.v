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

From GallinaC.Utils Require Import ListExt.
From GallinaC.Imp Require Import Store State.
From GallinaC.Seplog Require Import Hoare.
From GallinaC.Seplog.State Require Import EmpHeap.
From GallinaC.Seplog.Indep Require Import Indep.
From GallinaC.Seplog.ConjOverlapStore Require Import ConjOverlapStore Facts.
From GallinaC.Seplog.State Require Import Atoms.
From GallinaC.Seplog Require Import Frame.

Local Open Scope separation_scope.

Section Frame.

  Context [Sm: State.type].

  Lemma conj_overlap_store_frame_law:
    forall (total: bool) A (P: Pred Sm) (Q: A -> Pred Sm) (R: Pred Sm) (R': A -> Pred Sm) (c: program Sm A),
      (action_local c /\ indep_cnt R /\ indep_no_cnt R c /\ forall v, |- R ===> R' v) ->
      hoare total P c Q -> hoare total (P *&s R) c (fun v => Q v *&s R' v).
  Proof using Type.
    move=> total A P Q R R' c [ACTLOC [CI [INDEPR IMPL] ] ] TRIPLE.
    apply: (strengthen (Q := fun v => Q v *&s R)).
    { move=> s [sp [sr [EQstp [EQstr [EQsg [EQhp [EQalc [Psp Rsr] ] ] ] ] ] ] ].
      pose f := mk_state $0 (scnt sr) (heap sr) (alc sr)
                  (dominates_emp (scnt sr)) (state_heap_dominates sr).
      have EQstf: store f = $0 := store_mk_state _ _ _ _ _ _.
      have EQsgf: scnt f = scnt sr := scnt_mk_state _ _ _ _ _ _.
      have EQhpf: heap f = heap sr := heap_mk_state _ _ _ _ _ _.
      have EQalcf: alc f = alc sr := alc_mk_state _ _ _ _ _ _.
      have EQs: sp $+ f = Some s.
      { apply/state_sum_spec.
        rewrite EQstf EQsgf EQhpf EQalcf.
        split; [ by rewrite EQstp; exact: (op_id_r _) | ].
        by split; [ exact: EQsg | split; [ exact: EQhp | exact: EQalc ] ]. }
      move: (TRIPLE sp Psp) (ACTLOC sp s f EQs).
      case EQc: (c sp) => [ [ [ v sp' ] | ] | ] TR AL.
      - case: AL => s' [EQs' ->].
        case/state_sum_spec: EQs' => EQst' [EQsg' [EQhp' EQalc'] ].
        move: EQstf EQsgf EQst' EQsg' => -> -> EQst' EQsg'.
        move: EQhpf EQalcf EQhp' EQalc' => -> -> EQhp' EQalc'.
        have EQstp': store sp' = store s' := partition_emp_r EQst'.
        have Dr': dominates (store s') (scnt sr)
          := dominates_sub_cnt (store s') (scnt s') (scnt sr)
               (substate_of_partition_r EQsg') (state_store_dominates s').
        pose sr' := mk_state (store s') (scnt sr) (heap sr) (alc sr)
                     Dr' (state_heap_dominates sr).
        have EQstr': store sr' = store s' := store_mk_state _ _ _ _ _ _.
        have EQsgr': scnt sr' = scnt sr := scnt_mk_state _ _ _ _ _ _.
        have EQhpr': heap sr' = heap sr := heap_mk_state _ _ _ _ _ _.
        have EQalcr': alc sr' = alc sr := alc_mk_state _ _ _ _ _ _.
        apply: (conj_overlap_store_intro (Q v) R s' sp' sr').
        + exact: EQstp'.
        + exact: EQstr'.
        + by rewrite EQsgr'; exact: EQsg'.
        + by rewrite EQhpr'; exact: EQhp'.
        + by rewrite EQalcr'; exact: EQalc'.
        + exact: TR.
        + apply: (CI (set_store_no_cnt sr sp') sr').
          * by rewrite store_set_store_no_cnt EQstr'.
          * by rewrite heap_set_store_no_cnt EQhpr'.
          * by rewrite alc_set_store_no_cnt EQalcr'.
          * apply: (INDEPR sp v sp' sr EQc).
            apply: (CI sr (set_store_no_cnt sr sp)).
            -- by rewrite store_set_store_no_cnt EQstr EQstp.
            -- by rewrite heap_set_store_no_cnt.
            -- by rewrite alc_set_store_no_cnt.
            -- exact: Rsr.
      - by [].
      - by rewrite AL. }
    move=> v.
    apply: (_: |- _ ===> _).
    f_equiv.
    exact: IMPL.
  Qed.

  HB.instance Definition conj_overlap_store_framing :=
    isFraming.Build Sm (@conj_overlap_store Sm)
      (fun A P Q R R' c => action_local c /\ indep_cnt R /\ indep_no_cnt R c /\ forall v, |- R ===> R' v)
      conj_overlap_store_frame_law.

  Lemma frame_store_weaken [total: bool] [A] [P R P': Pred Sm] [Q Q': A -> Pred Sm] [c: program Sm A]
    (ACTLOC: action_local c)
    (CI: indep_cnt R) (INDEPR: indep_no_cnt R c)
    (TRIPLE: hoare total P c Q)
    (PRE: |- P' ===> P *&s R) (POST: forall v, |- Q v *&s R ===> Q' v)
    : hoare total P' c Q'.
  Proof using Type.
    apply: (weaken _ PRE).
    apply: (strengthen _ POST).
    exact: (conj_overlap_store_frame_law total A P Q R (fun _ => R) c
              (conj ACTLOC (conj CI (conj INDEPR (fun _ => impl_refl_taut R)))) TRIPLE).
  Qed.

  (* A heapless and counterless frame condition can be freely added to a triple *)
  Lemma frame_store_elim [total: bool] [A] [P R: Pred Sm] [Q: A -> Pred Sm] [c: program Sm A]
    (EMPh: |- R ===> Emp_heap_cnt)
    (ACTLOC: action_local c)
    (CI: indep_cnt R) (INDEPR: indep_no_cnt R c)
    (TRIPLE: hoare total P c Q)
    : hoare total (P *&s R) c Q.
  Proof using Type.
    apply: (frame_store_weaken ACTLOC CI INDEPR TRIPLE).
    - exact: impl_refl_taut.
    - move=> v.
      exact: (conj_overlap_store_weaken_r (Q v) R (Q v) EMPh (impl_refl_taut (Q v))).
  Qed.

  Lemma frame_store_lift_store [total: bool] [A] [p: Prop] [P: Pred Sm] [Q: A -> Pred Sm] [c: program Sm A]
    (ACTLOC: action_local c) (TRIPLE: hoare total P c Q)
    : hoare total (P *&s lift_store p) c (fun v => Q v *&s lift_store p).
  Proof using Type.
    exact: (conj_overlap_store_frame_law total A P Q (lift_store p) (fun _ => lift_store p) c
              (conj ACTLOC (conj (indep_cnt_lift_store p)
                 (conj (indep_no_cnt_of_replace _ _ [] (indep_store_replace_lift_store p)
                          (indep_cmd_partial_store_nil c))
                    (fun _ => impl_refl_taut (lift_store p)))))
              TRIPLE).
  Qed.

End Frame.

Arguments conj_overlap_store_framing {Sm}.
