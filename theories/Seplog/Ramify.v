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

From GallinaC.Utils Require Import OptionExt.
From GallinaC.Imp Require Import State.
From GallinaC.Seplog.Inter Require Import Inter.
From GallinaC.Seplog.Forall Require Import Forall.
From GallinaC.Seplog Require Import Hoare.
From GallinaC.Seplog.Precise Require Import Precise.
From GallinaC.Seplog.Star Require Import Star Facts.
From GallinaC.Seplog.Upclose Require Import Upclose.
From GallinaC.Seplog.Wand Require Import Wand Facts.
From GallinaC.Seplog.Septract Require Import Septract Facts.
From GallinaC.Seplog.ConjOverlap Require Import ConjOverlap.
From GallinaC.Seplog Require Import Frame.
From GallinaC.Seplog.Star Require Import Frame.

Local Open Scope separation_scope.

Section Ramify.

  Context [S: Separation.type].

  Lemma ramify_disjoint (P1 Q1 R1 R1' P2 Q2 R2 R2': Pred S):
    |- R1 ===> P1 ** (Q1 -* R1') ->
    |- R2 ===> P2 ** (Q2 -* R2') ->
    |- R1 ** R2 ===> (P1 ** P2) ** ((Q1 ** Q2) -* (R1' ** R2')).
  Proof using Type.
    move=> RAM1 RAM2.
    have WAND: |- (Q1 -* R1') ** (Q2 -* R2') ===> ((Q1 ** Q2) -* (R1' ** R2')).
    { apply: wand_intro.
      rewrite (star_swap4 (Q1 -* R1') (Q2 -* R2') Q1 Q2).
      f_equiv; move=> s WQs.
      - apply: (star_wand_mp Q1 R1').
        by apply/star_comm.
      - apply: (star_wand_mp Q2 R2').
        by apply/star_comm. }
    move=> s SPLIT.
    rewrite RAM1 RAM2 in SPLIT.
    move/(star_swap4 P1 (Q1 -* R1') P2 (Q2 -* R2') s): SPLIT => SPLIT.
    rewrite WAND in SPLIT.
    exact: SPLIT.
  Qed.

  Lemma ramify_inter_precise (P F Q R R': Pred S):
    precise P ->
    |- R ===> P ** (Q -* R') ->
    |- (P ** F) && R ===> P ** (Q -* ((Q ** F) && R')).
  Proof using Type.
    move=> PREC RAM s [ [ sp [ sf [ EQs [ Psp Fsf ] ] ] ] Rs ].
    case: (RAM s Rs) => [ sp' [ sf' [ EQs' [ Psp' WAND ] ] ] ].
    have EQsp': sp = sp'.
    { apply: (PREC s sp sp' Psp Psp').
      - exact: (substate_of_partition_l EQs).
      - exact: (substate_of_partition_l EQs'). }
    move: EQsp' EQs' => <- EQs'.
    have EQsf': sf = sf' by exact: (op_cancel_l sp sf sf' s EQs EQs').
    move: EQsf' WAND => <- WAND.
    exists sp, sf; split; first exact: EQs.
    split; first exact: Psp.
    move=> sq sqfR Qsq EQsqfR.
    split.
    - exists sq, sf; split; last by split.
      exact: partition_comm.
    - exact: (WAND sq sqfR Qsq EQsqfR).
  Qed.

  Lemma ramify_inter_septract (P F Q R R': Pred S):
    |- (P -** R) ===> (Q -* R') ->
    |- (P ** F) && R ===> P ** (Q -* ((Q ** F) && R')).
  Proof using Type.
    move=> RAM s [ [ sp [ sf [ EQs [ Psp Fsf ] ] ] ] Rs ].
    have WAND: (Q -* R') sf.
    { apply: RAM. exists sp, s; split; first exact: Psp.
      split; last exact: Rs.
      exact: partition_comm. }
    exists sp, sf; split; first exact: EQs.
    split; first exact: Psp.
    move=> sq sqfR Qsq EQsqfR.
    split.
    - exists sq, sf; split; last by split.
      exact: partition_comm.
    - exact: (WAND sq sqfR Qsq EQsqfR).
  Qed.

  Lemma ramify_overlap_frame (P Q F R R': Pred S)
    (PRECP: precise P) (PRECQ: precise Q)
    (RAM: |- P *& R ===> P ** (Q -* (Q *& R')))
    : |- (P ** F) *& R ===> P ** (Q -* ((Q ** F) *& R')).
  Proof using Type.
    move=> s [ s1 [ s2 [ s3 [ spf [ sr [ EQspf [ EQsr [ EQs [ PFspf Rsr ] ] ] ] ] ] ] ] ].
    case: PFspf => sp [ sf [ EQspf' [ Psp Fsf ] ] ].
    case: (op_cross_split _ _ _ _ _ EQspf EQspf') => s1a [ s1b [ s2a [ s2b [ EQs1 [ EQs2 [ EQsp EQsf ] ] ] ] ] ].
    case: (partition_assoc EQs2 EQsr) => s4 [ EQs4 EQsr' ].
    case: (partition_assoc EQspf EQs) => _ [ /(Some_congr EQsr) <- EQs' ].
    case: (op_swap _ _ _ _ _ EQs1 EQs') => spr [ EQspr EQs'' ].
    case: (partition_assoc_rev EQsr' EQspr) => _ [ /(Some_congr EQsp) <- EQspr' ].
    have PRspr: (P *& R) spr by exists s1a, s2a, s4, sp, sr.
    case: (RAM spr PRspr) => sp' [ s4' [ EQspr'' [ Psp' WAND ] ] ].
    have EQsp': sp = sp'.
    { apply: (PRECP spr sp sp' Psp Psp').
      - exact: (substate_of_partition_l EQspr').
      - exact: (substate_of_partition_l EQspr''). }
    move: EQsp' EQspr'' => <- EQspr''.
    have EQs4': s4 = s4' by exact: (op_cancel_l sp s4 s4' spr EQspr' EQspr'').
    move: EQs4' WAND => <- WAND.
    case: (partition_assoc EQspr' EQs'') => sw [ EQsw EQs''' ].
    exists sp, sw.
    split; first exact: EQs'''.
    split; first exact: Psp.
    move=> sq sqfR Qsq EQsqfR.
    case: (op_swap _ _ _ _ _ EQsw EQsqfR) => sqR [ EQsqR EQsqfR' ].
    case: (WAND sq sqR Qsq EQsqR) => s5 [ s6 [ s4'' [ sq' [ sR [ + [ EQsR [ EQsqR' [ Qsq' R'sR ] ] ] ] ] ] ] ].
    have EQsq': sq' = sq.
    { apply: (PRECQ sqR sq' sq Qsq' Qsq).
      - exact: (substate_of_partition_l EQsqR').
      - exact: (substate_of_partition_r EQsqR). }
    move: EQsq' EQsqR' => -> EQsqR' EQsq.
    move/partition_comm: EQsqR => EQsqR.
    have EQs4'': s4'' = s4 by exact: (op_cancel_l sq s4'' s4 sqR EQsqR' EQsqR).
    move: EQs4'' EQsR => -> EQsR.
    case: (partition_assoc_rev EQs4 EQsqR) => s7 [ EQs7 EQsqR'' ].
    case: (op_swap _ _ _ _ _ EQsqR'' EQsqfR') => sqf [ EQsqf EQsqfR'' ].
    case: (partition_assoc EQs7 EQsqf) => _ [ /(Some_congr (partition_comm EQsf)) <- EQsqf' ].
    case: (partition_assoc_rev EQs4 EQsR) => s8 [ EQs8 EQsR' ].
    case: (partition_swap4 EQsq EQsf EQsqf') => s9 [ _ [ EQs9 [ /(Some_congr EQs8) <- EQsqf'' ] ] ].
    exists s9, s8, s3, sqf, sR.
    split; first exact: EQsqf''.
    split; first exact: EQsR'.
    split; first exact: EQsqfR''.
    split; last exact: R'sR.
    by exists sq, sf.
  Qed.

  Lemma ramify_overlap_piecewise (P P' Q1 Q2 Q1' Q2': Pred S)
    (PRECP: precise P) (PRECP': precise P')
    (RAM1: |- P *& Q1 ===> P ** (P' -* (P' *& Q1')))
    (RAM2: |- P *& Q2 ===> P ** (P' -* (P' *& Q2')))
    : |- (P *& Q1) *& Q2 ===> P ** (P' -* ((P' *& Q1') *& Q2')).
  Proof using Type.
    move=> s [ s1 [ s2 [ s3 [ spq1 [ sq2 [ EQspq1 [ EQsq2 [ EQs [ PQ1spq1 Q2sq2 ] ] ] ] ] ] ] ] ].
    case: PQ1spq1 => s4 [ s5 [ s6 [ sp [ sq1 [ EQsp [ EQsq1 [ EQspq1' [ Psp Q1sq1 ] ] ] ] ] ] ] ].
    have PQ1spq1: (P *& Q1) spq1 by exists s4, s5, s6, sp, sq1.
    case: (RAM1 spq1 PQ1spq1) => sp' [ s6' [ EQspq1'' [ Psp' WAND1 ] ] ].
    have EQsp': sp = sp'.
    { apply: (PRECP spq1 sp sp' Psp Psp').
      - exact: (substate_of_partition_l EQspq1').
      - exact: (substate_of_partition_l EQspq1''). }
    move: EQsp' EQspq1'' => <- EQspq1''.
    have EQs6': s6 = s6' by exact: (op_cancel_l sp s6 s6' spq1 EQspq1' EQspq1'').
    move: EQs6' WAND1 => <- WAND1.
    case: (op_cross_split _ _ _ _ _ EQspq1 EQspq1') => s1a [ s1b [ s2a [ s2b [ EQs1 [ EQs2 [ EQsp' EQs6 ] ] ] ] ] ].
    case: (partition_assoc EQs2 EQsq2) => s7 [ EQs7 EQsq2' ].
    case: (partition_assoc EQspq1 EQs) => _ [ /(Some_congr EQsq2) <- EQs' ].
    case: (op_swap _ _ _ _ _ EQs1 EQs') => spq2 [ EQspq2 EQs'' ].
    case: (partition_assoc_rev EQsq2' EQspq2) => _ [ /(Some_congr EQsp') <- EQspq2' ].
    have PQ2spq2: (P *& Q2) spq2 by exists s1a, s2a, s7, sp, sq2.
    case: (RAM2 spq2 PQ2spq2) => sp'' [ s7' [ EQspq2'' [ Psp'' WAND2 ] ] ].
    have EQsp'': sp = sp''.
    { apply: (PRECP spq2 sp sp'' Psp Psp'').
      - exact: (substate_of_partition_l EQspq2').
      - exact: (substate_of_partition_l EQspq2''). }
    move: EQsp'' EQspq2'' => <- EQspq2''.
    have EQs7': s7 = s7' by exact: (op_cancel_l sp s7 s7' spq2 EQspq2' EQspq2'').
    move: EQs7' WAND2 => <- WAND2.
    case: (partition_assoc EQspq1' EQs) => sw [ EQsw EQs''' ].
    exists sp, sw.
    split; first exact: EQs'''.
    split; first exact: Psp.
    move=> sP sPQ1Q2 P'sP EQsPQ1Q2.
    case: (op_swap _ _ _ _ _ EQsw EQsPQ1Q2) => sPQ1 [ EQsPQ1 EQsPQ1Q2' ].
    have P'Q1'sPQ1 := WAND1 sP sPQ1 P'sP EQsPQ1.
    case: (partition_assoc EQs6 EQsw) => _ [ /(Some_congr EQs7) <- EQsw' ].
    case: (partition_assoc EQsw' EQsPQ1Q2) => sPQ2 [ EQsPQ2 EQsPQ1Q2'' ].
    case: (WAND2 sP sPQ2 P'sP EQsPQ2) => s8 [ s9 [ s7'' [ sP' [ sQ2 [ + [ EQsQ2 [ EQsPQ2' [ P'sP' Q2'sQ2 ] ] ] ] ] ] ] ].
    have EQsP': sP' = sP.
    { apply: (PRECP' sPQ2 sP' sP P'sP' P'sP).
      - exact: (substate_of_partition_l EQsPQ2').
      - exact: (substate_of_partition_r EQsPQ2). }
    move: EQsP' EQsPQ2' => -> EQsPQ2' EQsP.
    move/partition_comm: EQsPQ2 => EQsPQ2.
    have EQs7'': s7'' = s7 by exact: (op_cancel_l sP s7'' s7 sPQ2 EQsPQ2' EQsPQ2).
    move: EQs7'' EQsQ2 => -> EQsQ2.
    case: (partition_assoc_rev EQs7 EQsQ2) => s10 [ EQs10 EQsQ2' ].
    case: (partition_swap4 EQs6 EQsP EQsPQ1) => s11 [ _ [ EQs11 [ /(Some_congr (partition_comm EQs10)) <- EQsPQ1' ] ] ].
    exists s11, s10, s3, sPQ1, sQ2.
    split; first exact: EQsPQ1'.
    split; first exact: EQsQ2'.
    split; first exact: EQsPQ1Q2'.
    by split.
  Qed.

End Ramify.

Section RamifyFrame.

  Context [Sm: State.type].

  Lemma ramify [total: bool] [A] [c: program Sm A] [P R: Pred Sm] [Q R': A -> Pred Sm]:
    action_local_strong c ->
    hoare total P c Q ->
    |- R ===> P ** (Forall v, Q v -* R' v) ->
    hoare total R c R'.
  Proof using Type.
    move=> LOCAL TRIPLE RAM.
    have FRAMED := star_frame_law total A P Q (Forall v, Q v -* R' v) (fun _ => Forall v, Q v -* R' v) c
                     (conj LOCAL (fun _ => impl_refl_taut _)) TRIPLE.
    apply: (consequence _ FRAMED).
    - exact: RAM.
    - move=> v s [ sq [ sw [ EQs [ Qvsq WAND ] ] ] ].
      apply: (WAND v sq s Qvsq).
      exact: partition_comm.
  Qed.

  Lemma ramify_fw [total: bool] [A] [c: program Sm A] [P R: Pred Sm] [Q R': A -> Pred Sm]:
    action_local_strong c ->
    hoare total P c Q ->
    |- R ===> upclose P ->
    (forall v, |- (P -** R) ** Q v ===> R' v) ->
    hoare total R c R'.
  Proof using Type.
    move=> LOCAL TRIPLE UP POST.
    have FRAMED := star_frame_law total A P Q (P -** R) (fun _ => P -** R) c
                     (conj LOCAL (fun _ => impl_refl_taut _)) TRIPLE.
    apply: (consequence _ FRAMED).
    - exact: (upclose_septract_split P R UP).
    - move=> v s QvPRs.
      apply: (POST v s).
      by apply/star_comm.
  Qed.

End RamifyFrame.
