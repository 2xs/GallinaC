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

From GallinaC.Utils Require Import Algebra OptionExt.
From GallinaC.Seplog Require Import Pred.
From GallinaC.Seplog.Inter Require Import Inter.
From GallinaC.Seplog.Exists Require Import Exists.
From GallinaC.Seplog.Emp Require Import Emp.
From GallinaC.Seplog.Lift Require Import Lift.
From GallinaC.Seplog.Star Require Import Star.
From GallinaC.Seplog.Wand Require Import Wand.
From GallinaC.Seplog.ConjOverlap Require Import ConjOverlap.

Local Open Scope separation_scope.

Section Facts.

  Context [S: Separation.type].

  Lemma conj_overlap_comm (P Q: Pred S):
    |- P *& Q <==> Q *& P.
  Proof using Type.
    move=> s.
    have SWAP: forall (X Y: Pred S), (X *& Y) s -> (Y *& X) s.
    { move=> X Y [ s1 [ s2 [ s3 [ sx [ sy [ EQsx [ EQsy [ EQs [ Xsx Ysy ] ] ] ] ] ] ] ] ].
      case: (partition_assoc EQsx EQs) => _ [ /(Some_congr EQsy) <- EQs' ].
      exists s3, s2, s1, sy, sx.
      split; [ exact: (partition_comm EQsy) | ].
      split; [ exact: (partition_comm EQsx) | ].
      split; [ exact: (partition_comm EQs') | ].
      by split. }
    by split; apply: SWAP.
  Qed.

  Lemma conj_overlap_substate_l (P Q: Pred S) (s: S):
    (P *& Q) s -> exists sp, sp $<= s /\ P sp.
  Proof using Type.
    move=> [ s1 [ s2 [ s3 [ sp [ sq [ EQsp [ EQsq [ EQs [ Psp Qsq ] ] ] ] ] ] ] ] ].
    exists sp.
    by split; [ exact: (substate_of_partition_l EQs) | exact: Psp ].
  Qed.

  Lemma conj_overlap_substate_r (P Q: Pred S) (s: S):
    (P *& Q) s -> exists sq, sq $<= s /\ Q sq.
  Proof using Type.
    move=> [ s1 [ s2 [ s3 [ sp [ sq [ EQsp [ EQsq [ EQs [ Psp Qsq ] ] ] ] ] ] ] ] ].
    case: (partition_assoc EQsp EQs) => _ [ /(Some_congr EQsq) <- EQs' ].
    exists sq.
    by split; [ exact: (substate_of_partition_r EQs') | exact: Qsq ].
  Qed.

  Lemma Exists_conj_overlap_left [A: Type] (P: A -> Pred S) (Q: Pred S):
    |- (Exists (x:A), ((P x) *& Q)) <==> (Exists (x:A), P x) *& Q.
  Proof using Type.
    apply: impl_antisym_taut; move=> s PQs.
    - case: PQs => x [ s1 [ s2 [ s3 [ sp [ sq [ EQsp [ EQsq [ EQs [ Pxsp Qsq ] ] ] ] ] ] ] ] ].
      exists s1, s2, s3, sp, sq.
      split; first by [].
      split; first by [].
      split; first by [].
      by split; [ exists x | ].
    - case: PQs => s1 [ s2 [ s3 [ sp [ sq [ EQsp [ EQsq [ EQs [ [ x Pxsp ] Qsq ] ] ] ] ] ] ] ].
      exists x, s1, s2, s3, sp, sq.
      split; first by [].
      split; first by [].
      split; first by [].
      by split.
  Qed.

  Lemma Exists_conj_overlap_right [A: Type] (P: Pred S) (Q: A -> Pred S):
    |- (Exists (x:A), (P *& (Q x))) <==> P *& (Exists (x:A), Q x).
  Proof using Type.
    apply: impl_antisym_taut; move=> s PQs.
    - case: PQs => x [ s1 [ s2 [ s3 [ sp [ sq [ EQsp [ EQsq [ EQs [ Psp Qxsq ] ] ] ] ] ] ] ] ].
      exists s1, s2, s3, sp, sq.
      split; first by [].
      split; first by [].
      split; first by [].
      by split; [ | exists x ].
    - case: PQs => s1 [ s2 [ s3 [ sp [ sq [ EQsp [ EQsq [ EQs [ Psp [ x Qxsq ] ] ] ] ] ] ] ] ].
      exists x, s1, s2, s3, sp, sq.
      split; first by [].
      split; first by [].
      split; first by [].
      by split.
  Qed.

  Lemma star_conj_overlap (P Q: Pred S):
    |- P ** Q ===> P *& Q.
  Proof using Type.
    move=> s [ sp [ sq [ EQs [ Psp Qsq ] ] ] ].
    exists sp, ($0: S), sq, sp, sq.
    split; [ exact: (op_id_r _) | ].
    split; [ exact: (op_id_l _) | ].
    split; [ exact: EQs | ].
    by split.
  Qed.

  Lemma Emp_conj_overlap_l (P: Pred S):
    |- P ===> $$0 *& P.
  Proof using Type.
    move=> s Ps.
    exists ($0: S), ($0: S), s, ($0: S), s.
    split; [ exact: (op_id_l _) | ].
    split; [ exact: (op_id_l _) | ].
    split; [ exact: (op_id_l _) | ].
    by split.
  Qed.

  Lemma Emp_conj_overlap_r (P: Pred S):
    |- P ===> P *& $$0.
  Proof using Type.
    move=> s Ps.
    exists s, ($0: S), ($0: S), s, ($0: S).
    split; [ exact: (op_id_r _) | ].
    split; [ exact: (op_id_l _) | ].
    split; [ exact: (op_id_r _) | ].
    by split.
  Qed.

  Lemma lift_conj_overlap_l (P: Prop) (Q: Pred S):
    P -> |- Q ===> [| P |] *& Q.
  Proof using Type.
    move=> HP s Qs.
    exists ($0: S), ($0: S), s, ($0: S), s.
    split; [ exact: (op_id_l _) | ].
    split; [ exact: (op_id_l _) | ].
    split; [ exact: (op_id_l _) | ].
    by split; [ split; [ exact: HP | ] | ].
  Qed.

  Lemma lift_conj_overlap_prop (P: Prop) (Q: Pred S) (s: S):
    ([| P |] *& Q) s -> P.
  Proof using Type.
    by move=> [ s1 [ s2 [ s3 [ sp [ sq [ EQsp [ EQsq [ EQs [ [ HP EMP ] Qsq ] ] ] ] ] ] ] ] ].
  Qed.

  Lemma inter_conj_overlap (P Q: Pred S): |- P && Q ===> P *& Q.
  Proof using Type.
    move=> s [ Ps Qs ].
    exists ($0: S), s, ($0: S), s, s.
    split; first exact: op_id_l.
    split; first exact: op_id_r.
    split; first exact: op_id_r.
    by split.
  Qed.

  Lemma conj_overlap_star_top (P Q: Pred S): |- P *& Q ===> P ** top.
  Proof using Type.
    move=> s [ s1 [ s2 [ s3 [ sp [ sq [ EQsp [ EQsq [ EQs [ Psp Qsq ] ] ] ] ] ] ] ] ].
    exists sp, s3.
    split; first exact: EQs.
    by split.
  Qed.

  Lemma conj_overlap_wand_exists (P Q: Pred S):
    |- P *& Q <==> (Exists (R: Pred S), (R -* P) ** (R -* Q) ** R).
  Proof using Type.
    move=> s; split.
    - move=> [ s1 [ s2 [ s3 [ sp [ sq [ EQsp [ EQsq [ EQs [ Psp Qsq ] ] ] ] ] ] ] ] ].
      exists (fun s2' => s2' = s2).
      case: (op_swap _ _ _ _ _ EQsp EQs) => su [ EQsu EQs' ].
      exists su, s2.
      split; first exact: EQs'.
      split; last by [].
      exists s1, s3.
      split; first exact: EQsu.
      split.
      + move=> sr sp' -> EQsp'.
        by rewrite (Some_congr EQsp' EQsp).
      + move=> sr sq' -> EQsq'.
        by rewrite (Some_congr (partition_comm EQsq') EQsq).
    - move=> [ R [ su [ sr [ EQs' [ [ s1 [ s3 [ EQsu [ WANDP WANDQ ] ] ] ] Rsr ] ] ] ] ].
      case: (op_swap _ _ _ _ _ EQsu EQs') => sp [ EQsp EQs ].
      case: (partition_assoc EQsu EQs') => sq [ EQsq _ ].
      exists s1, sr, s3, sp, sq.
      split; first exact: EQsp.
      split; first exact: (partition_comm EQsq).
      split; first exact: EQs.
      split; [ exact: (WANDP sr sp Rsr EQsp) | exact: (WANDQ sr sq Rsr EQsq) ].
  Qed.

  Lemma conj_overlap_assoc (P Q R: Pred S):
    |- (P *& Q) *& R <==> P *& (Q *& R).
  Proof using Type.
    have ASSOC: forall (X Y Z: Pred S), |- X *& (Y *& Z) ===> (X *& Y) *& Z.
    { move=> X Y Z.
      move=> s [ s1 [ s2 [ s3 [ sx [ syz [ EQsx [ EQsyz [ EQs [ Xsx YZsyz ] ] ] ] ] ] ] ] ].
      case: YZsyz => s4 [ s5 [ s6 [ sy [ sz [ EQsy [ EQsz [ EQsyz' [ Ysy Zsz ] ] ] ] ] ] ] ].
      case: (op_cross_split _ _ _ _ _ EQsyz EQsyz')
        => s2a [ s2b [ s3a [ s3b [ EQs2 [ EQs3 [ EQsy' EQs6 ] ] ] ] ] ].
      move/partition_comm: EQs2 => EQs2.
      case: (partition_assoc_rev EQs2 EQsx) => s7 [ EQs7 EQsx' ].
      case: (partition_assoc_rev EQs3 EQs) => sxy [ EQsxy EQs' ].
      case: (partition_assoc_rev EQs6 EQsz) => s8 [ EQs8 EQsz' ].
      case: (partition_assoc EQsx' EQsxy) => _ [ /(Some_congr EQsy') <- EQsxy' ].
      case: (partition_assoc_rev EQsy EQsxy') => s9 [ EQs9 EQsxy'' ].
      case: (op_swap _ _ _ _ _ EQs7 EQs9) => s10 [ EQs10 EQs9' ].
      case: (partition_assoc EQs9' EQsxy'') => _ [ /partition_comm/(Some_congr EQs8) <- EQsxy''' ].
      exists s10, s8, s3b, sxy, sz.
      split; first exact: EQsxy'''.
      split; first exact: EQsz'.
      split; first exact: EQs'.
      split; last exact: Zsz.
      exists s7, s2a, s3a, sx, sy.
      by do 3 (split; first by []); split. }
    move=> s; split=> PQRs.
    - have RPQs := proj1 (conj_overlap_comm _ _ s) PQRs.
      rewrite (conj_overlap_comm P Q) in RPQs.
      have RQPs := ASSOC R Q P s RPQs.
      have PRQs := proj1 (conj_overlap_comm _ _ s) RQPs.
      rewrite (conj_overlap_comm R Q) in PRQs.
      exact: PRQs.
    - exact: (ASSOC P Q R s PQRs).
  Qed.

End Facts.
