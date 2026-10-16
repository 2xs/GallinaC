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

From GallinaC.Utils Require Import Algebra.
From GallinaC.Seplog Require Import Pred.
From GallinaC.Seplog.Inter Require Import Inter.
From GallinaC.Seplog.Exists Require Import Exists.
From GallinaC.Seplog.Emp Require Import Emp.
From GallinaC.Seplog.Stateless Require Import Stateless.
From GallinaC.Seplog.Lift Require Import Lift.
From GallinaC.Seplog.Precise Require Import Precise.
From GallinaC.Seplog.Star Require Import Star.

Local Open Scope separation_scope.

Section Facts.

  Context [S: Separation.type].

  Lemma star_comm :
    forall (P Q: Pred S), |- P ** Q <==> Q ** P.
  Proof using Type.
    move=> P Q s.
    have SWAP: forall (X Y: Pred S), (X ** Y) s -> (Y ** X) s.
    { move=> X Y [ sx [ sy [ EQs [ Xsx Ysy ] ] ] ].
      exists sy, sx.
      split; [ exact: (partition_comm EQs) | ].
      by split. }
    by split; apply: SWAP.
  Qed.

  Lemma star_assoc :
    forall (P Q R: Pred S),
      |- P ** Q ** R <==> P ** (Q ** R).
  Proof using Type.
    move=> P Q R s;
      split; move=> PQRs.
    - case: PQRs => spq [ sr [ EQs [ [ sp [ sq [ EQspq [ Psp Qsq ] ] ] ] Rsr ] ] ].
      case: (partition_assoc EQspq EQs) => sqr [ EQsqr EQs' ].
      exists sp, sqr.
      split; [ exact: EQs' | ].
      split; first by [].
      exists sq, sr.
      split; [ exact: EQsqr | ].
      by split.
    - case: PQRs => sp [ sqr [ EQs [ Psp [ sq [ sr [ EQsqr [ Qsq Rsr ] ] ] ] ] ] ].
      case: (partition_assoc_rev EQsqr EQs) => spq [ EQspq EQs' ].
      exists spq, sr.
      split; [ exact: EQs' | ].
      split; last by [].
      exists sp, sq.
      split; [ exact: EQspq | ].
      by split.
  Qed.

  Lemma star_swap (P Q R: Pred S):
    |- P ** (Q ** R) <==> Q ** (P ** R).
  Proof using Type.
    by rewrite -!star_assoc (star_comm P Q).
  Qed.

  Lemma star_swap4 (P Q R T: Pred S):
    |- (P ** Q) ** (R ** T) <==> (P ** R) ** (Q ** T).
  Proof using Type.
    rewrite star_assoc (star_swap Q R T).
    rewrite -(star_assoc P R (Q ** T)).
    reflexivity.
  Qed.

  Lemma Exists_star_left_r [A: Type] (P: A -> Pred S) (Q: Pred S):
        |- (Exists (x:A), P x) ** Q ===> Exists (x:A), ((P x) ** Q).
  Proof using Type.
    move=> s [ sp [ sq [ EQs [ [ x Pxsp ] Qsq ] ] ] ].
    exists x, sp, sq.
    split; first by [].
    by split.
  Qed.

  Lemma Exists_star_right_l [A: Type] (P: Pred S) (Q: A -> Pred S):
      |- (Exists (x:A), P ** (Q x)) ===> P ** (Exists (x:A), Q x).
  Proof using Type.
    move=> s [ x [ sp [ sq [ EQs [ Psp Qxsq ] ] ] ] ].
    exists sp, sq.
    split; first by [].
    by split; [ | exists x ].
  Qed.

  Lemma Exists_star_left_l [A: Type] (P: A -> Pred S) (Q: Pred S):
        |- (Exists (x:A), ((P x) ** Q)) ===> (Exists (x:A), P x) ** Q.
  Proof using Type.
    move=> s [ x [ sp [ sq [ EQs [ Pxsp Qsq ] ] ] ] ].
    exists sp, sq.
    split; first by [].
    by split; [ exists x | ].
  Qed.

  Lemma Exists_star_right_r [A: Type] (P: Pred S) (Q: A -> Pred S):
      |- P ** (Exists (x:A), Q x) ===> (Exists (x:A), P ** (Q x)).
  Proof using Type.
    move=> s [ sp [ sq [ EQs [ Psp [ x Qxsq ] ] ] ] ].
    exists x, sp, sq.
    split; first by [].
    by split.
  Qed.

  Lemma Exists_star_left [A: Type] (P: A -> Pred S) (Q: Pred S):
      |- (Exists (x:A), ((P x) ** Q)) <==> (Exists (x:A), P x) ** Q.
  Proof using Type.
    by apply: impl_antisym_taut; [ apply: Exists_star_left_l | apply: Exists_star_left_r ].
  Qed.

  Lemma Exists_star_right [A: Type] (P: Pred S) (Q: A -> Pred S):
      |- (Exists (x:A), P ** (Q x)) <==> P ** (Exists (x:A), Q x).
  Proof using Type.
    by apply: impl_antisym_taut; [ apply: Exists_star_right_l | apply: Exists_star_right_r ].
  Qed.

  Lemma lift_and: forall (P Q: Prop),
      |- ([| P |] ** [| Q |] : Pred S) <==> [| P /\ Q |].
  Proof using Type.
    move=> P Q.
    apply: impl_antisym_taut; move=> s PQs.
    - case: PQs => sp [ sq [ EQs [ [ HP EMP1 ] [ HQ EMP2 ] ] ] ].
      move: EMP1 EQs => -> /partition_emp_l EQs.
      by split; [ split | congruence ].
    - case: PQs => [ [ HP HQ ] EMP ].
      rewrite EMP.
      exists $0, $0.
      split; [ exact: (op_id_l _) | ].
      by split; split.
  Qed.

  Lemma eq_star_rw [A: Type] (a b: A) (P: A -> Pred S):
        |- [| a = b |] ** P a ===> P b.
  Proof using Type.
    move=> s [ ? [ sp [ EQs [ [ -> EMP ] Pbsp ] ] ] ].
    move: EMP EQs => -> /partition_emp_l EQs.
    by rewrite -EQs.
  Qed.

  Lemma Emp_neutral_star_l: forall (P: Pred S),
      |- $$0 ** P <==> P.
  Proof using Type.
    move=> P.
    apply: impl_antisym_taut.
    - move=> s [ ? [ sp [ EQs [ EMP Psp ] ] ] ].
      move: EMP EQs => -> /partition_emp_l EQs.
      by rewrite -EQs.
    - move=> s Ps.
      exists $0, s.
      split; [ exact: (op_id_l _) | ].
      by split.
  Qed.

  Lemma Emp_neutral_star_r: forall (P: Pred S), |- P ** $$0 <==> P.
  Proof using Type.
    move=> P s; split=> [ PEmps | Ps ].
    - by apply/Emp_neutral_star_l; apply/star_comm.
    - by apply/star_comm; apply/Emp_neutral_star_l.
  Qed.

  Lemma star_semicancel_l (P Q R: Pred S):
      stateless R ->
      (|- R ** P ===> Q) -> |- (R ** P) ===> (R ** Q).
  Proof using Type.
    move=> STATELESS IMP s RPs.
    have Qs := IMP s RPs.
    case: RPs => sr [ sp [ EQs [ Rsr Psp ] ] ].
    have EMP := STATELESS _ Rsr.
    exists sr, s.
    split; [ rewrite EMP; exact: (op_id_l _) | ].
    by split; [ exact: Rsr | exact: Qs ].
  Qed.

  Lemma star_semicancel_r (P Q R: Pred S):
      stateless R ->
      (|- P ** R ===> Q) -> |- (P ** R) ===> (Q ** R).
  Proof using Type.
    move=> STATELESS IMP s PRs.
    have Qs := IMP s PRs.
    case: PRs => sp [ sr [ EQs [ Psp Rsr ] ] ].
    have EMP := STATELESS _ Rsr.
    exists s, sr.
    split; [ rewrite EMP; exact: (op_id_r _) | ].
    by split; [ exact: Qs | exact: Rsr ].
  Qed.

  Lemma star_weaken_l (P Q R: Pred S):
      stateless Q ->
        |- P ===> R -> |- Q ** P ===> R.
  Proof using Type.
    move=> STATELESS IMP s [ sq [ sp [ EQs [ Qsq Psp ] ] ] ].
    have EMP := STATELESS sq Qsq.
    move: EMP EQs => -> /partition_emp_l EQs.
    by apply: IMP; rewrite -EQs.
  Qed.

  Lemma star_weaken_r (P Q R: Pred S):
    stateless Q ->
        |- P ===> R -> |- P ** Q ===> R.
  Proof using Type.
    move=> STATELESS IMP s [ sp [ sq [ EQs [ Psp Qsq ] ] ] ].
    have EMP := STATELESS _ Qsq.
    move: EMP EQs => -> /partition_emp_r EQs.
    by apply: IMP; rewrite -EQs.
  Qed.

  Lemma precise_star (P Q: Pred S):
    precise P -> precise Q -> precise (P ** Q).
  Proof using Type.
    move=> PRECP PRECQ s s1 s2 [ s1p [ s1q [ EQs1 [ Ps1p Qs1q ] ] ] ] [ s2p [ s2q [ EQs2 [ Ps2p Qs2q ] ] ] ] SUB1 SUB2.
    have EQs2p: s1p = s2p.
    { apply: (PRECP s s1p s2p Ps1p Ps2p).
      - exact: (substate_tran _ _ _ (substate_of_partition_l EQs1) SUB1).
      - exact: (substate_tran _ _ _ (substate_of_partition_l EQs2) SUB2). }
    have EQs2q: s1q = s2q.
    { apply: (PRECQ s s1q s2q Qs1q Qs2q).
      - exact: (substate_tran _ _ _ (substate_of_partition_r EQs1) SUB1).
      - exact: (substate_tran _ _ _ (substate_of_partition_r EQs2) SUB2). }
    move: EQs2p EQs2q EQs2 => <- <- EQs2.
    move: EQs1 EQs2 => -> EQs2.
    by case: EQs2.
  Qed.

  Lemma precise_star_inter (P Q R: Pred S):
    precise P -> |- (P ** Q) && (P ** R) ===> P ** (Q && R).
  Proof using Type.
    move=> PREC s [ [ sp [ sq [ EQs [ Psp Qsq ] ] ] ] [ sp' [ sr [ EQs' [ Psp' Rsr ] ] ] ] ].
    have EQsp': sp = sp'.
    { apply: (PREC s sp sp' Psp Psp').
      - exact: (substate_of_partition_l EQs).
      - exact: (substate_of_partition_l EQs'). }
    move: EQsp' EQs' => <- EQs'.
    have EQsr: sq = sr by exact: (op_cancel_l sp sq sr s EQs EQs').
    move: EQsr Rsr => <- Rsq.
    by exists sp, sq.
  Qed.

End Facts.
