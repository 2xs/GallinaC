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
From GallinaC.Seplog.Star Require Import Star.
From GallinaC.Seplog.Intuitionistic Require Import Intuitionistic.
From GallinaC.Seplog.Upclose Require Import Upclose.

Local Open Scope separation_scope.

Section Facts.

  Context [S: Separation.type].

  Lemma upclose_intro (P: Pred S):
    |- P ===> upclose P.
  Proof using Type.
    move=> s Ps.
    exists s, $0.
    split; [ exact: (op_id_r _) | ].
    by split.
  Qed.

  Lemma upclose_idem (P: Pred S):
    |- upclose (upclose P) <==> upclose P.
  Proof using Type.
    apply: impl_antisym_taut.
    - move=> s [ sup [ s1 [ EQs [ [ sp [ s2 [ EQsup [ Psp _ ] ] ] ] _ ] ] ] ].
      case: (partition_assoc EQsup EQs) => s3 [ _ EQs' ].
      by exists sp, s3.
    - exact: upclose_intro.
  Qed.

  Lemma upclose_substate (P: Pred S):
    forall s, upclose P s <-> exists sp, sp $<= s /\ P sp.
  Proof using Type.
    move=> s.
    split.
    - move=> [ sp [ s1 [ EQs [ Psp _ ] ] ] ].
      exists sp.
      split; [ exact: (substate_of_partition_l EQs) | exact: Psp ].
    - move=> [ sp [ [ s1 EQs ] Psp ] ].
      by exists sp, s1.
  Qed.

  Lemma upclose_intuitionistic (P: Pred S):
    intuitionistic (upclose P).
  Proof using Type.
    exact: upclose_idem P.
  Qed.

  Lemma upclose_star (P Q: Pred S):
    |- upclose P ** upclose Q ===> upclose (P ** Q).
  Proof using Type.
    move=> s [ sup [ suq [ EQs [ [ sp [ s1 [ EQsup [ Psp _ ] ] ] ] [ sq [ s2 [ EQsuq [ Qsq _ ] ] ] ] ] ] ] ].
    case: (partition_assoc EQsup EQs) => s3 [ EQs3 EQs' ].
    case: (partition_assoc EQsuq (partition_comm EQs3)) => s4 [ _ EQs3' ].
    case: (partition_assoc_rev EQs3' EQs') => spq [ EQspq EQs'' ].
    exists spq, s4.
    split; first by [].
    split; last by [].
    by exists sp, sq.
  Qed.

End Facts.
