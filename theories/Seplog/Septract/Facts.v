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
From GallinaC.Seplog.Precise Require Import Precise.
From GallinaC.Seplog.Star Require Import Star.
From GallinaC.Seplog.Upclose Require Import Upclose.
From GallinaC.Seplog.Wand Require Import Wand.
From GallinaC.Seplog.Septract Require Import Septract.

Local Open Scope separation_scope.

Section Facts.

  Context [S: Separation.type].

  Lemma septract_wand_dual (P Q: Pred S):
    |- (P -** Q) ===> neg (P -* neg Q).
  Proof using Type.
    move=> s [ sp [ sq [ Psp [ EQsq Qsq ] ] ] ] WAND.
    exact: (WAND sp sq Psp EQsq Qsq).
  Qed.

  Lemma septract_star_precise (P R: Pred S):
    precise P -> |- (P -** (P ** R)) ===> R.
  Proof using Type.
    move=> PREC s [ sp [ spr [ Psp [ EQspr [ sp' [ s' [ EQspr' [ Psp' Rs' ] ] ] ] ] ] ] ].
    have EQsp': sp = sp'.
    { apply: (PREC spr sp sp' Psp Psp').
      - exact: (substate_of_partition_r EQspr).
      - exact: (substate_of_partition_l EQspr'). }
    move: EQsp' EQspr' => <- EQspr'.
    have EQs': s = s'.
    { apply: (op_cancel_r sp s s' spr EQspr).
      exact: partition_comm. }
    by rewrite EQs'.
  Qed.

  Lemma upclose_septract_split (P R: Pred S):
    |- R ===> upclose P -> |- R ===> P ** (P -** R).
  Proof using Type.
    move=> UP s Rs.
    case: (UP s Rs) => [ sp [ s1 [ EQs [ Psp _ ] ] ] ].
    exists sp, s1.
    split; first exact: EQs.
    split; first exact: Psp.
    exists sp, s.
    split; first exact: Psp.
    split; last exact: Rs.
    exact: partition_comm.
  Qed.

End Facts.
