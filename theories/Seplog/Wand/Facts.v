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
From GallinaC.Seplog.Wand Require Import Wand.

Local Open Scope separation_scope.

Section Facts.

  Context [S: Separation.type].

  Lemma wand_intro (P Q R: Pred S):
      |- (P ** Q) ===> R -> |- P ===> (Q -* R).
  Proof using Type.
    move=> IMP s Ps sq sr Qsq EQsr.
    apply: IMP.
    exists s, sq.
    split; [ exact: EQsr | ].
    by split.
  Qed.

  Lemma wand_elim (P Q R: Pred S):
        |- P ===> (Q -* R) -> |- (P ** Q) ===> R.
  Proof using Type.
    move=> IMP s [ sp [ sq [ EQs [ Psp Qsq ] ] ] ].
    exact: (IMP sp Psp sq s Qsq EQs).
  Qed.

  Lemma star_wand_mp (P Q: Pred S):
        |- P ** (P -* Q) ===> Q.
  Proof using Type.
    move=> s [ sp [ sw [ EQs [ Psp WAND ] ] ] ].
    exact: (WAND sp s Psp (partition_comm EQs)).
  Qed.

End Facts.
