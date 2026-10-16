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

From GallinaC.Seplog Require Import Pred.
From GallinaC.Seplog.Exists Require Import Exists.
From GallinaC.Seplog.Union Require Import Union.

Local Open Scope separation_scope.

Lemma union_intro_l [A: Type] (P Q: Pred A):
  |- P ===> P || Q.
Proof.
  by move=> s Ps; left.
Qed.
#[global] Hint Resolve union_intro_l: seplog.

Lemma union_intro_r [A: Type] (P Q: Pred A):
  |- Q ===> P || Q.
Proof.
  by move=> s Qs; right.
Qed.
#[global] Hint Resolve union_intro_r: seplog.

Lemma union_elim [A: Type] (P Q R: Pred A):
  |- P ===> R -> |- Q ===> R -> |- P || Q ===> R.
Proof.
  by move=> IMP1 IMP2 s [/IMP1 | /IMP2].
Qed.
#[global] Hint Resolve union_elim: seplog.

Lemma union_comm [A: Type] (P Q: Pred A):
  |- P || Q <==> Q || P.
Proof.
  move=> s; exact: or_comm.
Qed.
#[global] Hint Resolve union_comm: seplog.

Lemma union_assoc [A: Type] (P Q R: Pred A):
  |- (P || Q) || R <==> P || (Q || R).
Proof.
  move=> s; exact: or_assoc.
Qed.
#[global] Hint Resolve union_assoc: seplog.

Lemma Exists_union [A B: Type] (P Q: A -> Pred B):
  |- (Exists x, P x || Q x) <==> (Exists x, P x) || (Exists x, Q x).
Proof.
  move=> s; split.
  - by move=> [x [Pxs | Qxs]]; [ left | right ]; exists x.
  - by move=> [[x Pxs] | [x Qxs]]; exists x; [ left | right ].
Qed.
#[global] Hint Resolve Exists_union: seplog.
