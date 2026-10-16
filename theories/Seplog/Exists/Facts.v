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

Local Open Scope separation_scope.

Lemma Exists_impl [A B: Type] s: forall (p: Pred A) (q: B -> Pred A),
    (Exists x, p ===> q x) s  -> (p ===> Exists x, q x) s.
Proof.
  move=> p q [ x IMPx ] ps.
  by exists x; apply: IMPx.
Qed.
#[global] Hint Resolve Exists_impl: seplog.

Lemma Exists_impl_taut [A B: Type]: forall (p: Pred A) (q: B -> Pred A),
    all (Exists x, p ===> q x)  -> |- p ===> Exists x, q x.
Proof.
  move=> p q IMP s ps.
  case: (IMP s) => x IMPx.
  by exists x; apply: IMPx.
Qed.
#[global] Hint Resolve Exists_impl_taut: seplog.

Lemma skolem_left [A B: Type] s: forall (p: B ->Pred A) (q: Pred A),
    (forall x, (p x ===> q) s) -> ((Exists x, p x) ===> q) s.
Proof.
  move=> p q IMP [ x Pxs ].
  by apply: (IMP x).
Qed.
#[global] Hint Resolve skolem_left: seplog.

Lemma skolem_left_taut[A B: Type]: forall (p: B ->Pred A)
                                     (q: Pred A),
    (forall x, |- p x ===> q) -> |- (Exists x, p x) ===> q.
Proof.
  move=> p q IMP s [ x Pxs ].
  by apply: (IMP x).
Qed.
#[global] Hint Resolve skolem_left_taut: seplog.

Lemma inst_Exists [A B: Type] s:
  forall (P: B -> Pred A),
  forall x, (P x s) -> (Exists x, P x) s.
Proof.
  move=> P x Pxs.
  by exists x.
Qed.
#[global] Hint Resolve inst_Exists: seplog.

Lemma inst_Exists_taut [A B: Type]:
  forall (P: B -> Pred A),
  forall x, all (P x) -> all (Exists x, P x).
Proof.
  move=> P x Px s.
  by exists x.
Qed.
#[global] Hint Resolve inst_Exists_taut: seplog.

Lemma swap_Exists [A B:Type] (p: B -> B -> Pred A):
  |- (Exists x y, p x y) <==> Exists y x, p x y .
Proof.
  apply: impl_antisym_taut => s [ x [ y Pxys ] ];
    by exists y, x.
Qed.
#[global] Hint Resolve swap_Exists: seplog.
