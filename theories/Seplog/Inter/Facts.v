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
From GallinaC.Seplog.Inter Require Import Inter.

Local Open Scope separation_scope.

Lemma inter_pair [A s] (P Q: Pred A): P s -> Q s -> (P && Q) s.
Proof.
  by move=> Ps Qs; split.
Qed.
#[global] Hint Resolve inter_pair: seplog.

Lemma inter_split [A s] (P: Pred A): (P && P) s -> P s.
Proof.
  by move=> [ Ps _ ].
Qed.
#[global] Hint Extern 4 => apply inter_split : seplog.

Lemma inter_split_l [A s] (P Q: Pred A): (P && Q) s -> P s.
Proof.
  by move=> [ Ps _ ].
Qed.
#[global] Hint Extern 4 => apply inter_split_l : seplog.

Lemma inter_split_r [A s] (P Q: Pred A): (P && Q) s -> Q s.
Proof.
  by move=> [ _ Qs ].
Qed.
#[global] Hint Extern 4 => apply inter_split_r : seplog.

Lemma inter_sym [A s] (P Q: Pred A): (P && Q) s -> (Q && P) s.
Proof.
  by move=> [ Ps Qs ]; split.
Qed.
#[global] Hint Resolve inter_sym: seplog.

Lemma inter_trans [A s] (P Q R: Pred A): (P && Q) s -> (Q && R) s -> (P && R) s.
Proof.
  by move=> [ Ps _ ] [ _ Rs ]; split.
Qed.
#[global] Hint Resolve inter_trans: seplog.

Lemma impl_cnj_right [A: Type] s :
  forall (p q r: Pred A),
    (p  ===> q) s -> (p ===> r) s  -> (p ===> q && r) s.
Proof.
  move=> p q r IMP1 IMP2 ps; split;
    [ exact: IMP1 | exact: IMP2 ].
Qed.
#[global] Hint Resolve impl_cnj_right: seplog.

Lemma impl_cnj_right_taut [A: Type] :
  forall (p q r: Pred A),
    |-  p  ===> q -> |- p ===>  r  -> |- p ===> q && r.
Proof.
  move=> p q r IMP1 IMP2 s ps; split;
    [ exact: IMP1 | exact: IMP2 ].
Qed.
#[global] Hint Resolve impl_cnj_right_taut: seplog.
