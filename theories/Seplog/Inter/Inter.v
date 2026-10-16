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

Local Open Scope separation_scope.

(* Conjunction *)
Definition inter [A: Type]: Pred A -> Pred A -> Pred A := pointwise_extension and (Tcons A Tnil).
Arguments inter : simpl never.
Infix "&&" := inter (at level 40, left associativity): separation_scope.

#[global] Hint Unfold inter: seplog.

#[global] Instance inter_proper (A: Type):
  Proper (pointwise_relation A iff ==> pointwise_relation A iff ==> pointwise_relation A iff) (@inter A).
Proof.
  move=> P P' EQP R R' EQR s.
  by split=> -[/EQP Ps /EQR Rs].
Qed.

#[global] Instance inter_proper_app (A: Type):
  Proper (pointwise_relation A iff ==> pointwise_relation A iff ==> eq ==> iff) (@inter A).
Proof.
  move=> P P' EQP R R' EQR s _ <-.
  exact: inter_proper A P P' EQP R R' EQR s.
Qed.

#[global] Instance inter_mono_proper (A: Type):
  Proper (pointwise_relation A Basics.impl ==> pointwise_relation A Basics.impl ==> pointwise_relation A Basics.impl) (@inter A).
Proof.
  by move=> P P' IMPP R R' IMPR s [ /IMPP Ps /IMPR Rs ].
Qed.

#[global] Instance inter_mono_proper_app (A: Type):
  Proper (pointwise_relation A Basics.impl ==> pointwise_relation A Basics.impl ==> eq ==> Basics.impl) (@inter A).
Proof.
  move=> P P' IMPP R R' IMPR s _ <-.
  exact: inter_mono_proper A P P' IMPP R R' IMPR s.
Qed.
