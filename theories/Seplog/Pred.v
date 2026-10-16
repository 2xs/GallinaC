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

Require Export Setoid.
Require Export Relation_Definitions.

From Stdlib Require Export Morphisms.

From GallinaC.Corec Require Export Sets.
From GallinaC.Utils Require Import Algebra.

Local Open Scope separation_scope.

Definition Pred (A:Type) := Setof A.

(* Implication *)
Definition impl [A: Type]: Pred A -> Pred A -> Pred A := pointwise_extension Basics.impl (Tcons A Tnil).
Arguments impl : simpl never.
Infix "===>" := impl (at level 70, right associativity): separation_scope.

Lemma impl_impl_1 [A s] (P Q: Pred A): (P s -> Q s) -> (P ===> Q) s.
Proof.
  by move=> IMP.
Qed.
#[global] Hint Resolve impl_impl_1: seplog.

Lemma impl_impl_2 [A s] (P Q: Pred A): (P ===> Q) s -> P s -> Q s.
Proof.
  by move=> IMP /IMP.
Qed.
#[global] Hint Extern 4 => apply impl_impl_2: seplog.

Lemma impl_refl [A s] (P: Pred A): (P ===> P) s.
Proof.
  by move=> Ps.
Qed.
#[global] Hint Resolve impl_refl: seplog.

Lemma impl_trans [A s] (P Q R: Pred A): (P ===> Q) s -> (Q ===> R) s -> (P ===> R) s.
Proof.
  by move=> IMP1 IMP2 /IMP1 /IMP2.
Qed.
#[global] Hint Resolve impl_trans: seplog.

#[global] Instance impl_proper (A: Type):
  Proper (pointwise_relation A iff ==> pointwise_relation A iff ==> pointwise_relation A iff) (@Pred.impl A).
Proof.
  move=> P P' EQP R R' EQR s.
  by split=> IMP /EQP /IMP /EQR.
Qed.

#[global] Instance impl_proper_app (A: Type):
  Proper (pointwise_relation A iff ==> pointwise_relation A iff ==> eq ==> iff) (@Pred.impl A).
Proof.
  move=> P P' EQP R R' EQR s _ <-.
  exact: impl_proper A P P' EQP R R' EQR s.
Qed.

#[global] Instance impl_mono_proper (A: Type):
  Proper (pointwise_relation A Basics.impl --> pointwise_relation A Basics.impl ==> pointwise_relation A Basics.impl) (@Pred.impl A).
Proof.
  by move=> P P' IMPP R R' IMPR s IMP /IMPP /IMP /IMPR.
Qed.

#[global] Instance impl_mono_proper_app (A: Type):
  Proper (pointwise_relation A Basics.impl --> pointwise_relation A Basics.impl ==> eq ==> Basics.impl) (@Pred.impl A).
Proof.
  move=> P P' IMPP R R' IMPR s _ <-.
  exact: impl_mono_proper A P P' IMPP R R' IMPR s.
Qed.

(* Equivalence *)
Definition equiv [A: Type]: Pred A -> Pred A -> Pred A := pointwise_extension iff (Tcons A Tnil).
Arguments equiv : simpl never.
Infix "<==>" := equiv (at level 75): separation_scope.

Lemma equiv_impl_l [A s] (P Q: Pred A): (P <==> Q) s -> (P ===> Q) s.
Proof.
  by move=> [ IMP _ ].
Qed.
#[global] Hint Resolve equiv_impl_l: seplog.

Lemma equiv_impl_r [A s] (P Q: Pred A): (P <==> Q) s -> (Q ===> P) s.
Proof.
  by move=> [ _ IMP ].
Qed.
#[global] Hint Resolve equiv_impl_r: seplog.

Lemma equiv_refl [A s] (P: Pred A): (P <==> P) s.
Proof.
  by split.
Qed.
#[global] Hint Resolve equiv_refl: seplog.

Lemma equiv_sym [A s] (P Q: Pred A): (P <==> Q) s -> (Q <==> P) s.
Proof.
  by move=> [ IMP1 IMP2 ]; split.
Qed.
#[global] Hint Resolve equiv_sym: seplog.

Lemma equiv_trans [A s] (P Q R: Pred A): (P <==> Q) s -> (Q <==> R) s -> (P <==> R) s.
Proof.
  move=> [ IMP1 IMP2 ] [ IMP3 IMP4 ].
  by split=> [ /IMP1 /IMP3 | /IMP4 /IMP2 ].
Qed.
#[global] Hint Resolve equiv_trans: seplog.

#[global] Instance equiv_proper (A: Type):
  Proper (pointwise_relation A iff ==> pointwise_relation A iff ==> pointwise_relation A iff) (@Pred.equiv A).
Proof.
  move=> P P' EQP R R' EQR s.
  by split=> -[IMP1 IMP2]; split=> [/EQP /IMP1 /EQR | /EQR /IMP2 /EQP].
Qed.

#[global] Instance equiv_proper_app (A: Type):
  Proper (pointwise_relation A iff ==> pointwise_relation A iff ==> eq ==> iff) (@Pred.equiv A).
Proof.
  move=> P P' EQP R R' EQR s _ <-.
  exact: equiv_proper A P P' EQP R R' EQR s.
Qed.

Notation "|- P ===> Q" := (pointwise_relation _ Basics.impl P Q) (at level 80, P at level 69, Q at level 70): separation_scope.
Notation "|- P <==> Q" := (pointwise_relation _ iff P Q) (at level 80, P at level 69, Q at level 74): separation_scope.
(* Uncomment to allow arbitrary quantified predicates.
   Note: This means that [|- P <==> Q] and [|- (P <==> Q)] denote convertible, but syntactically different terms. The second is not compatible with Rocq's rewrite system. *)
(* Notation "|- P" := (all P) (at level 80, P at level 69): separation_scope. *)

#[global] Instance pointwise_impl_proper (A: Type):
  Proper (pointwise_relation A iff ==> pointwise_relation A iff ==> iff) (pointwise_relation A Basics.impl).
Proof.
  move=> P P' EQP Q Q' EQQ.
  by split=> IMP s /EQP /IMP /EQQ.
Qed.

Lemma impl_refl_eq [A:Type] (p q : Pred A):
  p = q ->
      |- p ===> q.
Proof.
  by move=> -> s.
Qed.
#[global] Hint Resolve impl_refl_eq: seplog.

Lemma impl_refl_taut [A: Type] (P: Pred A):
      |- P ===> P.
Proof.
  by move=> s.
Qed.
#[global] Hint Resolve impl_refl_taut: seplog.

Lemma impl_trans_taut [A:Type] (p q r: Pred A) :
      |- p ===> q -> |- q ===> r -> |- p ===> r.
Proof.
  by move=> IMP1 IMP2 s /IMP1 /IMP2.
Qed.
#[global] Hint Resolve impl_trans_taut: seplog.

Lemma impl_antisym [A: Type] s (p q: Pred A):
  (p ===> q) s -> (q ===> p) s -> (p <==> q) s.
Proof.
  by move=> IMP1 IMP2; split.
Qed.
#[global] Hint Resolve impl_antisym: seplog.

Lemma impl_antisym_taut [A:Type] (p q: Pred A) :
      |- p ===> q -> |- q ===> p -> |- p <==> q.
Proof.
  move=> IMP1 IMP2 s.
  by split; [ apply: IMP1 | apply: IMP2 ].
Qed.
#[global] Hint Resolve impl_antisym_taut: seplog.

Lemma equiv_refl_eq [A: Type] (p q: Pred A):
  p = q -> |- p <==> q.
Proof.
  by move=> -> s.
Qed.
#[global] Hint Resolve equiv_refl_eq: seplog.

Lemma equiv_refl_taut [A: Type] (P: Pred A):
      |- P <==> P.
Proof.
  by move=> s.
Qed.
#[global] Hint Resolve equiv_refl_taut: seplog.

Lemma equiv_sym_taut [A: Type] (P Q: Pred A):
  (|- P <==> Q) -> (|- Q <==> P).
Proof.
  move=> EQV s.
  exact: iff_sym (EQV s).
Qed.
#[global] Hint Resolve equiv_sym_taut: seplog.

Lemma equiv_trans_taut [A: Type] (P Q R: Pred A):
  (|- P <==> Q) -> (|- Q <==> R) -> (|- P <==> R).
Proof.
  move=> EQV1 EQV2 s.
  exact: iff_trans (EQV1 s) (EQV2 s).
Qed.
#[global] Hint Resolve equiv_trans_taut: seplog.

(* Top *)
Notation top := (Basics.const True).

Lemma top_intro [A: Type] (P: Pred A):
  |- P ===> top.
Proof.
  by [].
Qed.
#[global] Hint Resolve top_intro: seplog.

(* Negation *)
Definition neg [A: Type] (P: Pred A): Pred A := impl P (Basics.const False).
Arguments neg : simpl never.

#[global] Instance neg_proper (A: Type):
  Proper (pointwise_relation A iff ==> pointwise_relation A iff) (@neg A).
Proof.
  move=> P P' EQP.
  exact: impl_proper A P P' EQP (Basics.const False) (Basics.const False) (fun _ => iff_refl False).
Qed.

#[global] Instance neg_proper_app (A: Type):
  Proper (pointwise_relation A iff ==> eq ==> iff) (@neg A).
Proof.
  move=> P P' EQP s _ <-.
  exact: neg_proper A P P' EQP s.
Qed.

#[global] Instance neg_mono_proper (A: Type):
  Proper (pointwise_relation A Basics.impl --> pointwise_relation A Basics.impl) (@neg A).
Proof.
  move=> P P' IMPP.
  exact: impl_mono_proper A P P' IMPP (Basics.const False) (Basics.const False) (impl_refl_taut (Basics.const False)).
Qed.

#[global] Instance neg_mono_proper_app (A: Type):
  Proper (pointwise_relation A Basics.impl --> eq ==> Basics.impl) (@neg A).
Proof.
  move=> P P' IMPP s _ <-.
  exact: neg_mono_proper A P P' IMPP s.
Qed.

#[global] Instance under_rel_proper {T: Type} {R: relation T} `{Equivalence T R}:
  Proper (R ==> R ==> iff) (Under_rel T R).
Proof.
  move=> X Y EQXY X' Y' EQXY'.
  by rewrite !Under_relE EQXY EQXY'.
Qed.
