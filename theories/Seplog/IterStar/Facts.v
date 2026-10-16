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

From Stdlib Require Import Permutation.

From GallinaC.Utils Require Import Algebra ListExt.
From GallinaC.Seplog Require Import Pred.
From GallinaC.Seplog.Emp Require Import Emp.
From GallinaC.Seplog.Star Require Import Star Facts.
From GallinaC.Seplog.IterStar Require Import IterStar.

Local Open Scope separation_scope.

Section Facts.

  Context [S: Separation.type].

  Lemma iter_star_nil [X: Type] (P: X -> Pred S):
    iter_star P [] = $$0.
  Proof using Type.
    reflexivity.
  Qed.

  Lemma iter_star_mono [X: Type] (P Q: X -> Pred S) (l: list X):
    (forall x, In x l -> |- P x ===> Q x) -> |- iter_star P l ===> iter_star Q l.
  Proof using Type.
    elim: l => [ | x l IH ] IMP s //=.
    move=> [ sp [ sip [ EQs [ Pxsp IPsip ] ] ] ].
    exists sp, sip; split; first exact: EQs.
    split; first exact: (IMP x (or_introl eq_refl) sp Pxsp).
    exact: (IH (fun y INy => IMP y (or_intror INy)) sip IPsip).
  Qed.

  Lemma iter_star_perm [X: Type] (P: X -> Pred S) (l1 l2: list X):
    Permutation l1 l2 -> |- iter_star P l1 <==> iter_star P l2.
  Proof using Type.
    elim=> [ | x l l' _ IH | x y l | l l' l'' _ IH1 _ IH2 ] /=.
    - reflexivity.
    - rewrite IH.
      reflexivity.
    - rewrite (star_swap (P y) (P x)).
      reflexivity.
    - rewrite IH1.
      exact: IH2.
  Qed.

  Lemma iter_star_map [X Y: Type] (P: Y -> Pred S) (f: X -> Y) (l: list X):
    iter_star P (map f l) = (Iter x in l, P (f x)).
  Proof using Type.
    elim: l => [ | x l IH ] //=.
    by rewrite IH.
  Qed.

  Lemma iter_star_cons [X: Type] (P: X -> Pred S) (a: X) (l: list X):
    iter_star P (a :: l) = P a ** iter_star P l.
  Proof using Type.
    reflexivity.
  Qed.

  Lemma iter_star_app [X: Type] (P: X -> Pred S) (l1 l2: list X):
    |- iter_star P (l1 ++ l2) <==> iter_star P l1 ** iter_star P l2.
  Proof using Type.
    elim: l1 => [ | x l1 IH ] /=.
    - rewrite Emp_neutral_star_l.
      reflexivity.
    - rewrite IH star_assoc.
      reflexivity.
  Qed.

  Lemma iter_star_star [X: Type] (P Q: X -> Pred S) (l: list X):
    |- (Iter x in l, P x ** Q x) <==> iter_star P l ** iter_star Q l.
  Proof using Type.
    elim: l => [ | x l IH ] /=.
    - rewrite Emp_neutral_star_l.
      reflexivity.
    - rewrite IH (star_assoc (P x) (Q x)).
      rewrite -(star_assoc (Q x) (Iter y in l, P y)) (star_comm (Q x) (Iter y in l, P y)).
      rewrite (star_assoc (Iter y in l, P y) (Q x)) -(star_assoc (P x) (Iter y in l, P y)).
      reflexivity.
  Qed.

End Facts.
