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

From GallinaC.Utils Require Import Algebra ListExt.
From GallinaC.Seplog Require Import Pred.
From GallinaC.Seplog.Emp Require Import Emp.
From GallinaC.Seplog.Star Require Import Star.

Local Open Scope separation_scope.

Section IterStar.

  Context [S: Separation.type].

  Fixpoint iter_star {X: Type} (P: X -> Pred S) (l: list X): Pred S :=
    match l with
    | [] => $$0
    | x :: l' => P x ** iter_star P l'
    end.

  Local Notation "'Iter' x 'in' l , p" := (iter_star (fun x => p) l) (at level 200, x binder, l at level 200, right associativity): separation_scope.

  #[global] Instance iter_star_proper (X: Type):
    Proper (pointwise_relation X (pointwise_relation S iff) ==> eq ==> pointwise_relation S iff) (@iter_star X).
  Proof using Type.
    move=> P P' EQP l _ <-.
    elim: l => [ | x l IH ].
    - move=> s.
      reflexivity.
    - exact: star_proper (P x) (P' x) (EQP x) (iter_star P l) (iter_star P' l) IH.
  Qed.

  #[global] Instance iter_star_proper_app (X: Type):
    Proper (pointwise_relation X (pointwise_relation S iff) ==> eq ==> eq ==> iff) (@iter_star X).
  Proof using Type.
    move=> P P' EQP l l' EQL s _ <-.
    exact: iter_star_proper X P P' EQP l l' EQL s.
  Qed.

  #[global] Instance iter_star_mono_proper (X: Type):
    Proper (pointwise_relation X (pointwise_relation S Basics.impl) ==> eq ==> pointwise_relation S Basics.impl) (@iter_star X).
  Proof using Type.
    move=> P P' IMPP l _ <-.
    elim: l => [ | x l IH ].
    - move=> s.
      reflexivity.
    - exact: star_mono_proper (P x) (P' x) (IMPP x) (iter_star P l) (iter_star P' l) IH.
  Qed.

  #[global] Instance iter_star_mono_proper_app (X: Type):
    Proper (pointwise_relation X (pointwise_relation S Basics.impl) ==> eq ==> eq ==> Basics.impl) (@iter_star X).
  Proof using Type.
    move=> P P' IMPP l l' EQL s _ <-.
    exact: iter_star_mono_proper X P P' IMPP l l' EQL s.
  Qed.

End IterStar.

Notation "'Iter' x 'in' l , p" := (iter_star (fun x => p) l) (at level 200, x binder, l at level 200, right associativity): separation_scope.
