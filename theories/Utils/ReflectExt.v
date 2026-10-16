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

From Stdlib Require Export Bool.

(** * Additional facts and utilities for [reflect]

Note that in this file, numerous definitions are closed using [Defined] and not
[Qed]. This is done on purpose. These lemmas are (among others) used in the
denotation and semantic equivalence modules to bridge the gap between
computational and proof values. Hence, they must remain transparent for
evaluation purposes. As these proofs are not complex anyway (the complexity
resides in the definitions of [eqb] and their [Bool.reflect] proofs), this is
(for now), not a problem either.

 *)

Definition sumbool_of_reflect [A B: Type] [P: A -> B -> Prop] [f: A -> B -> bool] (REFLECT: forall a b, Bool.reflect (P a b) (f a b)) a b : { P a b } + { ~P a b }.
Proof.
  now destruct (REFLECT a b); constructor.
Defined.
#[global] Hint Resolve sumbool_of_reflect: bool.


Definition reflect_refl {A: Type} {eqb: A -> A -> bool} (REFLECT: forall (x y: A), Bool.reflect (x = y) (eqb x y)) (x: A): eqb x x = true.
Proof.
  destruct (REFLECT x x) as [EQ | NE]; [ | exfalso; apply NE ]; reflexivity.
Defined.
#[global] Hint Resolve reflect_refl: bool.

Lemma reflect_sym {A: Type} {eqb: A -> A -> bool} (REFLECT: forall (x y: A), reflect (x = y) (eqb x y)) x y: eqb x y = eqb y x.
Proof.
  destruct (REFLECT x y) as [ EQ1 | NE1 ];
    destruct (REFLECT y x) as [ EQ2 | NE2 ];
    congruence.
Defined.
#[global] Hint Resolve reflect_sym: bool.

Lemma reflect_trans {A: Type} {eqb: A -> A -> bool} (REFLECT: forall (x y: A), reflect (x = y) (eqb x y)) {x y z} (EQBxy: eqb x y = true) (EQXyz: eqb y z = true): eqb x z = true.
Proof.
  destruct (REFLECT x y) as [ EQxy | NExy ];
    destruct (REFLECT y z) as [ EQyz | NEyz ];
    destruct (REFLECT x z) as [ EQxz | NExz ];
    congruence.
Defined.
#[global] Hint Resolve reflect_trans: bool.

Lemma eq_dec_refl_if {A: Type} (eq_dec: forall (x y: A), { x = y } + { x <> y }): forall (x: A), (if eq_dec x x then true else false) = true.
  intros x. destruct (eq_dec x x); subst; congruence.
Defined.
#[global] Hint Resolve eq_dec_refl_if: bool.

Lemma reflect_eq_of_true {A: Type} {eqb: A -> A -> bool} (REFLECT: forall (x y: A), reflect (x = y) (eqb x y)) {x y} (EQ: eqb x y = true): x = y.
Proof.
  now destruct (REFLECT x y).
Defined.

Lemma reflect_true_of_prop [P: Prop] [b: bool] (REFLECT: reflect P b) (HP: P): b = true.
Proof.
  destruct REFLECT; [ reflexivity | contradiction ].
Qed.

(* Computational rewrite. If two types [A] and [B] are equal, then one term of
type [A] can be rewritten into a term of type [B]. *)
Definition convert_eq [A B: Type] (EQ: A = B) (a: A) : B :=
  match EQ with eq_refl => a end.

(* Future work: convert_eq can be defined using rewrite <- EQ, i.e. just a direct [eq_rect] term.
  Consider reworking proofs in Agree and Denotation to use this instead *)
(* Definition convert_eq [A B: Type] (EQ: A = B) (a: A) : B. *)
(*   rewrite <- EQ. *)
(*   exact a. *)
(* Defined. *)
