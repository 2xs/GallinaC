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
From HB Require Import structures.

From Stdlib Require Import Bool.

From GallinaC.Utils Require Import Algebra.
Export ssrfun.Option.

Definition isSome := @ssrbool.isSome.
Arguments isSome {A} o: rename.

Section Eqb.

  Definition option_eqb [A: Type] (eqb: A -> A -> bool) (x y: option A): bool :=
    match x, y with
    | Some x, Some y => eqb x y
    | None, None => true
    | _, _ => false
    end.

  Lemma option_eqb_refl [A: Type] [eqb: A -> A -> bool] (eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y)): forall o, option_eqb eqb o o = true.
  Proof.
    destruct o; [ | reflexivity ].
    cbn.
    destruct (eqb_spec a a); [ reflexivity | contradiction ].
  Qed.


  Lemma option_eqb_spec [A: Type] [eqb: A -> A -> bool] (eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y)): forall x y , Bool.reflect (x = y) (option_eqb eqb x y).
  Proof.
    destruct x, y; try (constructor; congruence).
    cbn.
    destruct (eqb_spec a a0); constructor; congruence.
  Qed.

End Eqb.

HB.instance Definition _ (A: EqDec.type) :=
  hasEqDec.Build (option A) (option_eqb (@Algebra.eqb A)) (option_eqb_spec (@Algebra.eqb_spec A)).

#[global] Hint Resolve option_eqb_refl: datatypes.
#[global] Hint Resolve option_eqb_spec: datatypes.

Definition option_min [A: Type] (min: A -> A -> A) (o1 o2: option A): option A :=
  match o1, o2 with
  | None, o | o, None => o
  | Some a1, Some a2 => Some (min a1 a2)
  end.

Lemma option_ext [A: Type] (o1 o2: option A)
  (H: forall a, o1 = Some a <-> o2 = Some a)
  : o1 = o2.
Proof.
  case: o1 H => [a1|] H.
  - by rewrite -(proj1 (H a1) erefl).
  - case: o2 H => [a2|] H //.
    by move: (proj2 (H a2) erefl).
Qed.

Lemma Some_congr [A: Type] [o: option A] [x y: A]
  (EQx: o = Some x) (EQy: o = Some y)
  : x = y.
Proof.
  rewrite EQx in EQy.
  by case: EQy.
Qed.

Lemma bind_some [A B: Type] (f: A -> option B) (x: A): bind f (Some x) = f x.
Proof.
  by [].
Qed.

Lemma bind_none [A B: Type] (f: A -> option B): bind f None = None.
Proof.
  by [].
Qed.
