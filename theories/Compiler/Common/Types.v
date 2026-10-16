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

From Stdlib Require Import PArith NArith Arith List Psatz.
Import ListNotations.

From compcert.common Require AST.

From GallinaC.Utils Require ListExt ReflectExt.
From GallinaC.Utils Require Import Algebra.

Create HintDb deep_gallinac.

Inductive type: Set :=
| t_unit
| t_bool
| t_nat
| t_ofst
| t_ptr
.

Definition type_eqb (t1 t2: type): bool :=
  match t1, t2 with
  | t_unit, t_unit => true
  | t_bool, t_bool => true
  | t_nat, t_nat => true
  | t_ofst, t_ofst => true
  | t_ptr, t_ptr => true
  | _,_ => false
  end.

Lemma type_eqb_spec: forall (x y: type), Bool.reflect (x = y) (type_eqb x y).
Proof.
  destruct x, y; now constructor.
Defined.

HB.instance Definition _ := hasEqDec.Build type type_eqb type_eqb_spec.

Inductive Sized: type -> Prop :=
| sized_bool: Sized t_bool
| sized_nat: Sized t_nat
| sized_ofst: Sized t_ofst
| sized_ptr: Sized t_ptr
.
#[global] Hint Constructors Sized: deep_gallinac.

Definition sized (t: type): bool :=
  match t with
  | t_unit => false
  | t_bool => true
  | t_nat => true
  | t_ofst => true
  | t_ptr => true
  end.

Lemma sized_spec: forall t, Bool.reflect (Sized t) (sized t).
Proof.
  destruct t; constructor; try constructor; intros contra; inversion contra.
Qed.
