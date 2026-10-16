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

From Stdlib Require Import ZArith.

From compcert.common Require AST.

From GallinaC.Utils Require Import Algebra.

From GallinaC.Compiler.Common Require Export Prog.
From GallinaC.Compiler.IR Require Import Cmd.

Record f_extra :=
  {
    (* Stack usage in GallinaC memory words *)
    fn_stackspace: Z;
  }.

Definition f_extra_eqb (x y: f_extra): bool :=
  Z.eqb x.(fn_stackspace) y.(fn_stackspace).

Lemma f_extra_eqb_spec: forall x y, Bool.reflect (x = y) (f_extra_eqb x y).
Proof.
  destruct x as [ sz1 ], y as [ sz2 ]; unfold f_extra_eqb; cbn.
  destruct (Z.eqb_spec sz1 sz2); constructor; congruence.
Qed.

HB.instance Definition _ := hasEqDec.Build f_extra f_extra_eqb f_extra_eqb_spec.

Notation function := (function cmd f_extra).

Notation fundef := (fundef cmd f_extra).

Notation globdef := (globdef cmd f_extra).

Definition p_extra : Type := unit.

Notation program := (program cmd f_extra p_extra).

Notation genv := (genv cmd f_extra).
