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

From GallinaC.Utils Require Import Algebra.
From GallinaC.Seplog Require Import Pred.

Local Open Scope separation_scope.

Section Septract.

  Context [S: Separation.type].

  Definition septract (P Q: Pred S): Pred S :=
    fun s => exists sp sq, P sp /\ s $+ sp = Some sq /\ Q sq.

  Local Infix "-**" := septract (at level 70, right associativity): separation_scope.

  #[global] Instance septract_proper:
    Proper (pointwise_relation S iff ==> pointwise_relation S iff ==> pointwise_relation S iff) septract.
  Proof using Type.
    move=> P P' EQP Q Q' EQQ s.
    by split=> -[ sp [ sq [ /EQP Psp [ EQsq /EQQ Qsq ] ] ] ]; exists sp, sq.
  Qed.

  #[global] Instance septract_proper_app:
    Proper (pointwise_relation S iff ==> pointwise_relation S iff ==> eq ==> iff) septract.
  Proof using Type.
    move=> P P' EQP Q Q' EQQ s _ <-.
    exact: septract_proper P P' EQP Q Q' EQQ s.
  Qed.

  #[global] Instance septract_mono_proper:
    Proper (pointwise_relation S Basics.impl ==> pointwise_relation S Basics.impl ==> pointwise_relation S Basics.impl) septract.
  Proof using Type.
    move=> P P' IMPP Q Q' IMPQ s [ sp [ sq [ /IMPP Psp [ EQsq /IMPQ Qsq ] ] ] ].
    by exists sp, sq.
  Qed.

  #[global] Instance septract_mono_proper_app:
    Proper (pointwise_relation S Basics.impl ==> pointwise_relation S Basics.impl ==> eq ==> Basics.impl) septract.
  Proof using Type.
    move=> P P' IMPP Q Q' IMPQ s _ <-.
    exact: septract_mono_proper P P' IMPP Q Q' IMPQ s.
  Qed.

End Septract.

Arguments septract_proper {S}.
Arguments septract_proper_app {S}.
Arguments septract_mono_proper {S}.
Arguments septract_mono_proper_app {S}.

Infix "-**" := septract (at level 70, right associativity): separation_scope.
