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

Section Lift.

  Context [S: Separation.type].

  Definition lift (P: Prop) : Pred S :=
    fun s => P /\ s = $0.

  Local Notation "[| P |]" := (lift P) : separation_scope.

  #[global] Instance lift_proper: Proper (iff ==> pointwise_relation S iff) lift.
  Proof using Type.
    move=> P P' EQP s.
    by split=> -[ /EQP HP EMP ].
  Qed.

  #[global] Instance lift_proper_app: Proper (iff ==> eq ==> iff) lift.
  Proof using Type.
    move=> P P' EQP s _ <-.
    exact: lift_proper P P' EQP s.
  Qed.

  #[global] Instance lift_mono_proper: Proper (Basics.impl ==> pointwise_relation S Basics.impl) lift.
  Proof using Type.
    by move=> P P' IMPP s [ /IMPP HP EMP ].
  Qed.

  #[global] Instance lift_mono_proper_app: Proper (Basics.impl ==> eq ==> Basics.impl) lift.
  Proof using Type.
    move=> P P' IMPP s _ <-.
    exact: lift_mono_proper P P' IMPP s.
  Qed.

End Lift.

Arguments lift_proper {S}.
Arguments lift_proper_app {S}.
Arguments lift_mono_proper {S}.
Arguments lift_mono_proper_app {S}.

Notation "[| P |]" := (lift P) : separation_scope.
