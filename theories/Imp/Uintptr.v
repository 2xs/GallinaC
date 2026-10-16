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

From Stdlib Require Import ZArith NArith Psatz.

From GallinaC.Utils Require NExt.
From GallinaC.Imp Require Export Intops.

From compcert Require Archi Integers.

Local Open Scope N_scope.

Module NCarrier.

  Import Intops.IntCarrier.

  Local Obligation Tactic := try (lia).

  #[local] Remark le_lt_conv: forall a b, N.succ a <= b <-> a < b.
  Proof.
    intros; split; intros; lia.
  Qed.

  Program Definition n_int_carrier : IntCarrier.IntCarrier :=
    {|
      carrier := N;
      to_Z := Z.of_N;
      of_Z := Z.to_N;

      le := N.le;
      lt := N.lt;

      zero := 0;
      succ := N.succ;
      pred := N.pred;

      add := N.add;
      sub := N.sub;
      mul := N.mul;
      div := N.div;
      modulo := N.modulo;
      pow := N.pow;

      eqb := N.eqb;

      eqb_spec := N.eqb_spec;

    |}.

  Next Obligation.
    apply N2Z.inj_mod.
  Qed.

  Next Obligation.
    apply Z2N.inj_div.
  Qed.

  Next Obligation.
    apply Z2N.inj_mod.
  Qed.

  Next Obligation.
    apply Z2N.inj_pow.
  Qed.

End NCarrier.

Canonical Structure NCarrier.n_int_carrier.

Module Facts.

  Lemma LE: @IntCarrier.le NCarrier.n_int_carrier = N.le.
  Proof.
    reflexivity.
  Qed.

End Facts.

Import IntCarrier IntCarrier.Facts Unsigned Unsigned.Notations.

Local Obligation Tactic :=
  repeat (unfold two, one, zero, succ, le, lt, IntCarrier.add, pred, pow);
cbn.

Definition ptr_BW := match Archi.ptr64 with false => 32%positive | true => 64%positive end.

Program Definition n_ofst_t : Unsigned :=
  {|
    carrier := NCarrier.n_int_carrier;
    BW := ptr_BW;
  |}.

Canonical Structure n_ofst_t.
