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

From Stdlib Require Import PArith ZArith Arith Psatz.

From compcert Require Integers.

From GallinaC.Utils Require Import NatExt.
From GallinaC.Imp Require Export Intops.

Module NatCarrier.

  Import Intops.IntCarrier.

  Local Obligation Tactic := try (lia).

  Program Definition nat_int_carrier : IntCarrier :=
    {|
      carrier := nat;
      to_Z := Z.of_nat;
      of_Z := Z.to_nat;

      le := Peano.le;
      lt := Peano.lt;

      zero := 0;
      succ := S;
      pred := Nat.pred;

      add := Nat.add;
      sub := Nat.sub;
      mul := Nat.mul;
      div := Nat.div;
      modulo := Nat.modulo;
      pow := Nat.pow;

      eqb := Nat.eqb;

      eqb_spec := Nat.eqb_spec;
    |}.

  Next Obligation.
    apply Nat2Z.inj_div.
  Qed.

  Next Obligation.
    apply Nat2Z.inj_mod.
  Qed.

  Next Obligation.
    apply Nat2Z.inj_pow.
  Qed.

  Next Obligation.
    apply Z2Nat.inj_div.
  Qed.

  Next Obligation.
    apply Z2Nat.inj_mod.
  Qed.

  Next Obligation.
    apply Z2Nat.inj_pow.
  Qed.

End NatCarrier.

Canonical Structure NatCarrier.nat_int_carrier.

Import IntCarrier IntCarrier.Facts Unsigned Unsigned.Notations.

Definition nat_uint32_t : Unsigned :=
  {|
    carrier := NatCarrier.nat_int_carrier;
    BW := 32%positive;
  |}.

Canonical Structure nat_uint32_t.

Lemma nat_bounded_range [n: nat] (BOUNDED: Unsigned.Bounded (UInt := nat_uint32_t) n):
  (0 <= Z.of_nat n <= Integers.Int.max_unsigned)%Z.
Proof using Type.
  exact (Unsigned.CompCert.BW32.unsigned_range_cc (UInt := nat_uint32_t) eq_refl n BOUNDED).
Qed.

Lemma nat_div_inv [S: Type] [l r q: nat] [s: S]
  (BOUNDEDl: Unsigned.Bounded (UInt := nat_uint32_t) l)
  (DIV: Unsigned.div (UInt := nat_uint32_t) l r s = Some (Monad.Success (q, s)))
  : (0 < Z.of_nat r)%Z /\ Z.of_nat q = (Z.of_nat l / Z.of_nat r)%Z.
Proof using Type.
  specialize (nat_bounded_range BOUNDEDl) as RANGEl.
  unfold Integers.Int.max_unsigned in RANGEl.
  revert DIV.
  unfold Unsigned.div, Monad.ret, Monad.fail.
  change (@IntCarrier.to_Z (Unsigned.carrier nat_uint32_t)) with Z.of_nat.
  destruct (Z.eqb_spec (Z.of_nat r) 0) as [ EZ | NZ ]; cbv beta; intro DIV;
    [ discriminate DIV | ].
  injection DIV as EQq.
  assert (RPOS: (0 < Z.of_nat r)%Z) by lia.
  assert (DIVB: (0 <= Z.of_nat l / Z.of_nat r <= Z.of_nat l)%Z)
    by (split; [ apply Z.div_pos | apply Z.div_le_upper_bound ]; nia).
  split; [ exact RPOS | ].
  rewrite <- EQq, (Unsigned.CompCert.BW32.modulus_eq (UInt := nat_uint32_t) eq_refl).
  refine (eq_trans (IntCarrier.of_Z_id (IC := NatCarrier.nat_int_carrier) _ _)
            (Z.mod_small _ _ _));
    [ apply Z.mod_pos_bound; lia | lia ].
Qed.

Lemma nat_mdl_inv [S: Type] [l r q: nat] [s: S]
  (BOUNDEDr: Unsigned.Bounded (UInt := nat_uint32_t) r)
  (MDL: Unsigned.mdl (UInt := nat_uint32_t) l r s = Some (Monad.Success (q, s)))
  : (0 < Z.of_nat r)%Z /\ Z.of_nat q = (Z.of_nat l mod Z.of_nat r)%Z.
Proof using Type.
  specialize (nat_bounded_range BOUNDEDr) as RANGEr.
  unfold Integers.Int.max_unsigned in RANGEr.
  revert MDL.
  unfold Unsigned.mdl, Monad.ret, Monad.fail.
  change (@IntCarrier.to_Z (Unsigned.carrier nat_uint32_t)) with Z.of_nat.
  destruct (Z.eqb_spec (Z.of_nat r) 0) as [ EZ | NZ ]; cbv beta; intro MDL;
    [ discriminate MDL | ].
  injection MDL as EQq.
  assert (RPOS: (0 < Z.of_nat r)%Z) by lia.
  assert (MODB: (0 <= Z.of_nat l mod Z.of_nat r < Z.of_nat r)%Z)
    by (apply Z.mod_pos_bound; lia).
  split; [ exact RPOS | ].
  rewrite <- EQq, (Unsigned.CompCert.BW32.modulus_eq (UInt := nat_uint32_t) eq_refl).
  refine (eq_trans (IntCarrier.of_Z_id (IC := NatCarrier.nat_int_carrier) _ _)
            (Z.mod_small _ _ _));
    [ apply Z.mod_pos_bound; lia | lia ].
Qed.
