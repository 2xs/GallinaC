From Stdlib Require Import PArith ZArith Arith Psatz.

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
