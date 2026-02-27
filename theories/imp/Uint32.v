From Stdlib Require Import PArith Arith Psatz.

From Utils Require Import NatExt.
From Imp Require Export Intops.

From compcert Require Integers.

Module NatCarrier.

  Import Intops.IntCarrier.

  Local Obligation Tactic := try (lia).

  Program Definition nat_int_carrier : IntCarrier.IntCarrier :=
    {|
      carrier := nat;
      zero := 0;
      succ := S;
      pred := Nat.pred;

      inj_pos := Pos.to_nat;

      le := Peano.le;

      add := Nat.add;
      sub := Nat.sub;
      mul := Nat.mul;
      pow := Nat.pow;
      modulo := Nat.modulo;
      eqb := Nat.eqb;

      succ_induction := nat_ind;
      le_ind := Peano.le_ind;

      pow_0_r := Nat.pow_0_r;
      pow_S_r := Nat.pow_succ_r';

      eqb_spec := Nat.eqb_spec;
    |}.

  Next Obligation.
    intros; eapply Nat.mod_upper_bound; lia.
  Qed.

  Next Obligation.
    intros; now apply Nat.mod_small.
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

Module Facts.

  Lemma LE: @le nat_uint32_t = Nat.le.
  Proof.
    reflexivity.
  Qed.

End Facts.

Module CompCert.

  Import IntCarrier Unsigned Unsigned.Facts Arith PArith NArith ZArith Integers.

  Local Open Scope int_scope.

  Theorem modulus_eq: Z.of_nat modulus = Int.modulus.
  Proof.
    unfold modulus.
    rewrite inj_pow.
    reflexivity.
  Qed.
  #[global] Hint Resolve modulus_eq: ints.
  #[global] Hint Rewrite modulus_eq: ints.

  Theorem max_unsigned_eq: Z.of_nat max_unsigned = Int.max_unsigned.
  Proof.
    unfold max_unsigned.
    rewrite pred_sub.
    rewrite Nat2Z.inj_sub, Nat2Z.inj_pow.
    reflexivity.
    apply Nat.pow_lower_bound.
    discriminate.
  Qed.
  #[global] Hint Resolve max_unsigned_eq: ints.

  Theorem unsigned_range_cc: forall n, @Bounded nat_uint32_t n -> (0 <= Z.of_nat n <= Int.max_unsigned)%Z.
  Proof.
    intros n [ Hle0 Hlemax ].
    split; [ lia | ].
    apply Nat2Z.inj_le in Hlemax.
    now rewrite max_unsigned_eq in Hlemax.
  Qed.
  #[global] Hint Resolve unsigned_range_cc: ints.

  Theorem add_cc:
    forall l r l_i r_i,
      @Bounded nat_uint32_t l -> @Bounded nat_uint32_t r ->
      Int.unsigned l_i = Z.of_nat l -> Int.unsigned r_i = Z.of_nat r ->
      Z.of_nat (add l r) = Int.unsigned (Int.add l_i r_i).
  Proof.
    intros l r l_i r_i HBoundedl HBoundedr Hunsigned_l Hunsigned_r.
    rewrite Int.unsigned_add_carry.
    unfold Int.add_carry.
    rewrite Hunsigned_l, Hunsigned_r.
    rewrite (Int.unsigned_zero), Z.add_0_r.
    rewrite <- Nat2Z.inj_add.
    autorewrite with ints.
    destruct (Coqlib.zlt _ _) as [ Hlt | Hle ].
    - rewrite Int.unsigned_zero, Z.mul_0_l, Z.sub_0_r.
      rewrite add_bounded_transparent; [ reflexivity | constructor; [ apply le_0_n | ] ].
      apply Nat2Z.inj_le.
      rewrite Nat2Z.inj_add.
      rewrite max_unsigned_eq.
      unfold Int.max_unsigned.
      lia.
    - rewrite Int.unsigned_one, Z.mul_1_l.
      unfold add.
      rewrite <- modulus_eq, <- Nat2Z.inj_sub; [ | apply Nat2Z.inj_le; rewrite modulus_eq; lia ].
      apply Znat.inj_eq.
      apply Z.ge_le in Hle.
      destruct (Zle_lt_or_eq Int.modulus _ Hle) as [ Hle' | Heq ]; subst.
      + apply mod_add_sub; [ apply modulus_pos | apply bounded_lt_modulus | apply bounded_lt_modulus | ]; auto.
        apply Nat2Z.inj_le.
        rewrite Nat2Z.inj_succ.
        rewrite modulus_eq.
        lia.
      + rewrite <- modulus_eq in Heq.
        apply Nat2Z.inj in Heq.
        rewrite Heq.
        now rewrite Nat.Div0.mod_same, Nat.sub_diag.
  Qed.
  #[global] Hint Resolve add_cc: ints.

End CompCert.
