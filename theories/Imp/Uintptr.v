From Stdlib Require Import PArith NArith Psatz.

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
      zero := 0;
      succ := N.succ;
      pred := N.pred;

      inj_pos := Npos;

      le := N.le;

      add := N.add;
      sub := N.sub;
      mul := N.mul;
      pow := N.pow;
      modulo := N.modulo;

      eqb := N.eqb;

      succ_induction := N.peano_ind;

      pow_0_r := N.pow_0_r;

      eqb_spec := N.eqb_spec;
    |}.

  Next Obligation.
    intros a P HP Hrec c Hle.
    induction c using N.peano_ind.
    destruct a; [ auto | lia ].
    unfold N.le in Hle.
    destruct (a ?= N.succ c) eqn:E; try (contradiction).
    now apply N.compare_eq in E; subst.
    specialize (N.compare_lt_iff a (N.succ c)) as [ Hlt _ ].
    specialize (Hlt E).
    apply N.lt_succ_r in Hlt.
    apply Hrec; [ auto | now apply IHc ].
  Qed.

  Next Obligation.
    intros a b.
    rewrite N.pow_succ_r; [ lia | lia ].
  Qed.

  Next Obligation.

    intros a b; repeat (rewrite le_lt_conv); intros.
    apply N.mod_upper_bound; lia.
  Qed.

  Next Obligation.
    intros a b; repeat (rewrite le_lt_conv); intros; now apply N.mod_small.
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
  repeat (unfold two, one, zero, succ, le, lt, IntCarrier.add, pred, pow, inj_pos);
cbn.

Definition ptr_BW := match Archi.ptr64 with false => 32%positive | true => 64%positive end.

Program Definition n_ofst_t : Unsigned :=
  {|
    carrier := NCarrier.n_int_carrier;
    BW := ptr_BW;
  |}.

Canonical Structure n_ofst_t.

Module CompCert.

  Import IntCarrier Unsigned Unsigned.Facts NArith ZArith Integers NExt.

  Local Open Scope int_scope.

  Theorem modulus_eq: Z.of_N modulus = if Archi.ptr64 then Int64.modulus else Int.modulus .
  Proof.
    unfold modulus.
    destruct (Archi.ptr64) eqn:Earchi.
    - now cbv; rewrite Earchi.
    - now cbv; rewrite Earchi.
  Qed.
  #[global] Hint Resolve modulus_eq: ints.
  #[global] Hint Rewrite modulus_eq: ints.

  Theorem max_unsigned_eq: Z.of_N max_unsigned = if Archi.ptr64 then Int64.max_unsigned else Int.max_unsigned.
  Proof.
    unfold max_unsigned.
    destruct (Archi.ptr64) eqn:Earchi;
      now cbv; rewrite Earchi.
  Qed.
  #[global] Hint Resolve max_unsigned_eq: ints.
  #[global] Hint Rewrite max_unsigned_eq: ints.

  Theorem unsigned_range_cc: forall n, @Bounded n_ofst_t n -> (0 <= Z.of_N n <= (if Archi.ptr64 then Int64.max_unsigned else Int.max_unsigned))%Z.
  Proof.
    unfold Bounded.
    intros n [ Hle0 Hlemax ].
    apply N2Z.inj_le in Hle0.
    apply N2Z.inj_le in Hlemax; rewrite max_unsigned_eq in Hlemax.
    split; auto.
  Qed.
  #[global] Hint Resolve unsigned_range_cc: ints.

  Theorem add_cc_32
    {l r: N} {l_i r_i : Int.int}
    (Earchi32: Archi.ptr64 = false)
    (HBoundedl: Bounded l) (HBoundedr: Bounded r)
    (El: Int.unsigned l_i = Z.of_N l) (Er: Int.unsigned r_i = Z.of_N r)
    : Z.of_N (Unsigned.add l r) = Int.unsigned (Int.add l_i r_i).
  Proof.
    rewrite Int.unsigned_add_carry.
    unfold Int.add_carry.
    rewrite El, Er.
    rewrite Int.unsigned_zero, Z.add_0_r, <- N2Z.inj_add.
    destruct (Coqlib.zlt _ _) as [ Hlt | Hle ].
    - rewrite Int.unsigned_zero, Z.mul_0_l, Z.sub_0_r.
      rewrite add_bounded_transparent.
      reflexivity.
      constructor; [ now apply N.le_0_l | ].
      apply N2Z.inj_le.
      rewrite N2Z.inj_add, max_unsigned_eq, Earchi32.
      unfold Int.max_unsigned; lia.
    - rewrite Int.unsigned_one, Z.mul_1_l.
      specialize modulus_eq as Hmodulus; rewrite Earchi32 in Hmodulus.
      unfold add.
      rewrite <- Hmodulus, <- N2Z.inj_sub; [ | lia ].
      apply N2Z.inj_iff.
      apply Z.ge_le in Hle.
      destruct (Zle_lt_or_eq Int.modulus _ Hle) as [ Hle' | Heq ]; subst.
      + apply mod_add_sub.
        specialize (@modulus_pos n_ofst_t) as Hmodulus_pos.
        apply N.lt_le_trans with (m := 1); [ lia | eapply Hmodulus_pos ].
        apply N.lt_le_trans with (m := N.succ l); [ lia | now apply bounded_lt_modulus ].
        apply N.lt_le_trans with (m := N.succ r); [ lia | now apply bounded_lt_modulus ].
        lia.
      + rewrite <- Hmodulus in Heq.
        apply N2Z.inj in Heq.
        rewrite Heq.
        now rewrite N.Div0.mod_same, N.sub_diag.
  Qed.
  #[global] Hint Resolve add_cc_32: ints.

  Theorem add_cc_64
    {l r: N} {l_i r_i : Int64.int}
    (Earchi32: Archi.ptr64 = true)
    (HBoundedl: Bounded l) (HBoundedr: Bounded r)
    (El: Int64.unsigned l_i = Z.of_N l) (Er: Int64.unsigned r_i = Z.of_N r)
    : Z.of_N (Unsigned.add l r) = Int64.unsigned (Int64.add l_i r_i).
  Proof.
    rewrite Int64.unsigned_add_carry.
    unfold Int64.add_carry.
    rewrite El, Er.
    rewrite Int64.unsigned_zero, Z.add_0_r, <- N2Z.inj_add.
    destruct (Coqlib.zlt _ _) as [ Hlt | Hle ].
    - rewrite Int64.unsigned_zero, Z.mul_0_l, Z.sub_0_r.
      rewrite add_bounded_transparent.
      reflexivity.
      constructor; [ now apply N.le_0_l | ].
      apply N2Z.inj_le.
      rewrite N2Z.inj_add, max_unsigned_eq, Earchi32.
      unfold Int64.max_unsigned; lia.
    - rewrite Int64.unsigned_one, Z.mul_1_l.
      specialize modulus_eq as Hmodulus; rewrite Earchi32 in Hmodulus.
      unfold add.
      rewrite <- Hmodulus, <- N2Z.inj_sub; [ | lia ].
      apply N2Z.inj_iff.
      apply Z.ge_le in Hle.
      destruct (Zle_lt_or_eq Int64.modulus _ Hle) as [ Hle' | Heq ]; subst.
      + apply mod_add_sub.
        specialize (@modulus_pos n_ofst_t) as Hmodulus_pos.
        apply N.lt_le_trans with (m := 1); [ lia | eapply Hmodulus_pos ].
        apply N.lt_le_trans with (m := N.succ l); [ lia | now apply bounded_lt_modulus ].
        apply N.lt_le_trans with (m := N.succ r); [ lia | now apply bounded_lt_modulus ].
        lia.
      + rewrite <- Hmodulus in Heq.
        apply N2Z.inj in Heq.
        rewrite Heq.
        now rewrite N.Div0.mod_same, N.sub_diag.
  Qed.
  #[global] Hint Resolve add_cc_64: ints.

End CompCert.
