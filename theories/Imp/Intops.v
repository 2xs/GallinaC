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

From Stdlib Require Import ZArith Psatz.

From compcert Require Integers.

From GallinaC.Utils Require Import ReflectExt.
From GallinaC.Imp Require Import Monad.

Local Open Scope Z_scope.

Declare Scope int_scope.
Local Open Scope int_scope.
Delimit Scope int_scope with int.

Create HintDb ints.

(* Types which are well-adapted to implement C integers *)

Module IntCarrier.

  Structure IntCarrier :=
    {
      carrier :> Type;

      to_Z: carrier -> Z;
      of_Z: Z -> carrier;

      le: carrier -> carrier -> Prop;
      lt: carrier -> carrier -> Prop;

      zero: carrier;
      succ: carrier -> carrier;
      pred: carrier -> carrier;

      add: carrier -> carrier -> carrier;
      sub: carrier -> carrier -> carrier;
      mul: carrier -> carrier -> carrier;
      div: carrier -> carrier -> carrier;
      modulo: carrier -> carrier -> carrier;
      pow: carrier -> carrier -> carrier;

      eqb: carrier -> carrier -> bool;
      eqb_spec: forall a b, Bool.reflect (a = b) (eqb a b);

      to_Z_id: forall a, of_Z (to_Z a) = a;
      of_Z_id: forall a, 0 <= a -> to_Z (of_Z a) = a;

      to_Z_inj: forall a b, to_Z a = to_Z b <-> a = b;
      to_Z_le: forall a b, le a b <-> (to_Z a <= to_Z b);
      to_Z_lt: forall a b, lt a b <-> (to_Z a < to_Z b);
      to_Z_zero: to_Z zero = 0;
      to_Z_succ: forall a, to_Z (succ a) = Z.succ (to_Z a);
      to_Z_pred: forall a, lt zero a -> to_Z (pred a) = Z.pred (to_Z a);
      to_Z_add: forall a b, to_Z (add a b) = (to_Z a + to_Z b);
      to_Z_sub: forall a b, le b a -> to_Z (sub a b) = (to_Z a - to_Z b);
      to_Z_mul: forall a b, to_Z (mul a b) = (to_Z a * to_Z b);
      to_Z_div: forall a b, to_Z (div a b) = (to_Z a / to_Z b);
      to_Z_mod: forall a b, to_Z (modulo a b) = (to_Z a mod to_Z b);
      to_Z_pow: forall a b, to_Z (pow a b) = (to_Z a ^ to_Z b);

      of_Z_inj: forall a b, (0 <= a) -> (0 <= b) -> of_Z a = of_Z b <-> a = b;
      of_Z_le: forall a b, (0 <= a) -> (0 <= b) -> (a <= b) <-> le (of_Z a) (of_Z b);
      of_Z_lt: forall a b, (0 <= a) -> (0 <= b) -> (a < b) <-> lt (of_Z a) (of_Z b);
      of_Z_zero: of_Z 0 = zero;
      of_Z_succ: forall a, (0 <= a) -> of_Z (Z.succ a) = succ (of_Z a);
      of_Z_pred: forall a, of_Z (Z.pred a) = pred (of_Z a);
      of_Z_add: forall a b, (0 <= a) -> (0 <= b) -> of_Z (a + b) = add (of_Z a) (of_Z b);
      of_Z_sub: forall a b, (0 <= b) -> of_Z (a - b) = sub (of_Z a) (of_Z b);
      of_Z_mul: forall a b, (0 <= a) -> (0 <= b) -> of_Z (a * b) = mul (of_Z a) (of_Z b);
      of_Z_div: forall a b, (0 <= a) -> (0 <= b) -> of_Z (a / b) = div (of_Z a) (of_Z b);
      of_Z_mod: forall a b, (0 <= a) -> (0 <= b) -> of_Z (a mod b) = modulo (of_Z a) (of_Z b);
      of_Z_pow: forall a b, (0 <= a) -> (0 <= b) -> of_Z (a ^ b) = pow (of_Z a) (of_Z b);

    }.

  Arguments carrier IC: rename, simpl never.

  Arguments to_Z {IC} a: rename, simpl never.
  Arguments of_Z {IC} a: rename, simpl never.

  Arguments le {IC} a b: rename, simpl never.
  Arguments lt {IC} a b: rename, simpl never.

  Arguments zero IC: rename, simpl never.
  Arguments succ {IC} a: rename, simpl never.
  Arguments pred {IC} a: rename, simpl never.

  Arguments add {IC} a b: rename, simpl never.
  Arguments sub {IC} a b: rename, simpl never.
  Arguments mul {IC} a b: rename, simpl never.
  Arguments div {IC} a b: rename, simpl never.
  Arguments modulo {IC} a b: rename, simpl never.
  Arguments pow {IC} a b: rename, simpl never.

  Arguments eqb {IC} a b: rename, simpl never.
  Arguments eqb_spec {IC} a b: rename, simpl never.

  Arguments to_Z_id {IC} a: rename, simpl never.
  Arguments of_Z_id {IC} a: rename, simpl never.

  Arguments to_Z_inj {IC} a b: rename, simpl never.
  Arguments to_Z_le {IC} a b: rename, simpl never.
  Arguments to_Z_lt {IC} a b: rename, simpl never.
  Arguments to_Z_zero {IC}: rename, simpl never.
  Arguments to_Z_succ {IC} a: rename, simpl never.
  Arguments to_Z_pred {IC} a: rename, simpl never.
  Arguments to_Z_add {IC} a b: rename, simpl never.
  Arguments to_Z_sub {IC} a b: rename, simpl never.
  Arguments to_Z_mul {IC} a b: rename, simpl never.
  Arguments to_Z_div {IC} a b: rename, simpl never.
  Arguments to_Z_mod {IC} a b: rename, simpl never.
  Arguments to_Z_pow {IC} a b: rename, simpl never.

  Arguments of_Z_inj {IC} a b LE0a LE0b: rename, simpl never.
  Arguments of_Z_le {IC} a b LE0a LE0b: rename, simpl never.
  Arguments of_Z_lt {IC} a b LE0a LE0b: rename, simpl never.
  Arguments of_Z_zero {IC}: rename, simpl never.
  Arguments of_Z_succ {IC} a LE0a: rename, simpl never.
  Arguments of_Z_pred {IC} a: rename, simpl never.
  Arguments of_Z_add {IC} a b LE0a LE0b: rename, simpl never.
  Arguments of_Z_sub {IC} a b LE0b: rename, simpl never.
  Arguments of_Z_mul {IC} a b LE0a LE0b: rename, simpl never.
  Arguments of_Z_div {IC} a b LE0a LE0b: rename, simpl never.
  Arguments of_Z_mod {IC} a b LE0a LE0b: rename, simpl never.
  Arguments of_Z_pow {IC} a b LE0a LE0b: rename, simpl never.

  #[global] Hint Resolve
    to_Z_id of_Z_id eqb_spec
    to_Z_inj to_Z_le to_Z_lt to_Z_zero to_Z_succ to_Z_pred to_Z_add to_Z_sub to_Z_mul to_Z_div to_Z_mod to_Z_pow
    of_Z_inj of_Z_le of_Z_lt of_Z_zero of_Z_succ of_Z_pred of_Z_add of_Z_sub of_Z_mul of_Z_div of_Z_mod of_Z_pow
    : ints.

  Module Facts.

    Definition one (IC: IntCarrier) := succ (zero IC).
    #[global] Hint Unfold one: ints.

    Definition two (IC: IntCarrier) := succ (succ (zero IC)).
    #[global] Hint Unfold two: ints.

  End Facts.

  Module Notations.

    Import Facts.

    Notation ":0" := (zero _) (at level 0): int_scope.
    Notation ":1" := (one _) (at level 0): int_scope.
    Notation ":2" := (two _) (at level 0): int_scope.

    Notation "a :<: b" := (lt a b) (at level 70, no associativity): int_scope.
    Notation "a :<=: b" := (le a b) (at level 70, no associativity): int_scope.
    Notation "a :<: b :<: c" := (lt a b /\ lt b c) (at level 70, no associativity): int_scope.
    Notation "a :<: b :<=: c" := (lt a b /\ le b c) (at level 70, no associativity): int_scope.
    Notation "a :<=: b :<: c" := (le a b /\ lt b c) (at level 70, no associativity): int_scope.
    Notation "a :<=: b :<=: c" := (le a b /\ le b c) (at level 70, no associativity): int_scope.

    Notation "a :+: b" := (add a b) (at level 50): int_scope.
    Notation "a :-: b" := (sub a b) (at level 50): int_scope.
    Notation "a :*: b" := (mul a b) (at level 50): int_scope.
    Notation "a :^: b" := (pow a b) (at level 50): int_scope.
    Notation "a :%: b" := (modulo a b) (at level 50): int_scope.

    Notation "a :=?: b" := (eqb a b) (at level 70): int_scope.

  End Notations.

End IntCarrier.

(* How to implement an unsigned integer from an IntCarrier *)
Module Unsigned.

  Import IntCarrier IntCarrier.Notations IntCarrier.Facts.

  Structure Unsigned :=
    {
      carrier :> IntCarrier.IntCarrier;
      BW: positive;
    }.

  Arguments carrier UInt: rename, simpl never.
  Arguments BW UInt: rename, simpl never.

  Definition min_unsigned (UInt: Unsigned): Z := 0.
  Definition max_unsigned (UInt: Unsigned): Z := Z.pred (2 ^ (Zpos (BW UInt))).
  Definition modulus (UInt: Unsigned): Z := 2 ^ (Zpos (BW UInt)).

  Definition Bounded {UInt: Unsigned} (n: UInt): Prop := (min_unsigned UInt <= (to_Z n) <= max_unsigned UInt)%Z.

  Definition add {UInt: Unsigned} (l r: UInt): UInt := of_Z ((to_Z l + to_Z r) mod (modulus UInt)).

  Definition mul {UInt: Unsigned} (l r: UInt): UInt := of_Z ((to_Z l * to_Z r) mod (modulus UInt)).

  Definition div {S} {UInt: Unsigned} (l r: UInt): program S UInt :=
    if to_Z r =? 0 then
      fail
    else
      ret (of_Z ((to_Z l / to_Z r) mod (modulus UInt))).

  Definition mdl {S} {UInt: Unsigned} (l r: UInt): program S UInt :=
    if to_Z r =? 0 then
      fail
    else
      ret (of_Z ((to_Z l mod to_Z r) mod (modulus UInt))).

  Definition eqb {UInt: Unsigned} (l r: UInt): bool := ((to_Z l mod (modulus UInt)) =? (to_Z r mod (modulus UInt)))%Z.

  Arguments Bounded {UInt} n: rename, simpl never.
  Arguments add {UInt} l r: rename, simpl never.
  Arguments mul {UInt} l r: rename, simpl never.
  Arguments div {S UInt} l r: rename, simpl never.
  Arguments mdl {S UInt} l r: rename, simpl never.
  Arguments eqb {UInt} l r: rename, simpl never.

  Module Notations.

    Export IntCarrier.Notations.

    Notation "a + b" := (add a b): int_scope.
    Notation "a * b" := (mul a b): int_scope.
    Notation "a / b" := (div a b): int_scope.
    Notation "a % b" := (mdl a b) (at level 60, no associativity): int_scope.
    Notation "a =? b" := (eqb a b): int_scope.

  End Notations.

  Module Facts.

    Import ZArith Psatz.
    Local Open Scope Z_scope.

    Remark modulus_pos {UInt: Unsigned}: 1 <= (modulus UInt).
    Proof.
      unfold modulus.
      specialize (Z.pow_pos_nonneg 1 (2 ^ Z.pos (BW UInt))).
      lia.
    Qed.
    #[global] Hint Resolve modulus_pos: ints.

    Remark modulus_pos_lt {UInt: Unsigned}: 0 < (modulus UInt).
    Proof.
      specialize (@modulus_pos UInt).
      lia.
    Qed.
    #[global] Hint Resolve modulus_pos: ints.

    Remark modulus_neq_0 {UInt: Unsigned}: 0 <> modulus UInt.
    Proof.
      apply Z.lt_neq, modulus_pos_lt.
    Qed.
    #[global] Hint Resolve modulus_neq_0: ints.

    Remark max_lt_modulus {UInt: Unsigned}: (max_unsigned UInt) < (modulus UInt).
    Proof.
      unfold max_unsigned, modulus.
      lia.
    Qed.
    #[global] Hint Resolve max_lt_modulus: ints.

    Remark max_le_modulus {UInt: Unsigned}: (max_unsigned UInt) <= (modulus UInt).
    Proof.
      unfold max_unsigned, modulus.
      lia.
    Qed.
    #[global] Hint Resolve max_le_modulus: ints.

    Lemma bounded_lt_modulus {UInt: Unsigned}: forall (n: UInt), Bounded n -> (to_Z n) < (modulus UInt).
    Proof.
      intros n [ _ Hle ].
      unfold max_unsigned in Hle; unfold modulus.
      lia.
    Qed.

    Theorem add_bounded {UInt: Unsigned} (l r: carrier UInt): Bounded (add l r).
    Proof.
      unfold add.
      split; (rewrite of_Z_id; specialize (Z.mod_pos_bound (to_Z l + to_Z r) (modulus UInt) modulus_pos_lt) as [ LE0 LT ]; auto).
      unfold modulus, max_unsigned in *; lia.
    Qed.
    #[global] Hint Resolve add_bounded: ints.

    Theorem mul_bounded {UInt: Unsigned} (l r: carrier UInt): Bounded (mul l r).
    Proof.
      unfold mul.
      split; (rewrite of_Z_id; specialize (Z.mod_pos_bound (to_Z l * to_Z r) (modulus UInt) modulus_pos_lt) as [ LE0 LT ]; auto).
      unfold modulus, max_unsigned in *; lia.
    Qed.
    #[global] Hint Resolve mul_bounded: ints.

    Theorem add_bounded_transparent {UInt: Unsigned} (l r: carrier UInt) (HBoundedAdd: Bounded (l :+: r)): add l r = l :+: r.
    Proof.
      specialize (@modulus_pos_lt UInt) as LT.
      destruct HBoundedAdd as [ LE0 LEmax ].
      unfold add, modulus, max_unsigned, min_unsigned in *.
      rewrite <- to_Z_add.
      now rewrite Z.mod_small; [ rewrite to_Z_id | lia ].
    Qed.
    #[global] Hint Resolve add_bounded_transparent: ints.

    Lemma raw_add_lt_double_modulus [UInt: Unsigned] [l r: carrier UInt]
      (BOUNDEDl: Bounded l) (BOUNDEDr: Bounded r)
      : to_Z l + to_Z r < 2 * modulus UInt.
    Proof.
      rewrite <- Z.add_diag.
      specialize (bounded_lt_modulus _ BOUNDEDl).
      specialize (bounded_lt_modulus _ BOUNDEDr).
      lia.
    Qed.
    #[global] Hint Resolve raw_add_lt_double_modulus: ints.

    Theorem add_bounded_semi_transparent {UInt: Unsigned} (l r: carrier UInt) (BOUNDEDl: Bounded l) (BOUNDEDr: Bounded r) (EQ: (max_unsigned UInt) < to_Z l + to_Z r) : to_Z (add l r) = to_Z l + to_Z r - (modulus UInt).
    Proof.
      unfold add, max_unsigned, min_unsigned, modulus.
      specialize (raw_add_lt_double_modulus BOUNDEDl BOUNDEDr) as EQ'.
      destruct BOUNDEDl as [ LTl0 LElm ].
      destruct BOUNDEDr as [ LTr0 LErm ].
      revert LTl0 LElm LTr0 LErm EQ EQ'.
      generalize (to_Z r) as y.
      generalize (to_Z l) as x.
      unfold max_unsigned, min_unsigned, modulus.
      generalize (2 ^ Z.pos (BW UInt)) as m.
      intros. rewrite of_Z_id; [ | apply Z.mod_pos_bound; lia ].
      clear UInt l r.
      symmetry.
      apply Zmod_unique with (q := 1); lia.
    Qed.

    Theorem eqb_refl {UInt: Unsigned} (a: carrier UInt):
      eqb a a = true.
    Proof.
      unfold eqb; apply Z.eqb_refl.
    Qed.
    #[global] Hint Resolve eqb_refl: ints.

    Theorem eqb_symm {UInt: Unsigned} (l r: carrier UInt):
      eqb l r = eqb r l.
    Proof.
      unfold eqb; eapply Z.eqb_sym.
    Qed.
    #[global] Hint Resolve eqb_symm: ints.

    Theorem eqb_bounded {UInt: Unsigned} (l r: carrier UInt) (LB: Bounded l) (RB: Bounded r):
      eqb l r = IntCarrier.eqb l r.
    Proof.
      destruct LB as [ LE0l LEmaxl ].
      destruct RB as [ LE0r LEmaxr ].
      unfold eqb, modulus, min_unsigned, max_unsigned in *.
      destruct (eqb_spec l r) as [| NE]; [ subst | ].
      - apply Z.eqb_refl.
      - repeat (rewrite Z.mod_small; [ | lia ]).
        destruct (Z.eqb_spec (to_Z l) (to_Z r)) as [ EQ | NE' ]; [ now apply to_Z_inj in EQ | reflexivity ].
    Qed.
    #[global] Hint Resolve eqb_bounded: ints.

    Theorem bounded_mod_eq {UInt: Unsigned} (x: UInt): Bounded x -> x :%: (of_Z (modulus UInt)) = x.
    Proof.
      intros [ LE0 LEmax ].
      unfold min_unsigned, max_unsigned, modulus in *.
      eapply to_Z_inj.
      rewrite to_Z_mod, of_Z_id; [ | lia].
      rewrite Z.mod_small; lia.
    Qed.
    #[global] Hint Resolve bounded_mod_eq: ints.

    Lemma div_state_indep [S: Type] [UInt: Unsigned] [l r q: carrier UInt]
      [s1 s2: S]
      (DIV: div l r s1 = Some (Monad.Success (q, s1))):
      div l r s2 = Some (Monad.Success (q, s2)).
    Proof.
      unfold div in DIV |- *.
      destruct (Z.eqb (to_Z r) 0); [ discriminate DIV | ].
      cbn in DIV |- *; injection DIV as <-; reflexivity.
    Qed.

    Lemma mdl_state_indep [S: Type] [UInt: Unsigned] [l r q: carrier UInt]
      [s1 s2: S]
      (MDL: mdl l r s1 = Some (Monad.Success (q, s1))):
      mdl l r s2 = Some (Monad.Success (q, s2)).
    Proof.
      unfold mdl in MDL |- *.
      destruct (Z.eqb (to_Z r) 0); [ discriminate MDL | ].
      cbn in MDL |- *; injection MDL as <-; reflexivity.
    Qed.

  End Facts.

  Module CompCert.

    Import Facts Integers.

    Local Open Scope int_scope.

    Module BW32.

      Theorem modulus_eq [UInt: Unsigned] (BW32: BW UInt = 32%positive): (modulus UInt) = Int.modulus.
      Proof.
        now unfold modulus; rewrite BW32.
      Qed.
      #[global] Hint Resolve modulus_eq: ints.
      #[global] Hint Rewrite modulus_eq: ints.

      Theorem max_unsigned_eq [UInt: Unsigned] (BW32: BW UInt = 32%positive): max_unsigned UInt = Int.max_unsigned.
      Proof.
        now unfold max_unsigned; rewrite BW32.
      Qed.
      #[global] Hint Resolve max_unsigned_eq: ints.

      Theorem unsigned_range_cc [UInt: Unsigned] (BW32: BW UInt = 32%positive): forall n, @Bounded UInt n -> (0 <= to_Z n <= Int.max_unsigned)%Z.
      Proof.
        intros n [ LE0 LEmax ].
        unfold min_unsigned, max_unsigned, Int.max_unsigned, Int.modulus, Int.wordsize in *; cbn in *.
        rewrite BW32 in *; lia.
      Qed.
      #[global] Hint Resolve unsigned_range_cc: ints.

      Theorem add_cc [UInt: Unsigned] (BW32: BW UInt = 32%positive):
        forall l r l_i r_i,
          @Bounded UInt l -> @Bounded UInt r ->
          Int.unsigned l_i = to_Z l -> Int.unsigned r_i = to_Z r ->
          to_Z (add l r) = Int.unsigned (Int.add l_i r_i).
      Proof.
        intros l r l_i r_i BOUNDEDl BOUNDEDr UNSIGNEDl UNSIGNEDr.
        specialize (unsigned_range_cc BW32 l BOUNDEDl) as RANGEl.
        specialize (unsigned_range_cc BW32 r BOUNDEDr) as RANGEr.
        rewrite Int.unsigned_add_carry.
        unfold Int.add_carry.
        rewrite UNSIGNEDl, UNSIGNEDr.
        rewrite Int.unsigned_zero, Z.add_0_r.
        rewrite <- to_Z_add.
        destruct (Coqlib.zlt _ _) as [ Hlt | Hle ].
        - rewrite Int.unsigned_zero, Z.mul_0_l, Z.sub_0_r.
          rewrite add_bounded_transparent; [ reflexivity | constructor; [ unfold min_unsigned; rewrite to_Z_add; lia | ] ].
          unfold max_unsigned.
          rewrite to_Z_add, BW32 in *.
          unfold Int.modulus, two_power_nat in *; cbn in *.
          lia.
        - rewrite Int.unsigned_one.
          rewrite to_Z_add.
          rewrite Z.mul_1_l.
          rewrite <- (modulus_eq BW32).
          rewrite add_bounded_semi_transparent; auto.
          rewrite to_Z_add in Hle.
          unfold max_unsigned; rewrite BW32.
          unfold Int.modulus, two_power_nat in *; cbn in *.
          lia.
      Qed.
      #[global] Hint Resolve add_cc: ints.

      Theorem mul_cc [UInt: Unsigned] (BW32: BW UInt = 32%positive):
        forall l r l_i r_i,
          @Bounded UInt l -> @Bounded UInt r ->
          Int.unsigned l_i = to_Z l -> Int.unsigned r_i = to_Z r ->
          to_Z (mul l r) = Int.unsigned (Int.mul l_i r_i).
      Proof.
        intros l r l_i r_i BOUNDEDl BOUNDEDr UNSIGNEDl UNSIGNEDr.
        unfold mul, Int.mul.
        rewrite Int.unsigned_repr_eq, UNSIGNEDl, UNSIGNEDr, <- (modulus_eq BW32).
        apply of_Z_id.
        specialize (Z.mod_pos_bound (to_Z l * to_Z r) (modulus UInt) modulus_pos_lt) as [ LE0 _ ]; auto.
      Qed.
      #[global] Hint Resolve mul_cc: ints.

    End BW32.

    Module BW64.

      Theorem modulus_eq [UInt: Unsigned] (BW64: BW UInt = 64%positive): (modulus UInt) = Int64.modulus.
      Proof.
        now unfold modulus; rewrite BW64.
      Qed.
      #[global] Hint Resolve modulus_eq: ints.
      #[global] Hint Rewrite modulus_eq: ints.

      Theorem max_unsigned_eq [UInt: Unsigned] (BW64: BW UInt = 64%positive): max_unsigned UInt = Int64.max_unsigned.
      Proof.
        now unfold max_unsigned; rewrite BW64.
      Qed.
      #[global] Hint Resolve max_unsigned_eq: ints.

      Theorem unsigned_range_cc [UInt: Unsigned] (BW64: BW UInt = 64%positive): forall n, @Bounded UInt n -> (0 <= to_Z n <= Int64.max_unsigned)%Z.
      Proof.
        intros n [ LE0 LEmax ].
        unfold min_unsigned, max_unsigned, Int64.max_unsigned, Int64.modulus, Int64.wordsize in *; cbn in *.
        rewrite BW64 in *; lia.
      Qed.
      #[global] Hint Resolve unsigned_range_cc: ints.

      Theorem add_cc [UInt: Unsigned] (BW64: BW UInt = 64%positive):
        forall l r l_i r_i,
          @Bounded UInt l -> @Bounded UInt r ->
          Int64.unsigned l_i = to_Z l -> Int64.unsigned r_i = to_Z r ->
          to_Z (add l r) = Int64.unsigned (Int64.add l_i r_i).
      Proof.
        intros l r l_i r_i BOUNDEDl BOUNDEDr UNSIGNEDl UNSIGNEDr.
        specialize (unsigned_range_cc BW64 l BOUNDEDl) as RANGEl.
        specialize (unsigned_range_cc BW64 r BOUNDEDr) as RANGEr.
        rewrite Int64.unsigned_add_carry.
        unfold Int64.add_carry.
        rewrite UNSIGNEDl, UNSIGNEDr.
        rewrite (Int64.unsigned_zero), Z.add_0_r.
        rewrite <- to_Z_add.
        destruct (Coqlib.zlt _ _) as [ Hlt | Hle ].
        - rewrite Int64.unsigned_zero, Z.mul_0_l, Z.sub_0_r.
          rewrite add_bounded_transparent; [ reflexivity | constructor; [ unfold min_unsigned; rewrite to_Z_add; lia | ] ].
          unfold max_unsigned.
          rewrite to_Z_add, BW64 in *.
          unfold Int64.modulus, two_power_nat in *; cbn in *.
          lia.
        - rewrite Int64.unsigned_one.
          rewrite to_Z_add.
          rewrite Z.mul_1_l.
          rewrite <- (modulus_eq BW64).
          rewrite add_bounded_semi_transparent; auto.
          rewrite to_Z_add in Hle.
          unfold max_unsigned; rewrite BW64.
          unfold Int64.modulus, two_power_nat in *; cbn in *.
          lia.
      Qed.
      #[global] Hint Resolve add_cc: ints.

    End BW64.

    Module Ptrofs.

      Theorem modulus_eq [UInt: Unsigned] (BWptr: BW UInt = if Archi.ptr64 then 64%positive else 32%positive): (modulus UInt) = Ptrofs.modulus.
      Proof.
        now unfold modulus; rewrite BWptr.
      Qed.
      #[global] Hint Resolve modulus_eq: ints.
      #[global] Hint Rewrite modulus_eq: ints.

      Theorem max_unsigned_eq [UInt: Unsigned] (BWptr: BW UInt = if Archi.ptr64 then 64%positive else 32%positive): max_unsigned UInt = Ptrofs.max_unsigned.
      Proof.
        now unfold max_unsigned; rewrite BWptr.
      Qed.
      #[global] Hint Resolve max_unsigned_eq: ints.

      Theorem unsigned_range_cc [UInt: Unsigned] (BWptr: BW UInt = if Archi.ptr64 then 64%positive else 32%positive): forall n, @Bounded UInt n -> (0 <= to_Z n <= Ptrofs.max_unsigned)%Z.
      Proof.
        intros n [ LE0 LEmax ].
        unfold min_unsigned, max_unsigned, Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize in *;
          destruct Archi.ptr64;
          cbn in *;
          rewrite BWptr in *; lia.
      Qed.
      #[global] Hint Resolve unsigned_range_cc: ints.

      Theorem unsigned_range_cc_32 [UInt: Unsigned] (BWptr: BW UInt = if Archi.ptr64 then 64%positive else 32%positive) (PTR32: Archi.ptr64 = false): forall n, @Bounded UInt n -> (0 <= to_Z n <= Int.max_unsigned)%Z.
      Proof.
        specialize (unsigned_range_cc BWptr).
        unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
        now rewrite PTR32 in *.
      Qed.
      #[global] Hint Resolve unsigned_range_cc_32: ints.

      Theorem unsigned_range_cc_64 [UInt: Unsigned] (BWptr: BW UInt = if Archi.ptr64 then 64%positive else 32%positive) (PTR64: Archi.ptr64 = true): forall n, @Bounded UInt n -> (0 <= to_Z n <= Int64.max_unsigned)%Z.
      Proof.
        specialize (unsigned_range_cc BWptr).
        unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
        now rewrite PTR64 in *.
      Qed.
      #[global] Hint Resolve unsigned_range_cc_64: ints.

      Theorem add_cc [UInt: Unsigned] (BWptr: BW UInt = if Archi.ptr64 then 64%positive else 32%positive):
        forall l r l_i r_i,
          @Bounded UInt l -> @Bounded UInt r ->
          Ptrofs.unsigned l_i = to_Z l -> Ptrofs.unsigned r_i = to_Z r ->
          to_Z (add l r) = Ptrofs.unsigned (Ptrofs.add l_i r_i).
      Proof.
        intros l r l_i r_i BOUNDEDl BOUNDEDr UNSIGNEDl UNSIGNEDr.
        specialize (unsigned_range_cc BWptr l BOUNDEDl) as RANGEl.
        specialize (unsigned_range_cc BWptr r BOUNDEDr) as RANGEr.
        rewrite Ptrofs.unsigned_add_carry.
        unfold Ptrofs.add_carry.
        rewrite UNSIGNEDl, UNSIGNEDr.
        rewrite (Ptrofs.unsigned_zero), Z.add_0_r.
        rewrite <- to_Z_add.
        destruct (Coqlib.zlt _ _) as [ Hlt | Hle ].
        - rewrite Ptrofs.unsigned_zero, Z.mul_0_l, Z.sub_0_r.
          rewrite add_bounded_transparent; [ reflexivity | constructor; [ unfold min_unsigned; rewrite to_Z_add; lia | ] ].
          unfold max_unsigned.
          rewrite to_Z_add, BWptr in *.
          unfold Ptrofs.modulus, two_power_nat, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize in *;
            destruct Archi.ptr64;
            cbn in *;
            lia.
        - rewrite Ptrofs.unsigned_one.
          rewrite to_Z_add.
          rewrite Z.mul_1_l.
          rewrite <- (modulus_eq BWptr).
          rewrite add_bounded_semi_transparent; auto.
          rewrite to_Z_add in Hle.
          unfold max_unsigned; rewrite BWptr.
          unfold Ptrofs.modulus, two_power_nat, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize in *;
            destruct Archi.ptr64;
            cbn in *;
            lia.
      Qed.
      #[global] Hint Resolve add_cc: ints.

    End Ptrofs.

  End CompCert.

End Unsigned.
