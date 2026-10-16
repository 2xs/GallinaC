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
Import ssrfun.Option.
From HB Require Import structures.

From GallinaC.Utils Require Import ReflectExt.
From GallinaC.Utils Require Export Algebra.


Local Open Scope separation_scope.

Definition prod_eqb [A B: EqDec.type] (x y: A * B): bool :=
  eqb (fst x) (fst y) && eqb (snd x) (snd y).

Lemma prod_eqb_spec [A B: EqDec.type] (x y: A * B)
  : Bool.reflect (x = y) (prod_eqb x y).
Proof.
  move: x y => [ x1 x2 ] [ y1 y2 ]; rewrite /prod_eqb/=.
  case (eqb_spec x1 y1) => [ EQ | NE ]/=; [ subst | right; congruence ].
  case (eqb_spec x2 y2) => [ EQ | NE ]/=; constructor; congruence.
Qed.

HB.instance Definition _ (A B: EqDec.type) :=
  hasEqDec.Build (A * B)%type (@prod_eqb A B) (@prod_eqb_spec A B).

Definition prod_sum [A B: Separation.type] (x y: A * B): option (A * B) :=
  match x, y with
  | (a1, b1), (a2, b2) =>
      match a1 $+ a2, b1 $+ b2 with
      | Some a, Some b => Some (a, b)
      | _, _ => None
      end
  end.

#[local] Lemma prod_sum_speci [A B: Separation.type] (x y z: A * B):
  prod_sum x y = Some z
  <-> (fst x $+ fst y = Some (fst z) /\ snd x $+ snd y = Some (snd z)).
Proof.
  move: x y z => [x1 x2] [y1 y2] [z1 z2].
  rewrite /prod_sum /=.
  case E1: (x1 $+ y1) => [a|]; case E2: (x2 $+ y2) => [b|]; split.
  - by move=> [-> ->].
  - by move=> [[->] [->]].
  - discriminate.
  - by move=> [_ H].
  - discriminate.
  - by move=> [H _].
  - discriminate.
  - by move=> [H _].
Qed.

Lemma prod_sum_comm [A B: Separation.type] (x y: A * B):
  prod_sum x y = prod_sum y x.
Proof.
  move: x y => [x1 x2] [y1 y2].
  by rewrite /prod_sum (op_comm x1) (op_comm x2).
Qed.

Lemma prod_sum_id_l [A B: Separation.type] (x: A * B):
  prod_sum ($0, $0) x = Some x.
Proof.
  apply/prod_sum_speci => /=.
  by split; apply: op_id_l.
Qed.

Lemma prod_sum_id_r [A B: Separation.type] (x: A * B):
  prod_sum x ($0, $0) = Some x.
Proof.
  apply/prod_sum_speci => /=.
  by split; apply: op_id_r.
Qed.

Lemma prod_sum_assc [A B: Separation.type] (x y z: A * B):
  bind (Basics.flip (@prod_sum A B) z) (prod_sum x y)
  = bind (@prod_sum A B x) (prod_sum y z).
Proof.
  move: x y z => [x1 x2] [y1 y2] [z1 z2].
  have EL: bind (Basics.flip (@prod_sum A B) (z1, z2)) (prod_sum (x1, x2) (y1, y2))
           = match bind (Basics.flip (@op A) z1) (x1 $+ y1),
                   bind (Basics.flip (@op B) z2) (x2 $+ y2) with
             | Some u, Some v => Some (u, v)
             | _, _ => None
             end.
  { rewrite /prod_sum /Basics.flip /=.
    case: (x1 $+ y1) => [a|]; case: (x2 $+ y2) => [b|] //=.
    by case: (a $+ z1) => [u|]. }
  have ER: bind (@prod_sum A B (x1, x2)) (prod_sum (y1, y2) (z1, z2))
           = match bind ((@op A) x1) (y1 $+ z1),
                   bind ((@op B) x2) (y2 $+ z2) with
             | Some u, Some v => Some (u, v)
             | _, _ => None
             end.
  { rewrite /prod_sum /=.
    case: (y1 $+ z1) => [a|]; case: (y2 $+ z2) => [b|] //=.
    by case: (x1 $+ a) => [u|]. }
  by rewrite EL ER !op_assc.
Qed.

Lemma prod_sum_cancel_l [A B: Separation.type] (x y z w: A * B)
  (EQ1: prod_sum x y = Some w) (EQ2: prod_sum x z = Some w)
  : y = z.
Proof.
  move: EQ1 EQ2 => /prod_sum_speci [H1 H2] /prod_sum_speci [K1 K2].
  move: y z H1 H2 K1 K2 => [y1 y2] [z1 z2] /= H1 H2 K1 K2.
  by rewrite (op_cancel_l _ _ _ _ H1 K1) (op_cancel_l _ _ _ _ H2 K2).
Qed.

Lemma prod_sum_cancel_r [A B: Separation.type] (x y z w: A * B)
  (EQ1: prod_sum y x = Some w) (EQ2: prod_sum z x = Some w)
  : y = z.
Proof.
  move: EQ1 EQ2 => /prod_sum_speci [H1 H2] /prod_sum_speci [K1 K2].
  move: y z H1 H2 K1 K2 => [y1 y2] [z1 z2] /= H1 H2 K1 K2.
  by rewrite (op_cancel_r _ _ _ _ H1 K1) (op_cancel_r _ _ _ _ H2 K2).
Qed.

Lemma prod_sum_cross_split [A B: Separation.type] (a b c d z: A * B)
  (EQ1: prod_sum a b = Some z) (EQ2: prod_sum c d = Some z)
  : exists ac ad bc bd: A * B,
      prod_sum ac ad = Some a /\ prod_sum bc bd = Some b /\
      prod_sum ac bc = Some c /\ prod_sum ad bd = Some d.
Proof.
  move: EQ1 EQ2 => /prod_sum_speci [E11 E12] /prod_sum_speci [E21 E22].
  case: (op_cross_split _ _ _ _ _ E11 E21) => ac1 [ad1 [bc1 [bd1 [EQa1 [EQb1 [EQc1 EQd1]]]]]].
  case: (op_cross_split _ _ _ _ _ E12 E22) => ac2 [ad2 [bc2 [bd2 [EQa2 [EQb2 [EQc2 EQd2]]]]]].
  exists (ac1, ac2), (ad1, ad2), (bc1, bc2), (bd1, bd2).
  by do ![split]; apply/prod_sum_speci.
Qed.

HB.instance Definition _ (A B: NonEmpty.type) :=
  isNonEmpty.Build (A * B)%type (@non_empty_witness A, @non_empty_witness B).

HB.instance Definition _ (A B: Separation.type) :=
  hasOp.Build (A * B)%type (@prod_sum A B).

HB.instance Definition _ (A B: Separation.type) :=
  hasComm.Build (A * B)%type (@prod_sum_comm A B).

HB.instance Definition _ (A B: Separation.type) :=
  hasIdentity.Build (A * B)%type ($0, $0) (@prod_sum_id_l A B) (@prod_sum_id_r A B).

HB.instance Definition _ (A B: Separation.type) :=
  hasAssc.Build (A * B)%type (@prod_sum_assc A B).

HB.instance Definition _ (A B: Separation.type) :=
  hasCancel.Build (A * B)%type (@prod_sum_cancel_l A B) (@prod_sum_cancel_r A B).

HB.instance Definition _ (A B: Separation.type) :=
  hasCrossSplit.Build (A * B)%type (@prod_sum_cross_split A B).

Lemma prod_sum_spec [A B: Separation.type] (x y z: A * B):
  x $+ y = Some z <-> (x.1 $+ y.1 = Some z.1 /\ x.2 $+ y.2 = Some z.2).
Proof. exact: prod_sum_speci. Qed.
#[global] Hint Resolve -> prod_sum_spec: seplog.
#[global] Hint Resolve <- prod_sum_spec: seplog.
