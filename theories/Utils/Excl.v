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

From GallinaC.Utils Require Import Algebra.

Local Open Scope separation_scope.

(** * Exclusive access separation algebra

[Excl T] equips any type with a separation algebra of exclusive access
*)

Inductive excl (T: Type): Type :=
| Unowned
| Owned (x: T).

Arguments Unowned {T}.
Arguments Owned [T] x.

Definition excl_sum [T: Type] (a b: excl T): option (excl T) :=
  match a, b with
  | Unowned, y => Some y
  | x, Unowned => Some x
  | Owned _, Owned _ => None
  end.

Section Option.

  Definition excl_option [A: Type] (x: excl A): option A :=
    match x with
    | Unowned => None
    | Owned a => Some a
    end.

End Option.

Section Map.

  Definition excl_map [A B: Type] (f: A -> B) (x: excl A): excl B :=
    match x with
    | Unowned => Unowned
    | Owned a => Owned (f a)
    end.

  Lemma excl_map_id [A: Type] (x: excl A): excl_map id x = x.
  Proof. by case: x. Qed.

  Lemma excl_map_comp [A B C: Type] (f: A -> B) (g: B -> C) (x: excl A)
    : excl_map g (excl_map f x) = excl_map (ssrfun.comp g f) x.
  Proof. by case: x. Qed.

End Map.

Section ExclLaws.

  Context (T: Type).

  Lemma excl_sum_comm: forall x y: excl T, excl_sum x y = excl_sum y x.
  Proof using Type.
    by case=> [|x]; case=> [|y].
  Qed.

  Lemma excl_sum_id_l: forall x: excl T, excl_sum Unowned x = Some x.
  Proof using Type.
    by case=> [|x].
  Qed.

  Lemma excl_sum_id_r: forall x: excl T, excl_sum x Unowned = Some x.
  Proof using Type.
    by case=> [|x].
  Qed.

  Lemma excl_sum_assc: forall x y z: excl T,
      bind (Basics.flip (@excl_sum T) z) (excl_sum x y)
      = bind (excl_sum x) (excl_sum y z).
  Proof using Type.
    by case=> [|x]; case=> [|y]; case=> [|z].
  Qed.

  Lemma excl_sum_cancel_l: forall x y z w: excl T,
      excl_sum x y = Some w -> excl_sum x z = Some w -> y = z.
  Proof using Type.
    by move=> [|x] [|y] [|z] [|w] /= E1 E2; congruence.
  Qed.

  Lemma excl_sum_cancel_r: forall x y z w: excl T,
      excl_sum y x = Some w -> excl_sum z x = Some w -> y = z.
  Proof using Type.
    move=> x y z w E1 E2.
    rewrite excl_sum_comm in E1.
    rewrite excl_sum_comm in E2.
    exact: (excl_sum_cancel_l x y z w E1 E2).
  Qed.

  #[local] Definition excl_pick (x y: excl T): excl T :=
    match x, y with Owned _, Owned _ => x | _, _ => Unowned end.

  Lemma excl_sum_cross_split: forall a b c d z: excl T,
      excl_sum a b = Some z -> excl_sum c d = Some z ->
      exists ac ad bc bd: excl T,
        excl_sum ac ad = Some a /\ excl_sum bc bd = Some b /\
        excl_sum ac bc = Some c /\ excl_sum ad bd = Some d.
  Proof using Type.
    move=> a b c d z E1 E2.
    exists (excl_pick a c), (excl_pick a d), (excl_pick b c), (excl_pick b d).
    by move: a b c d E1 E2 => [|a] [|b] [|c] [|d] /= E1 E2; do !split; congruence.
  Qed.

  (* [excl] implements an exclusive ownership algebra.
     When a composition succeeds, at least one must not own the value *)
  Lemma excl_sum_excl: forall x y z: excl T,
      excl_sum x y = Some z -> x = Unowned \/ y = Unowned.
  Proof using Type.
    by case=> [|x]; case=> [|y]; case=> [|z] E; auto.
  Qed.

End ExclLaws.

HB.instance Definition _ (T: Type) :=
  hasOp.Build (excl T) (@excl_sum T).

HB.instance Definition _ (T: Type) :=
  hasComm.Build (excl T) (excl_sum_comm T).

HB.instance Definition _ (T: Type) :=
  hasIdentity.Build (excl T) Unowned (excl_sum_id_l T) (excl_sum_id_r T).

HB.instance Definition _ (T: Type) :=
  hasAssc.Build (excl T) (excl_sum_assc T).

HB.instance Definition _ (T: Type) :=
  hasCancel.Build (excl T) (excl_sum_cancel_l T) (excl_sum_cancel_r T).

HB.instance Definition _ (T: Type) :=
  hasCrossSplit.Build (excl T) (excl_sum_cross_split T).

#[global] Hint Resolve excl_sum_comm excl_sum_id_l excl_sum_id_r excl_sum_assc
  excl_sum_cancel_l excl_sum_cancel_r excl_sum_excl: seplog.
#[global] Hint Rewrite @excl_sum_id_l @excl_sum_id_r: seplog.
#[global] Hint Rewrite @excl_map_id @excl_map_comp: seplog.
