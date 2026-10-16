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
From HB Require Import structures.

From Stdlib Require Import Arith ZArith List SetoidList.

From GallinaC.Imp Require Import Heap Store Intops.
From GallinaC.Imp Require Export Value.
From GallinaC.Compiler.Common Require Import Types.

Inductive Sized [Ad Pt] : @value Ad Pt -> Prop :=
| sized_bool: forall b, Sized (v_bool b)
| sized_nat: forall n, Sized (v_nat n)
| sized_ofst: forall n, Sized (v_ofst n)
| sized_ptr: forall p, Sized (v_ptr p)
.

Definition sized [Ad Pt] (v: @value Ad Pt): bool :=
  match v with
  | v_bool _ => true
  | v_tt => false
  | v_nat _ => true
  | v_ofst _ => true
  | v_ptr _ => true
  end.

Inductive wt_value Ad Pt: @value Ad Pt -> type -> Prop :=
| wt_v_tt: wt_value Ad Pt v_tt t_unit
| wt_v_bool: forall b, wt_value Ad Pt (v_bool b) t_bool
| wt_v_nat: forall n, wt_value Ad Pt (v_nat n) t_nat
| wt_v_ofst: forall n, wt_value Ad Pt (v_ofst n) t_ofst
| wt_v_ptr: forall p, wt_value Ad Pt (v_ptr p) t_ptr
.
Arguments wt_value [Ad Pt].
Arguments wt_v_tt {Ad Pt}.
Arguments wt_v_bool [Ad Pt].
Arguments wt_v_nat [Ad Pt].
Arguments wt_v_ofst [Ad Pt].
Arguments wt_v_ptr [Ad Pt].

Definition type_of_value [Ad Pt] (v: @value Ad Pt): type :=
  match v with
  | v_tt => t_unit
  | v_bool _ => t_bool
  | v_nat _ => t_nat
  | v_ofst _ => t_ofst
  | v_ptr _ => t_ptr
  end.

Module Facts.

  Lemma sized_spec [Ad Pt]: forall v, Bool.reflect (Sized v) (@sized Ad Pt v).
  Proof.
    case=> [|b|n|o|p] /=; constructor; try by constructor.
    by move=> C; inversion C.
  Qed.

  Lemma sized_or_unit_dec [Ad Pt]: forall v, (@Sized Ad Pt v * (v <> v_tt))%type + { v = v_tt }.
  Proof.
    case=> [|b|n|o|p]; first by right.
    all: by left; split; [ constructor | discriminate ].
  Qed.

  Lemma type_of_value_correct {Ad Pt v}: wt_value v (@type_of_value Ad Pt v).
  Proof.
    by case v as [|b|n|o|p]; constructor.
  Qed.

  Lemma type_of_value_complete {Ad Pt v t} (WT: wt_value v t): @type_of_value Ad Pt v = t.
  Proof.
    by case WT.
  Qed.

  Lemma wt_value_fun [Ad Pt v t1 t2]:
    forall (WT1: @wt_value Ad Pt v t1) (WT2: @wt_value Ad Pt v t2)
    , t2 = t1.
  Proof.
    by case => [|b|n|o|p] WT; inversion WT.
  Qed.
  #[global] Hint Resolve wt_value_fun: deep_gallinac.

  Lemma wt_value_sized [Ad Pt v t]:
    forall (WT: @wt_value Ad Pt v t) (SIZED: Value.Sized v)
    , Types.Sized t.
  Proof.
    by case => [|b|n|o|p] SIZED; first [ constructor | inversion SIZED ].
  Qed.
  #[global] Hint Resolve wt_value_sized: deep_gallinac.

End Facts.

