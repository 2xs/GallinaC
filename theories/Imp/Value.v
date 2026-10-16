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

From Stdlib Require Import NArith Arith.
From Stdlib Require Import BinInt.
From compcert Require Archi.
From compcert.lib Require Integers.
From GallinaC.Utils Require Import Algebra.
From GallinaC.Imp Require Intops Uintptr.
From GallinaC.Imp Require Import Storable.
From GallinaC.Imp Require Export Heap.

Local Open Scope separation_scope.

Definition memword_bytes: nat := if Archi.ptr64 then 8%nat else 4%nat.

Lemma memword_bytes_pos: (0 < memword_bytes)%nat.
Proof.
  unfold memword_bytes; destruct Archi.ptr64; apply Nat.lt_0_succ.
Qed.

Lemma memword_bytes_small64 (ARCHI64: Archi.ptr64 = true)
  : (0 <= Z.of_N (N.of_nat memword_bytes) <= Integers.Int64.max_unsigned)%Z.
Proof.
  unfold memword_bytes; destruct Archi.ptr64; split; vm_compute; discriminate.
Qed.

Lemma memword_bytes_small32 (ARCHI32: Archi.ptr64 = false)
  : (0 <= Z.of_N (N.of_nat memword_bytes) <= Integers.Int.max_unsigned)%Z.
Proof.
  unfold memword_bytes; destruct Archi.ptr64; split; vm_compute; discriminate.
Qed.

Definition alloc_max_size: N :=
  Z.to_N (Z.div (Intops.Unsigned.max_unsigned Uintptr.n_ofst_t)
            (Z.of_nat memword_bytes)).

Inductive value [Ad: Addr.type] (Pt: Ptr.type Ad) :=
| v_tt   : value Pt
| v_bool : forall (b: bool), value Pt
| v_nat  : forall (n: nat), value Pt
| v_ofst : forall (n: N), value Pt
| v_ptr  : Pt -> value Pt
.
Arguments v_tt {Ad Pt}.
Arguments v_bool [Ad Pt].
Arguments v_nat [Ad Pt].
Arguments v_ofst [Ad Pt].
Arguments v_ptr [Ad Pt].

Section Value.
  Context [Ad: Addr.type] (Pt: Ptr.type Ad).

  Definition value_eqb (v w: value Pt): bool :=
    match v, w with
    | v_tt, v_tt => true
    | v_bool b1, v_bool b2 => Bool.eqb b1 b2
    | v_nat n1, v_nat n2 => Nat.eqb n1 n2
    | v_ofst n1, v_ofst n2 => N.eqb n1 n2
    | v_ptr p1, v_ptr p2 => eqb p1 p2
    | _, _ => false
    end.

  Lemma value_eqb_spec (v w: value Pt): Bool.reflect (v = w) (value_eqb v w).
  Proof.
    case: v => [|b|n|o|p]; case: w => [|b0|n0|o0|p0] /=; try by constructor; congruence.
    - by case: (Bool.eqb_spec b b0) => [->|NE]; constructor; congruence.
    - by case: (Nat.eqb_spec n n0) => [->|NE]; constructor; congruence.
    - by case: (N.eqb_spec o o0) => [->|NE]; constructor; congruence.
    - by case: (eqb_spec p p0) => [->|NE]; constructor; congruence.
  Qed.

  (* decoders *)
  Definition dec_unit (v: value Pt) := match v with v_tt => Some tt | _ => None end.
  Definition dec_bool (v: value Pt) := match v with v_bool b => Some b | _ => None end.
  Definition dec_nat  (v: value Pt) := match v with v_nat n => Some n | _ => None end.
  Definition dec_ofst (v: value Pt) := match v with v_ofst n => Some n | _ => None end.
  Definition dec_ptr  (v: value Pt) := match v with v_ptr p => Some p | _ => None end.

  Definition enc_unit (_: unit): value Pt := v_tt.
  Lemma unit_ed: forall o, dec_unit (enc_unit o) = Some o. Proof. by case. Qed.
  Lemma unit_de: forall v o, dec_unit v = Some o -> enc_unit o = v. Proof. by case. Qed.
  Lemma bool_ed: forall o, dec_bool (v_bool o) = Some o. Proof. by []. Qed.
  Lemma bool_de: forall v o, dec_bool v = Some o -> v_bool o = v. Proof. by case=> //= b o [<-]. Qed.
  Lemma nat_ed: forall o, dec_nat (v_nat o) = Some o. Proof. by []. Qed.
  Lemma nat_de: forall v o, dec_nat v = Some o -> v_nat o = v. Proof. by case=> //= n o [<-]. Qed.
  Lemma ofst_ed: forall o, dec_ofst (v_ofst o) = Some o. Proof. by []. Qed.
  Lemma ofst_de: forall v o, dec_ofst v = Some o -> v_ofst o = v. Proof. by case=> //= n o [<-]. Qed.
  Lemma ptr_ed: forall o, dec_ptr (v_ptr o) = Some o. Proof. by []. Qed.
  Lemma ptr_de: forall v o, dec_ptr v = Some o -> v_ptr o = v. Proof. by case=> //= p o [<-]. Qed.
  Lemma id_de (v x: value Pt): Some v = Some x -> x = v. Proof. by move=> [->]. Qed.
End Value.

HB.instance Definition _ [Ad: Addr.type] (Pt: Ptr.type Ad) := isNonEmpty.Build (value Pt) (@v_tt Ad Pt).
HB.instance Definition _ [Ad: Addr.type] (Pt: Ptr.type Ad) :=
  hasEqDec.Build (value Pt) (value_eqb Pt) (value_eqb_spec Pt).

(* Storable instances, declared once, parametric over P, keyed on the payload. *)
HB.instance Definition _ [Ad: Addr.type] (Pt: Ptr.type Ad) :=
  isStorable.Build (value Pt) unit (enc_unit Pt) (dec_unit Pt) (unit_ed Pt) (unit_de Pt).
HB.instance Definition _ [Ad: Addr.type] (Pt: Ptr.type Ad) :=
  isStorable.Build (value Pt) bool (@v_bool Ad Pt) (dec_bool Pt) (bool_ed Pt) (bool_de Pt).
HB.instance Definition _ [Ad: Addr.type] (Pt: Ptr.type Ad) :=
  isStorable.Build (value Pt) nat (@v_nat Ad Pt) (dec_nat Pt) (nat_ed Pt) (nat_de Pt).
HB.instance Definition _ [Ad: Addr.type] (Pt: Ptr.type Ad) :=
  isStorable.Build (value Pt) N (@v_ofst Ad Pt) (dec_ofst Pt) (ofst_ed Pt) (ofst_de Pt).
#[non_forgetful_inheritance]
HB.instance Definition _ [Ad: Addr.type] (Pt: Ptr.type Ad) :=
  isStorable.Build (value Pt) Pt (@v_ptr Ad Pt) (dec_ptr Pt) (ptr_ed Pt) (ptr_de Pt).
HB.instance Definition _ [Ad: Addr.type] (Pt: Ptr.type Ad) :=
  isStorable.Build (value Pt) (value Pt) id (@Some (value Pt)) (fun _ => erefl) (@id_de Ad Pt).
