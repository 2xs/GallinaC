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

From Stdlib Require Import NArith Lia.
From Corelib Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

From GallinaC.Utils Require Export Algebra.

(** * Addresses

In a [Heap], memory is divided in blocks within which values are stored at
different offsets.

An address packages this information as an implicit pair composed of a [block]
and an [offset].

 *)

HB.mixin Record isAddr A :=
  {
    mkAddr: nat -> N.t -> A;
    block: A -> nat;
    offset: A -> N.t;

    mkAddr_block: forall b o, block (mkAddr b o) = b;
    mkAddr_offset: forall b o, offset (mkAddr b o) = o;
    mkAddr_ext: forall a, mkAddr (block a) (offset a) = a;
  }.
HB.structure Definition Addr := { A of isAddr A & hasEqDec A }.

Lemma mkAddr_inj [Ad: Addr.type] b b' o o'
  (EQ: mkAddr (s:=Ad) b o = mkAddr b' o')
  : b = b' /\ o = o'.
Proof.
  have Hb := mkAddr_block (s:=Ad) b o.
  have Ho := mkAddr_offset (s:=Ad) b o.
  rewrite EQ mkAddr_block in Hb.
  rewrite EQ mkAddr_offset in Ho.
  by split.
Qed.
#[global] Hint Resolve mkAddr_inj: seplog.

Lemma addr_ext [Ad: Addr.type] (a a': Ad)
  (BLK: block a = block a') (OFS: offset a = offset a')
  : a = a'.
Proof.
  by rewrite -(mkAddr_ext a) -(mkAddr_ext a') BLK OFS.
Qed.
#[global] Hint Resolve addr_ext | 20: seplog.

Definition shift_fw [Ad: Addr.type] (a: Ad) (s: N.t): Ad := mkAddr (block a) (offset a + s).

Definition shift_bw [Ad: Addr.type] (a: Ad) (s: N.t): option Ad :=
  if (s <=? offset a)%N then Some (mkAddr (block a) (offset a - s)) else None.

Definition Shift [Ad: Addr.type] (a: Ad) (s: N.t) a': Prop := shift_fw a s = a'.

Lemma shift_fw_spec [Ad: Addr.type] (a: Ad) s a': Shift a s a' <-> shift_fw a s = a'.
Proof. by []. Qed.
#[global] Hint Resolve shift_fw_spec: seplog.

Lemma Shift_fun [Ad: Addr.type] (a: Ad) s a' a'': Shift a s a' -> Shift a s a'' -> a'' = a'.
Proof. rewrite /Shift => <- <- //. Qed.
#[global] Hint Resolve Shift_fun | 10: seplog.

Lemma Shift_inj [Ad: Addr.type] (a': Ad) a'' s a: Shift a' s a -> Shift a'' s a -> a'' = a'.
Proof.
  rewrite /Shift/shift_fw => EQ1 EQ2.
  rewrite -EQ1 in EQ2.
  case: (mkAddr_inj _ _ _ _ EQ2) => BLK OFS.
  apply: addr_ext => //.
  lia.
Qed.
#[global] Hint Resolve Shift_inj | 10: seplog.

Lemma shift_bw_spec [Ad: Addr.type] (a: Ad) s a': Shift a' s a <-> shift_bw a s = Some a'.
Proof.
  rewrite /Shift/shift_fw/shift_bw; split.
  - move=> <-.
    rewrite mkAddr_block mkAddr_offset.
    have -> : (s <=? offset a' + s)%N = true by apply N.leb_le; lia.
    have -> : (offset a' + s - s = offset a')%N by lia.
    by rewrite mkAddr_ext.
  - case E: (s <=? offset a)%N => // - [<-].
    rewrite mkAddr_block mkAddr_offset.
    apply: addr_ext; rewrite ?mkAddr_block ?mkAddr_offset //.
    move: E => /N.leb_le; lia.
Qed.
#[global] Hint Resolve shift_bw_spec: seplog.

Lemma shift_fw_0 [Ad: Addr.type] (a: Ad): shift_fw a 0 = a.
Proof. by rewrite /shift_fw N.add_0_r mkAddr_ext. Qed.
#[global] Hint Resolve shift_fw_0: seplog.
#[global] Hint Rewrite @shift_fw_0: seplog.

Lemma shift_fw_twice [Ad: Addr.type] (a: Ad) n1 n2: shift_fw (shift_fw a n1) n2 = shift_fw a (n1 + n2).
Proof.
  rewrite /shift_fw mkAddr_block mkAddr_offset.
  by rewrite N.add_assoc.
Qed.
#[global] Hint Resolve shift_fw_twice: seplog.
#[global] Hint Rewrite @shift_fw_twice: seplog.

Lemma shift_fw_block [Ad: Addr.type] (a: Ad) s: block (shift_fw a s) = block a.
Proof. by rewrite /shift_fw mkAddr_block. Qed.
#[global] Hint Resolve shift_fw_block: seplog.
#[global] Hint Rewrite @shift_fw_block: seplog.

Lemma shift_fw_offset [Ad: Addr.type] (a: Ad) s: offset (shift_fw a s) = (offset a + s)%N.
Proof. by rewrite /shift_fw mkAddr_offset. Qed.
#[global] Hint Resolve shift_fw_offset: seplog.
#[global] Hint Rewrite @shift_fw_offset: seplog.

Lemma Shift_imm [Ad: Addr.type] (a: Ad) s: Shift a s (shift_fw a s).
Proof. by []. Qed.
#[global] Hint Resolve Shift_imm: seplog.
