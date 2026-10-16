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

From Stdlib Require Import Arith NArith Psatz.

From GallinaC.Utils Require Import Algebra Excl UnitExt OptionExt.
From GallinaC.Imp Require Import Value Addr Memory RWMemory.
From GallinaC.Models Require Import Pointer.

Local Open Scope separation_scope.

(** * Block memory

A canonical model of block-structured memories, shared by the store and heap
models.

A memory maps a block index and an offset to at most one value. The definition
guarantees that each value is canonical by construction, similar to CompCert's
[PTree].

A top-level inductive distinguishes between an empty and non-empty memory.
For non-empty memories a custom inductive encodes a necessarily non-empty list. At each position except the last, a value might be either present or absent. The last offset must necessarily be filled.

The tail position element is parametric: at [unit] it carries no additional information, at [excl nat] it carries the allocator. When the memory is empty, it is directly stored by the empty case of the top-level inductive. Otherwise, it is at the tail of the non-empty block list. The [nat] encodes the gap between the current top value and the next generated block.

Two conversions, [to_mem] and [to_tail], allow respectively to drop the [excl nat] from a memory and replace it with a [unit] and to extract the tail element, either a [excl nat] or a [unit].

Examples:
- [MEmpty tt]: Empty memory no allocator at all
- [MEmpty Unowned]: Empty memory, empty allocator but may be joined with a non-empty one
- [MEmpty (Owned 0)]: Next generated bid is [0]
- [MEmpty (Owned 3)]: Next generated bid is [3]
- [MLive (M'Cons _ (M'Tail _ (Owned 0)))]: Next generated bid is [2]
- [MLive (M'Cons _ (M'Tail _ (Owned 2)))]: Next generated bid is [4]
 *)
Inductive block :=
| BTail (v: value Pointer.t)
| BCons (e: excl (value Pointer.t)) (b: block)
.

Fixpoint block_sum (x y: block): option block :=
  match x, y with
  | BTail _, BTail _ => None
  | BCons ex x, BCons ey y =>
      match ex $+ ey, block_sum x y with
      | Some o, Some b => Some (BCons o b)
      | None, _ | _, None => None
      end
  | BTail v, BCons e b
  | BCons e b, BTail v
    =>
      match (Owned v) $+ e with
      | Some e => Some (BCons e b)
      | None => None
      end
  end.

Lemma block_sum_ne_l: forall x y: block, block_sum x y <> Some x.
Proof.
  elim=> [v|ex xb IH]; case=> [w|ey yb] //=.
  - by case: ey => [|ey].
  - by case: ex => [|ex].
  - case: ex => [|ex]; case: ey => [|ey] //=;
    case E: (block_sum xb yb) => [t|] //=;
    by move=> [Et]; rewrite Et in E; move: (IH _ E).
Qed.

Lemma block_sum_comm: forall x y: block, block_sum x y = block_sum y x.
Proof.
  elim=> [v|ex xb IH]; case=> [w|ey yb] //=.
  by rewrite IH; case: ex => [|ex]; case: ey => [|ey].
Qed.

Lemma block_sum_assc: forall x y z: block,
    bind (Basics.flip block_sum z) (block_sum x y)
    = bind (block_sum x) (block_sum y z).
Proof.
  elim=> [v|ex xb IH]; case=> [w|ey yb]; case=> [u|ez zb];
    rewrite /Basics.flip //=.
  - by case: ez => [|ez].
  - by case: ey => [|ey].
  - by case: ey => [|ey]; case: ez => [|ez] //=; case: (block_sum yb zb).
  - by case: ex => [|ex].
  - by case: ex => [|ex]; case: ez => [|ez] //=; case: (block_sum xb zb).
  - by case: ex => [|ex]; case: ey => [|ey] //=; case: (block_sum xb yb).
  - move: (IH yb zb); rewrite /Basics.flip;
    case: ex => [|ex]; case: ey => [|ey]; case: ez => [|ez] //=;
    case E1: (block_sum xb yb) => [t|] //=;
    case E2: (block_sum yb zb) => [s|] //=;
    by [move=> ->; case: (block_sum xb s) | move=> -> | move=> <-].
Qed.

Lemma block_sum_cancel_l: forall x y z w: block,
    block_sum x y = Some w -> block_sum x z = Some w -> y = z.
Proof.
  elim=> [v|ex xb IH] y z w; case: y => [u|ey yb]; case: z => [u'|ez zb] //=.
  - by case: ey => [|ey]; case: ez => [|ez] //=; move=> E1 E2; congruence.
  - by case: ex => [|ex] //=; move=> E1 E2; congruence.
  - case: ex => [|ex] //=; case E: (block_sum xb zb) => [t|] //=.
    move=> [<-] [E1 E2]; rewrite E2 in E.
    by case: (block_sum_ne_l xb zb E).
  - case: ex => [|ex] //=; case E: (block_sum xb yb) => [t|] //=.
    move=> E1 E2; rewrite -E2 in E1; case: E1 => _ E4; rewrite E4 in E.
    by case: (block_sum_ne_l xb yb E).
  - case: ex => [|ex]; case: ey => [|ey]; case: ez => [|ez] //=;
    case E1: (block_sum xb yb) => [t|] //=;
    case E2: (block_sum xb zb) => [s|] //=;
    move=> E3 E4; rewrite -E4 in E3; case: E3 => *; subst;
    by rewrite (IH _ _ _ E1 E2).
Qed.

Lemma block_sum_cancel_r: forall x y z w: block,
    block_sum y x = Some w -> block_sum z x = Some w -> y = z.
Proof.
  move=> x y z w E1 E2.
  rewrite block_sum_comm in E1; rewrite block_sum_comm in E2.
  exact: (block_sum_cancel_l x y z w E1 E2).
Qed.

HB.instance Definition _ := hasOp.Build block block_sum.
HB.instance Definition _ := hasComm.Build block block_sum_comm.
HB.instance Definition _ := hasAssc.Build block block_sum_assc.
HB.instance Definition _ := hasCancel.Build block block_sum_cancel_l block_sum_cancel_r.

Definition osum [A: Type] (f: A -> A -> option A) (o1 o2: option A)
  : option (option A) :=
  match o1 with
  | Some a1 => match o2 with
               | Some a2 => option_map Some (f a1 a2)
               | None => Some (Some a1)
               end
  | None => Some o2
  end.

Lemma osum_block_comm: forall x y: option block,
    (osum block_sum) x y = (osum block_sum) y x.
Proof.
  by case=> [b1|]; case=> [b2|] //=; rewrite block_sum_comm.
Qed.

Lemma osum_block_assc: forall x y z: option block,
    bind (Basics.flip (osum block_sum) z) ((osum block_sum) x y)
    = bind ((osum block_sum) x) ((osum block_sum) y z).
Proof.
  case=> [b1|]; case=> [b2|]; case=> [b3|]; rewrite /Basics.flip //=;
    try by case: (block_sum _ _).
  move: (block_sum_assc b1 b2 b3); rewrite /Basics.flip.
  case B12: (block_sum b1 b2) => [b12|] /=;
    case B23: (block_sum b2 b3) => [b23|] /= => H;
    by rewrite ?H //= -?H //=; case: (block_sum _ _).
Qed.

Lemma osum_block_ss: forall b1 b2: block,
    (osum block_sum) (Some b1) (Some b2)
    = bind (fun b => Some (Some b)) (block_sum b1 b2).
Proof.
  by [].
Qed.

Lemma osum_block_swap: forall x y z: option block,
    bind ((osum block_sum) x) ((osum block_sum) y z) = bind ((osum block_sum) y) ((osum block_sum) x z).
Proof.
  move=> x y z.
  by rewrite -osum_block_assc (osum_block_comm x y) osum_block_assc.
Qed.

Lemma osum_block_cancel_l: forall x y z w: option block,
    (osum block_sum) x y = Some w -> (osum block_sum) x z = Some w -> y = z.
Proof.
  case=> [b1|] y z w; last by move=> /= [<-] [->].
  case: y => [b2|]; case: z => [b3|] //=.
  - case E2: (block_sum b1 b2) => [c2|] //=;
    case E3: (block_sum b1 b3) => [c3|] //=.
    move=> [<-] [Ec]; rewrite Ec in E3.
    by rewrite (block_sum_cancel_l _ _ _ _ E2 E3).
  - case E2: (block_sum b1 b2) => [c2|] //=.
    move=> [<-] [Ec]; rewrite Ec in E2.
    by case: (block_sum_ne_l _ _ E2).
  - case E3: (block_sum b1 b3) => [c3|] //=.
    move=> [<-] [Ec]; rewrite Ec in E3.
    by case: (block_sum_ne_l _ _ E3).
Qed.

Lemma osum_block_cancel_r: forall x y z w: option block,
    (osum block_sum) y x = Some w -> (osum block_sum) z x = Some w -> y = z.
Proof.
  move=> x y z w E1 E2.
  rewrite osum_block_comm in E1; rewrite osum_block_comm in E2.
  exact: (osum_block_cancel_l x y z w E1 E2).
Qed.
Fixpoint block_get (b: block) (o: nat): option (value Pointer.t) :=
  match b, o with
  | BTail v, O => Some v
  | BTail _, S _ => None
  | BCons e _, O => excl_option e
  | BCons _ b, S o => block_get b o
  end.

Lemma block_get_nonempty (b: block): exists o v, block_get b o = Some v.
Proof.
  elim: b => [v|e b [o [v E]]].
  - by exists 0, v.
  - by exists (S o), v.
Qed.

Lemma block_ext (b1: block): forall b2: block,
    (forall o, block_get b1 o = block_get b2 o) -> b1 = b2.
Proof.
  elim: b1 => [v1|e1 b1 IH]; case=> [v2|e2 b2] EXT.
  - by move: (EXT 0) => /= [->].
  - exfalso.
    case: (block_get_nonempty b2) => [o [v E]].
    by move: (EXT (S o)) => /=; rewrite E.
  - exfalso.
    case: (block_get_nonempty b1) => [o [v E]].
    by move: (EXT (S o)) => /=; rewrite E.
  - have EXT': forall o, block_get b1 o = block_get b2 o
      by move=> o; exact: (EXT (S o)).
    move: {EXT} (EXT 0) => /= E0.
    rewrite (IH b2 EXT').
    by case: e1 E0 => [|x]; case: e2 => [|y] //= [->].
Qed.

Lemma block_of_cells (b: block) (o: option block)
  (EXT: forall off, block_get b off
                    = match o with Some b' => block_get b' off | None => None end)
  : o = Some b.
Proof.
  case: o EXT => [b'|] EXT.
  - by rewrite (block_ext b b' EXT).
  - exfalso.
    case: (block_get_nonempty b) => [off [v E]].
    by move: (EXT off); rewrite E.
Qed.

Fixpoint block_one (o: nat) (v: value Pointer.t): block :=
  match o with
  | O => BTail v
  | S o => BCons Unowned (block_one o v)
  end.

Lemma block_get_one (o: nat) (v: value Pointer.t): forall o',
    block_get (block_one o v) o' = if Nat.eqb o' o then Some v else None.
Proof.
  by elim: o => [|o IH] [|o'] //=.
Qed.

Fixpoint block_full (n: nat) (v: value Pointer.t): block :=
  match n with
  | O => BTail v
  | S n => BCons (Owned v) (block_full n v)
  end.

Lemma block_get_full (n: nat) (v: value Pointer.t): forall o,
    block_get (block_full n v) o = if Nat.leb o n then Some v else None.
Proof.
  by elim: n => [|n IH] [|o] //=.
Qed.

Fixpoint block_set (b: block) (o: nat) (v: value Pointer.t): option block :=
  match b with
  | BTail _ =>
      match o with
      | O => Some (BTail v)
      | S _ => None
      end
  | BCons e b =>
      match o with
      | O =>
          match e with
          | Unowned => None
          | Owned _ => Some (BCons (Owned v) b)
          end
      | S o => option_map (BCons e) (block_set b o v)
      end
  end.

Lemma block_set_defined (b: block): forall (o: nat) (v: value Pointer.t),
    (exists v0, block_get b o = Some v0) <-> (exists b', block_set b o v = Some b').
Proof.
  elim: b => [w|e b IH] [|o] v /=.
  - by split=> _; eexists.
  - by split=> -[x E].
  - case: e => [|w] /=.
    + by split=> -[x E].
    + by split=> _; eexists.
  - rewrite (IH o v).
    split=> -[x E].
    + by exists (BCons e x); rewrite E.
    + move: E; case E': (block_set b o v) => [b'|] //= _.
      by exists b'.
Qed.

Lemma block_set_get (b: block): forall (o: nat) (v: value Pointer.t) (b': block),
    block_set b o v = Some b'
    -> forall o', block_get b' o' = if Nat.eqb o' o then Some v else block_get b o'.
Proof.
  elim: b => [w|e b IH] [|o] v b' //=.
  - by move=> [<-] [|o'].
  - case: e => [|w] //= [<-].
    by case=> [|o'].
  - case E: (block_set b o v) => [b''|] //= [<-].
    case=> [|o'] //=.
    exact: (IH o v b'' E o').
Qed.

Definition vclash (v1 v2: value Pointer.t): option (value Pointer.t) := None.

Lemma osum_None_l [A: Type] (f: A -> A -> option A) (x: option A):
  osum f None x = Some x.
Proof. by []. Qed.

Lemma osum_None_r [A: Type] (f: A -> A -> option A) (x: option A):
  osum f x None = Some x.
Proof. by case: x. Qed.

Lemma block_sum_get (b1: block): forall (b2 b: block),
    block_sum b1 b2 = Some b
    -> forall o, osum vclash (block_get b1 o) (block_get b2 o) = Some (block_get b o).
Proof.
  elim: b1 => [v|ex xb IH]; case=> [w|ey yb] b //=.
  - rewrite /op /=; case: ey => [|y] //= [<-].
    by case=> [|o'] //=; rewrite osum_None_l.
  - rewrite /op /=; case: ex => [|x] //= [<-].
    by case=> [|o'] //=; rewrite osum_None_r.
  - case: ex => [|x]; case: ey => [|y]; rewrite /op //=;
    case E: (block_sum xb yb) => [t|] //= [<-]; case=> [|o'] //=.
    + exact: (IH yb t E o').
    + exact: (IH yb t E o').
    + exact: (IH yb t E o').
Qed.

Lemma block_sum_some (b1: block): forall b2: block,
    (forall o, osum vclash (block_get b1 o) (block_get b2 o) <> None)
    -> exists b, block_sum b1 b2 = Some b.
Proof.
  elim: b1 => [v1|e1 b1 IH]; case=> [v2|e2 b2] CELLS //=.
  - exfalso.
    by move: (CELLS 0) => /=.
  - rewrite /op /=.
    case: e2 CELLS => [|w] CELLS.
    + by eexists.
    + exfalso.
      by move: (CELLS 0) => /=.
  - rewrite /op /=.
    case: e1 CELLS => [|w] CELLS.
    + by eexists.
    + exfalso.
      by move: (CELLS 0) => /=.
  - have CELLS': forall o, osum vclash (block_get b1 o) (block_get b2 o) <> None
      by move=> o; exact: (CELLS (S o)).
    case: (IH b2 CELLS') => [b Eb].
    rewrite /op /= Eb.
    case: e1 CELLS => [|w1]; case: e2 => [|w2] CELLS.
    + by eexists.
    + by eexists.
    + by eexists.
    + exfalso.
      by move: (CELLS 0) => /=.
Qed.

Lemma osum_block_ext (o1 o2 o: option block)
  (CELLS: forall off, osum vclash
      (match o1 with Some b => block_get b off | None => None end)
      (match o2 with Some b => block_get b off | None => None end)
    = Some (match o with Some b => block_get b off | None => None end))
  : osum block_sum o1 o2 = Some o.
Proof.
  case: o1 CELLS => [b1|]; case: o2 => [b2|] CELLS /=.
  - have NN: forall off, osum vclash (block_get b1 off) (block_get b2 off) <> None
      by move=> off; rewrite CELLS.
    case: (block_sum_some b1 b2 NN) => [b Eb].
    rewrite Eb /= (block_of_cells b o) // => off.
    by move: (block_sum_get b1 b2 b Eb off); rewrite CELLS => -[->].
  - rewrite (block_of_cells b1 o) // => off.
    by move: (CELLS off); rewrite osum_None_r => -[->].
  - rewrite (block_of_cells b2 o) // => off.
    by move: (CELLS off) => /= -[->].
  - case: o CELLS => [b|] CELLS //.
    case: (block_get_nonempty b) => [off [v E]].
    by move: (CELLS off); rewrite E.
Qed.

Lemma osum_vclash_cross (ga gb gc gd gz: option (value Pointer.t))
  (E1: osum vclash ga gb = Some gz) (E2: osum vclash gc gd = Some gz)
  : osum vclash (if isSome gc then ga else None) (if isSome gd then ga else None) = Some ga
    /\ osum vclash (if isSome gc then gb else None) (if isSome gd then gb else None) = Some gb
    /\ osum vclash (if isSome gc then ga else None) (if isSome gc then gb else None) = Some gc
    /\ osum vclash (if isSome gd then ga else None) (if isSome gd then gb else None) = Some gd.
Proof.
  by move: ga gb gc gd gz E1 E2 => [va|] [vb|] [vc|] [vd|] [vz|] //= [->] [->].
Qed.

Definition odiff [A: Type] (f: A -> A -> option A) (o2 o1: option A): option A :=
  match o2 with
  | None => None
  | Some a2 => match o1 with
               | Some a1 => f a2 a1
               | None => Some a2
               end
  end.

Lemma odiff_vclash (o2 o1: option (value Pointer.t)):
  odiff vclash o2 o1 = match o1 with Some _ => None | None => o2 end.
Proof.
  by case: o2 => [v2|]; case: o1 => [v1|].
Qed.

Lemma odiff_None_r [A: Type] (f: A -> A -> option A) (x: option A):
  odiff f x None = x.
Proof.
  by case: x.
Qed.

Definition block_cons (e: excl (value Pointer.t)) (ob: option block)
  : option block :=
  match ob with
  | Some b => Some (BCons e b)
  | None => match e with
            | Owned v => Some (BTail v)
            | Unowned => None
            end
  end.

Lemma block_cons_get (e: excl (value Pointer.t)) (ob: option block) (o: nat):
  match block_cons e ob with
  | Some b => block_get b o
  | None => None
  end
  = match o with
    | O => excl_option e
    | S o => match ob with
             | Some b => block_get b o
             | None => None
             end
    end.
Proof.
  by case: ob => [b|]; case: e => [|v]; case: o => [|o].
Qed.

Fixpoint block_diff (b2 b1: block) {struct b2}: option block :=
  match b2 with
  | BTail v2 =>
      match block_get b1 0 with
      | Some _ => None
      | None => Some (BTail v2)
      end
  | BCons e2 b2 =>
      block_cons (match block_get b1 0 with
                  | Some _ => Unowned
                  | None => e2
                  end)
        (match b1 with
         | BTail _ => Some b2
         | BCons _ b1 => block_diff b2 b1
         end)
  end.

Lemma block_diff_get (b2: block): forall (b1: block) (o: nat),
    match block_diff b2 b1 with
    | Some b => block_get b o
    | None => None
    end
    = match block_get b1 o with
      | Some _ => None
      | None => block_get b2 o
      end.
Proof.
  elim: b2 => [v2|e2 b2 IH] b1 o /=.
  - case E: (block_get b1 0) => [w|]; case: o => [|o'] //=.
    + by rewrite E.
    + by case: (block_get b1 (S o')) => [w'|].
    + by rewrite E.
    + by case: (block_get b1 (S o')) => [w'|].
  - rewrite block_cons_get.
    case: o => [|o'] /=.
    + by case E: (block_get b1 0) => [w|].
    + case: b1 => [v1|e1 b1] /=.
      * by [].
      * exact: (IH b1 o').
Qed.

Fixpoint block_filter (k: nat -> bool) (b: block): option block :=
  match b with
  | BTail v => if k 0 then Some (BTail v) else None
  | BCons e b => block_cons (if k 0 then e else Unowned) (block_filter (fun o => k (S o)) b)
  end.

Lemma block_filter_get (b: block): forall (k: nat -> bool) (o: nat),
    match block_filter k b with Some b' => block_get b' o | None => None end
    = if k o then block_get b o else None.
Proof.
  elim: b => [v|e b IH] k o /=.
  - case: o => [|o] /=.
    + by case: (k 0).
    + by case: (k 0); case: (k (S o)).
  - rewrite block_cons_get.
    case: o => [|o] /=.
    + by case: (k 0); case: e.
    + exact: (IH (fun o => k (S o)) o).
Qed.

Definition oincl [A: Type] (g: A -> A -> bool) (o1 o2: option A): bool :=
  match o1 with
  | None => true
  | Some a1 => match o2 with
               | Some a2 => g a1 a2
               | None => false
               end
  end.
Section Inclusion.

  Context (veqb: value Pointer.t -> value Pointer.t -> bool)
          (veqb_spec: forall x y, Bool.reflect (x = y) (veqb x y)).

  Lemma oincl_spec (o1 o2: option (value Pointer.t)):
    Bool.reflect (forall v, o1 = Some v -> o2 = Some v) (oincl veqb o1 o2).
  Proof.
    case: o1 => [v1|]; case: o2 => [v2|] /=.
    - case: (veqb_spec v1 v2) => [->|NE]; constructor.
      + by move=> v [<-].
      + move=> H.
        move: (H v1 erefl) => [E].
        by rewrite E in NE.
    - constructor => H.
      by move: (H v1 erefl).
    - by constructor.
    - by constructor.
  Qed.

  Fixpoint block_incl (b1 b2: block): bool :=
    match b1 with
    | BTail v1 => oincl veqb (Some v1) (block_get b2 0)
    | BCons e1 b1 =>
        match b2 with
        | BTail _ => false
        | BCons e2 b2 => (oincl veqb (excl_option e1) (excl_option e2)
                          && block_incl b1 b2)%bool
        end
    end.

  Lemma block_incl_spec (b1: block): forall b2: block,
      Bool.reflect
        (forall o v, block_get b1 o = Some v -> block_get b2 o = Some v)
        (block_incl b1 b2).
  Proof.
    elim: b1 => [v1|e1 b1 IH] b2 /=.
    - case E0: (block_get b2 0) => [w|] /=.
      + case: (veqb_spec v1 w) => [->|NE]; constructor.
        * move=> o v; case: o => [|o'] //= [<-].
          exact: E0.
        * move=> H.
          move: (H 0 v1 erefl); rewrite E0 => -[E1].
          exact: (NE (esym E1)).
      + constructor => H.
        move: (H 0 v1 erefl); rewrite E0 => E1.
        by discriminate E1.
    - case: b2 => [v2|e2 b2].
      + constructor => H.
        case: (block_get_nonempty b1) => [o [v E]].
        by move: (H (S o) v E).
      + case: (oincl_spec (excl_option e1) (excl_option e2)) => [I|N] /=.
        * case: (IH b2) => [I'|N']; constructor.
          -- move=> o v; case: o => [|o'] /=.
             ++ exact: I.
             ++ exact: I'.
          -- move=> H; apply: N' => o v E.
             exact: (H (S o) v E).
        * constructor => H; apply: N => v E.
          exact: (H 0 v E).
  Qed.

End Inclusion.

Inductive mem' (A: Type) :=
| M'Tail (b: block) (a: A)
| M'Cons (o: option block) (m: mem' A)
.

Inductive mem (A: Type) :=
| MEmpty (a: A)
| MLive (m: mem' A)
.

Arguments M'Tail {A} b a.
Arguments M'Cons {A} o m.
Arguments MEmpty {A} a.
Arguments MLive {A} m.

Fixpoint mem'_map [A B: Type] (f: A -> B) (m: mem' A): mem' B :=
  match m with
  | M'Tail b a => M'Tail b (f a)
  | M'Cons o m => M'Cons o (mem'_map f m)
  end.

Definition mem_map [A B: Type] (f: A -> B) (m: mem A): mem B :=
  match m with
  | MEmpty a => MEmpty (f a)
  | MLive m => MLive (mem'_map f m)
  end.

HB.mixin Record hasShift T of Separation T := {
  rshift: T -> option T;
  runshift: T -> T;
  rshift_runshift: forall a: T, rshift (runshift a) = Some a;
  runshift_id: runshift id_e = id_e;
  rshift_sum: forall a b: T,
      bind rshift (a $+ b)
      = bind (fun a' => bind (fun b' => a' $+ b') (rshift b)) (rshift a);
  rshift_inj: forall a b c: T,
      rshift a = Some c -> rshift b = Some c -> a = b;
}.
HB.structure Definition AllocSlot := { T of Separation T & hasShift T }.

Section PureOps.

  Context {A: Type}.

  Fixpoint mem'_get (m: mem' A) (bi: nat): option block :=
    match m, bi with
    | M'Tail b _, O => Some b
    | M'Tail _ _, S _ => None
    | M'Cons o _, O => o
    | M'Cons _ m, S bi => mem'_get m bi
    end.

  Definition get (m: mem A) (bi o: nat): option (value Pointer.t) :=
    match m with
    | MEmpty _ => None
    | MLive m' =>
        match mem'_get m' bi with
        | Some b => block_get b o
        | None => None
        end
    end.

  Lemma mem'_get_nonempty (m: mem' A): exists bi b, mem'_get m bi = Some b.
  Proof.
    elim: m => [b a|o m [bi [b E]]].
    - by exists 0, b.
    - by exists (S bi), b.
  Qed.

  Fixpoint mem'_pad (k: nat) (m: mem' A): mem' A :=
    match k with
    | O => m
    | S k => M'Cons None (mem'_pad k m)
    end.

  Lemma mem'_get_pad_tail (k: nat) (b: block) (a: A): forall bi,
      mem'_get (mem'_pad k (M'Tail b a)) bi = if Nat.eqb bi k then Some b else None.
  Proof.
    by elim: k => [|k IH] [|bi] //=.
  Qed.

  Fixpoint mem'_set (m: mem' A) (bi o: nat) (v: value Pointer.t): option (mem' A) :=
    match m with
    | M'Tail b a =>
        match bi with
        | O => option_map (fun b => M'Tail b a) (block_set b o v)
        | S _ => None
        end
    | M'Cons ob m =>
        match bi with
        | O =>
            match ob with
            | Some b => option_map (fun b => M'Cons (Some b) m) (block_set b o v)
            | None => None
            end
        | S bi => option_map (M'Cons ob) (mem'_set m bi o v)
        end
    end.

  Definition set (m: mem A) (bi o: nat) (v: value Pointer.t): option (mem A) :=
    match m with
    | MEmpty _ => None
    | MLive m' => option_map MLive (mem'_set m' bi o v)
    end.

  Lemma mem'_set_defined (m: mem' A): forall (bi o: nat) (v: value Pointer.t),
      (exists v0, match mem'_get m bi with
                  | Some b => block_get b o
                  | None => None
                  end = Some v0)
      <-> (exists m', mem'_set m bi o v = Some m').
  Proof.
    elim: m => [b a|ob m IH] [|bi] o v /=.
    - rewrite (block_set_defined b o v).
      split=> -[x E].
      + by exists (M'Tail x a); rewrite E.
      + move: E; case E': (block_set b o v) => [b'|] //= _.
        by exists b'.
    - by split=> -[x E].
    - case: ob => [b|] /=.
      + rewrite (block_set_defined b o v).
        split=> -[x E].
        * by exists (M'Cons (Some x) m); rewrite E.
        * move: E; case E': (block_set b o v) => [b'|] //= _.
          by exists b'.
      + by split=> -[x E].
    - rewrite (IH bi o v).
      split=> -[x E].
      + by exists (M'Cons ob x); rewrite E.
      + move: E; case E': (mem'_set m bi o v) => [m'|] //= _.
        by exists m'.
  Qed.

  Lemma mem'_set_get (m: mem' A): forall (bi o: nat) (v: value Pointer.t) (m': mem' A),
      mem'_set m bi o v = Some m'
      -> forall bi' o',
          match mem'_get m' bi' with
          | Some b => block_get b o'
          | None => None
          end
          = if (Nat.eqb bi' bi && Nat.eqb o' o)%bool then Some v
            else match mem'_get m bi' with
                 | Some b => block_get b o'
                 | None => None
                 end.
  Proof.
    elim: m => [b a|ob m IH] [|bi] o v m' //=.
    - case E: (block_set b o v) => [b'|] //= [<-].
      case=> [|bi'] o' //=.
      exact: (block_set_get b o v b' E o').
    - case: ob => [b|] //=.
      case E: (block_set b o v) => [b'|] //= [<-].
      case=> [|bi'] o' //=.
      exact: (block_set_get b o v b' E o').
    - case E: (mem'_set m bi o v) => [m''|] //= [<-].
      case=> [|bi'] o' //=.
      exact: (IH bi o v m'' E bi' o').
  Qed.

  Lemma set_defined (m: mem A) (bi o: nat) (v: value Pointer.t):
    (exists v0, get m bi o = Some v0) <-> (exists m', set m bi o v = Some m').
  Proof.
    case: m => [a|m] /=.
    - by split=> -[x E].
    - rewrite (mem'_set_defined m bi o v).
      split=> -[x E].
      + by exists (MLive x); rewrite E.
      + move: E; case E': (mem'_set m bi o v) => [m'|] //= _.
        by exists m'.
  Qed.

  Lemma set_get (m m': mem A) (bi o: nat) (v: value Pointer.t)
    (EQ: set m bi o v = Some m') (bi' o': nat):
    get m' bi' o'
    = if (Nat.eqb bi' bi && Nat.eqb o' o)%bool then Some v else get m bi' o'.
  Proof.
    case: m EQ => [a|m] //=.
    case E: (mem'_set m bi o v) => [m''|] //= [<-].
    exact: (mem'_set_get m bi o v m'' E bi' o').
  Qed.

  Fixpoint mem'_nblocks (m: mem' A): nat :=
    match m with
    | M'Tail _ _ => 1
    | M'Cons _ m => S (mem'_nblocks m)
    end.

  Definition nblocks (m: mem A): nat :=
    match m with
    | MEmpty _ => 0
    | MLive m => mem'_nblocks m
    end.

  Lemma mem'_nblocks_pos (m: mem' A): 1 <= mem'_nblocks m.
  Proof.
    case: m => [b a|o m] /=; lia.
  Qed.

  Lemma mem'_get_ge (m: mem' A): forall bi, mem'_nblocks m <= bi -> mem'_get m bi = None.
  Proof.
    elim: m => [b a|o m IH] [|bi] /= GE //.
    - lia.
    - lia.
    - apply: IH; lia.
  Qed.

  Lemma get_nblocks_ge (m: mem A) (bi o: nat) (GE: nblocks m <= bi): get m bi o = None.
  Proof.
    case: m GE => [a|m] //= GE.
    by rewrite (mem'_get_ge m bi GE).
  Qed.

  Lemma mem'_get_last (m: mem' A):
    exists b, mem'_get m (Nat.pred (mem'_nblocks m)) = Some b.
  Proof.
    elim: m => [b a|o m [b E]] /=.
    - by exists b.
    - exists b.
      move: (mem'_nblocks_pos m) E.
      case: (mem'_nblocks m) => [|k] POS' E.
      + lia.
      + exact: E.
  Qed.

  Lemma mem_last_bound (m: mem A) (POS: 0 < nblocks m):
    exists o v, get m (Nat.pred (nblocks m)) o = Some v.
  Proof.
    case: m POS => [a|m] /= POS.
    - lia.
    - case: (mem'_get_last m) => [b E].
      case: (block_get_nonempty b) => [o [v E']].
      exists o, v.
      by rewrite E.
  Qed.

  Definition block_vacant (m: mem A) (bi: nat): bool :=
    match m with
    | MEmpty _ => true
    | MLive m' => match mem'_get m' bi with Some _ => false | None => true end
    end.

  Lemma block_vacant_spec (m: mem A) (bi: nat):
    Bool.reflect (forall o v, get m bi o <> Some v) (block_vacant m bi).
  Proof.
    case: m => [a|m] /=.
    - by constructor.
    - case E: (mem'_get m bi) => [b|]; constructor.
      + move=> H.
        case: (block_get_nonempty b) => [o [v E']].
        exact: (H o v E').
      + by move=> o v.
  Qed.

  Fixpoint mcovers (m: mem A) (bi: nat) (n: nat): bool :=
    match get m bi n with
    | Some _ =>
        match n with
        | O => true
        | S n' => mcovers m bi n'
        end
    | None => false
    end.

  Lemma mcovers_spec (m: mem A) (bi: nat): forall n,
      Bool.reflect (forall o, o <= n -> exists v, get m bi o = Some v) (mcovers m bi n).
  Proof.
    elim=> [|n IH] /=.
    - case E: (get m bi 0) => [v|]; constructor.
      + move=> o LE.
        have EQ: o = 0 by lia.
        subst o.
        by exists v.
      + move=> H.
        case: (H 0 (Nat.le_refl 0)) => [v Ev].
        by rewrite E in Ev.
    - case E: (get m bi (S n)) => [v|].
      + case: IH => [CC|NC]; constructor.
        * move=> o LE.
          case: (Nat.eq_dec o (S n)) => [EQ|NEQ].
          -- subst o.
             by exists v.
          -- apply: CC.
             lia.
        * move=> H.
          apply: NC.
          move=> o LE.
          apply: H.
          lia.
      + constructor.
        move=> H.
        case: (H (S n) (Nat.le_refl (S n))) => [w Ew].
        by rewrite E in Ew.
  Qed.

  Lemma mem'_nblocks_pad_tail (k: nat) (b: block) (a: A):
    mem'_nblocks (mem'_pad k (M'Tail b a)) = S k.
  Proof.
    by elim: k => [|k IH] //=; rewrite IH.
  Qed.

  Section Incl.

    Context (veqb: value Pointer.t -> value Pointer.t -> bool)
            (veqb_spec: forall x y, Bool.reflect (x = y) (veqb x y)).

    Fixpoint mem'_incl (m1 m2: mem' A): bool :=
      match m1 with
      | M'Tail b1 _ =>
          match mem'_get m2 0 with
          | Some b2 => block_incl veqb b1 b2
          | None => false
          end
      | M'Cons ob1 m1 =>
          match m2 with
          | M'Tail _ _ => false
          | M'Cons ob2 m2 => (oincl (block_incl veqb) ob1 ob2 && mem'_incl m1 m2)%bool
          end
      end.

    Lemma mem'_incl_spec (m1: mem' A): forall m2: mem' A,
        Bool.reflect
          (forall bi o v,
              match mem'_get m1 bi with
              | Some b => block_get b o
              | None => None
              end = Some v
              -> match mem'_get m2 bi with
                 | Some b => block_get b o
                 | None => None
                 end = Some v)
          (mem'_incl m1 m2).
    Proof.
      elim: m1 => [b1 a1|ob1 m1 IH] m2 /=.
      - case E2: (mem'_get m2 0) => [b2|].
        + case: (block_incl_spec veqb veqb_spec b1 b2) => [I|N]; constructor.
          * move=> bi o v; case: bi => [|bi'] //= E.
            rewrite E2.
            exact: (I o v E).
          * move=> H; apply: N => o v E.
            move: (H 0 o v) => /=.
            rewrite E2.
            by move=> /(_ E).
        + constructor => H.
          case: (block_get_nonempty b1) => [o [v E]].
          move: (H 0 o v) => /=.
          rewrite E2.
          by move=> /(_ E).
      - case: m2 => [b2 a2|ob2 m2].
        + constructor => H.
          case: (mem'_get_nonempty m1) => [bi [b E]].
          case: (block_get_nonempty b) => [o [v E']].
          move: (H (S bi) o v) => /=.
          rewrite E.
          by move=> /(_ E').
        + case: ob1 => [b1|] /=.
          * case: ob2 => [b2|] /=.
            -- case: (block_incl_spec veqb veqb_spec b1 b2) => [I|N] /=.
               ++ case: (IH m2) => [I'|N']; constructor.
                  ** move=> bi o v; case: bi => [|bi'] /=.
                     --- exact: I.
                     --- exact: I'.
                  ** move=> H; apply: N' => bi o v E.
                     exact: (H (S bi) o v E).
               ++ constructor => H; apply: N => o v E.
                  exact: (H 0 o v E).
            -- constructor => H.
               case: (block_get_nonempty b1) => [o [v E]].
               by move: (H 0 o v E).
          * case: (IH m2) => [I'|N']; constructor.
            -- move=> bi o v; case: bi => [|bi'] //=.
               exact: I'.
            -- move=> H; apply: N' => bi o v E.
               exact: (H (S bi) o v E).
    Qed.

  End Incl.

End PureOps.

Lemma mem'_get_map [A B: Type] (f: A -> B) (m: mem' A): forall bi: nat,
    mem'_get (mem'_map f m) bi = mem'_get m bi.
Proof.
  by elim: m => [b a|o m IH] [|bi] //=.
Qed.

Lemma get_map [A B: Type] (f: A -> B) (m: mem A) (bi o: nat):
  get (mem_map f m) bi o = get m bi o.
Proof.
  case: m => [a|m] //=.
  by rewrite mem'_get_map.
Qed.

Section TailAlgebra.

  Context {A: AllocSlot.type}.

  Lemma rshift_id: rshift ($0: A) = Some $0.
  Proof.
    by rewrite -{1}runshift_id rshift_runshift.
  Qed.

  Lemma runshift_inj: forall a b: A, runshift a = runshift b -> a = b.
  Proof.
    move=> a b E.
    have := rshift_runshift a.
    rewrite E rshift_runshift.
    by case.
  Qed.

  Lemma shift_op: forall a a' t s: A,
      rshift a = Some a' -> a' $+ t = Some s
      -> a $+ runshift t = Some (runshift s).
  Proof.
    move=> a a' t s Ra Es.
    have H := rshift_sum a (runshift t).
    rewrite Ra rshift_runshift /= Es in H.
    case E: (a $+ runshift t) H => [u|] //= H.
    by rewrite (rshift_inj _ _ _ H (rshift_runshift s)).
  Qed.

  Lemma runshift_op: forall a b c: A,
      a $+ b = Some c -> runshift a $+ runshift b = Some (runshift c).
  Proof.
    move=> a b c E.
    exact: (shift_op _ _ _ _ (rshift_runshift a) E).
  Qed.

  Fixpoint to_tail' (m: mem' A): A :=
    match m with
    | M'Tail _ a => a
    | M'Cons _ m => runshift (to_tail' m)
    end.

  Definition to_tail (m: mem A): A :=
    match m with
    | MEmpty a => a
    | MLive m => runshift (to_tail' m)
    end.

  Fixpoint mem'_push_a (a: A) (m: mem' A): option (mem' A) :=
    match m with
    | M'Tail b t =>
        match rshift a with
        | Some a' =>
            match a' $+ t with
            | Some s => Some (M'Tail b s)
            | None => None
            end
        | None => None
        end
    | M'Cons o m =>
        match rshift a with
        | Some a' =>
            match mem'_push_a a' m with
            | Some m' => Some (M'Cons o m')
            | None => None
            end
        | None => None
        end
    end.



  Lemma mem'_push_a_id: forall m: mem' A, mem'_push_a $0 m = Some m.
  Proof.
    elim=> [b t|o m IH] /=; rewrite rshift_id.
    - by rewrite op_id_l.
    - by rewrite IH.
  Qed.

  Lemma mem'_push_a_twice: forall (m: mem' A) (a b: A),
      bind (mem'_push_a a) (mem'_push_a b m)
      = bind (mem'_push_a ^~ m) (a $+ b).
  Proof.
    elim=> [bt t|o m IH] a b;
      have H := rshift_sum a b;
      move: H; rewrite /=;
      case Ra: (rshift a) => [a'|]; case Rb: (rshift b) => [b'|] /= => H.
    - have HA := op_assc a' b' t; rewrite /Basics.flip in HA.
      case Ebt: (b' $+ t) HA => [s|] /= HA;
        case Eab: (a $+ b) H => [c|] /= H.
      + rewrite /= Ra H.
        case Ed: (a' $+ b') HA => [d|] /= HA.
        * by rewrite HA.
        * by rewrite -HA.
      + rewrite -H /= in HA.
        by rewrite /= Ra -HA.
      + rewrite /= H.
        case Ed: (a' $+ b') HA => [d|] /= HA //.
        by rewrite HA.
      + by [].
    - case Eab: (a $+ b) H => [c|] /= H //=.
      by rewrite H.
    - case Ebt: (b' $+ t) => [s|] //=; rewrite ?Ra //=;
        case Eab: (a $+ b) H => [c|] /= H //=;
        by rewrite H.
    - case Eab: (a $+ b) H => [c|] /= H //=.
      by rewrite H.
    - have HI := IH a' b'.
      case Ebm: (mem'_push_a b' m) HI => [m1|] /= HI;
        case Eab: (a $+ b) H => [c|] /= H.
      + rewrite /= Ra H.
        case Ed: (a' $+ b') HI => [d|] /= HI.
        * by rewrite HI.
        * by rewrite HI.
      + rewrite -H /= in HI.
        by rewrite /= Ra HI.
      + rewrite /= H.
        case Ed: (a' $+ b') HI => [d|] /= HI //.
        by rewrite -HI.
      + by [].
    - case Eab: (a $+ b) H => [c|] /= H //=.
      by rewrite H.
    - case Ebm: (mem'_push_a b' m) => [m1|] //=; rewrite ?Ra //=;
        case Eab: (a $+ b) H => [c|] /= H //=;
        by rewrite H.
    - case Eab: (a $+ b) H => [c|] /= H //=.
      by rewrite H.
  Qed.

  Lemma mem'_push_a_swap: forall (m: mem' A) (a b: A),
      bind (mem'_push_a a) (mem'_push_a b m) = bind (mem'_push_a b) (mem'_push_a a m).
  Proof.
    move=> m a b.
    by rewrite !mem'_push_a_twice (op_comm a b).
  Qed.

  Lemma mem'_push_a_inj: forall (x1 x2: mem' A) (a: A) (m: mem' A),
      mem'_push_a a x1 = Some m -> mem'_push_a a x2 = Some m -> x1 = x2.
  Proof.
    elim=> [b1 t1|o1 m1 IH]; case=> [b2 t2|o2 m2] a m /=;
      case Ra: (rshift a) => [a'|] //.
    - case E1: (a' $+ t1) => [s1|] //; case E2: (a' $+ t2) => [s2|] //.
      move=> [<-] [Eb Es].
      rewrite Eb; rewrite Es in E2.
      by rewrite (op_cancel_l _ _ _ _ E1 E2).
    - case: (a' $+ t1) => [s1|] //; case: (mem'_push_a a' m2) => [t|] //.
      by move=> E1' E2'; congruence.
    - case: (mem'_push_a a' m1) => [t|] //; case: (a' $+ t2) => [s2|] //.
      by move=> E1' E2'; congruence.
    - case E1: (mem'_push_a a' m1) => [t1|] //; case E2: (mem'_push_a a' m2) => [t2|] //.
      move=> [<-] [Eo Et].
      rewrite Eo; rewrite Et in E2.
      by rewrite (IH _ _ _ E1 E2).
  Qed.

  Lemma mem'_push_a_inj_a: forall (x: mem' A) (a a': A) (m: mem' A),
      mem'_push_a a x = Some m -> mem'_push_a a' x = Some m -> a = a'.
  Proof.
    elim=> [b t|o xm IH] a a' m /=;
      case Ra: (rshift a) => [a1|] //; case Ra': (rshift a') => [a1'|] //.
    - case E1: (a1 $+ t) => [s1|] //; case E2: (a1' $+ t) => [s2|] //.
      move=> [<-] [Es].
      rewrite Es in E2.
      rewrite (op_cancel_r _ _ _ _ E1 E2) in Ra.
      exact: (rshift_inj _ _ _ Ra Ra').
    - case E1: (mem'_push_a a1 xm) => [t1|] //; case E2: (mem'_push_a a1' xm) => [t2|] //.
      move=> [<-] [Et].
      rewrite Et in E2.
      rewrite (IH _ _ _ E1 E2) in Ra.
      exact: (rshift_inj _ _ _ Ra Ra').
  Qed.

  Lemma mem'_push_a_get: forall (m: mem' A) (a: A) (m': mem' A),
      mem'_push_a a m = Some m' -> forall bi, mem'_get m' bi = mem'_get m bi.
  Proof.
    elim=> [b t|o m IH] a m' /=; case Ra: (rshift a) => [a'|] //.
    - by case: (a' $+ t) => [s|] // [<-].
    - case E: (mem'_push_a a' m) => [t|] // [<-].
      case=> [|bi] //=.
      exact: (IH _ _ E bi).
  Qed.

  Lemma mem'_push_a_to_tail: forall (m: mem' A) (a: A) (m': mem' A),
      mem'_push_a a m = Some m'
      -> a $+ runshift (to_tail' m) = Some (runshift (to_tail' m')).
  Proof.
    elim=> [b t|o m IH] a m' /=; case Ra: (rshift a) => [a'|] //.
    - case Es: (a' $+ t) => [s|] // [<-] /=.
      exact: (shift_op _ _ _ _ Ra Es).
    - case E: (mem'_push_a a' m) => [t|] // [<-] /=.
      exact: (shift_op _ _ _ _ Ra (IH _ _ E)).
  Qed.

  Lemma mem'_push_a_total (RT: forall a: A, exists a', rshift a = Some a')
    (OT: forall a b: A, exists c, a $+ b = Some c):
    forall (m: mem' A) (a: A), exists m', mem'_push_a a m = Some m'.
  Proof.
    elim=> [b t|o m IH] a /=.
    - case: (RT a) => [a' ->].
      case: (OT a' t) => [s ->].
      by eexists.
    - case: (RT a) => [a' ->].
      case: (IH a') => [m' ->].
      by eexists.
  Qed.

  Lemma op_swapA (x y z: A): bind (op x) (y $+ z) = bind (op y) (x $+ z).
  Proof.
    have H1 := op_assc x y z; have H2 := op_assc y x z.
    rewrite /Basics.flip in H1 H2.
    by rewrite -H1 -H2 (op_comm x y).
  Qed.

  Fixpoint mem'_sum (x y: mem' A): option (mem' A) :=
    match x, y with
    | M'Tail b1 a1, M'Tail b2 a2 =>
        match block_sum b1 b2, a1 $+ a2 with
        | Some b, Some a => Some (M'Tail b a)
        | None, _ | _, None => None
        end
    | M'Cons b1 x, M'Cons b2 y =>
        match mem'_sum x y with
        | Some m =>
            match b1, b2 with
            | o, None | None, o => Some (M'Cons o m)
            | Some b1, Some b2 =>
                match block_sum b1 b2 with
                | Some b => Some (M'Cons (Some b) m)
                | None => None
                end
            end
        | None => None
        end
    | M'Tail b a, M'Cons o y
    | M'Cons o y, M'Tail b a
      =>
        let b :=
          match o with
          | Some b2 => block_sum b b2
          | None => Some b
          end
        in
        match b with
        | Some b =>
            match mem'_push_a a y with
            | Some m => Some (M'Cons (Some b) m)
            | None => None
            end
        | None => None
        end
    end.

  Lemma mem'_sum_tail_tail: forall (b1: block) (a1: A) (b2: block) (a2: A),
      mem'_sum (M'Tail b1 a1) (M'Tail b2 a2)
      = bind (fun b => bind (fun a => Some (M'Tail b a)) (a1 $+ a2))
          (block_sum b1 b2).
  Proof.
    move=> b1 a1 b2 a2 /=.
    by case: (block_sum b1 b2) => [b|] //=; case: (a1 $+ a2) => [a|].
  Qed.
  Lemma mem'_sum_cons_cons: forall (o1 o2: option block) (x y: mem' A),
      mem'_sum (M'Cons o1 x) (M'Cons o2 y)
      = bind (fun o => bind (fun m => Some (M'Cons o m)) (mem'_sum x y))
          ((osum block_sum) o1 o2).
  Proof.
    move=> [b1|] [b2|] x y //=; try by case: (mem'_sum x y).
    by case: (block_sum b1 b2) => [b|] //=; case: (mem'_sum x y).
  Qed.
  Lemma mem'_sum_tail_cons: forall (b: block) (a: A) (o: option block) (y: mem' A),
      mem'_sum (M'Tail b a) (M'Cons o y)
      = bind (fun o' => bind (fun m => Some (M'Cons o' m)) (mem'_push_a a y))
          ((osum block_sum) (Some b) o).
  Proof.
    move=> b a [c|] y //=.
    by case: (block_sum b c).
  Qed.
  Lemma mem'_sum_cons_tail: forall (o: option block) (x: mem' A) (b: block) (a: A),
      mem'_sum (M'Cons o x) (M'Tail b a)
      = bind (fun o' => bind (fun m => Some (M'Cons o' m)) (mem'_push_a a x))
          ((osum block_sum) (Some b) o).
  Proof.
    move=> [c|] x b a //=.
    by case: (block_sum b c).
  Qed.

  Lemma mem'_sum_comm: forall x y: mem' A, mem'_sum x y = mem'_sum y x.
  Proof.
    elim=> [b1 a1|o1 xm IH]; case=> [b2 a2|o2 ym] //=.
    - rewrite block_sum_comm (op_comm a1 a2).
      by case: (block_sum b2 b1) => [b|] //=.
    - rewrite IH; case: (mem'_sum ym xm) => [m|] //=.
      case: o1 => [b1|]; case: o2 => [b2|] //=.
      by rewrite block_sum_comm.
  Qed.

  Lemma mem'_sum_push_a: forall (x y: mem' A) (a: A),
      bind (mem'_sum x) (mem'_push_a a y) = bind (mem'_push_a a) (mem'_sum x y).
  Proof.
    elim=> [bx ax|ox xm IH]; case=> [bb ay|oy ym] a /=;
      case Ra: (rshift a) => [a'|] /=.
    - have HS := op_swapA ax a' ay.
      case Es: (a' $+ ay) HS => [s|] /= HS;
        case Ea: (ax $+ ay) HS => [c|] /= HS;
        case Eb: (block_sum bx bb) => [b|] //=.
      + by rewrite /= Ra HS.
      + by rewrite /= HS.
      + by rewrite /= Ra -HS.
    - case Eb: (block_sum bx bb) => [b|] //=;
        case Ea: (ax $+ ay) => [c|] //=.
      by rewrite /= Ra.
    - have HP := mem'_push_a_swap ym ax a'.
      case Epy: (mem'_push_a a' ym) HP => [t|] /= HP;
        case Epx: (mem'_push_a ax ym) HP => [u|] /= HP.
      + case: oy => [c|] /=; [case Eb: (block_sum bx c) => [b|] //=|];
          by rewrite /= Ra HP.
      + case: oy => [c|] /=; [case Eb: (block_sum bx c) => [b|] //=|];
          by rewrite /= HP.
      + case: oy => [c|] /=; [case Eb: (block_sum bx c) => [b|] //=|];
          by rewrite /= Ra -HP.
      + by case: oy => [c|] /=; [case Eb: (block_sum bx c) => [b|] //=|].
    - case: oy => [c|] /=; [case Eb: (block_sum bx c) => [b|] //=|];
        case Epx: (mem'_push_a ax ym) => [u|] //=;
        by rewrite /= Ra.
    - have HT := mem'_push_a_twice xm a' ay.
      case Es: (a' $+ ay) HT => [s|] /= HT;
        case Epx: (mem'_push_a ay xm) HT => [u|] /= HT.
      + case: ox => [c|] /=; [case Eb: (block_sum bb c) => [b|] //=|];
          by rewrite /= Ra HT.
      + case: ox => [c|] /=; [case Eb: (block_sum bb c) => [b|] //=|];
          by rewrite /= -HT.
      + case: ox => [c|] /=; [case Eb: (block_sum bb c) => [b|] //=|];
          by rewrite /= Ra HT.
      + by case: ox => [c|] /=; [case Eb: (block_sum bb c) => [b|] //=|].
    - case: ox => [c|] /=; [case Eb: (block_sum bb c) => [b|] //=|];
        case Epx: (mem'_push_a ay xm) => [u|] //=;
        by rewrite /= Ra.
    - have HI := IH ym a'.
      case Epy: (mem'_push_a a' ym) HI => [t|] /= HI;
        case Eg: (mem'_sum xm ym) HI => [w|] /= HI.
      + case: ox => [b1|]; case: oy => [b2|] /=;
          try (case Eb: (block_sum b1 b2) => [b|] /=;
               [|by rewrite HI; case: (mem'_push_a a' w)]);
          by rewrite /= HI Ra.
      + by rewrite /= HI.
      + case: ox => [b1|]; case: oy => [b2|] /=;
          try (case Eb: (block_sum b1 b2) => [b|] //=);
          by rewrite /= Ra -HI.
      + by [].
    - case Eg: (mem'_sum xm ym) => [w|] //=;
        case: ox => [b1|]; case: oy => [b2|] /=;
        try (case Eb: (block_sum b1 b2) => [b|] //=);
        by rewrite /= Ra.
  Qed.

  Lemma mem'_sum_push_a_l: forall (x y: mem' A) (a: A),
      bind (mem'_sum ^~ y) (mem'_push_a a x) = bind (mem'_push_a a) (mem'_sum x y).
  Proof.
    move=> x y a.
    move: (mem'_sum_push_a y x a).
    rewrite (mem'_sum_comm y x).
    case: (mem'_push_a a x) => [t|] //=.
    by rewrite (mem'_sum_comm y t).
  Qed.

  Lemma mem'_sum_assc: forall x y z: mem' A,
      bind (Basics.flip mem'_sum z) (mem'_sum x y)
      = bind (mem'_sum x) (mem'_sum y z).
  Proof.
    elim=> [b1 a1|o1 xm IH]; case=> [b2 a2|o2 ym]; case=> [b3 a3|o3 zm].
    {
    have HB := block_sum_assc b1 b2 b3; rewrite /Basics.flip in HB.
    have HA := op_assc a1 a2 a3; rewrite /Basics.flip in HA.
    rewrite /Basics.flip /=.
    case B12: (block_sum b1 b2) HB => [b12|] /= HB;
      case B23: (block_sum b2 b3) HB => [b23|] /= HB.
    - case A12: (a1 $+ a2) HA => [a12|] /= HA;
        case A23: (a2 $+ a3) HA => [a23|] /= HA.
      + by rewrite /= HB HA.
      + rewrite /= HA.
        by case: (block_sum b12 b3).
      + rewrite /= -HA.
        by case: (block_sum b1 b23).
      + by [].
    - case A12: (a1 $+ a2) HA => [a12|] /= HA.
      + by rewrite /= HB.
      + by [].
    - case A23: (a2 $+ a3) HA => [a23|] /= HA.
      + by rewrite /= -HB.
      + by [].
    - by [].
    }
    {
    rewrite mem'_sum_tail_tail mem'_sum_tail_cons.
    case H23: ((osum block_sum) (Some b2) o3) => [h23|]; last first.
    - case B12: (block_sum b1 b2) => [b12|]; last by [].
      case A12: (a1 $+ a2) => [a12|]; last by [].
      rewrite !bind_some /Basics.flip mem'_sum_tail_cons.
      move: (osum_block_assc (Some b1) (Some b2) o3).
      rewrite H23 osum_block_ss B12 !bind_some !bind_none /Basics.flip => Hb.
      by rewrite Hb.
    - case F2: (mem'_push_a a2 zm) => [s|]; last first.
      + case B12: (block_sum b1 b2) => [b12|]; last by [].
        case A12: (a1 $+ a2) => [a12|]; last by [].
        rewrite !bind_some /Basics.flip mem'_sum_tail_cons.
        move: (mem'_push_a_twice zm a1 a2); rewrite F2 A12 !bind_none bind_some => Hp.
        by rewrite -Hp; case: ((osum block_sum) (Some b12) o3) => [u|].
      + case B12: (block_sum b1 b2) => [b12|]; last first.
        * rewrite !bind_some mem'_sum_tail_cons.
          move: (osum_block_assc (Some b1) (Some b2) o3).
          rewrite H23 osum_block_ss B12 !bind_none bind_some => Hb.
          by rewrite -Hb.
        * case A12: (a1 $+ a2) => [a12|]; last first.
          -- rewrite !bind_some mem'_sum_tail_cons.
             move: (mem'_push_a_twice zm a1 a2); rewrite F2 A12 !bind_some bind_none => Hp.
             by rewrite Hp; case: ((osum block_sum) (Some b1) h23) => [u|].
          -- rewrite !bind_some /Basics.flip !mem'_sum_tail_cons.
             move: (osum_block_assc (Some b1) (Some b2) o3).
             rewrite H23 osum_block_ss B12 !bind_some /Basics.flip => Hb.
             move: (mem'_push_a_twice zm a1 a2); rewrite F2 A12 !bind_some => Hp.
             by rewrite Hb Hp.
    }
    {
    rewrite mem'_sum_tail_cons mem'_sum_cons_tail.
    case H12: ((osum block_sum) (Some b1) o2) => [h12|]; last first.
    - case H32: ((osum block_sum) (Some b3) o2) => [h32|]; last by [].
      case F3: (mem'_push_a a3 ym) => [t3|]; last by [].
      rewrite !bind_some mem'_sum_tail_cons.
      move: (osum_block_swap (Some b3) (Some b1) o2).
      rewrite H12 H32 !bind_none bind_some => Hb.
      by rewrite -Hb.
    - case F1: (mem'_push_a a1 ym) => [t1|]; last first.
      + case H32: ((osum block_sum) (Some b3) o2) => [h32|]; last by [].
        case F3: (mem'_push_a a3 ym) => [t3|]; last by [].
        rewrite !bind_some mem'_sum_tail_cons.
        move: (mem'_push_a_swap ym a3 a1); rewrite F1 F3 !bind_none bind_some => Hp.
        by rewrite -Hp; case: ((osum block_sum) (Some b1) h32) => [u|].
      + rewrite !bind_some /Basics.flip mem'_sum_cons_tail.
        case H32: ((osum block_sum) (Some b3) o2) => [h32|]; last first.
        * move: (osum_block_swap (Some b3) (Some b1) o2).
          rewrite H12 H32 !bind_some bind_none => Hb.
          by rewrite Hb.
        * case F3: (mem'_push_a a3 ym) => [t3|]; last first.
          -- move: (mem'_push_a_swap ym a3 a1); rewrite F1 F3 !bind_some bind_none => Hp.
             by rewrite Hp; case: ((osum block_sum) (Some b3) h12) => [u|].
          -- rewrite !bind_some mem'_sum_tail_cons.
             move: (osum_block_swap (Some b3) (Some b1) o2); rewrite H12 H32 !bind_some => Hb.
             move: (mem'_push_a_swap ym a3 a1); rewrite F1 F3 !bind_some => Hp.
             by rewrite Hb Hp.
    }
    {
    rewrite mem'_sum_tail_cons mem'_sum_cons_cons.
    case H12: ((osum block_sum) (Some b1) o2) => [h12|]; last first.
    - case H23: ((osum block_sum) o2 o3) => [h23|]; last by [].
      case G2: (mem'_sum ym zm) => [w|]; last by [].
      rewrite !bind_some mem'_sum_tail_cons.
      move: (osum_block_assc (Some b1) o2 o3); rewrite H12 H23 !bind_none bind_some => Hb.
      by rewrite -Hb.
    - case F1: (mem'_push_a a1 ym) => [t|]; last first.
      + case H23: ((osum block_sum) o2 o3) => [h23|]; last by [].
        case G2: (mem'_sum ym zm) => [w|]; last by [].
        rewrite !bind_some mem'_sum_tail_cons.
        move: (mem'_sum_push_a_l ym zm a1); rewrite F1 G2 !bind_none bind_some => Hp.
        by rewrite -Hp; case: ((osum block_sum) (Some b1) h23) => [u|].
      + rewrite !bind_some /Basics.flip mem'_sum_cons_cons.
        move: (mem'_sum_push_a_l ym zm a1); rewrite F1 bind_some => Hp.
        case H23: ((osum block_sum) o2 o3) => [h23|]; last first.
        * move: (osum_block_assc (Some b1) o2 o3).
          rewrite H12 H23 !bind_some bind_none /Basics.flip => Hb.
          by rewrite Hb.
        * case G2: (mem'_sum ym zm) => [w|]; last first.
          -- move: Hp; rewrite G2 bind_none => Hp.
             by rewrite Hp; case: ((osum block_sum) h12 o3) => [u|].
          -- rewrite !bind_some mem'_sum_tail_cons.
             move: (osum_block_assc (Some b1) o2 o3).
             rewrite H12 H23 !bind_some /Basics.flip => Hb.
             move: Hp; rewrite G2 bind_some => Hp.
             by rewrite Hb Hp.
    }
    {
    rewrite mem'_sum_cons_tail mem'_sum_tail_tail.
    case H21: ((osum block_sum) (Some b2) o1) => [h21|]; last first.
    - case B23: (block_sum b2 b3) => [b23|]; last by [].
      case A23: (a2 $+ a3) => [a23|]; last by [].
      rewrite !bind_some mem'_sum_cons_tail.
      move: (osum_block_assc (Some b3) (Some b2) o1).
      rewrite osum_block_ss (block_sum_comm b3 b2) B23 H21 !bind_some !bind_none /Basics.flip => Hb.
      by rewrite Hb.
    - case F2: (mem'_push_a a2 xm) => [t|]; last first.
      + case B23: (block_sum b2 b3) => [b23|]; last by [].
        case A23: (a2 $+ a3) => [a23|]; last by [].
        rewrite !bind_some mem'_sum_cons_tail.
        move: (mem'_push_a_twice xm a3 a2).
        rewrite (op_comm a3 a2) F2 A23 !bind_none bind_some => Hp.
        by rewrite -Hp; case: ((osum block_sum) (Some b23) o1) => [u|].
      + rewrite !bind_some /Basics.flip mem'_sum_cons_tail.
        case B23: (block_sum b2 b3) => [b23|]; last first.
        * move: (osum_block_assc (Some b3) (Some b2) o1).
          rewrite osum_block_ss (block_sum_comm b3 b2) B23 H21 !bind_none bind_some => Hb.
          by rewrite -Hb.
        * case A23: (a2 $+ a3) => [a23|]; last first.
          -- move: (mem'_push_a_twice xm a3 a2).
             rewrite (op_comm a3 a2) F2 A23 !bind_some bind_none => Hp.
             by rewrite Hp; case: ((osum block_sum) (Some b3) h21) => [u|].
          -- rewrite !bind_some mem'_sum_cons_tail.
             move: (osum_block_assc (Some b3) (Some b2) o1).
             rewrite osum_block_ss (block_sum_comm b3 b2) B23 H21 !bind_some /Basics.flip => Hb.
             move: (mem'_push_a_twice xm a3 a2).
             rewrite (op_comm a3 a2) F2 A23 !bind_some => Hp.
             by rewrite -Hb Hp.
    }
    {
    rewrite mem'_sum_cons_tail mem'_sum_tail_cons.
    case H21: ((osum block_sum) (Some b2) o1) => [h21|]; last first.
    - case H23: ((osum block_sum) (Some b2) o3) => [h23|]; last by [].
      case F2z: (mem'_push_a a2 zm) => [s|]; last by [].
      rewrite !bind_some mem'_sum_cons_cons.
      move: (osum_block_assc o1 (Some b2) o3).
      rewrite (osum_block_comm o1 (Some b2)) H21 H23 !bind_none bind_some => Hb.
      by rewrite -Hb.
    - case F2x: (mem'_push_a a2 xm) => [t|]; last first.
      + case H23: ((osum block_sum) (Some b2) o3) => [h23|]; last by [].
        case F2z: (mem'_push_a a2 zm) => [s|]; last by [].
        rewrite !bind_some mem'_sum_cons_cons.
        move: (mem'_sum_push_a xm zm a2); rewrite F2z bind_some => Hp2.
        move: (mem'_sum_push_a_l xm zm a2); rewrite F2x !bind_none => Hp1.
        by rewrite Hp2 -Hp1; case: ((osum block_sum) o1 h23) => [u|].
      + rewrite !bind_some /Basics.flip mem'_sum_cons_cons.
        move: (mem'_sum_push_a_l xm zm a2); rewrite F2x bind_some => Hp1.
        case H23: ((osum block_sum) (Some b2) o3) => [h23|]; last first.
        * move: (osum_block_assc o1 (Some b2) o3).
          rewrite (osum_block_comm o1 (Some b2)) H21 H23 !bind_some bind_none /Basics.flip => Hb.
          by rewrite Hb.
        * case F2z: (mem'_push_a a2 zm) => [s|]; last first.
          -- move: (mem'_sum_push_a xm zm a2); rewrite F2z !bind_none => Hp2.
             by rewrite Hp1 -Hp2; case: ((osum block_sum) h21 o3) => [u|].
          -- rewrite !bind_some mem'_sum_cons_cons.
             move: (osum_block_assc o1 (Some b2) o3).
             rewrite (osum_block_comm o1 (Some b2)) H21 H23 !bind_some /Basics.flip => Hb.
             move: (mem'_sum_push_a xm zm a2); rewrite F2z bind_some => Hp2.
             by rewrite Hb Hp1 Hp2.
    }
    {
    rewrite mem'_sum_cons_cons mem'_sum_cons_tail.
    case H12: ((osum block_sum) o1 o2) => [h12|]; last first.
    - case H32: ((osum block_sum) (Some b3) o2) => [h32|]; last by [].
      case F3: (mem'_push_a a3 ym) => [t3|]; last by [].
      rewrite !bind_some mem'_sum_cons_cons.
      move: (osum_block_swap (Some b3) o1 o2); rewrite H12 H32 !bind_none bind_some => Hb.
      by rewrite -Hb.
    - case G1: (mem'_sum xm ym) => [m|]; last first.
      + case H32: ((osum block_sum) (Some b3) o2) => [h32|]; last by [].
        case F3: (mem'_push_a a3 ym) => [t3|]; last by [].
        rewrite !bind_some mem'_sum_cons_cons.
        move: (mem'_sum_push_a xm ym a3); rewrite F3 G1 bind_some bind_none => Hp.
        by rewrite Hp; case: ((osum block_sum) o1 h32) => [u|].
      + rewrite !bind_some /Basics.flip mem'_sum_cons_tail.
        case H32: ((osum block_sum) (Some b3) o2) => [h32|]; last first.
        * move: (osum_block_swap (Some b3) o1 o2); rewrite H12 H32 !bind_some bind_none => Hb.
          by rewrite Hb.
        * case F3: (mem'_push_a a3 ym) => [t3|]; last first.
          -- move: (mem'_sum_push_a xm ym a3); rewrite F3 G1 !bind_none bind_some => Hp.
             by rewrite -Hp; case: ((osum block_sum) (Some b3) h12) => [u|].
          -- rewrite !bind_some mem'_sum_cons_cons.
             move: (osum_block_swap (Some b3) o1 o2); rewrite H12 H32 !bind_some => Hb.
             move: (mem'_sum_push_a xm ym a3); rewrite F3 G1 !bind_some => Hp.
             by rewrite Hb Hp.
    }
    {
    rewrite !mem'_sum_cons_cons.
    case H12: ((osum block_sum) o1 o2) => [h12|]; last first.
    - case H23: ((osum block_sum) o2 o3) => [h23|]; last by [].
      case G2: (mem'_sum ym zm) => [w|]; last by [].
      rewrite !bind_some mem'_sum_cons_cons.
      move: (osum_block_assc o1 o2 o3); rewrite H12 H23 !bind_none bind_some => Hb.
      by rewrite -Hb.
    - case G1: (mem'_sum xm ym) => [m|]; last first.
      + case H23: ((osum block_sum) o2 o3) => [h23|]; last by [].
        case G2: (mem'_sum ym zm) => [w|]; last by [].
        rewrite !bind_some mem'_sum_cons_cons.
        move: (IH ym zm); rewrite G1 G2 !bind_none bind_some => Hp.
        by rewrite -Hp; case: ((osum block_sum) o1 h23) => [u|].
      + rewrite !bind_some /Basics.flip mem'_sum_cons_cons.
        move: (IH ym zm); rewrite G1 bind_some /Basics.flip => Hp.
        case H23: ((osum block_sum) o2 o3) => [h23|]; last first.
        * move: (osum_block_assc o1 o2 o3); rewrite H12 H23 !bind_some bind_none /Basics.flip => Hb.
          by rewrite Hb.
        * case G2: (mem'_sum ym zm) => [w|]; last first.
          -- move: Hp; rewrite G2 bind_none => Hp.
             by rewrite Hp; case: ((osum block_sum) h12 o3) => [u|].
          -- rewrite !bind_some mem'_sum_cons_cons.
             move: (osum_block_assc o1 o2 o3); rewrite H12 H23 !bind_some /Basics.flip => Hb.
             move: Hp; rewrite G2 bind_some => Hp.
             by rewrite Hb Hp.
    }
  Qed.

  Lemma mem'_push_a_not_sum: forall (x: mem' A) (a: A) (z m: mem' A),
      mem'_push_a a x = Some m -> mem'_sum x z = Some m -> False.
  Proof.
    elim=> [bx ax|ox xm IH] a z m /=; case Ra: (rshift a) => [a'|] //.
    - case Es: (a' $+ ax) => [s|] // [<-].
      case: z => [bz az|oz zm] /=.
      + case E: (block_sum bx bz) => [b|] //.
        case A2: (ax $+ az) => [aa|] // [Eb Ea].
        rewrite Eb in E.
        exact: (block_sum_ne_l bx bz E).
      + case: oz => [c|] /=;
          [case E: (block_sum bx c) => [b|] //|];
          by case: (mem'_push_a ax zm) => [t|].
    - case Ep: (mem'_push_a a' xm) => [t|] // [<-].
      case: z => [bz az|oz zm] /=.
      + case: ox Ep => [c|] Ep /=.
        * case E: (block_sum bz c) => [b|] //.
          case F: (mem'_push_a az xm) => [u|] // [Eb Eu].
          rewrite Eb block_sum_comm in E.
          exact: (block_sum_ne_l c bz E).
        * by case: (mem'_push_a az xm) => [u|].
      + case G: (mem'_sum xm zm) => [u|] //.
        case: ox Ep => [c|] Ep; case: oz => [e|] //=.
        * case E: (block_sum c e) => [b|] // [Eb Eu].
          rewrite Eb in E.
          exact: (block_sum_ne_l c e E).
        * move=> [Eu]; rewrite Eu in G.
          exact: (IH _ _ _ Ep G).
        * move=> [Eu]; rewrite Eu in G.
          exact: (IH _ _ _ Ep G).
  Qed.


  Lemma mem'_sum_cancel_l: forall x y z w: mem' A,
      mem'_sum x y = Some w -> mem'_sum x z = Some w -> y = z.
  Proof.
    elim=> [bx ax|ox xm IH] y z w; case: y => [b2 a2|o2 ym]; case: z => [b3 a3|o3 zm].
    - rewrite !mem'_sum_tail_tail.
      case E2: (block_sum bx b2) => [c2|]; case A2: (ax $+ a2) => [d2|];
      case E3: (block_sum bx b3) => [c3|]; case A3: (ax $+ a3) => [d3|] //=.
      move=> [<-] [Ec Ed]; rewrite Ec in E3; rewrite Ed in A3.
      by rewrite (block_sum_cancel_l _ _ _ _ E2 E3) (op_cancel_l _ _ _ _ A2 A3).
    - rewrite mem'_sum_tail_tail mem'_sum_tail_cons.
      case E2: (block_sum bx b2) => [c2|]; case A2: (ax $+ a2) => [d2|];
      case H3: ((osum block_sum) (Some bx) o3) => [h3|]; case F3: (mem'_push_a ax zm) => [t3|] //=.
      by move=> [<-].
    - rewrite mem'_sum_tail_cons mem'_sum_tail_tail.
      case H2: ((osum block_sum) (Some bx) o2) => [h2|]; case F2: (mem'_push_a ax ym) => [t2|];
      case E3: (block_sum bx b3) => [c3|]; case A3: (ax $+ a3) => [d3|] //=.
      by move=> [<-].
    - rewrite !mem'_sum_tail_cons.
      case H2: ((osum block_sum) (Some bx) o2) => [h2|]; case F2: (mem'_push_a ax ym) => [t2|];
      case H3: ((osum block_sum) (Some bx) o3) => [h3|]; case F3: (mem'_push_a ax zm) => [t3|] //=.
      move=> [<-] [Eo Em]; rewrite Eo in H3; rewrite Em in F3.
      by rewrite (osum_block_cancel_l _ _ _ _ H2 H3) (mem'_push_a_inj _ _ _ _ F2 F3).
    - rewrite !mem'_sum_cons_tail.
      case H2: ((osum block_sum) (Some b2) ox) => [h2|]; case F2: (mem'_push_a a2 xm) => [t2|];
      case H3: ((osum block_sum) (Some b3) ox) => [h3|]; case F3: (mem'_push_a a3 xm) => [t3|] //=.
      move=> [<-] [Eo Em]; rewrite Eo in H3; rewrite Em in F3.
      move: (osum_block_cancel_r _ _ _ _ H2 H3) => [Eb].
      by rewrite Eb (mem'_push_a_inj_a _ _ _ _ F2 F3).
    - rewrite mem'_sum_cons_tail mem'_sum_cons_cons.
      case H2: ((osum block_sum) (Some b2) ox) => [h2|]; case F2: (mem'_push_a a2 xm) => [t2|];
      case H3: ((osum block_sum) ox o3) => [h3|]; case G3: (mem'_sum xm zm) => [m3|] //=.
      move=> [<-] [Eo Em]; rewrite Em in G3.
      by case: (mem'_push_a_not_sum _ _ _ _ F2 G3).
    - rewrite mem'_sum_cons_cons mem'_sum_cons_tail.
      case H2: ((osum block_sum) ox o2) => [h2|]; case G2: (mem'_sum xm ym) => [m2|];
      case H3: ((osum block_sum) (Some b3) ox) => [h3|]; case F3: (mem'_push_a a3 xm) => [t3|] //=.
      move=> [<-] [Eo Em]; rewrite Em in F3.
      by case: (mem'_push_a_not_sum _ _ _ _ F3 G2).
    - rewrite !mem'_sum_cons_cons.
      case H2: ((osum block_sum) ox o2) => [h2|]; case G2: (mem'_sum xm ym) => [m2|];
      case H3: ((osum block_sum) ox o3) => [h3|]; case G3: (mem'_sum xm zm) => [m3|] //=.
      move=> [<-] [Eo Em]; rewrite Eo in H3; rewrite Em in G3.
      by rewrite (osum_block_cancel_l _ _ _ _ H2 H3) (IH _ _ _ G2 G3).
  Qed.

  Lemma mem'_sum_cancel_r: forall x y z w: mem' A,
      mem'_sum y x = Some w -> mem'_sum z x = Some w -> y = z.
  Proof.
    move=> x y z w E1 E2.
    rewrite mem'_sum_comm in E1; rewrite mem'_sum_comm in E2.
    exact: (mem'_sum_cancel_l x y z w E1 E2).
  Qed.

  Definition mem_sum (x y: mem A): option (mem A) :=
    match x, y with
    | MEmpty a1, MEmpty a2 =>
        match a1 $+ a2 with
        | Some a => Some (MEmpty a)
        | None => None
        end
    | MEmpty a, MLive m
    | MLive m, MEmpty a
      =>
        match mem'_push_a a m with
        | Some m => Some (MLive m)
        | None => None
        end
    | MLive m1, MLive m2 =>
        match mem'_sum m1 m2 with
        | Some m => Some (MLive m)
        | None => None
        end
    end.

  Lemma mem_sum_comm: forall x y: mem A, mem_sum x y = mem_sum y x.
  Proof.
    case=> [a1|m1]; case=> [a2|m2] //=.
    - by rewrite (op_comm a1 a2).
    - by rewrite mem'_sum_comm.
  Qed.

  Lemma mem_sum_id_l: forall x: mem A, mem_sum (MEmpty $0) x = Some x.
  Proof.
    case=> [a|m] /=.
    - by rewrite op_id_l.
    - by rewrite mem'_push_a_id.
  Qed.

  Lemma mem_sum_id_r: forall x: mem A, mem_sum x (MEmpty $0) = Some x.
  Proof.
    case=> [a|m] /=.
    - by rewrite op_id_r.
    - by rewrite mem'_push_a_id.
  Qed.


  Lemma mem_sum_assc: forall x y z: mem A,
      bind (Basics.flip mem_sum z) (mem_sum x y) = bind (mem_sum x) (mem_sum y z).
  Proof.
    case=> [a1|m1]; case=> [a2|m2]; case=> [a3|m3];
      rewrite /Basics.flip /=.

    {
      have HA := op_assc a1 a2 a3; rewrite /Basics.flip in HA.
      case A12: (a1 $+ a2) HA => [a12|] /= HA;
        case A23: (a2 $+ a3) HA => [a23|] /= HA.
      - by rewrite /= HA.
      - by rewrite /= HA.
      - by rewrite /= -HA.
      - by [].
    }

    {
      move: (mem'_push_a_twice m3 a1 a2).
      case EA: (a1 $+ a2) => [a12|]; case F: (mem'_push_a a2 m3) => [t|] /= => Hp;
      by [rewrite Hp | rewrite -Hp | idtac].
    }
    {
      move: (mem'_push_a_swap m2 a3 a1).
      case F1: (mem'_push_a a1 m2) => [t|]; case F3: (mem'_push_a a3 m2) => [s|] /= => Hp;
      by [rewrite Hp | rewrite -Hp | idtac].
    }
    {
      move: (mem'_sum_push_a_l m2 m3 a1).
      case F: (mem'_push_a a1 m2) => [t|]; case G: (mem'_sum m2 m3) => [w|] /= => Hp;
      by [rewrite /= Hp | rewrite -Hp | idtac].
    }
    {
      move: (mem'_push_a_twice m1 a3 a2); rewrite (op_comm a3 a2).
      case F: (mem'_push_a a2 m1) => [t|]; case EA: (a2 $+ a3) => [a23|] /= => Hp;
      by [rewrite Hp | rewrite -Hp | idtac].
    }
    {
      move: (mem'_sum_push_a_l m1 m3 a2) (mem'_sum_push_a m1 m3 a2).
      case F1: (mem'_push_a a2 m1) => [t|]; case F2: (mem'_push_a a2 m3) => [s|] /= => Hp1 Hp2;
      by [rewrite /= Hp1 Hp2 | rewrite /= Hp1 -Hp2 | rewrite /= Hp2 -Hp1 | idtac].
    }
    {
      move: (mem'_sum_push_a m1 m2 a3).
      case G: (mem'_sum m1 m2) => [t|]; case F: (mem'_push_a a3 m2) => [s|] /= => Hp;
      by [rewrite /= Hp | rewrite -Hp | idtac].
    }
    {
      move: (mem'_sum_assc m1 m2 m3); rewrite /Basics.flip.
      case G1: (mem'_sum m1 m2) => [t|] /=; case G2: (mem'_sum m2 m3) => [w|] /= => H.
      - by rewrite /= H; case: (mem'_sum m1 w) => [u|].
      - by rewrite /= H.
      - by rewrite /= -H.
      - by [].
    }
  Qed.

  Lemma mem_sum_cancel_l: forall x y z w: mem A,
      mem_sum x y = Some w -> mem_sum x z = Some w -> y = z.
  Proof.
    case=> [a1|m1]; case=> [a2|m2]; case=> [a3|m3] w //=.
    - rewrite /=.
      case A2: (a1 $+ a2) => [d2|]; case A3: (a1 $+ a3) => [d3|] //=.
      move=> [<-] [Ed]; rewrite Ed in A3.
      by rewrite (op_cancel_l _ _ _ _ A2 A3).
    - rewrite /=.
      case A2: (a1 $+ a2) => [d2|]; case F3: (mem'_push_a a1 m3) => [t3|] //=.
      by move=> [<-].
    - rewrite /=.
      case F2: (mem'_push_a a1 m2) => [t2|]; case A3: (a1 $+ a3) => [d3|] //=.
      by move=> [<-].
    - case F2: (mem'_push_a a1 m2) => [t2|]; case F3: (mem'_push_a a1 m3) => [t3|] //=.
      move=> [<-] [Et]; rewrite Et in F3.
      by rewrite (mem'_push_a_inj _ _ _ _ F2 F3).
    - case F2: (mem'_push_a a2 m1) => [t2|]; case F3: (mem'_push_a a3 m1) => [t3|] //=.
      move=> [<-] [Et]; rewrite Et in F3.
      by rewrite (mem'_push_a_inj_a _ _ _ _ F2 F3).
    - rewrite /=.
      case F2: (mem'_push_a a2 m1) => [t2|]; case G3: (mem'_sum m1 m3) => [s3|] //=.
      move=> [<-] [Et]; rewrite Et in G3.
      by case: (mem'_push_a_not_sum _ _ _ _ F2 G3).
    - rewrite /=.
      case G2: (mem'_sum m1 m2) => [t2|]; case F3: (mem'_push_a a3 m1) => [t3|] //=.
      move=> [<-] [Et]; rewrite Et in F3.
      by case: (mem'_push_a_not_sum _ _ _ _ F3 G2).
    - rewrite /=.
      case G2: (mem'_sum m1 m2) => [t2|]; case G3: (mem'_sum m1 m3) => [t3|] //=.
      move=> [<-] [Et]; rewrite Et in G3.
      by rewrite (mem'_sum_cancel_l _ _ _ _ G2 G3).
  Qed.

  Lemma mem_sum_cancel_r: forall x y z w: mem A,
      mem_sum y x = Some w -> mem_sum z x = Some w -> y = z.
  Proof.
    move=> x y z w E1 E2.
    rewrite mem_sum_comm in E1; rewrite mem_sum_comm in E2.
    exact: (mem_sum_cancel_l x y z w E1 E2).
  Qed.

End TailAlgebra.

HB.instance Definition _ (T: AllocSlot.type) :=
  hasOp.Build (mem' T) mem'_sum.
HB.instance Definition _ (T: AllocSlot.type) :=
  hasComm.Build (mem' T) mem'_sum_comm.
HB.instance Definition _ (T: AllocSlot.type) :=
  hasAssc.Build (mem' T) mem'_sum_assc.
HB.instance Definition _ (T: AllocSlot.type) :=
  hasCancel.Build (mem' T) mem'_sum_cancel_l mem'_sum_cancel_r.

HB.instance Definition _ (T: AllocSlot.type) :=
  hasOp.Build (mem T) mem_sum.
HB.instance Definition _ (T: AllocSlot.type) :=
  hasComm.Build (mem T) mem_sum_comm.
HB.instance Definition _ (T: AllocSlot.type) :=
  hasIdentity.Build (mem T) (MEmpty id_e) mem_sum_id_l mem_sum_id_r.
HB.instance Definition _ (T: AllocSlot.type) :=
  hasAssc.Build (mem T) mem_sum_assc.
HB.instance Definition _ (T: AllocSlot.type) :=
  hasCancel.Build (mem T) mem_sum_cancel_l mem_sum_cancel_r.

Section TailAlgebra.

  Context {A: AllocSlot.type}.

  Lemma mem'_sum_get (x: mem' A): forall (y m: mem' A),
      mem'_sum x y = Some m
      -> forall bi, osum block_sum (mem'_get x bi) (mem'_get y bi)
                    = Some (mem'_get m bi).
  Proof.
    elim: x => [bx ax|ox xm IH]; case=> [by' ay|oy ym] m //=.
    - rewrite /=.
      case E: (block_sum bx by') => [b|] //=.
      case EA: (ax $+ ay) => [aa|] //= [<-].
      case=> [|bi'] //=.
      by rewrite E.
    - case: oy => [c|] /=.
      + rewrite /=; case E: (block_sum bx c) => [b|] //=.
        case F: (mem'_push_a ax ym) => [t|] //= [<-].
        case=> [|bi'] //=.
        * by rewrite E.
        * by rewrite (mem'_push_a_get ym ax t F bi').
      + case F: (mem'_push_a ax ym) => [t|] //= [<-].
        case=> [|bi'] //=.
        by rewrite (mem'_push_a_get ym ax t F bi').
    - case: ox => [c|] /=.
      + rewrite /=; case E: (block_sum by' c) => [b|] //=.
        case F: (mem'_push_a ay xm) => [t|] //= [<-].
        case=> [|bi'] //=.
        * by rewrite block_sum_comm E.
        * rewrite osum_None_r.
          by rewrite (mem'_push_a_get xm ay t F bi').
      + case F: (mem'_push_a ay xm) => [t|] //= [<-].
        case=> [|bi'] //=.
        rewrite osum_None_r.
        by rewrite (mem'_push_a_get xm ay t F bi').
    - case G: (mem'_sum xm ym) => [t|] //=.
      case: ox => [c|]; case: oy => [d|] //=.
      + rewrite /=; case E: (block_sum c d) => [b|] //= [<-].
        case=> [|bi'] //=.
        * by rewrite E.
        * exact: (IH ym t G bi').
      + move=> [<-]; case=> [|bi'] //=.
        exact: (IH ym t G bi').
      + move=> [<-]; case=> [|bi'] //=.
        exact: (IH ym t G bi').
      + move=> [<-]; case=> [|bi'] //=.
        exact: (IH ym t G bi').
  Qed.

  Lemma sum_get (m1 m2 m: mem A) (EQ: mem_sum m1 m2 = Some m) (bi o: nat):
    osum vclash (get m1 bi o) (get m2 bi o) = Some (get m bi o).
  Proof.
    case: m1 m2 EQ => [a1|m1] [a2|m2] //=.
    - by case: (a1 $+ a2) => [c|] //= [<-].
    - case F: (mem'_push_a a1 m2) => [t|] //= [<-] /=.
      by rewrite (mem'_push_a_get m2 a1 t F bi).
    - case F: (mem'_push_a a2 m1) => [t|] //= [<-] /=.
      rewrite (mem'_push_a_get m1 a2 t F bi).
      by rewrite osum_None_r.
    - case G: (mem'_sum m1 m2) => [t|] //= [<-] /=.
      move: (mem'_sum_get m1 m2 t G bi).
      case E1: (mem'_get m1 bi) => [b1|]; case E2: (mem'_get m2 bi) => [b2|] //=.
      + case E: (block_sum b1 b2) => [b|] //= [<-].
        exact: (block_sum_get b1 b2 b E o).
      + by move=> [<-]; rewrite osum_None_r.
      + by move=> [<-].
      + by move=> [<-].
  Qed.

  Lemma mem'_sum_to_tail: forall (x y m: mem' A),
      mem'_sum x y = Some m
      -> to_tail' x $+ to_tail' y = Some (to_tail' m).
  Proof.
    elim=> [bx ax|ox xm IH]; case=> [by' ay|oy ym] m //=.
    - case E: (block_sum bx by') => [b|] //=.
      by case EA: (ax $+ ay) => [aa|] //= [<-] /=.
    - case: oy => [c|] /=;
        [case E: (block_sum bx c) => [b|] //=|];
        case F: (mem'_push_a ax ym) => [t|] //= [<-] /=;
        exact: (mem'_push_a_to_tail ym ax t F).
    - case: ox => [c|] /=;
        [case E: (block_sum by' c) => [b|] //=|];
        case F: (mem'_push_a ay xm) => [t|] //= [<-] /=;
        rewrite op_comm;
        exact: (mem'_push_a_to_tail xm ay t F).
    - case G: (mem'_sum xm ym) => [t|] //=.
      have STEP := runshift_op _ _ _ (IH _ _ G).
      case: ox => [c|]; case: oy => [d|] //=.
      + case E: (block_sum c d) => [b|] //=.
        by move=> [<-] /=; exact: STEP.
      + by move=> [<-] /=; exact: STEP.
      + by move=> [<-] /=; exact: STEP.
      + by move=> [<-] /=; exact: STEP.
  Qed.

  Lemma sum_to_tail (m1 m2 m: mem A) (EQ: mem_sum m1 m2 = Some m):
    to_tail m1 $+ to_tail m2 = Some (to_tail m).
  Proof.
    case: m1 m2 EQ => [a1|m1] [a2|m2] //=.
    - by case EA: (a1 $+ a2) => [c|] //= [<-].
    - case F: (mem'_push_a a1 m2) => [t|] //= [<-] /=.
      exact: (mem'_push_a_to_tail m2 a1 t F).
    - case F: (mem'_push_a a2 m1) => [t|] //= [<-] /=.
      rewrite op_comm.
      exact: (mem'_push_a_to_tail m1 a2 t F).
    - case G: (mem'_sum m1 m2) => [t|] //= [<-] /=.
      exact: (runshift_op _ _ _ (mem'_sum_to_tail m1 m2 t G)).
  Qed.

  Lemma mem'_sum_some_total
    (RT: forall a: A, exists a', rshift a = Some a')
    (OT: forall a b: A, exists c, a $+ b = Some c):
    forall (x y: mem' A),
      (forall bi o, osum vclash
          (match mem'_get x bi with Some b => block_get b o | None => None end)
          (match mem'_get y bi with Some b => block_get b o | None => None end)
       <> None)
      -> exists m, mem'_sum x y = Some m.
  Proof.
    elim=> [bx ax|ox xm IH]; case=> [by' ay|oy ym] CELLS /=.
    - case: (block_sum_some bx by' (fun o => CELLS 0 o)) => [b Eb].
      rewrite Eb.
      case: (OT ax ay) => [c ->].
      by eexists.
    - case: (mem'_push_a_total RT OT ym ax) => [t Et].
      case: oy CELLS => [c|] CELLS /=.
      + case: (block_sum_some bx c (fun o => CELLS 0 o)) => [b Eb].
        rewrite Eb Et.
        by eexists.
      + rewrite Et.
        by eexists.
    - case: (mem'_push_a_total RT OT xm ay) => [t Et].
      case: ox CELLS => [c|] CELLS /=.
      + have CELLS0: forall o, osum vclash (block_get by' o) (block_get c o) <> None.
        { move=> o.
          move: (CELLS 0 o) => /=.
          by case: (block_get c o) => [w|]; case: (block_get by' o) => [w'|]. }
        case: (block_sum_some by' c CELLS0) => [b Eb].
        rewrite Eb Et.
        by eexists.
      + rewrite Et.
        by eexists.
    - have CELLS': forall bi o, osum vclash
          (match mem'_get xm bi with Some b => block_get b o | None => None end)
          (match mem'_get ym bi with Some b => block_get b o | None => None end)
        <> None
        by move=> bi o; exact: (CELLS (S bi) o).
      case: (IH ym CELLS') => [t Et].
      rewrite Et.
      case: ox CELLS => [c|] CELLS; case: oy CELLS => [d|] CELLS //=.
      + case: (block_sum_some c d (fun o => CELLS 0 o)) => [b Eb].
        rewrite Eb.
        by eexists.
      + by eexists.
      + by eexists.
      + by eexists.
  Qed.

  Lemma mem_sum_some_total
    (RT: forall a: A, exists a', rshift a = Some a')
    (OT: forall a b: A, exists c, a $+ b = Some c):
    forall (m1 m2: mem A),
      (forall bi o, osum vclash (get m1 bi o) (get m2 bi o) <> None)
      -> exists m, mem_sum m1 m2 = Some m.
  Proof.
    case=> [a1|m1] [a2|m2] CELLS /=.
    - case: (OT a1 a2) => [c ->].
      by eexists.
    - case: (mem'_push_a_total RT OT m2 a1) => [t ->].
      by eexists.
    - case: (mem'_push_a_total RT OT m1 a2) => [t ->].
      by eexists.
    - case: (mem'_sum_some_total RT OT m1 m2 (fun bi o => CELLS bi o)) => [t ->].
      by eexists.
  Qed.

  Lemma mem'_ext (m1: mem' A): forall m2: mem' A,
      (forall bi, mem'_get m1 bi = mem'_get m2 bi)
      -> to_tail' m1 = to_tail' m2
      -> m1 = m2.
  Proof.
    elim: m1 => [b1 a1|o1 m1 IH]; case=> [b2 a2|o2 m2] EXT TAILS.
    - by move: (EXT 0) TAILS => /= [->] ->.
    - exfalso.
      case: (mem'_get_nonempty m2) => [bi [b E]].
      by move: (EXT (S bi)) => /=; rewrite E.
    - exfalso.
      case: (mem'_get_nonempty m1) => [bi [b E]].
      by move: (EXT (S bi)) => /=; rewrite E.
    - move: (EXT 0) => /= ->.
      rewrite (IH m2) //.
      + by move=> bi; exact: (EXT (S bi)).
      + move: TAILS => /= TAILS.
        exact: (runshift_inj _ _ TAILS).
  Qed.

  Lemma ext_tail (m1 m2: mem A)
    (EXT: forall bi o, get m1 bi o = get m2 bi o)
    (TAILS: to_tail m1 = to_tail m2): m1 = m2.
  Proof.
    case: m1 m2 EXT TAILS => [a1|m1] [a2|m2] EXT TAILS.
    - by move: TAILS => /= ->.
    - exfalso.
      case: (mem'_get_nonempty m2) => [bi [b E]].
      case: (block_get_nonempty b) => [o [v E']].
      by move: (EXT bi o) => /=; rewrite E E'.
    - exfalso.
      case: (mem'_get_nonempty m1) => [bi [b E]].
      case: (block_get_nonempty b) => [o [v E']].
      by move: (EXT bi o) => /=; rewrite E E'.
    - congr MLive.
      apply: mem'_ext.
      + move=> bi.
        case E1: (mem'_get m1 bi) => [b1|]; case E2: (mem'_get m2 bi) => [b2|] //.
        * congr Some.
          apply: block_ext => o.
          by move: (EXT bi o) => /=; rewrite E1 E2.
        * exfalso.
          case: (block_get_nonempty b1) => [o [v E]].
          by move: (EXT bi o) => /=; rewrite E1 E2 E.
        * exfalso.
          case: (block_get_nonempty b2) => [o [v E]].
          by move: (EXT bi o) => /=; rewrite E1 E2 E.
      + move: TAILS => /= TAILS.
        exact: (runshift_inj _ _ TAILS).
  Qed.

  Definition one_at (bi o: nat) (v: value Pointer.t): mem A :=
    MLive (mem'_pad bi (M'Tail (block_one o v) $0)).

  Lemma get_one_at (bi o: nat) (v: value Pointer.t) (bi' o': nat):
    get (one_at bi o v) bi' o'
    = if (Nat.eqb bi' bi && Nat.eqb o' o)%bool then Some v else None.
  Proof.
    rewrite /= mem'_get_pad_tail.
    case: (Nat.eqb bi' bi) => /=.
    - exact: block_get_one.
    - by [].
  Qed.

  Lemma to_tail'_pad_tail (k: nat) (b: block) (a: A):
    to_tail' (mem'_pad k (M'Tail b a)) = Nat.iter k runshift a.
  Proof.
    by elim: k => [|k IH] //=; rewrite IH.
  Qed.

  Lemma runshift_iter_id (k: nat): Nat.iter k runshift ($0: A) = $0.
  Proof.
    by elim: k => [|k IH] //=; rewrite IH runshift_id.
  Qed.

  Lemma to_tail_one_at (bi o: nat) (v: value Pointer.t):
    to_tail (one_at bi o v) = $0.
  Proof.
    by rewrite /= to_tail'_pad_tail runshift_iter_id runshift_id.
  Qed.

  Definition full_at (bi n: nat) (v: value Pointer.t): mem A :=
    MLive (mem'_pad bi (M'Tail (block_full n v) $0)).

  Lemma get_full_at (bi n: nat) (v: value Pointer.t) (bi' o: nat):
    get (full_at bi n v) bi' o
    = if (Nat.eqb bi' bi && Nat.leb o n)%bool then Some v else None.
  Proof.
    rewrite /= mem'_get_pad_tail.
    case: (Nat.eqb bi' bi) => /=.
    - exact: block_get_full.
    - by [].
  Qed.

  Lemma to_tail_full_at (bi n: nat) (v: value Pointer.t):
    to_tail (full_at bi n v) = $0.
  Proof.
    by rewrite /= to_tail'_pad_tail runshift_iter_id runshift_id.
  Qed.

  Lemma mem'_set_to_tail (m: mem' A): forall (bi o: nat) (v: value Pointer.t) (m': mem' A),
      mem'_set m bi o v = Some m' -> to_tail' m' = to_tail' m.
  Proof.
    elim: m => [b a|ob m IH] [|bi] o v m' //=.
    - by case E: (block_set b o v) => [b'|] //= [<-].
    - case: ob => [b|] //=.
      by case E: (block_set b o v) => [b'|] //= [<-].
    - case E: (mem'_set m bi o v) => [m''|] //= [<-] /=.
      by rewrite (IH bi o v m'' E).
  Qed.

  Lemma set_to_tail (m m': mem A) (bi o: nat) (v: value Pointer.t)
    (EQ: set m bi o v = Some m'): to_tail m' = to_tail m.
  Proof.
    case: m EQ => [a|m] //=.
    case E: (mem'_set m bi o v) => [m''|] //= [<-] /=.
    by rewrite (mem'_set_to_tail m bi o v m'' E).
  Qed.

  Definition mem'_cons (ob: option block) (r: mem A): mem A :=
    match r with
    | MLive m => MLive (M'Cons ob m)
    | MEmpty a =>
        match ob with
        | Some b => MLive (M'Tail b a)
        | None => MEmpty (runshift a)
        end
    end.

  Lemma mem'_cons_get (ob: option block) (r: mem A) (bi: nat):
    match mem'_cons ob r with
    | MEmpty _ => None
    | MLive m => mem'_get m bi
    end
    = match bi with
      | O => ob
      | S bi => match r with
                | MEmpty _ => None
                | MLive m => mem'_get m bi
                end
      end.
  Proof.
    by case: r => [a|m]; case: ob => [b|]; case: bi => [|bi].
  Qed.

  Lemma mem'_cons_to_tail (ob: option block) (r: mem A):
    to_tail (mem'_cons ob r) = runshift (to_tail r).
  Proof.
    by case: r => [a|m]; case: ob => [b|].
  Qed.

  Fixpoint mem'_pop (m: mem' A): mem A :=
    match m with
    | M'Tail _ a => MEmpty (runshift a)
    | M'Cons ob m => mem'_cons ob (mem'_pop m)
    end.

  Definition mpop (m: mem A): option (mem A) :=
    match m with
    | MEmpty _ => None
    | MLive m' => Some (mem'_pop m')
    end.

  Lemma mem'_pop_to_tail (m: mem' A):
    to_tail (mem'_pop m) = runshift (to_tail' m).
  Proof.
    elim: m => [b a|ob m IH] //=.
    case E: (mem'_pop m) IH => [a|m'] /= IH.
    - by case: ob => [b|] /=; rewrite IH.
    - by rewrite IH.
  Qed.

  Lemma mem'_pop_get (m: mem' A): forall bi,
      match mem'_pop m with
      | MEmpty _ => None
      | MLive m' => mem'_get m' bi
      end
      = if Nat.eqb (S bi) (mem'_nblocks m) then None else mem'_get m bi.
  Proof.
    elim: m => [b a|ob m IH] bi /=.
    - by case: bi.
    - case E: (mem'_pop m) IH => [a|m'] IH.
      + case: ob => [b0|].
        * case: bi => [|bi'] /=.
          -- move: (mem'_nblocks_pos m).
             case: (mem'_nblocks m) => [|k] POS' //=.
             lia.
          -- exact: (IH bi').
        * case: bi => [|bi'] /=.
          -- move: (mem'_nblocks_pos m).
             by case: (mem'_nblocks m) => [|k] POS'.
          -- exact: (IH bi').
      + case: bi => [|bi'] /=.
        * move: (mem'_nblocks_pos m).
          case: (mem'_nblocks m) => [|k] POS' //=.
          lia.
        * exact: (IH bi').
  Qed.

  Lemma mpop_some (m: mem A) (NE: forall a, m <> MEmpty a): exists m', mpop m = Some m'.
  Proof.
    case: m NE => [a|m] NE.
    - by exfalso; apply: (NE a).
    - by eexists.
  Qed.

  Lemma mpop_get (m m': mem A) (EQ: mpop m = Some m') (bi o: nat):
    get m' bi o = if Nat.eqb (S bi) (nblocks m) then None else get m bi o.
  Proof.
    case: m EQ => [a|m] EQ; first by [].
    move: EQ => -[<-].
    rewrite [nblocks (MLive m)]/=.
    move: (mem'_pop_get m bi).
    case Eb: (Nat.eqb (S bi) (mem'_nblocks m)) => H.
    - case: (mem'_pop m) H => [a'|m1] H //.
      by rewrite /get H.
    - case: (mem'_pop m) H => [a'|m1] H.
      + by rewrite /get -H.
      + by rewrite /get H.
  Qed.

  Lemma to_tail_mpop (m m': mem A) (EQ: mpop m = Some m'): to_tail m' = to_tail m.
  Proof.
    case: m EQ => [a|m] //= [<-].
    exact: mem'_pop_to_tail.
  Qed.

  Fixpoint mem'_unown (m: mem' A): mem' A :=
    match m with
    | M'Tail b _ => M'Tail b $0
    | M'Cons ob m => M'Cons ob (mem'_unown m)
    end.

  Lemma mem'_unown_get (m: mem' A): forall bi,
      mem'_get (mem'_unown m) bi = mem'_get m bi.
  Proof.
    by elim: m => [b a|ob m IH] [|bi] //=.
  Qed.

  Lemma mem'_unown_to_tail (m: mem' A): to_tail' (mem'_unown m) = $0.
  Proof.
    by elim: m => [b a|ob m IH] //=; rewrite ?IH ?runshift_id.
  Qed.

  Fixpoint mem'_diff (m2 m1: mem' A) {struct m2}: mem A :=
    match m2 with
    | M'Tail b2 a2 =>
        mem'_cons (odiff block_diff (Some b2) (mem'_get m1 0)) (MEmpty a2)
    | M'Cons ob2 m2 =>
        mem'_cons (odiff block_diff ob2 (mem'_get m1 0))
          (match m1 with
           | M'Tail _ _ => MLive m2
           | M'Cons _ m1 => mem'_diff m2 m1
           end)
    end.

  Lemma mem'_diff_get (m2: mem' A): forall (m1: mem' A) (bi: nat),
      match mem'_diff m2 m1 with
      | MEmpty _ => None
      | MLive m => mem'_get m bi
      end
      = odiff block_diff (mem'_get m2 bi) (mem'_get m1 bi).
  Proof.
    elim: m2 => [b2 a2|ob2 m2 IH] m1 bi /=.
    - case E1: (mem'_get m1 0) => [b1|] /=.
      + case: bi => [|bi'] /=.
        * rewrite E1.
          by case: (block_diff b2 b1) => [b|].
        * by case: (block_diff b2 b1) => [b|].
      + case: bi => [|bi'] /=.
        * by rewrite E1.
        * by [].
    - case: m1 => [b1 a1|ob1 m1] /=.
      + case: bi => [|bi'] /=.
        * by [].
        * by rewrite odiff_None_r.
      + rewrite mem'_cons_get.
        by case: bi => [|bi'] //=.
  Qed.

  Lemma mem'_diff_to_tail (m2: mem' A): forall m1: mem' A,
      to_tail (mem'_diff m2 m1) = runshift (to_tail' m2).
  Proof.
    elim: m2 => [b2 a2|ob2 m2 IH] m1 /=.
    - case: (mem'_get m1 0) => [b1|] /=.
      + by case: (block_diff b2 b1) => [b|].
      + by [].
    - rewrite mem'_cons_to_tail.
      case: m1 => [b1 a1|ob1 m1] //=.
      by rewrite (IH m1).
  Qed.

  Lemma rshift_op_runshift (a t t': A)
    (EQ: a $+ runshift t = Some (runshift t'))
    : exists a', rshift a = Some a' /\ a' $+ t = Some t'.
  Proof.
    have EQt' := rshift_sum a (runshift t).
    rewrite EQ /= !rshift_runshift /= in EQt'.
    case: (rshift a) EQt' => [a'|] //= EQt'.
    by exists a'.
  Qed.

  Lemma runshift_op_inv (p q r: A)
    (EQ: runshift p $+ runshift q = Some (runshift r))
    : p $+ q = Some r.
  Proof.
    case: (rshift_op_runshift _ _ _ EQ) => p' [].
    by rewrite rshift_runshift => -[<-].
  Qed.

  Lemma mem'_push_a_complete (ym: mem' A): forall (mm: mem' A) (a: A),
      (forall bi, mem'_get ym bi = mem'_get mm bi)
      -> a $+ runshift (to_tail' ym) = Some (runshift (to_tail' mm))
      -> mem'_push_a a ym = Some mm.
  Proof.
    elim: ym => [b t|o ym IH]; case=> [b' t'|o' mm] a POS TAIL;
      case: (rshift_op_runshift _ _ _ TAIL) => a' [Ra /= Ea] /=; rewrite Ra.
    - move: (POS 0) => /= [<-].
      by rewrite Ea.
    - exfalso.
      case: (mem'_get_nonempty mm) => [bi [b0 E]].
      by move: (POS (S bi)) => /=; rewrite E.
    - exfalso.
      case: (mem'_get_nonempty ym) => [bi [b0 E]].
      by move: (POS (S bi)) => /=; rewrite E.
    - move: (POS 0) => /= <-.
      by rewrite (IH mm a' (fun bi => POS (S bi)) Ea).
  Qed.

  Lemma mem'_sum_complete (x: mem' A): forall (y m: mem' A),
      (forall bi, osum block_sum (mem'_get x bi) (mem'_get y bi) = Some (mem'_get m bi))
      -> to_tail' x $+ to_tail' y = Some (to_tail' m)
      -> mem'_sum x y = Some m.
  Proof.
    elim: x => [bx ax|ox xm IH]; case=> [by' ay|oy ym]; case=> [bm am|om mm] POS TAIL;
      rewrite /= in TAIL.
    - have P0: osum block_sum (Some bx) (Some by') = Some (Some bm) := POS 0.
      rewrite /= in P0.
      case E: (block_sum bx by') P0 => [b|] // [<-].
      by rewrite mem'_sum_tail_tail E /= TAIL.
    - exfalso.
      case: (mem'_get_nonempty mm) => [bi [b E]].
      have := POS (S bi).
      by rewrite /= E.
    - exfalso.
      case: (mem'_get_nonempty ym) => [bi [b E]].
      have := POS (S bi).
      by rewrite /= E.
    - have P0: osum block_sum (Some bx) oy = Some om := POS 0.
      have POS': forall bi, mem'_get ym bi = mem'_get mm bi.
      { move=> bi.
        have := POS (S bi).
        by rewrite /= => -[->]. }
      by rewrite mem'_sum_tail_cons P0 /= (mem'_push_a_complete ym mm ax POS' TAIL).
    - exfalso.
      case: (mem'_get_nonempty xm) => [bi [b E]].
      have := POS (S bi).
      by rewrite /= E.
    - have P0: osum block_sum (Some by') ox = Some om
        by rewrite osum_block_comm; exact: (POS 0).
      have POS': forall bi, mem'_get xm bi = mem'_get mm bi.
      { move=> bi.
        have := POS (S bi).
        by rewrite /= osum_None_r => -[->]. }
      rewrite op_comm in TAIL.
      by rewrite mem'_sum_cons_tail P0 /= (mem'_push_a_complete xm mm ay POS' TAIL).
    - exfalso.
      case: (mem'_get_nonempty xm) => [bi [b E]].
      have := POS (S bi).
      rewrite /= E.
      case: (mem'_get ym bi) => [c|] //=.
      by case: (block_sum b c).
    - have P0: osum block_sum ox oy = Some om := POS 0.
      rewrite mem'_sum_cons_cons P0 /=.
      by rewrite (IH ym mm (fun bi => POS (S bi)) (runshift_op_inv _ _ _ TAIL)).
  Qed.

  Lemma mem'_cell_nonempty (m: mem' A): exists bi o v, get (MLive m) bi o = Some v.
  Proof.
    case: (mem'_get_nonempty m) => [bi [b E]].
    case: (block_get_nonempty b) => [o [v E']].
    by exists bi, o, v; rewrite /= E E'.
  Qed.

  Lemma mem_sum_complete (m1 m2 m: mem A)
    (CELLS: forall bi o, osum vclash (get m1 bi o) (get m2 bi o) = Some (get m bi o))
    (TAIL: to_tail m1 $+ to_tail m2 = Some (to_tail m))
    : mem_sum m1 m2 = Some m.
  Proof.
    case: m1 m2 m CELLS TAIL => [a1|x] [a2|y] [am|mm] CELLS TAIL; rewrite /= in TAIL.
    - by rewrite /= TAIL.
    - exfalso.
      case: (mem'_cell_nonempty mm) => [bi [o [v E]]].
      by move: (CELLS bi o); rewrite E.
    - exfalso.
      case: (mem'_cell_nonempty y) => [bi [o [v E]]].
      by move: (CELLS bi o); rewrite E.
    - have POS: forall bi, mem'_get y bi = mem'_get mm bi.
      { move=> bi.
        by move: (osum_block_ext None (mem'_get y bi) (mem'_get mm bi) (CELLS bi))
          => /= -[->]. }
      by rewrite /= (mem'_push_a_complete y mm a1 POS TAIL).
    - exfalso.
      case: (mem'_cell_nonempty x) => [bi [o [v E]]].
      by move: (CELLS bi o); rewrite E osum_None_r.
    - have POS: forall bi, mem'_get x bi = mem'_get mm bi.
      { move=> bi.
        move: (osum_block_ext (mem'_get x bi) None (mem'_get mm bi) (CELLS bi)).
        by rewrite osum_None_r => -[->]. }
      rewrite op_comm in TAIL.
      by rewrite /= (mem'_push_a_complete x mm a2 POS TAIL).
    - exfalso.
      case: (mem'_cell_nonempty x) => [bi [o [v E]]].
      move: (CELLS bi o); rewrite E.
      by case: (get (MLive y) bi o).
    - have POS: forall bi, osum block_sum (mem'_get x bi) (mem'_get y bi)
                           = Some (mem'_get mm bi)
        by move=> bi; exact: (osum_block_ext _ _ _ (CELLS bi)).
      by rewrite /= (mem'_sum_complete x y mm POS (runshift_op_inv _ _ _ TAIL)).
  Qed.

  Lemma get_mem'_cons (ob: option block) (r: mem A) (bi o: nat):
    get (mem'_cons ob r) bi o
    = match bi with
      | O => match ob with Some b => block_get b o | None => None end
      | S bi => get r bi o
      end.
  Proof.
    by case: r => [a|m]; case: ob => [b|]; case: bi => [|bi].
  Qed.

  Fixpoint mem'_filter (k: nat -> nat -> bool) (m: mem' A): mem A :=
    match m with
    | M'Tail b _ => mem'_cons (block_filter (k 0) b) (MEmpty $0)
    | M'Cons ob m =>
        mem'_cons (bind (block_filter (k 0)) ob) (mem'_filter (fun bi => k (S bi)) m)
    end.

  Lemma get_mem'_filter (m: mem' A): forall (k: nat -> nat -> bool) (bi o: nat),
      get (mem'_filter k m) bi o = if k bi o then get (MLive m) bi o else None.
  Proof.
    elim: m => [b t|ob m IH] k bi o; rewrite get_mem'_cons.
    - case: bi => [|bi] /=.
      + exact: block_filter_get.
      + by case: (k (S bi) o).
    - case: bi => [|bi] /=.
      + case: ob => [b|] /=.
        * exact: block_filter_get.
        * by case: (k 0 o).
      + exact: (IH (fun bi => k (S bi)) bi o).
  Qed.

  Lemma to_tail_mem'_filter (m: mem' A): forall k: nat -> nat -> bool,
      to_tail (mem'_filter k m) = $0.
  Proof.
    elim: m => [b t|ob m IH] k; rewrite mem'_cons_to_tail ?IH; exact: runshift_id.
  Qed.

  Definition mem_filter (k: nat -> nat -> bool) (m: mem A): mem A :=
    match m with
    | MEmpty _ => MEmpty $0
    | MLive m => mem'_filter k m
    end.

  Lemma get_mem_filter (k: nat -> nat -> bool) (m: mem A) (bi o: nat):
    get (mem_filter k m) bi o = if k bi o then get m bi o else None.
  Proof.
    case: m => [a|m] /=.
    - by case: (k bi o).
    - exact: get_mem'_filter.
  Qed.

  Lemma to_tail_mem_filter (k: nat -> nat -> bool) (m: mem A):
    to_tail (mem_filter k m) = $0.
  Proof.
    case: m => [a|m] //=.
    exact: to_tail_mem'_filter.
  Qed.

  Lemma mem_piece (x: mem A) (k: nat -> nat -> bool) (t u: A)
    (TU: t $+ u = Some (to_tail x))
    : exists p, (forall bi o, get p bi o = if k bi o then get x bi o else None)
                /\ to_tail p = t.
  Proof.
    have E01: mem_sum (mem_filter k x) (mem_filter (fun bi o => ~~ k bi o) x)
              = Some (mem_filter (fun _ _ => true) x).
    { apply: mem_sum_complete.
      - move=> bi o.
        rewrite !get_mem_filter.
        case: (k bi o) => /=.
        + exact: osum_None_r.
        + by [].
      - by rewrite !to_tail_mem_filter op_id_l. }
    have E2: mem_sum (mem_filter (fun _ _ => true) x) (MEmpty (to_tail x)) = Some x.
    { apply: mem_sum_complete.
      - move=> bi o.
        rewrite get_mem_filter /=.
        exact: osum_None_r.
      - by rewrite to_tail_mem_filter /= op_id_l. }
    have E3: mem_sum (MEmpty t) (MEmpty u) = Some (MEmpty (to_tail x))
      by rewrite /= TU.
    case: (op_swap _ _ _ _ _ E01 E2) => [u1 [E4 _]].
    rewrite op_comm in E4.
    case: (op_swap _ _ _ _ _ E3 E4) => [p [E5 _]].
    exists p; split.
    - move=> bi o.
      move: (sum_get _ _ _ E5 bi o).
      by rewrite get_mem_filter /= => -[<-].
    - move: (sum_to_tail _ _ _ E5).
      by rewrite to_tail_mem_filter /= op_id_r => -[<-].
  Qed.

  Lemma mem_sum_cross_split: forall a b c d z: mem A,
      mem_sum a b = Some z -> mem_sum c d = Some z ->
      exists ac ad bc bd: mem A,
        mem_sum ac ad = Some a /\ mem_sum bc bd = Some b
        /\ mem_sum ac bc = Some c /\ mem_sum ad bd = Some d.
  Proof.
    move=> a b c d z E1 E2.
    case: (op_cross_split _ _ _ _ _ (sum_to_tail _ _ _ E1) (sum_to_tail _ _ _ E2))
      => tac [tad [tbc [tbd [Ta [Tb [Tc Td]]]]]].
    have Ta': tad $+ tac = Some (to_tail a) by rewrite op_comm.
    have Tb': tbd $+ tbc = Some (to_tail b) by rewrite op_comm.
    case: (mem_piece a (fun bi o => isSome (get c bi o)) _ _ Ta) => pac [Gac EQtac].
    case: (mem_piece a (fun bi o => isSome (get d bi o)) _ _ Ta') => pad [Gad EQtad].
    case: (mem_piece b (fun bi o => isSome (get c bi o)) _ _ Tb) => pbc [Gbc EQtbc].
    case: (mem_piece b (fun bi o => isSome (get d bi o)) _ _ Tb') => pbd [Gbd EQtbd].
    have CELLS := fun bi o =>
      osum_vclash_cross _ _ _ _ _ (sum_get _ _ _ E1 bi o) (sum_get _ _ _ E2 bi o).
    exists pac, pad, pbc, pbd.
    split; [|split; [|split]]; apply: mem_sum_complete => [bi o|].
    - by rewrite Gac Gad; case: (CELLS bi o).
    - by rewrite EQtac EQtad.
    - by rewrite Gbc Gbd; case: (CELLS bi o) => _ [].
    - by rewrite EQtbc EQtbd.
    - by rewrite Gac Gbc; case: (CELLS bi o) => _ [_ []].
    - by rewrite EQtac EQtbc.
    - by rewrite Gad Gbd; case: (CELLS bi o) => _ [_ [_]].
    - by rewrite EQtad EQtbd.
  Qed.

  Section AddrInterface.

    Context {Ad: Addr.type}.

    Definition aone (a: Ad) (v: value Pointer.t): mem A :=
      one_at (Imp.Addr.block a) (N.to_nat (offset a)) v.

    Definition aget (m: mem A) (a: Ad): option (value Pointer.t) :=
      get m (Imp.Addr.block a) (N.to_nat (offset a)).

    Lemma aget_aone (a: Ad) (v: value Pointer.t) (a': Ad):
      aget (aone a v) a'
      = if (Nat.eqb (Imp.Addr.block a') (Imp.Addr.block a)
            && Nat.eqb (N.to_nat (offset a')) (N.to_nat (offset a)))%bool
        then Some v else None.
    Proof.
      exact: (get_one_at (Imp.Addr.block a) (N.to_nat (offset a)) v
                (Imp.Addr.block a') (N.to_nat (offset a'))).
    Qed.

    Lemma aget_aone_eq (a: Ad) (v: value Pointer.t): aget (aone a v) a = Some v.
    Proof.
      by rewrite aget_aone !Nat.eqb_refl.
    Qed.

    Lemma aindex_neq (a a': Ad) (NE: a' <> a):
      (Nat.eqb (Imp.Addr.block a') (Imp.Addr.block a)
       && Nat.eqb (N.to_nat (offset a')) (N.to_nat (offset a)))%bool = false.
    Proof.
      case Eb: (Nat.eqb (Imp.Addr.block a') (Imp.Addr.block a)) => //.
      case Eo: (Nat.eqb (N.to_nat (offset a')) (N.to_nat (offset a))) => //.
      exfalso; apply: NE.
      move/Nat.eqb_eq in Eb.
      move/Nat.eqb_eq in Eo.
      by apply: addr_ext; [ exact: Eb | apply: N2Nat.inj; exact: Eo ].
    Qed.

    Lemma aindex_eq (a a': Ad)
      (EB: Nat.eqb (Imp.Addr.block a') (Imp.Addr.block a) = true)
      (EO: Nat.eqb (N.to_nat (offset a')) (N.to_nat (offset a)) = true):
      a' = a.
    Proof.
      move/Nat.eqb_eq in EB.
      move/Nat.eqb_eq in EO.
      by apply: addr_ext; [ exact: EB | apply: N2Nat.inj; exact: EO ].
    Qed.

    Lemma aone_mkAddr (k: nat) (o: N.t) (v: value Pointer.t):
      aone (mkAddr (s:=Ad) k o) v = one_at k (N.to_nat o) v.
    Proof.
      by rewrite /aone mkAddr_block mkAddr_offset.
    Qed.

    Lemma aext_tail (m1 m2: mem A)
      (EXT: forall a: Ad, aget m1 a = aget m2 a)
      (TAILS: to_tail m1 = to_tail m2): m1 = m2.
    Proof.
      apply: ext_tail => [bi o|//].
      move: (EXT (mkAddr bi (N.of_nat o))).
      by rewrite /aget mkAddr_block mkAddr_offset Nat2N.id.
    Qed.


    Definition mem_read {Nm: Ref.type Ad} (m: mem A) (r: Nm): option (value Pointer.t) :=
      match ref_addr r with
      | Some a => if allows r Operation.Read then aget m a else None
      | None => None
      end.

    Definition mem_mutate {Nm: Ref.type Ad} (m: mem A) (r: Nm) (v: value Pointer.t)
      : option (mem A) :=
      match ref_addr r with
      | Some a =>
          if allows r Operation.Write
          then set m (Imp.Addr.block a) (N.to_nat (offset a)) v
          else None
      | None => None
      end.

  End AddrInterface.

End TailAlgebra.

HB.instance Definition _ (T: AllocSlot.type) :=
  hasCrossSplit.Build (mem T) mem_sum_cross_split.

Definition excl_rshift (a: excl nat): option (excl nat) :=
  match a with
  | Unowned => Some Unowned
  | Owned 0 => None
  | Owned (S n) => Some (Owned n)
  end.

Lemma excl_rshift_runshift: forall a: excl nat, excl_rshift (excl_map S a) = Some a.
Proof.
  by case.
Qed.

Lemma excl_runshift_id: excl_map S ($0: excl nat) = ($0: excl nat).
Proof.
  by [].
Qed.

Lemma excl_rshift_sum: forall a b: excl nat,
    bind excl_rshift (a $+ b)
    = bind (fun a' => bind (fun b' => a' $+ b') (excl_rshift b)) (excl_rshift a).
Proof.
  by case=> [|[|n]]; case=> [|[|k]].
Qed.

Lemma excl_rshift_inj: forall a b c: excl nat,
    excl_rshift a = Some c -> excl_rshift b = Some c -> a = b.
Proof.
  by move=> [|[|n]] [|[|k]] [|c] //= [E1] [E2]; congruence.
Qed.

HB.instance Definition _ :=
  hasShift.Build (excl nat) excl_rshift (excl_map S)
    excl_rshift_runshift excl_runshift_id excl_rshift_sum excl_rshift_inj.

Lemma unit_some_inj: forall a b c: unit,
    Some a = Some c -> Some b = Some c -> a = b.
Proof.
  by case; case.
Qed.

HB.instance Definition _ :=
  hasShift.Build unit (fun a: unit => Some a) (fun a: unit => a)
    (fun a: unit => erefl) erefl (fun a b: unit => erefl)
    unit_some_inj.

Lemma unit_rshift_total: forall a: unit, exists a', rshift a = Some a'.
Proof.
  by move=> a; exists a.
Qed.

Lemma unit_op_total: forall a b: unit, exists c: unit, a $+ b = Some c.
Proof.
  by move=> a b; exists tt.
Qed.

Lemma to_tail'_pad_tail_alloc (k: nat) (b: block) (a: excl nat):
  to_tail' (mem'_pad k (M'Tail b a)) = excl_map (Nat.add k) a.
Proof.
  elim: k => [|k IH] /=.
  - by case: a.
  - by rewrite IH {IH}; case: a.
Qed.

Lemma to_tail'_nblocks_alloc (m: mem' (excl nat)): forall k,
    to_tail' m = Owned k -> mem'_nblocks m <= S k.
Proof.
  elim: m => [b a|o m IH] k /=.
  - move=> _; lia.
  - case E: (to_tail' m) => [|j] //= [<-].
    move: (IH j E); lia.
Qed.

Lemma to_tail_nblocks_alloc (m: mem (excl nat)) (k: nat) (EQ: to_tail m = Owned k):
  nblocks m <= k.
Proof.
  case: m EQ => [a|m] /=.
  - move=> _; lia.
  - case E: (to_tail' m) => [|j] //= [<-].
    exact: (to_tail'_nblocks_alloc m j E).
Qed.

Fixpoint mem'_alloc (m: mem' (excl nat)) (n: nat) (v: value Pointer.t): option (mem' (excl nat)) :=
  match m with
  | M'Tail b a =>
      match a with
      | Unowned => None
      | Owned g =>
          Some (M'Cons (Some b) (mem'_pad g (M'Tail (block_full n v) (Owned 0))))
      end
  | M'Cons ob m => option_map (M'Cons ob) (mem'_alloc m n v)
  end.

Definition alloc (m: mem (excl nat)) (n: nat) (v: value Pointer.t): option (mem (excl nat)) :=
  match m with
  | MEmpty Unowned => None
  | MEmpty (Owned k) => Some (MLive (mem'_pad k (M'Tail (block_full n v) (Owned 0))))
  | MLive m' => option_map MLive (mem'_alloc m' n v)
  end.

Lemma mem'_alloc_defined (m: mem' (excl nat)): forall (n: nat) (v: value Pointer.t),
    (exists j, to_tail' m = Owned j) <-> (exists m', mem'_alloc m n v = Some m').
Proof.
  elim: m => [b a|ob m IH] n v /=.
  - case: a => [|g].
    + by split=> -[x E].
    + by split=> _; eexists.
  - split=> -[x E].
    + move: E; case A: (to_tail' m) => [|j] //= _.
      case: (proj1 (IH n v) (ex_intro _ j A)) => [m' Em].
      by exists (M'Cons ob m'); rewrite Em.
    + move: E; case Em: (mem'_alloc m n v) => [m'|] //= _.
      case: (proj2 (IH n v) (ex_intro _ m' Em)) => [j Ej].
      by exists (S j); rewrite Ej.
Qed.

Lemma mem'_alloc_to_tail (m: mem' (excl nat)): forall (n: nat) (v: value Pointer.t) (m': mem' (excl nat)),
    mem'_alloc m n v = Some m' -> to_tail' m' = excl_map S (to_tail' m).
Proof.
  elim: m => [b a|ob m IH] n v m' /=.
  - case: a => [|g] //= [<-] /=.
    by rewrite to_tail'_pad_tail_alloc /= Nat.add_0_r.
  - case E: (mem'_alloc m n v) => [m''|] //= [<-] /=.
    by rewrite (IH n v m'' E); case: (to_tail' m).
Qed.

Lemma mem'_alloc_get (m: mem' (excl nat)): forall (n: nat) (v: value Pointer.t) (m': mem' (excl nat)) (j: nat),
    mem'_alloc m n v = Some m'
    -> to_tail' m = Owned j
    -> forall bi, mem'_get m' bi
                  = if Nat.eqb bi (S j) then Some (block_full n v) else mem'_get m bi.
Proof.
  elim: m => [b a|ob m IH] n v m' j /=.
  - case: a => [|g] //= [<-] [<-].
    case=> [|bi] //=.
    by rewrite mem'_get_pad_tail; case: (Nat.eqb bi g).
  - case E: (mem'_alloc m n v) => [m''|] //= [<-].
    case A: (to_tail' m) => [|j0] //= [<-].
    case=> [|bi] //=.
    exact: (IH n v m'' j0 E A bi).
Qed.

Lemma mem'_alloc_nblocks (m: mem' (excl nat)): forall (n: nat) (v: value Pointer.t) (m': mem' (excl nat)) (j: nat),
    mem'_alloc m n v = Some m'
    -> to_tail' m = Owned j
    -> mem'_nblocks m' = S (S j).
Proof.
  elim: m => [b a|ob m IH] n v m' j /=.
  - case: a => [|g] //= [<-] [<-] /=.
    by rewrite mem'_nblocks_pad_tail.
  - case E: (mem'_alloc m n v) => [m''|] //= [<-].
    case A: (to_tail' m) => [|j0] //= [<-] /=.
    by rewrite (IH n v m'' j0 E A).
Qed.

Lemma alloc_defined (m: mem (excl nat)) (n: nat) (v: value Pointer.t):
  (exists k, to_tail m = Owned k) <-> (exists m', alloc m n v = Some m').
Proof.
  case: m => [a|m] /=.
  - case: a => [|k].
    + by split=> -[x E].
    + by split=> _; eexists.
  - split=> -[x E].
    + have [j Ej]: exists j, to_tail' m = Owned j
        by move: E; case: (to_tail' m) => [|j] //= _; exists j.
      case: (proj1 (mem'_alloc_defined m n v) (ex_intro _ j Ej)) => [m' Em].
      by exists (MLive m'); rewrite Em.
    + move: E; case Em: (mem'_alloc m n v) => [m'|] //= _.
      case: (proj2 (mem'_alloc_defined m n v) (ex_intro _ m' Em)) => [j Ej].
      by exists (S j); rewrite Ej.
Qed.

Lemma to_tail_alloc (m m': mem (excl nat)) (n: nat) (v: value Pointer.t)
  (EQ: alloc m n v = Some m'): to_tail m' = excl_map S (to_tail m).
Proof.
  case: m EQ => [a|m] /=.
  - case: a => [|k] //= [<-] /=.
    by rewrite to_tail'_pad_tail_alloc /= Nat.add_0_r.
  - case E: (mem'_alloc m n v) => [m''|] //= [<-] /=.
    by rewrite (mem'_alloc_to_tail m n v m'' E); case: (to_tail' m).
Qed.

Lemma get_alloc (m m': mem (excl nat)) (n: nat) (v: value Pointer.t) (k: nat)
  (EQ: alloc m n v = Some m') (AL: to_tail m = Owned k) (bi o: nat):
  get m' bi o
  = if (Nat.eqb bi k && Nat.leb o n)%bool then Some v else get m bi o.
Proof.
  case: m EQ AL => [a|m] /=.
  - case: a => [|j] //= [<-] [<-] /=.
    rewrite mem'_get_pad_tail.
    case: (Nat.eqb bi j) => //=.
    exact: block_get_full.
  - case E: (mem'_alloc m n v) => [m''|] //= [<-].
    case A: (to_tail' m) => [|j] //= [<-] /=.
    rewrite (mem'_alloc_get m n v m'' j E A bi).
    case Eb: (Nat.eqb bi (S j)) => //=.
    move/Nat.eqb_eq in Eb; subst bi.
    rewrite (mem'_get_ge m (S j) (to_tail'_nblocks_alloc m j A)).
    exact: block_get_full.
Qed.

Lemma nblocks_alloc (m m': mem (excl nat)) (n: nat) (v: value Pointer.t) (k: nat)
  (EQ: alloc m n v = Some m') (AL: to_tail m = Owned k): nblocks m' = S k.
Proof.
  case: m EQ AL => [a|m] /=.
  - case: a => [|j] //= [<-] [<-] /=.
    by rewrite mem'_nblocks_pad_tail.
  - case E: (mem'_alloc m n v) => [m''|] //= [<-].
    case A: (to_tail' m) => [|j] //= [<-] /=.
    exact: (mem'_alloc_nblocks m n v m'' j E A).
Qed.

Lemma mpop_alloc_some (m m': mem (excl nat)) (n: nat) (v: value Pointer.t)
  (EQ: alloc m n v = Some m'): exists m'', mpop m' = Some m''.
Proof.
  case: m EQ => [a|m] /=.
  - by case: a => [|k] //= [<-]; eexists.
  - by case E: (mem'_alloc m n v) => [m''|] //= [<-]; eexists.
Qed.

Lemma mpop_alloc (m m' m'': mem (excl nat)) (n: nat) (v: value Pointer.t) (k: nat)
  (AL: to_tail m = Owned k)
  (EQ: alloc m n v = Some m') (EQ': mpop m' = Some m''):
  (forall bi o, get m'' bi o = get m bi o)
  /\ to_tail m'' = excl_map S (to_tail m).
Proof.
  split.
  - move=> bi o.
    rewrite (mpop_get m' m'' EQ' bi o) (nblocks_alloc m m' n v k EQ AL).
    rewrite (get_alloc m m' n v k EQ AL bi o) /=.
    case E: (Nat.eqb bi k) => /=.
    + move/Nat.eqb_eq in E; subst bi.
      by rewrite (get_nblocks_ge m k o (to_tail_nblocks_alloc m k AL)).
    + by [].
  - by rewrite (to_tail_mpop m' m'' EQ') (to_tail_alloc m m' n v EQ).
Qed.

Lemma mem'_push_a_pad_tail (k: nat): forall (B: nat) (b: block),
    k < B
    -> exists m', mem'_push_a (Owned B) (mem'_pad k (M'Tail b Unowned)) = Some m'.
Proof.
  elim: k => [|k IH] B b LT.
  - case: B LT => [|B'] LT.
    + lia.
    + by eexists.
  - case: B LT => [|B'] LT.
    + lia.
    + have LT': k < B' by lia.
      case: (IH B' b LT') => [t E] /=.
      rewrite E.
      by eexists.
Qed.

Lemma mem'_sum_one (m: mem' (excl nat)): forall (k: nat) (b: block),
    mem'_get m k = None
    -> (forall j, to_tail' m = Owned j -> k < S j)
    -> exists m', mem'_sum m (mem'_pad k (M'Tail b Unowned)) = Some m'.
Proof.
  elim: m => [b0 a0|ob m IH] k b VAC BND.
  - case: k VAC BND => [|k'] VAC BND; first by [].
    case: a0 {VAC} BND => [|g] BND /=.
    + rewrite mem'_push_a_id /=.
      by eexists.
    + have LT: k' < g by move: (BND g erefl); lia.
      case: (mem'_push_a_pad_tail k' g b LT) => [t E].
      rewrite E.
      by eexists.
  - case: k VAC BND => [|k'] VAC BND.
    + move: VAC => /= VAC.
      rewrite /= VAC mem'_push_a_id.
      by eexists.
    + have BND': forall j, to_tail' m = Owned j -> k' < S j.
      { move=> j Ej.
        have := BND (S j).
        rewrite /= Ej /= => /(_ erefl).
        lia. }
      case: (IH k' b VAC BND') => [t E].
      rewrite /= E.
      case: ob {VAC BND BND'} => [c|]; by eexists.
Qed.

Lemma sum_one_fresh_at_alloc (m: mem (excl nat)) (k o: nat) (v: value Pointer.t)
  (FRESH: forall o', get m k o' = None)
  (BOUND: forall B, to_tail m = Owned B -> k < B):
  exists m', mem_sum m (one_at k o v) = Some m'.
Proof.
  case: m FRESH BOUND => [a|m0] FRESH BOUND.
  - case: a {FRESH} BOUND => [|B] BOUND /=.
    + rewrite mem'_push_a_id.
      by eexists.
    + have LT: k < B by move: (BOUND B erefl).
      case: (mem'_push_a_pad_tail k B (block_one o v) LT) => [t E].
      rewrite E.
      by eexists.
  - have VAC: mem'_get m0 k = None.
    { case E: (mem'_get m0 k) => [b|] //.
      case: (block_get_nonempty b) => [o' [w Eb]].
      move: (FRESH o') => /=.
      by rewrite E Eb. }
    have BND': forall j, to_tail' m0 = Owned j -> k < S j.
    { move=> j Ej.
      have := BOUND (S j).
      rewrite /= Ej /= => /(_ erefl).
      lia. }
    case: (mem'_sum_one m0 k (block_one o v) VAC BND') => [t E].
    rewrite /= /op /= E.
    by eexists.
Qed.

Lemma mem'_push_a_some (m: mem' (excl nat)): forall g: nat,
    mem'_nblocks m <= g
    -> to_tail' m = Unowned
    -> exists m', mem'_push_a (Owned g) m = Some m'.
Proof.
  elim: m => [b a|ob m IH] g NB AL.
  - case: g NB => [|g'] NB; first by (exfalso; move: NB => /=; lia).
    move: AL => /= ->.
    by eexists.
  - case: g NB => [|g'] NB; first by (exfalso; move: NB => /=; lia).
    have NB': mem'_nblocks m <= g' by move: NB => /=; lia.
    have AL': to_tail' m = Unowned
      by move: AL => /=; case: (to_tail' m) => [|j].
    case: (IH g' NB' AL') => [t Et].
    rewrite /= Et.
    by eexists.
Qed.

Lemma mem'_sum_some (x: mem' (excl nat)): forall y: mem' (excl nat),
    (forall bi o, osum vclash
        (match mem'_get x bi with Some b => block_get b o | None => None end)
        (match mem'_get y bi with Some b => block_get b o | None => None end)
     <> None)
    -> to_tail' x $+ to_tail' y <> None
    -> (forall g, to_tail' x = Owned g -> mem'_nblocks y <= S g)
    -> (forall g, to_tail' y = Owned g -> mem'_nblocks x <= S g)
    -> exists m, mem'_sum x y = Some m.
Proof.
  elim: x => [bx ax|ox xm IH]; case=> [by' ay|oy ym] CELLS ALC DOMX DOMY //=.
  - case: (block_sum_some bx by' (fun o => CELLS 0 o)) => [b Eb].
    rewrite /op /= Eb.
    move: ALC; rewrite /op /=.
    case A: (excl_sum ax ay) => [aa|] //= _.
    by eexists.
  - have PUSH: exists t, mem'_push_a ax ym = Some t.
    { case: ax CELLS ALC DOMX {DOMY} => [|g] CELLS ALC DOMX.
      - rewrite mem'_push_a_id.
        by eexists.
      - apply: mem'_push_a_some.
        + move: (DOMX g erefl) => /=; lia.
        + move: ALC => /=.
          by case: (to_tail' ym) => [|j]. }
    case: PUSH => [t Et].
    case: oy CELLS {ALC DOMX DOMY} => [c|] CELLS /=.
    + case: (block_sum_some bx c (fun o => CELLS 0 o)) => [b Eb].
      rewrite /op /= Eb Et.
      by eexists.
    + rewrite Et.
      by eexists.
  - have PUSH: exists t, mem'_push_a ay xm = Some t.
    { case: ay CELLS ALC DOMY {DOMX} => [|g] CELLS ALC DOMY.
      - rewrite mem'_push_a_id.
        by eexists.
      - apply: mem'_push_a_some.
        + move: (DOMY g erefl) => /=; lia.
        + move: ALC => /=.
          by case: (to_tail' xm) => [|j]. }
    case: PUSH => [t Et].
    case: ox CELLS {ALC DOMX DOMY} => [c|] CELLS /=.
    + have CELLS0: forall o, osum vclash (block_get by' o) (block_get c o) <> None.
      { move=> o.
        move: (CELLS 0 o) => /=.
        by case: (block_get c o) => [w|]; case: (block_get by' o) => [w'|]. }
      case: (block_sum_some by' c CELLS0) => [b Eb].
      rewrite /op /= Eb Et.
      by eexists.
    + rewrite Et.
      by eexists.
  - have CELLS': forall bi o, osum vclash
        (match mem'_get xm bi with Some b => block_get b o | None => None end)
        (match mem'_get ym bi with Some b => block_get b o | None => None end)
      <> None
      by move=> bi o; exact: (CELLS (S bi) o).
    have ALC': to_tail' xm $+ to_tail' ym <> None.
    { move: ALC => /=.
      by case: (to_tail' xm) => [|j]; case: (to_tail' ym) => [|j']. }
    have DOMX': forall g, to_tail' xm = Owned g -> mem'_nblocks ym <= S g.
    { move=> g Eg.
      have := DOMX (S g).
      rewrite /= Eg /= => /(_ erefl).
      lia. }
    have DOMY': forall g, to_tail' ym = Owned g -> mem'_nblocks xm <= S g.
    { move=> g Eg.
      have := DOMY (S g).
      rewrite /= Eg /= => /(_ erefl).
      lia. }
    case: (IH ym CELLS' ALC' DOMX' DOMY') => [t Et].
    rewrite Et.
    case: ox CELLS {ALC DOMX DOMY CELLS' ALC' DOMX' DOMY'} => [c|] CELLS;
      case: oy CELLS => [d|] CELLS.
    + case: (block_sum_some c d (fun o => CELLS 0 o)) => [b Eb].
      rewrite /op /= Eb.
      by eexists.
    + by eexists.
    + by eexists.
    + by eexists.
Qed.

Lemma sum_defined_alloc (m1 m2: mem (excl nat)):
  ((forall bi o, osum vclash (get m1 bi o) (get m2 bi o) <> None)
   /\ to_tail m1 $+ to_tail m2 <> None
   /\ (forall B, to_tail m1 = Owned B -> nblocks m2 <= B)
   /\ (forall B, to_tail m2 = Owned B -> nblocks m1 <= B))
  <-> (exists m: mem (excl nat), mem_sum m1 m2 = Some m).
Proof.
  split.
  - move=> [CELLS [ALC [DOM1 DOM2]]].
    case: m1 CELLS ALC DOM1 DOM2 => [a1|m1] CELLS ALC DOM1 DOM2;
      case: m2 CELLS ALC DOM1 DOM2 => [a2|m2] CELLS ALC DOM1 DOM2 //=.
    + move: ALC; rewrite /op /=.
      case A: (excl_sum a1 a2) => [aa|] //= _.
      by eexists.
    + have PUSH: exists t, mem'_push_a a1 m2 = Some t.
      { case: a1 ALC DOM1 {CELLS DOM2} => [|g] ALC DOM1.
        - rewrite mem'_push_a_id.
          by eexists.
        - apply: mem'_push_a_some.
          + move: (DOM1 g erefl) => /=; lia.
          + move: ALC => /=.
            by case: (to_tail' m2) => [|j]. }
      case: PUSH => [t Et].
      rewrite Et.
      by eexists.
    + have PUSH: exists t, mem'_push_a a2 m1 = Some t.
      { case: a2 ALC DOM2 {CELLS DOM1} => [|g] ALC DOM2.
        - rewrite mem'_push_a_id.
          by eexists.
        - apply: mem'_push_a_some.
          + move: (DOM2 g erefl) => /=.
            lia.
          + move: ALC => /=.
            by case: (to_tail' m1) => [|j]. }
      case: PUSH => [t Et].
      rewrite Et.
      by eexists.
    + have ALC': to_tail' m1 $+ to_tail' m2 <> None.
      { move: ALC => /=.
        by case: (to_tail' m1) => [|j]; case: (to_tail' m2) => [|j']. }
      have DOM1': forall g, to_tail' m1 = Owned g -> mem'_nblocks m2 <= S g.
      { move=> g Eg.
        have := DOM1 (S g).
        rewrite /= Eg /= => /(_ erefl).
        by []. }
      have DOM2': forall g, to_tail' m2 = Owned g -> mem'_nblocks m1 <= S g.
      { move=> g Eg.
        have := DOM2 (S g).
        rewrite /= Eg /= => /(_ erefl).
        by []. }
      case: (mem'_sum_some m1 m2 (fun bi o => CELLS bi o) ALC' DOM1' DOM2')
        => [t Et].
      rewrite /op /= Et.
      by eexists.
  - move=> [m EQ].
    split; [|split; [|split]].
    + move=> bi o.
      by rewrite (sum_get m1 m2 m EQ bi o).
    + by rewrite (sum_to_tail m1 m2 m EQ).
    + move=> B AL1.
      have AL: to_tail m = Owned B.
      { move: (sum_to_tail m1 m2 m EQ).
        rewrite AL1.
        by case: (to_tail m2) => [|j] //= [<-]. }
      have GE := to_tail_nblocks_alloc m B AL.
      case LE: (Nat.leb (nblocks m2) B).
      * by move/Nat.leb_le in LE.
      * exfalso.
        have LT2: B < nblocks m2 by apply/Nat.leb_gt.
        have POS: 0 < nblocks m2 by lia.
        case: (mem_last_bound m2 POS) => [o [v Ev]].
        have LT: nblocks m <= Nat.pred (nblocks m2) by lia.
        move: (sum_get m1 m2 m EQ (Nat.pred (nblocks m2)) o).
        rewrite Ev (get_nblocks_ge m (Nat.pred (nblocks m2)) o LT).
        by case: (get m1 (Nat.pred (nblocks m2)) o) => [w|].
    + move=> B AL2.
      have AL: to_tail m = Owned B.
      { move: (sum_to_tail m1 m2 m EQ).
        rewrite AL2.
        by case: (to_tail m1) => [|j] //= [<-]. }
      have GE := to_tail_nblocks_alloc m B AL.
      case LE: (Nat.leb (nblocks m1) B).
      * by move/Nat.leb_le in LE.
      * exfalso.
        have LT2: B < nblocks m1 by apply/Nat.leb_gt.
        have POS: 0 < nblocks m1 by lia.
        case: (mem_last_bound m1 POS) => [o [v Ev]].
        have LT: nblocks m <= Nat.pred (nblocks m1) by lia.
        move: (sum_get m1 m2 m EQ (Nat.pred (nblocks m1)) o).
        rewrite Ev (get_nblocks_ge m (Nat.pred (nblocks m1)) o LT).
        by case: (get m2 (Nat.pred (nblocks m1)) o) => [w|].
Qed.

Definition mdiff_alloc (m2 m1: mem (excl nat)): mem (excl nat) :=
  match to_tail m1 with
  | Owned _ =>
      match m2 with
      | MEmpty _ => MEmpty Unowned
      | MLive m2' =>
          match (match m1 with
                 | MEmpty _ => MLive m2'
                 | MLive m1' => mem'_diff m2' m1'
                 end) with
          | MEmpty _ => MEmpty Unowned
          | MLive dm => MLive (mem'_unown dm)
          end
      end
  | Unowned =>
      match m2 with
      | MEmpty a2 => MEmpty a2
      | MLive m2' =>
          match m1 with
          | MEmpty _ => MLive m2'
          | MLive m1' => mem'_diff m2' m1'
          end
      end
  end.

Lemma mdiff_get_alloc (m2 m1: mem (excl nat)) (bi o: nat):
  get (mdiff_alloc m2 m1) bi o
  = match get m1 bi o with
    | Some _ => None
    | None => get m2 bi o
    end.
Proof.
  have CORE: forall (m2' m1': mem' (excl nat)),
      match mem'_diff m2' m1' with
      | MEmpty _ => None
      | MLive dm => match mem'_get dm bi with
                    | Some b => block_get b o
                    | None => None
                    end
      end
      = match get (MLive m1') bi o with
        | Some _ => None
        | None => get (MLive m2') bi o
        end.
  { move=> m2' m1'.
    move: (mem'_diff_get m2' m1' bi) => D.
    have ->: match mem'_diff m2' m1' with
             | MEmpty _ => None
             | MLive dm => match mem'_get dm bi with
                           | Some b => block_get b o
                           | None => None
                           end
             end
             = match (match mem'_diff m2' m1' with
                      | MEmpty _ => None
                      | MLive dm => mem'_get dm bi
                      end) with
               | Some b => block_get b o
               | None => None
               end
      by case: (mem'_diff m2' m1').
    rewrite D /=.
    case E2: (mem'_get m2' bi) => [b2|]; case E1: (mem'_get m1' bi) => [b1|] //=.
    - exact: (block_diff_get b2 b1 o).
    - by case: (block_get b1 o) => [w|]. }
  rewrite /mdiff_alloc.
  case AL: (to_tail m1) => [|B].
  - case: m2 => [a2|m2'].
    + by rewrite /=; case: (get m1 bi o) => [w|].
    + case: m1 AL => [a1|m1'] AL.
      * by [].
      * exact: (CORE m2' m1').
  - case: m2 => [a2|m2'].
    + by rewrite /=; case: (get m1 bi o) => [w|].
    + case: m1 AL => [a1|m1'] AL.
      * by rewrite /= mem'_unown_get.
      * move: (CORE m2' m1').
        case: (mem'_diff m2' m1') => [ad|dm] /= D.
        -- exact: D.
        -- rewrite mem'_unown_get.
           exact: D.
Qed.

Lemma to_tail_mdiff_alloc (m2 m1: mem (excl nat)):
  to_tail (mdiff_alloc m2 m1)
  = match to_tail m1 with
    | Owned _ => Unowned
    | Unowned => to_tail m2
    end.
Proof.
  rewrite /mdiff_alloc.
  case AL: (to_tail m1) => [|B].
  - case: m2 => [a2|m2'] //.
    case: m1 AL => [a1|m1'] AL //.
    exact: (mem'_diff_to_tail m2' m1').
  - case: m2 => [a2|m2'] //.
    case: m1 AL => [a1|m1'] AL.
    + by rewrite /= mem'_unown_to_tail.
    + case: (mem'_diff m2' m1') => [ad|dm] //=.
      by rewrite mem'_unown_to_tail.
Qed.

Lemma sum_complement_alloc (m1 m2: mem (excl nat))
  (INCL: forall bi o v, get m1 bi o = Some v -> get m2 bi o = Some v)
  (ALC: to_tail m1 = Unowned \/ to_tail m1 = to_tail m2):
  mem_sum m1 (mdiff_alloc m2 m1) = Some m2.
Proof.
  have CELLS: forall bi o, osum vclash (get m1 bi o) (get (mdiff_alloc m2 m1) bi o) <> None.
  { move=> bi o.
    by rewrite mdiff_get_alloc; case: (get m1 bi o) => [v|]. }
  have ALC2: to_tail m1 $+ to_tail (mdiff_alloc m2 m1) <> None.
  { rewrite to_tail_mdiff_alloc.
    by case: (to_tail m1) => [|B]. }
  have NB1: forall p o v B, get m1 p o = Some v -> to_tail m2 = Owned B -> p < B.
  { move=> p o v B E A2.
    have E2 := INCL p o v E.
    have GE := to_tail_nblocks_alloc m2 B A2.
    case LT: (Nat.ltb p B); first by move/Nat.ltb_lt in LT.
    exfalso.
    move/Nat.ltb_ge in LT.
    have GEp: nblocks m2 <= p by lia.
    by rewrite (get_nblocks_ge m2 p o GEp) in E2. }
  have NBD: forall p o v B, get (mdiff_alloc m2 m1) p o = Some v
            -> to_tail m2 = Owned B -> p < B.
  { move=> p o v B E A2.
    move: E; rewrite mdiff_get_alloc.
    case E1: (get m1 p o) => [w|] // E2.
    have GE := to_tail_nblocks_alloc m2 B A2.
    case LT: (Nat.ltb p B); first by move/Nat.ltb_lt in LT.
    exfalso.
    move/Nat.ltb_ge in LT.
    have GEp: nblocks m2 <= p by lia.
    by rewrite (get_nblocks_ge m2 p o GEp) in E2. }
  have DOM1: forall B, to_tail m1 = Owned B -> nblocks (mdiff_alloc m2 m1) <= B.
  { move=> B A1.
    have A2: to_tail m2 = Owned B.
    { case: ALC => [E|E].
      - by rewrite E in A1.
      - by rewrite -E A1. }
    case NBD0: (nblocks (mdiff_alloc m2 m1)) => [|k]; first by lia.
    have POS: 0 < nblocks (mdiff_alloc m2 m1) by rewrite NBD0; lia.
    case: (mem_last_bound (mdiff_alloc m2 m1) POS) => [o [v Ev]].
    have LT := NBD (Nat.pred (nblocks (mdiff_alloc m2 m1))) o v B Ev A2.
    rewrite NBD0 in LT.
    lia. }
  have DOMD: forall B, to_tail (mdiff_alloc m2 m1) = Owned B -> nblocks m1 <= B.
  { move=> B AD.
    have A2: to_tail m2 = Owned B.
    { move: AD; rewrite to_tail_mdiff_alloc.
      case: (to_tail m1) => [|C].
      - by [].
      - by move=> AD'; discriminate AD'. }
    case NB0: (nblocks m1) => [|k]; first by lia.
    have POS: 0 < nblocks m1 by rewrite NB0; lia.
    case: (mem_last_bound m1 POS) => [o [v Ev]].
    have LT := NB1 (Nat.pred (nblocks m1)) o v B Ev A2.
    rewrite NB0 in LT.
    lia. }
  case: (proj1 (sum_defined_alloc m1 (mdiff_alloc m2 m1))
           (conj CELLS (conj ALC2 (conj DOM1 DOMD)))) => [m EQ].
  have Em: m = m2.
  { apply: ext_tail.
    - move=> bi o.
      move: (sum_get m1 (mdiff_alloc m2 m1) m EQ bi o).
      rewrite mdiff_get_alloc.
      case E1: (get m1 bi o) => [v|] /=.
      + move=> [<-].
        by rewrite (INCL bi o v E1).
      + by move=> [<-].
    - move: (sum_to_tail m1 (mdiff_alloc m2 m1) m EQ).
      rewrite to_tail_mdiff_alloc.
      case A1: (to_tail m1) => [|B] /=.
      + by move=> [<-].
      + move=> [<-].
        case: ALC => [E|E].
        * by rewrite E in A1.
        * by rewrite -E A1. }
  by rewrite EQ Em.
Qed.

Section InclusionAlloc.

  Context (veqb: value Pointer.t -> value Pointer.t -> bool)
          (veqb_spec: forall x y, Bool.reflect (x = y) (veqb x y)).

  Definition incl_alloc (m1 m2: mem (excl nat)): bool :=
    ((match m1 with
      | MEmpty _ => true
      | MLive m1' => match m2 with
                     | MEmpty _ => false
                     | MLive m2' => mem'_incl veqb m1' m2'
                     end
      end)
     && (match to_tail m1 with
         | Unowned => true
         | Owned B1 => match to_tail m2 with
                       | Owned B2 => Nat.eqb B1 B2
                       | Unowned => false
                       end
         end))%bool.

  Lemma incl_spec_alloc (m1 m2: mem (excl nat)):
    Bool.reflect
      ((forall bi o v, get m1 bi o = Some v -> get m2 bi o = Some v)
       /\ (to_tail m1 = Unowned \/ to_tail m1 = to_tail m2))
      (incl_alloc m1 m2).
  Proof.
    rewrite /incl_alloc.
    have RC: Bool.reflect
               (forall bi o v, get m1 bi o = Some v -> get m2 bi o = Some v)
               (match m1 with
                | MEmpty _ => true
                | MLive m1' => match m2 with
                               | MEmpty _ => false
                               | MLive m2' => mem'_incl veqb m1' m2'
                               end
                end).
    { case: m1 => [a1|m1'].
      - by constructor.
      - case: m2 => [a2|m2'].
        + constructor => H.
          case: (mem'_get_nonempty m1') => [bi [b E]].
          case: (block_get_nonempty b) => [o [v E']].
          have E'': get (MLive m1') bi o = Some v by rewrite /= E.
          by move: (H bi o v E'').
        + case: (mem'_incl_spec veqb veqb_spec m1' m2') => [I|N]; constructor.
          * move=> bi o v E.
            exact: (I bi o v E).
          * move=> H; apply: N => bi o v E.
            exact: (H bi o v E). }
    have RA: Bool.reflect
               (to_tail m1 = Unowned \/ to_tail m1 = to_tail m2)
               (match to_tail m1 with
                | Unowned => true
                | Owned B1 => match to_tail m2 with
                              | Owned B2 => Nat.eqb B1 B2
                              | Unowned => false
                              end
                end).
    { case A1: (to_tail m1) => [|B1].
      - by constructor; left.
      - case A2: (to_tail m2) => [|B2].
        + constructor => -[E|E]; by discriminate E.
        + case: (Nat.eqb_spec B1 B2) => [->|NE]; constructor.
          * by right.
          * move=> [E|E]; first by discriminate E.
            case: E => E'.
            exact: (NE E'). }
    case: RC => [PC|NC]; case: RA => [PA|NA] /=; constructor.
    - by split.
    - by move=> [_ P].
    - by move=> [P _].
    - by move=> [P _].
  Qed.

  Lemma incl_sum_spec_alloc (m1 m2: mem (excl nat)):
    Bool.reflect (exists m3, mem_sum m1 m3 = Some m2) (incl_alloc m1 m2).
  Proof.
    case: (incl_spec_alloc m1 m2) => [[PC PA]|N]; constructor.
    - exists (mdiff_alloc m2 m1).
      exact: (sum_complement_alloc m1 m2 PC PA).
    - move=> [m3 E].
      apply: N.
      split.
      + move=> bi o v E1.
        move: (sum_get m1 m3 m2 E bi o).
        rewrite E1.
        case E3: (get m3 bi o) => [w|] /=.
        * by move=> E2; discriminate E2.
        * by move=> [<-].
      + move: (sum_to_tail m1 m3 m2 E).
        case A1: (to_tail m1) => [|B1] /=.
        * by left.
        * case A3: (to_tail m3) => [|B3] /=.
          -- move=> [E2].
             by right; rewrite E2.
          -- by move=> E2; discriminate E2.
  Qed.

End InclusionAlloc.

Lemma unit_tail_eq: forall a b: unit, a = b.
Proof.
  by case; case.
Qed.

Lemma ext_noalloc (m1 m2: mem unit)
  (EXT: forall bi o, get m1 bi o = get m2 bi o): m1 = m2.
Proof.
  apply: (ext_tail m1 m2 EXT).
  exact: unit_tail_eq.
Qed.

Lemma sum_defined_noalloc (m1 m2: mem unit):
  (forall bi o, osum vclash (get m1 bi o) (get m2 bi o) <> None)
  <-> (exists m, mem_sum m1 m2 = Some m).
Proof.
  split.
  - move=> CELLS.
    exact: (mem_sum_some_total unit_rshift_total unit_op_total m1 m2 CELLS).
  - move=> [m EQ] bi o.
    by rewrite (sum_get m1 m2 m EQ bi o).
Qed.

Lemma sum_one_fresh_at_noalloc (m: mem unit) (k o: nat) (v: value Pointer.t)
  (FRESH: forall o', get m k o' = None):
  exists m', mem_sum m (one_at k o v) = Some m'.
Proof.
  apply: (proj1 (sum_defined_noalloc m (one_at k o v))).
  move=> bi o'.
  rewrite get_one_at.
  case Ebi: (Nat.eqb bi k).
  - move/Nat.eqb_eq in Ebi; subst bi.
    rewrite (FRESH o') /=.
    by case: (Nat.eqb o' o).
  - by rewrite /= osum_None_r.
Qed.

Definition mdiff_noalloc (m2 m1: mem unit): mem unit :=
  match m2 with
  | MEmpty a2 => MEmpty a2
  | MLive m2' =>
      match m1 with
      | MEmpty _ => MLive m2'
      | MLive m1' => mem'_diff m2' m1'
      end
  end.

Lemma mdiff_get_noalloc (m2 m1: mem unit) (bi o: nat):
  get (mdiff_noalloc m2 m1) bi o
  = match get m1 bi o with
    | Some _ => None
    | None => get m2 bi o
    end.
Proof.
  case: m2 => [a2|m2'] /=.
  - by case: (get m1 bi o) => [w|].
  - case: m1 => [a1|m1'] //=.
    move: (mem'_diff_get m2' m1' bi) => D.
    have ->: get (mem'_diff m2' m1') bi o
             = match (match mem'_diff m2' m1' with
                      | MEmpty _ => None
                      | MLive dm => mem'_get dm bi
                      end) with
               | Some b => block_get b o
               | None => None
               end
      by case: (mem'_diff m2' m1').
    rewrite D /=.
    case E2: (mem'_get m2' bi) => [b2|]; case E1: (mem'_get m1' bi) => [b1|] //=.
    + exact: (block_diff_get b2 b1 o).
    + by case: (block_get b1 o) => [w|].
Qed.

Lemma sum_complement_noalloc (m1 m2: mem unit)
  (INCL: forall bi o v, get m1 bi o = Some v -> get m2 bi o = Some v):
  mem_sum m1 (mdiff_noalloc m2 m1) = Some m2.
Proof.
  have CELLS: forall bi o, osum vclash (get m1 bi o) (get (mdiff_noalloc m2 m1) bi o) <> None.
  { move=> bi o.
    by rewrite mdiff_get_noalloc; case: (get m1 bi o) => [v|]. }
  case: (proj1 (sum_defined_noalloc m1 (mdiff_noalloc m2 m1)) CELLS) => [m EQ].
  have Em: m = m2.
  { apply: ext_noalloc => bi o.
    move: (sum_get m1 (mdiff_noalloc m2 m1) m EQ bi o).
    rewrite mdiff_get_noalloc.
    case E1: (get m1 bi o) => [v|] /=.
    + move=> [<-].
      by rewrite (INCL bi o v E1).
    + by move=> [<-]. }
  by rewrite EQ Em.
Qed.

Section InclusionNoAlloc.

  Context (veqb: value Pointer.t -> value Pointer.t -> bool)
          (veqb_spec: forall x y, Bool.reflect (x = y) (veqb x y)).

  Definition incl_noalloc (m1 m2: mem unit): bool :=
    match m1 with
    | MEmpty _ => true
    | MLive m1' => match m2 with
                   | MEmpty _ => false
                   | MLive m2' => mem'_incl veqb m1' m2'
                   end
    end.

  Lemma incl_spec_noalloc (m1 m2: mem unit):
    Bool.reflect
      (forall bi o v, get m1 bi o = Some v -> get m2 bi o = Some v)
      (incl_noalloc m1 m2).
  Proof.
    rewrite /incl_noalloc.
    case: m1 => [a1|m1'].
    - by constructor.
    - case: m2 => [a2|m2'].
      + constructor => H.
        case: (mem'_get_nonempty m1') => [bi [b E]].
        case: (block_get_nonempty b) => [o [v E']].
        have E'': get (MLive m1') bi o = Some v by rewrite /= E E'.
        by move: (H bi o v E'').
      + case: (mem'_incl_spec veqb veqb_spec m1' m2') => [I|N]; constructor.
        * move=> bi o v E.
          exact: (I bi o v E).
        * move=> H; apply: N => bi o v E.
          exact: (H bi o v E).
  Qed.

  Lemma incl_sum_spec_noalloc (m1 m2: mem unit):
    Bool.reflect (exists m3, mem_sum m1 m3 = Some m2) (incl_noalloc m1 m2).
  Proof.
    case: (incl_spec_noalloc m1 m2) => [PC|N]; constructor.
    - exists (mdiff_noalloc m2 m1).
      exact: (sum_complement_noalloc m1 m2 PC).
    - move=> [m3 E].
      apply: N => bi o v E1.
      move: (sum_get m1 m3 m2 E bi o).
      rewrite E1.
      case E3: (get m3 bi o) => [w|] /=.
      + by move=> E2; discriminate E2.
      + by move=> [<-].
  Qed.

End InclusionNoAlloc.

Section AddrInterfaceNoAlloc.

  Context {Ad: Addr.type}.

  Lemma aext_noalloc (m1 m2: mem unit)
    (EXT: forall a: Ad, aget m1 a = aget m2 a): m1 = m2.
  Proof.
    apply: (aext_tail m1 m2 EXT).
    exact: unit_tail_eq.
  Qed.

End AddrInterfaceNoAlloc.

Lemma sub_noalloc (m1 m2: mem unit):
  m1 $<= m2 <-> (forall bi o v, get m1 bi o = Some v -> get m2 bi o = Some v).
Proof.
  split.
  - move=> [m3 E] bi o v G1.
    have E': mem_sum m1 m3 = Some m2 := E.
    have G := sum_get _ _ _ E' bi o.
    rewrite G1 in G.
    case G3: (get m3 bi o) => [v3|]; rewrite G3 /= in G.
    + by [].
    + by inversion G.
  - move=> H.
    exists (mdiff_noalloc m2 m1).
    exact: (sum_complement_noalloc m1 m2 H).
Qed.

Lemma aone_sub_noalloc (a: Addr.t) (v: value Pointer.t) (m: mem unit):
  aone a v $<= m <-> aget m a = Some v.
Proof.
  rewrite sub_noalloc.
  split.
  - move=> H.
    apply: (H (Imp.Addr.block a) (N.to_nat (offset a)) v).
    exact: (aget_aone_eq a v).
  - move=> G bi o v' G1.
    have G2: get (one_at (A:=unit) (Imp.Addr.block a) (N.to_nat (offset a)) v) bi o = Some v'
      by exact: G1.
    rewrite get_one_at in G2.
    case Eb: (Nat.eqb bi (Imp.Addr.block a)); rewrite Eb /= in G2; last by [].
    case Eo: (Nat.eqb o (N.to_nat (offset a))); rewrite Eo /= in G2; last by [].
    inversion G2; subst v'.
    move: Eb Eo => /Nat.eqb_eq -> /Nat.eqb_eq ->.
    exact: G.
Qed.

(* Freshness of a block, as bindings *)
Lemma block_fresh_iff: forall (mm: mem unit) (bid: nat),
    (forall (o: N) (v': value Pointer.t), ~ (aone ((mkAddr bid o): Addr.t) v' $<= mm))
    <-> block_vacant mm bid = true.
Proof.
  move=> mm bid.
  split.
  - move=> H.
    case: (block_vacant_spec mm bid) => [V|NV] //.
    exfalso; apply: NV.
    move=> o v E.
    apply: (H (N.of_nat o) v).
    apply: (proj2 (aone_sub_noalloc _ v mm)).
    have AG: aget mm ((mkAddr bid (N.of_nat o)): Addr.t) = get mm bid o.
    { by rewrite /aget mkAddr_block mkAddr_offset Nat2N.id. }
    by rewrite AG.
  - move=> V o v' SUB.
    case: (block_vacant_spec mm bid) V => [NB|NV] V; last by [].
    have G := proj1 (aone_sub_noalloc _ v' mm) SUB.
    have G2: get mm (Imp.Addr.block ((mkAddr bid o): Addr.t))
               (N.to_nat (offset ((mkAddr bid o): Addr.t))) = Some v'
      by exact: G.
    rewrite mkAddr_block mkAddr_offset in G2.
    exact: (NB (N.to_nat o) v' G2).
Qed.

Lemma one_similar_noalloc: forall (a: Addr.t) (v: value Pointer.t) (m: mem unit),
    (exists v', aone a v' $<= m) <-> (aone a v) $+ m = None.
Proof.
  move=> a v mm.
  split.
  - move=> [v' SUB].
    have G := proj1 (aone_sub_noalloc a v' mm) SUB.
    have N: mem_sum (aone a v) mm = None.
    { case Em: (mem_sum (aone a v) mm) => [ms|] //.
      have S := sum_get _ _ _ Em (Imp.Addr.block a) (N.to_nat (offset a)).
      have C1: get (aone (A:=unit) a v) (Imp.Addr.block a) (N.to_nat (offset a)) = Some v
        by exact: (aget_aone_eq a v).
      have C2: get mm (Imp.Addr.block a) (N.to_nat (offset a)) = Some v' by exact: G.
      by rewrite C1 C2 /= in S. }
    exact: N.
  - move=> E.
    have E2: mem_sum (aone a v) mm = None by exact: E.
    case Ea: (get mm (Imp.Addr.block a) (N.to_nat (offset a))) => [v'|].
    + exists v'.
      apply: (proj2 (aone_sub_noalloc a v' mm)).
      exact: Ea.
    + exfalso.
      have [ms' Em']: exists m, mem_sum (aone a v) mm = Some m.
      { apply: (proj1 (sum_defined_noalloc (aone a v) mm)).
        move=> bi o.
        have C: get (aone (A:=unit) a v) bi o
                = if (Nat.eqb bi (Imp.Addr.block a) && Nat.eqb o (N.to_nat (offset a)))%bool
                  then Some v else None
          by exact: (get_one_at (Imp.Addr.block a) (N.to_nat (offset a)) v bi o).
        rewrite C.
        case Eb: (Nat.eqb bi (Imp.Addr.block a)) => /=; last by [].
        case Eo: (Nat.eqb o (N.to_nat (offset a))) => /=; last by [].
        move: Eb Eo => /Nat.eqb_eq -> /Nat.eqb_eq ->.
        by rewrite Ea. }
      by rewrite Em' in E2.
Qed.

Lemma one_min_noalloc: forall (m: mem unit) (a: Addr.t) (v: value Pointer.t),
    m $<= aone a v -> m = $0 \/ m = aone a v.
Proof.
  move=> mm a v SUB.
  have SUB2 := proj1 (sub_noalloc mm (aone a v)) SUB.
  case Ea: (aget mm a) => [v0|].
  - right.
    have Ev: (Some v: option (value Pointer.t)) = Some v0.
    { rewrite -(aget_aone_eq (A:=unit) a v).
      apply: (SUB2 (Imp.Addr.block a) (N.to_nat (offset a)) v0).
      exact: Ea. }
    injection Ev as Ev; subst v0.
    have EXT: forall a': Addr.t, aget mm a' = aget (aone (A:=unit) a v) a'.
    { move=> a'.
      case Ea': (aget mm a') => [v'|].
      + have G := SUB2 (Imp.Addr.block a') (N.to_nat (offset a')) v' Ea'.
        have G2: aget (aone (A:=unit) a v) a' = Some v' by exact: G.
        by rewrite G2.
      + case Eb: (Nat.eqb (Imp.Addr.block a') (Imp.Addr.block a)).
        * case Eo: (Nat.eqb (N.to_nat (offset a')) (N.to_nat (offset a))).
          -- exfalso.
             have EQa := aindex_eq a a' Eb Eo; subst a'.
             congruence.
          -- by rewrite aget_aone Eb Eo.
        * by rewrite aget_aone Eb. }
    exact: (aext_noalloc mm (aone a v) EXT).
  - left.
    have EXT: forall a': Addr.t, aget mm a' = aget (MEmpty tt) a'.
    { move=> a'.
      case Ea': (aget mm a') => [v'|]; last by [].
      exfalso.
      have G := SUB2 (Imp.Addr.block a') (N.to_nat (offset a')) v' Ea'.
      have G2: aget (aone (A:=unit) a v) a' = Some v' by exact: G.
      rewrite aget_aone in G2.
      case Eb: (Nat.eqb (Imp.Addr.block a') (Imp.Addr.block a)); rewrite Eb /= in G2; last by [].
      case Eo: (Nat.eqb (N.to_nat (offset a')) (N.to_nat (offset a)));
        rewrite Eo /= in G2; last by [].
      have EQa := aindex_eq a a' Eb Eo; subst a'.
      congruence. }
    exact: (aext_noalloc mm (MEmpty tt) EXT).
Qed.

Lemma one_discriminate_noalloc: forall (m: mem unit) (a: Addr.t) (v: value Pointer.t)
    (m': mem unit)
    (EQ: aone a v $+ m = Some m')
    (a': Addr.t) (v': value Pointer.t)
    (SUB: aone a' v' $<= m'),
    (a' = a /\ v' = v) \/ (a' <> a /\ aone a' v' $<= m).
Proof.
  move=> mm a v mm' EQ a' v' SUB.
  have Em: mem_sum (aone a v) mm = Some mm' by exact: EQ.
  have G := proj1 (aone_sub_noalloc a' v' mm') SUB.
  have S := sum_get _ _ _ Em (Imp.Addr.block a') (N.to_nat (offset a')).
  have G2: get mm' (Imp.Addr.block a') (N.to_nat (offset a')) = Some v' by exact: G.
  rewrite G2 in S.
  have C: get (aone (A:=unit) a v) (Imp.Addr.block a') (N.to_nat (offset a'))
          = if (Nat.eqb (Imp.Addr.block a') (Imp.Addr.block a)
                && Nat.eqb (N.to_nat (offset a')) (N.to_nat (offset a)))%bool
            then Some v else None
    by exact: (aget_aone a v a').
  case Eb: (Nat.eqb (Imp.Addr.block a') (Imp.Addr.block a)).
  - case Eo: (Nat.eqb (N.to_nat (offset a')) (N.to_nat (offset a))).
    + left.
      rewrite C Eb Eo /= in S.
      case Emm: (get mm (Imp.Addr.block a') (N.to_nat (offset a'))) => [w|];
        rewrite Emm /= in S; first by [].
      injection S as S2.
      subst v'.
      split; [ exact: (aindex_eq a a' Eb Eo) | by [] ].
    + right.
      have NE: a' <> a.
      { move=> EQa; subst a'. by rewrite Nat.eqb_refl in Eo. }
      split; [ exact: NE | ].
      rewrite C Eb Eo /= in S.
      injection S as S2.
      apply: (proj2 (aone_sub_noalloc a' v' mm)).
      exact: S2.
  - right.
    have NE: a' <> a.
    { move=> EQa; subst a'. by rewrite Nat.eqb_refl in Eb. }
    split; [ exact: NE | ].
    rewrite C Eb /= in S.
    injection S as S2.
    apply: (proj2 (aone_sub_noalloc a' v' mm)).
    exact: S2.
Qed.

Lemma mem_sep_noalloc: forall (m1 m2: mem unit)
    (ONES: forall (a1 a2: Addr.t) (v1 v2: value Pointer.t)
                  (SUB1: aone a1 v1 $<= m1)
                  (SUB2: aone a2 v2 $<= m2),
        aone (A:=unit) a1 v1 $/= aone a2 v2),
    m1 $/= m2.
Proof.
  move=> mm1 mm2 ONES.
  have [m Em]: exists m, mem_sum mm1 mm2 = Some m.
  { apply: (proj1 (sum_defined_noalloc mm1 mm2)).
    move=> bi o.
    case E1: (get mm1 bi o) => [v1|]; last by [].
    case E2: (get mm2 bi o) => [v2|]; last by [].
    exfalso.
    pose a := ((mkAddr bi (N.of_nat o)): Addr.t).
    have AG1: aget mm1 a = get mm1 bi o.
    { by rewrite /aget /a mkAddr_block mkAddr_offset Nat2N.id. }
    have AG2: aget mm2 a = get mm2 bi o.
    { by rewrite /aget /a mkAddr_block mkAddr_offset Nat2N.id. }
    have SUB1: aone a v1 $<= mm1.
    { apply: (proj2 (aone_sub_noalloc a v1 mm1)). by rewrite AG1 E1. }
    have SUB2: aone a v2 $<= mm2.
    { apply: (proj2 (aone_sub_noalloc a v2 mm2)). by rewrite AG2 E2. }
    case: (ONES a a v1 v2 SUB1 SUB2) => [mc Ec].
    have Ems: mem_sum (aone a v1) (aone a v2) = Some mc by exact: Ec.
    have S := sum_get _ _ _ Ems (Imp.Addr.block a) (N.to_nat (offset a)).
    have C1: get (aone (A:=unit) a v1) (Imp.Addr.block a) (N.to_nat (offset a)) = Some v1
      by exact: (aget_aone_eq a v1).
    have C2: get (aone (A:=unit) a v2) (Imp.Addr.block a) (N.to_nat (offset a)) = Some v2
      by exact: (aget_aone_eq a v2).
    by rewrite C1 C2 /= in S. }
  exists m.
  exact: Em.
Qed.

Lemma mem_ext_noalloc: forall (m1 m2: mem unit),
    (forall (a: Addr.t) (v: value Pointer.t), aone a v $<= m1 <-> aone a v $<= m2) -> m1 = m2.
Proof.
  move=> mm1 mm2 H.
  have EXT: forall a: Addr.t, aget mm1 a = aget mm2 a.
  { move=> a.
    case E1: (aget mm1 a) => [v|].
    - symmetry.
      apply: (proj1 (aone_sub_noalloc a v mm2)).
      apply: (proj1 (H a v)).
      apply: (proj2 (aone_sub_noalloc a v mm1)).
      exact: E1.
    - case E2: (aget mm2 a) => [v|]; last by [].
      exfalso.
      have G := proj1 (aone_sub_noalloc a v mm1)
                  (proj2 (H a v) (proj2 (aone_sub_noalloc a v mm2) E2)).
      congruence. }
  exact: (aext_noalloc mm1 mm2 EXT).
Qed.

HB.instance Definition _ :=
  isMemory.Build Addr.t (value Pointer.t) (mem unit)
    (aone (A:=unit) (Ad:=Addr.t))
    one_similar_noalloc
    one_min_noalloc
    one_discriminate_noalloc
    mem_sep_noalloc
    mem_ext_noalloc.

Definition subb_noalloc (m1 m2: mem unit): bool :=
  incl_noalloc (value_eqb Pointer.t) m1 m2.

Lemma subb_spec_noalloc (m1 m2: mem unit): reflect (m1 $<= m2) (subb_noalloc m1 m2).
Proof.
  rewrite /subb_noalloc.
  case: (incl_sum_spec_noalloc (value_eqb Pointer.t) (value_eqb_spec Pointer.t) m1 m2)
    => [I|N]; constructor.
  - case: I => [m3 E].
    by exists m3.
  - move=> [m3 E].
    apply: N.
    by exists m3.
Qed.

HB.instance Definition _ :=
  isDecRel.Build (mem unit) (@Substate (mem unit)) subb_noalloc subb_spec_noalloc.

Lemma mem_read_iff_noalloc (m: mem unit) (r: Pointer.t) (v: value Pointer.t):
  (exists a, References r a /\ Allows r Operation.Read /\ aone a v $<= m)
  <-> mem_read m r = Some v.
Proof.
  split.
  - move=> [a [REF [ALW SUB]]].
    rewrite /mem_read REF ALW.
    exact: (proj1 (aone_sub_noalloc a v m) SUB).
  - rewrite /mem_read.
    case REF: (ref_addr r) => [a|] //.
    case ALW: (allows r Operation.Read) => //.
    move=> E.
    exists a.
    split; [ by [] | ].
    split; [ by [] | ].
    apply: (proj2 (aone_sub_noalloc a v m)).
    exact: E.
Qed.

Lemma mem_mutate_some_iff_noalloc (m: mem unit) (r: Pointer.t) (v: value Pointer.t):
  (exists a v0, References r a /\ Allows r Operation.Write /\ aone a v0 $<= m)
  <-> (exists m', mem_mutate m r v = Some m').
Proof.
  split.
  - move=> [a [v0 [REF [ALW SUB]]]].
    rewrite /mem_mutate REF ALW.
    have G := proj1 (aone_sub_noalloc a v0 m) SUB.
    apply: (proj1 (set_defined m (Imp.Addr.block a) (N.to_nat (offset a)) v)).
    by exists v0.
  - move=> [m' E].
    move: E; rewrite /mem_mutate.
    case REF: (ref_addr r) => [a|] //.
    case ALW: (allows r Operation.Write) => //.
    move=> E.
    have [v0 G]: exists v0, get m (Imp.Addr.block a) (N.to_nat (offset a)) = Some v0.
    { apply: (proj2 (set_defined m (Imp.Addr.block a) (N.to_nat (offset a)) v)).
      by exists m'. }
    exists a, v0.
    split; [ by [] | ].
    split; [ by [] | ].
    apply: (proj2 (aone_sub_noalloc a v0 m)).
    exact: G.
Qed.

Lemma mem_mutate_mem_iff_noalloc (m: mem unit) (r: Pointer.t) (v: value Pointer.t)
  (m': mem unit) (a: Addr.t)
  (REF: References r a)
  (EQ: mem_mutate m r v = Some m')
  (a': Addr.t) (v': value Pointer.t):
  aone a' v' $<= m' <-> ((a' = a /\ v' = v) \/ (a' <> a /\ aone a' v' $<= m)).
Proof.
  rewrite /mem_mutate REF in EQ.
  case ALW: (allows r Operation.Write); rewrite ALW /= in EQ; last by [].
  have SG := set_get _ _ _ _ _ EQ.
  split.
  - move=> SUB.
    have G := proj1 (aone_sub_noalloc a' v' m') SUB.
    have G2: get m' (Imp.Addr.block a') (N.to_nat (offset a')) = Some v' by exact: G.
    rewrite (SG (Imp.Addr.block a') (N.to_nat (offset a'))) in G2.
    case Eb: (Nat.eqb (Imp.Addr.block a') (Imp.Addr.block a)).
    + case Eo: (Nat.eqb (N.to_nat (offset a')) (N.to_nat (offset a))).
      * left.
        rewrite Eb Eo /= in G2.
        injection G2 as G2.
        subst v'.
        split; [ exact: (aindex_eq a a' Eb Eo) | by [] ].
      * right.
        have NE: a' <> a.
        { move=> EQa; subst a'. by rewrite Nat.eqb_refl in Eo. }
        split; [ exact: NE | ].
        apply: (proj2 (aone_sub_noalloc a' v' m)).
        rewrite Eb Eo /= in G2.
        exact: G2.
    + right.
      have NE: a' <> a.
      { move=> EQa; subst a'. by rewrite Nat.eqb_refl in Eb. }
      split; [ exact: NE | ].
      apply: (proj2 (aone_sub_noalloc a' v' m)).
      rewrite Eb /= in G2.
      exact: G2.
  - move=> [[-> ->] | [NE SUB]].
    + apply: (proj2 (aone_sub_noalloc a v m')).
      have G: get m' (Imp.Addr.block a) (N.to_nat (offset a)) = Some v.
      { by rewrite (SG (Imp.Addr.block a) (N.to_nat (offset a))) !Nat.eqb_refl. }
      exact: G.
    + apply: (proj2 (aone_sub_noalloc a' v' m')).
      have G := proj1 (aone_sub_noalloc a' v' m) SUB.
      have G2: get m (Imp.Addr.block a') (N.to_nat (offset a')) = Some v' by exact: G.
      have G3: get m' (Imp.Addr.block a') (N.to_nat (offset a')) = Some v'.
      { rewrite (SG (Imp.Addr.block a') (N.to_nat (offset a'))) (aindex_neq a a' NE).
        exact: G2. }
      exact: G3.
Qed.

HB.instance Definition _ :=
  isRWMemory.Build Addr.t Pointer.t (value Pointer.t) (mem unit)
    (mem_read (A:=unit) (Ad:=Addr.t) (Nm:=Pointer.t))
    (mem_mutate (A:=unit) (Ad:=Addr.t) (Nm:=Pointer.t))
    mem_read_iff_noalloc
    mem_mutate_some_iff_noalloc
    mem_mutate_mem_iff_noalloc.

Lemma bbound_ub_noalloc (m: mem unit) (a: Addr.t) (v: value Pointer.t)
  (SUB: aone a v $<= m): Imp.Addr.block a < nblocks m.
Proof.
  have S := proj1 (aone_sub_noalloc a v m) SUB.
  rewrite /aget in S.
  case: (Nat.le_gt_cases (nblocks m) (Imp.Addr.block a)) => [GE|LT]; last by exact: LT.
  by rewrite (get_nblocks_ge m (Imp.Addr.block a) (N.to_nat (offset a)) GE) in S.
Qed.

Lemma bbound_tight_noalloc (m: mem unit):
  nblocks m = 0
  \/ exists (a: Addr.t) (v: value Pointer.t),
      aone a v $<= m /\ S (Imp.Addr.block a) = nblocks m.
Proof.
  case: (Nat.eq_dec (nblocks m) 0) => [Z|NZ]; [ by left | right ].
  case: (mem_last_bound m ltac:(lia)) => [o [v EGET]].
  exists (mkAddr (Nat.pred (nblocks m)) (N.of_nat o): Addr.t), v.
  have EBLK: Imp.Addr.block (mkAddr (Nat.pred (nblocks m)) (N.of_nat o): Addr.t)
             = Nat.pred (nblocks m) by apply: mkAddr_block.
  have EOFS: N.to_nat (offset (mkAddr (Nat.pred (nblocks m)) (N.of_nat o): Addr.t)) = o
    by rewrite mkAddr_offset; apply: Nat2N.id.
  split; [ | rewrite EBLK; lia ].
  apply: (proj2 (aone_sub_noalloc _ v m)).
  rewrite /aget EBLK EOFS.
  exact: EGET.
Qed.

HB.instance Definition _ :=
  hasBlockBound.Build Addr.t (value Pointer.t) (mem unit)
    (nblocks (A:=unit))
    bbound_ub_noalloc
    bbound_tight_noalloc.

Definition to_mem (m: mem (excl nat)): mem unit :=
  mem_map (fun _ => tt) m.

Lemma get_to_mem (m: mem (excl nat)) (bi o: nat): get (to_mem m) bi o = get m bi o.
Proof.
  exact: get_map.
Qed.

Lemma to_mem_sum (x y z: mem (excl nat)) (EQ: mem_sum x y = Some z):
  mem_sum (to_mem x) (to_mem y) = Some (to_mem z).
Proof.
  have CELLS: forall bi o, osum vclash (get (to_mem x) bi o) (get (to_mem y) bi o) <> None.
  { move=> bi o.
    rewrite !get_to_mem.
    by rewrite (sum_get x y z EQ bi o). }
  case: (proj1 (sum_defined_noalloc (to_mem x) (to_mem y)) CELLS) => [u EU].
  rewrite EU.
  congr Some.
  apply: ext_noalloc => bi o.
  move: (sum_get (to_mem x) (to_mem y) u EU bi o).
  rewrite !get_to_mem (sum_get x y z EQ bi o).
  by move=> [->].
Qed.
