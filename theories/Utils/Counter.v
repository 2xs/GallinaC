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

From Stdlib Require Import Arith.

From GallinaC.Utils Require Import Algebra OptionExt.
From GallinaC.Utils Require Export Excl.

Local Open Scope separation_scope.

(** Counters
    A counter is a source of fresh identifiers.

    [cget C] gets the counter's current value.
    It may fail (return [None]), indicating that the counter is exhausted.

    [cnext] advances the counter to the next value.
    The concrete next value is not specified. Instead, is just guaranteed that the new value is strictly greater than the previous one.

    [mk_cnt n b] constructs a counter starting at [n].
    The budget [b] set to [None] indicates an infinite counter.
    A budget set to [Some b] indicates a counter able to produce at least [b] values, potentially more.
 *)
HB.mixin Record isCounter T := {
  cget: T -> option nat;
  cnext: T -> T;
  mk_cnt: nat -> option nat -> T;
  cnext_lt: forall (t: T) (i0 i1: nat)
                   (EQ0: cget t = Some i0) (EQ1: cget (cnext t) = Some i1),
    i0 < i1;
  cget_next_bw_some: forall (t: T) (i1: nat) (EQ: cget (cnext t) = Some i1),
    exists i0, cget t = Some i0;
  cget_mk_cnt_some: forall n b, cget (mk_cnt n (Some (S b))) = Some n;
  cget_mk_cnt_none: forall n, cget (mk_cnt n None) = Some n;
  cnext_mk_cnt: forall n b, cnext (mk_cnt n b) = mk_cnt (S n) (option_map Nat.pred b);
}.
HB.structure Definition Counter := { T of isCounter T }.

#[global] Hint Resolve cnext_lt cget_next_bw_some
  cget_mk_cnt_some cget_mk_cnt_none cnext_mk_cnt: seplog.
#[global] Hint Rewrite @cget_mk_cnt_some @cget_mk_cnt_none @cnext_mk_cnt: seplog.

(* Exhaustion is absorbing *)
Lemma cget_next_fw_none [Cn: Counter.type] (t: Cn) (EQ: cget t = None)
  : cget (cnext t) = None.
Proof.
  case E: (cget (cnext t)) => [i1|] //.
  by case: (cget_next_bw_some t i1 E) => i0; rewrite EQ.
Qed.
#[global] Hint Resolve cget_next_fw_none: seplog.

(* Once a counter is exhausted, calling [cnext] will never unexhaust it *)
Lemma cget_none_iter [Cn: Counter.type] (t: Cn) (EQ: cget t = None) (k: nat)
  : cget (Nat.iter k cnext t) = None.
Proof.
  elim: k => [|k IH] //=.
  exact: (cget_next_fw_none _ IH).
Qed.
#[global] Hint Resolve cget_none_iter: seplog.

(** An infinite counter never runs out: once it yields a name, it keeps yielding one. *)
HB.mixin Record isInfinite T of isCounter T := {
  cget_next_some: forall (t: T) (n: nat) (EQ: cget t = Some n),
    exists n', cget (cnext t) = Some n';
}.
HB.structure Definition InfiniteCounter := { T of Counter T & isInfinite T }.

#[global] Hint Resolve cget_next_some: seplog.

(** [CBudget t n]: the counter [t] can still produce at least [n] further identifiers *)
Fixpoint CBudget [Cn: Counter.type] (t: Cn) (n: nat): Prop :=
  match n with
  | 0 => True
  | S n' => (exists i, cget t = Some i) /\ CBudget (cnext t) n'
  end.

Lemma cbudget_0 [Cn: Counter.type] (t: Cn): CBudget t 0.
Proof. by []. Qed.
#[global] Hint Resolve cbudget_0: seplog.

Lemma cbudget_some [Cn: Counter.type] (t: Cn) (n: nat) (B: CBudget t (S n))
  : exists i, cget t = Some i.
Proof. by case: B. Qed.
#[global] Hint Resolve cbudget_some: seplog.

Lemma cbudget_cnext [Cn: Counter.type] (t: Cn) (n: nat) (B: CBudget t (S n))
  : CBudget (cnext t) n.
Proof. by case: B. Qed.
#[global] Hint Resolve cbudget_cnext: seplog.

Lemma cbudget_pred [Cn: Counter.type] (t: Cn) (n: nat) (B: CBudget t (S n)): CBudget t n.
Proof.
  elim: n t B => [|n IH] t B //.
  case: B => [[i EQ] B'].
  by split; [exists i | apply: IH].
Qed.
#[global] Hint Resolve cbudget_pred: seplog.

(* A budget is downward closed. *)
Lemma cbudget_le [Cn: Counter.type] (t: Cn) (n m: nat) (LE: n <= m) (B: CBudget t m)
  : CBudget t n.
Proof.
  elim: LE B => [|m' _ IH] B; first by [].
  exact: (IH (cbudget_pred t m' B)).
Qed.
#[global] Hint Resolve cbudget_le: seplog.

Lemma cbudget_infinite [Ic: InfiniteCounter.type] (t: Ic) (i: nat) (EQ: cget t = Some i)
  (n: nat) : CBudget t n.
Proof.
  elim: n t i EQ => [|n IH] t i EQ //.
  split; first by exists i.
  case: (cget_next_some t i EQ) => i' EQ'.
  exact: (IH (cnext t) i' EQ').
Qed.
#[global] Hint Resolve cbudget_infinite: seplog.

(** [excl C] equips a counter with a separation algebra *)
Definition eget [Cn: Counter.type] (x: excl Cn): option nat :=
  bind cget (excl_option x).

Definition enext [Cn: Counter.type] (x: excl Cn): excl Cn :=
  excl_map cnext x.

Definition emk_cnt [Cn: Counter.type] (n: nat) (b: option nat): excl Cn :=
  Owned (mk_cnt n b).

Section ExclCounter.

  Context (Cn: Counter.type).

  Lemma eget_next_bw_some: forall (c: excl Cn) (id1: nat) (EQ: eget (enext c) = Some id1),
      exists id0, eget c = Some id0.
  Proof using Type.
    case=> [|a] id1 /= EQ; first by discriminate EQ.
    exact: (cget_next_bw_some a id1 EQ).
  Qed.

  Lemma eget_next_lt: forall (c: excl Cn) (id0 id1: nat)
                             (EQ0: eget c = Some id0) (EQ1: eget (enext c) = Some id1),
      id0 < id1.
  Proof using Type.
    case=> [|a] id0 id1 /= EQ0 EQ1; first by discriminate EQ0.
    exact: (cnext_lt a id0 id1 EQ0 EQ1).
  Qed.

  Lemma eget_sep: forall c1 c2: excl Cn,
      c1 $/= c2 -> eget c1 <> eget c2 \/ (eget c1 = None /\ eget c2 = None).
  Proof using Type.
    case=> [|a]; case=> [|b] [c EQ]; cbn in EQ |- *.
    - by right.
    - by case E: (cget b) => [n|]; [left | right].
    - by case E: (cget a) => [n|]; [left | right].
    - by discriminate EQ.
  Qed.

  Lemma eget_sum: forall (c1 c2 c: excl Cn) (EQ: c1 $+ c2 = Some c),
      eget c = option_min Nat.min (eget c1) (eget c2).
  Proof using Type.
    case=> [|a]; case=> [|b] c EQ; cbn in EQ; try discriminate EQ;
      injection EQ as <-; cbn.
    - by [].
    - by case: (cget b).
    - by case: (cget a).
  Qed.

  Lemma eget_emk_cnt_some: forall n b, eget (emk_cnt n (Some (S b)): excl Cn) = Some n.
  Proof using Type. exact: cget_mk_cnt_some. Qed.

  Lemma eget_emk_cnt_none: forall n, eget (emk_cnt n None: excl Cn) = Some n.
  Proof using Type. exact: cget_mk_cnt_none. Qed.

  Lemma enext_emk_cnt: forall n b,
      enext (emk_cnt n b: excl Cn) = emk_cnt (S n) (option_map Nat.pred b).
  Proof using Type.
    by move=> n b; rewrite /enext /emk_cnt /= cnext_mk_cnt.
  Qed.

End ExclCounter.

HB.instance Definition _ (Cn: Counter.type) :=
  isCounter.Build (excl Cn)
    (@eget Cn)
    (@enext Cn)
    (@emk_cnt Cn)
    (@eget_next_lt Cn)
    (@eget_next_bw_some Cn)
    (@eget_emk_cnt_some Cn)
    (@eget_emk_cnt_none Cn)
    (@enext_emk_cnt Cn).

(** The container is transparent to the counter operations: [excl] tracks ownership
    and forwards everything else to the counter it wraps. *)
Lemma cget_owned [Cn: Counter.type] (c: Cn): cget (Owned c: excl Cn) = cget c.
Proof. by []. Qed.
#[global] Hint Resolve cget_owned: seplog.
#[global] Hint Rewrite @cget_owned: seplog.

Lemma cget_unowned {Cn: Counter.type}: cget (Unowned: excl Cn) = None.
Proof. by []. Qed.
#[global] Hint Resolve cget_unowned: seplog.
#[global] Hint Rewrite @cget_unowned: seplog.

Lemma cnext_owned [Cn: Counter.type] (c: Cn): cnext (Owned c: excl Cn) = Owned (cnext c).
Proof. by []. Qed.
#[global] Hint Resolve cnext_owned: seplog.
#[global] Hint Rewrite @cnext_owned: seplog.

Lemma cnext_unowned {Cn: Counter.type}: cnext (Unowned: excl Cn) = Unowned.
Proof. by []. Qed.
#[global] Hint Resolve cnext_unowned: seplog.
#[global] Hint Rewrite @cnext_unowned: seplog.

Lemma cnext_iter_owned [Cn: Counter.type] (c: Cn) (k: nat)
  : Nat.iter k cnext (Owned c: excl Cn) = Owned (Nat.iter k cnext c).
Proof.
  elim: k => [|k IH] //=.
  by rewrite IH cnext_owned.
Qed.
#[global] Hint Resolve cnext_iter_owned: seplog.
#[global] Hint Rewrite @cnext_iter_owned: seplog.

Lemma mk_cnt_owned [Cn: Counter.type] (n: nat) (b: option nat)
  : (mk_cnt n b: excl Cn) = Owned (mk_cnt n b).
Proof. by []. Qed.
#[global] Hint Resolve mk_cnt_owned: seplog.
#[global] Hint Rewrite @mk_cnt_owned: seplog.

Lemma eget_next_some [Ic: InfiniteCounter.type] (t: excl Ic) (n: nat)
  (EQ: cget t = Some n)
  : exists n', cget (cnext t) = Some n'.
Proof.
  case: t EQ => [|c]; first by [].
  rewrite cnext_owned !cget_owned.
  exact: (cget_next_some c n).
Qed.

HB.instance Definition _ (Ic: InfiniteCounter.type) :=
  isInfinite.Build (excl Ic) (@eget_next_some Ic).

(* Restating the counter laws in a way more amenable to proof search *)
Lemma cget_emp {Cn: Counter.type}: cget ($0: excl Cn) = None.
Proof. by []. Qed.
#[global] Hint Resolve cget_emp: seplog.
#[global] Hint Rewrite @cget_emp: seplog.

Lemma cget_sep [Cn: Counter.type] (c1 c2: excl Cn) (SEP: c1 $/= c2)
  : cget c1 <> cget c2 \/ (cget c1 = None /\ cget c2 = None).
Proof. exact: (eget_sep Cn c1 c2 SEP). Qed.
#[global] Hint Resolve cget_sep: seplog.

Lemma cget_sum [Cn: Counter.type] (c1 c2 c: excl Cn) (EQ: c1 $+ c2 = Some c)
  : cget c = option_min Nat.min (cget c1) (cget c2).
Proof. exact: (eget_sum Cn c1 c2 c EQ). Qed.
#[global] Hint Resolve cget_sum: seplog.

Lemma cget_sub [Cn: Counter.type] (c1 c2: excl Cn) (SUB: c1 $<= c2) (b1: nat)
  (EQ: cget c1 = Some b1)
  : exists b2, cget c2 = Some b2 /\ b2 <= b1.
Proof.
  case: SUB => b Eb.
  rewrite (cget_sum c1 b c2 Eb) EQ.
  case: (cget b) => [b2|] /=.
  - by exists (Nat.min b1 b2); split; [| apply: Nat.le_min_l].
  - by exists b1; split.
Qed.
#[global] Hint Resolve cget_sub: seplog.

Lemma cbudget_unowned [Cn: Counter.type] (n: nat) (B: CBudget (Unowned: excl Cn) (S n)): False.
Proof.
  case: B => [[i EQ] _].
  by discriminate EQ.
Qed.
#[global] Hint Resolve cbudget_unowned: seplog.

(* An owned counter is transparent *)
Lemma cbudget_owned [Cn: Counter.type] (n: nat) (c: Cn)
  : CBudget (Owned c: excl Cn) n <-> CBudget c n.
Proof.
  elim: n c => [|n IH] c; first by split.
  split; case=> [[i EQ] B]; (split; first by exists i).
  - exact: (proj1 (IH (cnext c)) B).
  - exact: (proj2 (IH (cnext c)) B).
Qed.
#[global] Hint Rewrite @cbudget_owned: seplog.

Lemma cget_mk_cnt_ne_0 [Cn: Counter.type] (n: nat) (b: option nat) (NE: b <> Some 0)
  : cget (mk_cnt n b: Cn) = Some n.
Proof.
  case: b NE => [[|b]|] NE.
  - by case: NE.
  - exact: cget_mk_cnt_some.
  - exact: cget_mk_cnt_none.
Qed.
#[global] Hint Resolve cget_mk_cnt_ne_0: seplog.

(* A counter with infinite budget has an arbitrary [CBudget] *)
Lemma cbudget_mk_cnt_none [Cn: Counter.type] (n k: nat)
  : CBudget (mk_cnt n None: Cn) k.
Proof.
  elim: k n => [|k IH] n //=.
  split; first by exists n; exact: cget_mk_cnt_none.
  rewrite cnext_mk_cnt /=.
  exact: IH.
Qed.
#[global] Hint Resolve cbudget_mk_cnt_none: seplog.

(** The canonical infinite counter. *)
Record nat_cnt: Set := mkNatCnt { nat_cnt_current: nat }.

Definition nat_cnt_get (c: nat_cnt): option nat := Some c.(nat_cnt_current).

Definition nat_cnt_next (c: nat_cnt): nat_cnt := {| nat_cnt_current := S c.(nat_cnt_current) |}.

Definition nat_cnt_mk (n: nat) (_: option nat): nat_cnt := mkNatCnt n.

Lemma nat_cnt_next_lt: forall (c: nat_cnt) (i0 i1: nat)
    (EQ0: nat_cnt_get c = Some i0) (EQ1: nat_cnt_get (nat_cnt_next c) = Some i1),
    i0 < i1.
Proof.
  rewrite /nat_cnt_get /nat_cnt_next => n i0 i1 [<-] [<-].
  exact: Nat.lt_succ_diag_r.
Qed.

Lemma nat_cnt_next_bw_some: forall (c: nat_cnt) (i1: nat)
    (EQ: nat_cnt_get (nat_cnt_next c) = Some i1),
    exists i0, nat_cnt_get c = Some i0.
Proof.
  by move=> c i1 _; exists c.(nat_cnt_current) .
Qed.

Lemma nat_cnt_get_some: forall n b, nat_cnt_get (nat_cnt_mk n (Some (S b))) = Some n.
Proof. by []. Qed.

Lemma nat_cnt_get_none: forall n, nat_cnt_get (nat_cnt_mk n None) = Some n.
Proof. by []. Qed.

Lemma nat_cnt_next_mk: forall n b,
    nat_cnt_next (nat_cnt_mk n b) = nat_cnt_mk (S n) (option_map Nat.pred b).
Proof. by []. Qed.

HB.instance Definition _ :=
  isCounter.Build nat_cnt nat_cnt_get nat_cnt_next nat_cnt_mk
    nat_cnt_next_lt nat_cnt_next_bw_some
    nat_cnt_get_some nat_cnt_get_none nat_cnt_next_mk.

Lemma nat_cnt_next_some: forall (c: nat_cnt) (m: nat)
    (EQ: nat_cnt_get c = Some m),
    exists m', nat_cnt_get (nat_cnt_next c) = Some m'.
Proof.
  by move=> c m _; exists (S c.(nat_cnt_current)).
Qed.

HB.instance Definition _ :=
  isInfinite.Build nat_cnt nat_cnt_next_some.
