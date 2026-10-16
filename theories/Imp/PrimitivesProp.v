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

From Stdlib Require Import Psatz.
From Stdlib Require Import NArith.

From GallinaC.Utils Require Import Algebra Counter.
From GallinaC.Imp Require Import Storable Store Heap While.
From GallinaC.Imp Require Export Intops Primitives Monad.

Local Open Scope program_scope.

Section PrimitivesProp.

Context {Sm: State.type}.
Local Notation Ad := (@m_ad Sm).
Local Notation Nm := (@var_name Sm).
Local Notation Pt := (@ptr_t Sm).
Local Notation Vl := (value (@ptr_t Sm)).
Local Notation St := (@m_st Sm).
Local Notation Hp := (@m_hp Sm).

Lemma read_var_eq_state [So: Storable.type Vl]: forall (nm: Nm) (s: Sm) (v: So) s',
    read_var nm s = Some (Success (v, s')) -> s' = s.
Proof using Type.
  intros nm s v s' Hread_var.
  unfold read_var in Hread_var.
  cbn in Hread_var.
  destruct (lookup (State.store s) nm) as [w|] eqn:Hlookup; [ | discriminate ].
  now destruct (decode w); inversion Hread_var.
Qed.

Lemma read_ptr_eq_state [So: Storable.type Vl]: forall (ptr: Pt) (s: Sm) (v: So) s',
    read_ptr ptr s = Some (Success (v, s')) -> s' = s.
Proof using Type.
  intros ptr s v s' Hread_ptr.
  unfold read_ptr in Hread_ptr.
  cbn in Hread_ptr.
  destruct (lookup (State.heap s) ptr) as [w|] eqn:Hlookup; [ | discriminate ].
  now destruct (decode w); inversion Hread_ptr.
Qed.

Lemma write_var_some [So: Storable.type Vl] (varname: Nm) (val: So)
  (s s': Sm) (st: St)
  (EQ: mutate (store s) varname (encode val) = Some st)
  (EQst: store s' = st) (EQsg: scnt s' = scnt s)
  (EQhp: heap s' = heap s) (EQalc: alc s' = alc s)
  : write_var varname val s = Some (Success (tt, s')).
Proof using Type.
  rewrite /write_var /bind /get EQ.
  have MK: mk_state_opt st (scnt s) (heap s) (alc s) = Some s'.
  { apply/mk_state_opt_some; repeat split; assumption. }
  by rewrite MK.
Qed.

Lemma write_var_none [So: Storable.type Vl] (varname: Nm) (val: So) (s: Sm)
  (EQ: mutate (store s) varname (encode val) = None)
  : write_var varname val s = Some Failure.
Proof using Type.
  by rewrite /write_var /bind /get EQ.
Qed.

Lemma write_ptr_some [So: Storable.type Vl] (p: Pt) (val: So)
  (s s': Sm) (h: Hp)
  (EQ: mutate (heap s) p (encode val) = Some h)
  (EQst: store s' = store s) (EQsg: scnt s' = scnt s)
  (EQhp: heap s' = h) (EQalc: alc s' = alc s)
  : write_ptr p val s = Some (Success (tt, s')).
Proof using Type.
  rewrite /write_ptr /bind /get EQ.
  have MK: mk_state_opt (store s) (scnt s) h (alc s) = Some s'.
  { apply/mk_state_opt_some; repeat split; assumption. }
  by rewrite MK.
Qed.

Lemma write_ptr_none [So: Storable.type Vl] (p: Pt) (val: So) (s: Sm)
  (EQ: mutate (heap s) p (encode val) = None)
  : write_ptr p val s = Some Failure.
Proof using Type.
  by rewrite /write_ptr /bind /get EQ.
Qed.

Lemma free_ptr_some (p: Pt) (s s': Sm) (h: Hp)
  (EQ: free (heap s) p = Some h)
  (EQst: store s' = store s) (EQsg: scnt s' = scnt s)
  (EQhp: heap s' = h) (EQalc: alc s' = alc s)
  : free_ptr p s = Some (Success (tt, s')).
Proof using Type.
  rewrite /free_ptr /bind /get EQ.
  have MK: mk_state_opt (store s) (scnt s) h (alc s) = Some s'.
  { apply/mk_state_opt_some; repeat split; assumption. }
  by rewrite MK.
Qed.

Lemma free_ptr_none (p: Pt) (s: Sm)
  (EQ: free (heap s) p = None)
  : free_ptr p s = Some Failure.
Proof using Type.
  by rewrite /free_ptr /bind /get EQ.
Qed.

Lemma alloc_ptr_some [So: Storable.type Vl] (n: N) (val: So) (s s': Sm)
  (hp: Hp) (c: excl (@heap_alc _ Pt Vl Hp)) (ptr: Pt)
  (BND: (n <= alloc_max_size)%N)
  (EQ: alloc (heap s) (alc s) n (encode val) = Some (hp, c, ptr))
  (EQst: store s' = store s) (EQsg: scnt s' = scnt s)
  (EQhp: heap s' = hp) (EQalc: alc s' = c)
  : alloc_ptr n val s = Some (Success (ptr, s')).
Proof using Type.
  rewrite /alloc_ptr (proj2 (N.leb_le _ _) BND) /bind /get EQ.
  have MK: mk_state_opt (store s) (scnt s) hp c = Some s'.
  { apply/mk_state_opt_some; repeat split; assumption. }
  by rewrite MK.
Qed.

Lemma alloc_ptr_overflow_fail [So: Storable.type Vl] (n: N) (val: So) (s: Sm)
  (BND: (alloc_max_size < n)%N)
  : alloc_ptr n val s = Some Failure.
Proof using Type.
  by rewrite /alloc_ptr; case: (N.leb_spec0 n alloc_max_size) => // LE; lia.
Qed.

Lemma alloc_ptr_none [So: Storable.type Vl] (n: N) (val: So) (s: Sm)
  (EQ: alloc (heap s) (alc s) n (encode val) = None)
  : alloc_ptr n val s = Some Failure.
Proof using Type.
  rewrite /alloc_ptr.
  case: (N.leb n alloc_max_size); [ | reflexivity ].
  by rewrite /bind /get EQ.
Qed.

Lemma with_var_step {A} {So: Storable.type Vl}
  (e_var: So) (k: Nm -> program Sm A) (s s1: Sm) st sg nm
  (PUSH: push (store s) (scnt s) (encode e_var) = Some (st, sg, nm))
  (MK: mk_state_opt st sg (heap s) (alc s) = Some s1)
  : with_var e_var k s
    = (do v <- k nm;
       do s' <- get;
       match pop (store s') with
       | Some st' =>
           match mk_state_opt st' (scnt s') (heap s') (alc s') with
           | Some s'' => put s'';; ret v
           | None => fail
           end
       | None => fail
       end) s1.
Proof using Type.
  by rewrite /with_var /bind /get /put PUSH MK.
Qed.

Lemma bind_with_var_step {A B} {So: Storable.type Vl}
  (e_var: So) (k: Nm -> program Sm A) (j: A -> program Sm B) (s s1: Sm) st sg nm
  (PUSH: push (store s) (scnt s) (encode e_var) = Some (st, sg, nm))
  (MK: mk_state_opt st sg (heap s) (alc s) = Some s1)
  : (do x <- with_var e_var k; j x) s
    = (do v <- k nm;
       do s' <- get;
       match pop (store s') with
       | Some st' =>
           match mk_state_opt st' (scnt s') (heap s') (alc s') with
           | Some s'' => put s'';; j v
           | None => fail
           end
       | None => fail
       end) s1.
Proof using Type.
  rewrite /with_var /bind /get /put PUSH MK.
  case: (k nm s1) => [[[v s2]|]|] //=.
  case: (pop (store s2)) => [st'|] //=.
  by case: (mk_state_opt st' (scnt s2) (heap s2) (alc s2)) => [s3|].
Qed.

End PrimitivesProp.

#[global] Hint Resolve write_var_some: seplog.
#[global] Hint Resolve write_var_none: seplog.
#[global] Hint Resolve write_ptr_some: seplog.
#[global] Hint Resolve write_ptr_none: seplog.
#[global] Hint Resolve free_ptr_some: seplog.
#[global] Hint Resolve free_ptr_none: seplog.
#[global] Hint Resolve alloc_ptr_some: seplog.
#[global] Hint Resolve alloc_ptr_none: seplog.

(** ** Reduction tactics

These tactics allow "reducing" GallinaC programs. These only work on concrete
states (i.e. ones built from a concrete model such as [Models.GCModel]).

 *)

(** [norm_state s] forces the evaluation on a state, reducing it. The goal is to
replace heaps such as [ _ $+ _ ] by their concrete counterparts. *)
Local Ltac norm_state s :=
  let s' := eval vm_compute in s in
    progress (change s with s').

(** [norm_monadic m s] forces the evaluation of a monadic computation under state
[s].

 Don't apply this on [while] or other opaque computations. It is used by the
 "toplevel" reduce tactic to only reduce the "topmost" monadic computation. *)
Local Ltac norm_monadic m s :=
  lazymatch type of m with
  | program _ _ =>
      let x := (eval vm_compute in (m s)) in
      match x with
      | Some (Success (?a, ?s')) =>
          erewrite (bind_success (m := m) (a := a) (s' := s')) by reflexivity
      end
  end.

(** [reduce] aggressively reduces monadic computations.

This tactic unrolls while loops using [while_fixpoint]. On a non-terminating
program, this [repeat reduce] will never return.

If the tactic doesn't progress, it is most likely because a primitive is not
registered.

 *)
Ltac reduce :=
  match goal with
  | |- context [ do x <- (do y <- _; _); _ ] =>
      rewrite bind_assoc
  | |- context [ do var v <- _; _ ] =>
      erewrite with_var_step by reflexivity
  | |- context C [ (do x <- ?m; _) ?s ] =>
      (try norm_state s);
      match m with
      | ret _ => norm_monadic m s
      | While.while _ _ => rewrite While.while_fixpoint
      | with_var _ _ => erewrite bind_with_var_step by reflexivity
      | read_var _ => norm_monadic m s
      | write_var _ _ => norm_monadic m s
      | alloc_ptr _ _ => norm_monadic m s
      | read_ptr _ => norm_monadic m s
      | write_ptr _ _ => norm_monadic m s
      | free_ptr _ => norm_monadic m s
      | shift_fw_ptr _ _ => norm_monadic m s
      | shift_bw_ptr _ _ => norm_monadic m s
      | eq_ptr _ _ => norm_monadic m s
      | Monad.get => norm_monadic m s
      | put _ => norm_monadic m s
      | Unsigned.div _ _ => norm_monadic m s
      | Unsigned.mdl _ _ => norm_monadic m s
      end
  end; cbn; simpl.
