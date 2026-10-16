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

From Stdlib Require Import NArith Arith.

From GallinaC.Utils Require Import ListExt Algebra Counter.
From GallinaC.Imp Require Import Monad Storable Heap Store While.
From GallinaC.Imp Require Export State.

Local Open Scope separation_scope.
Local Open Scope program_scope.

Section Primitives.

  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).



  Definition with_var {A} {So: Storable.type Vl} (e_var: So) (p_cont: Nm -> program Sm A): program Sm A :=
    do s <- get;
    match push (store s) (scnt s) (encode e_var) with
    | Some (st, sg, n) =>
        match mk_state_opt st sg (heap s) (alc s) with
        | Some s1 =>
            put s1;;
            do v <- p_cont n;
            do s' <- get;
            match pop (store s') with
            | Some st' =>
                match mk_state_opt st' (scnt s') (heap s') (alc s') with
                | Some s'' => put s'';; ret v
                | None => fail
                end
            | None => fail
            end
        | None => fail
        end
    | None => fail
    end.

  Definition read_var {So: Storable.type Vl} (varname: Nm): program Sm So :=
    do s <- get;
    match lookup (store s) varname with
    | Some val =>
        match decode val with
        | Some v => ret v
        | None => fail
        end
    | None => fail
    end.

  Definition write_var {So: Storable.type Vl} (varname: Nm) (val: So): program Sm unit :=
    do s <- get;
    match mutate (store s) varname (encode val) with
    | Some st =>
        match mk_state_opt st (scnt s) (heap s) (alc s) with
        | Some s' => put s'
        | None => fail
        end
    | None => fail
    end.

  Definition read_ptr {So: Storable.type Vl} (p: Pt): program Sm So :=
    do s <- get;
    match (lookup (heap s) p) with
    | Some val =>
        match decode val with
        | Some v => ret v
        | None => fail
        end
    | None => fail
    end.

  Definition write_ptr {So: Storable.type Vl} (p: Pt) (val: So): program Sm unit :=
    do s <- get;
    match mutate (heap s) p (encode val) with
    | Some h =>
        match mk_state_opt (store s) (scnt s) h (alc s) with
        | Some s' => put s'
        | None => fail
        end
    | None => fail
    end.

  Definition alloc_ptr {So: Storable.type Vl} (n: N.t) (val: So): program Sm Pt :=
    if N.leb n alloc_max_size then
      do s <- get;
      match alloc (heap s) (alc s) n (encode val) with
      | Some (hp, alc', ptr) =>
          match mk_state_opt (store s) (scnt s) hp alc' with
          | Some s' => put s';; ret ptr
          | None => fail
          end
      | None => fail
      end
    else fail.

  Definition free_ptr (p: Pt): program Sm unit :=
    do s <- get;
    match free (heap s) p with
    | Some h =>
        match mk_state_opt (store s) (scnt s) h (alc s) with
        | Some s' => put s'
        | None => fail
        end
    | None => fail
    end.

  Definition shift_fw_ptr (ptr: Pt) (shift: N.t): program Sm Pt :=
    do s <- get;
    match weakly_valid (heap s) ptr, ptr_shift_fw ptr shift with
    | true, Some p =>
        match weakly_valid (heap s) p with
        | true => ret p
        | false => fail
        end
    | false,_ | _, None => fail
    end.

  Definition shift_bw_ptr (ptr: Pt) (shift: N.t): program Sm Pt :=
    do s <- get;
    match weakly_valid (heap s) ptr, ptr_shift_bw ptr shift with
    | true, Some p =>
        match weakly_valid (heap s) p with
        | true => ret p
        | false => fail
        end
    | false,_ | _, None => fail
    end.

  Definition eq_ptr (ptr_l: Pt) (ptr_r: Pt): program Sm bool :=
    do s <- get;
    match cmp_valid (heap s) ptr_l ptr_r, cmp ptr_l ptr_r with
    | true, Some b => ret b
    | _, _ => fail
    end.

End Primitives.

Arguments alloc_ptr {Sm So} n%_N_scope val.
Arguments shift_fw_ptr {Sm} ptr shift%_N_scope.
Arguments shift_bw_ptr {Sm} ptr shift%_N_scope.

#[global] Hint Opaque with_var read_var write_var read_ptr write_ptr alloc_ptr free_ptr
  shift_fw_ptr shift_bw_ptr eq_ptr : seplog seplog_search.

Notation "'do' 'var' x <- m1 ; m2" := (with_var m1 (fun x => m2))
                                  (at level 100, x name, m1 at level 90, m2 at level 100):
    program_scope.

Notation "'do' 'var' ( x : t )  <- m1 ; m2" := (with_var (m1: t) (fun x => m2))
                                       (at level 100, x name, m1 at level 90, m2 at level 100):
    program_scope.

Notation "ptr ~+> shift" := (shift_fw_ptr ptr shift) (at level 50, left associativity): program_scope.

Notation "ptr ~-> shift" := (shift_bw_ptr ptr shift) (at level 50, left associativity): program_scope.

Definition while {S: Type} := @While.while S.

(* Notation "{ m }" := (m: program _ _): program_scope. *)
