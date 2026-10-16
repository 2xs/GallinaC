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

From GallinaC.Imp Require Import State.
From GallinaC.Seplog Require Import Pred.
From GallinaC.Seplog.Emp Require Import Emp.
From GallinaC.Seplog.Stateless Require Import Stateless.
From GallinaC.Seplog.Lift Require Import Lift.
From GallinaC.Seplog.Star Require Import Star.

Local Open Scope separation_scope.
Local Open Scope mem_scope.

Section EmpHeap.

  Context [Sm: State.type].

  Definition Emp_heap: Pred Sm := fun s => heap s = $0 /\ alc s = $0.

  Local Notation "$$0h" := Emp_heap: separation_scope.

  Lemma Emp_Emp_heap: |- ($$0: Pred Sm) ===> Emp_heap.
  Proof using Type.
    move=> s.
    rewrite /Emp => ->.
    case: (@emp_proj Sm) => _ [ _ [ EQhp0 EQalc0 ] ].
    by split.
  Qed.

  Definition Emp_heap_cnt: Pred Sm :=
    fun s => scnt s = $0 /\ heap s = $0 /\ alc s = $0.

  Definition heapless (P: Pred Sm) : Prop :=
    |- P ===> $$0h.

  Lemma heapless_star (P Q: Pred Sm) : heapless P -> heapless Q -> heapless (P ** Q).
  Proof using Type.
    move=> HEAPLESSP HEAPLESSQ s [ sp [ sq [ EQs [ Psp Qsq ] ] ] ].
    case: (HEAPLESSP _ Psp) => EQhpp EQalcp.
    case: (HEAPLESSQ _ Qsq) => EQhpq EQalcq.
    case/state_sum_spec: EQs => _ [ _ [ EQhp EQalc ] ].
    move: EQhpp EQhpq EQhp => -> -> EQhp.
    move: EQalcp EQalcq EQalc => -> -> EQalc.
    move/partition_emp_l: EQhp => EQhp.
    move/partition_emp_l: EQalc => EQalc.
    by split; congruence.
  Qed.

  Lemma heapless_lift P : heapless ([| P |]: Pred Sm).
  Proof using Type.
    move=> s [ HP -> ].
    by split; [ exact: heap_emp | exact: alc_emp ].
  Qed.

  Lemma stateless_heapless (P: Pred Sm) : stateless P -> heapless P.
  Proof using Type.
    move=> STATELESS s Ps.
    rewrite (STATELESS s Ps).
    by split; [ exact: heap_emp | exact: alc_emp ].
  Qed.

End EmpHeap.

Arguments Emp_heap {Sm}.
Arguments Emp_Emp_heap {Sm}.
Arguments Emp_heap_cnt {Sm}.

Notation "$$0h" := Emp_heap: separation_scope.
