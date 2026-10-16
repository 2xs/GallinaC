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

From Stdlib Require Import NArith.

From GallinaC.Utils Require Import ListExt.
From GallinaC.Imp Require Import Storable.
From GallinaC.Imp Require Export Store Heap Primitives.
From GallinaC.Seplog Require Import Pred.
From GallinaC.Seplog.Exists Require Import Exists.
From GallinaC.Seplog.Lift Require Import Lift.
From GallinaC.Seplog.Star Require Import Star.
From GallinaC.Seplog.State Require Import Atoms.

Local Open Scope mem_scope.
Local Open Scope separation_scope.

Section ListAssertion.

  Context [Sm: State.type].
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).

  Fixpoint llist (o: N) (l: list Vl) (p: Pt) : Pred Sm :=
    match l with
    | [] => [| p = null |]
    | v :: l' => Exists (a: Ad) (p': Pt),
        [| References p a /\ Allows p Operation.Write
           /\ Reaches p (shift_fw a o) /\ Reaches p (shift_fw a (o + 1)) |]
        ** a ||~> v ** shift_fw a o ||~> encode p' ** llist o l' p'
    end.

  Lemma llist_null (o: N) (l: list Vl):
    |- llist o l null <==> [| l = [] |].
  Proof using Type.
    apply: impl_antisym_taut.
    - move=> s LIST.
      case: l LIST => [ | v l ] LIST.
      + case: LIST => _ EMP.
        by split.
      + case: LIST => a [ p' [ s1 [ s2 [ _ [ [ s3 [ s4 [ _ [ [ s5 [ s6 [ _ [ [ [ REF _ ] _ ] _ ] ] ] ] _ ] ] ] ] _ ] ] ] ] ].
        by move: REF; rewrite (proj2 (null_addr (null: Pt)) eq_refl).
    - move=> s [ -> EMP ].
      by split.
  Qed.

  Lemma llist_cons (o: N) (v: Vl) (l: list Vl) (p: Pt):
    |- llist o (v :: l) p <==>
       Exists (a: Ad) (p': Pt),
         [| References p a /\ Allows p Operation.Write
            /\ Reaches p (shift_fw a o) /\ Reaches p (shift_fw a (o + 1)) |]
         ** a ||~> v ** shift_fw a o ||~> encode p' ** llist o l p'.
  Proof using Type.
    move=> s.
    reflexivity.
  Qed.

  Lemma llist_nonnull (o: N) (l: list Vl) (p: Pt) (NN: p <> null):
    |- llist o l p <==> Exists (v: Vl) (l': list Vl), [| l = v :: l' |] ** llist o (v :: l') p.
  Proof using Type.
    apply: impl_antisym_taut.
    - move=> s LIST.
      case: l LIST => [ | v l' ] LIST.
      + case: LIST => NULL _.
        by case: (NN NULL).
      + exists v, l', $0, s.
        split; [ exact: (op_id_l s) | ].
        split; [ by split | exact: LIST ].
    - move=> s [ v [ l' [ ? [ s1 [ EQs [ [ -> EMP ] LIST ] ] ] ] ] ].
      move: EMP EQs => -> /partition_emp_l EQs.
      by rewrite -EQs.
  Qed.

  Lemma llist_cons_intro (o: N) (v: Vl) (l: list Vl) (p p': Pt) (a: Ad)
    (REF: References p a) (ALW: Allows p Operation.Write)
    (RCH: Reaches p (shift_fw a o)) (RCH1: Reaches p (shift_fw a (o + 1))):
    |- a ||~> v ** shift_fw a o ||~> encode p' ** llist o l p' ===> llist o (v :: l) p.
  Proof using Type.
    move=> s [ s1 [ s2 [ EQs [ [ s3 [ s4 [ EQs1 [ CA CO ] ] ] ] LIST ] ] ] ].
    exists a, p', s1, s2.
    split; [ exact: EQs | split; [ | exact: LIST ] ].
    exists s3, s4.
    split; [ exact: EQs1 | split; [ | exact: CO ] ].
    exists $0, s3.
    split; [ exact: (op_id_l s3) | split; [ split; [ | by [] ] | exact: CA ] ].
    by repeat split.
  Qed.

End ListAssertion.
