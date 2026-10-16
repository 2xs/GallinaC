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

From GallinaC.Imp Require Export Monad While.
From GallinaC.Seplog Require Export Pred.
From GallinaC.Seplog.Exists Require Import Exists.
From GallinaC.Seplog.Union Require Import Union.
From GallinaC.Seplog.Forall Require Import Forall.

Local Open Scope program_scope.
Local Open Scope separation_scope.

Definition hoare [S A: Type] (total: bool) (P: Pred S) (m: program S A) (Q: A -> Pred S): Prop :=
  forall s, P s -> match m s with
                   | Some (Success (a, s')) => Q a s'
                   | Some Failure => False
                   | None => ~~ total
                   end.

Notation "{{ P }} m {{ Q }}" :=
  (hoare false P m Q)
    (at level 90,
      format "'[' '[' {{  P  }}  ']' '/  ' '[' m ']' '['  {{  Q  }} ']' ']'"
    ).

Notation "[[ P ]] m [[ Q ]]" :=
  (hoare true P m Q)
    (at level 90,
      format "'[' '[' [[  P  ]]  ']' '/  ' '[' m ']' '['  [[  Q  ]] ']' ']'"
    ).

#[global] Instance hoare_proper [S A: Type] (total: bool):
  Proper (pointwise_relation S iff ==> eq ==> pointwise_relation A (pointwise_relation S iff) ==> iff)
    (@hoare S A total).
Proof.
  move=> P P' EQP m _ <- Q Q' EQQ.
  by split=> TRIPLE s /EQP /TRIPLE;
    case: (m s) => [ [ [ a s' ] | ] | ] // /(EQQ a s').
Qed.

Lemma weaken [S A: Type] [total: bool] [m: program S A] [P Q: Pred S] [R: A -> Pred S]:
  hoare total Q m R -> (forall s, P s -> Q s) -> hoare total P m R.
Proof.
  by move=> TRIPLE IMP s /IMP /TRIPLE.
Qed.

Lemma strengthen [S A: Type] [total: bool] [m: program S A] [P: Pred S] [Q R: A -> Pred S]:
  hoare total P m Q -> (forall a s, Q a s -> R a s) -> hoare total P m R.
Proof.
  move=> TRIPLE IMP s /TRIPLE.
  by case: (m s) => [ [ [ a s' ] | ] | ] // /IMP.
Qed.

Lemma consequence [S A: Type] [total: bool] [m: program S A] [P P': Pred S] [Q Q': A -> Pred S]:
  (forall s, P' s -> P s) -> hoare total P m Q -> (forall a s, Q a s -> Q' a s) ->
  hoare total P' m Q'.
Proof.
  move=> PRE TRIPLE POST.
  exact: strengthen (weaken TRIPLE PRE) POST.
Qed.

Lemma total_partial [S A: Type] [P: Pred S] [m: program S A] [Q: A -> Pred S]:
  [[ P ]] m [[ Q ]] -> {{ P }} m {{ Q }}.
Proof.
  move=> TRIPLE s /TRIPLE.
  by case: (m s) => [ [ [ a s' ] | ] | ].
Qed.

Lemma exists_pre [S A B: Type] [total: bool] [P: B -> Pred S] [m: program S A] [Q: A -> Pred S]:
  (forall x, hoare total (P x) m Q) -> hoare total (Exists x, P x) m Q.
Proof.
  move=> TRIPLE s [ x Pxs ].
  exact: TRIPLE x s Pxs.
Qed.

Lemma disj_rule [S A: Type] [total: bool] [P1 P2: Pred S] [m: program S A] [Q1 Q2: A -> Pred S]:
  hoare total P1 m Q1 -> hoare total P2 m Q2 ->
  hoare total (P1 || P2) m (fun a => Q1 a || Q2 a).
Proof.
  move=> TRIPLE1 TRIPLE2 s [/TRIPLE1 | /TRIPLE2].
  - by case: (m s) => [ [ [ a s' ] | ] | ] // Q1as'; left.
  - by case: (m s) => [ [ [ a s' ] | ] | ] // Q2as'; right.
Qed.

Lemma conj_rule [S A I: Type] [total: bool] [P: I -> Pred S] [m: program S A] [Q: I -> A -> Pred S]:
  inhabited I -> (forall i, hoare total (P i) m (Q i)) ->
  hoare total (Forall i, P i) m (fun a => Forall i, Q i a).
Proof.
  move=> [i0] TRIPLE s FPs.
  case EQm: (m s) (TRIPLE i0 s (FPs i0)) => [ [ [ a s' ] | ] | ] // _ i.
  by move: (TRIPLE i s (FPs i)); rewrite EQm.
Qed.

Lemma pure_pre [S A: Type] [total: bool] [p: Prop] [P: Pred S] [m: program S A] [Q: A -> Pred S]:
  (p -> hoare total P m Q) -> hoare total (fun s => p /\ P s) m Q.
Proof.
  move=> TRIPLE s [Hp Ps].
  exact: TRIPLE Hp s Ps.
Qed.
