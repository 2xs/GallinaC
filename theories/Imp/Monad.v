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

From Stdlib Require Import FunctionalExtensionality Morphisms.

Declare Scope program_scope.
Local Open Scope program_scope.
Delimit Scope program_scope with program.

Inductive outcome(T:Type) : Type :=
| Success : T -> outcome T
| Failure : outcome T.
Arguments Success {_} _.
Arguments Failure {_}.

Definition program (S A : Type) : Type := S -> option (outcome (A * S)).

Definition ret {S A : Type} (a : A) : program S A :=
  fun s => Some (Success (a, s)).

Definition bind {S A B : Type} (m : program S A) (f : A -> program S B) :
  program S B :=
  fun s => match m s with
           | None => None
           | Some Failure => Some Failure
           | Some (Success (a,s')) => f a s'
           end.

Notation "'do' x <- m1 ; m2" := (@bind _ _ _ m1 (fun x => m2))
                                  (at level 100, x name, m1 at level 90, m2 at level 100)
    : program_scope.

Notation "'do' ( x : t )  <- m1 ; m2" := (@bind _ _ _ (m1: program _ t) (fun x => m2))
                                           (at level 100, x name, m1 at level 90, m2 at level 100)
    : program_scope.

Notation "'do' ' p <- m1 ; m2" := (@bind _ _ _ m1 (fun x => match x with p => m2 end))
                                  (at level 100, p pattern, m1 at level 90, m2 at level 100)
    : program_scope.

Notation "'do' ' ( p : t )  <- m1 ; m2" := (@bind _ _ _ (m1: program _ t) (fun x => match x with p => m2 end))
                                           (at level 100, p pattern, m1 at level 90, m2 at level 100)
    : program_scope.

Notation "m1 ;; m2" := (@bind _ _ _ m1 (fun _ => m2))
                         (at level 100, m2 at level 100) : program_scope.

Definition loop{S A : Type} : program S A :=
  fun _ => None.

Definition fail{S A : Type} : program S A :=
  fun _ => Some Failure.

Definition get {S : Type} : program S S :=
  fun s => Some (Success (s, s)).

Definition put {S : Type} (s : S) : program S unit :=
  fun _ => Some (Success (tt, s)).

Definition modify {S : Type} (f : S -> S) : program S unit :=
  do s <- get;
  put (f s).

Notation "'If' c 'then' m1 'else' m2" :=
  (do b <- c ; if b then m1 else m2) (at level 200) : program_scope.

Lemma ret_left {S A B : Type} (a : A) (f : A -> program S B) :
  (do x <- ret a; f x) = f a.
Proof.
  repeat constructor.
Qed.

Lemma ret_right {S A : Type} (m : program S A) : (do x <- m ; ret x) = m.
Proof.
  extensionality s.
  unfold bind.
  destruct (m s) as [ [ [ a s' ] | ] | ]; reflexivity.
Qed.

Lemma bind_assoc
  {S A B C : Type}
  (m : program S A) (f : A -> program S B) (g : B -> program S C) :
  (do y <- (do x <- m; f x); g y) = (do x <- m; do y <- f x; g y).
Proof.
  extensionality s.
  unfold bind.
  destruct (m s) as [ [ [ a s' ] | ] | ]; reflexivity.
Qed.

Lemma bind_success
  {S A B: Type}
  {m: program S A} {f: A -> program S B} {a s s'}
  (EQ: m s = Some (Success (a, s'))):
  (bind m f) s = f a s'.
Proof.
  now unfold bind; rewrite EQ.
Qed.

Lemma bind_failure
  {S A B: Type}
  {m: program S A} {f: A -> program S B} {s}
  (EQ: m s = Some Failure):
  (bind m f) s = fail s.
Proof.
  now unfold bind; rewrite EQ.
Qed.

Lemma bind_diverge
  {S A B: Type}
  {m: program S A} {f: A -> program S B} {s}
  (EQ: m s = None):
  (bind m f) s = loop s.
Proof.
  now unfold bind; rewrite EQ.
Qed.

(* Registers [bind] as a morphism for [setoid_rewrite]. Note that the
continuation uses [pointwise_relation A eq] and not [eq]. Otherwise, rewriting
fails. *)
#[export] Instance bind_Proper {S A B} :
  Proper (eq ==> pointwise_relation A eq ==> eq) (@bind S A B).
Proof.
  unfold pointwise_relation.
  intros m1 m2 EQm f1 f2 EQf. subst m2.
  unfold bind. extensionality s.
  destruct (m1 s) as [ [ [ a s' ] | ] | ].
  - rewrite EQf; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
