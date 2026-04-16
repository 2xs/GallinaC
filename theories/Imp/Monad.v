From Stdlib Require Import FunctionalExtensionality.

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
