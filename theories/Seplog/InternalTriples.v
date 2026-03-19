From GallinaC.Imp Require Import Primitives.
From GallinaC.Imp Require Import Memval.
From GallinaC.Seplog Require Export Hoare Pred.
Import Nat.
Import Pointer.
Import Heap(Heap).
Import Store(Store).

Local Open Scope state_scope.
Local Open Scope program_scope.
Local Open Scope heap_scope.

Lemma bind_get_rule
  {S A : Type} (f : S -> program S A)
  (P : S -> Prop) (Q : A -> S -> Prop)
  (Hhoare: forall s', {{ fun s => P s /\ s' = s }} f s' {{ Q }}):
  {{ P }} do s <- get; f s {{ Q }}.
Proof.
  intros s HP.
  cbn.
  destruct (f s s) as [ [ (a & s') | ] | ] eqn:Hfss; auto;
    specialize (Hhoare s s ltac:(easy));
    now rewrite Hfss in Hhoare.
Qed.
