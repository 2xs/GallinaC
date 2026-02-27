From Coq Require Import FunctionalExtensionality ProofIrrelevance.
From Corec Require Export CPO.


Definition is_fixpoint{X :Type} (f : X -> X) (x:X)
:= f x = x.


Definition is_least_fixpoint{X :Poset} (f : X -> X) (x:X) :=
    is_fixpoint f x /\ forall y, is_fixpoint f y -> x <= y.

Fixpoint iterate{X: PPO} (n : nat) (f :  X -> X):=
    match n with 
    | S n' => f (iterate n' f) 
    | 0 => ppo_bot
    end.


Lemma iterate_mono_aux{X: PPO} : forall  n(f : X -> X),
    is_monotonic f -> 
    (iterate  n f) <= (iterate (S n) f).
Proof.
induction n ; intros f Hm.
-
  apply ppo_bot_least.
-
  cbn.
  now apply Hm, IHn.
Qed.  


Lemma iterate_mono{X: PPO} : forall  n m (f : X -> X),
    is_monotonic f -> 
    (n <= m)%nat -> 
    (iterate  n f) <= (iterate m f).
Proof.
intros n m f Hm  Hle.
induction Hle.
-
 apply poset_refl.
-
 eapply poset_trans; eauto.
 now apply iterate_mono_aux.
Qed. 


Lemma iterate_directed{X: PPO} : forall (f : X -> X),
is_monotonic f -> 
is_directed (fun x => exists n, x = iterate n f ).
Proof.
intros f Hm.
split.
-
 apply not_empty_member.
 exists ppo_bot.
 now exists 0.
-
 intros x y Hmx Hmy.
 destruct Hmx as (n & Heq); subst.
 destruct Hmy as (m & Heq); subst.
 exists (iterate (max n m) f); repeat split.
 +
   now exists (max n m).
 +
   apply iterate_mono; auto.
   apply PeanoNat.Nat.le_max_l.
 +
   apply iterate_mono; auto.
   apply PeanoNat.Nat.le_max_r.
Qed.   


Definition iterate_lub{X:CPO}(f : X -> X) :=
cpo_lub (fun x => exists n, x = iterate n f ).

Lemma iterate_lub_fixpoint{X:CPO}(f : X -> X)(Hc:is_continuous f):
  is_fixpoint f (iterate_lub f ).
Proof.
  unfold is_fixpoint,iterate_lub.
  remember (iterate_directed f (continuous_implies_monotonic f Hc)) as Hd.
  specialize (cpo_lub_prop _  Hd) as Hl.
  specialize 
  (continuous_implies_commutes_with_lub _ Hc _ _
  Hd Hl) as Hcl.
  assert (Hd' : is_directed (fmap
  (fun x : X =>
   exists n : nat, x = iterate n f) f))
  by
   (apply monotonic_directed; auto;
   now apply continuous_implies_monotonic).
  apply is_lub_cpo_lub_eq in Hcl; auto.
  rewrite Hcl.
  apply poset_antisym; auto.
  -
   apply forallex_lelub; auto.
   intros x Hmx.
   destruct Hmx as (y & (n & Heq) & Heq'); 
   subst.
   exists (iterate (S n) f);split; [| apply poset_refl].
   now exists (S n).
  -
   apply forallex_lelub; auto.
   intros x (n & Heq); subst.
   exists (iterate (S n) f); split.
   +
     exists (iterate n f); split; auto.
     now exists n.
   +
    apply iterate_mono_aux.
    now apply continuous_implies_monotonic.
Qed.  


Lemma lub_iter_fix_is_least_aux{A:PPO} : forall n (G: A -> A) 
(a a':A),
is_monotonic G -> is_fixpoint G a' -> 
iterate n G  <= a'.
Proof.
induction n ; intros G a a' Hm Hf; [apply ppo_bot_least|].
cbn.
unfold is_fixpoint in Hf.
rewrite <- Hf.
now apply Hm, IHn.
Qed.

Lemma lub_iter_fix_is_least{A:PPO}: forall (F: A -> A) l,
is_monotonic F ->
is_lub (P:= A) (fun x => exists n, x = iterate n F) l ->
is_fixpoint F l ->
is_least_fixpoint F l.
Proof.
intros F l Hm Hl Hf.
split; auto.
intros a' Hf'.
assert (Hup : is_upper ((fun x : A =>
exists n : nat,
  x = iterate n F)) a').
{
 intros y (n & Heq); subst.
 now apply lub_iter_fix_is_least_aux.
}
destruct Hl as (_ & Hmin).
now apply Hmin.
Qed.


Lemma Kleene{A:CPO}(f : A ->A )(Hc : is_continuous f) :
  is_least_fixpoint f 
   (iterate_lub f).
Proof.
split.
 - 
  now apply  iterate_lub_fixpoint.
 -
  apply lub_iter_fix_is_least.
  +
    now apply continuous_implies_monotonic.
  +
    apply cpo_lub_prop.
    apply iterate_directed.
    now apply continuous_implies_monotonic.
  +
   now apply iterate_lub_fixpoint.
Qed.   

