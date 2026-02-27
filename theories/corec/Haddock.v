From Coq Require Import FunctionalExtensionality.
From Corec Require Export Kleene Exp.

(*
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
*)

Lemma cont_iff_hcont_aux{A:Type}{B:CPO} :
  forall (S : Setof (EXP A B)) 
     (Hd : is_directed (P := EXP_Poset A B) S)
     (F : (A -> B) -> A -> B),
     is_monotonic(P1 := EXP_Poset A B)(P2:= EXP_Poset A B) F ->
     (fun a => cpo_lub (fmap S (fun f => F f a)))
         =
     (cpo_lub (c:= EXP_CPO A B) (fmap S F)).
Proof.
intros S Hd F Hm.
extensionality a.
assert (Hdl : forall a, is_directed (fmap S (fun f => F f a))).
{
  intro a'.
  apply  (@monotonic_directed (EXP_Poset A B) B); [| exact Hd].
  intros f f' Hle. 
  now apply Hm.
}
assert (Hdr : is_directed (P:= EXP_Poset A B) (fmap S F))
by
 now apply(@monotonic_directed  (EXP_Poset A B) (EXP_Poset A B)).
specialize (cpo_lub_prop _ (Hdl a)) as Hlbl.
specialize (@cpo_lub_prop (EXP_CPO A B) (fmap S F) Hdr) as Hlbr.
apply poset_antisym.
-
 
 assert (Haa : forall f, 
  member S f -> F f a <= (cpo_lub (c := EXP_CPO A B) (fmap S F)) a).
 {
   intros f Hmf.
   destruct Hlbr as (Hu & _).
   specialize (Hu (F f) (member_fmap S F f Hmf)).   
   apply (Hu a).
 }
 destruct Hlbl as (Hu & Hmin).
 apply Hmin.
 intros x (u & Hmu & Heq); subst.
 now apply Haa.
-
 clear Hlbl.
 assert (Hlbl : forall a, is_lub
           (fmap S
              (fun f : EXP A B => F f a))
           (cpo_lub
              (fmap S
                 (fun f : EXP A B =>
                  F f a)))) by (intro a'; now apply cpo_lub_prop).
 remember (fun a =>  cpo_lub (fmap S (fun f => F f a))) as h.
 assert (Hleh : forall g, member S g -> poset_le (p := EXP_Poset A B) (F g) h).
 {
  intros g Hmg.
  subst.
  intro x.
  specialize (Hlbl x).
  destruct Hlbl as (Hu & Hmin).
  apply Hu.
  now exists g.
 }
 assert (Hleh' : poset_le 
   (p := EXP_Poset A B) (cpo_lub (c := EXP_CPO A B) (fmap S F)) h).
  {
   destruct Hlbr as (Hu & Hmin).
   apply Hmin.
   intros g (u & Hmf & Heq); subst.
   intro a'.
   now apply Hleh.
  }
  subst.
  apply Hleh'.
Qed.


Definition is_H_continuous{A:Type}{B:CPO} (F : (A -> B) -> A -> B) :=
is_monotonic (P1 := EXP_Poset A B) (P2 := EXP_Poset A B) F /\
forall (S: Setof (EXP A B)),  is_directed (P := EXP_Poset A B) S ->
    F (fun a => cpo_lub (proj S a)) 
      =
    fun a => cpo_lub (fmap S (fun f => F f a)).

Theorem cont_iff_H_cont{A:Type}{B:CPO}:
forall F : (A -> B) -> A -> B,
  is_continuous (P1 := EXP_CPO A B)(P2 := EXP_CPO A B) F 
   <-> 
   is_H_continuous F.
Proof.
split; intro Hc.
- 
 rewrite  continuous_iff_mono_commutes in Hc.
 destruct Hc as (Hm & Hc).
 split; auto.
 intros S Hd.
 specialize (Hc S (cpo_lub (c:= EXP_CPO A B) S) Hd). 
 specialize (cpo_lub_prop (c:= EXP_CPO A B) S Hd) as Hl.
 specialize (Hc Hl).
 specialize (lub_proj S Hd) as Hlp.
 apply is_lub_unique with (x := cpo_lub (c:= EXP_CPO A B) S) in Hlp; auto.
 rewrite <- Hlp.

 rewrite  cont_iff_hcont_aux; auto.
 assert (Hdr : is_directed (P:= EXP_Poset A B) (fmap S F))
  by
   now apply(@monotonic_directed  (EXP_Poset A B) (EXP_Poset A B)).
 specialize (cpo_lub_prop (c:= EXP_CPO A B) _ Hdr) as Hl'.
 apply is_lub_unique with (x:= F (cpo_lub (c:= EXP_CPO A B) S)) in Hl'; auto.
-
 rewrite  continuous_iff_mono_commutes.
 destruct Hc as (Hm & Hc).
 split; auto.
 intros S l Hd Hl.
 specialize (Hc S Hd). 
 specialize (lub_proj S Hd) as Hlp.
 apply is_lub_unique with (x := l) in Hlp; auto.
 rewrite <- Hlp in Hc.
 rewrite Hc.
 cbn in *.
 rewrite  cont_iff_hcont_aux; auto.
 apply  (cpo_lub_prop  (c:= EXP_CPO A B)).
 now apply(@monotonic_directed  (EXP_Poset A B) (EXP_Poset A B)).
Qed.

Lemma H_continuous_implies_monotonic{A:Type}{B:CPO}:
forall (F: (A -> B) -> A -> B), is_H_continuous F ->
is_monotonic (P1 := EXP_Poset A B) (P2 := EXP_Poset A B) F.
Proof.
now intros F (Hm & _).
Qed.

Corollary Haddock{A:Type}{B:CPO}:
 forall (F: (A -> B) -> A -> B),
 is_H_continuous F ->
  is_least_fixpoint (X := EXP_Poset A B) F
   (iterate_lub (X := EXP_CPO A B) F).
Proof.
intros F Hc.
rewrite <-  (cont_iff_H_cont F) in Hc.
exact  (Kleene _ Hc).
Qed.
 

Definition pointwise_fix{A:Type}{B:CPO}(F: (A -> B) -> (A -> B))(a:A) :=
  cpo_lub (c := B) (fun (b:B) => 
    (exists n, b = (iterate (X:= EXP_PPO A B) n F) a)).



Lemma fix_pointwise_fix_aux{A:Type}{B:CPO} : 
forall (F: (A -> B) -> (A -> B)), is_H_continuous F -> 
forall a,
 @is_directed B
(fun b : B =>
 exists n : nat,
   b =
   @iterate (EXP_PPO A B)
     n F a).
Proof.
intros F Hc a.
split.
-
 apply not_empty_member.
 exists ppo_bot.
 now exists 0.
-
intros x y (n & Hequ) (m &Heqv); subst.
exists (@iterate (EXP_PPO A B) (max n m) F a); repeat split; 
[now exists (max n m) | | ].
+
  specialize (@iterate_mono (EXP_PPO A B) n (Nat.max n m) F
    (H_continuous_implies_monotonic F Hc)) as Hu.
  cbn in Hu.   
  apply Hu.
  apply PeanoNat.Nat.le_max_l.
+  
 specialize (@iterate_mono (EXP_PPO A B) m (Nat.max n m) F
 (H_continuous_implies_monotonic F Hc)) as Hu.
 cbn in Hu.   
 apply Hu.
 apply PeanoNat.Nat.le_max_r.
Qed. 

Lemma fix_pointwise_fix{A:Type}{B:CPO} : 
  forall (F: (A -> B) -> (A -> B)), is_H_continuous F ->
  (iterate_lub (X := EXP_CPO A B) F) =
  pointwise_fix F.
Proof.
intros F Hc.
unfold iterate_lub, pointwise_fix.
specialize (H_continuous_implies_monotonic F Hc) as Hm.

specialize (cont_iff_hcont_aux   (fun x : EXP_CPO A B
=> exists n : nat,
  x = iterate  (X:= EXP_PPO A B) n F) 
   (iterate_directed (X :=  EXP_PPO A B)F Hm) F Hm) 
     as Haux.
  assert (Heq1 : cpo_lub (c:= EXP_CPO A B)
  (fmap
     (fun x : EXP_CPO A B =>
      exists n : nat,
        x = iterate (X:= EXP_PPO A B) n F) F) =  
        cpo_lub
        (fun x : EXP_CPO A B =>
         exists n : nat, x = iterate (X:= EXP_PPO A B)  n F)).
 {
  apply poset_antisym.
  - 
  apply forallex_lelub.
  +
  apply(@monotonic_directed  (EXP_Poset A B) (EXP_Poset A B)); auto.
  now apply (iterate_directed (X :=  EXP_PPO A B)).
  +
  now apply (iterate_directed (X :=  EXP_PPO A B)).
  +
   intros x ( u & (n & Heqn) & Heq); subst.
   exists (fun a => F (iterate  (X:= EXP_PPO A B) n F) a).
   split ; [| apply poset_refl].
   now eexists (S n).
 -
  apply forallex_lelub.
  +
  now apply (iterate_directed (X :=  EXP_PPO A B)).
  +
  apply(@monotonic_directed  (EXP_Poset A B) (EXP_Poset A B)); auto.
  now apply (iterate_directed (X :=  EXP_PPO A B)).
  +
  intros x ( n & Hmu); subst.
  exists (iterate  (X:= EXP_PPO A B) (S n) F).
  split.
  *
    exists (iterate  (X:= EXP_PPO A B) n F); split; [| reflexivity].
    now exists n.
  *
    now apply iterate_mono_aux.
 }        
cbn in Heq1, Haux.
rewrite Heq1 in Haux.
clear Heq1.
assert (Heq2 : 
  (fun a : A =>
        cpo_lub 
          (fmap
             (fun x : EXP A B =>
              exists n : nat,
                x = iterate (X:= EXP_PPO A B) n F)
             (fun f : EXP A B =>
              F f a))) = (fun a : A =>
              cpo_lub
                (fun b : B =>
                 exists n : nat, b = iterate (X:= EXP_PPO A B) n F a))
).
{
  extensionality a.
  apply poset_antisym.
  {
    apply forallex_lelub.
    -
     apply (@monotonic_directed (EXP_Poset A B) B).
     +
      intros x y Hlexy.
      now apply (H_continuous_implies_monotonic _ Hc).
     +
      apply (@iterate_directed (EXP_PPO A B)).
      now apply H_continuous_implies_monotonic.
  -
    now apply fix_pointwise_fix_aux.
  -
   intros x (f & (n & Heq' ) & Heq) ; subst.
   exists (F
   (@iterate (EXP_PPO A B)
      n F) a); split; [| apply poset_refl].
         now exists (S n).
  }
  {
    apply forallex_lelub.
    - 
      now apply fix_pointwise_fix_aux.
    -
    apply (@monotonic_directed (EXP_Poset A B) B).
    +
     intros x y Hlexy.
     now apply (H_continuous_implies_monotonic _ Hc).
    +
     apply (@iterate_directed (EXP_PPO A B)).
     now apply H_continuous_implies_monotonic.
    -
    intros x (n & Heq) ; subst.
    cbn.
    exists (@iterate (EXP_PPO A B) (S n) F a); split.
      +
        eexists.
        split; [exists n ;reflexivity | reflexivity].
      +
      specialize (iterate_mono_aux (X := EXP_PPO A B) n F );
      cbn; intro Hs.
      apply Hs.
      now apply H_continuous_implies_monotonic.
  }  
}
rewrite Heq2 in Haux.
clear Heq2.
rewrite Haux.
clear Haux.
specialize (@lub_proj A B (fun x : EXP_CPO A B =>
exists n : nat, x = @iterate (EXP_CPO A B) n F)) as Haux.
specialize (iterate_directed (X :=  EXP_CPO A B) F
 (H_continuous_implies_monotonic F Hc) )
  as Hid. 
specialize (Haux Hid).
specialize (cpo_lub_prop _ Hid) as Hlu.
eapply is_lub_unique in Hlu; eauto.
Qed.

Corollary Haddock_pointwise{A:Type}{B:CPO}:
 forall (F: (A -> B) -> A -> B),
 is_H_continuous F ->
  is_least_fixpoint (X := EXP_Poset A B) F
  (pointwise_fix F).
Proof.
intros F Hcont.
rewrite <- fix_pointwise_fix; [now apply Haddock | exact Hcont ].
Qed.

