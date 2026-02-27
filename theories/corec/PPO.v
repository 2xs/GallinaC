From Coq Require Import IndefiniteDescription ProofIrrelevance PeanoNat
 Compare_dec Lia Classical List.
Import Nat ListNotations.
From Corec Require Export Poset Oracle.


Global Obligation Tactic := idtac.

Record PPO : Type := {
  ppo_poset :> Poset;
  ppo_bot : ppo_poset;  
  ppo_bot_least : forall x, poset_le ppo_bot  x
}.

Arguments ppo_bot {_}.
Arguments ppo_bot_least {_} _.


Lemma is_directed_add_ppo_bot{P:PPO} :
  forall (S: Setof P),
is_directed S -> is_directed (add S ppo_bot).
Proof.
intros S Hd.  
split.
- 
  rewrite not_empty_member.
  exists ppo_bot.
  now right.
-  
  destruct Hd as (_ & Hd).
  intros x y [Hmx | Hmw] [Hmy |Hmy]; subst.
  +
    destruct (Hd _ _ Hmx Hmy) as (z & Hmz & Hle1 & Hle2).
    exists z; split; auto.
    now left.
  +
    exists x; repeat split; auto;
      [now left | apply poset_refl| apply ppo_bot_least].
  +
    exists y; repeat split; auto;
      [now left | apply ppo_bot_least| apply poset_refl].
  +
    exists ppo_bot; repeat split;
      [now right | apply poset_refl | apply poset_refl].
 Qed.   

Lemma is_lub_remove_bot{P : PPO}:
  forall (S: Setof P) (l : P),
    ~ is_empty S ->
  S <> single (ppo_bot) -> is_lub S l <-> is_lub (remove S ppo_bot) l.
Proof.
intros S l Hne Hns.
rewrite not_empty_member in Hne.
destruct Hne as (a & Hma).
split; intro Hl ; auto.  
- 
  split.
  +
    intros x Hm.
    destruct Hm as (Hm & _).
    destruct Hl as (Hu & _).
    now apply Hu.
  +
    intros y Hu'.
    destruct Hl as (Hu & Hmin).
    apply Hmin.
    intros x Hmx.
    destruct (oracle (x= ppo_bot)); subst; [ apply ppo_bot_least |].
    apply Hu'.
    split; auto.
-    
  split.
  +
    intros y Hu'.
    destruct Hl as (Hu & Hmin).
    destruct (oracle (y= ppo_bot)); subst; [ apply ppo_bot_least |].
    apply Hu.
    split; auto.
  +
    intros y Hu'.
    destruct Hl as (Hu & Hmin).
    apply Hmin.
    intros x Hmx.
    apply (Hu' x).
    now destruct Hmx.
Qed.   
       
Lemma le_bot_eq{P : PPO}: forall (x : P),
    x <= ppo_bot -> x = ppo_bot.
Proof.  
intros x Hle.
apply poset_antisym; auto; apply ppo_bot_least.
Qed.



Lemma le_bot_iff_eq{P : PPO}: forall (x : P),
    x <= ppo_bot <-> x = ppo_bot.
Proof.
split; intro; subst; auto; try apply poset_refl.
now apply le_bot_eq.
Qed.


Lemma lub_bot_implies_single_bot{P: PPO}:
  forall (S: Setof P),
~is_empty S -> is_upper S ppo_bot -> S = single ppo_bot.
Proof.
intros S Hne Hu.
apply set_equal; intro x; split; intro Hm.
- 
  apply member_single_iff.
  apply le_bot_eq.
  now apply Hu.
-
  rewrite not_empty_member in Hne.
  destruct Hne as (y & Hmy).
  rewrite member_single_iff in Hm; subst.
  specialize (Hu _ Hmy).
  apply le_bot_eq in Hu;  now subst.
Qed.

Lemma single_bot_is_dclosed{P : PPO} :
  is_dclosed (single (@ppo_bot P)).
Proof.
intros x Hm y Hle.
rewrite member_single_iff in *; subst.
now apply le_bot_eq.
Qed.

Lemma single_bot_is_ideal{P : PPO} :
  is_ideal (single (@ppo_bot P)).
Proof.
split.
-
  apply single_is_directed.
-
  apply single_bot_is_dclosed.
Qed.



Lemma single_bot_is_principal_bot{P : PPO} :
  single (@ppo_bot P) = principal  (@ppo_bot P).
Proof.
apply set_equal; intros x; split ; intro Hm.  
-
  rewrite member_single_iff in Hm; subst.
  apply member_principal.
-  
  rewrite member_principal_iff in Hm.
  apply le_bot_iff_eq in Hm; subst.
  apply member_single. 
Qed.

Lemma remove_bot_directed{P : PPO} :
  forall (S: Setof P) (x: P),
    is_directed S ->member S x ->x <> ppo_bot ->
    is_directed (remove S ppo_bot).
Proof.  
intros S x Hd Hm Hne;split.       
- 
  apply not_empty_member.
  now exists x.
-
  intros z y (Hmz& Hnez) (Hmy & Hney).
  destruct Hd as (_ & Hd).
  specialize (Hd _ _ Hmz Hmy).
  destruct Hd as (z0 & Hmz0 & Hle1 & Hle2).
  exists z0; split; auto.
  split; auto.
  intro Heq; subst.
  apply le_bot_eq in Hle1.
  now apply Hnez.
Qed.


Lemma list_directed_has_upper{P:PPO} :
forall (l: list P)  (T: Setof P), is_directed T -> 
 (forall i, i < length l -> member T (nth  i l ppo_bot) ) ->
  exists q, member T q /\  
   forall j, j < length l -> nth j l ppo_bot <= q.
Proof.
induction l; intros T Hd Ha.
-
 destruct Hd as (Hne & _).
 rewrite not_empty_member in Hne.
 destruct Hne as (x & Hm).
 exists x; split; auto.
 intros j Hlt; cbn in Hlt; lia.
-
 cbn [length] in *.
 destruct l.
 +
  exists a; split ; auto.
  *
   cbn [length] in *.
   specialize (Ha 0); cbn in Ha; apply Ha; lia.
  *
   cbn [length]. 
   intros i Hi.
   assert (Heq : i = 0) by lia; subst.
   apply poset_refl.
 +
  cbn [length] in *.
  specialize (IHl _ Hd).
  assert (Hal : (forall i : nat,
    i < S (length l) -> member T (nth i (p :: l) ppo_bot))).
  { 
   intros i Hlt.
   apply (Ha (S i)); lia.
  }
  specialize (IHl Hal).
  clear Hal.
  destruct IHl as (q & Hmq & Hal).
  specialize Ha as Ha'.
  specialize (Ha' 0); cbn in Ha'.
  assert (Hma : member T a) by (apply Ha'; lia).
  clear Ha'.
  destruct Hd as (Hne & Hd).
  specialize (Hd _ _ Hmq Hma).
  destruct Hd as (z &  Hmz & Hleqz & Hleaz).
  exists z; split; auto.
  intros j Hlt.
  destruct j; auto.
  replace (nth (S j) (a :: p :: l) ppo_bot) with
  (  nth j (p :: l) ppo_bot); [|reflexivity].
   apply @poset_trans with (y :=q); auto.
   apply Hal;lia.
Qed.  


Lemma list_directed_has_upper_alt{P:PPO} :
forall (T: Setof P), is_directed T -> 
forall (l: list P),  (forall x, In x l ->  member T x ) ->
  exists q, member T q /\  
   forall x, In x l  -> x <= q.
Proof.   
intros T Hd l Ha.
assert (Ha' :(forall i, i < length l -> member T (nth  i l ppo_bot))) by
  (intros i Hlt; now apply Ha, nth_In).
clear Ha.
apply list_directed_has_upper in Ha'; auto.
destruct Ha' as (q & Hmq & Ha).
exists q; split; auto.
intros x Hin.
specialize (In_nth l x ppo_bot Hin) as Hin'.  
destruct Hin' as (n & Hlt & Heq).
rewrite <- Heq.
now apply Ha.
Qed.
