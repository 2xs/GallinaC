From Coq Require Import IndefiniteDescription ProofIrrelevance.
From Corec Require Export PPO.


Record CPO : Type := {
    cpo_ppo :> PPO;
    cpo_lub : forall (S : Setof cpo_ppo), cpo_ppo;
    cpo_lub_prop : forall S, 
      is_directed (P:= cpo_ppo) S -> 
       is_lub  (P:= cpo_ppo) S (cpo_lub S)
}.


Arguments cpo_ppo {_}.
Arguments cpo_lub {_} _.
Arguments cpo_lub_prop {_} _ _.


Lemma cpo_lub_eq_lub  {P : CPO} :
  forall (S : Setof P) (Hd : is_directed S),
    cpo_lub S = lub S
         (ex_intro (is_lub S)
            (cpo_lub S) ( cpo_lub_prop S Hd)).
Proof.
intros S Hd.
 erewrite is_lub_unique; eauto.
-
  apply lub_is_lub.
-
  now apply cpo_lub_prop.
Qed.


Lemma is_lub_cpo_lub_eq{C:CPO}:
  forall (S: Setof C)(c: C), 
is_lub S c -> is_directed S -> c = cpo_lub S.
Proof.
intros S c Hl Hd.
specialize (cpo_lub_prop S Hd) as Hl'.
eapply is_lub_unique; eauto.
Qed.


Lemma is_lub_eq_cpo_lub{P:CPO}:
forall (S S': Setof P)
  (Hd : is_directed S) (Hd': is_directed S'),
 is_lub S' (cpo_lub S)
 ->
  cpo_lub S =
    cpo_lub S'.
Proof.
intros S S' Hd Hd' Hl.
specialize (cpo_lub_prop _ Hd') as Hl'.
eapply is_lub_unique; eauto.  
Qed.


Lemma cpo_lub_single{P: CPO}:
  forall (x : P), cpo_lub (single x) = x.
Proof.
intros x.
specialize (single_is_directed x) as Hd.                    
specialize (cpo_lub_prop (c:=P) (single x) Hd) as Hp.
specialize (is_lub_single x) as Hs.
eapply is_lub_unique; eauto.
Qed.


(*Lemma 1 in the paper *)
Lemma forallex_lelub  {P : CPO} :
      forall (S S' : Setof P) (Hd : is_directed S) (Hd' : is_directed S'),
      (forall x, member S x -> exists y, member S' y /\ x <= y) ->
      cpo_lub  S <= cpo_lub S'.
Proof.
intros S S' Hd Hd' Hae.
rewrite   cpo_lub_eq_lub with (Hd := Hd).
rewrite   cpo_lub_eq_lub with (Hd := Hd').
now apply gforallex_lelub.
Qed.


Definition is_compact{P : CPO} (cc : P) :=
  forall S (Hd : is_directed S),
    cc <= cpo_lub S->  exists c, member S c /\ cc <= c.

Lemma is_compact_alt{P: CPO} :
  forall cc, is_compact (P:= P) cc <->
         forall S (Hd : is_directed S)(Hc: is_dclosed S),
          cc  <= cpo_lub S->  exists c, member S c /\ cc <= c.
Proof.                   
split; intro Hc.
-
  intros S Hd Hdc.
  now apply Hc.
-   
  intros S Hd Hdc.
  specialize (cpo_lub_prop _ Hd) as Hlup.
  specialize (is_lub_dclosure S) as Hil.
  rewrite Hil in Hlup; clear Hil.
  specialize (Hc _ (dclosure_is_directed _ Hd)
                (dclosure_is_dclosed S)).
  replace (cpo_lub (dclosure S) )
    with  (cpo_lub S) in *.
  {
    specialize (Hc Hdc).
    destruct Hc as (c & Hm & Hle).
    destruct Hm as (y & Hm & Hley).
    exists y; split; auto.
    eapply poset_trans; [apply Hle | apply Hley].
  }  
  specialize (cpo_lub_prop  _ Hd) as Hps.
  erewrite is_lub_eq_cpo_lub; eauto.
  now apply dclosure_is_directed.
Qed.

    
Lemma bot_is_compact{C:CPO} : is_compact (P := C) ppo_bot.
Proof.
intros S (Hne & Hd) Hle.
clear Hd Hle.
rewrite not_empty_member in Hne.
destruct Hne as (x & Hme); exists x; split; auto.
apply ppo_bot_least.
Qed.
  
  
  (*Lemma 2 in the paper *)
Lemma forallex_iff_lelub  {P : CPO} :
  forall (S S' : Setof P)  (Hd : is_directed S) (Hd' : is_directed S'),
      (forall x, member S x -> is_compact x) ->
      ((forall x, member S x -> exists y, member S' y /\ x <= y) <->
          cpo_lub S<= cpo_lub S').
Proof.
intros S S'  Hd Hd' Hc.
split.
-
  intros Hae.
  now apply forallex_lelub.
-
  intros Hle x Hm.
  specialize (Hc _ Hm).
  specialize Hle as Hle'.
  rewrite  cpo_lub_eq_lub with (Hd := Hd) in Hle'.
  rewrite  cpo_lub_eq_lub with (Hd := Hd') in Hle'.
  specialize (luble_memle _ _ _ Hle' _ Hm) as Hle''.
  rewrite <-  cpo_lub_eq_lub in Hle''.
  unfold is_compact in Hc.
  destruct (Hc _ Hd' Hle'') as (y & Hmy & Hley).
  now exists y.
Qed.


Definition is_continuous{P1 P2 : CPO}
  (f : P1 -> P2) := forall (S: Setof P1),
  is_directed  S ->
  is_directed  (fmap S f) /\
  f(cpo_lub S) =  
  cpo_lub  (fmap S f). 

Lemma continuous_implies_monotonic{P1 P2 : CPO} :
  forall (f : P1 -> P2), is_continuous f -> is_monotonic f.
Proof.
intros f Hc x y Hle.
specialize (Hc (fun z => z = x \/ z = y)
              (ordered_pair_is_directed  x y  Hle)).
destruct Hc as (Hd &  Heq). 
specialize (cpo_lub_prop _  (ordered_pair_is_directed x y Hle)) as Hcup.
specialize (cpo_lub_prop _ Hd) as Hcup'.
specialize (ordered_pair_has_lub _ _ Hle) as Hopl.
eapply is_lub_unique in Hcup; eauto.
rewrite <- Hcup in Heq; subst.
assert (Hisl:
         is_lub (fmap (fun z : P1 => z = x \/ z = y) f) (f y))
by
  (rewrite Heq;
  now apply cpo_lub_prop).
destruct Hisl as (Hu & _).
apply (Hu (f x)).
exists x ; split; auto.
Qed.

Lemma continuous_implies_commutes_with_lub  {P1 P2 : CPO} :
    forall (f : P1 -> P2), is_continuous f ->
                           forall S l, is_directed S -> commutes_with_lub f S l.
Proof.
intros f Hc S l Hd Hi.
specialize (Hc _ Hd).
destruct Hc as (Hd' & Heq).
specialize (cpo_lub_prop S Hd) as His'.
eapply is_lub_unique in Hi; eauto.
rewrite Hi in *.
rewrite Heq.
now apply cpo_lub_prop.
Qed.


Lemma mono_commutes_implies_continuous{P1 P2 : CPO} :  forall (f : P1 -> P2),
      is_monotonic f ->
       (forall S l, is_directed S -> commutes_with_lub f S l) ->
      is_continuous f.
Proof.
intros f Hm Hall S Hd.
split; [apply (monotonic_directed _ _ Hm Hd) |].
specialize (Hall _ (cpo_lub S) Hd (cpo_lub_prop S Hd)).
specialize (cpo_lub_prop (fmap S f) (monotonic_directed _ _ Hm Hd)) as His.
eapply is_lub_unique; eauto.
Qed.


Lemma continuous_iff_mono_commutes{P1 P2 : CPO} :  forall (f : P1 -> P2),
    is_continuous f <->
      (is_monotonic f /\
       (forall S l, is_directed S -> commutes_with_lub f S l)).
Proof.
 split ; intro HH.
 -
   split.
   +
     now apply continuous_implies_monotonic.
   +
     now apply continuous_implies_commutes_with_lub.
 -
   now apply mono_commutes_implies_continuous.
Qed.


Record CPO_ISOMORPHISM (P1 P2 : CPO)  : Type :=
{
  iso :>  Poset_ISOMORPHISM P1 P2;
  to_comm : forall S l, is_directed S -> commutes_with_lub (to iso) S l;
  from_comm : forall S l, is_directed S -> commutes_with_lub (from iso) S l         
}.

Arguments iso {_}.
Arguments to_comm {_} _ _ _.
Arguments from_comm {_} _ _ _.

Definition ppo_iso_cpo_iso{P1 P2: CPO}: Poset_ISOMORPHISM P1 P2 ->
CPO_ISOMORPHISM P1 P2.
intro Hi.
unshelve econstructor.
-
  exact Hi.
-
  intros S l Hd.
  now apply  to_commutes_with_lub.
-
  intros S l Hd.
  now apply from_commutes_with_lub.
Defined.  


Definition CPO_ISOMORPHISM_refl (P: CPO) :  CPO_ISOMORPHISM P P. 
unshelve econstructor.
-
 exact (Poset_ISOMORPHISM_refl P).
-
  cbn.
  intros S l Hd Hl.
  now rewrite fmap_id. 
-
  intros S l Hd Hl.
  cbn.
  now rewrite fmap_id. 
Defined.

Definition CPO_ISOMORPHISM_sym  (P1 P2: CPO) :
  CPO_ISOMORPHISM P1 P2 -> CPO_ISOMORPHISM P2 P1.
intros (iso , Hc1 , Hc2).  
unshelve econstructor.
-
  exact (Poset_ISOMORPHISM_sym _ _ iso).
-
  intros S l Hd.
  now apply Hc2.
-
  intros S l Hd.
  now apply Hc1.
Defined.

Definition CPO_ISOMORPHISM_trans  (P1 P2 P3: CPO) :
  CPO_ISOMORPHISM P1 P2 -> CPO_ISOMORPHISM P2 P3 -> CPO_ISOMORPHISM P1 P3.
intros (iso1 , Hc1, Hc'1) (iso2, Hc2, Hc'2).
unshelve econstructor.
-
  now apply Poset_ISOMORPHISM_trans with (P2 := P2).
-
  intros S l Hd Hl.
  cbn.
  rewrite fmap_comp.    
  apply Poset_isomorphism_lub_from_to.
  cbn.
  do 2 rewrite <- fmap_comp.
  apply Poset_isomorphism_lub_from_to.
  rewrite <- fmap_comp.
  rewrite bijection_from_to.
  rewrite comp_id_left.
  rewrite bijection_from_to.
  now rewrite fmap_id.
-
  intros S l Hd Hl.
  cbn.
  rewrite fmap_comp.
  apply Poset_isomorphism_lub_to_from.
  cbn.
  do 2 rewrite <- fmap_comp.
  apply Poset_isomorphism_lub_to_from.
  rewrite <- fmap_comp.
  rewrite bijection_to_from.
  rewrite comp_id_left.
  rewrite bijection_to_from.
  now rewrite fmap_id.
Defined.


Lemma from_is_continuous{P P' : CPO}(i : CPO_ISOMORPHISM P P'):
  is_continuous (from i).
Proof.  
rewrite continuous_iff_mono_commutes.
    split.
    -
      apply from_mono.
    -
      apply from_comm.
Qed.


Lemma to_is_continuous{P P' : CPO}(i : CPO_ISOMORPHISM P P'):
  is_continuous (to i).
Proof.  
rewrite continuous_iff_mono_commutes.
    split.
    -
      apply to_mono.
    -
      apply to_comm.
Qed.   
  



Lemma isomorphic_compact{P P' : CPO}(i : CPO_ISOMORPHISM P P'):
  forall cc, is_compact (P:= P) cc -> is_compact (P := P') (to i cc).
Proof.
intros cc Hc S' Hd' Hle.
specialize (monotonic_directed _ _ (from_mono _  _ i) Hd') as Hd.
eapply from_mono with (P1 := P)(p:= i)  in Hle .
rewrite from_to in Hle.
specialize (from_is_continuous i) as Hcf.
specialize (Hcf   _ Hd').
destruct Hcf as (Hd'' & Heq).
assert (Heqp  : Hd = Hd'') by apply proof_irrelevance.
subst.
rewrite Heq in *.
specialize (Hc _ Hd'' Hle).
destruct Hc as (c & Hl & Hle').
apply inv_member_fmap in Hl.
destruct Hl as (x & Heq' & Hm).
subst.
exists x; split; auto.
replace x with (to i (from i x)) in *; [| apply to_from].
rewrite from_to in Hle'.
now apply to_mono.
Qed.

  
Lemma isomorphic_compact_inv{P P' : CPO}
  (i : CPO_ISOMORPHISM P P'):
  forall cc, is_compact (P := P') (to i cc) ->
             is_compact (P:= P) cc.
Proof.
intros cc Hc.
remember (CPO_ISOMORPHISM_sym _ _ i) as j.    
replace cc with (to j (from j cc)) in *; [| apply to_from].
apply isomorphic_compact.
replace (to j) with (from i) in *.
- 
  now rewrite to_from in Hc.
-  
  now subst.
Qed.

Lemma isomorphic_compact_iff{P P' : CPO}
  (i : CPO_ISOMORPHISM P P'):
  forall cc, is_compact (P := P') (to i cc)  <->
             is_compact (P:= P) cc.
Proof.
intros cc; split; intro Hc.
-
  eapply isomorphic_compact_inv; eauto.
-
  now apply isomorphic_compact.
Qed.  


Lemma cpo_lub_eq{P: CPO} :
  forall (S S' : Setof P) (Hd : is_directed S) (Hd' : is_directed S'),
   S = S' ->   cpo_lub S = cpo_lub S'.
Proof.
intros S S' Hd Hd' Heq.
subst.
reflexivity.
Qed.




Lemma id_is_continuous{P:CPO}: 
 is_continuous (P1:= P) (P2 := P) id.
Proof.
intros S Hd.
rewrite fmap_id.
split; auto.
Qed.

Lemma comp_is_continous{P1 P2 P3: CPO}:
  forall (f : P2 -> P3) (g : P1 -> P2),
    is_continuous (P1 := P2) (P2 := P3) f
    -> is_continuous (P1:= P1)(P2 := P2) g ->
    is_continuous (f° g).
Proof.  
intros f g Hc2 Hc1 S Hd1.
specialize Hc1 as Hc1'.
apply continuous_implies_monotonic in Hc1'.
specialize Hc2 as Hc2'.
apply continuous_implies_monotonic in Hc2'.
unfold is_continuous in *.
destruct (Hc1 _ Hd1) as (Hd2 & Heq2).
destruct (Hc2 _ Hd2) as (Hd2' & Heq').
unfold "°".
unshelve eexists.
-
 apply monotonic_directed; auto.
 apply comp_is_monotonic; now apply 
 continuous_implies_monotonic.
-
  rewrite Heq2, Heq'.
  +
   apply cpo_lub_eq; auto.
   *
     apply monotonic_directed; auto.  
     now apply comp_is_monotonic.
   *
   now rewrite <- fmap_comp.
Qed.




Lemma cst_is_continous{P1 P2: CPO}: forall (a:P2),
    is_continuous (P1 := P1) (P2 := P2) (fun _ => a).
Proof.
intro a.
rewrite continuous_iff_mono_commutes.
split; [apply cst_is_monotonic|].
intros T l Hd Hl.
split.
-
  intros x (z & Hmz & Heq); subst.
  apply poset_refl.
-
 intros y Huy.
 apply Huy.
 destruct Hd as (Hne & _).
 rewrite not_empty_member in Hne.
 destruct Hne as (x & Hm).
 now exists x.
Qed.  


Lemma cpo_from_poset_iso{P:CPO}{Q:PPO}:  
  Poset_ISOMORPHISM P Q -> forall (S:Setof Q), is_directed S ->
  {l : Q | is_lub S l}.
Proof.
intros Hi S Hd.
apply Poset_ISOMORPHISM_sym in Hi.
apply (isomorphic_directed Hi) in Hd.
remember (fmap S (to Hi)) as S'.
remember (cpo_lub S') as l'.
specialize (cpo_lub_prop S' Hd) as Hil.
remember (from Hi l') as l.
exists l.
subst.
now apply Poset_isomorphism_lub_to_from.
Qed.



Lemma lem39part1{P:CPO}: 
forall (S:Setof P) (comps : P -> Setof P),
is_directed S -> 
(forall x, member S x -> 
  (forall y, member (comps x) y -> is_compact y) /\ 
   is_directed (comps x)  /\ is_lub (comps x) x) ->
 is_directed (union (fun (V: Setof P) => exists x, 
 member S x /\ V = comps x)).
Proof.
intros S comps Hd Ha.
split.
- 
  rewrite not_empty_member.
  destruct Hd as (Hne & _).
  rewrite not_empty_member in Hne.
  destruct Hne as (x & Hmx).
  destruct (Ha _ Hmx) as (_  & Hdx & _).
  destruct Hdx as (Hnex & _).
  rewrite not_empty_member in Hnex.
  destruct Hnex as (y & Hmy).
  exists y, (comps x); split; auto.
  exists  x; split; auto.
-
  intros a b Hma Hmb.
  apply  member_union_member_one in Hma,Hmb.
  destruct Hma as (Sa  & Hma & Hma').
  destruct Hmb as (Sb  & Hmb & Hmb').
  destruct Hma as (ca & Hmca & Heqa); subst.
  destruct Hmb as (cb & Hmcb & Heqb); subst.
  destruct (Ha _ Hmca) as (Haca & Hda & Hla).
  destruct (Ha _ Hmcb) as (Hacb & Hdb & Hlb).
  specialize (Haca _ Hma').
  specialize (Hacb _ Hmb').
  destruct Hd as (_ & Hd).
  destruct (Hd _ _ Hmca Hmcb) as 
   (c & Hmc & Hleca & Hlecb).
  destruct Hla as (Hua & _).
  destruct Hlb as (Hub & _).
  specialize (Hua _ Hma').
  specialize (Hub _ Hmb').
  destruct (Ha _ Hmc) as (_ & Hdc & Hlc).
  specialize (cpo_lub_prop _ Hdc) as Hlc'.
  apply is_lub_unique with (x := c) in Hlc' ; auto.
  assert (Hac : a <= c) by (eapply poset_trans; eauto).
  assert (Hbc: b <= c) by (eapply poset_trans; eauto).
  rewrite Hlc' in *.
  rewrite <- Hlc' in Hmc.
  assert (Hdc' : is_directed (comps c)) by 
  now rewrite <- Hlc' in Hdc.
  specialize (Haca _ Hdc' Hac).
  specialize (Hacb _ Hdc' Hbc).
  clear Hac Hbc Hleca Hlecb Hua Hub.
  destruct Haca as (c'a & Hmc'a & Hac'a).
  destruct Hacb as (c'b & Hmc'b & Hbc'b).
  destruct Hdc as (Hnec  & Hdc).
  rewrite <- Hlc' in Hdc.
  destruct (Hdc _ _ Hmc'a Hmc'b) as 
    (z  & Hmz & Hlea1 & Hlea2).
  exists z; repeat split; try 
    (eapply poset_trans; eauto).
  exists (comps c); split; auto.
  exists c ; split; auto.
  Qed.


Lemma lem39part2{P:CPO}: 
  forall (S:Setof P) (comps : P -> Setof P),
  is_directed S -> 
  (forall x, member S x -> 
    (forall y, member (comps x) y -> is_compact y) /\ 
     is_directed (comps x)  /\ is_lub (comps x) x) ->
     is_lub S
     (cpo_lub (union (fun (V: Setof P) => exists x, 
    member S x /\ V = comps x))).
Proof.
intros S comps Hd Ha.
specialize (lem39part1 S comps Hd Ha) as Hdu.
replace (cpo_lub
(union
   (fun V : Setof P =>
    exists x : P,
      member S x /\
      V = comps x))
) with (cpo_lub S); 
[now apply cpo_lub_prop | ].  
apply poset_antisym.
-
assert (Hale : forall x, member S x -> 
x <= cpo_lub
(union
   (fun V : Setof P =>
    exists x : P,
      member S x /\
      V = comps x))).
 {  
 intros x Hmx.
 specialize Ha as Ha'.
 specialize (Ha' _ Hmx) as (Hacc &  Hd' & Hl).
 replace x with (cpo_lub (comps x)); 
 [| erewrite is_lub_cpo_lub_eq; eauto].
 rewrite cpo_lub_eq_lub with (Hd := Hd').
 rewrite cpo_lub_eq_lub with (Hd := Hdu).

 apply lub_mono.
 intros y Hmy.
 exists (comps x); split; auto.
 exists x; split; auto.
 }
 specialize (cpo_lub_prop _ Hd) as (Hu & Hmin).
 apply Hmin.
 intros x Hmx.
 now apply Hale.
 -
  rewrite <- forallex_iff_lelub; auto.
  +
   intros x Hm.
   destruct Hm as (S' & (HmS' & HmS'y)).
   destruct HmS' as (y& Hmy & Heq); subst.
   exists y; split; auto.
   specialize (Ha _ Hmy) as (Hacc &  Hd' & Hl).
   destruct Hl as (Hu & _).
   now apply Hu.
 + 
   intros x Hm.
   destruct Hm as (S' & (HmS' & HmS'y)).
   destruct HmS' as (y& Hmy & Heq); subst.
   destruct (Ha _ Hmy) as (Ha' & _ & _).
   now apply Ha'.
 Qed.

Lemma lem51{D:Type}{C:CPO}: 
 forall (dset : D -> Setof C) (S: Setof D)
 (Ha : forall d,  is_directed (dset d)) l l',
    is_lub (union (fun V  => 
      exists d, member S d /\ V = single (cpo_lub (dset d)))) l ->
    is_lub (union(fun V => exists d, member S d /\ V = dset d)) l' ->
         l = l'.
 intros dset S Ha l l' Hl Hl'.
 apply poset_antisym.
 - specialize (lub_is_lub (union (fun V  => 
   exists d, member S d /\ V = single (cpo_lub (dset d)))) (
   ltac:(now exists l))) as Hll. 
   replace l with ((lub
   (union
      (fun V : Setof C =>
       exists d : D, member S d /\ V =single (cpo_lub (dset d))))
   (ex_intro _ l Hl)));
   [| erewrite is_lub_unique; eauto].
   specialize (lub_is_lub
    (union
   (fun V : Setof C =>
    exists d : D, member S d /\ V = dset d)) (ltac:(now exists l'))) as Hll'.
   replace l' with (lub
   (union
     (fun V : Setof C =>
      exists d : D, member S d /\ V = dset d))
   (ex_intro _ l'  Hl'));
    [| erewrite is_lub_unique; eauto].
   assert (Hal : forall d, member S d -> 
    cpo_lub (dset d) <=
    lub
    (union
     (fun V : Setof C => 
      exists d : D, member S d /\ V = dset d))
    (ex_intro _ l' Hl')
   ).
   {
    intros d Hmd.
    rewrite cpo_lub_eq_lub with (Hd := Ha d).
    apply lub_mono.
    intros x Hm.
    exists (dset d); split; auto.
    now exists d.
   }
  clear Hll'.
  destruct Hll as (_& Hmin).
  apply Hmin.
  clear Hmin.
  intros y Hu.
  destruct Hu as (V & HmV & Hmv').
  destruct HmV as (x & Hmx & Heq); subst.
  rewrite member_single_iff in Hmv'; subst.
  rewrite cpo_lub_eq_lub with (Hd := Ha x).
  apply lub_mono.
  intros y Hmy.
  exists (dset x); split; auto.
  now exists x.
-
 specialize (lub_is_lub (union (fun V  => 
  exists d, member S d /\V = single (cpo_lub (dset d)))) (
  ltac:(now exists l))) as Hll. 
 replace l with ((lub
 (union
   (fun V : Setof C =>
    exists d : D, member S d /\
      V = single (cpo_lub  (dset d))))
 (ex_intro _ l Hl)));
   [| erewrite is_lub_unique; eauto].
 specialize (lub_is_lub
 (union
  (fun V : Setof C =>
  exists d : D, member S d /\ V = dset d)) (ltac:(now exists l'))) as Hll'.
 replace l' with (lub
  (union
  (fun V : Setof C =>
   exists d : D, member S d /\ V = dset d))
  (ex_intro _ l'  Hl'));
   [| erewrite is_lub_unique; eauto].
   apply gforallex_lelub.
  intros x Hmx.
  destruct Hmx as (V & HmV & HmV').
  destruct HmV as (d & Hmd & Heq); subst.
  destruct Hll' as (Hu & _).
  exists (cpo_lub (dset d)); split.
  + 
  exists (single
  (cpo_lub (dset d))); split; 
  [| apply member_single].
  now exists d.
  +
   clear Hu Hll Hl Hl'.
   specialize (cpo_lub_prop _ (Ha d)) as Hl.
   destruct Hl as (Hu & _).
   now apply Hu.
Qed.  




Definition continuous_alt{P1 P2:CPO}(f : P1 -> P2) :=
forall (S : Setof P1) (Hd1 : is_directed S),
is_directed (fmap S f) /\
  f (cpo_lub S) <= cpo_lub (fmap S f).

Lemma continous_alt_implies_continuous{P1 P2:CPO} :
forall (f :  P1 -> P2), is_monotonic f ->
continuous_alt f -> is_continuous f.
Proof.
intros f Hm Hc S Hd.
specialize (Hc _ Hd).
destruct Hc as (Hd' & Hle).
split ; auto.
apply poset_antisym;auto.
specialize (cpo_lub_prop _ Hd') as Hc.
destruct Hc as (_ & Hu).
apply Hu.
intros y (z & Hmz & Heq); subst.
apply Hm.
specialize (cpo_lub_prop _ Hd) as Hc.
destruct Hc as (Hm' & _).
now apply Hm'.
Qed.