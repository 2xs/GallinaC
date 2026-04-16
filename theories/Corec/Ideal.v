From Stdlib Require Import ProofIrrelevance FunctionalExtensionality
 PropExtensionality IndefiniteDescription.
From GallinaC.Corec Require Export CPO.


Record IDEAL (P: Poset) : Type :=
{
  ideal_set :> Setof P;
  ideal_prop : is_ideal ideal_set;
}.

Lemma ideal_equal{P : Poset} : forall (I J : IDEAL P),
    ideal_set _ I = ideal_set _ J -> I = J.
Proof.
intros I J Heq.
destruct I, J.
cbn in *.
revert ideal_prop0.
rewrite Heq.
intros.
f_equal.
apply proof_irrelevance.
Qed.

Definition ideal_bot{P:PPO} : IDEAL P:=
{|
  ideal_set := single ppo_bot;
  ideal_prop := single_bot_is_ideal
|}.

Lemma ideal_bot_is_principal{P:PPO} :
  is_principal (@ideal_bot P).
Proof.
exists ppo_bot.
cbn.
apply set_equal.
intros x; split; intro Hm.
-
  rewrite member_single_iff in Hm.
  rewrite Hm.
  apply member_principal.
-
  rewrite member_principal_iff in Hm.
  apply  le_bot_eq in Hm.
  rewrite Hm.
  apply member_single.
Qed.

Lemma ideal_bot_is_principal_if{P:PPO} :
  forall (x : P), ideal_set _ ideal_bot = principal x ->
                  x = ppo_bot.
Proof.
intros x Heq.
rewrite set_equal in Heq.
unfold ideal_bot in Heq.
cbn [ideal_set] in Heq.
specialize (Heq x).
rewrite member_single_iff in Heq.
rewrite Heq.
apply member_principal.
Qed.

Lemma bot_in_all_ideals{P:PPO} :
  forall (I : IDEAL P), member I ppo_bot.
Proof.
intros  (I , ((Hn,He), Hc)).
cbn.
rewrite not_empty_member in Hn.
destruct Hn as (x & Hm).
now specialize (Hc _ Hm _ (ppo_bot_least _)).
Qed.



Lemma subset_single_bot_all_ideals{P:PPO} :
  forall (I : IDEAL P), subset (single ppo_bot) I.
Proof.
intro I.
specialize (bot_in_all_ideals I) as Hm.
destruct I as  (I , ((Hn,He), Hc)).
cbn in *.
now rewrite single_subset_member.
Qed.

Lemma ideals_subset_antisym{P : Poset} :
  forall (I J : IDEAL P),
    subset I J -> subset J I -> I = J.
Proof.
intros (I, (Hd, Hc)) (J, (Hd',Hc')); cbn; intros Hs1 Hs2.
apply subset_antisym in Hs1; auto;subst.
f_equal; apply proof_irrelevance.
Qed.


Definition ideals_poset (P : Poset) :Poset :=
{|
  poset_carrier := IDEAL P ;
  poset_le :=  subset ;
  poset_refl := subset_refl ;
  poset_trans := subset_trans ;
  poset_antisym := ideals_subset_antisym ;
|}.

Definition ideals_ppo (P : PPO) :PPO :=
{|
  ppo_poset := ideals_poset P ;
  ppo_bot := ideal_bot;
  ppo_bot_least := subset_single_bot_all_ideals
|}.


Lemma union_ideals_is_ideal{P:Poset} :
  forall (SS: (Setof (Setof P))),
    is_directed (P := ideals_poset P) SS ->
    (forall S, member SS S -> is_ideal S) ->
    is_ideal (union SS).
Proof.
intros SS (Hne & Hmax)  Hall.
repeat split.
-
  rewrite not_empty_member.
  rewrite not_empty_member in Hne.
  destruct Hne as (S & Hm).
  unfold member in Hm.
  unfold ideals_poset in S; subst; cbn in *.
  destruct  S as (S , ((Hn , HmaxS) , Hd)); subst; cbn in *.
  rewrite not_empty_member in Hn.
  destruct Hn as (x & Hmx).
  now exists x, S.
-
  intros x y Hm1 Hm2.
  destruct Hm1 as (S1 & HmS1 & HmS1').
  destruct Hm2 as (S2 & HmS2 & HmS2').
  specialize (Hall _ HmS1) as Hi1.
  specialize (Hall _ HmS2) as Hi2.
  remember
    {| ideal_set := S1 ;
      ideal_prop := Hi1
    |} as I1.
   remember
    {| ideal_set := S2 ;
      ideal_prop := Hi2
    |} as I2.

   specialize (Hmax I1 I2).
   unfold member in Hmax.
   cbn in Hmax.
   subst.
   cbn in Hmax.
   specialize (Hmax HmS1 HmS2).
   destruct Hmax as (S & Hm & Hsub1 & Hsub2).
   eapply member_subset in Hsub1; eauto.
   eapply member_subset in Hsub2; eauto.
   destruct S as (S , ((HneS & HddS) , HdS)).
   cbn in *.
   specialize (HddS _ _ Hsub1 Hsub2).
   destruct HddS as (z & Hmz & Hlexz & Hleyz).
   exists z ; repeat split; auto.
   now apply member_union with (S := S).
-
  intros x Hmx y Hle.
  apply member_union_member_one in Hmx.
  destruct Hmx as (S & HmS & Hmx).
  apply member_union with (S := S); auto.
  destruct (Hall _ HmS) as (_ & Hd).
  now apply (Hd x).
Qed.


Lemma union_ideals_is_lub{P:PPO} :
  forall (SS: (Setof (Setof P)))
   (HD: is_directed (P := ideals_ppo P) SS)
    (Hall : (forall S, member SS S -> is_ideal S)),
    is_lub  (P := ideals_ppo P)  SS (Build_IDEAL _ (union SS)
    (union_ideals_is_ideal SS HD Hall)).
Proof.
intros SS HD Hall.
unfold ideals_ppo in * ; cbn in *.
split.
-
  unfold is_upper.
  cbn in *.
  intros y Hm.
  unfold member in Hm.
  apply member_union_subset; auto.
-
  cbn.
  intros y Hu.
  unfold is_upper in Hu.
  cbn in Hu.
  apply union_lub.
  intros S  Hm.
  specialize (Hu  (Build_IDEAL _ S (Hall _ Hm))).
  apply Hu,Hm.
Qed.


Lemma member_ideals_set_is_ideal{P : PPO} :
  forall
    (SS : Setof (ideals_ppo P)), (forall  (S: Setof P),
    member (fmap  SS (fun (I:ideals_ppo P) => (ideal_set _ I))) S
     -> is_ideal S).
Proof.
intros SS S Hm.
destruct Hm as (x & HSS & Heq).
rewrite Heq.
now destruct x.
Qed.

Definition ideal_lub_sig{P:PPO}
(S:Setof (IDEAL P)) (HD :is_directed (P:= ideals_ppo P) S) :
{I : IDEAL P | is_lub (P := ideals_poset P)S I}.

remember (fmap  S (fun (I:ideals_ppo P) => (ideal_set _ I))) as SS.
assert  (is_directed (P := ideals_poset P) SS).
{
  rewrite HeqSS.
  split.
  -
   rewrite not_empty_member.
   destruct HD as (Hn & _).
   rewrite not_empty_member in Hn.
   destruct Hn as (x & Hm).
   exists x.
   now exists x.
  -
   cbn in *.
   intros x y Hmx Hmy.
   destruct Hmx as (v & Hv & Heq); rewrite Heq in *; clear Heq.
   destruct Hmy as (w & Hw & Heq); rewrite Heq in *; clear Heq.
   destruct HD as (_ & Hma).
   destruct (Hma _ _ Hv Hw) as (z &  Hmz & Hlev & Hlew); clear Hma.
   exists z; repeat split; auto.
   now exists z.
}
 specialize  (member_ideals_set_is_ideal S) as Haux.
 assert (HallI : forall I, member SS I -> is_ideal I).
 {
  intros I Hm.
  apply Haux.
  now subst.
 }
 (*Huai, HallI*)
  specialize (union_ideals_is_ideal SS H) as Huai.
  exists (Build_IDEAL _ (union SS) (Huai HallI)).
  cbn.
  specialize (union_ideals_is_lub SS H HallI)
    as Huil.
  cbn in *.
  split.
  -
    intros x Hmx.
    destruct Huil as (Hu & _).
    apply (Hu x).
    unfold member.
    subst.
    now exists x.
  -
   intros y Huy.
   destruct Huil as (Hu & Hmin).
   apply Hmin.
   intros w Hmw.
   apply Huy.
   subst.
   destruct Hmw as (q & Hq & Heq); subst.
   cbn in *.
   assert (w = q)
     by now apply ideal_equal.
   now subst.
Defined.




Program Definition ideals_cpo (P : PPO) : CPO :=
{|
  cpo_ppo := ideals_ppo P;
  cpo_lub := _;
  cpo_lub_prop := _
|}.

Next Obligation.
intros P S.
cbn in *.
destruct (oracle (is_directed (P:= ideals_poset P) S)).
-
 exact (proj1_sig (ideal_lub_sig S i)).
-
 exact (ideal_bot).
Defined.

Next Obligation.
intros P S HD.
cbn in *.

unfold  ideals_cpo_obligation_1.
destruct ( oracle
(@is_directed
   (ideals_poset
      (ppo_poset P)) S)).
-
  cbn in *.
  exact  (proj2_sig (ideal_lub_sig S i)).
-
  contradiction.
Qed.



Lemma principal_is_compact{P: PPO} : forall (x :P),
    is_compact (P := (@ideals_cpo P))
      (Build_IDEAL _ (principal  x)
         (principal_is_ideal x)).
Proof.
intros x S Hd Hle.
cbn in *.
(*Set Printing Coercions.*)
remember (fmap S (fun I : IDEAL P => (ideal_set _ I)))  as SS.
unfold ideals_cpo_obligation_1 in Hle.
destruct (oracle (is_directed (P := ideals_poset P)S)); [|contradiction].
cbn in *.
unfold subset in Hle.
apply member_union_member_one  with (x := x)in Hle;
[| apply member_principal].
destruct Hle as (S' & Hm & Hm').
subst.
destruct Hm as (I & HSI & HeqI).
exists I.
subst.
split; auto.
rewrite principal_subset; auto.
destruct I; now destruct ideal_prop0.
Qed.


Definition all_principals{P: PPO} (I : IDEAL P) : Setof (Setof P) :=
  fmap (ideal_set _ I) principal.

Lemma all_principals_are_ideals{P:PPO} : forall I (S: Setof P),
  member (all_principals I) S -> is_ideal S.
Proof.
intros I S Hm.
destruct Hm as (x & HIx & Heq).
subst.
apply principal_is_ideal.
Qed.



Lemma all_principals_directed{P:PPO} : forall I,
    @is_directed  (@ideals_ppo P) (all_principals I).
Proof.
intros I.
destruct I as (S & HI).
specialize HI as HI'.
destruct HI' as ((Hns &HdS) & HcS).
split.
-
  cbn.
  rewrite  not_empty_member in *.
  specialize (not_empty_member S) as HneS.
  assert (Hex : exists x, member S x) by tauto.
  clear HneS.
  destruct Hex as (x & Hmx).
  exists (Build_IDEAL _ (principal x) (principal_is_ideal x)).
  cbn.
  now exists x.
-
  cbn in *.
  intros I J HmI HmJ.
  destruct HmI as (x & Hmx & Heq).
  destruct HmJ as (y & Hmy & Heqy).
  cbn in *.
  subst.
  destruct (HdS _ _  Hmx Hmy) as (z & Hmz & Hlexz& Hleyz).
  exists (Build_IDEAL _ (principal z) (principal_is_ideal z)).
  cbn.
  repeat split.
  +
    now exists z.
  +
    rewrite Heq.
    rewrite principal_subset.
    *
      now rewrite member_principal_iff.
    *
      now destruct (principal_is_ideal z).
  +
    rewrite Heqy.
    rewrite principal_subset.
    *
      now rewrite member_principal_iff.
    *
      now destruct (principal_is_ideal z).
Qed.



Lemma reformulate_compact_in_ideals{P: PPO} :
  forall (cc : ideals_cpo P),
    is_compact (P := ideals_cpo P) cc
    -> forall (S : Setof(IDEAL P))
    (HD : is_directed (P:= ideals_cpo P) S),
      subset (ideal_set _  cc)
        (union (fmap S (fun I : IDEAL P => ideal_set _ I)))
                    -> exists c, S c /\ subset (ideal_set _  cc) c.
Proof.
intros cc Hc S HD Hsub.
cbn in *.
unfold is_compact in Hc.
apply   (Hc _ HD ).
cbn in *.
unfold ideals_cpo_obligation_1.
destruct
(oracle (is_directed (P := ideals_poset P )S));
 [|contradiction].
apply Hsub.
Qed.


Lemma subset_ideals_union{P: PPO}:
  forall (I : IDEAL P),
    subset (ideal_set P I)
          (union
             (fmap
                (fun J : IDEAL P =>
                 all_principals I
                   (ideal_set P J))
                (fun K : IDEAL P =>
                   ideal_set _ K)
             )
          ).
(* NB these are actually equal *)
Proof.
intros I x Hmem.
exists (principal x); split; auto.
-
  exists (Build_IDEAL _ (principal x) (principal_is_ideal x)).
  cbn; split; auto.
  now exists x.
-
  apply member_principal.
Qed.




Lemma compact_is_principal{P: PPO} : forall (I : IDEAL P),
    is_compact (P := (@ideals_cpo P)) I ->
    exists x, ideal_set _ I =(principal  x).
Proof.
intros I Hc.
specialize (reformulate_compact_in_ideals _ Hc
                (fun J => member (all_principals I) J)
                (all_principals_directed I)
              (subset_ideals_union I)
           ) as Hc'.
destruct Hc' as (J & Hm & Hs).
destruct Hm as (x & Sx & Heq).
replace J with I in *.
-
  now exists x.
-
  apply ideal_equal.
  apply subset_antisym; auto.
  rewrite Heq in *.
  rewrite <- subset_principal_iff in *.
  intros y Hy.
  rewrite  member_principal_iff in Hy.
  destruct I as (SI & Hd & Hcc).
  now apply (Hcc x).
Qed.
