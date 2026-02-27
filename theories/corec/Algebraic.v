From Coq Require Import FunctionalExtensionality ProofIrrelevance. 
From Corec Require Export Ideal.

Definition compacts_le{P: CPO}(c : P) := fun cc => is_compact cc /\ cc <= c.

Record ALGEBRAIC : Type :=
{
  algebraic_cpo :> CPO;
  algebraic_dir : forall c,
    is_directed (compacts_le (P := algebraic_cpo) c);
  algebraic_lub : forall c,
    c = cpo_lub (c:=algebraic_cpo) (compacts_le c)
            
}.


Arguments algebraic_cpo {_}.
Arguments algebraic_dir {_} _.
Arguments algebraic_lub {_} _.


Definition is_ed_continuous{X Y : ALGEBRAIC}(f: X -> Y):=
forall cy x, is_compact cy -> cy <= f x -> 
exists cx, is_compact cx /\ cx <= x  /\ cy <= f cx.

Lemma continuous_ed_continuous{X Y: ALGEBRAIC} :
forall (f: X -> Y), is_continuous f -> is_ed_continuous f.
Proof.
intros f Hc.
specialize Hc as Hm.
apply continuous_implies_monotonic in Hm.
intros  cy x Hcy Hle.
specialize (algebraic_lub x) as Hal.
destruct (Hc _ (algebraic_dir x)) as (Hdf & Heqf).
rewrite <- Hal in Heqf.
rewrite Heqf in Hle.
specialize (Hcy _ Hdf Hle).
destruct Hcy as (c & (z & (Hcz & Hlez) & Heqz) & Hlec); subst.
exists z ;split; auto.
Qed.


Lemma ed_continuous_mono_continuous{X Y: ALGEBRAIC} :
forall (f: X -> Y), 
is_monotonic f ->is_ed_continuous f -> is_continuous f.
Proof.
intros f Hm Hc.
apply continous_alt_implies_continuous;auto.
intros S Hd.
specialize (monotonic_directed _ _ Hm Hd) as Hd'.
split; auto.
specialize (algebraic_lub (f(cpo_lub S))) as Hl.
rewrite Hl.
apply  forallex_lelub; auto.
 -
  apply algebraic_dir.

 - intros cy (Hcy & Hlecy).
specialize (Hc _ _ Hcy Hlecy).
destruct Hc as (cx & Hcx & Hle1 & Hle2).
destruct (Hcx _ Hd Hle1) as (y & Hmy & Hle).
exists (f y); split; auto.
+
  now exists y.
+
  eapply poset_trans ; [now apply Hle2|].
  now apply Hm.
Qed.  


Lemma continuous_iff_ed_continuous_mono{X Y: ALGEBRAIC} :
forall (f: X -> Y), 
is_continuous f <-> (is_monotonic f /\ is_ed_continuous f).
Proof.
split.
-
 intro Hc ; split.
 + now apply continuous_implies_monotonic.
 + now apply continuous_ed_continuous.
 -
  intros (Hm & Hc).
  now apply ed_continuous_mono_continuous.
Qed.  


Lemma compacts_le_single_bot{C : ALGEBRAIC}:
  forall (c : C), compacts_le c =
                    single ppo_bot -> c = ppo_bot.
Proof.
intros c Heq.
specialize (algebraic_lub c) as Hl.
specialize (cpo_lub_prop  _  (algebraic_dir c)) as Hil.
rewrite  <- Hl in Hil.
rewrite Heq in Hil.
destruct Hil as (Hu & Hmin).
apply le_bot_eq.
apply Hmin.
intros x Hm.
rewrite member_single_iff in Hm.
subst; apply poset_refl.
Qed.


Lemma nonempty_compacts_le{C: CPO} :
  forall (c: C), ~ is_empty (compacts_le c).
Proof.  
intro c.
apply not_empty_member.
exists ppo_bot; split; auto;
  [apply bot_is_compact | apply ppo_bot_least].
Qed.

Lemma compacts_le_upper{C: CPO} :
  forall (c: C), is_upper  (compacts_le c) c.
Proof.  
intros c x Hm.
now destruct Hm.
Qed.



Lemma compacts_le_directed{P : PPO}:
forall (c :IDEAL P),
  is_directed (P := ideals_ppo P)
    (fun cc  =>
       is_compact  (P := ideals_cpo P) cc /\ cc <= c).
Proof.  
intros c.
destruct c as (S & (Hne & Hd) & Hc).
cbn in *.
repeat split.
-
  rewrite not_empty_member in *.
  rewrite not_empty_member in Hne.
  destruct Hne as (x & Hm).
  cbn.
  exists (Build_IDEAL _ (principal x) (principal_is_ideal x)).
  repeat split; cbn.
  +
    apply principal_is_compact.
  +  
    now rewrite principal_subset.
-
  cbn.
  intros x y Hmx Hmy.
  destruct Hmx as (Hxc & Hsub).
  apply compact_is_principal in Hxc.
  destruct Hxc as (Maxx & Heq).
  rewrite Heq in Hsub.
  rewrite principal_subset in Hsub; auto.
  destruct Hmy as (Hyc & Hsub').
  apply compact_is_principal in Hyc.
  destruct Hyc as (Maxy & Heq').
  rewrite Heq' in Hsub'.
  rewrite principal_subset in Hsub'; auto.
  destruct (Hd _ _ Hsub Hsub') as (z & Hmz & Hlexz & Hleyz).
  exists (Build_IDEAL _ (principal z) (principal_is_ideal z)).
  repeat split; cbn.
  +
    apply principal_is_compact.
  +
    now rewrite principal_subset.
  +
    rewrite <- subset_principal_iff.
    intros w Hw.
    rewrite Heq in Hw.
    assert (Hmw :  (member (principal Maxx) w)) by exact Hw.
    rewrite member_principal_iff in Hmw.
    eapply poset_trans; eauto.
  +
    rewrite <- subset_principal_iff.
    intros w Hw.
    rewrite Heq' in Hw.
    assert (Hmw :  (member (principal Maxy) w)) by exact Hw.
    rewrite member_principal_iff in Hmw.
    eapply poset_trans; eauto.
Qed.


Lemma lub_le_compacts{P : PPO}: forall c : IDEAL P,
  c =
  cpo_lub (compacts_le (P:=  (ideals_cpo P)) c).
     
Proof.
intro c.
specialize (compacts_le_directed (P:= P) c) as Hd.
cbn in *.
unfold Ideal.ideals_cpo_obligation_1.
destruct (oracle
(is_directed (P:= ideals_poset P)
   (compacts_le (P:= ideals_cpo P) c))); [| contradiction].

apply ideal_equal.
apply set_equal.
split; intro Hm.
-
  exists (principal x); split; [ | apply member_principal].
  exists (Build_IDEAL _ (principal x) (principal_is_ideal x)).
  cbn; repeat split; auto.
  + 
    apply principal_is_compact.
  +
    cbn.
    rewrite  principal_subset; auto.
    now destruct c as (S & Hd' & Hc).
-
  destruct Hm as (S & Hm & HM).
  cbn in *.
  destruct Hm as (I & (HcI & Hsub)& HeqS).
  cbn in *.
  rewrite <- HeqS in Hsub.
  apply (Hsub _ HM).
Qed.
  
    
 Definition ideals_algebraic (P : PPO) : ALGEBRAIC :=
{|
  algebraic_cpo := ideals_cpo P;
  algebraic_dir := compacts_le_directed;
  algebraic_lub := lub_le_compacts
|}.


      
Lemma ppo_isomorphic_compact_le{P P' : CPO}
    (i : Poset_ISOMORPHISM P P'):
    forall c, fmap (compacts_le (P := P') (to i c)) (from i) =
              compacts_le (P:= P) c.
Proof.
intro c; apply set_equal; split; intro Hm.
-
  destruct Hm as (y & (Hc & Hle) & Heq); subst.
  split.
  +
    replace y with (to i (from i y)) in Hc; [| apply to_from].
    now apply (@isomorphic_compact_inv) with (i := ppo_iso_cpo_iso i). 
  +  
     replace c with (from i (to i c)) ; [| apply from_to].
    now apply from_mono.
-      
  destruct Hm as (Hc & Hle).
  exists (to i x); split.
  + 
    split.
    *
      now apply (@isomorphic_compact) with (i := ppo_iso_cpo_iso i).
    *
      now apply to_mono.
  +
    symmetry.
    apply from_to.
 Qed.  

 Lemma is_lub_fmap_compacts_le{P1 P2:CPO}: 
 forall (f : P1 -> P2) (x:P1),
 is_monotonic_on f (fun x => is_compact x) -> 
 is_compact x ->
 is_lub (fmap (compacts_le x) f) (f x).
 Proof.
 intros f x Hm Hc.
 split.
 - 
  intros y Hmy.
  destruct Hmy as (z & (Hmcz & Hlez) & Heq); subst.
  apply Hm; auto.
 -
  intros y Hu.
  apply Hu.
  exists x; repeat split; auto.
  apply poset_refl.
 Qed.  
  


 Program Definition compacts_poset (A : ALGEBRAIC) : Poset :=
   {|
   poset_carrier := {x : A | is_compact x};
   poset_le := fun x y => proj1_sig x <= proj1_sig y
   |}.


Next Obligation.
cbn; intros.
apply poset_refl.
Qed.

Next Obligation.
cbn.
intros.
eapply poset_trans; eauto.
Qed.

Next Obligation.
cbn.
intros.
destruct x, y ; cbn in *.
assert (Heq: x =x0) by (apply poset_antisym; auto); subst.
f_equal.
apply proof_irrelevance.
Qed.

Program Definition compacts_ppo (A : ALGEBRAIC) : PPO :=
  {|
  ppo_poset := compacts_poset A;
  ppo_bot := (exist _ ppo_bot bot_is_compact);
  |}.
 
Next Obligation.
intros.
cbn.
apply ppo_bot_least.
Qed.


