From Coq Require Import IndefiniteDescription ProofIrrelevance.
From Corec Require Export Algebraic.

Record COMPLETION (P : PPO) : Type :=
{
  alg :> ALGEBRAIC;
  inject : P -> alg;
  inject_bot : inject ppo_bot = ppo_bot;
  inject_bimono : forall p p', p <= p' <-> inject p <= inject p';
  inject_compact : forall p, is_compact (inject p);
  rev_inj : alg -> P;
  rev_inj_iff : forall cc p, is_compact cc -> 
  (rev_inj cc = p <-> inject p = cc)
}.    


Arguments alg {_} _.
Arguments inject {_ _}   _.
Arguments inject_bot {_} _.
Arguments inject_bimono {_}. 
Arguments inject_compact {_ _} _.
Arguments rev_inj {_ _} _.
Arguments rev_inj_iff {_} _ _ _ _.


Lemma inject_injective{P:PPO}: forall (A : COMPLETION P),
    is_injective  (inject (c := A)).
Proof.
intro A.
apply bimono_injective.
unfold is_bimonotonic, is_monotonic,is_rev_monotonic; split; intros.
-  now rewrite <- inject_bimono.
-  now rewrite <- inject_bimono in H.
Qed.

Lemma inject_compacts{P:PPO} :
  forall (A : COMPLETION P) (cc : A),
    is_compact  cc <-> exists p, cc = inject  p.
Proof.
intros A cc.
split ; intro Hs.
-
  exists (rev_inj cc).
  symmetry.
  now rewrite <-rev_inj_iff.
-
  destruct Hs as (p & Heq).
  subst.
  apply inject_compact.
Qed.

Lemma rev_inj_bimono{P:PPO} :
   forall (A : COMPLETION P) (cc cc': A),
    is_compact cc -> is_compact cc' ->
      (cc <= cc' <-> rev_inj cc <= rev_inj cc').         
Proof.
intros A cc cc' Hc Hc'.  
remember  (rev_inj cc) as p.
remember  (rev_inj cc') as p'.
symmetry in Heqp,Heqp'.
rewrite rev_inj_iff in Heqp,Heqp'; auto.
rewrite <- Heqp, <-Heqp'.
split ; apply inject_bimono.
Qed.

Lemma rev_inj_injective{P:PPO}{A : COMPLETION P} :
forall (cc cc': A),
is_compact cc -> is_compact cc' -> rev_inj cc = rev_inj cc' -> 
cc = cc'.
Proof.
intros cc cc' Hc Hc' Heq.
apply poset_antisym.
-  
  rewrite rev_inj_bimono; auto.
  rewrite Heq; apply poset_refl.
-  
  rewrite rev_inj_bimono; auto.
  rewrite Heq; apply poset_refl.
Qed.  


Lemma inject_rev_inj{P:PPO}: forall (M:COMPLETION P),
forall cc, is_compact cc ->
inject (c := M)  (rev_inj cc) = cc.
Proof.
intros M cc Hc.
now rewrite <- rev_inj_iff.
Qed.


Lemma rev_inj_inject{P:PPO}: forall (M:COMPLETION P),
forall cc, 
 rev_inj (c := M) (inject  cc) = cc.
Proof.
intros M cc.
rewrite rev_inj_iff; auto.
apply inject_compact.
Qed.


Definition ideal_completion (P : PPO) : COMPLETION P.
unshelve econstructor.
-
  exact (ideals_algebraic P).
-
  intro p.
  cbn.
  exact (Build_IDEAL _ (principal p) (principal_is_ideal p)).
-
  cbn.
  intro cc.
  destruct (oracle (is_compact (P := ideals_cpo P) cc)) as [Hc | Hc].
  +
   apply compact_is_principal in Hc.
   destruct (constructive_indefinite_description _ Hc) as (p & Heq).
   exact p.
  +
   exact ppo_bot.

-
  cbn.
 (* Set Printing Implicit.
  Set Printing Coercions.*)
  unfold ideal_bot.
  apply ideal_equal.
  cbn.
  now rewrite single_bot_is_principal_bot.
-
  split.
  +
    intros Hle.
    cbn.
    rewrite <- subset_principal_iff.
    intros y Hm.
    apply member_principal_iff in Hm.
    eapply poset_trans; eauto.
  +
    intro Hle.
    cbn in Hle.
    rewrite <- subset_principal_iff in Hle.
    apply Hle,member_principal.
-
  intros p S Hd Hle.
  specialize (principal_is_compact p) as Hc.  
  apply  (Hc _ Hd Hle).

-
  cbn.
  intros cc p Hc.
  destruct (oracle (is_compact  (P := ideals_cpo P) cc));
  [| exfalso; now apply n].
  remember ( constructive_indefinite_description
     _
     (compact_is_principal cc i)) as ci.
  destruct ci.
  clear Heqci.  
  destruct cc; cbn in *; subst.
  split; subst; intros Heq; subst.
  +
     now apply ideal_equal.
  +
    injection Heq; intros; subst.
    now apply principal_injective.
Qed.    




Program Definition self_completion (A:ALGEBRAIC) : COMPLETION (compacts_ppo A):=
{|
 alg := A;
 inject :=  fun (Hc : compacts_ppo A) => proj1_sig Hc;
 rev_inj := 
   fun a => 
     match (oracle (is_compact a)) with
      left H => (exist _ a H)
      | right _ => ppo_bot
     end
|}.

Next Obligation.
reflexivity.
Qed.

Next Obligation.
intros.
split; tauto.
Qed.

Next Obligation.
intros.
now destruct p.
Qed.

Next Obligation.
cbn.
intros.
destruct (oracle (is_compact cc)); 
 [| exfalso; now apply n].
destruct p; cbn.
split.
-
   intros.
   injection H0; intros ; now subst.
-
   intros Heq ;subst.
   f_equal.
   apply proof_irrelevance.   
Qed.

    
