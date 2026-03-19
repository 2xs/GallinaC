From Stdlib Require Import List Arith Lia.
Import ListNotations.
From Stdlib Require Export Morphisms.
From GallinaC.Utils Require Import Algebra.
From GallinaC.Imp Require Import Heap Store Primitives.
From GallinaC.Seplog Require Export Pred.
Import Heap.Facts Store.Facts.

Local Open Scope separation_scope.
Local Open Scope heap_scope.
Local Open Scope store_scope.
Local Open Scope state_scope.

Definition lift {St Hp} (P: Prop) : Pred (State St Hp) :=
  fun s => P /\ (Primitives.heap s) = $0.

Notation "[| P |]" := (lift P) : state_scope.

Definition Emp {St Hp}: Pred (State St Hp) := fun s => (Primitives.heap s) = $0.

Notation "$$0" := Emp: state_scope.

Lemma lift_impl {St: Store} {Hp: Heap} : forall P Q, (P -> Q) -> |- ([| P |]: Pred (State St Hp)) ===> [| Q |].
Proof.
  intros P Q Hi s Hs.
  destruct Hs; split; eauto.
Qed.

Lemma Emp_lift_True {St: Store} {Hp: Heap}: |- (@Emp St Hp) <==> [|True|].
Proof.
  intros s.
  constructor; intros Hs.
  - constructor; auto.
  - destruct Hs; auto.
Qed.

Definition star {St: Store} {Hp: Heap} (P Q: Pred _) : Pred (State St Hp) :=
  fun s => exists s1 s2,
      store s = store s1 /\
        store s = store s2 /\
        (heap s1) $+ (heap s2) = Some (heap s) /\
        P s1 /\ Q s2.

Infix "**" := star (at level 40, left associativity): state_scope.

Lemma star_comm :
  forall {St: Store} {Hp: Heap} (P Q: Setof (State St Hp)), |- P ** Q <==> Q ** P.
Proof.
  intros St Hp P Q.
  intros s; constructor; intros STAR.
  - destruct STAR as (s1 & s2 & ST1 & ST2 & EQHp & HP & HQ).
    exists s2, s1; repeat split; eauto with seplog.
    now rewrite op_comm.
  - destruct STAR as (s1 & s2 & EQSt1 & EQSt2 & EQHp & HP & HQ).
    exists s2, s1; repeat split; eauto with seplog.
    now rewrite op_comm.
Qed.

Lemma star_assoc {St: Store} {Hp: Heap} :
  forall (P Q R: Setof (State St Hp)),
    |- P ** Q ** R <==> P ** (Q ** R).
Proof.
  intros P Q R s;
    constructor; intros STAR.
  - destruct STAR as (s1 & s2 & EQSt1 & EQSt2 & EQHp1 &
                        (s3 & s4 & EQSt3 & EQSt4 & EQHp2 & HP & HQ) & HR).
    rewrite <- EQSt1 in EQSt3, EQSt4.
    assert (SEP_2_4: heap s2 $/= heap s4) by eauto with seplog.
    assert (SEP_2_3: heap s2 $/= heap s3) by eauto with seplog.
    assert (SEP_3_4: heap s3 $/= heap s4) by eauto with seplog.
    pose proof SEP_2_4 as H;
      destruct H as (h_2_4 & EQ24).
    exists s3, (mkState (store s) h_2_4).
    split; [ congruence | cbn ].
    split; [ congruence | ].
    split; [ | ].
    {
      specialize (op_assc (heap s3) (heap s2) (heap s4)).
      rewrite (op_comm (heap s3) (heap s2)).
      rewrite op_assc.
      rewrite EQ24; cbn.
      rewrite EQHp2; cbn.
      rewrite op_comm, EQHp1.
      now intros PROOF; symmetry in PROOF.
    }
    split; [ assumption | ].
    exists s4, s2; cbn.
    split; [ congruence | ].
    split; [ congruence | ].
    split; [ now rewrite op_comm | split; auto ].
  - destruct STAR as ( s1 & s2 & EQSt1 & EQSt2 & EQHp1 & HP & ( s3 & s4 & EQSt3 & EQSt4 & EQHp2 & HQ & HR ) ).
    assert (SEP_1_4: heap s1 $/= heap s4) by eauto with seplog.
    assert (SEP_1_3: heap s1 $/= heap s3) by eauto with seplog.
    assert (SEP_3_4: heap s3 $/= heap s4) by eauto with seplog.
    pose proof SEP_1_4 as H;
      destruct H as (h_1_4 & EQ14).
    pose proof SEP_1_3 as H;
      destruct H as (h_1_3 & EQ13).
    pose proof SEP_3_4 as H;
      destruct H as (h_3_4 & EQ34).
    exists (mkState (store s) h_1_3), s4; cbn.
    split; [ congruence | ].
    split; [ congruence | ].
    split; [ | split; auto ].
    {
      specialize (op_assc (heap s4) (heap s1) (heap s3)).
      rewrite EQ13; cbn.
      rewrite (op_comm (heap s4) (heap s1)).
      rewrite op_assc.
      rewrite (op_comm (heap s4) (heap s3)).
      rewrite EQHp2; cbn.
      rewrite EQHp1.
      rewrite op_comm.
      intros PROOF.
      now symmetry in PROOF.
    }
    exists s1, s3; cbn.
    split; [ congruence | ].
    split; [ congruence | ].
    split; [ auto | split; auto ].
Qed.

Lemma Emp_neutral_star_l {St Hp}: forall (P: Pred (State St Hp)),
    |- $$0 ** P <==> P.
Proof.
  intros P.
  eapply impl_antisym_taut.
  - intros s ( s1 & s2 & EQSt1 & EQSt2 & EQHp & HEmp & HP ).
    unfold Emp in HEmp.
    rewrite HEmp, op_id_l in EQHp.
    destruct s, s2;
      cbn in EQSt2, EQHp; congruence.
  - intros s HP.
    exists (mkState (store s) $0).
    exists (mkState (store s) (heap s)).
    cbn.
    split; [ reflexivity | ].
    split; [ reflexivity | ].
    split; [ apply op_id_l | ].
    split; [ unfold Emp; reflexivity | destruct s; now eauto ].
Qed.

Lemma Emp_neutral_star_r {St Hp}: forall (P: Pred (State St Hp)), |- P ** $$0 <==> P.
  intros P s; split; intros H.
  apply star_comm in H; now apply Emp_neutral_star_l.
  apply star_comm; now apply Emp_neutral_star_l.
Qed.

Lemma lift_and {St: Store} {Hp: Heap}: forall (P Q: Prop),
    |- ([| P |] ** [| Q |] <==> [| P /\ Q |] : Pred (State St Hp)).
  intros P Q.
  apply impl_antisym_taut; intros s Hs.
  -
    destruct Hs as (s1 & s2 & Hr1 & Hr2 & HPartition & (HP1 & Hm1) & (HP2 & Hm2)).
    rewrite Hr1, Hr2 in *.
    split; auto.
    rewrite Hm1 in HPartition.
    rewrite Hm2 in HPartition.
    rewrite op_id_l in HPartition.
    congruence.
  -
    destruct Hs as ((HP & HQ) & Hm).
    exists (mkState (store s) $0), (mkState (store s) $0).
    split; [ reflexivity | ].
    split; [ reflexivity | ].
    split; [ cbn; rewrite Hm; apply op_id_l; congruence | ].
    split; [ now split | now split ].
Qed.

Lemma np_p_false {St Hp} P:
    |- (([| ~P |] ** [| P |]) <==> [|False|] : Pred (State St Hp)).
Proof.
  apply impl_antisym_taut.
  - intros s ( s1 & s2 & Hst1 & Hst2 & HPartition & HnP & HP ).
    destruct HnP as [ HnP Hs1 ].
    destruct HP as [ HP Hs2 ].
    constructor; [ contradiction | ].
    rewrite Hs1, Hs2 in HPartition.
    symmetry.
    rewrite op_id_l in HPartition; congruence.
  - intros ( st & hp ) ( HFalse & HEmp ).
    contradiction.
Qed.

Lemma p_p_p {St Hp} P :
    |- ( [| P |] ** [| P |] <==> [| P |] : Pred (State St Hp) ).
Proof.
  intros s.
  apply impl_antisym.
  intros ( s1 & s2 & Hst1 & Hst2 & HPartition & ( HP & HEmp1 ) & ( _ & HEmp2 ) ).
  rewrite HEmp1, HEmp2 in HPartition.
  rewrite op_id_l in HPartition.
  constructor; [ assumption | congruence ].
  intros ( HP & HEmp1 ).
  exists s, s.
  split; [ reflexivity | ].
  split; [ reflexivity | ].
  split; [ rewrite HEmp1; apply op_id_l | ].
  split; constructor; auto.
Qed.

Lemma Ex_falso {St Hp} (P: Pred (State St Hp)):
  |- [| False|] ===> P.
Proof.
  intros s Hs; now destruct Hs.
Qed.

Lemma cond_Ex_falso {St Hp} (P Q R: Pred (State St Hp)) :
  P = Q ** [| False|] ->
      |- P  ===> R.
Proof.
  intros Heq s Hs; subst.
  destruct Hs as
    (_ & _ & _ & _ & _ & _ & (HFalse & _)).
  contradiction.
Qed.

Lemma star_cancel_l {St Hp} (P Q R: Pred (State St Hp)):
    (|- P ===> Q) -> |- (R ** P) ===> (R ** Q).
Proof.
  intros Himp s (s1 & s2 & Hst1 & Hst2 & HPartition & HR & HP).
  exists s1,s2; repeat split; eauto with mem.
  now apply Himp.
Qed.

Lemma star_cancel_r {St Hp} (P Q R: Pred (State St Hp)):
    (|- P ===> Q) -> |- (P ** R) ===> (Q ** R).
Proof.
  intros Himp s Hs.
  apply star_comm; apply star_comm in Hs.
  eapply star_cancel_l; eauto.
Qed.

Definition heapless {St Hp} (P: Pred (State St Hp)) : Prop :=
  forall s, P s -> heap s = $0.

Lemma heapless_star {St Hp} (P Q: Pred (State St Hp)) : heapless P -> heapless Q -> heapless (P ** Q).
Proof.
  intros HheaplessP HheaplessQ s ( s1 & s2 & Hst1 & Hst2 & HPartition & HP & HQ ).
  specialize (HheaplessP _ HP).
  specialize (HheaplessQ _ HQ).
  rewrite HheaplessP, HheaplessQ in HPartition.
  symmetry; rewrite op_id_l in HPartition; congruence.
Qed.

Lemma Emp_weakest_heapless {St Hp} (P: Pred (State St Hp)) :
  heapless P -> |- P ===> $$0.
Proof.
  intros Hheapless s HP.
  now apply Hheapless.
Qed.

Lemma heapless_lift {St Hp} P : heapless ([| P |]: Pred (State St Hp)).
Proof.
  now intros s ( HP & Hheap ).
Qed.

Definition indep_store {St Hp} (P: Pred (State St Hp)) : Prop :=
  forall s1 s2, heap s1 = heap s2 -> P s1 -> P s2.

Lemma indep_store_lift {St Hp} P:
    @indep_store St Hp [| P |].
Proof.
  intros s1 s2 Hm (HP & Hheap); split; auto.
  congruence.
Qed.

Lemma star_semicancel_l {St Hp} (P Q R: Pred (State St Hp)):
    heapless R ->
    (|- R ** P  ===> Q) -> |- (R ** P) ===> (R ** Q).
Proof.
  intros Hheapless Himp s Hs.
  destruct Hs as (s1 & s2 & Hr1 & Hr2 & HPartition & HR & HP).
  specialize HR as Hr'.
  apply Hheapless in Hr'.
  exists (mkState (store s1) (heap s1)), (mkState (store s) (heap s2)); cbn.
  split; [ congruence | ].
  split; [ congruence | ].
  split; [ assumption | ].
  split; [ destruct s1; now apply HR | ].
  apply Himp.
  rewrite Hr' in HPartition.
  rewrite op_id_l in HPartition;
    inversion HPartition; rewrite H0.
  exists (mkState (store s1) (heap s1)), (mkState (store s2) (heap s2)); cbn.
  split; [ congruence | ].
  split; [ congruence | ].
  split; [ rewrite Hr'; rewrite H0; apply op_id_l | ].
  split; [ destruct s1; assumption | destruct s2; assumption ].
Qed.

Lemma star_semicancel_r {St Hp} (P Q R: Pred (State St Hp)):
    heapless R ->
    (|- P ** R ===> Q) -> |- (P ** R) ===> (Q ** R).
Proof.
  intros Hheapless Himp s Hs.
  specialize (Himp s Hs).
  exists s, (mkState (store s) $0); cbn.
  split; [ congruence | ].
  split; [ congruence | ].
  split; [ now rewrite op_id_r | ].
  split; [ assumption | ].
  destruct Hs as ( s1 & s2 & Hst1 & Hst2 & HPartition & HP & HR ).
  specialize (Hheapless _ HR).
  rewrite Hheapless in HPartition.
  rewrite op_id_r in HPartition.
  injection HPartition.
  intros EQ.
  rewrite <- Hheapless, Hst2.
  destruct s2; assumption.
Qed.

Lemma star_mono {St Hp} (P Q R T: Pred (State St Hp)):
      |- P ===> Q -> |- R ===> T -> |- P**R ===> Q**T.
Proof.
  intros HPQ HRT s HPR.
  destruct HPR as (
      s1 & s2 & Hst1 & Hst2 & HPartition & HP & HR).
  exists s1,s2; repeat split; eauto with mem.
  now apply HPQ.
  now apply HRT.
Qed.

Lemma star_weaken_l {St Hp} (P Q R: Pred (State St Hp)):
    heapless Q ->
      |- P ===> R -> |- Q ** P  ===> R.
Proof.
  intros Hheapless HPR s HQP.
  destruct HQP as
    (s1 & s2 & Hst1 & Hst2 & HPartition & HQ & HP).
  apply HPR.
  specialize (Hheapless s1 HQ).
  destruct s1 as [ st1 hp1 ];
    cbn in Hheapless, Hst1, Hst2, HPartition, HQ.
  rewrite Hheapless in HQ, HPartition.
  rewrite op_id_l in HPartition.
  injection HPartition as EQ.
  assert (s2 = s) by (destruct s2, s; f_equal; [ now cbn in Hst2 | now cbn in EQ ]);
    subst.
  assumption.
Qed.

Lemma star_weaken_r {St Hp} (P Q R: Pred (State St Hp)):
  heapless Q ->
      |- P ===> R -> |- P ** Q ===> R.
Proof.
  intros Hheapless HPR s HPQ.
  destruct HPQ as
    (s1 & s2 & Hst1 & Hst2 & HPartition & HP & HQ).
  apply HPR.
  specialize (Hheapless _ HQ).
  rewrite Hheapless in HPartition.
  rewrite op_id_r in HPartition;
    injection HPartition as EQ.
  destruct s.
  cbn in Hst1, EQ.
  rewrite Hst1. rewrite <- EQ.
  destruct s1; apply HP.
Qed.

Lemma eq_star_rw {St Hp} {A:Type} (a b: A) (P: A -> Pred (State St Hp)):
      |- [| a = b |] ** P a ===> P b.
Proof.
  intros s HeqP.
  destruct HeqP as
    (s1 & s2 & Hst1 & Hst2 & HPartition & (Heqab & Hheapless) & HP);
    subst.
  rewrite Hheapless in HPartition.
  rewrite op_id_l in HPartition;
    injection HPartition as EQ.
  assert (s2 = s) by (destruct s, s2; cbn in Hst2, EQ; congruence);
    now subst.
Qed.

Lemma Exists_star_left_r {St Hp} {A:Type} (P: A -> Pred (State St Hp)) (Q: Pred (State St Hp)):
      |- (Exists (x:A), P x) ** Q ===> Exists (x:A), ((P x) ** Q).
Proof.
  intros s Hs.
  destruct Hs as (s1 & s2 & Hst1 & Hst2 & HPartition & (x & HPx) & HQ).
  exists x,s1,s2; repeat split ; eauto with mem.
Qed.

Lemma Exists_star_right_l {St Hp} {A:Type} (P: Pred (State St Hp)) (Q: A -> Pred (State St Hp)):
    |- (Exists (x:A), P ** (Q x)) ===> P ** (Exists (x:A), Q x).
Proof.
  intros s Hs.
  destruct Hs as (x & (s1 & s2 & Hr1 & Hr2 & HPartition & HP & HQ)).
  exists s1, s2; repeat split; eauto with mem.
  now exists x.
Qed.

Lemma Exists_star_left_l{St Hp} {A:Type} (P: A -> Pred (State St Hp)) (Q: Pred (State St Hp)):
      |- (Exists (x:A), ((P x) ** Q)) ===> (Exists (x:A), P x) ** Q.
Proof.
  intros s Hs.
  destruct Hs as (x & (s1 & s2 & Hst1 & Hst2 & HPartition & HPx & HQ)).
  exists s1,s2 ; repeat split ; eauto with mem.
  now exists x.
Qed.

Lemma Exists_star_right_r {St Hp} {A:Type} (P: Pred (State St Hp)) (Q: A -> Pred (State St Hp)):
    |- P ** (Exists (x:A), Q x) ===> (Exists (x:A), P ** (Q x)).
Proof.
  intros s Hs.
  destruct Hs as (s1 & s2 & Hr1 & Hr2 & HPartition & HP & ( x & Hqx)).
  exists x, s1,s2 ; repeat split; eauto with mem.
Qed.

Lemma Exists_star_left {St Hp} {A:Type} (P: A -> Pred (State St Hp)) (Q: Pred (State St Hp)):
    |- (Exists (x:A), ((P x) ** Q)) <==> (Exists (x:A), P x) ** Q.
Proof.
  apply impl_antisym_taut; [ apply Exists_star_left_l | apply Exists_star_left_r ].
Qed.

Lemma Exists_star_right {St Hp} {A:Type} (P: Pred (State St Hp)) (Q: A -> Pred (State St Hp)):
    |- (Exists (x:A), P ** (Q x)) <==> P ** (Exists (x:A), Q x).
Proof.
  apply impl_antisym_taut; [ apply Exists_star_right_l | apply Exists_star_right_r].
Qed.

Lemma cond_star_cancel_l {St Hp} (P Q R U V: Pred (State Hp St)):
    |- U <==> R ** P -> |- V <==> R ** Q -> |- P ===> Q ->
    |- U ===> V.
Proof.
  intros HURP HVRQ HPQ s HU.
  destruct (HVRQ s) as [ _ HRQV ].
  apply HRQV.
  destruct (HURP s) as [ HURPs _ ].
  specialize (HURPs HU) as HRP.
  eapply star_cancel_l; eauto.
Qed.

Lemma cond_star_weaken_l {St Hp} (P Q R T: Pred (State Hp St)):
  heapless Q -> |- T <==> Q ** P ->
      |- P ===> R -> |- T ===> R.
Proof.
  intros Hheapless HTQP HPR s HT.
  assert (HProof := star_weaken_l _ _ _ Hheapless HPR).
  destruct (HTQP s) as [ HQP _ ].
  apply (HProof s (HQP HT)).
Qed.

Lemma cond_star_semicancel_l {St Hp} (P Q R U V: Pred (State Hp St)):
  heapless R ->
  |- U <==> R ** P -> |- V <==> R ** Q ->
      |- U ===> Q -> |- U ===> V.
Proof.
  intros Hheapless HURP HVRQ HUQ s HU.
  apply HVRQ.

  exists (mkState (store s) $0), s; cbn.
  repeat split; eauto with seplog.
  destruct (HURP s) as [ HRP _ ].
  specialize (HRP HU).
  destruct HRP as ( s1 & s2 & Hst1 & Hst2 & HPartition & HR & HP ).
  destruct s1 as [ store1 heap1 ]; cbn in HR, Hst1.
  now specialize (Hheapless _ HR); cbn in Hheapless; rewrite Hheapless, <- Hst1 in HR.
  now eapply HUQ.
Qed.

Definition wand {St Hp} (P Q : Pred (State St Hp)) : Pred (State St Hp) :=
  fun s => forall s' hp, P s' -> heap s $+ heap s' = Some hp ->
                        store s' = store s ->
                        Q (mkState (store s') hp).

Infix "-*" := wand (at level 70, right associativity): state_scope.

Lemma wand_elim {St Hp} (P Q R: Pred (State St Hp)):
    |- (P ** Q) ===> R -> |- P ===> (Q -* R).
Proof.
  intros HPQR s HP s' hp HQ HPartition Hst.
  eapply HPQR.
  exists s, s'; cbn; repeat split; eauto with mem.
Qed.

Lemma wand_intro {St Hp} (P Q R: Pred (State St Hp)):
      |- P ===> (Q -* R) -> |- (P ** Q) ===> R.
Proof.
  intros HPQR s HPQ.
  destruct HPQ as ( s1 & s2 & Hst1 & Hst2 & HPartition & HP & HQ ).
  specialize (HPQR s1 HP s2 (heap s) HQ HPartition ltac:(congruence)).
  rewrite <- Hst2 in HPQR.
  destruct s; apply HPQR.
Qed.

Lemma star_wand_mp {St Hp} (P Q R: Pred (State St Hp)):
      |- (P ** (P -* Q) ===> Q).
Proof.
  intros s Hs.
  destruct Hs as (s1 & s2 & Hst1 & Hst2 & HPartition & HP & Hwand).
  destruct s as [ st hp ]; cbn in Hst1, Hst2, HPartition.
  rewrite op_comm in HPartition.
  specialize (Hwand _ _ HP HPartition ltac:(congruence)).
  now rewrite Hst1.
Qed.

Lemma indep_regs_star {St Hp} (P Q: Pred (State St Hp)):
    indep_store P -> indep_store Q -> indep_store (P ** Q).
Proof.
  intros HindepP HindepQ s s' Heqm Hs.
  destruct Hs as (s1 & s2 & Hr1 & Hr2 & HPartition & HP1 & HP2).
  rewrite Heqm in HPartition.
  exists (mkState (store s') (heap s1)),
    (mkState (store s') (heap s2)); cbn.
  repeat split; eauto with mem.
  - eapply HindepP in HP1; eauto with mem.
  - eapply HindepQ in HP2; eauto with mem.
Qed.
