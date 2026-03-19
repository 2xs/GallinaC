From Stdlib Require Import
  FunctionalExtensionality PropExtensionality List Lia Arith NArith.
Import ListNotations.
From GallinaC.Utils Require Export Algebra.
From GallinaC.Seplog Require Export ListAssertion.
Import Store.Facts Heap.Facts.

Local Open Scope state_scope.
Local Open Scope heap_scope.
Local Open Scope separation_scope.

Definition indep_var {St: Store.Store} {Hp: Heap} (P: Pred (State St Hp)) v: Prop :=
  forall s s', heap s = heap s'->
               (forall w x, v <> w -> BindsTo w x (store s) <-> BindsTo w x (store s')) ->
               P s -> P s'.

Lemma indep_var_star {St: Store} {Hp: Heap} (P Q: Pred (State St Hp)) v:
  indep_var P v -> indep_var Q v -> indep_var (P ** Q) v.
Proof.
  intros Hi1 Hi2 s s' Hheap Hvar Hs.
  destruct Hs as (s1 & s2 & Hst1 & Hst2 & HPartition & HP & HQ).
  exists
    {| store := store s1; heap := heap s1|},
    {| store := store s2; heap := heap s2|}; cbn.
  (* TODO return to after IR *)
  (*     unfold reg, mem in *; cbn; repeat split; f_equal; auto; try congruence. *)
  (*   - *)
  (*     now inversion HPartition. *)
  (*   - *)
  (*     inversion HPartition. *)
  (*     intros HPointsTo. *)
  (*     rewrite <- Hmem in HPointsTo. *)
  (*     eapply (H4 a v); eauto. *)
  (*   - rewrite <- Hmem. *)
  (*     inversion HPartition. *)
  (*     eapply H4; eauto. *)
  (*   - apply (Hi1 s1); auto. *)
  (*   - eapply (Hi2 s2); auto. *)
  (* Qed. *)
Abort.

(* Definition indep_reg2(P: Pred State) : Prop := *)
(*   forall s s', memory s = memory s'-> *)
(*                reg1 s = reg1 s' -> P s -> P s'. *)

(* Lemma indep_reg2_star: forall p q, *)
(*     indep_reg2 p -> indep_reg2 q -> indep_reg2 (p ** q). *)
(* Proof. *)
(*   intros p q Hi1 Hi2 s s' Hmem Hreg1 Hs. *)
(*   destruct Hs as (s1 & s2 & Hr1 & Hr2 & HPartition & Hp & Hq). *)
(*   injection Hr1; injection Hr2; intros ; subst; clear Hr1 Hr2. *)
(*   exists *)
(*     {|reg1 := reg1 s1; reg2 := reg2 s'; memory := memory s1|}, *)
(*     {|reg1 := reg1 s2; reg2 := reg2 s'; memory := memory s2|}; *)
(*     unfold reg, mem in *; cbn; repeat split; f_equal; auto; try congruence. *)
(*   - now inversion HPartition. *)
(*   - inversion HPartition. *)
(*     rewrite <- Hmem. *)
(*     intros HPointsTo. *)
(*     eapply H4; eauto. *)
(*   - inversion HPartition. *)
(*     rewrite <- Hmem. *)
(*     eapply H4; eauto. *)
(*   - *)
(*     now apply Hi1 with (s := s1). *)
(*   - *)
(*     now apply Hi2 with (s := s2). *)
(* Qed. *)



Lemma indep_store_var {St Hp} (P: Pred (State St Hp)) v:
  indep_store P -> indep_var P v.
Proof.
  intros Hi s s' Heqm Heqr HP.
  now  apply (Hi s s').
Qed.

Lemma One_indep_store {St Hp} a v:
  @indep_store St Hp (a ||~> v).
Proof.
  intros s s' Heqhp HP.
  congruence.
Qed.

Definition var_equals {St Hp} v x: Pred (State St Hp) :=
  fun s => BindsTo v x (store s) /\ (heap s) = $0.

Notation " 'var=' v x" := (var_equals v x) (v at level 5, at level 70).

Lemma var_equals_rw {St Hp} v x y:
      |- (var= v x) ** [| x = y |] ===> ((var= v y): Pred (State St Hp)).
Proof.
  intros s Hs.
  destruct Hs as
    (s1 & s2 & Hst1 & Hst2 & HPartition & (Hvar & HEmpty1) & (Heq & HEmpty2));
    rewrite HEmpty1, HEmpty2 in HPartition.
  rewrite op_id_r in *.
  constructor; [ now subst; rewrite Hst1 | congruence ].
Qed.

Lemma heapless_var_equals {St Hp} v x:
  heapless ((var= v x): Pred (State St Hp)).
Proof.
  now intros s (Ha & Hb).
Qed.

Lemma var_equals_indep_other {St Hp} v w x (Hneq: v <> w):
  (@indep_var St Hp (var= v x) w).
Proof.
  unfold var_equals.
  intros s s' Hheap Hv (Hr & Hm0); split; [ | congruence ].
  apply Hv; [ congruence | assumption ].
Qed.

Lemma var_equals_star {St Hp} (P: Pred (State St Hp)) v x:
      |- (var= v x) ** P <==> fun s => BindsTo v x (store s) /\ P s.
Proof.
  eapply impl_antisym_taut; intros s Hm.
  -
    destruct Hm as (s1 & s2 & Hr1 & Hr2 & HPartition & (Hreg1 & Hs1) & HP).
    rewrite Hs1 in HPartition.
    rewrite <- Hr1 in Hreg1.
    rewrite op_id_l in *.
    assert (s2 = s) by (destruct s2, s; cbn in *; congruence); subst.
    split; auto.
  -
    destruct Hm as (Hreg1 & HP).
    exists ({| store := store s; heap := $0|}), s; cbn.
    split; [ reflexivity | ].
    split; [ reflexivity | ].
    split; [ now rewrite op_id_l | ].
    split; [ constructor; eauto | assumption ].
Qed.


(* TODO return to after IR *)
(* Lemma pre_read_var_eq {St Hp} (P: Pred (State St Hp)) v: *)
(*   |- (Exists r, (var= v r) ** (P r)) <==> fun s => P ( s) s. *)
(* Proof. *)
(*   intro P. *)
(*   apply set_equal ; intro s; unfold member; split; intro Hm. *)
(*   - *)
(*     destruct Hm as (r & Hex). *)
(*     rewrite reg1_equals_star in Hex. *)
(*     destruct Hex as (Heq & HP); now subst. *)
(*   - *)
(*     exists (reg1 s). *)
(*     rewrite reg1_equals_star; now split. *)
(* Qed. *)

Definition pre_write_var {St Hp} (vn: name) (p: Pred (State St Hp)) (r: memval): Pred (State St Hp) :=
  fun s => p {| store := Store.mutate_unchecked s.(store) vn r; heap := heap s |}.

Notation "[var x = r ]-* p" :=
  (pre_write_var x p r)
    (x at level 5,
      at level 70,
      format "[var  x  =  r ]-*  p").

Lemma wand_var_mono {St Hp} (P Q: Pred (State St Hp)) v r:
      |- P ===> Q ->
      |- [var v = r ]-* P ===>  [var v = r]-* Q.
Proof.
  intros Himp s Hm.
  unfold pre_write_var.
  now apply Himp.
Qed.

Lemma wand_var_indep_var {St Hp} {P: Pred (State St Hp)} v r :
  indep_var ([var v = r]-* P) v.
Proof.
  unfold pre_write_var, indep_var.
  intros [ st hp ] [ st' hp' ]; cbn;
    intros Heqhp;
    subst.
  (* TODO return to after IR *)
  (* now rewrite <- Heqm, <- Heqr2. *)
  (* Qed. *)
Admitted.



Lemma wand_var_var_star {St Hp} (P: Pred (State St Hp)) v r:
      |- [var v = r]-* ((var= v r) ** P) <==>
           [var v= r]-* P.
Proof.
  (* TODO return to after IR *)
  (*   unfold "[reg1= _ ]-*  _", "reg1= _", "**". *)
  (*   cbn. *)
  (*   intros p r. *)
  (*   unfold reg,mem; cbn. *)
  (*   apply impl_antisym; intros s Hm. *)
  (*   - *)
  (*     destruct Hm as (s1 & s2 & Hr1 & Hr2 & HPartition & (Hreg1 & Hs1) & Hp). *)
  (*     rewrite Hs1 in *. *)
  (*     apply Partition_is_empty_l in HPartition. *)
  (*     injection Hr1; injection Hr2 ; intros ; subst. *)
  (*     apply Equal_eq in HPartition. *)
  (*     rewrite <- HPartition,H,H0. *)
  (*     now replace s2 with *)
  (*       {| reg1:= reg1 s2; reg2 := reg2 s2; memory := memory s2|} in Hp by auto. *)
  (*   - *)
  (*     exists *)
  (*       {| reg1 := r ; reg2 := reg2 s; memory := $0 |}, *)
  (*       {| reg1 := r ; reg2 := reg2 s; memory := memory s |}; *)
  (*       cbn; repeat split; auto; *)
  (*       [ *)
  (*         apply Disjoint_empty_l *)
  (*       | *)
  (*         intros H; destruct H as [ HPointsTo | HPointsTo ]; *)
  (*         [ *)
  (*           now apply MapHeap.emp_spec in HPointsTo *)
  (*         | *)
  (*           auto *)
  (*         ] *)
  (*       ]. *)
  (* Qed. *)
Admitted.

Lemma indep_var_wand_var {St Hp} (P: Pred (State St Hp)) v (Hindep: indep_var P v) r:
      |- P <==> [var v = r]-* P.
Proof.
  (* TODO return to after IR *)
  (*   unfold "[reg1= _ ]-* _", indep_reg1. *)
  (*   intros P Ha r. *)
  (*   apply impl_antisym ; intros s Hm. *)
  (*   - *)
  (*     now apply Ha with (s := s). *)
  (*   - *)
  (*     now apply Ha with *)
  (*       (s := *)
  (*          {| reg1 := r; reg2 := reg2 s; memory := memory s |} ). *)
  (* Qed. *)
Admitted.

Lemma wand_var_elim {St Hp} (P Q: Pred (State St Hp)) v r
  (Hindep: indep_var P v) (Himp: |- (P ** (var= v r)) ===> Q):
      |- P ===>( [var v = r ]-* Q).
Proof.
  (* TODO return to after IR *)
  (*   intros r p q Hi Hh s Hs. *)
  (*   unfold pre_write_reg1. *)
  (*   apply Hh. *)
  (*   exists {| *)
  (*       reg1 := r; *)
  (*       reg2 := reg2 s; *)
  (*       memory := memory s *)
  (*     |}, *)
  (*     {| *)
  (*       reg1 := r; *)
  (*       reg2 := reg2 s; *)
  (*       memory := $0 *)
  (*     |}; repeat split; cbn; auto; *)
  (*     [ *)
  (*       apply Disjoint_empty_r *)
  (*     | *)
  (*       intros H; destruct H as [ HPointsTo | HPointsTo ]; auto; *)
  (*       now apply MapHeap.emp_spec in HPointsTo *)
  (*     | *)
  (*       now apply (Hi s) *)
  (*     ]. *)

  (* Qed. *)
Admitted.

Lemma wand_var_intro {St Hp} (P Q: Pred (State St Hp)) v r
  (Himp: |- P ===>( [var v = r ]-*  Q)):
      |- (P ** (var= v r)) ===> Q.
Proof.
  (* TODO return to after IR *)
  (*   intros r p q Hh s Hs. *)
  (*   destruct Hs as (s1 & s2 & Hr1 & Hr2 & HPartition & Hp & *)
  (*                     (Hr & Hs2)); unfold mem in *; *)
  (*     injection Hr1 ; injection Hr2 ; intros; subst. *)
  (*   rewrite Hs2 in *. *)
  (*   apply Partition_is_empty_r in HPartition. *)
  (*   apply Equal_eq in HPartition. *)
  (*   specialize (Hh _ Hp). *)
  (*   unfold pre_write_reg1 in Hh. *)
  (*   rewrite <- H0, <-H1, HPartition in Hh. *)
  (*   exact Hh. *)
  (* Qed. *)
Admitted.

Lemma wand_var_wand_var {St Hp} (P: Pred (State St Hp)) v r1 w r2:
      |- [var v = r1]-*([var w = r2]-* P) <==>
           [var w = r2]-*([var v= r1]-* P).
Proof.
  (* TODO return to after IR *)
  (* intros; reflexivity. *)
  (* Qed. *)
Abort.


Notation " a ---> x" :=
  (fun s => (a |-> x) $<= (heap s)) (at level 20).

Lemma two_succ_pts_snd {St Hp} (P: Pred (State St Hp)) a v a':
      |- (a ||~> (v, a'))  ** P
           ===>
           (Addr.shift_fw a 1%N) ---> a'.
Proof.
  (* TODO return to after IR *)
  (*   intros r c a p s Hs. *)
  (*   destruct Hs as (s1 & s2 & Hr1 & Hr2 & HPartition & *)
  (*                     Htwo & Hp). *)
  (*   unfold Two in Htwo. *)
  (*   rewrite Htwo in *. *)
  (*   eapply Partition_PointsTo_iff; eauto. *)
  (*   left. *)
  (*   apply HFacts.two_spec. *)
  (*   now constructor. *)
  (* Qed. *)
Abort.

Lemma pre_read_addr_eq {St Hp} a (P: _ -> Pred (State St Hp)):
      |- (Exists a', (a ---> a') && P a') <==>
           fun s => exists a', s.(heap) = a |-> a'  /\ P a' s.
Proof.
  apply impl_antisym_taut; intros s Hm;
    destruct Hm as (a' & Haa' & Hpa').
Abort.

Definition write_addr_wp {St Hp} (a:Addr.t) v (p : Pred (State St Hp)) :=
  (Exists x, (a ||~> x))**((a ||~> v) -* p).

Lemma One_star_mem {St Hp} a v (P: Pred (State St Hp)):
      |- (a ||~> v ** P) ===> a ---> v.
Proof.
  intros s Hs.
  destruct Hs as  (s1 & s2 & Hr1 & Hr2 & HPartition & HP & HQ).
  exists (heap s2).
  now rewrite <- HP.
Qed.

(* Lemma One_star_pred {St Hp} a v (P: Pred (State St Hp)): *)
(*       |-  (a ||~> v ** P)   ===> *)
(*             fun s =>  P {| *)
(*                           store := store s; *)
(*                           heap := Heap.free_unchecked (heap s) a *)
(*                         |}. *)
(* Proof. *)
(*   intros (st & hp); cbn; intros Hs. *)
(*   destruct Hs as  ( (st1 & hp1) & (st2 & hp2) & Hst1 & Hst2 & HPartition & HP & HQ); *)
(*     cbn in Hst1, Hst2, HPartition; subst; *)
(*     cbn. *)
(*   rewrite HP in HPartition; clear HP. *)
(*   assert (Heq: free_unchecked hp a = hp2). *)
(*   { *)
(*     apply eq_spec. *)
(*     - intros a_any v_any. *)
(*       split; intros HPointsTo. *)
(*       + destruct (free_unchecked_spec_PointsTo_r HPointsTo) as [ Hneq HPointsTo' ]; *)
(*           destruct (Partition_spec_PointsTo_lr HPartition HPointsTo'); [ | assumption ]. *)
(*         exfalso; apply Hneq. symmetry; eapply one_spec_ll; eauto. *)
(*       + apply free_unchecked_spec_PointsTo_l. *)
(*         * intros contra; subst. *)
(*           eapply Partition_Disjoint; eauto. *)
(*           split. *)
(*           eapply Contains_of_PointsTo. apply one_spec; split; reflexivity. *)
(*           eapply Contains_of_PointsTo; eauto. *)
(*         * eapply Partition_spec_PointsTo_r; [ exact HPartition | assumption ]. *)
(*   } *)
(*   now subst. *)
(* Qed. *)

(* Lemma wand_pred {St Hp} a v (P: Pred (State St Hp)) s: *)
(*   (a ||~> v -* P) s -> *)
(*   (~ exists v, a |-> v $<= (heap s)) -> *)
(*   P *)
(*     {| *)
(*       store := store s; *)
(*       heap := Heap.mutate_unchecked (heap s) a v *)
(*     |}. *)
(* Proof. *)
(*   intros Hwand HNContains. *)
(*   unfold wand in Hwand. *)
(*   specialize (Hwand {| store := store s; heap := (a |-> v)|} ). *)
(*   cbn in Hwand. *)
(*   assert (Hdsj : one a v $/= heap s). *)
(*   { *)
(*     intros a_any [ HContains1 HContainss ]. *)
(*     destruct (PointsTo_of_Contains HContains1) as [ v' HPointsTo1 ]. *)
(*     apply one_spec_ll in HPointsTo1; subst. *)
(*     contradiction. *)
(*   } *)
(*   eapply Hwand; eauto. *)
(*   - now auto. *)
(*   - split; [ | ]. *)
(*     + now symmetry. *)
(*     + intros a' v'; split; [ intros HPointsTo | intros [ HPointsTo | HPointsTo ] ]. *)
(*       * destruct (mutate_unchecked_spec_r _ _ _ _ _ HPointsTo) as [ [ Heqa Heqv ] | [ Hneqa HPointsTo' ] ]; [ subst; right; now apply one_spec | now left ]. *)
(*       * eapply Heap.Facts.mutate_unchecked_spec_l. *)
(*         right; split; auto. *)
(*         intros contra; subst. *)
(*         eapply Hdsj; split; now eauto with mem. *)
(*       * eapply mutate_unchecked_spec_l. *)
(*         eapply one_spec in HPointsTo; now constructor. *)
(* Qed. *)


(* Lemma write_addr_wp_eq (a: Addr.t) (v : MapHeap.value) (p : Pred state) s : *)
(*   (((Exists x, (a |~> x))**((a |~> v) -* p)) s) <-> *)
(*   (MapHeap.Contains a s.(memory) -> *)
(*    p {| reg1 := s.(reg1); *)
(*        reg2 := s.(reg2); *)
(*        memory := MapHeap.set s.(memory) a v *)
(*      |}). *)
(* (* match s.(memory) a with *) *)
(*   (* Some _ => *) *)
(*   (*   p  {| *) *)
(*   (*   reg1 := s.(reg1); *) *)
(*   (*   reg2 := s.(reg2); *) *)
(*   (*   memory := fun x => if x =? a *) *)
(*   (*    then Some v else s.(memory) x |} *) *)
(*   (* | None => False *) *)
(*   (* end. *) *)
(* Proof. *)
(*   split. *)
(*   - intros Hm [ v' HPointsTo ]. *)
(*   specialize Hm as Hex. *)
(*   rewrite <- Exists_star_left in Hex. *)
(*   destruct Hex as (v'' & Hs). *)
(*   specialize Hs as Hs'. *)
(*   apply One_star_mem in Hs. *)
(*   apply One_star_pred in Hs'. *)
(*   apply wand_pred in Hs'; cbn in Hs'. *)
(*   + now rewrite set_unset_inv in Hs'. *)
(*   + intros [ v''' HPointsTo' ]. *)
(*     cbn in HPointsTo'. *)
(*     apply MapHeap.unset_spec in HPointsTo'. *)
(*     destruct HPointsTo'; congruence. *)
(*   - intros HP. *)
(*     rewrite <- Exists_star_left. *)
(*     exists v. *)
(*     exists {| reg1 := reg1 s; reg2 := reg2 s; memory := (a |-> v) |}, *)
(*       {| reg1 := reg1 s; reg2 := reg2 s; memory := MapHeap.unset (memory s) a |}; *)
(*       unfold reg, mem. *)
(*     split; try reflexivity. *)
(*     split; try reflexivity. *)
(*     split. *)
(*     { cbn. *)
(*       apply unset_Partition_one. *)
(*     } *)
(* apply impl_antisym; intros s Hm. *)
(* - *)
(*   intros [ v' HPointsTo ]. *)
(*   specialize Hm as Hex. *)
(*   rewrite <- Exists_star_left in Hex. *)
(*   destruct Hex as (v'' & Hs). *)
(*   specialize Hs as Hs'. *)
(*   apply One_star_mem in Hs. *)
(*   apply One_star_pred in Hs'. *)
(*   apply wand_pred in Hs'; cbn in Hs'. *)
(*   + now rewrite set_unset_inv in Hs'. *)
(*   + intros [ v''' HPointsTo' ]. *)
(*     cbn in HPointsTo'. *)
(*     apply MapHeap.unset_spec in HPointsTo'. *)
(*     destruct HPointsTo'; congruence. *)
(* - rewrite <- Exists_star_left. *)
(*   exists v. *)
(*   unfold "**". *)
(*   exists {| reg1 := reg1 s; reg2 := reg2 s; memory := (a |-> v) |}, *)
(*     {| reg1 := reg1 s; reg2 := reg2 s; memory := MapHeap.unset (memory s) a |}; *)
(*     unfold reg, mem. *)
(*   split; try reflexivity. *)
(*   split; try reflexivity. *)
(*   split. *)
(*   { cbn. *)
(*   apply unset_Partition_one. } *)
(*   split. *)
(*   { reflexi } *)
(*   + intros a' [ [ v' HPointsTo' ] [ v'' HPointsTo'' ] ]. *)
(*     apply one_spec in HPointsTo'. *)
(*     destruct HPointsTo'; subst. *)
(*     apply MapHeap.unset_spec in HPointsTo''. *)
(*     destruct HPointsTo''; congruence. *)
(*   + intros HPointsTo. *)
(*     specialize HPointsTo as HPartition. *)
(*     apply unset_Partition_one in HPartition. *)
(*     destruct (Addr.eq_dec a0 a); [ subst | ]. *)
(*     * eapply Partition_PointsTo_iff in HPartition. *)
(*       destruct HPartition as [ HProof _ ]. *)
(*       eapply HProof in HPointsTo. *)
(*       destruct HPointsTo. *)
(*       specialize H as H'. *)
(*       apply one_spec in H'. *)
(*       destruct H'; subst. *)
(* Admitted. *)

(* Lemma wp_deref_succ_reg1_eq (P : nat -> State -> Prop): *)
(* (fun s : State => *)
(*       (Exists (a : nat), (reg1 s + 1) ---> a && P a) *)
(*         s) *)
(* = *)
(* (Exists (a r:nat), (reg1= r) ** *)
(*      ((r + 1) ---> a && P a)). *)
(* Proof. *)
(* apply impl_antisym; intros s Hm. *)
(* - *)
(*   destruct Hm as (a & Hr & Hp). *)
(*   exists a, (reg1 s). *)
(*   exists {| reg1 := reg1 s; reg2 := reg2 s; memory := $0|}, *)
(*     {| reg1 := reg1 s; reg2 := reg2 s; *)
(*                        memory :=(memory s) $+  (reg1 s +1, a)|}; *)
(*     unfold reg, mem; *)
(*     cbn; repeat split; cbn ; auto. *)
(*   + *)
(*     rewrite emp_neutral_sum_l. *)
(*     now apply already_some_add_eq. *)
(*   + *)
(*     apply emp_dsj. *)
(*   + *)
(*     apply add_some. *)
(*   + *)
(*     rewrite <- already_some_add_eq; auto. *)
(* - *)
(*   destruct Hm as (a & r & Hs). *)
(*   exists a. *)
(*   destruct Hs as (s1 & s2 & Hr1 & Hr2 & Heq & Hd & *)
(*                     (Hreg1 & Hs1) & (Himpr1 & HimpP)). *)
(*   injection Hr1 ; injection Hr2 ; intros; subst. *)
(*   unfold mem in *. *)
(*   rewrite Hs1 in *. *)
(*   rewrite emp_neutral_sum_l in Heq. *)
(*   rewrite <- Heq in Himpr1. *)
(*   rewrite H2. *)
(*   split; auto. *)
(*   replace s with {| reg1 := reg1 s; reg2 := reg2 s; *)
(*                        memory :=memory s |} by auto. *)
(*   rewrite  H0,H,Heq. *)
(*   now replace s2 with {| reg1 := reg1 s2; reg2 := reg2 s2; *)
(*                        memory :=memory s2 |} in HimpP by auto. *)
(* Qed. *)


(* Lemma wand_reg1_Exists{A:Type}: *)
(* forall (r:nat) (p: A -> Pred state), *)
(* [reg1= r]-*(Exists (x:A), p x) = *)
(* (Exists (x:A), [reg1= r]-* (p x)). *)
(* Proof. *)
(* intros r p. *)
(* apply impl_antisym; intros s Hs; *)
(* unfold "[reg1= _ ]-* _ " in *; *)
(*  destruct Hs as (x & Hx); *)
(*  now exists x. *)
(* Qed. *)


(* Lemma wand_reg2_Exists{A:Type}: *)
(* forall (r:nat) (p: A -> Pred state), *)
(* [reg2= r]-*(Exists (x:A), p x) = *)
(* (Exists (x:A), [reg2= r]-* (p x)). *)
(* Proof. *)
(* intros r p. *)
(* apply impl_antisym; intros s Hs; *)
(* unfold "[reg2= _ ]-* _ " in *; *)
(*  destruct Hs as (x & Hx); *)
(*  now exists x. *)
(* Qed. *)
