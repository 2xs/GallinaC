From Stdlib Require Import
FunctionalExtensionality PropExtensionality List Psatz Arith NArith.
Import ListNotations.
From GallinaC.Imp Require Export Store Heap Primitives.
Import Heap.Facts.
From GallinaC.Seplog Require Export Pred GenAssertion.

Local Open Scope state_scope.
Local Open Scope heap_scope.
Local Open Scope separation_scope.

Definition One {St Hp} (a: Addr.t) (v: memval): Pred (State St Hp) :=
  fun s => heap s = a |-> v.

Definition Two {St Hp} (a:Addr.t) (v1 v2:memval): Pred (State St Hp) :=
  fun s => heap s = of_list a [v1; v2].

Notation "a ||~> v" :=
  (One a v)
    (at level 35, no associativity).

Notation "a ||~> ( v1 , v2 )" :=
  (Two a v1 v2)
    (at level 35, no associativity).

Lemma Two_star {St Hp}: forall a v1 v2,
    |- ((a ||~> (v1, v2)) <==>
          (a ||~> v1) ** ((Addr.shift_fw a 1%N) ||~> v2): Pred (State St Hp)).
Proof.
  intros a v1 v2.
  unfold One,Two.
  apply impl_antisym_taut.
  - intros s Hs.
    exists
      (mkState (store s) (a |-> v1)),
      (mkState (store s) ((Addr.shift_fw a 1%N) |-> v2)); cbn.
    repeat split; auto.
    unfold of_list in Hs.
    cbn in Hs.
    rewrite op_id_r in Hs.
    destruct ((Addr.shift_fw a 1) |-> v2 $+ a |-> v1) as [ hp | ] eqn:E; [ rewrite op_comm; congruence | ].
    destruct (proj1 (@one_ne_addr Hp (Addr.shift_fw a 1) a v2 v1)).
    intros contra; destruct a; cbn in *; inversion contra; lia.
    congruence.
  - intros s ( s1 & s2 & Hst1 & Hst2 & HPartition & Hfirst & Hsecond ).
Abort.

Fixpoint llist {St Hp} (p:Pointer.t) (l: list memval) : Pred (State St Hp) :=
  match l with
  | [] => [| p = Pointer.NULL |]
  | v :: l' => [| p <> Pointer.NULL |] **
                 Exists a p', [| Pointer.References p a |] ** a ||~> (v,VPtr p') ** (llist p' l')
  end.

Lemma llist_null {St Hp}: forall l,
    |- @llist St Hp Pointer.NULL l <==> [| l = [] |].
Proof.
  intro l.
  apply impl_antisym_taut; intros s Hm; unfold lift in *.
  -
    (destruct l; cbn in Hm); [ split; auto; now destruct Hm  | ].
    destruct Hm as (_ & _ & _ & _ & _ & (HNULL & _) & _ & _ ).
    contradiction.
  -
    destruct Hm; subst.
    split; auto.
Qed.

Lemma list_nonnull {St Hp}:
  forall p l,
    |- ([| p <> Pointer.NULL |] : Pred (State St Hp)) ** llist p l
         ===>
         [| p <> Pointer.NULL |]  **
         Exists (v : memval)
         (l' : list memval)
         (a: Addr.t)
         (p' : Pointer.t),
  [| Pointer.References p a |] **
    [| l = v :: l' |] **
    a ||~> (v, VPtr p') **
    llist p' l'.
Proof.
  intros p l.
  apply cond_star_semicancel_l with
    (R := [| p <> Pointer.NULL |])
    (P := llist p l)
    (Q := (Exists (v : memval)
             (l' : list memval)
             (a : Addr.t)
             (p': Pointer.t),
            [| Pointer.References p a |] **
              [|l = v :: l'|] **
              a ||~> (v, VPtr p') **
              llist p' l'));
    [apply heapless_lift | now apply equiv_refl_taut | apply equiv_refl_taut | ].
  destruct l; cbn.
  -
    intros s ( _ & _ & _ & _ & _ & [ H1 _ ] & [ H2 _ ] ).
    contradiction.
  - intros s Hs.
    apply star_assoc in Hs.
    apply Exists_star_right in Hs; destruct Hs as ( a & Hs ).
    apply Exists_star_right in Hs; destruct Hs as ( p' & Hs ).
    destruct Hs as (snull & s' & Hst1 & Hst2 & HPartition1 & HNull &  H ).
    apply p_p_p in HNull.
    destruct HNull as ( HNull & HEmp ).
    exists m, l, a.
    (* TODO return to after IR *)
    (* destruct Hs as ( ?a & ?H ). *)
    (*     (rewrite <- star_assoc). *)
    (*     rewrite p_p_p. *)
    (*     rewrite <- Exists_star_right. *)
    (*     apply skolem_left. *)
    (*     intro a. *)
    (*     apply Exists_impl. *)
    (*     apply inst_Exists with (x := v). *)
    (*     apply Exists_impl. *)
    (*     apply inst_Exists with (x := l). *)
    (*     apply Exists_impl. *)
    (*     apply inst_Exists with (x := a). *)
    (*     apply star_weaken_l; [apply heapless_lift | apply impl_refl]. *)
    (*     intros s [ p ( s1 & s2 & Hr1 & Hr2 & HPartition & (s3 & s4 & Hr3 & Hr4 & HPartition' & HReferences & HOne) & Hllist ) ]. *)
    (*     exists p. *)
    (*     eexists (mk_state (reg s) (mem s1)); eexists (mk_state (reg s) (mem s2)). *)
    (*     split; [ now rewrite reg_state | ]. *)
    (*     split; [ now rewrite reg_state | ]. *)
    (*     split; [ now repeat rewrite mem_state | ]. *)
    (*     split. *)
    (*     eexists (mk_state (reg s) (mem s3)); eexists (mk_state (reg s) (mem s4)). *)
    (*     split; [ now repeat rewrite reg_state | ]. *)
    (*     split; [ now repeat rewrite reg_state | ]. *)
    (*     split; [ now repeat rewrite mem_state | split ]. *)
    (*     eexists (mk_state (reg s) (mem s3)); eexists (mk_state (reg s) $0). *)
    (*     split; [ now repeat rewrite reg_state | ]. *)
    (*     split; [ now repeat rewrite reg_state | ]. *)
    (*     split; [ repeat rewrite mem_state; now apply Partition_is_empty_r | split ]. *)
    (*     rewrite Hr1; rewrite Hr3; rewrite state_reg_mem; assumption. *)
    (*     constructor; try rewrite mem_state; reflexivity. *)
    (*     rewrite Hr1; rewrite Hr4; rewrite state_reg_mem; assumption. *)
    (*     rewrite Hr2; rewrite state_reg_mem; assumption. *)
    (* Qed. *)
Abort.

Lemma cond_list_nonnull {St: Store.Store} {Hp: Heap} (P U V: Pred (State St Hp)):
  forall  r l,
    U =  [|r <> Pointer.NULL|] ** llist r l ** P ->
    |- [|r <> Pointer.NULL|]  **
     (Exists (v : memval)
        (l' : list memval)
        (a: Addr.t)
      (p' : Pointer.t),
       [| Pointer.References r a |] **
       [| l = v :: l' |] **
         a ||~> (v, VPtr p') **
      llist p' l') ** P  ===> V
      ->
     |- U ===> V.
Proof.
  intros r l HU HP;subst.
  (* TODO return to after IR *)
(* apply impl_trans with (Q := [|r <> Pointer.NULL|] ** *)
(*           (Exists (v : memval) *)
(*              (l' : list memval) *)
(*              (a: Addr.t) *)
(*              (p' : Pointer.t), *)
(*             [| Pointer.References r a |] ** *)
(*             [|l = v :: l'|] ** *)
(*               a ||~> (v, VPtr p') ** *)
(*               llist p' l') ** P); auto. *)
(* apply star_cancel_r. *)
(* eapply list_nonnull. *)
(* Qed. *)
Admitted.

Lemma llist_indep_regs {St: Store.Store} {Hp: Heap}: forall p l,
@indep_store St Hp (llist p l).
Proof.
intros p l s s'.
revert p s s'.
induction l as [ | v l ] ; intros p s s' Heqm Hll.
- cbn in Hll; cbn.
  destruct Hll as (Ha' & Hs).
  rewrite Heqm in Hs.
  split; auto.
-
  cbn in Hll; cbn.
  destruct Hll as (s1 & s2 & Hr1 & Hr2 & HPartition & HNNull & (a & p' & s3 & s4 & Hr3 & Hr4 & HPartition' & ( s5 & s6 & Hr5 & Hr6 & HPartition'' & HReferences & HTwo) & Hllist)).
  (* TODO return to after IR *)
  (* eexists (mk_state (reg s') (mem s1)), (mk_state (reg s') (mem s2)). *)
(*   split; [ now rewrite reg_state | ]. *)
(*   split; [ now rewrite reg_state | ]. *)
(*   split; [ repeat rewrite mem_state; rewrite <- Heqm; assumption | ]. *)
(*   split; [ inversion HNNull; unfold lift; rewrite mem_state; split; auto | ]. *)
(*   exists a, p'. *)
(*   exists (mk_state (reg s') (mem s3)), (mk_state (reg s') (mem s4)). *)
(*   split; [ now repeat rewrite reg_state | ]. *)
(*   split; [ now repeat rewrite reg_state | ]. *)
(*   split; [ now repeat rewrite mem_state | ]. *)
(*   split. *)
(*   eexists (mk_state (reg s') (mem s5)), (mk_state (reg s') (mem s6)). *)
(*   split; [ now repeat rewrite reg_state | ]. *)
(*   split; [ now repeat rewrite reg_state | ]. *)
(*   split; [ now repeat rewrite mem_state | ]. *)
(*   split. *)
(*   split; [ now inversion HReferences | rewrite mem_state; now inversion HReferences ]. *)
(*   unfold Two. *)
(*   now rewrite mem_state. *)
(*   specialize (IHl p' s4 (mk_state (reg s') (mem s4))). *)
(*   rewrite mem_state in IHl. *)
(*   now specialize (IHl (eq_refl _) Hllist ). *)
(* Qed. *)
Abort.
