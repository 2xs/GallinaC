From Stdlib Require Import List Arith NArith.
From GallinaC.Imp Require Import Primitives.
From GallinaC.Imp Require Import Memval.
From GallinaC.Seplog Require Export Hoare Pred GenAssertion.
From GallinaC.Seplog Require Import InternalTriples.
Import Nat.
Import Pointer.
Import Heap(Heap).
Import Store(Store).

Local Open Scope state_scope.
Local Open Scope program_scope.
Local Open Scope heap_scope.

Section Store.
  Import Store Store.Facts.
  Import Primitives.

  Lemma read_var_triple {St: Store} {Hp: Heap} {MS: MemStorable} (P : obj MS -> (State St Hp) -> Prop) varname :
    {{ fun s => exists v, BindsTo varname (encode v) s.(store) /\ P v s }} read_var varname {{ P }}.
  Proof.
    unfold read_var.
    eapply bind_rule with
      (Q := fun s s' => exists v, BindsTo varname (encode v) s.(store) /\ P v s /\ s' = s).
    - intro s.
      intros s' (v & HBindsTo & HP & Heq); subst.
      rewrite (lookup_spec_l HBindsTo), encode_decode.
      now cbn.
    - intros s (v & HBindsTo & HP).
      cbn; eexists; split; eauto.
  Qed.

  Lemma write_var_triple {St: Store} {Hp: Heap} {MS: MemStorable} (varname: name) (val: obj MS) (P: unit -> (State St Hp) -> Prop):
    {{ fun s => exists v_old, BindsTo varname v_old s.(store) /\ P tt {| store := mutate_unchecked s.(store) varname (encode val); heap := s.(heap) |} }}
      write_var varname val
      {{ P }}.
  Proof.
    unfold write_var.
    eapply bind_rule with
      (Q := fun s s' => exists v, BindsTo varname v s.(store) /\ P tt {| store := mutate_unchecked s.(store) varname (encode val); heap := s.(heap) |} /\ s' = s).
    - intros s s' (v & HBindsTo & HP & Heq); subst.
      destruct (mutate_spec1_l (encode val) HBindsTo) as [ s' Emutate ]; rewrite Emutate.
      erewrite mutate_unchecked_mutate_spec in Emutate; eauto; inversion Emutate; subst; clear Emutate.
      now auto.
    - intros s ( v & HBindsTo & HP ).
      cbn; exists v; auto.
  Qed.

End Store.

Section Heap.
  Import Heap Heap.Facts.
  Import Primitives.

  Lemma read_ptr_triple {St: Store} {Hp: Heap} {MS: MemStorable} (ptr : Pointer.t) (P : obj MS -> (State St Hp) -> Prop) :
    {{ fun s => exists a v,
           Pointer.References ptr a /\
             Pointer.Allows ptr Operation.Read /\
             s.(heap) = a |-> (encode v) /\
             P v s
    }}
      read_ptr ptr
      {{ P }}.
  Proof.
    unfold read_ptr.
    eapply bind_rule with
      (Q := fun s s' => exists addr val, Pointer.References ptr addr /\ Pointer.Allows ptr Operation.Read /\  s.(heap) = addr |-> (encode val) /\ P val s /\ s' = s).
    - intros s s' (addr & val & HReferences & HAllows & HPointsTo & HP & Heq); subst.
      rewrite (proj1 (lookup_some _ _ (encode val))).
      rewrite encode_decode; auto.
      exists addr; split; auto.
      split; auto.
      exists $0%sep.
      rewrite op_id_r.
      congruence.
  Abort.

  Lemma write_ptr_triple {St: Store} {Hp: Heap} {MS: MemStorable} (ptr: Pointer.t) (val : obj MS) (P : unit -> (State St Hp) -> Prop) :
    {{ fun s => exists addr v,
           Pointer.References ptr addr /\
             Pointer.Allows ptr Operation.Write /\
             s.(heap) = addr |-> v /\
             P tt {| store := s.(store) ; heap := addr |-> (encode val) |}
    }}
      write_ptr ptr val
      {{ P }}.
  Proof.
    unfold write_ptr.
  Abort.

  (* Lemma alloc_ptr_triple {St: Store} {Hp: Heap} {MS: MemStorable} (n: Nat.t) (val: obj MS) (P: Pointer.t -> (State St Hp) -> Prop): *)
  (*   {{ fun s => forall ptr addr hp, ~Contains addr s.(heap) -> Pointer.References ptr addr -> (forall a v, PointsTo a v hp <-> (Pointer.Reaches ptr a /\ v = (encode val)) \/ (~Pointer.Reaches ptr a /\ PointsTo a v hp)) -> P ptr {| store := s.(store); heap := hp |}  }} *)
  (*     alloc_ptr n val *)
  (*     {{ P }}. *)
  (* Proof. *)
  (*   unfold alloc_ptr. *)
  (*   eapply bind_get_rule. *)
  (*   intros s' s (HP & Heq); subst. *)
  (*   destruct (alloc (heap s) n (encode val)) as [ hp' [ [ addr prov ] | ] ] eqn:Ealloc. *)
  (*   - cbn. *)
  (*     assert (HNContains: ~Contains addr (heap s)). *)
  (*     { *)
  (*       destruct (alloc_spec (heap s) n (encode val) hp' (Some (addr, prov))) as (addr' & HReferences' & _ & HReaches & H & _). *)
  (*       congruence. *)
  (*       inversion HReferences'; subst addr'; subst. *)
  (*       apply H. *)
  (*       apply HReaches. *)
  (*       exists 0. *)
  (*       split. *)
  (*       lia. *)
  (*       destruct addr. *)
  (*       now rewrite <- (Nat.add_0_r offset) at 2. *)
  (*     } *)
  (*     eapply HP; eauto with mem. *)
  (*     constructor. *)
  (*     specialize (alloc_spec (heap s) n (encode val) hp' (Some (addr, prov))) as HProof. *)
  (*     intros a v; split. *)
  (*     intros HPointsTo. *)
  (*     + destruct (Pointer.reaches_spec (Some (addr, prov)) a) as [ HReaches | HNReaches ]. *)
  (*       * left. *)
  (*         split > [ assumption | ]. *)
  (* Abort. *)

  (*   Lemma free_ptr_triple {St: Store} {Hp: Heap} (p: Pointer.t) (P: unit -> Pred (State St Hp)): *)
  (*     {{ fun s => exists addr, Pointer.Allows ptr Operation.Free /\ Pointer.References ptr addr /\ Contains addr (heap s) /\ P ptr {| store := s.(store); heap :=  }} *)
  (*       free_ptr ptr *)
  (*       {{ P }} *)

  Lemma shift_fw_ptr_triple {St: Store} {Hp: Heap} (ptr: Pointer.t) (shift: N) (P: Pointer.t -> Pred (State St Hp)):
    {{ fun s => exists ptr', Pointer.Shift ptr shift ptr' /\ P ptr' s }}
      shift_fw_ptr ptr shift
      {{ P }}.
  Proof.
    unfold shift_fw_ptr.
    apply bind_get_rule.
    intros s'.
  Abort.

  (* Lemma eq_ptr_triple {St: Store} {Hp: Heap} (ptr_l: Pointer.t) (ptr_r: Pointer.t) (P: bool -> Pred (State _ _)): *)
  (*   {{ fun s => exists b addr_l addr_r, Pointer.cmp ptr_l ptr_r = Some b /\ PointsTo  /\ P b s }} *)
  (*     eq_ptr ptr_l ptr_r *)
  (* do s <- get; *)
  (* match Heap.lookup s.(heap) ptr_l, Heap.lookup s.(heap) ptr_r, Pointer.cmp ptr_l ptr_r with *)
  (* | Some _, Some _, Some b => ret b *)
  (* | _, _, _ => fail *)
  (* end. *)


End Heap.
