From Stdlib Require Import Arith.
From Stdlib Require Import List SetoidList Sorting.
Import ListNotations.
From Imp Require Import Memval.

Declare Scope store_scope.
Delimit Scope store_scope with store.

Structure Store: Type :=
  {
    store :> Type;
    name: Type;

    name_eq_dec: forall (x y: name), { x = y } + { x <> y };

    emp: store;

    BindsTo: name -> memval -> store -> Prop;
    WF: store -> Prop;
    Empty: store -> Prop;
    Equal: store -> store -> Prop;

    lookup: store -> name -> option memval;
    mutate: store -> name -> memval -> option store;
    push: store -> memval -> store * name;
    pop: store -> option store;

    mutate_unchecked: store -> name -> memval -> store;
    push_unchecked: store -> name -> memval -> store;

    emp_spec: forall n v, ~BindsTo n v emp;
    emp_wf: WF emp;

    BindsTo_spec: forall s n v w, BindsTo n v s -> BindsTo n w s -> v = w;
    (* WF_spec: forall s s', WF s -> WF s' -> Equal s s' -> s = s'; *)
    Empty_spec: forall s n v, Empty s -> ~BindsTo n v s;
    Equal_spec: forall s s', Equal s s' <-> (forall n v, BindsTo n v s <-> BindsTo n v s');

    lookup_spec: forall s n v, BindsTo n v s <-> lookup s n = Some v;
    mutate_spec1: forall s n v, (exists v_old, BindsTo n v_old s) <-> (exists s', mutate s n v = Some s');
    mutate_spec2: forall s n v s', mutate s n v = Some s' -> BindsTo n v s';
    mutate_spec3: forall s n v s' n' v', n <> n' -> mutate s n v = Some s' -> (BindsTo n' v' s <-> BindsTo n' v' s');
    mutate_wf: forall s n v s', WF s -> mutate s n v = Some s' -> WF s';
    push_spec1: forall s n v s' v', WF s -> push s v = (s', n) -> ~BindsTo n v' s;
    push_spec2: forall s n v s', WF s -> push s v = (s', n) -> BindsTo n v s';
    push_wf: forall s n v s', WF s -> push s v = (s', n) -> WF s';
    (* This rule is faulty, only the bindings should be equal *)
    pop_spec: forall s n v s', push s v = (s', n) -> exists s'', pop s' = Some s'' /\ Equal s s'';
    pop_wf: forall s s', WF s -> pop s = Some s' -> WF s';

    mutate_unchecked_spec: forall s n v n' v', ((n = n' /\ v = v') \/ (n <> n' /\ BindsTo n v s)) <-> BindsTo n v (mutate_unchecked s n' v');

    mutate_unchecked_mutate_spec: forall n v s v_old, BindsTo n v_old s -> mutate s n v = Some (mutate_unchecked s n v);
    push_mutate_spec: forall s n v s' s'' v', push s v = (s', n) -> mutate s' n v' = Some s'' -> push s v' = (s'', n);
  }.

Arguments store St: rename.
Arguments name {_}.
Arguments name_eq_dec {_}.
Arguments emp {_}.
Arguments BindsTo {_}.
Arguments WF {_}.
Arguments Empty {_}.
Arguments Equal {_}.
Arguments lookup {_}.
Arguments mutate {_}.
Arguments push {_}.
Arguments pop {_}.
Arguments mutate_unchecked {_}.
Arguments emp_spec {_}.
Arguments emp_wf {_}.
Arguments BindsTo_spec {_}.
(* Arguments WF_spec {_}. *)
Arguments Empty_spec {_}.
Arguments Equal_spec {_}.
Arguments lookup_spec {_}.
Arguments mutate_spec1 {_}.
Arguments mutate_spec2 {_}.
Arguments mutate_spec3 {_}.
Arguments mutate_wf {_}.
Arguments push_spec1 {_}.
Arguments push_spec2 {_}.
Arguments push_wf {_}.
Arguments pop_spec {St st nm v s'} Hpush: rename.
Arguments pop_wf {_}.
Arguments mutate_unchecked_spec {_}.
Arguments mutate_unchecked_mutate_spec {_}.
Arguments push_mutate_spec {_}.

Hint Resolve
  name_eq_dec
  emp_spec emp_wf
  BindsTo_spec (* WF_spec *) Empty_spec Equal_spec
  lookup_spec
  mutate_spec1 mutate_spec2 mutate_spec3 mutate_wf
  push_spec1 push_spec2  push_wf
  pop_spec pop_wf
  mutate_unchecked_spec
  mutate_unchecked_mutate_spec push_mutate_spec
  : mem.

Module Facts.

  Lemma Equal_spec_l: forall {S: Store} s s' n v, Equal s s' -> BindsTo n v s -> @BindsTo S n v s'.
  Proof.
    intros S s s' n v HEqual HBindsTo.
    destruct (Equal_spec s s') as [ HProof _ ].
    destruct (HProof HEqual n v); eauto.
  Qed.

  Lemma Equal_spec_r: forall {S: Store} s s' n v, Equal s s' -> BindsTo n v s' -> @BindsTo S n v s.
  Proof.
    intros S s s' n v HEqual HBindsTo.
    destruct (Equal_spec s s') as [ HProof _ ].
    destruct (HProof HEqual n v); eauto.
  Qed.

  Hint Resolve Equal_spec_l Equal_spec_r: mem.

  Lemma lookup_spec_l: forall {S: Store} {s n v}, BindsTo n v s -> @lookup S s n = Some v.
  Proof.
    intros S s n v HBindsTo.
    now eapply lookup_spec.
  Qed.

  Lemma lookup_spec_r: forall {S: Store} {s n v}, lookup s n = Some v -> @BindsTo S n v s.
  Proof.
    intros S s n v Hlookup.
    now eapply lookup_spec.
  Qed.

  Hint Resolve lookup_spec_l lookup_spec_r: mem.

  Lemma mutate_spec1_l: forall {S s n v_old} v, BindsTo n v_old s -> (exists s', @mutate S s n v = Some s').
  Proof.
    intros; eapply mutate_spec1; econstructor; eauto.
  Qed.

  Lemma mutate_spec1_r: forall {S} s n v s', mutate s n v = Some s' -> (exists v_old, @BindsTo S n v_old s).
  Proof.
    intros S s n v v_old Hmutate.
    eapply mutate_spec1; econstructor; eauto.
  Qed.

  Hint Resolve mutate_spec1_l mutate_spec1_r: mem.

  Lemma mutate_spec3_l: forall {S} s n v s' n' v', n <> n' -> mutate s n v = Some s' -> BindsTo n' v' s -> @BindsTo S n' v' s'.
  Proof.
    intros S s n v s' n' v' Hneq Hmutate HBindsTo.
    now apply (mutate_spec3 s n v s' n' v' Hneq Hmutate).
  Qed.

  Lemma mutate_spec3_r: forall {S} s n v s' n' v', n <> n' -> mutate s n v = Some s' -> BindsTo n' v' s' -> @BindsTo S n' v' s.
  Proof.
    intros S s n v s' n' v' Hneq Hmutate HBindsTo.
    now apply (mutate_spec3 s n v s' n' v' Hneq Hmutate).
  Qed.

  Hint Resolve mutate_spec3_l mutate_spec3_r: mem.

  Lemma mutate_unchecked_spec_ll: forall {S} s n v n' v', n = n' -> v = v' -> BindsTo n v (@mutate_unchecked S s n' v').
  Proof.
    intros S s n v n' v' Heq1 Heq2.
    apply (mutate_unchecked_spec s n v n' v'); eauto.
  Qed.

  Lemma mutate_unchecked_spec_lr: forall {S} s n v n' v', n <> n' -> BindsTo n v s -> @BindsTo S n v (mutate_unchecked s n' v').
  Proof.
    intros S s n v n' v' Hneq HBindsTo.
    apply (mutate_unchecked_spec s n v n' v'); eauto.
  Qed.

  Lemma mutate_unchecked_spec_r: forall {S} s n v n' v', BindsTo n v (mutate_unchecked s n' v') -> ((n = n' /\ v = v') \/ (n <> n' /\ @BindsTo S n v s)).
  Proof.
    intros S s n v n' v' HBindsTo.
    apply (mutate_unchecked_spec s n v n' v'); eauto.
  Qed.

  Hint Resolve mutate_unchecked_spec_ll mutate_unchecked_spec_lr mutate_unchecked_spec_r: mem.

End Facts.
