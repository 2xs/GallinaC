From Stdlib Require Import Arith NArith List Lia ssrfun Bool.
Import ListNotations.
From Utils Require Import OptionExt GenId.
From Utils Require Export Algebra.
From Imp Require Export Pointer Memval.

Local Open Scope separation_scope.

Declare Scope heap_scope.
Delimit Scope heap_scope with heap.
Local Open Scope heap_scope.

(** * Memory

    Memory is a mapping from addresses to memory values, it is not associated
    with semantics.

    A memory extends a separation algebra with specific axioms.

    All previous properties and notations of separation algebras hold:
    - [ $0 ] is the empty memory
    - [ m1 $+ m2 ] is the partial union of memories [m1] and [m2] (fails on duplicate bindings)
    - [ m1 $/= m2 ] denotes disjoint memories, etc.

    In addition, it introduces the constructor [one a v] with notation (a |-> v). It denotes a singleton memory containing only value [v] at address [a].
 *)
Structure Memory: Type :=
  {
    mem :> Separation;

    (* Constructors *)
    one: Addr.t -> memval -> mem;

    (* Inspecting memory *)
    with_one: mem -> Addr.t -> memval -> bool;
    contains: mem -> Addr.t -> bool;

    (* empty axioms *)
    emp_no_sub: forall a v, ~(one a v $<= $0);

    (* one axioms *)
    one_inj: forall a a' v v', one a v = one a' v' <-> a = a' /\ v = v';
    one_ne_addr: forall a a' v v', a <> a' <-> (one a v) $/= (one a' v');
    one_sep: forall a v m, (forall a' v', one a' v' $<= m -> one a v $/= one a' v') <-> (one a v) $/= m;
    one_fun: forall a v1 v2 m (SUB1: one a v1 $<= m) (SUB2: one a v2 $<= m), v1 = v2;
    one_similar: forall a v m, (exists v', one a v' $<= m) <-> (one a v) $+ m = None;
    one_min: forall m a v, m $<= one a v <-> m = $0 \/ m = one a v;
    one_discriminate: forall m a v m'
                             (EQ: one a v $+ m = Some m')
                             a' v',
      (one a' v' $<= m') <->
        ((a' = a /\ v' = v) \/ (a' <> a /\ one a' v' $<= m));

    (* General axioms *)
    sep_mem: forall m1 m2, (forall a1 a2 v1 v2 (SUB1: one a1 v1 $<= m1) (SUB2: one a2 v2 $<= m2), one a1 v1 $/= one a2 v2) <-> m1 $/= m2;
    canc_mem: forall (m1 m2 m3 m4: mem) (EQ1: m1 $+ m2 = Some m4) (EQ2: m1 $+ m3 = Some m4), m2 = m3;


    (* Inspection axioms *)
    with_one_spec: forall m a v, reflect (one a v $<= m) (with_one m a v);
    contains_spec: forall m a, reflect (exists v, one a v $<= m) (contains m a);
  }.

Arguments mem M: rename.
Arguments one [M] a v: rename.
Arguments with_one [M] m a v: rename.
Arguments contains [M] m a: rename.
Arguments emp_no_sub [M] a v: rename.
Arguments one_inj [M] a a' v v': rename.
Arguments one_ne_addr [M] a a' v v': rename.
Arguments one_sep [M] a v m: rename.
Arguments one_fun [M] a v1 v2 m SUB1 SUB2: rename.
Arguments one_similar [M] a v m: rename.
Arguments one_min [M] m a v: rename.
Arguments one_discriminate [M] m a v m' EQ a' v': rename.
Arguments sep_mem [M] m1 m2: rename.
Arguments canc_mem [M] m1 m2 m3 m4 EQ1 EQ2: rename.
Arguments with_one_spec [M] m a v: rename.
Arguments contains_spec [M] m a: rename.

Notation "a |-> v" := (one a v) (at level 5, no associativity): heap_scope.

(** * Heaps

    A heap extends a memory by equiping it with executional semantics

 *)
Structure Heap: Type :=
  {
    heap :> Memory;
    heap_alc: GenId;

    (* Constructor *)
    emp_with_alc: heap_alc -> heap;
    (* Coercions *)
    to_allocator: heap -> carrier heap_alc;

    (* Primitive Operations *)
    lookup: heap -> Pointer.t -> option memval;
    mutate: heap -> Pointer.t -> memval -> option (heap);
    alloc: heap -> N.t -> memval -> option (heap * Pointer.t);
    free: heap -> Pointer.t -> option (heap);

    (* Specification of operations *)
    (** allocators **)
    emp_alc: to_allocator $0 = $0;
    one_alc: forall a v, to_allocator (a |-> v) = $0;
    sum_alc: forall h1 h2, Option.map to_allocator (h1 $+ h2) = to_allocator h1 $+ to_allocator h2;
    emp_with_alc_alc: forall alc, to_allocator (emp_with_alc alc) = alc;
    (** lookup **)
    lookup_some: forall h p v, (exists addr, Pointer.References p addr /\ Pointer.Allows p Operation.Read /\ addr |-> v $<= h) <-> lookup h p = Some v;
    (** mutate **)
    mutate_some: forall h p v, (exists addr, Pointer.References p addr /\ Pointer.Allows p Operation.Write /\ exists v, (addr |-> v) $<= h) <-> exists h', mutate h p v = Some h';
    mutate_mem: forall h p v h' a v' m, mutate h p v = Some h' -> Pointer.References p a -> (a |-> v') $+ m = Some h -> (a |-> v) $+ m = Some h';
    mutate_alc: forall h p v h', mutate h p v = Some h' -> to_allocator h' = to_allocator h;
    (** alloc **)
    alloc_some: forall h sz v, (exists bid, get (to_allocator h) = Some bid /\ 0 < sz)%N <-> exists h' p, alloc h sz v = Some (h', p);
    alloc_references: forall h sz v h' p bid, alloc h sz v = Some (h', p) -> get (to_allocator h) = Some bid -> Pointer.References p (Addr.mkAddr bid 0);
    alloc_allows: forall h sz v h' p bid, alloc h sz v = Some (h', p) -> get (to_allocator h) = Some bid -> Pointer.Allows p Operation.Free;
    alloc_reaches: forall h sz v h' p bid, alloc h sz v = Some (h', p) -> get (to_allocator h) = Some bid -> forall sz', (sz' <= sz)%N <-> Pointer.Reaches p (Addr.mkAddr bid sz');
    alloc_absent: forall h sz v h' p, alloc h sz v = Some (h', p) -> forall a, Pointer.Reaches p a -> ~exists v_old, (a |-> v_old) $<= h;
    alloc_mem: forall h sz v h' p, alloc h sz v = Some (h', p) -> forall a' v', (a' |-> v') $<= h' <-> (Pointer.Reaches p a' /\ v' = v \/ ~Pointer.Reaches p a' /\ (a' |-> v') $<= h);
    alloc_alc: forall h sz v h' p, alloc h sz v = Some (h', p) -> to_allocator h' = next (to_allocator h);
    (** free **)
    free_some: forall h p, (Pointer.Allows p Operation.Free /\ (forall a, Pointer.Reaches p a -> exists v, (a |-> v) $<= h)) <-> exists h', free h p = Some h';
    free_mem: forall h p h', free h p = Some h' -> forall a, (Pointer.Reaches p a /\ ~exists v, a |-> v $<= h' \/ ~Pointer.Reaches p a /\ (forall v, a |-> v $<= h <-> a |-> v $<= h'));
    free_alc: forall h p h', free h p = Some h' -> to_allocator h' = to_allocator h;
  }.

Arguments heap Hp: rename.
Arguments heap_alc Hp: rename.
Arguments emp_with_alc [Hp] alc: rename.
Arguments to_allocator [Hp] hp: rename.
Arguments lookup [Hp] hp p: rename.
Arguments mutate [Hp] hp p v: rename.
Arguments alloc [Hp] hp sz v: rename.
Arguments free [Hp] hp p: rename.
Arguments emp_alc {Hp}: rename.
Arguments one_alc [Hp] a v: rename.
Arguments sum_alc [Hp] h1 h2: rename.
Arguments emp_with_alc_alc [Hp] alc: rename.
Arguments lookup_some [Hp] hp p v: rename.
Arguments mutate_some [Hp] hp p v: rename.
Arguments mutate_mem [Hp] hp p v h' a v' m EQ REF SUB: rename.
Arguments mutate_alc [Hp] hp p v h' EQ: rename.
Arguments alloc_some [Hp] hp sz v: rename.
Arguments alloc_references [Hp] hp sz v h' p bid EQ GetAlloc: rename.
Arguments alloc_allows [Hp] hp sz v h' p EQ: rename.
Arguments alloc_reaches [Hp] hp sz v h' p EQ sz': rename.
Arguments alloc_absent [Hp] hp sz v h' p EQ a REACH: rename.
Arguments alloc_mem [Hp] hp sz v h' p EQ a' v': rename.
Arguments alloc_alc [Hp] hp sz v h' p EQ: rename.
Arguments free_some [Hp] hp p: rename.
Arguments free_mem [Hp] hp p h' EQ a: rename.
Arguments free_alc [Hp] hp p h' EQ: rename.

Hint Resolve
  lookup_some
  mutate_some mutate_mem mutate_alc
  alloc_references alloc_allows alloc_reaches alloc_absent alloc_mem alloc_alc
  free_some free_mem free_alc
  : seplog.

Module Facts.

  Lemma one_eq_addr [M: Memory] a v v': (@one M a v) $+ (one a v') = None.
  Proof.
    destruct (a |-> v $+ a |-> v') as [m|] eqn:EQ; auto.
    now contradiction (proj2 (one_ne_addr a a v v') ltac:(eexists; exact EQ)).
  Qed.
  Hint Resolve one_eq_addr: seplog.

  Lemma one_neq_emp [M: Memory] a v:
    @one M a v <> $0.
  Proof.
    intros EQ.
    specialize (@op_id_l M $0).
    rewrite <- EQ.
    rewrite one_eq_addr.
    discriminate.
  Qed.
  Hint Resolve one_neq_emp: seplog.

  Definition Valid [Hp: Heap] (hp: Hp) (ptr: Pointer.t) :=
    exists addr v, Pointer.References ptr addr /\ (addr |-> v) $<= hp.

  Definition POValid [Hp: Heap] (hp: Hp) (ptr: Pointer.t) :=
    exists addr addr' v, Pointer.References ptr addr' /\ Addr.Shift addr 1 addr' /\ (addr |-> v) $<= hp.

  Definition WValid [Hp: Heap] (hp: Hp) (ptr: Pointer.t) :=
    Valid hp ptr \/ POValid hp ptr \/ ptr = Pointer.NULL.

  Definition valid [Hp: Heap] (hp: Hp) (ptr: Pointer.t): bool :=
    match ptr with
    | Some (addr, _) => contains hp addr
    | None => false
    end.

  Definition valid_past_one [Hp: Heap] (hp: Hp) (ptr: Pointer.t): bool :=
    match ptr with
    | Some (addr, _) =>
        match Addr.shift_bw addr 1 with
        | Some addr => contains hp addr
        | None => false
        end
    | None => false
    end.

  Definition weakly_valid [Hp: Heap] (hp: Hp) (ptr: Pointer.t) :=
    match ptr with
    | Some _ => valid hp ptr || valid_past_one hp ptr
    | None => true
    end.

  Lemma valid_spec [Hp: Heap] (hp: Hp) (ptr: Pointer.t)
    : reflect (Valid hp ptr) (valid hp ptr).
  Proof.
    unfold Valid, valid.
    destruct ptr as [ [addr prov]|] ; [ | right; intros (addr & v & REF & SUB); inversion REF ].
    destruct (contains_spec hp addr) as [ SUB | contra]; constructor.
    - destruct SUB as (v & SUB).
      exists addr, v.
      split; [ constructor | assumption ].
    - intros ( addr' & v & REF & SUB ).
      inversion REF; subst addr'; subst.
      apply contra.
      now exists v.
  Qed.

  Lemma valid_past_one_spec [Hp: Heap] (hp: Hp) (ptr: Pointer.t)
    : reflect (POValid hp ptr) (valid_past_one hp ptr).
  Proof.
    unfold POValid, valid_past_one.
    destruct ptr as [ [addr prov]|]; [| right; intros (addr & addr' & v & REF & SHIFT & SUB); inversion REF ].
    destruct (Addr.shift_bw addr 1) as [addr'|] eqn:Eshift; [|constructor; intros (addr' & addr'' & v & REF & SHIFT & SUB); inversion REF; subst; specialize ((proj1 (Addr.shift_bw_spec _ _ _) SHIFT)); congruence ].
    destruct (contains_spec hp addr') as [ SUB | contra]; constructor.
    - destruct SUB as (v & SUB).
      exists addr', addr, v.
      split; constructor.
      now apply Addr.shift_bw_spec.
      assumption.
    - intros ( addr'' & addr''' & v & REF & SHIFT & SUB).
      inversion REF; subst addr'''; subst.
      assert (addr'' = addr') by
        (eapply Addr.Shift_bw_fun; [ apply Addr.shift_bw_spec, Eshift | apply SHIFT ]);
        subst.
      apply contra.
      now exists v.
  Qed.

  Lemma weakly_valid_spec [Hp: Heap] (hp: Hp) (ptr: Pointer.t)
    : reflect (WValid hp ptr) (weakly_valid hp ptr).
  Proof.
    unfold WValid, weakly_valid.
    destruct ptr as [ (addr&prov) | ] eqn:E; [ rewrite <- E | now left; right; right ].
    destruct (valid_spec hp ptr) as [ VALID | NValid]; [ now constructor; left | cbn ].
    destruct (valid_past_one_spec hp ptr) as [ VALID | NValid']; [ now constructor; right; left | right ].
    intros contra.
    now destruct contra as [ Valid | [ Valid | EQ ] ]; [ apply NValid, Valid | apply NValid', Valid | rewrite E in EQ ].
  Qed.

  #[local] Fixpoint of_listi [M: Memory] (m: M) (addr: Addr.t) (vs: list memval): option M :=
    match vs with
    | [] => Some m
    | v::vs =>
        match (addr |-> v) $+ m with
        | Some m =>
            of_listi m (Addr.shift_fw addr 1) vs
        | None => None
        end
    end.

  #[local] Lemma of_listi_some [M: Memory]:
    forall (m: M) addr vs
           (LT: forall a v, (a |-> v) $<= m -> (Addr.block a <> Addr.block addr \/ Addr.offset a < Addr.offset addr)%N),
      exists m', @of_listi M m addr vs = Some m'.
  Proof.
    intros m addr vs.
    revert m addr.
    induction vs as [|v vs]; intros; [ now exists m | cbn ].
    destruct (addr |-> v $+ m) as [m'|] eqn:Esum.
    apply (IHvs m' (Addr.shift_fw addr 1)).
    intros a_any v_any SUB_any.
    specialize (proj1 (one_discriminate m addr v m' Esum a_any v_any) SUB_any) as [ [ EQ1 EQ2 ] | [ NE SUB' ] ];
      subst.
    right; destruct addr; cbn; lia.
    specialize (LT _ _ SUB') as [ NE' | LT ]; [ now destruct addr, a_any; left | right ].
    etransitivity; [ apply LT | ].
    destruct addr; cbn; lia.
    destruct (proj1 (one_sep addr v m)) as [ m' EQ ]; [ | congruence ].
    intros a_any v_any SUB.
    specialize (LT a_any v_any SUB).
    apply one_ne_addr.
    destruct LT as [ NEb | LTo ].
    destruct a_any, addr; congruence.
    destruct addr, a_any.
    intros EQ.
    cbn in LTo, EQ.
    inversion EQ; lia.
  Qed.

  #[local] Lemma of_listi_emp_some [M: Memory] addr vs
    : exists m', @of_listi M $0 addr vs = Some m'.
  Proof.
    apply of_listi_some.
    intros a v contra.
    now apply emp_no_sub in contra.
  Qed.

  #[local] Lemma of_listi_none [M: Memory]:
    forall (m: M) addr vs
           (LT: forall a v, (a |-> v) $<= m -> (Addr.block a <> Addr.block addr \/ Addr.offset a < Addr.offset addr)%N),
      of_listi m addr vs <> None.
  Proof.
    intros m addr vs.
    revert m addr.
    induction vs as [| v vs]; intros; [ discriminate | ].
    cbn.
    destruct (addr |-> v $+ m) as [ m' | ] eqn:EQ.
    - apply (IHvs m' (Addr.shift_fw addr 1)).
      intros a_any v_any SUB.
      destruct SUB as (m'' & EQ_any).
      specialize (proj1 (one_discriminate m addr v m' EQ a_any v_any) ltac:(eauto with seplog)) as [ [ EQ1 EQ2 ] | [ NEa SUB_any ] ]; [ subst | ].
      right; destruct addr; cbn; lia.
      destruct (LT a_any v_any SUB_any) as [ NEb | LTo ].
      left; destruct a_any, addr; cbn in *; lia.
      right; destruct a_any, addr; cbn in *; etransitivity; [ apply LTo | lia ].
    - destruct (proj1 (one_sep addr v m)).
      intros a' v' SUB.
      apply one_ne_addr.
      specialize (LT a' v' SUB) as [ NEb | LTo ].
      destruct a', addr. congruence.
      destruct a', addr; intros contra; cbn in *; inversion contra; lia.
      congruence.
  Qed.

  #[local] Lemma of_listi_hd [M: Memory]
    (m: M) a
    v vs m'
    (EQ: of_listi m a (v::vs) = Some m')
    : (a |-> v) $<= m'.
  Proof.
    cbn in EQ.
    destruct (a |-> v $+ m) as [m''|] eqn:Esum; [| discriminate].
    assert (LT: 0 < 1) by lia.
    revert m a v m' m'' Esum EQ LT.
    change 1%N with (N.of_nat 1).
    generalize 1%nat as o.
    induction vs as [|v' vs].
    - intros.
      cbn in EQ.
      inversion EQ; subst; clear EQ.
      now exists m.
    - intros.
      cbn in EQ.
      destruct ((Addr.shift_fw a (N.of_nat o)) |-> v' $+ m'') as [m'''|] eqn:Esum'; [| discriminate ].
      rewrite Addr.shift_fw_twice in EQ; cbn in EQ.
      change 1%N with (N.of_nat 1) in EQ.
      rewrite <- Nat2N.inj_add in EQ.
      specialize (op_assc (a |-> v) m ((Addr.shift_fw a (N.of_nat o)) |-> v')).
      rewrite Esum; cbn.
      unfold Basics.flip.
      rewrite op_comm, Esum'.
      destruct (m $+ (Addr.shift_fw a (N.of_nat o)) |-> v') as [m'4|] eqn:Esum''; try discriminate.
      cbn.
      intros Esum'''.
      eapply IHvs; [ | apply EQ | lia].
      symmetry; apply Esum'''.
  Qed.

  #[local] Lemma of_listi_preserves [M: Memory]
    (m: M) addr vs
    m'
    (EQ: of_listi m addr vs = Some m')
    a v (SUB: a |-> v $<= m)
    : a |-> v $<= m'.
  Proof.
    revert m addr m' EQ a v SUB.
    induction vs as [ | vs_hd vs_tl ]; intros.
    - now inversion EQ; subst m'.
    - cbn in EQ.
      destruct (addr |-> vs_hd $+ m) as [m''|] eqn:Esum; try discriminate.
      eapply IHvs_tl.
      apply EQ.
      etransitivity.
      apply SUB.
      eexists; rewrite op_comm; apply Esum.
  Qed.

  #[local] Lemma of_listi_spec [M: Memory]
    (m: M) addr vs
    (LT: forall a v, (a |-> v) $<= m -> (Addr.block a <> Addr.block addr \/ Addr.offset a < Addr.offset addr)%N)
    n v
    m'
    (EQ: of_listi m addr vs = Some m')
    : List.nth_error vs n = Some v <-> (Addr.shift_fw addr (N.of_nat n)) |-> v $<= m'.
  Proof.
    split;
      revert m addr LT n v m' EQ;
      induction vs as [| vs_hd vs_tl];
      intros m addr LT n v m' EQ;
      try (intros; destruct n; discriminate).
    - intros Nth.
      destruct n.
      + assert (vs_hd = v) by (cbn in Nth; congruence); subst.
        cbn. rewrite Addr.shift_fw_0.
        eapply of_listi_hd.
        apply EQ.
      + cbn in Nth.
        change (S n) with (1 + n).
        rewrite Nat2N.inj_add, <- Addr.shift_fw_twice.
        cbn in EQ.
        destruct (addr |-> vs_hd $+ m) as [m''|] eqn:Esum; try discriminate.
        eapply IHvs_tl; [ | apply EQ | apply Nth ].
        intros a_any v_any SUB_any.
        specialize (proj1 (one_discriminate m addr vs_hd m'' Esum a_any v_any) SUB_any) as [ [ EQ1 EQ2 ] | [ NE SUB' ] ]; subst.
        right; destruct addr; cbn; lia.
        specialize (LT a_any v_any SUB') as [ NEb | LTo ].
        now destruct a_any, addr; cbn in *; left.
        right.
        etransitivity.
        apply LTo.
        destruct addr; cbn; lia.
    - cbn in EQ; inversion EQ; subst m'; clear EQ.
      intros SUB.
      specialize (LT _ _ SUB) as [ contra | contra ];
        destruct addr; cbn in contra; lia.
    - intros SUB.
      cbn in EQ.
      destruct (addr |-> vs_hd $+ m) as [m'' | ] eqn:Esum; try discriminate.
      destruct n.
      + cbn in *; rewrite Addr.shift_fw_0 in SUB.
        specialize (of_listi_preserves _ _ _ _ EQ _ _ ltac:(eexists; apply Esum)) as SUB'.
        f_equal.
        eapply one_fun; eauto.
      + cbn.
        replace (Addr.shift_fw addr (N.of_nat (S n))) with (Addr.shift_fw (Addr.shift_fw addr 1) (N.of_nat n)) in SUB.
        eapply IHvs_tl; [ | apply EQ | apply SUB ].
        intros a_any v_any SUB_any.
        specialize (proj1 (one_discriminate _ _ _ _ Esum a_any v_any) SUB_any) as [ [ EQ1 EQ2 ] | [ NE SUB' ] ];
          subst.
        right; destruct addr; cbn; lia.
        specialize (LT a_any v_any SUB') as [ NEb | LTo ].
        destruct addr; left; apply NEb.
        destruct addr; right; cbn in *; lia.
        change (S n) with (1 + n).
        now rewrite Nat2N.inj_add, Addr.shift_fw_twice.
  Qed.

  Definition of_list [M: Memory] addr vs :=
    match @of_listi M $0 addr vs with
    | Some m => m
    | None => $0
    end.

  Lemma of_list_spec [M: Memory] addr vs
    n v
    : List.nth_error vs n = Some v <-> (Addr.shift_fw addr (N.of_nat n)) |-> v $<= (@of_list M addr vs).
  Proof.
    unfold of_list.
    destruct (@of_listi_emp_some M addr vs) as (m' & EQ).
    rewrite EQ.
    eapply of_listi_spec; [ now intros a' v' contra; apply emp_no_sub in contra | apply EQ].
  Qed.

End Facts.
