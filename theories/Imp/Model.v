From Stdlib Require Import Arith List SetoidList Psatz.
Import ListNotations.
From GallinaC.Utils Require Import ListExt.
From GallinaC.Imp Require Import Memval.
From GallinaC.Utils Require GenId.
From GallinaC.Imp Require Store Heap.

Section ListStore.

  Import Store.

  Record list_store: Type :=
    mkListStore
      {
        ls_bindings : list (Nat.t * memval);
        ls_next_var : Nat.t
      }.

  Definition list_store_emp: list_store := mkListStore [] 0.

  Definition list_store_lookup (s: list_store) n := findA (Nat.eqb n) (ls_bindings s).
  Definition list_store_mutate (s: list_store) n v :=
    match findA (Nat.eqb n) (ls_bindings s) with
    | Some _ => Some (mkListStore (@replace _ _ Nat.eq_dec n v (ls_bindings s)) (ls_next_var s))
    | None => None
    end.
  Definition list_store_push (s: list_store) v :=
    let n := ls_next_var s in
    let next_id := S (ls_next_var s) in
    (mkListStore ((n,v)::(ls_bindings s)) next_id, n).
  Definition list_store_pop (s: list_store) :=
    match ls_bindings s with [] => None | _::s' => Some (mkListStore s' (ls_next_var s)) end.

  Definition list_store_mutate_unchecked (s: list_store) n v :=
    match findA (Nat.eqb n) (ls_bindings s) with
    | Some _ => mkListStore (@replace _ _ Nat.eq_dec n v (ls_bindings s)) (ls_next_var s)
    | None => mkListStore ((n, v):: ls_bindings s) (ls_next_var s)
    end.

  Local Obligation Tactic := cbn; eauto; unfold list_store_lookup, list_store_mutate, list_store_push, list_store_pop, list_store_mutate_unchecked.

  Program Definition ListStore: Store :=
    {|
      store := list_store;
      name := Nat.t;

      name_eq_dec := Nat.eq_dec;

      emp := list_store_emp;

      BindsTo := fun n v s => BindIn n v (ls_bindings s);
      WF := fun s => Forall (fun x => (fst x) < (ls_next_var s)) (ls_bindings s);
      Empty := fun s => ls_bindings s = [];
      Equal := fun s s' => forall n v, BindIn n v (ls_bindings s) <-> BindIn n v (ls_bindings s');

      lookup := list_store_lookup;
      mutate := list_store_mutate;
      push := list_store_push;
      pop := list_store_pop;

      mutate_unchecked := list_store_mutate_unchecked;
    |}.

  Next Obligation.
    intros n v contra.
    inversion contra.
  Qed.

  Next Obligation.
    cbn; intros s n v w HBindInv HBindInw.
    eapply BindIn_fun; eauto.
  Qed.

  Next Obligation.
    intros s n v Heq contra.
    rewrite Heq in contra.
    inversion contra.
  Qed.

  Next Obligation.
    split; auto.
  Qed.

  Next Obligation.
    intros s n v.
    split.
    - intros HBindIn.
      induction HBindIn as [ n v binds | n v binds n' v' Hneq HBindIn IHBindIn ]; cbn.
      + now rewrite Nat.eqb_refl.
      + apply Nat.eqb_neq in Hneq; now rewrite Hneq.
    - intros HfindA.
      destruct s as [ bindings next_var ].
      induction bindings; cbn in HfindA;
        try discriminate.
      destruct a as [ n' v' ].
      destruct (Nat.eqb_spec n n'); subst.
      + inversion HfindA; subst; left.
      + right; [ auto | now apply IHbindings ].
  Qed.

  Next Obligation.
    intros s n v.
    destruct s as [ binds nvar ];
      cbn;
      split.
    - intros [ v' HBindIn ].
      induction HBindIn as [ n v_old binds | n v_old binds n' v' Hneq HBindIn [ s' IHBindIn ] ].
      + exists (mkListStore ((n,v)::binds)  nvar).
        destruct (findA (Nat.eqb n) ((n, v_old)::binds)) eqn:Efind.
        * cbn.
          destruct (Nat.eq_dec n n); [ clear e | contradiction ].
          reflexivity.
        * cbn in Efind.
          now rewrite Nat.eqb_refl in Efind.
      + exists (mkListStore ((n',v')::ls_bindings s') nvar).
        cbn.
        assert (Hrewrite: n =? n' = false) by (now apply Nat.eqb_neq);
          rewrite Hrewrite; clear Hrewrite.
        destruct (findA (Nat.eqb n) binds) eqn:Efind; try discriminate.
        inversion IHBindIn; subst; clear IHBindIn.
        destruct (Nat.eq_dec n' n); try (congruence).
        reflexivity.
    - induction binds as [ | [ n' v' ] binds IHbinds ];
        intros [ s' HfindA ].
      + destruct (@findA nat memval (Nat.eqb n) []) eqn:Efind;
          cbn in Efind; discriminate.
      + cbn in HfindA.
        destruct (Nat.eqb_spec n' n) as [ Heq | Hneq ]; subst.
        * rewrite (Nat.eqb_refl n) in HfindA.
          destruct (Nat.eq_dec n n) as [ Heq | Hneq ]; [ clear Heq | contradiction ].
          exists v'.
          now constructor.
        * destruct (Nat.eqb_spec n n') as [ Heq | _ ], (Nat.eq_dec n' n); try (congruence).
          destruct (findA (Nat.eqb n) binds) eqn:EfindA; try (discriminate).
          destruct IHbinds as [ v_old HBindIn ].
          eexists; reflexivity.
          exists v_old.
          right; [ congruence | assumption ].
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] Hmutate;
      cbn; cbn in Hmutate.
    destruct (findA (Nat.eqb n) binds) as [ v' | ] eqn:Efind; [ | discriminate ].
    inversion Hmutate; subst; clear Hmutate.
    clear nvar'.
    revert n v v' Efind.
    induction binds as [ | [ n'' v'' ] ]; [ discriminate | ].
    intros.
    cbn.
    destruct (Nat.eq_dec n'' n) as [ Heq | Hneq ]; [ subst; cbn in Efind; rewrite Nat.eqb_refl in Efind; inversion Efind; subst; clear Efind | ].
    constructor; now inversion HForall.
    constructor.
    now symmetry.
    eapply IHbinds; eauto.
    cbn in Efind.
    destruct (Nat.eqb_spec n n''); [ congruence | eauto ].
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] n' v' Hneq Hmutate.
    cbn.
    cbn in Hmutate.
    destruct (findA (Nat.eqb n) binds) eqn:Efind; [ | discriminate ].
    inversion Hmutate; subst; clear Hmutate.
    induction binds as [ | [ n'' v'' ] binds IHbinds ].
    - split; intros H; cbn in H; now inversion H.
    - cbn.
      split; intros HBindIn.
      + destruct (Nat.eq_dec n'' n) as [ Heq | Hneq'' ]; subst.
        cbn in Efind.
        rewrite Nat.eqb_refl in Efind.
        inversion Efind; subst; clear Efind.
        right.
        now symmetry.
        inversion HBindIn; [ congruence | now auto ].
        cbn in Efind.
        destruct (Nat.eqb_spec n n'') as [ Heq | _ ]; [ congruence | ].
        inversion HBindIn; subst.
        left.
        right; auto.
        apply IHbinds; auto.
      + destruct (Nat.eq_dec n'' n) as [ Heq | Hneq'' ]; [ subst | ].
        right; auto.
        inversion HBindIn; [ congruence | auto ].
        inversion HBindIn as [ | ?x ?y ?l ?x' ?y' ?Hneq HBindIn' ]; [ now left | subst ].
        right; auto.
        apply IHbinds; auto.
        cbn in Efind.
        destruct (Nat.eqb_spec n n''); [ congruence | assumption ].
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] HForall Hmutate.
    cbn; cbn in HForall, Hmutate.
    destruct (findA (Nat.eqb n) binds) as [ v'' | ] eqn:Efind; [ inversion Hmutate; subst; clear Hmutate | discriminate ].
    induction binds as [ | [ n' v' ] binds IHbinds ]; [ constructor | ].
    cbn.
    cbn in Efind.
    destruct (Nat.eqb_spec n n') as [ Heq | Hneq ], (Nat.eq_dec n' n) as [ Heq' | Hneq' ];
      try (subst n'; clear Heq Heq');
      try (congruence);
      try (clear Hneq').
    inversion Efind; subst v''; clear Efind.
    constructor; now inversion HForall.
    constructor.
    now inversion HForall.
    apply IHbinds; auto.
    now inversion HForall.
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] v' HForall Hpush contra.
    cbn in HForall, Hpush, contra.
    inversion Hpush; subst; clear Hpush.
    induction binds.
    - inversion contra.
    - inversion HForall as [ | x l Hlt HForall' ]; subst.
      inversion contra; [ subst; cbn in Hlt; lia | subst ].
      apply IHbinds; auto.
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] HForall Hpush.
    unfold list_store_push in Hpush;
      cbn; cbn in HForall, Hpush.
    inversion Hpush; subst.
    constructor.
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] HForall Hpush.
    cbn; cbn in HForall, Hpush.
    inversion Hpush; subst; clear Hpush.
    constructor; [ cbn; lia | ].
    eapply Forall_impl; [ | apply HForall ].
    cbn; lia.
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] Hpush.
    cbn; cbn in Hpush.
    inversion Hpush; subst; clear Hpush.
    eexists; split; [ reflexivity | ].
    intros n' v'; split.
    - intros HBindIn.
      induction HBindIn; now constructor.
    - now cbn.
  Qed.

  Next Obligation.
    intros [ binds nvar ] [ binds' nvar' ] HWF Hpop.
    cbn; cbn in HWF, Hpop.
    destruct binds as [ | [ n v ] binds ]; [ discriminate | ].
    inversion Hpop; subst; clear Hpop.
    now inversion HWF.
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v n' v'.
    cbn.
    split.
    - intros [ [ Heqn Heqv ] | [ Hneqn HBindIn ] ]; subst; cbn.
      + induction binds as [ | [ n v ] binds IHbinds ]; cbn.
        * constructor.
        * destruct (findA (Nat.eqb n') binds) eqn:Efind.
          -- cbn in IHbinds.
             destruct (Nat.eqb_spec n n') as [ Heq | Hneq ]; subst;
               repeat (rewrite Nat.eqb_refl); cbn.
             destruct (Nat.eq_dec n' n') as [ H | H ]; [ clear H | contradiction ].
             left.
             destruct (Nat.eqb_spec n' n) as [ H | H ]; [ congruence | clear H ].
             cbn.
             destruct (Nat.eq_dec n n') as [ | H ]; [ congruence | clear H].
             now right.
          -- cbn in IHbinds.
             destruct (Nat.eqb_spec n' n) as [ Heq | Hneq ]; subst;
               repeat (rewrite Nat.eqb_refl);
               cbn.
             destruct (Nat.eq_dec n n) as [ H | H ]; [ now left | contradiction ].
             left.
      + destruct (findA (Nat.eqb n') binds) eqn:Efind.
        * cbn.
          induction binds as [ | [ n'' v'' ] binds ]; [ discriminate | ].
          cbn; cbn in Efind.
          destruct (Nat.eqb_spec n'' n') as [ Heq | Hneq ], (Nat.eq_dec n'' n') as [ Heq' | Hneq' ];
            (try (congruence));
            subst;
            (try clear Heq');
            (try clear Hneq').
          rewrite Nat.eqb_refl in Efind.
          inversion Efind; subst.
          constructor; auto.
          inversion HBindIn; [ contradiction | auto ].
          destruct (Nat.eqb_spec n' n'') as [ Heq | _ ]; [ congruence | ].
          inversion HBindIn; subst.
          constructor.
          right; auto.
        * now constructor.
    - induction binds as [ | [ n'' v'' ] binds ].
      + cbn.
        intros HBindIn.
        inversion HBindIn as [ | ?x ?y ?l ?x' ?y' ?Hneq ?HBindIn' ]; subst.
        now repeat constructor.
        inversion HBindIn'.
      + cbn.
        intros HBindIn.
        destruct (Nat.eqb_spec n'' n') as [ Heq | Hneq ]; subst.
        * rewrite Nat.eqb_refl in HBindIn.
          cbn in HBindIn.
          destruct (Nat.eq_dec n' n') as [ H | H ]; [ clear H | contradiction ].
          inversion HBindIn; subst.
          left; split; auto.
          right; split; auto.
          right; auto.
        * destruct (Nat.eqb_spec n' n'') as [ Heq | _ ]; [ congruence | ].
          destruct (Nat.eq_dec n'' n') as [ H | _ ]; [ contradiction | ].
          destruct (findA (Nat.eqb n') binds) as [ v''' | ] eqn:Efind; [ | ];
            cbn in HBindIn, IHbinds.
          (inversion HBindIn as [ | ?x ?y ?l ?x' ?y' ?Hneq HBindIn' ]; subst);
          [
            now repeat constructor
          |
            destruct (IHbinds HBindIn') as [ H | H ];
            [ destruct H; subst; now repeat constructor
            | destruct H; now repeat constructor ]
          ].
          inversion HBindIn as [ | ?x ?y ?l ?x' ?y' ?Hneq HBindIn' ]; subst.
          now repeat constructor.
          right; now split.
  Qed.

  Next Obligation.
    intros n v [ binds nvar ] v_old HBindIn.
    cbn; cbn in HBindIn.
    induction HBindIn.
    - cbn.
      rewrite Nat.eqb_refl.
      reflexivity.
    - cbn.
      destruct (Nat.eqb_spec x x') as [ Heq | _ ]; [ congruence | ].
      destruct (Nat.eq_dec x' x) as [ Heq | _ ]; [ congruence | ].
      destruct (findA (Nat.eqb x) l) eqn:Efind; congruence.
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] [ binds'' nvar'' ] v' Hpush Hmutate.
    cbn; cbn in Hpush.
    inversion Hpush; subst; clear Hpush.
    cbn in Hmutate.
    rewrite Nat.eqb_refl in Hmutate.
    destruct (Nat.eq_dec n n) as [ _ | Hneq ]; [ | congruence ].
    inversion Hmutate; subst.
    reflexivity.
  Qed.

End ListStore.

Canonical ListStore.

Section OptionAllocator.
  Import Algebra Arith GenId ssrfun.Option.

  Local Obligation Tactic := (try (intros [ [x|] ];
                                   (try intros [ [y|] ]);
                                   (try intros [ [z|] ]);
                                   first [ reflexivity | discriminate ])).

  Local Open Scope bool_scope.
  Local Open Scope program_scope.

  Record option_alloc: Set :=
    mkOptAlloc
      {
        next: option nat;
      }.

  Definition option_alloc_unit: option_alloc := mkOptAlloc None.

  Definition option_alloc_sum (l r: option_alloc): option option_alloc :=
    match l, r with
    | mkOptAlloc None, mkOptAlloc None => Some (mkOptAlloc None)
    | mkOptAlloc (Some n), mkOptAlloc None
    | mkOptAlloc None, mkOptAlloc (Some n) => Some (mkOptAlloc (Some n))
    | mkOptAlloc (Some _), mkOptAlloc (Some _) => None
    end.

  Definition option_alloc_get (a: option_alloc): option nat := next a.

  Definition option_alloc_next (a: option_alloc): option_alloc :=
    match a with
    | mkOptAlloc None => mkOptAlloc None
    | mkOptAlloc (Some n) => mkOptAlloc (Some (S n))
    end.

  Program Definition option_alloc_separation: Separation :=
    {|
      Algebra.carrier := option_alloc;
      op := option_alloc_sum;
      id_e := option_alloc_unit;
    |}.

  Program Definition option_alloc_genid: GenId :=
    {|
      GenId.carrier := option_alloc_separation;
      GenId.get := option_alloc_get;
      GenId.next := option_alloc_next;
    |}.
  Next Obligation.
    intros [[id0|] ]; cbn; intros id1 EQ.
    inversion EQ; subst; clear EQ.
    now eexists.
    discriminate.
  Qed.

  Next Obligation.
    intros [[id0'|] ]; cbn; intros id0 id1 EQ1 EQ2.
    inversion EQ1; subst; inversion EQ2; subst; clear EQ1 EQ2; lia.
    discriminate.
  Qed.

  Next Obligation.
    intros [[id0|] ] [[id1|]] ([[id2|]] & EQ); cbn in *;
      unfold "$+" in *; cbn in *;
      first
        [ discriminate
        | left; discriminate
        | auto ].
  Qed.

  Next Obligation.
    intros [[id0|] ] [[id1|] ] ([[id2|]] & EQ);
      cbn in *; unfold "$+" in *; cbn in *;
      first
        [ discriminate
        | eexists; reflexivity
        | auto ].
  Qed.

End OptionAllocator.

Canonical option_alloc_separation.
Canonical option_alloc_genid.

Section ListHeap.

  Import Algebra Heap Arith NArith ssrfun.Option.

  Local Obligation Tactic := idtac.
  Local Open Scope bool_scope.
  Local Open Scope separation_scope.

  Definition memblock: Set := list (option memval).
  Record list_heap_carrier: Set :=
    mkListHeap
      {
        list_heap: list memblock;
        alloc: bool;
      }.

  Fixpoint memblock_sum (l r: memblock): option memblock :=
    match l, r with
    | [], [] => Some []
    | [], ((_::_) as mb)
    | ((_::_) as mb), []
      => Some mb
    | Some vl::l, Some vr::r => None
    | None::l, None::r =>
        match memblock_sum l r with
        | Some mb => Some (None::mb)
        | None => None
        end
    | Some v::l, None::r
    | None::l, Some v::r
      => match memblock_sum l r with
         | Some mb =>  Some ((Some v)::mb)
         | None => None
         end
    end.

  Lemma memblock_sum_id_l (mb: memblock): memblock_sum [] mb = Some mb.
  Proof.
    induction mb as [| [v|] mb]; cbn; auto.
  Qed.

  Lemma memblock_sum_id_r (mb: memblock): memblock_sum mb [] = Some mb.
  Proof.
    induction mb as [| [v|] mb]; cbn; auto.
  Qed.

  Lemma memblock_sum_comm (l r: memblock): memblock_sum l r = memblock_sum r l.
  Proof.
    revert r.
    induction l as [| [vl|] l]; intros.
    - now rewrite memblock_sum_id_r, memblock_sum_id_l.
    - cbn.
      destruct r as [| [vr|] r]; auto.
      now rewrite IHl.
    - cbn.
      destruct r as [| [vr|] r].
      now rewrite memblock_sum_id_l.
      now rewrite IHl.
      now rewrite IHl.
  Qed.

  Lemma memblock_sum_assc (x y z: memblock): bind (Basics.flip memblock_sum z) (memblock_sum x y) = bind (memblock_sum x) (memblock_sum y z).
  Proof.
    revert x z.
    induction y as [| vy y]; intros [| vx x] [| vz z]; auto;
      try (now destruct vx; auto);
      try (now destruct vy; auto).
    - unfold flip, bind, apply;
        rewrite memblock_sum_id_l; cbn -[memblock_sum].
      now destruct (memblock_sum _ _); [ rewrite memblock_sum_id_l | ].
    - unfold flip, bind, apply.
      rewrite memblock_sum_id_r.
      now destruct (memblock_sum _ _); [ rewrite memblock_sum_id_r | ].
    - specialize (IHy x z).
      destruct vx as [vx|], vy as [vy|], vz as [vz|]; auto.
      now cbn; destruct (memblock_sum y z); cbn; auto.
      now cbn; destruct (memblock_sum x y), (memblock_sum y z) eqn:Eyz; cbn; auto.
      cbn; destruct (memblock_sum x y) as [xy|], (memblock_sum y z) as [yz|]; cbn; auto.
      now cbv -[memblock_sum] in IHy; rewrite IHy.
      now cbv -[memblock_sum] in IHy; rewrite IHy.
      now cbn in IHy; rewrite <- IHy.
      now cbn; destruct (memblock_sum x y).
      revert IHy;
        cbn; destruct (memblock_sum x y) as [xy|]; unfold flip; cbn.
      destruct (memblock_sum xy z) as [xyz|]; cbn.
      destruct (memblock_sum y z) as [yz|]; cbn; [ now intros EQ; rewrite <- EQ| discriminate].
      destruct (memblock_sum y z) as [yz|]; cbn; [ now intros EQ; rewrite <- EQ| reflexivity ].
      destruct (memblock_sum y z) as [yz|]; cbn; [ now intros EQ; rewrite <- EQ| reflexivity ].
      revert IHy;
        cbn; destruct (memblock_sum x y) as [xy|]; unfold flip; cbn.
      now destruct (memblock_sum y z) as [yz|]; cbn; intros EQ; rewrite EQ.
      destruct (memblock_sum y z); [ | reflexivity ].
      now cbn; intros EQ; rewrite <- EQ.
      revert IHy; cbn.
      destruct (memblock_sum x y) as [xy|]; unfold flip; cbn;
        destruct (memblock_sum y z) as [yz|]; cbn;
        intros EQ; first [ rewrite EQ | rewrite <- EQ | auto ]; auto.
      now destruct (memblock_sum x yz).
  Qed.

  Fixpoint memblocks_sum (l r: list memblock): option (list memblock) :=
    match l, r with
    | [], mbs | mbs, [] => Some mbs
    | mbl::mbsl, mbr::mbsr =>
        match memblock_sum mbl mbr, memblocks_sum mbsl mbsr with
        | Some mb, Some mbs => Some (mb::mbs)
        | None, _ | _, None => None
        end
    end.

  Lemma memblocks_sum_id_l mbs: memblocks_sum [] mbs = Some mbs.
  Proof.
    induction mbs; auto.
  Qed.

  Lemma memblocks_sum_id_r mbs: memblocks_sum mbs [] = Some mbs.
  Proof.
    induction mbs; auto.
  Qed.

  Lemma memblocks_sum_comm (mbsl mbsr: list memblock): memblocks_sum mbsl mbsr = memblocks_sum mbsr mbsl.
  Proof.
    revert mbsr.
    induction mbsl as [|mbl mbsl]; intros.
    - now rewrite memblocks_sum_id_l, memblocks_sum_id_r.
    - destruct mbsr as [|mbr mbsr]; cbn; auto.
      now rewrite memblock_sum_comm, IHmbsl.
  Qed.

  Lemma memblocks_sum_assc (x y z: list memblock): bind (flip memblocks_sum z) (memblocks_sum x y) = bind (memblocks_sum x) (memblocks_sum y z).
  Proof.
    revert y z.
    induction x as [|mbx x]; intros.
    - unfold flip; rewrite memblocks_sum_id_l; cbn.
      now destruct (memblocks_sum y z).
    - destruct y as [|mby y], z as [|mbz z]; auto.
      unfold flip; rewrite memblocks_sum_id_r; cbn.
      destruct (memblock_sum mbx mby); [ | reflexivity ].
      now destruct (memblocks_sum x y).
      specialize (IHx y z); revert IHx.
      specialize (memblock_sum_assc mbx mby mbz).
      unfold flip; cbn.
      destruct (memblock_sum mbx mby) as [mbxy|]; cbn;
        destruct (memblock_sum mby mbz) as [mbyz|]; cbn;
        destruct (memblocks_sum x y) as [xy|]; cbn;
        destruct (memblocks_sum y z) as [yz|]; cbn;
        auto;
        intros EQmb EQmbs;
        (try (now rewrite EQmb, EQmbs));
        (try now rewrite EQmb);
        (try now rewrite <- EQmb).
      now destruct (memblock_sum mbxy mbz); [ rewrite EQmbs | ].
      now destruct (memblock_sum mbx mbyz); [ rewrite <- EQmbs | ].
  Qed.

  Lemma memblocks_sum_length_max: forall [mbsl mbsr mbs] (EQ: memblocks_sum mbsl mbsr = Some mbs), length mbs = Nat.max (length mbsl) (length mbsr).
  Proof.
    induction mbsl as [|mbl mbsl].
    - intros mbsr mbs; rewrite memblocks_sum_id_l; cbn; congruence.
    - intros [|mbr mbsr] mbs; cbn; intros EQ.
      inversion EQ; subst; clear EQ; auto.
      destruct (memblock_sum mbl mbr); try discriminate.
      destruct (memblocks_sum mbsl mbsr) as [mbs'|] eqn:E;
        inversion EQ; subst; clear EQ.
      cbn.
      f_equal.
      now apply IHmbsl.
  Qed.

  Definition list_heap_sum (l r: list_heap_carrier): option list_heap_carrier :=
    match l, r with
    | mkListHeap mbsl allocl, mkListHeap mbsr allocr =>
        if (allocl && allocr) || (allocl && (length mbsl <? length mbsr)) || (allocr && (length mbsr <? length mbsl))
        then
          None
        else
          match memblocks_sum mbsl mbsr with
          | Some mbs => Some (mkListHeap mbs (allocl || allocr))
          | None => None
          end
    end.

  Definition list_heap_unit: list_heap_carrier := mkListHeap [] false.

  Fixpoint memblock_one (o: nat) (v: memval): memblock :=
    match o with
    | 0 => [Some v]
    | S o => None::(memblock_one o v)
    end.

  Lemma memblock_one_inj (o o': nat) (v v': memval):
    memblock_one o v = memblock_one o' v' <-> o = o' /\ v = v'.
  Proof.
    split; [ intros EQ; split | intros [ EQo EQv ] ].
    - revert o' v v' EQ.
      induction o; intros.
      + destruct o'; [ reflexivity | discriminate ].
      + destruct o'; [ discriminate | cbn in EQ ].
        f_equal; eapply IHo.
        injection EQ; eauto.
    - revert o' v v' EQ.
      induction o; intros;
        destruct o';
        [ now inversion EQ
        | discriminate
        | discriminate
        | eapply IHo; injection EQ; eauto ].
    - now subst.
  Qed.

  Lemma memblock_one_ne_addr o o' v v'
    : o <> o' <-> exists mb', memblock_sum (memblock_one o v) (memblock_one o' v') = Some mb'.
  Proof.
    split; [ intros NE | intros (mb' & EQ)].
    - revert o' NE;
        induction o; intros.
      destruct o';
        [ contradiction |
          cbn; destruct (memblock_one o' v'); eexists; reflexivity].
      destruct o';
        [ cbn; rewrite memblock_sum_id_r; eexists; reflexivity
        | specialize (IHo o' ltac:(apply Nat.succ_inj_wd_neg, NE)) as (mb' & EQ);
          cbn; rewrite EQ; eexists; reflexivity ].
    - intros contra; subst o'.
      revert mb' EQ.
      induction o; intros; [ discriminate | ].
      cbn in EQ; destruct (memblock_sum _ _); [ destruct mb'; [ discriminate | inversion EQ; subst ]; apply (IHo mb'); auto | discriminate ].
  Qed.

  Fixpoint memblocks_one (b o: nat) (v: memval): list memblock :=
    match b with
    | 0 => [memblock_one o v]
    | S b => []::(memblocks_one b o v)
    end.

  Lemma memblocks_one_inj b b' o o' v v':
    memblocks_one b o v = memblocks_one b' o' v' <-> b = b' /\ o = o' /\ v = v'.
  Proof.
    split; [ intros EQ; split; [|split] | now intros ( EQb & EQo & EQv); subst ];
      revert b' o o' v v' EQ; induction b;
      intros.
    - destruct b'; [ reflexivity | cbn in EQ ].
      destruct o; discriminate.
    - destruct b'; [ destruct o, o'; cbn in EQ; discriminate  | cbn in EQ; injection EQ as EQ ].
      f_equal; eapply IHb, EQ.
    - destruct b'; [ cbn in EQ; injection EQ as EQ; eapply memblock_one_inj, EQ | destruct o, o'; discriminate ].
    - destruct b'; [ destruct o, o'; discriminate | ].
      injection EQ as EQ. eapply IHb, EQ.
    - destruct b'; [ injection EQ as EQ; eapply memblock_one_inj, EQ | ].
      destruct o, o'; discriminate.
    - destruct b'; [ destruct o, o'; discriminate | injection EQ; eapply IHb ].
  Qed.

  Lemma memblocks_one_ne_block b b' o o' v v'
    : (b <> b') -> exists mbs', memblocks_sum (memblocks_one b o v) (memblocks_one b' o' v') = Some mbs'.
  Proof.
    intros NE.
    revert b' NE.
    induction b; intros.
    - destruct b'; [ contradiction | clear NE ]; cbn.
      rewrite memblock_sum_id_r; eexists; reflexivity.
    - destruct b'; [ destruct o, o'; cbn; try rewrite memblocks_sum_id_r; eexists; reflexivity | ].
      cbn.
      specialize (IHb b' ltac:(apply Nat.succ_inj_wd_neg, NE)) as (mbs' & EQ).
      now rewrite EQ; eexists.
  Qed.

  Lemma memblocks_one_eq_block_ne_offset b o o' v v'
    : o <> o' <-> exists mbs', memblocks_sum (memblocks_one b o v) (memblocks_one b o' v') = Some mbs'.
  Proof.
    split; [ intros NE | ].
    - revert o o' NE.
      induction b.
      + intros o o' NE; cbn.
        specialize (proj1 (memblock_one_ne_addr o o' v v') NE) as (mb' & EQ).
        rewrite EQ; eexists; reflexivity.
      + intros o o' NE; cbn.
        specialize (IHb o o' NE) as (mbs' & EQ).
        rewrite EQ; eexists; reflexivity.
    - intros (mbs' & EQ).
      revert mbs' EQ; induction b; intros.
      + cbn in EQ.
        destruct (memblock_sum _ _) eqn:E; [ | discriminate].
        eapply memblock_one_ne_addr.
        eexists; apply E.
      + cbn in EQ. destruct (memblocks_sum _ _) eqn:E; [ | discriminate ].
        inversion EQ; subst.
        now eapply IHb.
  Qed.

  Lemma memblocks_one_ne_addr b b' o o' v v'
    : (b <> b' \/ o <> o') <-> exists mbs', memblocks_sum (memblocks_one b o v) (memblocks_one b' o' v') = Some mbs'.
  Proof.
    split; [ intros [ NE | NE ] | intros (mbs' & EQ) ].
    - now apply memblocks_one_ne_block.
    - now destruct (Nat.eq_dec b b'); [ subst; apply memblocks_one_eq_block_ne_offset | apply memblocks_one_ne_block ].
    - destruct (Nat.eq_dec b b'); [ subst b'; right | now left ].
      apply (memblocks_one_eq_block_ne_offset b o o' v v'); eexists mbs'; apply EQ.
  Qed.

  Definition list_heap_one (addr: Addr.t) (v: memval): list_heap_carrier :=
    match addr with
    | Addr.mkAddr b o =>
        mkListHeap (memblocks_one b (N.to_nat o) v) false
    end.

  Lemma list_heap_one_inj addr addr' v v'
    : list_heap_one addr v = list_heap_one addr' v' <-> addr = addr' /\ v = v'.
  Proof.
    split; [ | now intros [EQa EQv]; subst ].
    unfold list_heap_one.
    destruct addr, addr'. intros EQ; injection EQ as EQ.
    apply memblocks_one_inj in EQ as (EQb & EQo & EQv).
    apply N2Nat.inj in EQo; split; f_equal; congruence.
  Qed.

  Lemma list_heap_one_ne_addr a a' v v'
    : a <> a' <-> exists lh', list_heap_sum (list_heap_one a v) (list_heap_one a' v') = Some lh'.
  Proof.
    destruct a as [b o], a' as [b' o'].
    split; [ intros NE | intros (lh' & EQ) ].
    - cbn.
      specialize (proj1 (memblocks_one_ne_addr b b' (N.to_nat o) (N.to_nat o') v v')) as (mbs' & EQ).
      destruct (Nat.eq_dec b b'); [ subst b' | now left].
      destruct (N.eq_dec o o') as [|NEo]; [ subst; contradiction | right; intros contra; apply NEo, N2Nat.inj, contra ].
      rewrite EQ.
      eexists; reflexivity.
    - intros contra.
      cbn in EQ.
      destruct (memblocks_sum _ _) eqn:E; [clear lh' EQ | discriminate ].
      injection contra; intros; subst b' o'; clear contra.
      apply (proj2 (memblocks_one_eq_block_ne_offset b (N.to_nat o) (N.to_nat o) v v')); auto.
      eexists; apply E.
  Qed.

  Fixpoint memblock_with_one (mb: memblock) (o: nat) (v: memval): bool :=
    match o, mb with
    | 0, Some v'::_ => if Memval.eq_dec v v' then true else false
    | S o, _::mb => memblock_with_one mb o v
    | _, _ => false
    end.

  Fixpoint memblocks_with_one (mbs: list memblock) (b o: nat) (v: memval): bool :=
    match b, mbs with
    | 0, mb::_ => memblock_with_one mb o v
    | S b, _::mbs => memblocks_with_one mbs b o v
    | _, _ => false
    end.

  Definition list_heap_with_one (lh: list_heap_carrier) (a: Addr.t) (v: memval): bool :=
    match lh, a with
    | mkListHeap mbs _, Addr.mkAddr b o =>
        memblocks_with_one mbs b (N.to_nat o) v
    end.

  Fixpoint memblock_contains (mb: memblock) (o: nat): bool :=
    match o, mb with
    | 0, Some _::_ => true
    | S o, _::mb => memblock_contains mb o
    | _, _ => false
    end.

  Fixpoint memblocks_contains (mbs: list memblock) (b o: nat): bool :=
    match b, mbs with
    | 0, mb::_ => memblock_contains mb o
    | S b, _::mbs => memblocks_contains mbs b o
    | _, _ => false
    end.

  Definition list_heap_contains (lh: list_heap_carrier) (a: Addr.t): bool :=
    match lh, a with
    | mkListHeap mbs _, Addr.mkAddr b o =>
        memblocks_contains mbs b (N.to_nat o)
    end.

  Lemma list_heap_sum_comm: forall x y, list_heap_sum x y = list_heap_sum y x.
  Proof.
    intros [ mbx allocx ] [ mby allocy ].
    cbn -[Nat.ltb].
    rewrite (Bool.andb_comm allocy allocx).
    destruct (allocx && allocy) eqn:Ealloc; [ reflexivity | cbn -[Nat.ltb] ].
    rewrite (Bool.orb_comm (allocy && _) _).
    destruct (allocx && (length mbx <? length mby)); [ reflexivity | cbn -[Nat.ltb] ].
    destruct (allocy && (length mby <? length mbx)); [ reflexivity | cbn -[Nat.ltb] ].
    rewrite (memblocks_sum_comm mby mbx).
    destruct (memblocks_sum mbx mby); auto.
    destruct allocx, allocy; reflexivity.
  Qed.

  Definition list_heap_emp_with_alc (alc: option_alloc): list_heap_carrier :=
    match alc with
    | mkOptAlloc (Some n) =>
        mkListHeap (List.repeat [] n) true
    | mkOptAlloc None =>
        mkListHeap [] false
    end.

  Fixpoint memblocks_to_allocator (mbs: list memblock) (acc: nat): option_alloc :=
    match mbs with
    | [] => mkOptAlloc (Some acc)
    | _::mbs => memblocks_to_allocator mbs (S acc)
    end.

  Definition list_heap_to_allocator (lh: list_heap_carrier): option_alloc :=
    match lh with
    | mkListHeap mbs true => memblocks_to_allocator mbs 0
    | mkListHeap _ false => mkOptAlloc None
    end.

  Definition memblock_lookup (mb: memblock) (o: nat): option memval :=
    List.nth o mb None.

  Definition memblocks_lookup (mbs: list memblock) (b o: nat): option memval :=
    match List.nth_error mbs b with
    | Some mb => memblock_lookup mb o
    | None => None
    end.

  Definition list_heap_lookup (lh: list_heap_carrier) (p: Pointer.t): option memval :=
    match lh, p with
    | mkListHeap mbs _, Some(Addr.mkAddr b o, prov) =>
        if Pointer.allows p Operation.Read
        then
          memblocks_lookup mbs b (N.to_nat o)
        else
          None
    | _, None => None
    end.

  Fixpoint memblock_mutate (mb: memblock) (o: nat) (v: memval): option memblock :=
    match mb, o with
    | Some _::mb, 0 => Some ((Some v)::mb)
    | vo::mb, S o =>
        match memblock_mutate mb o v with
        | Some mb => Some (vo::mb)
        | None => None
        end
    | None::_, 0 | [], _ => None
    end.


  Fixpoint memblocks_mutate (mbs: list memblock) (b o: nat) (v: memval): option (list memblock) :=
    match mbs, b with
    | mb::mbs, 0 =>
        match memblock_mutate mb o v with
        | Some mb => Some (mb::mbs)
        | None => None
        end
    | mb::mbs, S b =>
        match memblocks_mutate mbs b o v with
        | Some mbs => Some(mb::mbs)
        | None => None
        end
    | [], _ => None
    end.

  Definition list_heap_mutate (lh: list_heap_carrier) (p: Pointer.t) (v: memval): option list_heap_carrier :=
    match lh, p with
    | mkListHeap mbs alloc, Some (Addr.mkAddr b o, prov) =>
        if Pointer.allows p Operation.Write then
          match memblocks_mutate mbs b (N.to_nat o) v with
          | Some mbs => Some (mkListHeap mbs alloc)
          | None => None
          end
        else
          None
    | _, None => None
    end.

  Definition list_heap_alloc (lh: list_heap_carrier) (sz: N.t) (v: memval): option (list_heap_carrier * Pointer.t) :=
    match lh with
    | mkListHeap mbs true =>
        Some (mkListHeap (mbs++[List.repeat (Some v) (N.to_nat sz)]) true, Some(Addr.mkAddr (length mbs) 0%N, Provenance.Allocation (length mbs) 0 sz 0 sz Permission.Free))
    | mkListHeap _ false => None
    end.

  Fixpoint memblocks_free (mbs: list memblock) (b: nat): option (list memblock) :=
    match mbs, b with
    | (_::_)::mbs, 0 => Some ([]::mbs)
    | mb::mbs, S b =>
        match memblocks_free mbs b with
        | Some mbs => Some (mb::mbs)
        | None => None
        end
    (* Double-free *)
    | []::_, _ => None
    (* Heap doesn't contain block *)
    | [], _ => None
    end.

  Definition list_heap_free (lh: list_heap_carrier) (p: Pointer.t): option list_heap_carrier :=
    match lh, p with
    | mkListHeap mbs alloc, Some(Addr.mkAddr b 0, prov) =>
        if Pointer.allows p Operation.Free then
          match memblocks_free mbs b with
          | Some mbs => Some (mkListHeap mbs alloc)
          | None => None
          end
        else
          None
    | _, _ => None
    end.


  Program Definition list_heap_separation: Separation :=
    {|
      Algebra.carrier := list_heap_carrier;
      op := list_heap_sum;
      id_e := list_heap_unit;
      op_comm := list_heap_sum_comm;
    |}.

  Local Opaque Nat.ltb.

  Next Obligation.
    intros [ mbx allocx ] [ mby allocy ] [ mbz allocz ].
    specialize (memblocks_sum_assc mbx mby mbz).
    unfold flip, list_heap_sum; cbn.
    destruct allocx, allocy, allocz;
      cbn.
    now destruct (Nat.ltb_spec (length mby) (length mbz)).
    destruct (Nat.ltb_spec (length mby) (length mbz)); [ reflexivity | cbn ].
    now destruct (memblocks_sum mby mbz).
    destruct (Nat.ltb_spec (length mbx) (length mby)); cbn.
    destruct (Nat.ltb_spec (length mbz) (length mby)); cbn.
    now destruct (memblocks_sum mby mbz).
    now destruct (memblocks_sum mby mbz).
    destruct (memblocks_sum mbx mby); cbn.
    destruct (Nat.ltb_spec (length mbz) (length mby)); [ reflexivity | ].
    now destruct (memblocks_sum mby mbz).
    destruct (Nat.ltb_spec (length mbz) (length mby)); [ reflexivity | cbn ].
    now destruct (memblocks_sum mby mbz).
    destruct (Nat.ltb_spec (length mbx) (length mby)); cbn.
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ cbn | reflexivity ].
    destruct (Nat.ltb_spec (length mbx) (length mbyz)); [ reflexivity | cbn ].
    destruct (memblocks_sum mbx mbyz) as [mbxyz|] eqn:Exyz; auto.
    specialize (memblocks_sum_length_max Eyz); lia.
    destruct (memblocks_sum mbx mby) as [mbxy|] eqn:Exy; cbn.
    destruct (Nat.ltb_spec (length mbxy) (length mbz)); cbn.
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ cbn | reflexivity ].
    destruct (Nat.ltb_spec (length mbx) (length mbyz)); [ reflexivity | cbn ].
    destruct (memblocks_sum mbx mbyz); [ | reflexivity ].
    specialize (memblocks_sum_length_max Exy);
    specialize (memblocks_sum_length_max Eyz);
      lia.
    destruct (memblocks_sum mbxy mbz) as [mbxyz|] eqn:Exyz; cbn.
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ cbn | discriminate ].
    destruct (Nat.ltb_spec (length mbx) (length mbyz)); cbn.
    intros Ex_yz.
    specialize (memblocks_sum_length_max Exy);
      specialize (memblocks_sum_length_max Exy).
    specialize (memblocks_sum_length_max Exyz);
      specialize (memblocks_sum_length_max Exyz).
    specialize (memblocks_sum_length_max Eyz);
      specialize (memblocks_sum_length_max Eyz).
    symmetry in Ex_yz;
      specialize (memblocks_sum_length_max Ex_yz);
      specialize (memblocks_sum_length_max Ex_yz).
    lia.
    destruct (memblocks_sum mbx mbyz); congruence.
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ cbn | reflexivity ].
    destruct (Nat.ltb_spec (length mbx) (length mbyz)); [ reflexivity | cbn ].
    destruct (memblocks_sum mbx mbyz) as [mbxyz|] eqn:Ex_yz; [ discriminate | reflexivity ].
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ cbn | reflexivity ].
    destruct (Nat.ltb_spec (length mbx) (length mbyz)); [ reflexivity | cbn ].
    now intros EQ; rewrite <- EQ.
    destruct (Nat.ltb_spec (length mby) (length mbx)); [ reflexivity | ].
    destruct (memblocks_sum mbx mby) as [mb_x_y|] eqn:E_x_y; [ reflexivity | reflexivity ].
    destruct (Nat.ltb_spec (length mby) (length mbx)); cbn.
    destruct (Nat.ltb_spec (length mby) (length mbz)); [ reflexivity | cbn ].
    destruct (memblocks_sum mby mbz) as [mb_y_z|] eqn:E_y_z; [ cbn | reflexivity ].
    destruct (Nat.ltb_spec (length mb_y_z) (length mbx)); [ reflexivity | cbn ].
    destruct (memblocks_sum mbx mb_y_z); [ | reflexivity ].
    specialize (memblocks_sum_length_max E_y_z); lia.
    destruct (memblocks_sum mbx mby) as [mbxy|] eqn:Exy; cbn.
    destruct (Nat.ltb_spec (length mbxy) (length mbz)); cbn.
    destruct (Nat.ltb_spec (length mby) (length mbz)); [ reflexivity | cbn ].
    specialize (memblocks_sum_length_max Exy); lia.
    destruct (Nat.ltb_spec (length mby) (length mbz)); cbn.
    destruct (memblocks_sum mbxy mbz) as [mbxyz|] eqn:Exyz; [ | reflexivity ].
    apply memblocks_sum_length_max in Exyz, Exy; lia.
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; cbn.
    destruct (Nat.ltb_spec (length mbyz) (length mbx)); [ | now intros EQ; rewrite EQ ].
    apply memblocks_sum_length_max in Exy, Eyz; lia.
    now intros EQ; rewrite EQ.
    destruct (Nat.ltb_spec (length mby) (length mbz)); [ reflexivity | cbn ].
    destruct (memblocks_sum mby mbz) as [mbyz|]; [now cbn; intros EQ; rewrite <- EQ; destruct (Nat.ltb _ _) |reflexivity ].
    destruct (memblocks_sum mbx mby) as [mbxy|] eqn:Exy; [apply memblocks_sum_length_max in Exy|];
      cbn.
    destruct (Nat.ltb_spec (length mbz) (length mbxy)); cbn.
    destruct (Nat.ltb_spec (length mbz) (length mby)); [ reflexivity | ].
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ apply memblocks_sum_length_max in Eyz; cbn | reflexivity ].
    destruct (Nat.ltb_spec (length mbyz) (length mbx)); [ reflexivity | lia ].
    destruct (Nat.ltb_spec (length mbz) (length mby)); [ lia | cbn ].
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ apply memblocks_sum_length_max in Eyz; cbn | now intros EQ; rewrite EQ].
    destruct (Nat.ltb_spec (length mbyz) (length mbx)); [ lia | now intros EQ; rewrite EQ ].
    destruct (Nat.ltb_spec (length mbz) (length mby)); [ reflexivity | ].
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ apply memblocks_sum_length_max in Eyz; cbn | reflexivity ].
    destruct (Nat.ltb_spec (length mbyz) (length mbx)); [ reflexivity | now intros EQ; rewrite <- EQ ].
    destruct (memblocks_sum mbx mby) as [mbxy|] eqn:Exy; [ apply memblocks_sum_length_max in Exy; cbn | now cbn; destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; auto; cbn; intros EQ; rewrite <- EQ ].
    intros EQ; rewrite EQ; clear EQ.
    now destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz.
  Qed.

  Next Obligation.
    intros [ mb alloc ]; cbn.
    now destruct (Nat.ltb_spec (length mb) 0); [ lia | rewrite Bool.andb_false_r].
  Qed.

  Next Obligation.
    intros [ mb alloc ]; cbn.
    destruct (Nat.ltb_spec (length mb) 0); [ lia | rewrite Bool.andb_false_r; cbn ].
    now rewrite Bool.orb_false_r, memblocks_sum_id_r.
  Qed.

  Program Definition list_heap_memory: Memory :=
    {|
      mem := list_heap_separation;
      one := list_heap_one;
      with_one := list_heap_with_one;
      contains := list_heap_contains;
      one_inj := list_heap_one_inj;
      one_ne_addr := list_heap_one_ne_addr;
    |}.

  Next Obligation.
    intros [ b o ] v [ [ mbs alloc ] EQ].
    revert EQ.
    unfold "$+", "$0"; cbn;
      unfold list_heap_unit.
    destruct alloc;
      [ destruct (Nat.ltb_spec (length mbs) (length (memblocks_one b (N.to_nat o) v))); [ discriminate | cbn; destruct (memblocks_sum _ _); congruence ]| cbn ].
    destruct (memblocks_sum _ _) eqn:Embs; [ intros EQ; inversion EQ; subst; clear EQ | discriminate ].
    apply memblocks_sum_length_max in Embs.
    cbn in Embs.
    destruct b; cbn in Embs;
      destruct (length mbs); lia.
  Qed.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Program Definition list_heap_heap: Heap :=
    {|
      Heap.heap := list_heap_memory;
      heap_alc := option_alloc_genid;
      emp_with_alc := list_heap_emp_with_alc;
      to_allocator := list_heap_to_allocator;
      lookup := list_heap_lookup;
      mutate := list_heap_mutate;
      Heap.alloc := list_heap_alloc;
      free := list_heap_free;
    |}.

  Next Obligation.
    reflexivity.
  Qed.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

End ListHeap.

Canonical list_heap_separation.
Canonical list_heap_memory.
Canonical list_heap_heap.
