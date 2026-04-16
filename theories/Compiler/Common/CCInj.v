From Stdlib Require Import ZArith Arith List SetoidList Psatz.
Import ListNotations.

From compcert.lib Require Import Maps Integers.
From compcert.common Require Memory Globalenvs.
Import Memory.

From GallinaC.Imp Require Import Memval Pointer Heap Store Primitives Intops Uint32 Uintptr.
From GallinaC.Compiler.Common Require Import Types Value.

Local Open Scope separation_scope.
Local Open Scope heap_scope.

(* Injecting GallinaC concepts into their CompCert equivalents *)

Definition heap_block_map := list (nat * Values.block).
Definition store_block_map {St} := list (@name St * (Values.block * nat * bool)).
Definition fun_block_map := list (AST.ident * Values.block).

Record injection {St}: Type :=
  {
    inj_hp_map: heap_block_map;
    inj_st_map: @store_block_map St;
    inj_fn_map: fun_block_map;
  }.

Arguments inj_hp_map {St} inj: rename.
Arguments inj_st_map {St} inj: rename.
Arguments inj_fn_map {St} inj: rename.

Definition type_mem_chunk (t: type): option AST.memory_chunk :=
  match t with
  | t_unit => None
  | t_bool => Some AST.Mbool
  | t_nat => Some AST.Mint32
  | t_ofst => Some AST.Mptr
  | t_ptr => Some AST.Mptr
  | t_fun ti to => None
  end.

Inductive memval_mem_chunk: memval -> AST.memory_chunk -> Prop :=
| vmchunk_bool: forall b, memval_mem_chunk (VBool b) AST.Mbool
| vmchunk_int: forall n, memval_mem_chunk (VInt n) AST.Mint32
| vmchunk_ptr: forall p, memval_mem_chunk (VPtr p) AST.Mptr
.

Inductive inj_value {St} (inj: @injection St): value -> Values.val -> Prop :=
| inj_bool: forall b,
    inj_value inj (v_bool b) (if b then Values.Vtrue else Values.Vfalse)
| inj_nat: forall (n: nat) i
                  (HBounded: Intops.Unsigned.Bounded n)
                  (Heq: Int.unsigned i = Z.of_nat n),
    inj_value inj (v_nat n) (Values.Vint i)
| inj_ofst: forall (n: N) v
                   (HBounded: Intops.Unsigned.Bounded n)
                   (Heq:
                     match Archi.ptr64 with
                     | true => exists i, Int64.unsigned i = Z.of_N n /\ v = Values.Vlong i
                     | false => exists i, Int.unsigned i = Z.of_N n /\ v = Values.Vint i
                     end),
    inj_value inj (v_ofst n) v
| inj_ptr_live: forall b o prov b' o',
    ListExt.BindIn b b' inj.(inj_hp_map) ->
    (0 <= (Z.of_N o) < Ptrofs.max_signed)%Z ->
    Ptrofs.signed o' = Z.of_N o ->
    inj_value inj (v_ptr (Some (Addr.mkAddr b o, prov))) (Values.Vptr b' o')
| inj_ptr_null: inj_value inj (v_ptr None) (Values.Vnullptr)
.

Definition memval_memsize :=
  Nat.max (Memdata.size_chunk_nat AST.Mptr)
    (Nat.max
       (Memdata.size_chunk_nat AST.Mint32)
       (Memdata.size_chunk_nat AST.Mbool)).

Record wf {St: Store} {Hp: Heap}
  (s: Primitives.State St Hp) (m: Memory.mem) (inj: @injection St): Prop :=
  mk_mem_state_agree
    {
      heap_block_map_sbinds2: ListExt.SBinds2 inj.(inj_hp_map);
      store_block_map_sbinds2: ListExt.SBinds2 inj.(inj_hp_map);
      fun_block_map_sbinds2: ListExt.SBinds2 inj.(inj_hp_map);

      heap_store_distinct: forall b b1 nm b2 o freeable, In (b, b1) inj.(inj_hp_map) -> In (nm, (b2, o, freeable)) inj.(inj_st_map) -> b1 <> b2;
      heap_fun_distinct: forall b b1 f_id b2, In (b, b1) inj.(inj_hp_map) -> In (f_id, b2) inj.(inj_fn_map) -> b1 <> b2;
      store_fun_distinct: forall nm b1 o f_id b2 freeable, In (nm, (b1, o, freeable)) inj.(inj_st_map) -> In (f_id, b2) inj.(inj_fn_map) -> b1 <> b2;

      mem_contents_of_heap:
      forall b o v,
        (Addr.mkAddr b (N.of_nat o)) |-> v $<= s.(Primitives.heap) ->
        exists b' v' mc,
          memval_mem_chunk v mc
          /\ inj_value inj (Value.value_of_memval v) v'
          /\ (forall o',
                 o' < Memdata.size_quantity_nat (Memdata.quantity_chunk mc) ->
                 ZMap.get (Z.of_nat (o + o')) (PMap.get b' (Mem.mem_contents m)) = Memdata.Fragment v' (Memdata.quantity_chunk mc) o /\
                   Mem.perm m b' (Z.of_nat (o + o')) Cur Freeable
             );

      mem_contents_of_store:
      forall nm v,
        BindsTo nm v s.(Primitives.store) ->
        exists b o mc v' freeable,
          In (nm, (b, o, freeable)) inj.(inj_st_map)
          /\ memval_mem_chunk v mc
          /\ inj_value inj (Value.value_of_memval v) v'
          /\ (forall o',
                 o' < Memdata.size_quantity_nat (Memdata.quantity_chunk mc) ->
                 ZMap.get (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (Z.of_nat o)) (Ptrofs.repr (Z.of_nat o')))) (PMap.get b (Mem.mem_contents m)) = Memdata.Fragment v' (Memdata.quantity_chunk mc) o' /\
                   Mem.perm m b (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (Z.of_nat o)) (Ptrofs.repr (Z.of_nat o')))) Cur Freeable
             );
      mem_contents_of_fun: forall id b, In (id, b) inj.(inj_fn_map) -> exists b, In (id, b) inj.(inj_fn_map) /\ ZMap.get 0%Z (PMap.get b (Mem.mem_contents m)) = Memdata.Undef /\ PMap.get b (Mem.mem_access m) 0%Z Memtype.Max = Some Memtype.Nonempty;

      mem_perm_of_store:
      forall nm b o freeable,
        In (nm, (b, o, freeable)) inj.(inj_st_map) ->
        Memory.Mem.range_perm m b (Z.of_nat o) (Z.of_nat (memval_memsize+o)) Memtype.Cur (if freeable then Memtype.Freeable else Memtype.Writable);

    }.
Arguments heap_block_map_sbinds2 [St Hp s m inj].
Arguments store_block_map_sbinds2 [St Hp s m inj].
Arguments fun_block_map_sbinds2 [St Hp s m inj].
Arguments heap_store_distinct [St Hp s m inj].
Arguments heap_fun_distinct [St Hp s m inj].
Arguments store_fun_distinct [St Hp s m inj].
Arguments mem_contents_of_heap [St Hp s m inj] wf [b o v]: rename.
Arguments mem_contents_of_store [St Hp s m inj].
Arguments mem_contents_of_fun [St Hp s m inj].
Arguments mem_perm_of_store [St Hp s m inj].

Definition xtype_of_type (t: type): option AST.xtype :=
  match t with
  | t_unit => None (* AST.Xvoid *)
  | t_bool => Some AST.Xbool
  | t_nat => Some AST.Xint
  | t_ofst => Some AST.Xsize_t
  | t_ptr => Some AST.Xptr
  | t_fun _ _ => Some AST.Xptr
  end.

Definition type_of_xtype (t: AST.xtype): option type :=
  match t with
  | AST.Xbool => Some t_bool
  | AST.Xint => if Archi.ptr64 then None else Some t_nat
  | AST.Xlong => if Archi.ptr64 then Some t_nat else None
  | AST.Xptr => Some t_ptr
  | _ => None
  end.

Definition offset_to_offset (offset: nat) := Z.of_nat (offset * memval_memsize).

Module Facts.

  Lemma val_mem_chunk_fun: forall v mc mc', memval_mem_chunk v mc -> memval_mem_chunk v mc' -> mc' = mc.
  Proof.
    intros v mc mc' Hvmc Hvmc'.
    inversion Hvmc; subst; inversion Hvmc'; now subst.
  Qed.
  Hint Resolve val_mem_chunk_fun: deep_gallinac.
  Hint Rewrite val_mem_chunk_fun: deep_gallinac.

  Lemma val_mem_chunk_dec: forall v mc, { memval_mem_chunk v mc } + { ~memval_mem_chunk v mc }.
  Proof.
    intros.
    destruct v, mc;
      (try (constructor; now constructor));
      right; intros contra; inversion contra.
  Qed.

  Lemma value_compcert_fun [St inj v_gc v_cc v_cc']:
    @inj_value St inj v_gc v_cc -> inj_value inj v_gc v_cc' -> v_cc' = v_cc.
  Proof.
    intros H H'.
    inversion H as [ ?b1 | ?n1 ?i1 ?Hle1 ?Hunsigned1 | | ?b1 ?o1 ?prov1 ?b'1 ?o'1 ?HIn1 ?Hrange1 ?Hsigned1 | ];
      subst;
      inversion H' as [ ?b2 | ?n2 ?i2 ?Hle2 ?Hunsigned2 | | ?b2 ?o2 ?prov2 ?b'2 ?o'2 ?HIn2 ?Hrange2 ?Hsigned2 | ]; subst; try reflexivity.
    - (* Compcert Ints ... *)
      f_equal.
      eapply Integers.Int.same_if_eq.
      unfold Int.eq.
      rewrite Hunsigned1, Hunsigned2.
      unfold Coqlib.zeq.
      destruct (Z.eq_dec); [ reflexivity | contradiction ].
    - (destruct (Archi.ptr64);
       destruct Heq as ( i & Hunsigned1 & Heq ), Heq0 as ( i' & Hunsigned2 & Heq' ); subst;
         f_equal);
        [ eapply Int64.same_if_eq; unfold Int64.eq
        | eapply Int.same_if_eq; unfold Int.eq ];
      rewrite Hunsigned1, Hunsigned2;
      unfold Coqlib.zeq;
      destruct (Z.eq_dec); congruence.
    - assert (b'2 = b'1) by (eapply ListExt.BindIn_fun; eauto); subst.
      assert (Hrewrite: Ptrofs.signed o'1 = Ptrofs.unsigned o'1) by (apply Ptrofs.signed_eq_unsigned; apply Ptrofs.signed_positive; lia);
        rewrite Hrewrite in Hsigned1; clear Hrewrite.
      assert (Hrewrite: Ptrofs.signed o'2 = Ptrofs.unsigned o'2) by (apply Ptrofs.signed_eq_unsigned; apply Ptrofs.signed_positive; lia);
        rewrite Hrewrite in Hsigned2; clear Hrewrite.
      f_equal.
      eapply Ptrofs.same_if_eq.
      unfold Ptrofs.eq.
      rewrite Hsigned1, Hsigned2.
      unfold Coqlib.zeq.
      destruct (Z.eq_dec); [ reflexivity | contradiction ].
  Qed.
  Hint Resolve value_compcert_fun: deep_gallinac.
  Hint Rewrite value_compcert_fun: deep_gallinac.

  Lemma value_compcert_nat_eq [St inj l r l_i r_i valid_pointer]
    (Hv_cc_l: inj_value inj (v_nat l) (Values.Vint l_i))
    (Hv_cc_r: inj_value inj (v_nat r) (Values.Vint r_i)):
    @inj_value St inj
      (v_bool (l =? r)%nat)
      (Values.Val.cmpu valid_pointer Ceq (Values.Vint l_i) (Values.Vint r_i)).
  Proof.
    unfold Values.Val.cmpu, Values.Val.cmpu_bool.
    cbn.
    inversion Hv_cc_l as [ | ?n ?i HBounded_l Heq_l | | | ]; subst;
      inversion Hv_cc_r as [ | ?n ?i HBounded_r Heq_r | | | ]; subst.
    unfold Int.eq, Coqlib.zeq.
    rewrite Heq_l, Heq_r.
    destruct (Nat.eqb_spec l r) as [ | Hneq_nat ]; [ subst r | ];
      destruct (Z.eq_dec (Z.of_nat l) (Z.of_nat _)) as [ Heq | Hneq_z ];
      (try apply Nat2Z.inj in Heq);
      (try contradiction);
      try constructor.
  Qed.
  Hint Resolve value_compcert_nat_eq: deep_gallinac.

  Lemma type_mem_chunk_sized: forall t, Types.sized t -> exists mc, type_mem_chunk t = Some mc.
  Proof.
    intros t Hstorable; destruct Hstorable; eexists; econstructor.
  Qed.
  Hint Resolve type_mem_chunk_sized: deep_gallinac.

  Lemma type_sized_mem_chunk: forall t mc, type_mem_chunk t = Some mc -> Types.sized t.
  Proof.
    intros t mc Hmc.
    destruct t; try discriminate; try constructor.
  Qed.
  Hint Resolve type_sized_mem_chunk: deep_gallinac.

  Lemma store_memsize_bounds: forall t mc, type_mem_chunk t = Some mc -> Memdata.size_chunk_nat mc <= memval_memsize.
  Proof.
    intros t mc Hmemchunk.
    destruct t; inversion Hmemchunk; subst; try discriminate; unfold memval_memsize; cbn; try (lia).
  Qed.
  Hint Resolve store_memsize_bounds: deep_gallinac.


  Lemma store_memsize_bounded: memval_memsize <= 8.
  Proof.
    unfold memval_memsize. unfold AST.Mptr.
    destruct (Archi.ptr64); now repeat constructor.
  Qed.
  Hint Resolve store_memsize_bounded: deep_gallinac.

  Lemma inj_bool_val {St inj b tv}
    (Hinj : @inj_value St inj (v_bool b) tv)
    : Values.Val.bool_of_val tv b.
  Proof.
    inversion Hinj; subst; destruct b; constructor.
  Qed.
  Hint Resolve inj_bool_val: deep_gallinac.

  Lemma val_type_mem_chunk_agree: forall v t mc mc', wt_value (Value.value_of_memval v) t -> CCInj.memval_mem_chunk v mc -> CCInj.type_mem_chunk t = Some mc' -> mc = mc'.
  Proof.
    intros v t mc mc' Hwt Hmcv Hmct.
    destruct v; cbn in Hwt;
      inversion Hwt; subst;
      inversion Hmcv; subst;
      inversion Hmct; subst;
      reflexivity.
  Qed.
  #[global] Hint Resolve val_type_mem_chunk_agree: deep_gallinac.

End Facts.
