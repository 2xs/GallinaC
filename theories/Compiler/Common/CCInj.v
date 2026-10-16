(*
GallinaC: Unifying Verification and Certified Compilation of System Programs in Rocq
Copyright (C) 2023-2026 GallinaC contributors (see CONTRIBUTORS.md)

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with this program. If not, see <https://www.gnu.org/licenses/>.
*)

From Corelib Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

From Stdlib Require Import ZArith Arith List SetoidList Psatz.
Import ListNotations.

From compcert.lib Require Import Maps Integers.
From compcert.common Require Memory Globalenvs.
Import Memory.

From GallinaC.Utils Require NatExt CompCertExt.
From GallinaC.Imp Require Import Heap Store Storable Primitives Intops Uint32 Uintptr.
From GallinaC.Compiler.Common Require Import Types Value.

Local Open Scope separation_scope.
Local Open Scope mem_scope.

(* Injecting GallinaC concepts into their CompCert equivalents *)

Definition heap_block_map := list (nat * (Values.block * (N * bool))).

Definition heap_map_free (b: nat) (l: heap_block_map): heap_block_map :=
  ListExt.bmap_update_a Nat.eqb b (fun szlv => (fst szlv, false)) l.
Definition store_block_map (Ad: Type) := list (Ad * (Values.block * nat * bool)).
Definition fun_block_map := list (AST.ident * Values.block).

Record injection (Ad: Type): Type :=
  {
    inj_hp_map: heap_block_map;
    inj_st_map: store_block_map Ad;
    inj_fn_map: fun_block_map;
  }.
Arguments inj_hp_map [Ad] inj: rename.
Arguments inj_st_map [Ad] inj: rename.
Arguments inj_fn_map [Ad] inj: rename.

Definition inj_hp_le [Ad] (inj inj': injection Ad): Prop :=
  forall b b' sz live,
    ListExt.BindIn b (b', (sz, live)) inj.(inj_hp_map) ->
    exists live', ListExt.BindIn b (b', (sz, live')) inj'.(inj_hp_map).

Lemma inj_hp_le_eq [Ad] [inj inj': injection Ad]
  (EHP: inj'.(inj_hp_map) = inj.(inj_hp_map))
  : inj_hp_le inj inj'.
Proof using Type.
  intros b b' sz live HIN; exists live; rewrite EHP; exact HIN.
Qed.

Lemma inj_hp_le_trans [Ad] [inj1 inj2 inj3: injection Ad]
  (LE12: inj_hp_le inj1 inj2) (LE23: inj_hp_le inj2 inj3)
  : inj_hp_le inj1 inj3.
Proof using Type.
  intros b b' sz live HIN.
  destruct (LE12 b b' sz live HIN) as ( lv2 & HIN2 ).
  exact (LE23 b b' sz lv2 HIN2).
Qed.

Lemma inj_hp_le_free [Ad] [inj: injection Ad] (bg: nat)
  : inj_hp_le inj
      (Build_injection Ad (heap_map_free bg inj.(inj_hp_map))
         inj.(inj_st_map) inj.(inj_fn_map)).
Proof using Type.
  intros b1 b1' sz1 lv1 HIN1; cbn [inj_hp_map].
  destruct (Nat.eq_dec b1 bg) as [ EB | NEB ].
  - subst b1; exists false.
    exact (ListExt.bmap_update_a_BindIn_eq (f := fun szlv => (fst szlv, false))
             Nat.eqb_spec HIN1).
  - exists lv1.
    exact (ListExt.bmap_update_a_BindIn_neq Nat.eqb_spec NEB HIN1).
Qed.

Definition type_mem_chunk (t: type): option AST.memory_chunk :=
  match t with
  | t_unit => None
  | t_bool => Some AST.Mbool
  | t_nat => Some AST.Mint32
  | t_ofst => Some AST.Mptr
  | t_ptr => Some AST.Mptr
  end.

Definition offset_to_offset (offset: Z): Z := (offset * Z.of_nat memword_bytes).

Lemma Ptrofs_eq_of_offsets [o1 o2: Ptrofs.int] [ofstl ofstr: N]
  (USGl: Ptrofs.unsigned o1 = offset_to_offset (Z.of_N ofstl))
  (USGr: Ptrofs.unsigned o2 = offset_to_offset (Z.of_N ofstr))
  : Ptrofs.eq o1 o2 = N.eqb ofstl ofstr.
Proof.
  specialize memword_bytes_pos as MSPOS.
  unfold Ptrofs.eq; rewrite USGl USGr; unfold offset_to_offset.
  destruct (N.eqb_spec ofstl ofstr) as [ -> | NE ].
  - destruct (Coqlib.zeq _ _) as [ _ | NEZ ]; [ reflexivity | exfalso; exact (NEZ eq_refl) ].
  - destruct (Coqlib.zeq _ _) as [ EZ | _ ]; [ exfalso; apply NE; apply N2Z.inj; nia | reflexivity ].
Qed.

Inductive InjValue [Ad] [Pt: Ptr.type Ad] (inj: injection Ad): value Pt -> Values.val -> Prop :=
| inj_bool: forall b,
    InjValue inj (v_bool b) (if b then Values.Vtrue else Values.Vfalse)
| inj_nat: forall (n: nat) i
                  (BOUNDED: Intops.Unsigned.Bounded n)
                  (EQ: Int.unsigned i = Z.of_nat n),
    InjValue inj (v_nat n) (Values.Vint i)
| inj_ofst: forall (n: N) v
                   (BOUNDED: Intops.Unsigned.Bounded n)
                   (EQ:
                     match Archi.ptr64 with
                     | true => exists i, Int64.unsigned i = Z.of_N n /\ v = Values.Vlong i
                     | false => exists i, Int.unsigned i = Z.of_N n /\ v = Values.Vint i
                     end),
    InjValue inj (v_ofst n) v
| inj_ptr: forall p b o sz live b' o',
    ListExt.BindIn b (b', (sz, live)) inj.(inj_hp_map) ->
    Extent p b sz ->
    Intops.Unsigned.Bounded o ->
    Ptrofs.unsigned o' = offset_to_offset (Z.of_N o) ->
    References p (Addr.mkAddr b o) ->
    InjValue inj (v_ptr p) (Values.Vptr b' o')
| inj_null: InjValue inj (v_ptr null) (Values.Vnullptr)
.

Definition inj_value [Ad] [Pt: Ptr.type Ad] (inj: injection Ad) (v: value Pt): option Values.val :=
  match v with
  | v_bool b => if b then Some Values.Vtrue else Some Values.Vfalse
  | v_tt => None
  | v_nat n =>
      if (IntCarrier.to_Z n <=? Unsigned.max_unsigned nat_uint32_t)%Z then
        Some (Values.Vint (Int.repr (IntCarrier.to_Z n)))
      else
        None
  | v_ofst o =>
      if (IntCarrier.to_Z o <=? Unsigned.max_unsigned n_ofst_t)%Z then
        match Archi.ptr64 with
        | true => Some (Values.Vlong (Int64.repr (IntCarrier.to_Z o)))
        | false => Some (Values.Vint (Int.repr (IntCarrier.to_Z o)))
        end
      else
        None
  | v_ptr p =>
      match p =? null with
      | true => Some (Values.Vnullptr)
      | false =>
          match ref_addr p with
          |  Some a =>
               let b := block a in
               let o := offset a in
               match findA (Nat.eqb b) inj.(inj_hp_map) with
               | Some (b', _) =>
                   if (IntCarrier.to_Z o <=? Unsigned.max_unsigned n_ofst_t)%Z then
                     Some (Values.Vptr b' (Ptrofs.repr (offset_to_offset (IntCarrier.to_Z o))))
                   else
                     None
               | None => None
               end
          | None => None
          end
      end
  end.

Section Wf.

  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).

Record wf
  (s: Sm) (m: Memory.mem) (inj: injection Ad): Prop :=
  mk_mem_state_agree
    {
      heap_block_bmap: ListExt.BMap inj.(inj_hp_map);
      store_block_map_sbinds2: ListExt.SBinds2 inj.(inj_st_map);
      fun_block_map_sbinds2: ListExt.SBinds2 inj.(inj_fn_map);

      heap_store_distinct: forall b b1 sz live a b2 o freeable, In (b, (b1, (sz, live))) inj.(inj_hp_map) -> In (a, (b2, o, freeable)) inj.(inj_st_map) -> b1 <> b2;
      heap_fun_distinct: forall b b1 sz live f_id b2, In (b, (b1, (sz, live))) inj.(inj_hp_map) -> In (f_id, b2) inj.(inj_fn_map) -> b1 <> b2;
      store_fun_distinct: forall a b1 o f_id b2 freeable, In (a, (b1, o, freeable)) inj.(inj_st_map) -> In (f_id, b2) inj.(inj_fn_map) -> b1 <> b2;

      mem_contents_of_heap:
      forall b o v,
        (mkAddr b (N.of_nat o)) |-> v $<= (State.heap s) ->
        exists b' sz,
          ListExt.BindIn b (b', (sz, true)) inj.(inj_hp_map)
          /\ (forall mc,
                 type_mem_chunk (type_of_value v) = Some mc ->
                 exists v',
                   InjValue inj v v'
                   /\ Mem.load mc m b' (offset_to_offset (Z.of_nat o)) = Some v'
             );

      mem_contents_of_store:
      forall a v,
        a |-> v $<= (State.store s) ->
        exists b o freeable,
          In (a, (b, o, freeable)) inj.(inj_st_map)
          /\ (forall mc,
                 type_mem_chunk (type_of_value v) = Some mc ->
                 exists v',
                   InjValue inj v v'
                   /\ Mem.load mc m b (offset_to_offset (Z.of_nat o)) = Some v'
             );
      mem_contents_of_fun:
      forall id b,
        In (id, b) inj.(inj_fn_map) ->
        ZMap.get 0%Z (PMap.get b (Mem.mem_contents m)) = Memdata.Undef
        /\ PMap.get b (Mem.mem_access m) 0%Z Memtype.Max = Some Memtype.Nonempty;

      mem_header_of_heap:
      forall b b' sz,
        ListExt.BindIn b (b', (sz, true)) inj.(inj_hp_map) ->
        Mem.load AST.Mptr m b' (- Memdata.size_chunk AST.Mptr)%Z
          = Some (Values.Vptrofs (Ptrofs.repr (offset_to_offset (Z.of_N sz))));

      mem_extent_of_heap:
      forall b b' sz live,
        ListExt.BindIn b (b', (sz, live)) inj.(inj_hp_map) ->
        (offset_to_offset (Z.of_N sz) <= Ptrofs.max_unsigned)%Z
        /\ Memory.Mem.valid_block m b'
        /\ (live = true ->
            Memory.Mem.range_perm m b'
              (- Memdata.size_chunk AST.Mptr)%Z
              (offset_to_offset (Z.of_N sz))
              Memtype.Cur Memtype.Freeable);

      heap_contents_compact:
      forall b o v b' sz live,
        (mkAddr b (N.of_nat o)) |-> v $<= (State.heap s) ->
        ListExt.BindIn b (b', (sz, live)) inj.(inj_hp_map) ->
        (N.of_nat o < sz)%N;

      mem_perm_of_store:
      forall a b o freeable,
        In (a, (b, o, freeable)) inj.(inj_st_map) ->
        Memory.Mem.range_perm m b (offset_to_offset (Z.of_nat o))
          (offset_to_offset (Z.of_nat o) + Z.of_nat memword_bytes) Memtype.Cur (if freeable then Memtype.Freeable else Memtype.Writable);

      heap_block_below_alc:
      forall b b' sz live bid,
        In (b, (b', (sz, live))) inj.(inj_hp_map) ->
        cget (State.alc s) = Some bid ->
        b < bid;

    }.

End Wf.

Arguments heap_block_bmap [Sm s m inj].
Arguments store_block_map_sbinds2 [Sm s m inj].
Arguments fun_block_map_sbinds2 [Sm s m inj].
Arguments heap_store_distinct [Sm s m inj].
Arguments heap_fun_distinct [Sm s m inj].
Arguments store_fun_distinct [Sm s m inj].
Arguments mem_contents_of_heap [Sm s m inj] wf [b o v]: rename.
Arguments mem_contents_of_store [Sm s m inj].
Arguments mem_contents_of_fun [Sm s m inj].
Arguments mem_header_of_heap [Sm s m inj].
Arguments mem_extent_of_heap [Sm s m inj].
Arguments heap_contents_compact [Sm s m inj].
Arguments mem_perm_of_store [Sm s m inj].
Arguments heap_block_below_alc [Sm s m inj].

Section StackBlock.

  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).

  Definition st_map_of_locals (sp: Values.block) (locals: list Nm): store_block_map Ad :=
    List.concat
      (ListExt.mapi
         (fun local ofst =>
            match ref_addr local with
            | Some a => [(a, (sp, ofst, true))]
            | None => []
            end)
         locals).

  Definition stack_block_st_map (inj: injection Ad) (sp: Values.block)
    (locals: list Nm): Prop :=
    forall (a: Ad) o f,
      In (a, (sp, o, f)) inj.(inj_st_map) ->
      exists n nm, List.nth_error locals n = Some nm
                   /\ References nm a
                   /\ o = n.

  Definition stack_block_st_rows (inj: injection Ad) (sp: Values.block)
    (locals: list Nm): Prop :=
    forall n local a, List.nth_error locals n = Some local -> References local a ->
      In (a, (sp, n, true)) inj.(inj_st_map).

  Definition inj_st_nonew (inj inj': injection Ad): Prop :=
    forall b (a: Ad) o f,
      (exists (a': Ad) o' f', In (a', (b, o', f')) inj.(inj_st_map)) ->
      In (a, (b, o, f)) inj'.(inj_st_map) -> In (a, (b, o, f)) inj.(inj_st_map).

  Definition inj_st_keep (st: St) (inj inj': injection Ad): Prop :=
    forall (a: Ad) x, In (a, x) inj.(inj_st_map) ->
      (exists w, a |-> w $<= st) -> In (a, x) inj'.(inj_st_map).

  Lemma st_map_of_locals_inv [sp] [locals: list Nm] [a: Ad] [b o f]
    (IN: In (a, (b, o, f)) (st_map_of_locals sp locals))
    : b = sp /\ f = true
      /\ exists n nm, List.nth_error locals n = Some nm
                      /\ References nm a
                      /\ o = n.
  Proof using Type.
    unfold st_map_of_locals, ListExt.mapi in IN.
    destruct (ListExt.concat_mapi'_inv _ locals 0%nat _ IN) as ( i & x & NTH & INg ).
    cbn [Nat.add] in INg.
    destruct (ref_addr x) as [ ax | ] eqn:REF; [ | contradiction ].
    destruct INg as [ EQ | [] ].
    injection EQ as EA EB EO EF; subst.
    split; [ reflexivity | split; [ reflexivity | ] ].
    eexists _, x; split; [ exact NTH | split; [ exact REF | reflexivity ] ].
  Qed.

  Lemma stack_block_st_map_local [inj: injection Ad] [sp] [locals: list Nm] [a: Ad] [o f]
    (STACKBLMAP: stack_block_st_map inj sp locals)
    (IN: In (a, (sp, o, f)) inj.(inj_st_map))
    : exists n nm, List.nth_error locals n = Some nm
                   /\ References nm a
                   /\ o = n.
  Proof using Type.
    exact (STACKBLMAP a o f IN).
  Qed.

  Lemma write_var_dsj
    [inj: injection Ad] [sp] [locals: list Nm] [n nm] [a: Ad]
    (STACKBLMAP: locals = [] \/ stack_block_st_map inj sp locals)
    (DEREF: List.nth_error locals n = Some nm)
    (REF: References nm a)
    : forall a' b' o' f',
        a' <> a ->
        In (a', (b', o', f')) inj.(inj_st_map) ->
        b' <> sp
        \/ o' <> n.
  Proof using Type.
    destruct STACKBLMAP as [ ENIL | FM ];
      [ rewrite ENIL in DEREF; destruct n; cbn in DEREF; discriminate DEREF | ].
    intros a' b' o' f' NE IN.
    destruct (Values.eq_block b' sp) as [ EB | NEB ]; [ subst b' | now left ].
    right.
    destruct (stack_block_st_map_local FM IN) as ( n' & nm' & DEREF' & REF' & EO ).
    subst o'.
    destruct (Nat.eq_dec n' n) as [ EN | NEN ].
    - exfalso; subst n'.
      assert (ENM: nm' = nm) by congruence; subst nm'.
      apply NE; congruence.
    - exact NEN.
  Qed.

  Lemma st_map_of_locals_In [sp] [locals: list Nm] [i nm] [a: Ad]
    (NTH: List.nth_error locals i = Some nm) (REF: References nm a)
    : In (a, (sp, i, true)) (st_map_of_locals sp locals).
  Proof using Type.
    unfold st_map_of_locals, ListExt.mapi.
    refine (ListExt.concat_mapi'_fwd _ locals 0%nat i nm _ NTH _).
    cbn [Nat.add]; rewrite REF; left; reflexivity.
  Qed.

  Lemma st_map_of_locals'_sbinds2 (sp: Values.block):
    forall (locals: list Nm) (k: nat)
           (DISTINCT: forall i j nm1 nm2 (a1 a2: Ad),
               i <> j ->
               List.nth_error locals i = Some nm1 ->
               List.nth_error locals j = Some nm2 ->
               References nm1 a1 -> References nm2 a2 -> a1 <> a2),
      ListExt.SBinds2
        (List.concat
           (ListExt.mapi'
              (fun (local: Nm) (ofst: nat) =>
                 (match ref_addr local with
                  | Some a => [(a, (sp, ofst, true))]
                  | None => []
                  end: store_block_map Ad))
              locals k)).
  Proof using Type.
    induction locals as [ | nm locals IH ]; intros k DISTINCT; [ constructor | ].
    assert (DIST': forall i j nm1 nm2 (a1 a2: Ad),
               i <> j ->
               List.nth_error locals i = Some nm1 ->
               List.nth_error locals j = Some nm2 ->
               References nm1 a1 -> References nm2 a2 -> a1 <> a2).
    { intros i j nm1 nm2 a1 a2 NE N1 N2 R1 R2.
      exact (DISTINCT (S i) (S j) nm1 nm2 a1 a2 ltac:(lia) N1 N2 R1 R2). }
    specialize (IH (S k) DIST') as SBtail.
    cbn [ListExt.mapi' List.concat].
    destruct (ref_addr nm) as [ a | ] eqn:REF; cbn [List.app]; [ | exact SBtail ].
    refine (ListExt.SBinds2_cons a (sp, k, true) _ _ SBtail).
    refine (ListExt.AbsBind2_of_notin _).
    intros a' y INy.
    destruct (ListExt.concat_mapi'_inv _ locals (S k) (a', y) INy) as ( i & x & NTH & INg ).
    destruct (ref_addr x) as [ ax | ] eqn:REFx; [ | contradiction ].
    destruct INg as [ EQ | [] ].
    injection EQ as EA EY; subst a' y.
    split.
    - exact (DISTINCT 0%nat (S i) nm x a ax ltac:(lia) eq_refl NTH REF REFx).
    - intros EQ; apply (f_equal (fun z: Values.block * nat * bool => snd (fst z))) in EQ.
      cbn [fst snd] in EQ; lia.
  Qed.

  Lemma st_map_of_locals_sbinds2 [base] [st: St] [sp] [locals: list Nm]
    (LAYERED: layered base locals st)
    : ListExt.SBinds2 (st_map_of_locals sp locals).
  Proof using Type.
    unfold st_map_of_locals, ListExt.mapi.
    refine (st_map_of_locals'_sbinds2 sp locals 0%nat _).
    intros i j nm1 nm2 a1 a2 NE N1 N2 R1 R2.
    exact (layered_addr_neq LAYERED N1 R1 N2 R2 NE).
  Qed.

  Definition drop_stack_block_rows (locals: list Nm) (l: store_block_map Ad)
    : store_block_map Ad :=
    List.filter (fun row => negb (ref_addr_inb locals (fst row))) l.

  Lemma drop_stack_block_rows_in [locals: list Nm] [l] [row]
    (IN: In row (drop_stack_block_rows locals l)): In row l.
  Proof using Type.
    exact (proj1 (proj1 (List.filter_In _ row l) IN)).
  Qed.

  Lemma drop_stack_block_rows_notlocal [locals: list Nm] [l] [a: Ad] [x]
    (IN: In (a, x) (drop_stack_block_rows locals l))
    : ref_addr_inb locals a = false.
  Proof using Type.
    destruct (proj1 (List.filter_In _ (a, x) l) IN) as ( _ & E ).
    cbv beta in E; cbn [fst] in E.
    destruct (ref_addr_inb locals a); [ discriminate E | reflexivity ].
  Qed.

  Lemma drop_stack_block_rows_keep [locals: list Nm] [l] [a: Ad] [x]
    (IN: In (a, x) l) (NIN: ref_addr_inb locals a = false)
    : In (a, x) (drop_stack_block_rows locals l).
  Proof using Type.
    apply (proj2 (List.filter_In _ (a, x) l)); split; [ exact IN | ].
    cbv beta; cbn [fst]; rewrite NIN; reflexivity.
  Qed.

End StackBlock.

Definition type_to_xtype (t: type): AST.xtype :=
  match t with
  | t_unit => AST.Xvoid
  | t_bool => AST.Xbool
  | t_nat => AST.Xint
  | t_ofst => AST.Xsize_t
  | t_ptr => AST.Xptr
  end.

Definition xtype_to_type (t: AST.xtype): option type :=
  match t with
  | AST.Xbool => Some t_bool
  | AST.Xint => Some t_nat
  | AST.Xptr => Some t_ptr
  | AST.Xvoid => Some t_unit
  | AST.Xlong => if Archi.ptr64 then Some t_ofst else None
  | AST.Xint8signed | AST.Xint8unsigned
  | AST.Xint16signed | AST.Xint16unsigned
  | AST.Xfloat | AST.Xsingle
  | AST.Xany32 | AST.Xany64
    => None
  end.

Lemma type_to_xtype_to_type (t: type): xtype_to_type (type_to_xtype t) = Some t.
Proof. by case: t. Qed.

Inductive XTypeToType: AST.xtype -> type -> Prop :=
| tox_bool: XTypeToType AST.Xbool t_bool
| tox_int: XTypeToType AST.Xint t_nat
| tox_ptr: XTypeToType AST.Xptr t_ptr
| tox_void: XTypeToType AST.Xvoid t_unit
| tox_long: (Archi.ptr64 = true) -> XTypeToType AST.Xlong t_ofst
.

Module Facts.

Section WfFacts.

  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).

  Lemma heap_block_inj [s: Sm] [m inj] (WF: wf s m inj)
    [b1 b2 b' p1 p2]
    (IN1: In (b1, (b', p1)) inj.(inj_hp_map))
    (IN2: In (b2, (b', p2)) inj.(inj_hp_map))
    : b1 = b2.
  Proof using Type.
    exact (proj1 (ListExt.BMap_b_fun (heap_block_bmap WF) IN1 IN2)).
  Qed.

  Lemma inj_block_eq [s: Sm] [m inj] (WF: wf s m inj)
    [bl br b1 b2 pl pr]
    (INl: ListExt.BindIn bl (b1, pl) inj.(inj_hp_map))
    (INr: ListExt.BindIn br (b2, pr) inj.(inj_hp_map))
    : b1 = b2 <-> bl = br.
  Proof using Type.
    split; intro E; subst.
    - exact (heap_block_inj WF (ListExt.BindIn_In INl) (ListExt.BindIn_In INr)).
    - now injection (ListExt.BindIn_fun _ _ _ _ INl INr).
  Qed.

  Lemma heap_cell_perm [s: Sm] [m inj] (WF: wf s m inj)
    [b o v b' sz live]
    (CELL: (mkAddr b (N.of_nat o)) |-> v $<= (State.heap s))
    (HIN: ListExt.BindIn b (b', (sz, live)) inj.(inj_hp_map))
    : Memory.Mem.range_perm m b'
        (offset_to_offset (Z.of_nat o))
        (offset_to_offset (Z.of_nat o) + Z.of_nat memword_bytes)
        Memtype.Cur Memtype.Freeable.
  Proof using Type.
    destruct (mem_contents_of_heap WF CELL) as ( b'0 & sz0 & HIN0 & _ ).
    assert (EQ: (b'0, (sz0, true)) = (b', (sz, live)))
      by exact (ListExt.BindIn_fun _ _ _ _ HIN HIN0).
    injection EQ as Eb Esz Elive; subst b'0; subst sz0; subst live.
    destruct (mem_extent_of_heap WF b b' sz true HIN) as ( _ & _ & RP ).
    specialize (RP eq_refl).
    specialize (heap_contents_compact WF b o v b' sz true CELL HIN) as LT.
    specialize memword_bytes_pos as MSPOS.
    specialize (Memdata.size_chunk_pos AST.Mptr) as SCPOS.
    assert (LTZ: (Z.of_nat o < Z.of_N sz)%Z) by lia.
    intros ofs RNG; apply RP.
    unfold offset_to_offset in RNG |- *.
    assert (MSZ: (0 < Z.of_nat memword_bytes)%Z) by lia.
    nia.
  Qed.

  Lemma wf_heap_block_valid [inj: injection Ad] [s: Sm] [m]
    (WFINJ: wf s m inj) [b b' sz live]
    (IN: In (b, (b', (sz, live))) inj.(inj_hp_map))
    : Memory.Mem.valid_block m b'.
  Proof using Type.
    destruct (mem_extent_of_heap WFINJ b b' sz live
                (ListExt.BMap_In_BindIn (heap_block_bmap WFINJ) IN))
      as ( _ & VB & _ ).
    exact VB.
  Qed.

  Lemma wf_store_block_valid [inj: injection Ad] [s: Sm] [m]
    (WFINJ: wf s m inj)
    [a: Ad] [b o f] (IN: In (a, (b, o, f)) inj.(inj_st_map))
    : Memory.Mem.valid_block m b.
  Proof using Type.
    specialize memword_bytes_pos as MSPOS.
    refine (Memory.Mem.perm_valid_block m b (offset_to_offset (Z.of_nat o)) Memtype.Cur _ _).
    refine (mem_perm_of_store WFINJ a b o f IN (offset_to_offset (Z.of_nat o)) _).
    lia.
  Qed.

  Lemma wf_fun_block_valid [inj: injection Ad] [s: Sm] [m]
    (WFINJ: wf s m inj)
    [id b] (IN: In (id, b) inj.(inj_fn_map))
    : Memory.Mem.valid_block m b.
  Proof using Type.
    destruct (mem_contents_of_fun WFINJ id b IN) as ( _ & ACC ).
    refine (Memory.Mem.perm_valid_block m b 0%Z Memtype.Max Memtype.Nonempty _).
    unfold Memory.Mem.perm; rewrite ACC; constructor.
  Qed.

End WfFacts.

  Lemma InjValue_fun [Ad] [Pt: Ptr.type Ad] [inj: injection Ad] [v_gc: value Pt] [v_cc v_cc']
    (INJ: InjValue inj v_gc v_cc) (INJ': InjValue inj v_gc v_cc')
    : v_cc' = v_cc.
  Proof.
    inversion INJ as [ ?b1 | ?n1 ?i1 ?LE1 ?UNSIGNED1 | | ?p1 ?b1 ?o1 ?sz1 ?lv1 ?b'1 ?o'1 ?IN1 ?EXT1 ?RANGE1 ?SIGNED1 ?REF1 | ];
      subst;
      inversion INJ' as [ ?b2 | ?n2 ?i2 ?LE2 ?UNSIGNED2 | | ?p2 ?b2 ?o2 ?sz2 ?lv2 ?b'2 ?o'2 ?IN2 ?EXT2 ?RANGE2 ?SIGNED2 ?REF2 | ]; subst; try done.
    - (* Compcert Ints ... *)
      congr Values.Vint; apply: Integers.Int.same_if_eq.
      rewrite /Int.eq UNSIGNED1 UNSIGNED2 /Coqlib.zeq.
      by case: Z.eq_dec.
    - (destruct (Archi.ptr64);
       destruct EQ as ( i & UNSIGNED1 & EQi ), EQ0 as ( i' & UNSIGNED2 & EQi' ); subst;
         f_equal);
        [ apply: Int64.same_if_eq; rewrite /Int64.eq
        | apply: Int.same_if_eq; rewrite /Int.eq ];
      rewrite UNSIGNED1 UNSIGNED2 /Coqlib.zeq;
      by case: Z.eq_dec.
    - have Eaddr: mkAddr (s:=Ad) b1 o1 = mkAddr b2 o2
        by rewrite REF1 in REF2; congruence.
      case: (mkAddr_inj _ _ _ _ Eaddr) => Eb Eo; subst b2 o2.
      have Epair: (b'2, (sz2, lv2)) = (b'1, (sz1, lv1))
        by apply: ListExt.BindIn_fun; eauto.
      case: Epair => Eb' Esz Elv; subst b'2 sz2 lv2.
      congr Values.Vptr; apply: Ptrofs.same_if_eq.
      rewrite /Ptrofs.eq SIGNED1 SIGNED2 /Coqlib.zeq.
      by case: Z.eq_dec.
    - by rewrite (proj2 (null_addr (null: Pt)) erefl) in REF1.
    - by rewrite (proj2 (null_addr (null: Pt)) erefl) in REF2.
  Qed.
  #[global] Hint Resolve InjValue_fun: deep_gallinac.
  #[global] Hint Rewrite InjValue_fun: deep_gallinac.

  Lemma InjValue_hp_le [Ad] [Pt: Ptr.type Ad] [inj inj': injection Ad]
    (LEHP: inj_hp_le inj inj')
    [v: value Pt] [tv]
    (INJ: InjValue inj v tv)
    : InjValue inj' v tv.
  Proof using Type.
    destruct INJ as [ b | n i BND EQ | n w BND EQ
                    | pp bg og szg lvg b' o' HIN EXTp BNDp USGp REFp | ].
    - exact (inj_bool inj' b).
    - exact (inj_nat inj' n i BND EQ).
    - exact (inj_ofst inj' n w BND EQ).
    - destruct (LEHP bg b' szg lvg HIN) as ( lv' & HIN' ).
      exact (inj_ptr inj' pp bg og szg lv' b' o' HIN' EXTp BNDp USGp REFp).
    - exact (inj_null inj').
  Qed.

  Lemma InjValue_nat_eq [Ad] [Pt: Ptr.type Ad] [inj: injection Ad] [l r l_i r_i valid_pointer]
    (INJl: InjValue inj (v_nat (Pt:=Pt) l) (Values.Vint l_i))
    (INJr: InjValue inj (v_nat (Pt:=Pt) r) (Values.Vint r_i)):
    InjValue inj
      (v_bool (Pt:=Pt) (Unsigned.eqb l r))
      (Values.Val.cmpu valid_pointer Ceq (Values.Vint l_i) (Values.Vint r_i)).
  Proof.
    rewrite /Values.Val.cmpu /Values.Val.cmpu_bool /=.
    inversion INJl as [ | ?n ?i BOUNDEDl EQl | | | ]; subst;
      inversion INJr as [ | ?n ?i BOUNDEDr EQr | | | ]; subst.
    rewrite /Int.eq /Coqlib.zeq EQl EQr.
    rewrite (Unsigned.Facts.eqb_bounded _ _ BOUNDEDl BOUNDEDr).
    case: (@IntCarrier.eqb_spec (Unsigned.carrier nat_uint32_t) l r) => [ Eq_nat | NEnat ]; [ subst r | ];
      case: (Z.eq_dec (Z.of_nat l) (Z.of_nat _)) => [ EQ | NEz ];
      (try apply Nat2Z.inj in EQ);
      (try contradiction);
      try constructor.
  Qed.
  #[global] Hint Resolve InjValue_nat_eq: deep_gallinac.

  Lemma InjValue_nat_div [Ad: Addr.type] [Pt: Ptr.type Ad] [inj: injection Ad]
    [S: Type] [s: S] [l r q: nat] [l_i r_i: Int.int]
    (INJl: InjValue inj (v_nat (Pt:=Pt) l) (Values.Vint l_i))
    (INJr: InjValue inj (v_nat (Pt:=Pt) r) (Values.Vint r_i))
    (DIV: Unsigned.div l r s = Some (Monad.Success (q, s)))
    : Values.Val.divu (Values.Vint l_i) (Values.Vint r_i)
      = Some (Values.Vint (Int.divu l_i r_i))
      /\ InjValue inj (v_nat (Pt:=Pt) q) (Values.Vint (Int.divu l_i r_i)).
  Proof using Type.
    inversion INJl as [ | ?n ?i BOUNDEDl EQl | | | ]; subst.
    inversion INJr as [ | ?n ?i BOUNDEDr EQr | | | ]; subst.
    specialize (nat_bounded_range BOUNDEDl) as RANGEl.
    specialize (nat_bounded_range BOUNDEDr) as RANGEr.
    destruct (nat_div_inv BOUNDEDl DIV) as ( RPOS & EQq ).
    assert (DIVB: (0 <= Z.of_nat l / Z.of_nat r <= Z.of_nat l)%Z)
      by (split; [ apply Z.div_pos | apply Z.div_le_upper_bound ]; nia).
    assert (NEQ: Int.eq r_i Int.zero = false).
    { unfold Int.eq; rewrite EQr; rewrite Int.unsigned_zero.
      destruct (Coqlib.zeq (Z.of_nat r) 0); [ lia | reflexivity ]. }
    assert (QB: (0 <= Z.of_nat q <= Int.max_unsigned)%Z).
    { split; [ lia | ].
      apply (Z.le_trans _ (Z.of_nat l)); [ rewrite EQq; apply DIVB | apply RANGEl ]. }
    split; [ cbn; now rewrite NEQ | ].
    constructor.
    - unfold Unsigned.Bounded, Unsigned.min_unsigned.
      rewrite (Unsigned.CompCert.BW32.max_unsigned_eq (UInt := nat_uint32_t) eq_refl).
      exact QB.
    - unfold Int.divu.
      rewrite EQl; rewrite EQr; rewrite <- EQq; rewrite (Int.unsigned_repr _ QB).
      reflexivity.
  Qed.

  Lemma InjValue_nat_mdl [Ad: Addr.type] [Pt: Ptr.type Ad] [inj: injection Ad]
    [S: Type] [s: S] [l r q: nat] [l_i r_i: Int.int]
    (INJl: InjValue inj (v_nat (Pt:=Pt) l) (Values.Vint l_i))
    (INJr: InjValue inj (v_nat (Pt:=Pt) r) (Values.Vint r_i))
    (MDL: Unsigned.mdl l r s = Some (Monad.Success (q, s)))
    : Values.Val.modu (Values.Vint l_i) (Values.Vint r_i)
      = Some (Values.Vint (Int.modu l_i r_i))
      /\ InjValue inj (v_nat (Pt:=Pt) q) (Values.Vint (Int.modu l_i r_i)).
  Proof using Type.
    inversion INJl as [ | ?n ?i BOUNDEDl EQl | | | ]; subst.
    inversion INJr as [ | ?n ?i BOUNDEDr EQr | | | ]; subst.
    specialize (nat_bounded_range BOUNDEDl) as RANGEl.
    specialize (nat_bounded_range BOUNDEDr) as RANGEr.
    destruct (nat_mdl_inv BOUNDEDr MDL) as ( RPOS & EQq ).
    assert (MODB: (0 <= Z.of_nat l mod Z.of_nat r < Z.of_nat r)%Z)
      by (apply Z.mod_pos_bound; lia).
    assert (NEQ: Int.eq r_i Int.zero = false).
    { unfold Int.eq; rewrite EQr; rewrite Int.unsigned_zero.
      destruct (Coqlib.zeq (Z.of_nat r) 0); [ lia | reflexivity ]. }
    assert (QB: (0 <= Z.of_nat q <= Int.max_unsigned)%Z).
    { split; [ lia | ].
      apply (Z.le_trans _ (Z.of_nat r)); [ rewrite EQq; lia | apply RANGEr ]. }
    split; [ cbn; now rewrite NEQ | ].
    constructor.
    - unfold Unsigned.Bounded, Unsigned.min_unsigned.
      rewrite (Unsigned.CompCert.BW32.max_unsigned_eq (UInt := nat_uint32_t) eq_refl).
      exact QB.
    - unfold Int.modu.
      rewrite EQl; rewrite EQr; rewrite <- EQq; rewrite (Int.unsigned_repr _ QB).
      reflexivity.
  Qed.

  Lemma inj_value_complete [Ad] [Pt: Ptr.type Ad] [inj: injection Ad] [v: value Pt] [v']
    (INJ: InjValue inj v v'):
    inj_value inj v = Some v'.
  Proof.
    case: INJ => [ [] | n i BND EQi | n vc BND EQi | p b o sz lv b' o' IN EXT BND SGN REF | ]; auto; cbn.
    - case: BND => LE0 LEm.
      case: (Z.leb_spec (IntCarrier.to_Z n) (Unsigned.max_unsigned nat_uint32_t)) => [ _ | ];
        last by change (Unsigned.carrier nat_uint32_t) with NatCarrier.nat_int_carrier in *; lia.
      repeat f_equal; apply: Int.eqm_repr_eq.
      rewrite /Int.eqm /Zbits.eqmod.
      by exists 0%Z; rewrite Z.mul_0_l Z.add_0_l; symmetry.
    - case: BND => LE0 LEm.
      case: (Z.leb_spec (IntCarrier.to_Z n) (Unsigned.max_unsigned n_ofst_t)) => [ _ | ];
        last by change (Unsigned.carrier n_ofst_t) with NCarrier.n_int_carrier in *; lia.
      case: Archi.ptr64 EQi => [] [ i [ UNSIGNED EQ ] ]; subst; repeat f_equal;
        [ apply: Int64.eqm_repr_eq; rewrite /Int64.eq | apply: Int.eqm_repr_eq; rewrite /Int.eq ];
        rewrite /Zbits.eqmod;
        by exists 0%Z; rewrite Z.mul_0_l Z.add_0_l; symmetry.
    - case: BND => LE0 LEm.
      case: (eqb_spec p null) => [ Enull | _ ];
        first by rewrite Enull (proj2 (null_addr (null: Pt)) erefl) in REF.
      rewrite REF /= mkAddr_block mkAddr_offset.
      rewrite (ListExt.BindIn_findA_reflect_eq Nat.eqb_spec IN).
      change (Unsigned.carrier n_ofst_t) with NCarrier.n_int_carrier in *.
      case: (Z.leb_spec (IntCarrier.to_Z o) (Unsigned.max_unsigned n_ofst_t)) => [ _ | ]; last by lia.
      repeat f_equal; apply: Ptrofs.eqm_repr_eq.
      rewrite /Ptrofs.eqm /Zbits.eqmod.
      by exists 0%Z; rewrite Z.mul_0_l Z.add_0_l; symmetry.
    - by case: (eqb_spec (null: Pt) null).
  Qed.
  #[global] Hint Resolve inj_value_complete: deep_gallinac.
  #[global] Hint Rewrite inj_value_complete: deep_gallinac.

  Lemma type_mem_chunk_sized [t]
    (SIZED: Types.Sized t)
    : exists mc, type_mem_chunk t = Some mc.
  Proof.
    by case: SIZED; eexists; econstructor.
  Qed.
  #[global] Hint Resolve type_mem_chunk_sized: deep_gallinac.

  Lemma type_sized_mem_chunk [t mc]
    (MC: type_mem_chunk t = Some mc)
    : Types.Sized t.
  Proof.
    destruct t; try discriminate; try constructor.
  Qed.
  #[global] Hint Resolve type_sized_mem_chunk: deep_gallinac.

  Lemma store_memsize_bounds [t mc]
    (MC: type_mem_chunk t = Some mc)
    : Memdata.size_chunk_nat mc <= memword_bytes.
  Proof.
    destruct t; inversion MC; subst; try discriminate;
      rewrite /memword_bytes; cbv [AST.Mptr Archi.ptr64]; cbn; lia.
  Qed.
  #[global] Hint Resolve store_memsize_bounds: deep_gallinac.

  Lemma store_memsize_bounded: memword_bytes <= 8.
  Proof.
    rewrite /memword_bytes.
    by case: Archi.ptr64; repeat constructor.
  Qed.
  #[global] Hint Resolve store_memsize_bounded: deep_gallinac.

  Lemma memword_bytes_size_chunk [t mc] (MC: type_mem_chunk t = Some mc)
    : (Memdata.size_chunk mc <= Z.of_nat memword_bytes)%Z.
  Proof using Type.
    specialize (store_memsize_bounds MC) as LE.
    rewrite Memdata.size_chunk_conv; apply Nat2Z.inj_le; exact LE.
  Qed.

  Lemma memword_bytes_align [t mc] (MC: type_mem_chunk t = Some mc)
    : (Memdata.align_chunk mc | Z.of_nat memword_bytes)%Z.
  Proof using Type.
    destruct t; cbn in MC; inversion MC; subst;
      unfold memword_bytes, AST.Mptr, Memdata.size_chunk_nat;
      destruct Archi.ptr64; cbn;
      first [ apply Z.divide_1_l | apply Z.divide_refl | (exists 2%Z; reflexivity) ].
  Qed.

  Lemma offset_to_offset_mono [x y: Z] (LE: (x <= y)%Z)
    : (offset_to_offset x <= offset_to_offset y)%Z.
  Proof using Type.
    specialize memword_bytes_pos as MSPOS.
    unfold offset_to_offset; nia.
  Qed.

  Lemma offset_to_offset_dsj [i j: nat] (NE: i <> j)
    : (offset_to_offset (Z.of_nat i) + Z.of_nat memword_bytes
         <= offset_to_offset (Z.of_nat j))%Z
      \/ (offset_to_offset (Z.of_nat j) + Z.of_nat memword_bytes
           <= offset_to_offset (Z.of_nat i))%Z.
  Proof using Type.
    specialize memword_bytes_pos as MSPOS.
    unfold offset_to_offset.
    destruct (Nat.lt_total i j) as [ LT | [ EQ | GT ] ];
      [ left; nia | contradiction | right; nia ].
  Qed.

  Lemma offset_to_offset_slot [ofs: Z] (NN: (0 <= ofs)%Z)
    : exists n: nat,
        (offset_to_offset (Z.of_nat n) <= ofs
         < offset_to_offset (Z.of_nat n) + Z.of_nat memword_bytes)%Z.
  Proof using Type.
    specialize memword_bytes_pos as MSPOS.
    assert (MSZ: (0 < Z.of_nat memword_bytes)%Z) by lia.
    exists (Z.to_nat (ofs / Z.of_nat memword_bytes)).
    rewrite Z2Nat.id; [ apply Z.div_pos; lia | ].
    specialize (Z.div_mod ofs (Z.of_nat memword_bytes) ltac:(lia)) as DM.
    specialize (Z.mod_pos_bound ofs (Z.of_nat memword_bytes) MSZ) as MB.
    unfold offset_to_offset; lia.
  Qed.

  Lemma offset_to_offset_align [t mc] (MC: type_mem_chunk t = Some mc) (x: Z)
    : (Memdata.align_chunk mc | offset_to_offset x)%Z.
  Proof using Type.
    unfold offset_to_offset.
    exact (Z.divide_mul_r _ _ _ (memword_bytes_align MC)).
  Qed.

  Lemma alloc_count_extent [sz: N] (BND: (sz <= alloc_max_size)%N):
    (offset_to_offset (Z.of_N sz) <= Ptrofs.max_unsigned)%Z.
  Proof using Type.
    assert (MB: (0 < Z.of_nat memword_bytes)%Z)
      by (unfold memword_bytes; destruct Archi.ptr64; cbn; lia).
    assert (EMAX: Unsigned.max_unsigned n_ofst_t = Ptrofs.max_unsigned)
      by exact (Unsigned.CompCert.Ptrofs.max_unsigned_eq (UInt := n_ofst_t) eq_refl).
    assert (MAXP: (0 <= Ptrofs.max_unsigned)%Z)
      by (unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize,
            Wordsize_Ptrofs.wordsize; destruct Archi.ptr64; cbn; lia).
    assert (BZ: (Z.of_N sz <= Ptrofs.max_unsigned / Z.of_nat memword_bytes)%Z).
    { apply N2Z.inj_le in BND.
      unfold alloc_max_size in BND.
      rewrite Z2N.id in BND; [ apply Z.div_pos; lia | ].
      rewrite EMAX in BND; exact BND. }
    specialize (Z.mul_div_le Ptrofs.max_unsigned (Z.of_nat memword_bytes) MB) as MDL.
    unfold offset_to_offset.
    specialize (N2Z.is_nonneg sz) as SZP.
    nia.
  Qed.

  Lemma ofst_delta_64 (ARCHI: Archi.ptr64 = true) [nn: N] [i: Int64.int]
    (EQi: Int64.unsigned i = Z.of_N nn)
    (BND: (0 <= offset_to_offset (Z.of_N nn) <= Ptrofs.max_unsigned)%Z)
    : Ptrofs.unsigned
        (Ptrofs.of_int64
           (Int64.mul i (Int64.repr (Z.of_N (N.of_nat memword_bytes)))))
      = offset_to_offset (Z.of_N nn).
  Proof using Type.
    specialize store_memsize_bounded as MSLE.
    specialize memword_bytes_pos as MSPOS.
    assert (MB: (0 <= Z.of_N (N.of_nat memword_bytes) <= Int64.max_unsigned)%Z)
      by (rewrite nat_N_Z; split;
          [ lia | apply (Z.le_trans _ 8); [ lia | vm_compute; discriminate ] ]).
    unfold Ptrofs.of_int64, Int64.mul.
    rewrite EQi.
    rewrite (Int64.unsigned_repr _ MB).
    rewrite nat_N_Z.
    unfold offset_to_offset in BND |- *.
    rewrite (Int64.unsigned_repr _ (CompCertExt.Ints.Ptrofs.bound_int64 ARCHI BND)).
    apply Ptrofs.unsigned_repr; lia.
  Qed.

  Lemma ofst_delta_32 (ARCHI: Archi.ptr64 = false) [nn: N] [i: Int.int]
    (EQi: Int.unsigned i = Z.of_N nn)
    (BND: (0 <= offset_to_offset (Z.of_N nn) <= Ptrofs.max_unsigned)%Z)
    : Ptrofs.unsigned
        (Ptrofs.of_int
           (Int.mul i (Int.repr (Z.of_N (N.of_nat memword_bytes)))))
      = offset_to_offset (Z.of_N nn).
  Proof using Type.
    specialize store_memsize_bounded as MSLE.
    specialize memword_bytes_pos as MSPOS.
    assert (MB: (0 <= Z.of_N (N.of_nat memword_bytes) <= Int.max_unsigned)%Z)
      by (rewrite nat_N_Z; split;
          [ lia | apply (Z.le_trans _ 8); [ lia | vm_compute; discriminate ] ]).
    unfold Ptrofs.of_int, Int.mul.
    rewrite EQi.
    rewrite (Int.unsigned_repr _ MB).
    rewrite nat_N_Z.
    unfold offset_to_offset in BND |- *.
    rewrite (Int.unsigned_repr _ (CompCertExt.Ints.Ptrofs.bound_int32 ARCHI BND)).
    apply Ptrofs.unsigned_repr; lia.
  Qed.

  Lemma InjValue_load_result [Ad] [Pt: Ptr.type Ad] [inj: injection Ad]
    [v: value Pt] [tv mc]
    (INJ: InjValue inj v tv)
    (MC: type_mem_chunk (type_of_value v) = Some mc)
    : Values.Val.load_result mc tv = tv.
  Proof.
    inversion INJ as [ b | n i BND EQ | n w BND EQ
                     | p bb o sz lv b' o' HIN EXTp BNDp USGp REFp | ];
      subst; cbn in MC; inversion MC; subst; clear MC.
    - destruct b; vm_compute; reflexivity.
    - reflexivity.
    - unfold AST.Mptr; destruct Archi.ptr64 eqn:ARCHI;
        destruct EQ as ( i & EQi & Ev ); subst; reflexivity.
    - unfold AST.Mptr; destruct Archi.ptr64 eqn:ARCHI; cbn; rewrite ARCHI; reflexivity.
    - unfold AST.Mptr, Values.Vnullptr;
        destruct Archi.ptr64 eqn:ARCHI; cbn; reflexivity.
  Qed.
  #[global] Hint Resolve InjValue_load_result: deep_gallinac.

  Lemma InjValue_bool_val [Ad] [Pt: Ptr.type Ad] [inj: injection Ad] [b tv]
    (INJ : InjValue inj (v_bool (Pt:=Pt) b) tv)
    : Values.Val.bool_of_val tv b.
  Proof.
    by inversion INJ; subst; destruct b; constructor.
  Qed.
  #[global] Hint Resolve InjValue_bool_val: deep_gallinac.

  Lemma val_type_mem_chunk_agree [Ad] [Pt: Ptr.type Ad] [v: value Pt] [t mc mc']
    (WT: wt_value v t)
    (MVMC: type_mem_chunk (type_of_value v) = Some mc)
    (TMC: type_mem_chunk t = Some mc')
    : mc = mc'.
  Proof.
    rewrite (Value.Facts.type_of_value_complete WT) in MVMC.
    congruence.
  Qed.
  #[global] Hint Resolve val_type_mem_chunk_agree: deep_gallinac.
  #[global] Hint Rewrite val_type_mem_chunk_agree: deep_gallinac.

  Lemma value_compcert_sized [Ad] [Pt: Ptr.type Ad] [inj: injection Ad]
    [v: value Pt] [tv] (INJ: InjValue inj v tv)
    : Value.Sized v.
  Proof.
    apply inj_value_complete in INJ.
    destruct v; try constructor; discriminate.
  Qed.
  #[global] Hint Resolve value_compcert_sized: deep_gallinac.

  Lemma inj_has_argtype [Ad] [Pt: Ptr.type Ad] [inj: injection Ad]
    [v: value Pt] [tv t tt]
    (WT: wt_value v t)
    (INJ: InjValue inj v tv)
    (XT: type_to_xtype t = tt)
    : Values.Val.has_argtype tv tt.
  Proof.
    induction WT;
      inversion INJ; subst;
      (try (now constructor)).
    - destruct b; now constructor.
    - destruct (Archi.ptr64) eqn:Earchi;
        destruct EQ as (i & UNSIGNED & EQi);
        subst;
        unfold Values.Val.has_argtype;
        unfold type_to_xtype;
        unfold AST.Xsize_t;
        now rewrite Earchi.
  Qed.
  #[global] Hint Resolve inj_has_argtype: deep_gallinac.

End Facts.
