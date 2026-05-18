From Stdlib Require Import ZArith Arith List SetoidList.
Import ListNotations.

From compcert.common Require AST Events Memory Globalenvs Smallstep.
From compcert.lib Require Import Integers Maps.
Import Memory(mem, Mem.empty, Mem.alloc, Mem.load, Mem.store, Mem.free, Mem.drop_perm) Globalenvs(Genv.globalenv, Genv.find_symbol, Genv.find_funct_ptr, Genv.perm_globvar).

From GallinaC.Utils Require Import ListExt.

From GallinaC.Imp Require Heap Store Primitives Intops.
From GallinaC.Imp Require Import Uint32 Uintptr Memval Heap(Heap) Store(Store, name).

From GallinaC.Compiler.Common Require Import Value CCInj Types.
From GallinaC.Compiler.IR Require Import Cmd Prog Typing.

Import Primitives(store,heap).
Import Imp.Heap.Facts.

Section Semantics.
  Context {St: Store}.
  Context {Hp: Heap}.

  Definition env := PTree.t Value.value.

  Definition value_of_init_data (id: AST.init_data): option memval :=
    match id with
    | AST.Init_int8 int => Some (VInt (Z.to_nat (Int.unsigned int)))
    | AST.Init_int16 int => Some (VInt (Z.to_nat (Int.unsigned int)))
    | AST.Init_int32 int => Some (VInt (Z.to_nat (Int.unsigned int)))
    | AST.Init_int64 int => Some (VInt (Z.to_nat (Int64.unsigned int)))
    | AST.Init_float32 _ => None
    | AST.Init_float64 _ => None
    | AST.Init_space _ => None
    | AST.Init_addrof _ _ => None
    end.

  Definition store_init_data (m: mem) (b: Values.block) (id: AST.init_data): option mem :=
    match id with
    | AST.Init_int8 n => Mem.store AST.Mint8unsigned m b 0 (Values.Vint n)
    | AST.Init_int16 n => Mem.store AST.Mint16unsigned m b 0 (Values.Vint n)
    | AST.Init_int32 n => Mem.store AST.Mint32 m b 0 (Values.Vint n)
    | AST.Init_int64 n => Mem.store AST.Mint64 m b 0 (Values.Vlong n)
    | AST.Init_float32 n => Mem.store AST.Mfloat32 m b 0 (Values.Vsingle n)
    | AST.Init_float64 n => Mem.store AST.Mfloat64 m b 0 (Values.Vfloat n)
    | AST.Init_addrof symb ofs => None
    | AST.Init_space n => None
    end.

  Definition alloc_global (s: Primitives.State St Hp) (m: mem) (inj: injection) (id: AST.ident) (g: globdef): option (Primitives.State St Hp * mem * injection) :=
    match g with
    | AST.Gfun f =>
        let (m1, b) := Mem.alloc m 0 1 in
        match Mem.drop_perm m1 b 0 1 Memtype.Nonempty with
        | Some m2 => Some (s, m2, {| inj_hp_map := inj.(inj_hp_map); inj_st_map := inj.(inj_st_map); inj_fn_map := (id,b)::inj.(inj_fn_map) |} )
        | None => None
        end
    | AST.Gvar
        ({|
            AST.gvar_info := mkvardef var_type;
            AST.gvar_init := [ init ] as init_list;
            AST.gvar_readonly := false;
            AST.gvar_volatile := false;
          |} as v) =>
        let sz := (AST.init_data_list_size) init_list in
        match
          let (m1, b) := Mem.alloc m 0 sz in
          match Globalenvs.store_zeros m1 b 0 sz with
          | None => None
          | Some m2 =>
              match store_init_data m2 b init with
              | None => None
              | Some m3 =>
                  match Mem.drop_perm m3 b 0 sz (Genv.perm_globvar v) with
                  | Some m4 => Some (m4,b)
                  | None => None
                  end
              end
          end
        with
        | Some (m, b) =>
            match value_of_init_data init with
            | Some init =>
                let '(st, nm) := Store.push s.(store) init in
                Some
                  (
                    Primitives.mkState st s.(Primitives.heap) ,
                    m,
                    {|
                      inj_hp_map := inj.(inj_hp_map);
                      inj_st_map := (nm,(b, 0, false))::inj.(inj_st_map);
                      inj_fn_map := inj.(inj_fn_map);
                    |})
            | None => None
            end
        | None => None
        end
    (* Unitialized global variables are unsupported *)
    | AST.Gvar {| AST.gvar_init := [] ; |} => None
    (* No support for "arrays" yet *)
    | AST.Gvar {| AST.gvar_init := _::_::_ ; |} => None
    (* Read-only mutable variable ? *)
    | AST.Gvar {| AST.gvar_readonly := true; |} => None
    (* No point in volatile, if we are mono-thread *)
    | AST.Gvar {| AST.gvar_volatile := true; |} => None
    end.

  Fixpoint alloc_globals (st: Primitives.State St Hp) (m: mem) (inj: injection) (gl: list (AST.ident * globdef)): option (Primitives.State St Hp * mem * injection) :=
    match gl with
    | [] => Some (st, m, inj )
    | (id, g)::gl =>
        match alloc_global st m inj id g with
        | Some (st, m, inj) => alloc_globals st m inj gl
        | None => None
        end
    end.

  Lemma store_init_data_correct {F V}: forall ge m b id m', store_init_data m b id = Some m' -> @Globalenvs.Genv.store_init_data F V ge m b 0 id = Some m'.
  Proof using St Hp.
    intros ge m b id m' Heq.
    destruct id; cbn; cbn in Heq; try discriminate;
      auto.
  Qed.

  Lemma alloc_globals_correct: forall ge st m inj gl st' m' inj' m'', alloc_globals st m inj gl = Some (st', m', inj') -> Globalenvs.Genv.alloc_globals ge m gl = Some m'' -> m'' = m'.
  Proof using St Hp.
    intros ge st m inj gl; revert st m inj.
    induction gl as [ | [ id g ] gl ].
    - cbn; congruence.
    - cbn; unfold alloc_global; cbn.
      intros st m inj st' m' inj' m'' Halloc Halloc'.
      destruct g.
      + destruct (Mem.alloc m 0 1) eqn:Ealloc.
        destruct (Mem.drop_perm m0 b 0 1 Memtype.Nonempty) eqn:Edropperm; [ | discriminate ].
        eapply IHgl; eauto.
      + destruct v; try discriminate.
        destruct gvar_info.
        destruct gvar_init as [ | init_data [ | ] ]; try discriminate.
        destruct gvar_readonly; [discriminate | ].
        destruct gvar_volatile; [discriminate | ].
        cbn in Halloc, Halloc';
          rewrite Z.add_0_r in Halloc, Halloc'.
        destruct (Mem.alloc m 0 (AST.init_data_size init_data)).
        destruct (Globalenvs.store_zeros m0 b 0 (AST.init_data_size init_data)) eqn:Estore_zeros; try discriminate.
        destruct (store_init_data m1 b init_data) eqn:Estore_init_data; [ | discriminate].
        rewrite (store_init_data_correct _ _ _ _ _ Estore_init_data) in Halloc'.
        destruct (Mem.drop_perm m2 b 0 _ _) eqn:Edrop_perm; [ | discriminate].
        destruct (value_of_init_data init_data); [ | discriminate ].
        destruct (Store.push (store st) m4) as [st'' nm].
        eapply IHgl; eauto.
  Qed.

  Definition init_state (p: program) :=
    alloc_globals Primitives.emp Mem.empty {| inj_hp_map := []; inj_st_map := []; inj_fn_map := [] |} p.(prog_defs).

  Inductive cont: Type :=
  (* 1. To return from the program execution
   * /!\ Remember that even C evaluation is simply CPS to return to a caller *)
  | Kstop:
    cont

  (* (* 2. To sequence execution *) *)
  (* (* (* /!\ Recall that binds are only for "storable" values in IR *) *) *)
  (* | Kseq: *)
  (*   forall (returns: bool) *)
  (*          (c: @cmd St returns) *)
  (*          (k: cont) *)
  (*   , cont *)

  (* 3. To bind the result in a temporary variable *)
  | Kbind:
    forall (b_id: AST.ident)     (* identifier to bind *)
           (* (e: env)            (* execution environment of f *) *)
           (c: cmd)        (* command to execute next *)
           (k: cont)           (* then continue with k *)
    , cont

  | Kloop1:
    forall (c_cond: cmd)
           (id_cond: AST.ident)
           (c_body: cmd)
           (id_body: AST.ident)
           (k: cont)
    , cont

  | Kloop2:
    forall (c_cond: cmd)
           (id_cond: AST.ident)
           (c_body: cmd)
           (id_body: AST.ident)
           (k: cont)
    , cont

  (* 4. As a sub-function call *)
  | Kcall:
    forall (* (optid: AST.ident) (* Where to store the result of the function call *) *)
           (fn: function)      (* calling function f *)
           (e: env)            (* execution environment of f *)
           (locals: list (@name St))  (* stack variables of f *)
           (sp: Values.block)  (* stack pointer of f *)
           (k: cont)           (* then continue with k *)
    , cont

  .

  Inductive is_seq_cont: cont -> Prop :=
  | seq_cont_Kbind: forall b_id c_next k, is_seq_cont (Kbind b_id c_next k)
  | seq_cont_Kloop1: forall c_cond id_cond c_body id_body k, is_seq_cont (Kloop1 c_cond id_cond c_body id_body k)
  | seq_cont_Kloop2: forall c_cond id_cond c_body id_body k, is_seq_cont (Kloop2 c_cond id_cond c_body id_body k)
  .

  Inductive seq_cont_target: cont -> AST.ident -> Prop :=
  | seq_target_Kbind: forall b_id c_next k, seq_cont_target (Kbind b_id c_next k) b_id
  | seq_target_Kloop1: forall c_cond id_cond c_body id_body k, seq_cont_target (Kloop1 c_cond id_cond c_body id_body k) id_cond
  | seq_target_Kloop2: forall c_cond id_cond c_body id_body k, seq_cont_target (Kloop2 c_cond id_cond c_body id_body k) id_body
  .

  Inductive resolve_seq_cont: cont -> value -> cmd -> cont -> Prop :=
  | resolve_seq_Kbind: forall b_id c_next k v, resolve_seq_cont (Kbind b_id c_next k) v c_next k
  | resolve_seq_Kloop1: forall c_cond id_cond c_body id_body k b,
      resolve_seq_cont
        (Kloop1 c_cond id_cond c_body id_body k)
        (v_bool b)
        (if b then c_body else (c_ret e_tt t_unit))
        (if b then Kloop2 c_cond id_cond c_body id_body k else k)
  | resolve_seq_Kloop2: forall c_cond id_cond c_body id_body k, resolve_seq_cont (Kloop2 c_cond id_cond c_body id_body k) v_tt (c_while c_cond id_cond c_body id_body) (Kloop1 c_cond id_cond c_body id_body k)
  .

  Inductive is_call_cont: cont -> Prop :=
  | call_cont_Kstop: is_call_cont Kstop
  | call_cont_Kcall: forall fn e locals sp k, is_call_cont (Kcall fn e locals sp k)
  .

  Definition cont_target (k: cont): option AST.ident :=
    match k with
    | Kbind b_id _ _ => Some b_id
    | Kloop1 _ id_cond _ _ _ => Some id_cond
    | Kloop2 _ _ _ id_body _ => Some id_body
    | Kcall _ _ _ _ _ => None
    | Kstop => None
    end.

  Inductive state: Type :=
  | State:                              (* Execution within a function *)
    forall (fn: function)               (* currently executing function *)
           (c: cmd)                     (* command under consideration *)
           (k: cont)                    (* its continuation -- what to do next *)
           (e: env)                     (* current local environment *)
           (locals: list (@name St))    (* List of stack variables *)
           (sp: Values.block)           (* CompCert stack pointer *)
           (s: Primitives.State St Hp)  (* current memory and register states as viewed by GallinaC *)
           (m: mem)                     (* current memory as viewed by CompCert *)
           (inj: @injection St)
    , state
  | Callstate:                          (* Invocation of a function *)
    forall (f: fundef)                  (* function to invoke *)
           (arg: list value)            (* arguments provided by the caller *)
           (k: cont)                    (* what to do next *)
           (s: Primitives.State St Hp)  (* current memory and register states as viewed by GallinaC *)
           (m: mem)                     (* current memory as viewed by CompCert *)
           (inj: @injection St)
    , state
  | Returnstate:                        (* Return from a function *)
    forall (v: value)                   (* Return value *)
           (k: cont)                    (* what to do next *)
           (s: Primitives.State St Hp)  (* current memory and register states *)
           (m: mem)                     (* current memory as viewed by CompCert *)
           (inj: @injection St)
    , state
  .

  Definition mem_of_state (s: state): mem :=
    match s with
    | State _ _ _ _ _ _ _ m _ => m
    | Callstate _ _ _ _ m _ => m
    | Returnstate _ _ _ m _ => m
    end.

  Definition state_of_state (s: state): @Primitives.State St Hp :=
    match s with
    | State _ _ _ _ _ _ s _ _ => s
    | Callstate _ _ _ s _ _ => s
    | Returnstate _ _ s _ _ => s
    end.

  (* Fixpoint prog_init_store (ge: genv) (defs: list (AST.ident * globdef)): list (_ * (Values.block * ptrofs)) := *)
  (*   match defs with *)
  (*   | [] => [] *)
  (*   | (_, AST.Gfun _) ::defs => prog_init_store ge defs *)
  (*   | (id, AST.Gvar (AST.mkglobvar (mkvardef _) _ _ _)) :: defs => *)
  (*       match Genv.find_symbol ge id with *)
  (*       | Some b => *)
  (*           (nm, (b, Ptrofs.zero)) *)
  (*             :: prog_init_store ge defs *)
  (*       | None => [] *)
  (*       end *)
  (*   end. *)

  (* Fixpoint prog_init_fun (ge: @genv St) (defs: list (AST.ident * @globdef St)): list (AST.ident * Values.block) := *)
  (*   match defs with *)
  (*   | [] => [] *)
  (*   | (id, AST.Gfun _) :: defs => *)
  (*       match Genv.find_symbol ge id with *)
  (*       | Some b => *)
  (*           (id, b) :: prog_init_fun ge defs *)
  (*       | None => [] *)
  (*       end *)
  (*   | (_, AST.Gvar _) :: defs => *)
  (*       prog_init_fun ge defs *)
  (*   end. *)

  Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro:
    forall ge b f s0 m0 inj0
           (wt_prog: wt_program p)
           (init_prog_genv: Genv.globalenv p = ge)
           (init_init_state: init_state p = Some (s0, m0, inj0))
           (init_wf_inj: CCInj.wf s0 m0 inj0)
           (init_find_main_block: Genv.find_symbol ge (AST.prog_main p) = Some b)
           (init_find_main_funct: Genv.find_funct_ptr ge b = Some f)
           (init_main_sig: funsig f (mk_signature [] t_nat) ),
      initial_state p (Callstate f [] Kstop s0 m0 inj0)
  .

  Inductive final_state: state -> Integers.int -> Prop :=
  | final_state_intro: forall r s m inj,
      final_state (Returnstate (v_nat r) Kstop s m inj) (Integers.Int.repr (Z.of_nat r))
  .

  Fixpoint eval (e: expr) (env: env): option value :=
    match e with
    | e_var id =>
        match PTree.get id env with
        | Some v => Some v
        | _ => None
        end
    | e_tt => Some v_tt
    | e_bool b => Some (v_bool b)
    | e_nat n => Some (v_nat n)
    | e_ofst n => Some (v_ofst n)
    | e_nullptr => Some (v_ptr Pointer.NULL)
    | e_neg e =>
        match eval e env with
        | Some (v_bool b) => Some (v_bool (negb b))
        | _ => None
        end
    | e_plus e1 e2 =>
        match eval e1 env, eval e2 env with
        | Some (v_nat n1), Some (v_nat n2) => Some (v_nat (@Intops.Unsigned.add Uint32.nat_uint32_t n1 n2))
        | _, _ => None
        end
    | e_nat_eq e1 e2 =>
        match eval e1 env, eval e2 env with
        | Some (v_nat n1), Some (v_nat n2) => Some (v_bool (n1 =? n2))
        | _, _ => None
        end
    end.

  Fixpoint set_params {A: Type} (params: list (AST.ident * A)) (inits: list value): env :=
    match params, inits with
    | [], [] => PTree.empty value
    | (id, _)::params, v::inits => PTree.set id v (set_params params inits)
    | _, _ => PTree.empty _
    end.

  Definition pop_stack {St Hp} sp stackspace (s: Primitives.State St Hp) (m: Memory.mem) (inj: @injection St): option (Primitives.State St Hp * Memory.mem * @injection St) :=
    match Mem.free m sp 0 stackspace with
    | Some m' =>
        match NExt.iter_opt (fun st => Store.pop st) (Z.to_N stackspace) s.(Primitives.store) with
        | Some st' =>
            Some
              (
                Primitives.mkState st' s.(Primitives.heap),
                m',
                {|
                  inj_hp_map := inj.(inj_hp_map);
                  inj_st_map := N.iter (Z.to_N stackspace) (@tl _) inj.(inj_st_map);
                  inj_fn_map := inj.(inj_fn_map);
                |}
              )
        | None => None
        end
    | None => None
    end
  .

  (* "Primitive" operations *)
  Inductive builtin: cmd -> genv -> map_ctxt value -> list (@name St) -> Values.block -> Primitives.State St Hp -> mem -> @CCInj.injection St -> value -> Primitives.State St Hp -> mem -> @CCInj.injection St -> Prop :=
  | builtin_ret: forall e t genv env locals sp s m inj v
                        (EVAL: eval e env = Some v)
                        (WT: wt_value v t)
    , builtin
        (c_ret e t) genv env locals sp s m inj v s m inj

  | builtin_read_var: forall n t genv env sp locals s m inj v nm
                             (DEREF: List.nth_error locals n = Some nm)
                             (LOOKUP: Store.lookup s.(store) nm = Some (memval_of_value v))
                             (WT: wt_value v t)
    , builtin
        (c_read_var n t) genv env locals sp
        s m inj
        v
        s m inj
  | builtin_write_var: forall n t e genv env locals sp s m inj st' m' v nm
                              (EVAL: eval e env = Some v)
                              (DEREF: List.nth_error locals n = Some nm)
                              (MUTATE: Store.mutate s.(store) nm (memval_of_value v) = Some st')
                              (WT: wt_value v t)
                              (STORE: (Sized t /\ exists v_cc mc, Mem.store mc m sp (offset_to_offset (Z.of_nat n)) v_cc = Some m' /\ type_mem_chunk t = Some mc /\ CCInj.InjValue inj v v_cc) \/ (~Sized t /\ m' = m))
    , builtin
        (c_write_var n t e) genv env locals sp
        s m inj
        v_tt
        {| store := st'; heap := s.(heap); |} m' inj

  | builtin_alloc_ptr: forall e_size t e_init id_ptr id_init genv env locals sp s m inj addr prov hp' m' v_size v_init mc m_i0 m_i1 b_cc v_cc
                              (EVAL_SIZE: eval e_size env = Some (v_ofst v_size))
                              (EVAL_INIT: eval e_init env = Some v_init)
                              (WT: wt_value v_init t)
                              (ALLOC_GC: Heap.alloc s.(heap) v_size (memval_of_value v_init) = Some (hp', Some (addr, prov)))
                              (ALLOC_CC: Mem.alloc m (- Memdata.size_chunk AST.Mptr) ((Z.of_N v_size) * (Memdata.size_chunk mc)) = (m_i0, b_cc))
                              (STORE_SIZE: Mem.store AST.Mptr m_i0 b_cc (- Memdata.size_chunk AST.Mptr) (Values.Vptrofs (Ptrofs.repr (Z.of_N v_size))) = (Some m_i1))
                              (STORE_INIT: fold_left_opt (fun m n => Mem.store mc m b_cc (Z.of_nat (n * Memdata.size_chunk_nat mc)) v_cc) (List.seq 0 (N.to_nat v_size)) m_i1 = Some m')
                              (EQmc: type_mem_chunk t = Some mc)
                              (INJ: CCInj.InjValue inj v_init v_cc)
    , builtin
        (c_alloc_ptr e_size t e_init id_ptr id_init) genv env locals sp
        s m inj
        (v_ptr (Some (addr, prov)))
        {| store := s.(store); heap := hp'; |} m'
        {| inj_hp_map := (Addr.block addr, b_cc)::inj.(inj_hp_map); inj_st_map := inj.(inj_st_map); inj_fn_map := inj.(inj_fn_map) |}
  | builtin_read_ptr: forall e_ptr t genv env locals sp s m inj v_read v_ptr
                             (EVAL: eval e_ptr env = Some (Value.v_ptr v_ptr))
                             (LOOKUP: Heap.lookup s.(heap) v_ptr = Some (memval_of_value v_read))
                             (WT: wt_value v_read t)
                             (LOAD: Sized t -> exists v_ptr_b_cc v_ptr_ofs_cc v_read_cc mc,
                                   Mem.load mc m v_ptr_b_cc (Ptrofs.unsigned v_ptr_ofs_cc) = Some v_read_cc /\ type_mem_chunk t = Some mc /\ CCInj.InjValue inj (Value.v_ptr v_ptr) (Values.Vptr v_ptr_b_cc v_ptr_ofs_cc) /\ CCInj.InjValue inj v_read v_read_cc)
    , builtin
        (c_read_ptr e_ptr t) genv env locals sp
        s m inj
        v_read
        s m inj
  | builtin_write_ptr: forall e_ptr t e_data genv env locals sp s m inj hp' m' v_ptr v_data
                              (EVAL_ptr: eval e_ptr env = Some (Value.v_ptr v_ptr))
                              (EVAL_data: eval e_data env = Some v_data)
                              (MUTATE: Heap.mutate s.(heap) v_ptr (memval_of_value v_data) = Some hp')
                              (WT: wt_value v_data t)
                              (STORE: (Sized t /\ exists v_ptr_b_cc v_ptr_ofs_cc v_data_cc mc, Mem.store mc m v_ptr_b_cc (Ptrofs.unsigned v_ptr_ofs_cc) v_data_cc = Some m' /\ type_mem_chunk t = Some mc /\ CCInj.InjValue inj (Value.v_ptr v_ptr) (Values.Vptr v_ptr_b_cc v_ptr_ofs_cc) /\ CCInj.InjValue inj v_data v_data_cc) \/ (~Sized t /\ m' = m))

    , builtin
        (c_write_ptr e_ptr t e_data) genv env locals sp
        s m inj
        v_tt
        {| store := s.(store); heap := hp' |} m' inj
  | builtin_free_ptr: forall e_ptr genv env locals sp s m inj hp' m' addr prov b ofs
                             (EVAL: eval e_ptr env = Some (Value.v_ptr (Some (addr, prov))))
                             (FREE_GC: Heap.free s.(heap) (Some (addr, prov)) = Some hp')
                             (FREE_CC: Mem.free m b (- Memdata.size_chunk AST.Mptr) (Z.of_N (Provenance.prov_meofst prov)) = Some m')
                             (INJ: CCInj.InjValue inj (v_ptr (Some (addr, prov))) (Values.Vptr b ofs))
    , builtin
        (c_free_ptr e_ptr) genv env locals sp
        s m inj
        v_tt
        {| store := s.(store); heap := hp' |} m'
        {|
          inj_hp_map := @remove_bind _ _ _ Nat.eq_dec (Addr.block addr) inj.(inj_hp_map);
          inj_st_map := inj.(inj_st_map);
          inj_fn_map := inj.(inj_fn_map);
        |}

  | builtin_shift_fw_ptr: forall e_ptr e_shift genv env locals sp s m inj v_ptr' v_ptr v_shift
                                 (EVAL_ptr: eval e_ptr env = Some (Value.v_ptr v_ptr))
                                 (EVAL_shift: eval e_shift env = Some (v_ofst v_shift))
                                 (SHIFT: Pointer.Shift v_ptr v_shift v_ptr')
                                 (WVALID_pre: Heap.Facts.WValid s.(heap) v_ptr)
                                 (WVALID_post: Heap.Facts.WValid s.(heap) v_ptr')
    , builtin
        (c_shift_fw_ptr e_ptr e_shift) genv env locals sp
        s m inj
        (Value.v_ptr v_ptr')
        s m inj
  | builtin_shift_bw_ptr: forall e_ptr e_shift genv env locals sp s m inj v_ptr' v_ptr v_shift
                                 (EVAL_ptr: eval e_ptr env = Some (Value.v_ptr v_ptr))
                                 (EVAL_shift: eval e_shift env = Some (v_ofst v_shift))
                                 (SHIFT: Pointer.Shift v_ptr' v_shift v_ptr)
                                 (WVALID_pre: Heap.Facts.WValid s.(heap) v_ptr)
                                 (WVALID_post: Heap.Facts.WValid s.(heap) v_ptr')
    , builtin
        (c_shift_bw_ptr e_ptr e_shift) genv env locals sp
        s m inj
        (Value.v_ptr v_ptr')
        s m inj
  | builtin_eq_ptr: forall e_ptr_l e_ptr_r genv env locals sp s m inj b v_ptr_l v_ptr_r
                           (EVAL_l: eval e_ptr_l env = Some (v_ptr v_ptr_l))
                           (EVAL_r: eval e_ptr_r env = Some (v_ptr v_ptr_r))
                           (WVALID_l: Heap.Facts.WValid s.(heap) v_ptr_l)
                           (WVALID_r: Heap.Facts.WValid s.(heap) v_ptr_r)
                           (CMP: Pointer.cmp v_ptr_l v_ptr_r = Some b)
    , builtin
        (c_ptr_eq e_ptr_l e_ptr_r) genv env locals sp
        s m inj
        (v_bool b)
        s m inj
  .

  (* One step of execution *)
  (* Somewhere between CompCert.Cminor and GallinaC.Opsem *)
  (* Since C(minor) statements are essentially non-value-carrying, *)
  (* they perform their side-effects and then reduce to a skip statement *)
  (* When a skip statement is encountered, the continuation tells what to do *)
  (* In GallinaC, commands are value-carrying, thus there is no indirection *)
  (* Rules are listed in CompCert order, but follow GallinaC naming convention *)
  Inductive step: genv -> state -> Events.trace -> state -> Prop :=
  (* step_skip_* | N/A *)
  (* | step_skip_False: forall ge s1 e s2, False -> step ge s1 e s2 *)

  (* step_assign -> step_skip_seq | step_bind *)
  | step_bind: forall ge f id_b t_b c_b c_c t_c k env locals sp s m inj,
      step
        ge
        (State f (c_bind id_b t_b c_b c_c t_c) k locals env sp s m inj)
        Events.E0
        (State f c_b (Kbind id_b c_c k) locals env sp s m inj)

  (* N/A | step_builtin *)
  | step_builtin_call_cont: forall ge f c k env locals sp s m inj v m' s' inj' m'' s'' inj''
                                   (Hcall_cont: is_call_cont k)
                                   (BUILTIN: builtin c ge env locals sp s m inj v s' m' inj')
                                   (Hpop_stack: pop_stack sp f.(fn_extra).(fn_stackspace) s' m' inj' = Some (s'', m'', inj''))
    , step
        ge
        (State f c k env locals sp s m inj)
        Events.E0
        (Returnstate v k s'' m'' inj'')

  | step_builtin_seq_cont: forall ge f c k env locals sp s m inj c_next k' target_id v s' m' inj'
                                  (Hseq_target: seq_cont_target k target_id)
                                  (Hresolve_seq: resolve_seq_cont k v c_next k')
                                  (BUILTIN: builtin c ge env locals sp s m inj v s' m' inj')
    , step
        ge
        (State f c k env locals sp s m inj)
        Events.E0
        (State f c_next k' (PTree.set target_id v env) locals sp s' m' inj')

  (* (* N/A | step_builtin *) *)
  (* | step_builtin_Kbind: forall ge f c id c_next k env sp s m inj v m' s' inj' *)
  (*                              (BUILTIN: prim_effect c ge env sp s m inj v s' m' inj') *)
  (*   , step *)
  (*       ge *)
  (*       (State f c (Kbind id c_next k) env sp s m inj) *)
  (*       Events.E0 *)
  (*       (State f c_next k (PTree.set id v env) sp s' m' inj') *)
  (* | step_builtin_Kloop1_true: forall ge f c c_cond id_cond c_body id_body k env sp s m inj s' m' inj' *)
  (*                                    (BUILTIN: prim_effect c ge env sp s m inj (v_bool true) s' m' inj') *)
  (*   , step *)
  (*       ge *)
  (*       (State f c (Kloop1 c_cond id_cond c_body id_body k) env sp s m inj) *)
  (*       Events.E0 *)
  (*       (State f c_body (Kloop2 c_cond id_cond c_body id_body k) env sp s' m' inj') *)
  (* | step_builtin_Kloop1_false: forall ge f c c_cond id_cond c_body id_body k env sp s m inj s' m' inj' *)
  (*                                    (BUILTIN: prim_effect c ge env sp s m inj (v_bool false) s' m' inj') *)
  (*   , step *)
  (*       ge *)
  (*       (State f c (Kloop1 c_cond id_cond c_body id_body k) env sp s m inj) *)
  (*       Events.E0 *)
  (*       (State f (c_ret e_tt t_unit) k env sp s' m' inj') *)
  (* | step_builtin_Kloop2: forall ge f c c_cond id_cond c_body id_body k env sp s m inj s' m' inj' *)
  (*                               (BUILTIN: prim_effect c ge env sp s m inj v_tt s' m' inj') *)
  (*   , step *)
  (*       ge *)
  (*       (State f c (Kloop2 c_cond id_cond c_body id_body k) env sp s m inj) *)
  (*       Events.E0 *)
  (*       (State f (c_while c_cond id_cond c_body id_body) k env sp s m inj) *)

  (* step_call | step_[bf]app *)
  | step_app: forall
      ge fn id t_out args k env locals sp s m inj v_args b fd
      (Heval_args: map_opt (fun e => eval e env) (List.map fst args) = Some v_args)
      (Hfind_symbol: Globalenvs.Genv.find_symbol ge id = Some b)
      (Hfind_funct_ptr: Globalenvs.Genv.find_funct_ptr ge b = Some fd)
      (Hseq_cont: is_seq_cont k),
      step
        ge
        (State fn (c_app id t_out args) k env locals sp s m inj)
        Events.E0
        (Callstate fd v_args (Kcall fn env locals sp k) s m inj)

  | step_tailapp: forall
      ge fn f_id t_out args k env locals sp s m inj fd v_args s' m' inj' b
      (Heval_args: map_opt (fun e => eval e env) (List.map fst args) = Some v_args)
      (Hfind_symbol: Globalenvs.Genv.find_symbol ge f_id = Some b)
      (Hfind_funct_ptr: Globalenvs.Genv.find_funct_ptr ge b = Some fd)
      (Hpop_stack: pop_stack sp fn.(fn_extra).(fn_stackspace) s m inj = Some (s', m', inj'))
      (Hcall_cont: is_call_cont k)
    , step
        ge
        (State fn (c_app f_id t_out args) k env locals sp s m inj)
        Events.E0
        (Callstate fd v_args k s' m' inj')

  (* step_ifthenelse | step_if_(true|false) *)
  | step_ifthenelse: forall ge fn e_i c_t c_e t k env locals sp s m inj b
      (Heval_if: eval e_i env = Some (v_bool b)),
      step
        ge
        (State fn (c_if e_i c_t c_e t) k env locals sp s m inj)
        Events.E0
        (State fn (if b then c_t else c_e) k env locals sp s m inj)

  (* step_loop | step_while *)
  | step_while: forall ge fn c_cond id_cond c_body id_body k env locals sp s m inj,
      step
        ge
        (State fn (c_while c_cond id_cond c_body id_body) k env locals sp s m inj)
        Events.E0
        (State fn c_cond (Kloop1 c_cond id_cond c_body id_body k) env locals sp s m inj)

  (* step_internal_function | N/A *)
  | step_internal_function: forall ge fn args k locals sp s m inj env m' st
                                   (* NOTE Unlike C, we don't need to set the locals/temporary variables because wt_expr implies read after write *)

      (Hwt_args: Forall2T wt_value args (List.map snd fn.(fn_params)))
      (Halloc_sp: Mem.alloc m 0 (offset_to_offset fn.(fn_extra).(fn_stackspace)) = (m', sp))
      (Hset_params: set_params fn.(fn_params) args = env)
      (Hset_locals: N.iter
                      (Z.to_N fn.(fn_extra).(fn_stackspace))
                                      (fun '(st,locals) =>
                                         let '(st,local) := Store.push st VUnit in
                                         (st, local::locals)) (s.(Primitives.store), []) = (st,locals))
      (Hcall_cont: is_call_cont k),
      step
        ge
        (Callstate (AST.Internal fn) args k s m inj)
        Events.E0
        (State fn fn.(fn_body) k env locals sp {| store := st; heap := s.(heap) |} m' {| inj_hp_map := inj.(inj_hp_map); inj_st_map := ListExt.mapi (fun local ofst => (local, (sp, memval_memsize * ofst, true))) locals ++ inj.(inj_st_map); inj_fn_map := inj.(inj_fn_map) |})

  | step_external_function: forall ge nm sig args k s m inj
                                   (ToX_out: CCInj.type_of_xtype sig.(AST.sig_res) t_unit)
                                   (CALLK: is_call_cont k)
    , step
        ge
        (Callstate (AST.External (AST.EF_external nm sig)) args k s m inj)
        Events.E0
        (Returnstate v_tt k s m inj)
  (* (* step_return | N/A *) *)
  (* (* return from a function into the stop continuation *) *)
  (* | step_return_call_stop: forall ge v f env sp s m inj, *)
  (*     step *)
  (*       ge *)
  (*       (Returnstate v (Kcall f env sp Kstop) s m inj) *)
  (*       Events.E0 *)
  (*       (Returnstate v Kstop s m inj) *)

  (* step_return | N/A *)
  (* return from a function into a binding *)
  | step_return_call_seq: forall ge v fn env locals sp k s m inj c_next k' target_id
                                 (Hseq_target: seq_cont_target k target_id)
                                 (Hresolve_seq: resolve_seq_cont k v c_next k'),
      step
        ge
        (Returnstate v (Kcall fn env locals sp k) s m inj)
        Events.E0
        (State fn c_next k' (PTree.set target_id v env) locals sp s m inj)

  (* (* step_return | N/A *) *)
  (* (* return from a function into a call *) *)
  (* | step_return_call_call: forall ge v f env sp f' env' k s m inj, *)
  (*     step *)
  (*       ge *)
  (*       (Returnstate v (Kcall f env sp (Kcall f' env' sp k)) s m inj) *)
  (*       Events.E0 *)
  (*       (Returnstate v (Kcall f' env' sp k) s m inj) *)
.

  Definition semantics (p : program) :=
    Smallstep.Semantics step (initial_state p) final_state (Globalenvs.Genv.globalenv p).

End Semantics.

Section Typing.
  Context {St: Store}.
  Context {Hp: Heap}.

  Record wt_env (f: function) (ty_env: map_ctxt (type * bool)) (val_env: env): Type :=
    {
      wt_val_env: forall var_id t,
        In (var_id,t) (f.(fn_params) ++ f.(fn_temps)) ->
        { t &
          match PTree.get var_id val_env with
          | Some v => wt_value v t + (PTree.get var_id ty_env = Some (t,true))
          | None => PTree.get var_id ty_env = Some (t, false)
          end };
      wv_ty_env: forall var_id t b, PTree.get var_id ty_env = Some (t, b) -> (if b then { v & PTree.get var_id val_env = Some v & wt_value v t } else PTree.get var_id val_env = None) * In (var_id,t) (f.(fn_params) ++ f.(fn_temps));
    }.

  (* Continuations can be viewed as functions with type t -> k, where
   * * t is the type expected by the continuation
   *   * For Kstop it is t_nat
   *   * For Kcall it is the return type of the function
   *   * For Kbind it is the type of the variable to be bound
   * * k is an unconstructable type
   *
   * In essence, it is impossible to escape the continuation
   * except by providing a value of the requested type
   *
   * Kstop is the "main" continuation, i.e. it is how we exit the program.
   * By convention main has signature int main ()
   * Thus for all program contexts, Kstop always expects a value of type t_nat
   * Typically, inside `main`, the continuation is simply `Kstop`
   * The well-typedness of the Kstop continuation is thus
   * `forall ctx, wt_cont_call ctx Kstop t_nat`
   *
   * Kcall is a continuation to exit a function and return to the caller
   * Typically, if `main` terminates with a tailcall of `int tail (int, int)`
   * The continuation will be `Kcall f_main env_main sp_main Kstop`
   * This continuation is only well-typed if
   * returning from it produces exactly the type expected by the lower continuation
   *
   * Kbind is a continuation similar to Kseq in C-languages
   * We are currently evaluating a command, but when it "terminates", we don't exit the function
   * Instead, we bind the result to the provided variable
   * Typically, if when calling `int helper(int, int)` from `main` we enter a bind
   * The continuation could look like
   * `Kbind id_b_helper c_rest_helper
        (Kcall f_main env_main sp_main
          (Kbind id_b_main c_rest_main
            Kstop))`
   * This continuation is well-typed, iff
   * Executing the current command returns a value matching `id_b_helper`
   * Executing `c_rest_helper` produces a value match matching `id_b_main`
   * Executing `c_rest_main` produces a value of type `t_nat`
   * Thus Kbind is only well-type if
   * * Returning from it produces the type of id
   * * Executing c produces the type expected by k
   *)
  Inductive wt_cont_call: ctxt Empty_set Empty_set fundef vardef -> @cont St -> type -> Prop :=
  | wt_Kstop: forall ctx, wt_cont_call ctx Kstop t_nat
  | wt_Kcall: forall ctx f env locals sp k t ty_env
                     (Hwt_fn: wt_function ctx f)
                     (Hwt_env: wt_env f ty_env env)
                     (Hwt_cont: wt_cont (with_pure ty_env (with_stack (List.map (fun _ => tt) locals) ctx)) k t),
      wt_cont_call ctx (Kcall f env locals sp k) t

  with wt_cont: ctxt (type * bool) unit fundef vardef -> @cont St -> type -> Prop :=
  | wt_cont_Kbind: forall ctx id c k t_b t_c
                          (Hget_pure: get_pure id ctx = Some (t_b, false))
                          (Hwt_cmd: wt_cmd (set_pure id (t_b, true) ctx) c t_c)
                          (Hwt_cont: wt_cont ctx k t_c),
      wt_cont ctx (Kbind id c k) t_b
  | wt_cont_Kloop1: forall ctx c_cond id_cond c_body id_body k b
                           (Hwt_cond: wt_cmd ctx c_cond t_bool)
                           (Hwt_body: wt_cmd ctx c_body t_unit)
                           (Hwt_cont: wt_cont ctx k t_unit)
                           (Hget_pure: get_pure id_cond ctx = Some (t_bool, b)),
      wt_cont ctx (Kloop1 c_cond id_cond c_body id_body k) t_bool
  | wt_cont_Kloop2: forall ctx c_cond id_cond c_body id_body k b
                           (Hwt_cond: wt_cmd ctx c_cond t_bool)
                           (Hwt_body: wt_cmd ctx c_body t_unit)
                           (Hwt_cont: wt_cont ctx k t_unit)
                           (Hget_pure: get_pure id_body ctx = Some (t_unit, b)),
      wt_cont ctx (Kloop2 c_cond id_cond c_body id_body k) t_unit
  | wt_cont_other: forall ctx k tret
                          (Hwt_cont_call: wt_cont_call (with_pure (PTree.empty _) (with_stack [] ctx)) k tret),
      wt_cont ctx k tret
  .

  Record wt_State (f: function) (c: cmd) (k: @cont St) (e: env) (locals: list (@name St)) (sp: Values.block) (s: @Primitives.State St Hp) (m: mem) (inj: injection) (ctx: ctxt (type * bool) unit fundef vardef) (t: type) : Prop :=
    {
      State_wt_function: inhabited (wt_function (with_pure (PTree.empty _) (with_stack [] ctx)) f);
      State_wt_cmd: inhabited (wt_cmd ctx c t);
      State_wt_cont: wt_cont ctx k t;
      State_wt_env: inhabited (wt_env f ctx e);
      State_wf_inj: CCInj.wf s m inj;
      State_wt_stack: forall n loc, List.nth_error locals n = Some loc -> In (loc, (sp, memval_memsize * n, true)) inj.(inj_st_map);
    }.

  Inductive wt_state (p: program): @state St Hp -> Prop :=
  | wt_State_intro: forall f c k e locals sp s m inj ctx t
                     (Hwt_State: wt_State f c k e locals sp s m inj ctx t)
    , wt_state p (State f c k e locals sp s m inj)
  | wt_Callstate: forall f args k s m inj sig ctx
                         (Hwt_fundef: wt_fundef (mk_glob_ctxt p) f)
                         (Hwt_args: wt_fundef_call args f)
                         (Hsig: funsig f sig)
                         (Hwt_cont: wt_cont ctx k sig.(sig_res))
                         (Hwf_inj: CCInj.wf s m inj)
    , wt_state p (Callstate f args k s m inj)
  | wt_Returnstate: forall v k s m inj t ctx
                           (Hwt_res: wt_value v t)
                           (Hwt_cont: wt_cont ctx k t)
                           (Hwf_inj: CCInj.wf s m inj)
    , wt_state p (Returnstate v k s m inj)
  .

  Inductive step_ctxt_effect (ctx: ctxt (type * bool) unit fundef vardef): cmd -> @cont St -> ctxt (type * bool) unit fundef vardef -> Prop :=
  | step_ctxt_effect_bind : forall b_id t_b c_b c_c t_c k, step_ctxt_effect ctx (c_bind b_id t_b c_b c_c t_c) k ctx
  .
  (* | step_ctxt_effect_prim : forall c ge e sp s m inj v s' m' inj' (Hprim: @prim_effect St Hp c ge e sp s m inj v s' m' inj'), step_ctxt_effect ctx c ctx *)
  (* | step_ctxt_effect_if: forall e_if c_then c_else t_te, step_ctxt_effect ctx (c_if e_if c_then c_else t_te) ctx *)
  (* | step_ctxt_effect_while: forall c_cond id_cond c_body id_body, *)
  (*     step_ctxt_effect ctx (c_while c_cond id_cond c_body id_body) ctx *)
  (* . *)

End Typing.

Arguments wt_val_env {St f ty_env val_env}: rename.
Arguments wv_ty_env {St f ty_env val_env}: rename.

Module Facts.

  (* Lemma wt_env_fun_l {St f ctx_l e ctx_r} *)
  (*   (Hwt_function: wt_function (from_pure ctx_l) f) *)
  (*   (Hwt_env_l: @wt_env St f (ctxt_pure ctx_l) e) *)
  (*   (Hwt_env_r: @wt_env St f (ctxt_pure ctx_r) e): *)
  (*   PTree_Properties.Equal eq_equivalence (ctxt_pure ctx_l) (ctx_r. *)
  (* Proof. *)
  (*   destruct Hwt_env_l as ( wt_val_env_l & wv_ty_env_l ), *)
  (*       Hwt_env_r as ( wt_val_env_r & wv_ty_env_r ). *)
  (*   intros var_id. *)
  (*   specialize (wt_val_env_l var_id). *)
  (*   specialize (wv_ty_env_l var_id). *)
  (*   specialize (wt_val_env_r var_id). *)
  (*   specialize (wv_ty_env_r var_id). *)
  (*   destruct (ctx_l ! var_id) as [ [ t b ] | ] eqn:Ectx_l; *)
  (*     destruct (ctx_r ! var_id) as [ [ t' b' ] | ] eqn:Ectx_r; auto. *)
  (*   - specialize (wv_ty_env_l t b ltac:(reflexivity)) as ( wv_ty_env_l & HIn ). *)
  (*     specialize (wt_val_env_l t HIn) as ( t'' & wt_val_env_l ). *)
  (*     specialize (wt_val_env_r t HIn) as ( t''' & wt_val_env_r ). *)
  (*     specialize (wv_ty_env_r t' b' ltac:(reflexivity)) as ( wv_ty_env_r & HIn' ). *)

  (*     destruct b. *)
  (*     +  destruct wv_ty_env_l as ( v & Eget_val_env & Hwt_val ). *)
  (*        rewrite Eget_val_env in wt_val_env_l, wt_val_env_r. *)
  (*        destruct wt_val_env_l as ( Hwt_val' & Heq); *)
  (*          inversion Heq; subst t''; subst; clear Heq Hwt_val'. *)
  (*        destruct wt_val_env_r as ( Hwt_val' & Heq ); *)
  (*          inversion Heq; subst t''';  subst; clear Heq Hwt_val'. *)
  (*        destruct wv_ty_env_r as ( v' & Hget_val_env' & Hwt_val'); *)
  (*          assert (v' = v) by congruence; subst; *)
  (*          rewrite (Facts.wt_value_fun Hwt_val Hwt_val'); now eauto. *)
  (*     + rewrite wv_ty_env_l in wt_val_env_l, wt_val_env_r. *)
  (*       inversion wt_val_env_l; subst; clear wt_val_env_l; *)
  (*         inversion wt_val_env_r; subst; clear wt_val_env_r. *)
  (*       assert (t''' = t'') by congruence; subst;  *)
  (* Qed. *)

  Lemma cont_target_seq_cont_target_Some {St}: forall k target_id, cont_target k = (Some target_id) -> @seq_cont_target St k target_id.
  Proof.
    induction k; intros target_id CT;
      try (inversion CT);
      subst;
      now constructor.
  Qed.

  Lemma cont_target_seq_cont_target_None {St}: forall k, cont_target k = None -> forall target_id, ~@seq_cont_target St k target_id.
  Proof.
    induction k; intros CT;
      try (inversion CT; subst);
      intros target_id ST;
      inversion ST.
  Qed.

  Lemma seq_cont_target_cont_target {St}: forall k target_id, @seq_cont_target St k target_id -> cont_target k = (Some target_id).
    intros k target_id ST;
      inversion ST; subst; reflexivity.
  Qed.

  Lemma call_cont_target {St k}
    (Hcall_cont: @is_call_cont St k)
    : cont_target k = None.
  Proof.
    now destruct Hcall_cont.
  Qed.

End Facts.
