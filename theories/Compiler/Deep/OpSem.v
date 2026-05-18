From Stdlib Require Import ZArith.

From compcert.common Require Events Smallstep.

From GallinaC.Utils Require Import ListExt.
From GallinaC.Imp Require Import Heap Store Primitives Intops Uint32 Uintptr.
From GallinaC.Compiler.Common Require Import Types Ctxt Value Expr.
From GallinaC.Compiler.Deep Require Import Cmd Prog Typing.

Section State.

  Context {St: Store}.
  Context {Hp: Heap}.

  (* C evaluation under the CompCert model is CPS *)
  (* Hence, at any point in time, only one command (statement) is under consideration at a time *)
  (* Control-flow operations simply pushes values onto a continuation stack *)
  (* When a command terminates, it looks at the continuation to determine what to do with the result *)
  Inductive cont: Type :=
  (* 1. To return from the program execution *)
  | Kstop: cont
  (* 2. To bind the result in a temporary variable *)
  | Kbind:
    forall (id_b: AST.ident)            (* identifier to bind *)
           (c: cmd)                     (* command to execute next *)
           (k: cont)                    (* then continue with k *)
    , cont
  (* 3. To evaluate the condition of a while loop *)
  | Kloop1:
    forall (c_cond: cmd)                (* command of the condition *)
           (c_body: cmd)                (* command of the body *)
           (k: cont)                    (* when the loop terminates, continue with k *)
    , cont
  (* 4. To evaluate the body of a while loop *)
  | Kloop2:
    forall (c_cond: cmd)                (* command of the condition *)
           (c_body: cmd)                (* command of the body *)
           (k: cont)                    (* when the loop terminates, continue with k *)
    , cont
  (* 5. To return from a sub-function call *)
  | Kcall:
    forall (fn: function)               (* calling function f *)
           (e: map_ctxt value)          (* execution environment of f *)
           (locals: list (@name St))    (* live local variables of f *)
           (k: cont)                    (* then continue with k *)
    , cont
  .

  Inductive is_call_cont: cont -> Prop :=
  | call_cont_Kstop: is_call_cont Kstop
  | call_cont_Kcall: forall fn e locals k, is_call_cont (Kcall fn e locals k)
  .

  Inductive is_seq_cont: cont -> Prop :=
  | call_cont_Kbind: forall id_b c_next k, is_seq_cont (Kbind id_b c_next k)
  | call_cont_Kloop1: forall c_cond c_body k, is_seq_cont (Kloop1 c_cond c_body k)
  | call_cont_Kloop2: forall c_cond c_body k, is_seq_cont (Kloop1 c_cond c_body k)
  .

  Inductive resolve_seq_cont: cont -> map_ctxt value -> value -> cmd -> map_ctxt value -> cont -> Prop :=
  | resolve_seq_Kbind: forall id_b c_next k env v,
      resolve_seq_cont
        (Kbind id_b c_next k)
        env
        v
        c_next
        (Maps.PTree.set id_b v env)
        k
  | resolve_seq_Kloop1: forall c_cond c_body k env b,
      resolve_seq_cont
        (Kloop1 c_cond c_body k)
        env
        (v_bool b)
        (if b then c_body else (c_ret e_tt))
        env
        (if b then Kloop2 c_cond c_body k else k)
  | resolve_seq_Kloop2: forall c_cond c_body k env,
      resolve_seq_cont
        (Kloop2 c_cond c_body k)
        env
        v_tt
        c_cond
        env
        (Kloop1 c_cond c_body k)
  .

  Inductive state: Type :=
  | State:                              (* Execution within a function         *)
    forall (fn: function)               (* currently executing function        *)
           (c: cmd)                     (* command under consideration         *)
           (k: cont)                    (* its continuation -- what to do next *)
           (e: map_ctxt value)          (* current loval environment           *)
           (locals: list (@name St))    (* live local variables                *)
           (s: State St Hp)             (* current heap and store states       *)
    , state
  | Callstate:                          (* Invocation of a function *)
    forall (f: fundef)                  (* function to invoke       *)
           (arg: list value)            (* arguments provided by the caller *)
           (k: cont)                    (* what to do next *)
           (s: State St Hp)             (* current heap and store states *)
    , state
  | Returnstate:                        (* Return from a function *)
    forall (v: value)                   (* Return value *)
           (k: cont)                    (* what to do next *)
           (s: State St Hp)             (* current heap and store states *)
    , state
  .

  Definition state_of_state (s: state): Primitives.State St Hp :=
    match s with
    | State _ _ _ _ _ s => s
    | Callstate _ _ _ s => s
    | Returnstate _ _ s => s
    end.

  Definition alloc_global (s: Primitives.State St Hp) (g: globdef): option (Primitives.State St Hp) :=
    match g with
    | AST.Gfun _ => Some s
    | AST.Gvar _ => None
    end.

  Fixpoint alloc_globals (s: Primitives.State St Hp) (gl: list (AST.ident * globdef)): option (Primitives.State St Hp) :=
    match gl with
    | [] => Some s
    | (id, g)::gl =>
        match alloc_global s g with
        | Some s => alloc_globals s gl
        | None => None
        end
    end.

  Definition init_state (p: program): option state :=
    match findA (Pos.eqb p.(prog_main)) p.(prog_defs) with
    | None | Some (AST.Gvar _) => None
    | Some (AST.Gfun fd_main) =>
        match alloc_globals Primitives.emp p.(prog_defs) with
        | None => None
        | Some s0 => Some (Callstate fd_main [] Kstop s0)
        end
    end.

  Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro:
    forall ge0 f b
           (WT: wt_program p)
           (GE0: Globalenvs.Genv.globalenv p = ge0)
           (FIND_SYMB: Globalenvs.Genv.find_symbol ge0 (AST.prog_main p) = Some b)
           (FIND_FUNC: Globalenvs.Genv.find_funct_ptr ge0 b = Some f)
           (MAIN_SIG: funsig f (mk_signature [] t_nat))
    , initial_state p (Callstate f [] Kstop Primitives.emp)
  .

  Inductive final_state: state -> Integers.int -> Prop :=
  | final_state_intro: forall r s,
      final_state (Returnstate (v_nat r) Kstop s) (Integers.Int.repr (Z.of_nat r))
  .

  Fixpoint set_params [A: Type] (params: list (AST.ident * A)) (inits: list value): map_ctxt value :=
    match params, inits with
    | [], [] => Maps.PTree.empty _
    | (id, _)::params, v::inits => Maps.PTree.set id v (set_params params inits)
    | _, _ => Maps.PTree.empty _
    end.

  Definition pop_stack {St Hp} locals (s: Primitives.State St Hp): option (Primitives.State St Hp) :=
    match ListExt.fold_left_opt (B := @name St) (fun st _ => Store.pop st) locals s.(Primitives.store) with
    | Some st' => Some (Primitives.mkState st' s.(Primitives.heap))
    | None => None
    end
  .

  (* "Primitive" operations *)
  Inductive builtin: cmd -> genv -> map_ctxt value -> list (@name St) -> Primitives.State St Hp -> value -> Primitives.State St Hp -> Prop :=
  | builtin_ret: forall e genv env locals s v
                        (EVAL: eval e env = Some v)
    , builtin
        (c_ret e) genv env locals s v s

  | builtin_read_var: forall n t genv env locals s v mv nm
                             (DEREF: List.nth_error locals n = Some nm)
                             (LOOKUP: Store.lookup s.(store) nm = Some mv)
                             (VMV: value_memval v mv)
    , builtin
        (c_read_var n t) genv env locals
        s
        v
        s
  | builtin_write_var: forall n t e genv env locals s st' v nm
                              (EVAL: eval e env = Some v)
                              (DEREF: List.nth_error locals n = Some nm)
                              (MUTATE: Store.mutate s.(store) nm (memval_of_value v) = Some st')
                              (WT: wt_value v t)
    , builtin
        (c_write_var n t e) genv env locals
        s
        v_tt
        {| store := st'; heap := s.(heap); |}

  | builtin_alloc_ptr: forall e_size t e_init genv env locals s ptr hp' v_size v_init
                              (EVAL_SIZE: eval e_size env = Some (v_ofst v_size))
                              (EVAL_INIT: eval e_init env = Some v_init)
                              (WT: wt_value v_init t)
                              (ALLOC: Heap.alloc s.(heap) v_size (memval_of_value v_init) = Some (hp', ptr))
    , builtin
        (c_alloc_ptr e_size t e_init) genv env locals
        s
        (v_ptr ptr)
        {| store := s.(store); heap := hp'; |}
  | builtin_read_ptr: forall e_ptr t genv env locals s v_read v_ptr mv
                             (EVAL: eval e_ptr env = Some (Value.v_ptr v_ptr))
                             (LOOKUP: Heap.lookup s.(heap) v_ptr = Some mv)
                             (WT: wt_value v_read t)
                             (VMV: value_memval v_read mv)
    , builtin
        (c_read_ptr e_ptr t) genv env locals
        s
        v_read
        s
  | builtin_write_ptr: forall e_ptr t e_data genv env locals s hp' v_ptr v_data
                              (EVAL_ptr: eval e_ptr env = Some (Value.v_ptr v_ptr))
                              (EVAL_data: eval e_data env = Some v_data)
                              (MUTATE: Heap.mutate s.(heap) v_ptr (memval_of_value v_data) = Some hp')
                              (WT: wt_value v_data t)

    , builtin
        (c_write_ptr e_ptr t e_data) genv env locals
        s
        v_tt
        {| store := s.(store); heap := hp' |}
  | builtin_free_ptr: forall e_ptr genv env locals s hp' v_ptr
                             (EVAL: eval e_ptr env = Some (Value.v_ptr v_ptr))
                             (FREE: Heap.free s.(heap) v_ptr = Some hp')
    , builtin
        (c_free_ptr e_ptr) genv env locals
        s
        v_tt
        {| store := s.(store); heap := hp' |}

  | builtin_shift_fw_ptr: forall e_ptr e_shift genv env locals s v_ptr' v_ptr v_shift
                                 (EVAL_ptr: eval e_ptr env = Some (Value.v_ptr v_ptr))
                                 (EVAL_shift: eval e_shift env = Some (v_ofst v_shift))
                                 (SHIFT: Pointer.Shift v_ptr v_shift v_ptr')
                                 (WVALID_pre: Heap.Facts.WValid s.(heap) v_ptr)
                                 (WVALID_post: Heap.Facts.WValid s.(heap) v_ptr')
    , builtin
        (c_shift_fw_ptr e_ptr e_shift) genv env locals
        s
        (Value.v_ptr v_ptr')
        s
  | builtin_shift_bw_ptr: forall e_ptr e_shift genv env locals s v_ptr' v_ptr v_shift
                                 (EVAL_ptr: eval e_ptr env = Some (Value.v_ptr v_ptr))
                                 (EVAL_shift: eval e_shift env = Some (v_ofst v_shift))
                                 (SHIFT: Pointer.Shift v_ptr' v_shift v_ptr)
                                 (WVALID_pre: Heap.Facts.WValid s.(heap) v_ptr)
                                 (WVALID_post: Heap.Facts.WValid s.(heap) v_ptr')
    , builtin
        (c_shift_bw_ptr e_ptr e_shift) genv env locals
        s
        (Value.v_ptr v_ptr')
        s
  | builtin_eq_ptr: forall e_ptr_l e_ptr_r genv env locals s b v_ptr_l v_ptr_r
                           (EVAL_l: eval e_ptr_l env = Some (v_ptr v_ptr_l))
                           (EVAL_r: eval e_ptr_r env = Some (v_ptr v_ptr_r))
                           (WVALID_l: Heap.Facts.WValid s.(heap) v_ptr_l)
                           (WVALID_r: Heap.Facts.WValid s.(heap) v_ptr_r)
                           (CMP: Pointer.cmp v_ptr_l v_ptr_r = Some b)
    , builtin
        (c_ptr_eq e_ptr_l e_ptr_r) genv env locals
        s
        (v_bool b)
        s
  .

  Inductive step: genv -> state -> Events.trace -> state -> Prop :=
  | step_bind: forall ge f id_b t_b c_b c_c k env locals s,
      step
        ge
        (State f (c_bind id_b t_b c_b c_c) k env locals s)
        Events.E0
        (State f c_b (Kbind id_b c_c k) env locals s)
  | step_with_var: forall ge f t e_init c_next k env locals s v st' nm
                          (EVAL: eval e_init env = Some v)
                          (PUSH: Store.push s.(store) (memval_of_value v) = (st', nm))
    , step
        ge
        (State f (c_with_var t e_init c_next) k env locals s)
        Events.E0
        (State f c_next k env (locals++[nm]) {| store := st'; heap := s.(heap) |})

  | step_builtin_call_cont: forall ge f c k env locals s v s' s''
                                   (CALLK: is_call_cont k)
                                   (BUILTIN: builtin c ge env locals s v s')
                                   (POP_STACK: pop_stack locals s = Some s'')
    , step
        ge
        (State f c k env locals s)
        Events.E0
        (Returnstate v k s'')
  | step_builtin_seq_cont: forall ge f c k env locals s c_next k' env' s' v
                                  (RESOLVE: resolve_seq_cont k env v c_next env' k')
                                  (BUILTIN: builtin c ge env locals s v s')
    , step
        ge
        (State f c k env locals s)
        Events.E0
        (State f c_next k' env' locals s')

  | step_app: forall ge f id_f args k env locals s fd v_args b
                     (EVAL: map_opt (fun e => eval e env) args = Some v_args)
                     (FIND_SYMB: Globalenvs.Genv.find_symbol ge id_f = Some b)
                     (FIND_FUNC: Globalenvs.Genv.find_funct_ptr ge b = Some fd)
                     (SEQK: is_seq_cont k)
    , step
        ge
        (State f (c_app id_f args) k env locals s)
        Events.E0
        (Callstate fd v_args (Kcall f env locals k) s)
  | step_tailapp: forall ge f id_f args k env locals s fd v_args b
                         (EVAL: map_opt (fun e => eval e env) args = Some v_args)
                         (FIND_SYMB: Globalenvs.Genv.find_symbol ge id_f = Some b)
                         (FIND_FUNC: Globalenvs.Genv.find_funct_ptr ge b = Some fd)
                         (CALLK: is_call_cont k)
    , step
        ge
        (State f (c_app id_f args) k env locals s)
        Events.E0
        (Callstate fd v_args k s)

  | step_ifthenelse: forall ge f e_i c_t c_e k env locals s b
                            (EVAL: eval e_i env = Some (v_bool b))
    , step
        ge
        (State f (c_if e_i c_t c_e) k env locals s)
        Events.E0
        (State f (if b then c_t else c_e) k env locals s)

  | step_while: forall ge f c_cond c_body k env locals s
    , step
        ge
        (State f (c_while c_cond c_body) k env locals s)
        Events.E0
        (State f c_cond (Kloop1 c_cond c_body k) env locals s)

  | step_internal_function: forall ge f args k s env
                                   (WT_ARGS: Forall2T wt_value args (List.map snd f.(fn_params)))
                                   (SET_PARAMS: set_params f.(fn_params) args = env)
                                   (CALLK: is_call_cont k)
    , step
        ge
        (Callstate (AST.Internal f) args k s)
        Events.E0
        (State f f.(fn_body) k env [] s)
  | step_external_function: forall ge nm sig args k s
                                   (ToX_out: CCInj.type_of_xtype sig.(AST.sig_res) t_unit)
                                   (CALLK: is_call_cont k)
    , step
        ge
        (Callstate (AST.External (AST.EF_external nm sig)) args k s)
        Events.E0
        (Returnstate v_tt k s)

  | step_return_call_seq: forall ge v f env locals k s c_next k' env'
                                 (RESOLVE: resolve_seq_cont k env v c_next env' k')
    , step
        ge
        (Returnstate v (Kcall f env locals k) s)
        Events.E0
        (State f c_next k' env' locals s)
  .

  Definition semantics (p: program) :=
    Smallstep.Semantics step (initial_state p) final_state (Globalenvs.Genv.globalenv p).

  Definition step_star := Smallstep.star step.

End State.

Module Typing.

  Record wt_env (f: function) (ty_env: map_ctxt (type * bool)) (val_env: map_ctxt value): Type :=
    {
      wt_val_env: forall var_id t,
        List.In (var_id, t) (f.(fn_params) ++ f.(fn_temps)) ->
        { t &
          match Maps.PTree.get var_id val_env with
          | Some v => wt_value v t + (Maps.PTree.get var_id ty_env = Some (t, true))
          | None => Maps.PTree.get var_id ty_env = Some (t, false)
          end };
      wv_ty_env: forall var_id t b,
        Maps.PTree.get var_id ty_env = Some (t, b) ->
        (if b
         then { v & Maps.PTree.get var_id val_env = Some v & wt_value v t }
         else Maps.PTree.get var_id val_env = None)
        * List.In (var_id, t) (f.(fn_params) ++ f.(fn_temps));
    }.

  Inductive wt_cont_call[St]: ctxt Empty_set Empty_set fundef vardef -> @cont St -> type -> Type :=
  | wt_Kstop: forall ctx,
      wt_cont_call ctx Kstop t_nat
  | wt_Kcall: forall ctx f e locals k t ty_env
                     (Hwt_fn: wt_function ctx f)
                     (Hwt_env: wt_env f ty_env e)
                     (Hwt_cont: wt_cont (with_pure ty_env (with_stack (List.map (fun _ => tt) locals) ctx)) k t),
      wt_cont_call ctx (Kcall f e locals k) t

  with wt_cont[St]: ctxt (type * bool) unit fundef vardef -> @cont St -> type -> Type :=
  | wt_cont_Kbind: forall ctx id c k t_b t_c
                          (Hget_pure: get_pure id ctx = Some (t_b, false))
                          (Hwt_cmd: wt_cmd (set_pure id (t_b, true) ctx) c t_c)
                          (Hwt_cont: wt_cont ctx k t_c),
      wt_cont ctx (Kbind id c k) t_b
  | wt_cont_Kloop1: forall ctx c_cond c_body k
                           (Hwt_cond: wt_cmd ctx c_cond t_bool)
                           (Hwt_body: wt_cmd ctx c_body t_unit)
                           (Hwt_cont: wt_cont ctx k t_unit),
      wt_cont ctx (Kloop1 c_cond c_body k) t_bool
  | wt_cont_Kloop2: forall ctx c_cond c_body k
                           (Hwt_cond: wt_cmd ctx c_cond t_bool)
                           (Hwt_body: wt_cmd ctx c_body t_unit)
                           (Hwt_cont: wt_cont ctx k t_unit),
      wt_cont ctx (Kloop2 c_cond c_body k) t_unit
  | wt_cont_other: forall ctx k tret
                          (Hwt_cont_call: wt_cont_call (with_pure (Maps.PTree.empty _) (with_stack [] ctx)) k tret),
      wt_cont ctx k tret
  .

  Record wt_State {St: Store} {Hp: Heap} (f: function) (c: cmd) (k: cont)
    (e: map_ctxt value) (locals: list (@name St)) (s: Primitives.State St Hp)
    (ctx: ctxt (type * bool) unit fundef vardef) (t: type): Type :=
    {
      State_wt_function: wt_function (with_pure (Maps.PTree.empty _) (with_stack [] ctx)) f;
      State_wt_cmd: wt_cmd ctx c t;
      State_wt_cont: @wt_cont St ctx k t;
      State_wt_env: wt_env f ctx e;
      State_wt_stack: ctxt_stack ctx = List.map (fun _ => tt) locals;
    }.

  Inductive wt_state {St: Store} {Hp: Heap} (p: program): @state St Hp -> Type :=
  | wt_State_intro: forall f c k e locals s ctx t
                           (Hwt_State: wt_State f c k e locals s ctx t),
      wt_state p (State f c k e locals s)
  | wt_Callstate: forall f args k s sig ctx
                         (Hwt_fundef: wt_fundef (mk_glob_ctxt p) f)
                         (Hwt_args: wt_fundef_call args f)
                         (Hsig: funsig f sig)
                         (Hwt_cont: wt_cont ctx k sig.(sig_res)),
      wt_state p (Callstate f args k s)
  | wt_Returnstate: forall v k s ctx t
                           (Hwt_res: wt_value v t)
                           (Hwt_cont: wt_cont ctx k t),
      wt_state p (Returnstate v k s)
  .

  Lemma set_params_in_some_wt:
    forall (params: list (AST.ident * type)) (args: list value)
           (Hpsb: ListExt.SBinds params)
           (Hf2: ListExt.Forall2T wt_value args (List.map snd params))
           id t (HIn: In (id, t) params),
      exists v, Maps.PTree.get id (set_params params args) = Some v /\ wt_value v t.
  Proof.
    induction params as [|[id1 t1] params IH]; cbn; intros args Hpsb Hf2 id t HIn.
    - contradiction.
    - inversion Hf2 as [|v ? args' ? Hwtv Hf2_rest]; subst.
      destruct HIn as [Heq | HIn].
      + inversion Heq; subst id1 t1.
        exists v; split; [ apply Maps.PTree.gss | exact Hwtv ].
      + assert (Hne: id <> id1)
          by (eapply ListExt.SBinds_tl_neq with (a := id1) (b := t1) (a' := id) (b' := t);
              [ exact Hpsb | exact HIn ]).
        assert (Hsb': ListExt.SBinds params) by (inversion Hpsb; assumption).
        destruct (IH _ Hsb' Hf2_rest _ _ HIn) as [v' [Hget Hwt]].
        exists v'; split; [| exact Hwt ].
        rewrite Maps.PTree.gso by exact Hne; exact Hget.
  Qed.

  Lemma set_params_get_not_in:
    forall (params: list (AST.ident * type)) (args: list value) id
      (HNI: ~ In id (map fst params)),
      Maps.PTree.get id (set_params params args) = None.
  Proof.
    induction params as [|[id1 t1] params IH]; intros args id HNI.
    - destruct args; cbn; apply Maps.PTree.gempty.
    - destruct args as [|v args']; cbn; [apply Maps.PTree.gempty |].
      rewrite Maps.PTree.gso by (intros eq; subst; apply HNI; now left).
      apply IH. intros HIn; apply HNI; now right.
  Qed.

  Definition id_type_eq_dec : forall (x y: AST.ident * type), {x = y} + {x <> y}.
  Proof.
    intros [id1 t1] [id2 t2].
    destruct (Pos.eq_dec id1 id2);
      [destruct (type_eq_dec t1 t2);
       [ left; congruence | right; intros [=]; congruence ]
      | right; intros [=]; congruence ].
  Defined.

  Lemma wt_env_init
    (ctx: ctxt Empty_set Empty_set fundef vardef)
    (f: function) (args: list value)
    (Hwt_fn: wt_function ctx f)
    (Hwt_args: ListExt.Forall2T wt_value args (List.map snd f.(fn_params))) :
    wt_env f (ctxt_pure (mk_function_ctxt f.(fn_params) f.(fn_temps) ctx))
              (set_params f.(fn_params) args).
  Proof.
    pose proof (wt_fn_params_sbinds Hwt_fn) as Hpsb.
    pose proof (wt_fn_temps_sbinds Hwt_fn) as Htsb.
    pose proof (wt_fn_params_temps_distinct Hwt_fn) as Hdist.
    assert (Htemp_not_param: forall id t,
               In (id, t) f.(fn_temps) -> ~ In id (map fst f.(fn_params))).
    { intros id t HInT HInPfst.
      rewrite Forall_forall in Hdist.
      apply in_map_iff in HInPfst as [[ip tp] [Hfst HInp]]; cbn in Hfst; subst ip.
      apply (Hdist _ HInp).
      exists (id, t); split; [exact HInT | reflexivity]. }
    refine {|
      wt_val_env := _;
      wv_ty_env := _;
    |}.
    - (* wt_val_env *)
      intros id t HIn.
      exists t.
      destruct (in_dec id_type_eq_dec (id, t) f.(fn_params)) as [HInP | HnotP].
      + (* param case *)
        destruct (Maps.PTree.get id (set_params f.(fn_params) args)) as [v|] eqn:E.
        * left.
          destruct (set_params_in_some_wt _ _ Hpsb Hwt_args _ _ HInP) as [v' [Hget Hwt]].
          rewrite Hget in E; inversion E; subst; exact Hwt.
        * exfalso.
          destruct (set_params_in_some_wt _ _ Hpsb Hwt_args _ _ HInP) as [v [Hget _]].
          rewrite Hget in E; discriminate.
      + (* not in params: must be in temps *)
        assert (HInT: In (id, t) f.(fn_temps)).
        { apply in_app_or in HIn as [|]; [contradiction | assumption]. }
        rewrite (set_params_get_not_in _ args id (Htemp_not_param _ _ HInT)).
        exact (Facts.mk_function_ctxt_pure_get_temp _ _ _ Hpsb Htsb Hdist _ _ HInT).
    - (* wv_ty_env *)
      intros id t b Hget.
      destruct b.
      + (* b = true: id is a param *)
        assert (HInP: In (id, t) f.(fn_params)).
        { pose proof (Facts.mk_function_ctxt_pure_get_inv _ _ _ _ _ _ Hget) as Hcase.
          destruct Hcase as [[_ HInP] | [Hbf _]]; [exact HInP | discriminate]. }
        split; [| apply in_or_app; now left ].
        destruct (Maps.PTree.get id (set_params f.(fn_params) args)) as [v|] eqn:E.
        * exists v; [reflexivity |].
          destruct (set_params_in_some_wt _ _ Hpsb Hwt_args _ _ HInP) as [v' [Hget' Hwt]].
          rewrite Hget' in E; inversion E; subst; exact Hwt.
        * exfalso.
          destruct (set_params_in_some_wt _ _ Hpsb Hwt_args _ _ HInP) as [v [Hget' _]].
          rewrite Hget' in E; discriminate.
      + (* b = false: id is a temp *)
        assert (HInT: In (id, t) f.(fn_temps)).
        { pose proof (Facts.mk_function_ctxt_pure_get_inv _ _ _ _ _ _ Hget) as Hcase.
          destruct Hcase as [[Hbt _] | [_ HInT]]; [discriminate | exact HInT]. }
        split; [| apply in_or_app; now right ].
        apply set_params_get_not_in.
        exact (Htemp_not_param _ _ HInT).
  Defined.

End Typing.

Module Facts.

  Lemma resolve_seq_cont_fun [St k env v c' env' k' c'' env'' k'']
    (RESOLVE1: @resolve_seq_cont St k env v c' env' k')
    (RESOLVE2: @resolve_seq_cont St k env v c'' env'' k'')
    : c'' = c' /\ env'' = env' /\ k'' = k'.
  Proof.
    inversion RESOLVE1; subst;
      inversion RESOLVE2; subst;
      auto.
  Qed.

End Facts.

From GallinaC.Imp Require Import Model.
From GallinaC.Utils Require Import OptionExt.

Ltac guess_heap_substate :=
  match goal with
  | |- Algebra.Substate
         (Heap.one {| Pointer.Addr.block := ?b; Pointer.Addr.offset := ?o |} ?v)
         {| list_heap := ?bindings; alloc := ?a; |}
    =>
      exists ({| list_heap :=
                  ListExt.replace_nth b (ListExt.replace_nth (N.to_nat o) None (List.nth b bindings [])) bindings;
                  alloc := a|});
      reflexivity
  end.

Ltac guess_wvalid :=
  first
    [ left; cbn -[Heap.one]; eexists;
      match goal with
      | |- exists v : Memval.memval,
          Pointer.Pointer.References (Some ({| Pointer.Addr.block := ?b; Pointer.Addr.offset := ?o |}, _)) _
          /\ Algebra.Substate (Heap.one _ v) {| list_heap := ?bindings; alloc := _ |}
        =>
          exists (default Memval.VUnit (List.nth (N.to_nat o) (List.nth b bindings []) None));
          cbn -[Heap.one]
      end;
      split; [ now constructor | now cbn -[Heap.one]; guess_heap_substate ]
    | right; right; reflexivity
    ].

Ltac builtin_step :=
  first
    [ eapply builtin_ret; reflexivity
    | eapply builtin_read_var; [ reflexivity | reflexivity | now constructor ]
    | eapply builtin_write_var; [ reflexivity | reflexivity | reflexivity | now constructor ]
    | eapply builtin_alloc_ptr; [ reflexivity | reflexivity | now constructor | reflexivity ]
    | eapply builtin_read_ptr; [ reflexivity | reflexivity | now constructor | now constructor ]
    | eapply builtin_write_ptr; now constructor
    | eapply builtin_shift_fw_ptr; [ reflexivity | reflexivity | now constructor | now guess_wvalid | now guess_wvalid ]
    | eapply builtin_eq_ptr; [ reflexivity | reflexivity | guess_wvalid | guess_wvalid | reflexivity ]
    ].

Ltac one_step :=
  first
    [ apply Smallstep.star_refl
    | eapply Smallstep.star_step with (t1 := Events.E0) (t2 := Events.E0);
      [ first
          [ apply step_bind
          | eapply step_with_var; [ reflexivity | reflexivity ]
          | eapply step_builtin_call_cont; [ now constructor | builtin_step | reflexivity ]
          | eapply step_builtin_seq_cont; [ now constructor | builtin_step ]
          | eapply step_app ; [ reflexivity | reflexivity | reflexivity | now constructor ]
          | eapply step_while
          | eapply step_internal_function; [ now repeat constructor | reflexivity | now constructor ]
          | eapply step_external_function; [ now repeat constructor | now repeat constructor ]
          | eapply step_return_call_seq; now constructor
          ]
      | auto
      | reflexivity]
    ];
  cbn -[Globalenvs.Genv.globalenv].
