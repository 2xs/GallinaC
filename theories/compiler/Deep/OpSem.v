From Stdlib Require Import ZArith.

From compcert.common Require Events Smallstep.

From Utils Require Import ListExt.
From Imp Require Import Heap Store Primitives Intops Uint32 Uintptr.
From Compiler.Common Require Import Types Ctxt Value Expr.
From Compiler.Deep Require Import Cmd Prog Typing.

Section State.

  Context [St: Store].
  Context [Hp: Heap].

  (* C evaluation under the CompCert model is CPS *)
  (* Hence, at any point in time, only one command (statement) is under consideration at a time *)
  (* Control-flow operations simply pushes values onto a continuation stack *)
  (* When a command terminates, it looks at the continuation to determine what to do with the result *)
  Inductive cont: Type :=
  (* 1. To return from the program execution *)
  | Kstop: cont
  (* 2. To bind the result in a temporary variable *)
  | Kbind:
    forall (id_b: AST.ident)     (* identifier to bind *)
           (c: cmd)              (* command to execute next *)
           (k: cont)             (* then continue with k *)
    , cont
  (* 3. To evaluate the condition of a while loop *)
  | Kloop1:
    forall (c_cond: cmd)         (* command of the condition *)
           (c_body: cmd)         (* command of the body *)
           (k: cont)             (* when the loop terminates, continue with k *)
    , cont
  (* 4. To evaluate the body of a while loop *)
  | Kloop2:
    forall (c_cond: cmd)         (* command of the condition *)
           (c_body: cmd)         (* command of the body *)
           (k: cont)             (* when the loop terminates, continue with k *)
    , cont
  (* 5. To return from a sub-function call *)
  | Kcall:
    forall (fn: function)        (* calling function f *)
           (e: map_ctxt value)   (* execution environment of f *)
           (sp: list (@name St)) (* live local variables of f *)
           (k: cont)             (* then continue with k *)
    , cont
  .

  Inductive is_call_cont: cont -> Prop :=
  | call_cont_Kstop: is_call_cont Kstop
  | call_cont_Kcall: forall fn e sp k, is_call_cont (Kcall fn e sp k)
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
        (Kloop1 c_cond c_body k)
        env
        v_tt
        c_cond
        env
        (Kloop2 c_cond c_body k)
  .

  Inductive state: Type :=
  | State:                       (* Execution within a function         *)
    forall (fn: function)        (* currently executing function        *)
           (c: cmd)              (* command under consideration         *)
           (k: cont)             (* its continuation -- what to do next *)
           (e: map_ctxt value)   (* current loval environment           *)
           (sp: list (@name St)) (* live local variables                *)
           (s: State St Hp)      (* current heap and store states       *)
    , state
  | Callstate:                   (* Invocation of a function *)
    forall (f: fundef)           (* function to invoke       *)
           (arg: list value)     (* arguments provided by the caller *)
           (k: cont)             (* what to do next *)
           (s: State St Hp)      (* current heap and store states *)
    , state
  | Returnstate:                 (* Return from a function *)
    forall (v: value)            (* Return value *)
           (k: cont)             (* what to do next *)
           (s: State St Hp)      (* current heap and store states *)
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

  (* "Primitive" operations *)
  Inductive builtin: cmd -> genv -> map_ctxt value -> list (@name St) -> Primitives.State St Hp -> value -> Primitives.State St Hp -> Prop :=
  | builtin_ret: forall e genv env sp s v
                       (EVAL: eval e env = Some v)
    , builtin
        (c_ret e) genv env sp s v s

  | builtin_read_var: forall n t genv env sp s v nm
                             (DEREF: List.nth_error sp n = Some nm)
                             (LOOKUP: Store.lookup s.(store) nm = Some (memval_of_value v))
    , builtin
        (c_read_var n t) genv env sp
        s
        v
        s
  | builtin_write_var: forall n t e genv env sp s st' v nm
                              (EVAL: eval e env = Some v)
                              (DEREF: List.nth_error sp n = Some nm)
                              (MUTATE: Store.mutate s.(store) nm (memval_of_value v) = Some st')
                              (WT: wt_value v t)
    , builtin
        (c_write_var n t e) genv env sp
        s
        v_tt
        {| store := st'; heap := s.(heap); |}

  | builtin_alloc_ptr: forall e_size t e_init genv env sp s ptr hp' v_size v_init
                              (EVAL_SIZE: eval e_size env = Some (v_ofst v_size))
                              (EVAL_INIT: eval e_init env = Some v_init)
                              (WT: wt_value v_init t)
                              (ALLOC: Heap.alloc s.(heap) v_size (memval_of_value v_init) = Some (hp', ptr))
    , builtin
        (c_alloc_ptr e_size t e_init) genv env sp
        s
        (v_ptr ptr)
        {| store := s.(store); heap := hp'; |}
  | builtin_read_ptr: forall e_ptr t genv env sp s v_read v_ptr
                             (EVAL: eval e_ptr env = Some (Value.v_ptr v_ptr))
                             (LOOKUP: Heap.lookup s.(heap) v_ptr = Some (memval_of_value v_read))
                             (WT: wt_value v_read t)
    , builtin
        (c_read_ptr e_ptr t) genv env sp
        s
        v_read
        s
  | builtin_write_ptr: forall e_ptr t e_data genv env sp s hp' v_ptr v_data
                              (EVAL_ptr: eval e_ptr env = Some (Value.v_ptr v_ptr))
                              (EVAL_data: eval e_data env = Some v_data)
                              (MUTATE: Heap.mutate s.(heap) v_ptr (memval_of_value v_data) = Some hp')
                              (WT: wt_value v_data t)

    , builtin
        (c_write_ptr e_ptr t e_data) genv env sp
        s
        v_tt
        {| store := s.(store); heap := hp' |}
  | builtin_free_ptr: forall e_ptr genv env sp s hp' v_ptr
                             (EVAL: eval e_ptr env = Some (Value.v_ptr v_ptr))
                             (FREE: Heap.free s.(heap) v_ptr = Some hp')
    , builtin
        (c_free_ptr e_ptr) genv env sp
        s
        v_tt
        {| store := s.(store); heap := hp' |}

  | builtin_shift_fw_ptr: forall e_ptr e_shift genv env sp s v_ptr' v_ptr v_shift
                                 (EVAL_ptr: eval e_ptr env = Some (Value.v_ptr v_ptr))
                                 (EVAL_shift: eval e_shift env = Some (v_ofst v_shift))
                                 (SHIFT: Pointer.Shift v_ptr v_shift v_ptr')
                                 (WVALID_pre: Heap.Facts.WValid s.(heap) v_ptr)
                                 (WVALID_post: Heap.Facts.WValid s.(heap) v_ptr')
    , builtin
        (c_shift_fw_ptr e_ptr e_shift) genv env sp
        s
        (Value.v_ptr v_ptr')
        s
  | builtin_shift_bw_ptr: forall e_ptr e_shift genv env sp s v_ptr' v_ptr v_shift
                                 (EVAL_ptr: eval e_ptr env = Some (Value.v_ptr v_ptr))
                                 (EVAL_shift: eval e_shift env = Some (v_ofst v_shift))
                                 (SHIFT: Pointer.Shift v_ptr' v_shift v_ptr)
                                 (WVALID_pre: Heap.Facts.WValid s.(heap) v_ptr)
                                 (WVALID_post: Heap.Facts.WValid s.(heap) v_ptr')
    , builtin
        (c_shift_bw_ptr e_ptr e_shift) genv env sp
        s
        (Value.v_ptr v_ptr')
        s
  | builtin_eq_ptr: forall e_ptr_l e_ptr_r genv env sp s b v_ptr_l v_ptr_r
                           (EVAL_l: eval e_ptr_l env = Some (v_ptr v_ptr_l))
                           (EVAL_r: eval e_ptr_r env = Some (v_ptr v_ptr_r))
                           (WVALID_l: Heap.Facts.WValid s.(heap) v_ptr_l)
                           (WVALID_r: Heap.Facts.WValid s.(heap) v_ptr_r)
                           (CMP: Pointer.cmp v_ptr_l v_ptr_r = Some b)
    , builtin
        (c_ptr_eq e_ptr_l e_ptr_r) genv env sp
        s
        (v_bool b)
        s
  .

  Inductive step: genv -> state -> Events.trace -> state -> Prop :=
  | step_bind: forall ge f id_b t_b c_b c_c k env sp s,
      step
        ge
        (State f (c_bind id_b t_b c_b c_c) k env sp s)
        Events.E0
        (State f c_b (Kbind id_b c_c k) env sp s)
  | step_with_var: forall ge f t e_init c_next k env sp s v st' nm
                          (EVAL: eval e_init env = Some v)
                          (PUSH: Store.push s.(store) (memval_of_value v) = (st', nm))
    , step
        ge
        (State f (c_with_var t e_init c_next) k env sp s)
        Events.E0
        (State f c_next k env (sp++[nm]) {| store := st'; heap := s.(heap) |})

  | step_builtin_call_cont: forall ge f c k env sp s v s'
                                   (CALLK: is_call_cont k)
                                   (BUILTIN: builtin c ge env sp s v s')
    , step
        ge
        (State f c k env sp s)
        Events.E0
        (Returnstate v k s')
  | step_builtin_seq_cont: forall ge f c k env sp s c_next k' env' s' v
                                  (RESOLVE: resolve_seq_cont k env v c_next env' k')
                                  (BUILTIN: builtin c ge env sp s v s')
    , step
        ge
        (State f c k env sp s)
        Events.E0
        (State f c_next k' env' sp s')

  | step_app: forall ge f id_f args k env sp s fd v_args b
                     (EVAL: map_opt (fun e => eval e env) args = Some v_args)
                     (FIND_SYMB: Globalenvs.Genv.find_symbol ge id_f = Some b)
                     (FIND_FUNC: Globalenvs.Genv.find_funct_ptr ge b = Some fd)
                     (SEQK: is_seq_cont k)
    , step
        ge
        (State f (c_app id_f args) k env sp s)
        Events.E0
        (Callstate fd v_args (Kcall f env sp k) s)
  | step_tailapp: forall ge f id_f args k env sp s fd v_args b
                         (EVAL: map_opt (fun e => eval e env) args = Some v_args)
                         (FIND_SYMB: Globalenvs.Genv.find_symbol ge id_f = Some b)
                         (FIND_FUNC: Globalenvs.Genv.find_funct_ptr ge b = Some fd)
                         (CALLK: is_call_cont k)
    , step
        ge
        (State f (c_app id_f args) k env sp s)
        Events.E0
        (Callstate fd v_args k s)

  | step_ifthenelse: forall ge f e_i c_t c_e k env sp s b
                            (EVAL: eval e_i env = Some (v_bool b))
    , step
        ge
        (State f (c_if e_i c_t c_e) k env sp s)
        Events.E0
        (State f (if b then c_t else c_e) k env sp s)

  | step_while: forall ge f c_cond c_body k env sp s
    , step
        ge
        (State f (c_while c_cond c_body) k env sp s)
        Events.E0
        (State f c_cond (Kloop1 c_cond c_body k) env sp s)

  | step_internal_function: forall ge f args k s env
                                   (WT_ARGS: Forall2T wt_value args (List.map snd f.(fn_params)))
                                   (SET_PARAMS: set_params f.(fn_params) args = env)
                                   (CALLK: is_call_cont k)
    , step
        ge
        (Callstate (AST.Internal f) args k s)
        Events.E0
        (State f f.(fn_body) k env [] s)

  | step_return_call_seq: forall ge v f env sp k s c_next k' env'
                                 (RESOLVE: resolve_seq_cont k env v c_next env' k')
    , step
        ge
        (Returnstate v (Kcall f env sp k) s)
        Events.E0
        (State f c_next k' env' sp s)
  .

  Definition semantics (p: program) :=
    Smallstep.Semantics step (initial_state p) final_state (Globalenvs.Genv.globalenv p).

  Definition step_star := Smallstep.star step.

End State.

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
