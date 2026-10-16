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

From Stdlib Require Import ZArith.

From compcert.common Require Events Smallstep.

From GallinaC.Utils Require Import OptionExt ListExt CompCertExt PosExt ProdExt.
From GallinaC.Imp Require Import Heap Store Storable Primitives Intops Uint32 Uintptr.
From GallinaC.Imp Require Import State.
From GallinaC.Compiler.Common Require Import Types Ctxt Value Expr.
From GallinaC.Compiler.Deep Require Import Cmd Prog Typing.

Local Open Scope separation_scope.

Section State.

  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).

  (* Deep GallinaC matches shallow GallinaC closely due to the proof
  requirements in Agree.v. Hence, it must mimic how monadic computations pop
  their environments regularly.

   When execution [do x <- (do y <- a; b); c], [y] leaves the scope upon
   terminating the evaluation of [b]. Thus, deep GallinaC must do similarly.

   Two kinds of scopes may needed to be poped: [bind] and [with_var] (store)
   bindings. As the former are stored in a [PTree.t], the scope marker must
   track which has to be removed. On the other hand, as store variables are
   tracked in a stack, there is no need to track their names for scope purposes.

   *)
  Inductive scope_kind: Type :=
  | scope_bind: forall (id: AST.ident), scope_kind
  | scope_store: scope_kind
  .

  (* C evaluation under the CompCert model is CPS *)
  (* Hence, at any point in time, only one command (statement) is under consideration at a time *)
  (* Control-flow operations simply pushes values onto a continuation stack *)
  (* When a command terminates, it looks at the continuation to determine what to do with the result *)
  Inductive cont: Type :=
  (* 1. To return from the program execution *)
  | Kstop: cont
  (* 2. To bind the result in a temporary variable *)
  | Kbind:
    forall (b_id: AST.ident)            (* identifier to bind *)
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
           (e: Maps.PTree.t (value Pt))      (* execution environment of f *)
           (locals: list Nm)    (* live local variables of f *)
           (k: cont)                    (* then continue with k *)
    , cont
  (* 6. To exit a scope] *)
  | Kscope:
    forall (sx: scope_kind)             (* what kind of scope we exit *)
           (k: cont)                    (* then continue with k *)
    , cont
  .

  Inductive is_call_cont: cont -> Prop :=
  | call_cont_Kstop: is_call_cont Kstop
  | call_cont_Kcall: forall fn e locals k, is_call_cont (Kcall fn e locals k)
  .

  (* Upon exiting a function, there will likely be some trailing [Kscope]
  continuation which must be popped. In essence, this corresponds to the
  function epilogue popped the local stack frame.

   For an example, see [do x <- a; do y <- b; ret (x + y)]. Here, when the [ret]
   is encountered, there are still [Kscope] continuations for [x] and [y] before
   reaching a [Kcall]. The evaluation rule for function return must hence, first
   pop these continuations before performing function return.

   *)
  Inductive resolve_call_cont: cont -> cont -> Prop :=
  | resolve_call_here: forall k (CALLK: is_call_cont k), resolve_call_cont k k
  | resolve_call_Kscope: forall sx k k' (RES: resolve_call_cont k k'),
      resolve_call_cont (Kscope sx k) k'
  .

  Inductive is_seq_cont: cont -> Prop :=
  | call_cont_Kbind: forall id_b c_next k, is_seq_cont (Kbind id_b c_next k)
  | call_cont_Kloop1: forall c_cond c_body k, is_seq_cont (Kloop1 c_cond c_body k)
  | call_cont_Kloop2: forall c_cond c_body k, is_seq_cont (Kloop2 c_cond c_body k)
  | call_cont_Kscope: forall sx k, is_seq_cont (Kscope sx k)
  .

  (* [resolve_seq_cont k env v c_next env' k' n] considers continuation [k],
  temporary environment [env] and the last's command output value [v] and
  determinates the next command [c_next], the new temporary environment [env'],
  the new continuation [k'] and the number of store pops [n].

  For [Kbind], simply unwrap the continuation, set the bind's target to [v] and
  continue with the [Kbind]'s sub-continuation wrapped in a [Kscope].

  For [Kloop1]/[Kloop2], simply expect the right kind of value and either break
  or continue with the other continuation of the pair.

  For [Kscope], rewrite the pop the appropriate environment and recurse.

   *)
  Inductive resolve_seq_cont: cont -> Maps.PTree.t (value Pt) -> value Pt -> cmd -> Maps.PTree.t (value Pt) -> cont -> nat -> Prop :=
  | resolve_seq_Kbind: forall id_b c_next k env v,
      resolve_seq_cont
        (Kbind id_b c_next k)
        env
        v
        c_next
        (Maps.PTree.set id_b v env)
        (Kscope (scope_bind id_b) k)
        0
  | resolve_seq_Kloop1: forall c_cond c_body k env b,
      resolve_seq_cont
        (Kloop1 c_cond c_body k)
        env
        (v_bool b)
        (if b then c_body else (c_ret e_tt))
        env
        (if b then Kloop2 c_cond c_body k else k)
        0
  | resolve_seq_Kloop2: forall c_cond c_body k env,
      resolve_seq_cont
        (Kloop2 c_cond c_body k)
        env
        v_tt
        c_cond
        env
        (Kloop1 c_cond c_body k)
        0
  | resolve_seq_Kscope_unbind: forall id k env v c' env' k' n
      (RES: resolve_seq_cont k (Maps.PTree.remove id env) v c' env' k' n),
      resolve_seq_cont (Kscope (scope_bind id) k) env v c' env' k' n
  | resolve_seq_Kscope_pop: forall k env v c' env' k' n
      (RES: resolve_seq_cont k env v c' env' k' n),
      resolve_seq_cont (Kscope scope_store k) env v c' env' k' (S n)
  .

  Inductive state: Type :=
  | State:                              (* Execution within a function         *)
    forall (fn: function)               (* currently executing function        *)
           (c: cmd)                     (* command under consideration         *)
           (k: cont)                    (* its continuation -- what to do next *)
           (e: Maps.PTree.t (value Pt))          (* current loval environment           *)
           (locals: list Nm)    (* live local variables                *)
           (s: Sm)             (* current heap and store states       *)
    , state
  | Callstate:                          (* Invocation of a function *)
    forall (f: fundef)                  (* function to invoke       *)
           (arg: list (value Pt))            (* arguments provided by the caller *)
           (k: cont)                    (* what to do next *)
           (s: Sm)             (* current heap and store states *)
    , state
  | Returnstate:                        (* Return from a function *)
    forall (v: value Pt)                   (* Return value *)
           (k: cont)                    (* what to do next *)
           (s: Sm)             (* current heap and store states *)
    , state
  .

  Definition state_of_state (s: state): Sm :=
    match s with
    | State _ _ _ _ _ s => s
    | Callstate _ _ _ s => s
    | Returnstate _ _ s => s
    end.

  Definition alloc_global (s: Sm) (g: globdef): option (Sm) :=
    match g with
    | AST.Gfun _ => Some s
    | AST.Gvar _ => None
    end.

  Fixpoint alloc_globals (s: Sm) (gl: list (AST.ident * globdef)): option (Sm) :=
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
        match alloc_globals emp_state p.(prog_defs) with
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
    , initial_state p (Callstate f [] Kstop emp_state)
  .

  Inductive final_state: state -> Integers.int -> Prop :=
  | final_state_intro: forall r s,
      final_state (Returnstate (v_nat r) Kstop s) (Integers.Int.repr (Z.of_nat r))
  .

  Fixpoint set_params [A: Type] (params: list (AST.ident * A)) (inits: list (value Pt)): Maps.PTree.t (value Pt) :=
    match params, inits with
    | [], [] => Maps.PTree.Empty
    | (id, _)::params, v::inits => Maps.PTree.set id v (set_params params inits)
    | _, _ => Maps.PTree.Empty
    end.

  Definition pop_stack (locals: list Nm) (s: Sm): option Sm :=
    state_pop_n (BinNat.N.of_nat (length locals)) s.

  (* [pop_stack_n n s] pops n stack slots from [s]'s store *)
  Definition pop_stack_n (n: nat) (s: Sm): option Sm :=
    state_pop_n (BinNat.N.of_nat n) s.

  (* "Primitive" operations *)
  Inductive builtin: cmd -> genv -> Maps.PTree.t (value Pt) -> list Nm -> Sm -> value Pt -> Sm -> Prop :=
  | builtin_ret: forall e genv env locals s v
                        (EVAL: eval e env = Some v)
    , builtin
        (c_ret e) genv env locals s v s

  | builtin_read_var: forall n t genv env locals s v mv nm
                             (DEREF: List.nth_error locals n = Some nm)
                             (LOOKUP: lookup (store s) nm = Some mv)
                             (VMV: decode mv = Some v)
                             (WT: wt_value v t)
    , builtin
        (c_read_var n t) genv env locals
        s
        v
        s
  | builtin_write_var: forall n t e genv env locals s st' v nm
                              (EVAL: eval e env = Some v)
                              (DEREF: List.nth_error locals n = Some nm)
                              (MUTATE: mutate (store s) nm (encode v) = Some st')
                              (WT: wt_value v t)
    , builtin
        (c_write_var n t e) genv env locals
        s
        v_tt
        (state_mutate_store s MUTATE)

  | builtin_alloc_ptr: forall e_size t e_init genv env locals s ptr hp' alc' v_size v_init
                              (EVAL_SIZE: eval e_size env = Some (v_ofst v_size))
                              (EVAL_INIT: eval e_init env = Some v_init)
                              (WT: wt_value v_init t)
                              (BND: (v_size <= alloc_max_size)%N)
                              (ALLOC: alloc (heap s) (alc s) v_size (encode v_init) = Some (hp', alc', ptr))
    , builtin
        (c_alloc_ptr e_size t e_init) genv env locals
        s
        (v_ptr ptr)
        (state_alloc s ALLOC)
  | builtin_read_ptr: forall e_ptr t genv env locals s v_read v_ptr mv
                             (EVAL: eval e_ptr env = Some (Value.v_ptr v_ptr))
                             (LOOKUP: lookup (heap s) v_ptr = Some mv)
                             (WT: wt_value v_read t)
                             (VMV: decode mv = Some v_read)
    , builtin
        (c_read_ptr e_ptr t) genv env locals
        s
        v_read
        s
  | builtin_write_ptr: forall e_ptr t e_data genv env locals s hp' v_ptr v_data
                              (EVAL_ptr: eval e_ptr env = Some (Value.v_ptr v_ptr))
                              (EVAL_data: eval e_data env = Some v_data)
                              (MUTATE: mutate (heap s) v_ptr (encode v_data) = Some hp')
                              (WT: wt_value v_data t)

    , builtin
        (c_write_ptr e_ptr t e_data) genv env locals
        s
        v_tt
        (state_mutate_heap s MUTATE)
  | builtin_free_ptr: forall e_ptr genv env locals s hp' v_ptr
                             (EVAL: eval e_ptr env = Some (Value.v_ptr v_ptr))
                             (FREE: free (heap s) v_ptr = Some hp')
    , builtin
        (c_free_ptr e_ptr) genv env locals
        s
        v_tt
        (state_free s FREE)

  | builtin_shift_fw_ptr: forall e_ptr e_shift genv env locals s v_ptr' v_ptr v_shift
                                 (EVAL_ptr: eval e_ptr env = Some (Value.v_ptr v_ptr))
                                 (EVAL_shift: eval e_shift env = Some (v_ofst v_shift))
                                 (SHIFT: ptr_shift_fw v_ptr v_shift = Some v_ptr')
                                 (WVALID_pre: WValid (heap s) v_ptr)
                                 (WVALID_post: WValid (heap s) v_ptr')
    , builtin
        (c_shift_fw_ptr e_ptr e_shift) genv env locals
        s
        (Value.v_ptr v_ptr')
        s
  | builtin_shift_bw_ptr: forall e_ptr e_shift genv env locals s v_ptr' v_ptr v_shift
                                 (EVAL_ptr: eval e_ptr env = Some (Value.v_ptr v_ptr))
                                 (EVAL_shift: eval e_shift env = Some (v_ofst v_shift))
                                 (SHIFT: ptr_shift_bw v_ptr v_shift = Some v_ptr')
                                 (WVALID_pre: WValid (heap s) v_ptr)
                                 (WVALID_post: WValid (heap s) v_ptr')
    , builtin
        (c_shift_bw_ptr e_ptr e_shift) genv env locals
        s
        (Value.v_ptr v_ptr')
        s
  | builtin_eq_ptr: forall e_ptr_l e_ptr_r genv env locals s b v_ptr_l v_ptr_r
                           (EVAL_l: eval e_ptr_l env = Some (v_ptr v_ptr_l))
                           (EVAL_r: eval e_ptr_r env = Some (v_ptr v_ptr_r))
                           (CMPVALID: CmpValid (heap s) v_ptr_l v_ptr_r)
                           (CMP: cmp v_ptr_l v_ptr_r = Some b)
    , builtin
        (c_ptr_eq e_ptr_l e_ptr_r) genv env locals
        s
        (v_bool b)
        s
  | builtin_div: forall e_l e_r genv env locals s l r q
                        (EVAL_l: eval e_l env = Some (v_nat l))
                        (EVAL_r: eval e_r env = Some (v_nat r))
                        (DIV: Unsigned.div l r s = Some (Monad.Success (q, s)))
    , builtin
        (c_div e_l e_r) genv env locals
        s
        (v_nat q)
        s
  | builtin_mod: forall e_l e_r genv env locals s l r q
                        (EVAL_l: eval e_l env = Some (v_nat l))
                        (EVAL_r: eval e_r env = Some (v_nat r))
                        (MDL: Unsigned.mdl l r s = Some (Monad.Success (q, s)))
    , builtin
        (c_mod e_l e_r) genv env locals
        s
        (v_nat q)
        s
  .

  Inductive step: genv -> state -> Events.trace -> state -> Prop :=
  | step_bind: forall ge f id_b t_b c_b c_c k env locals s,
      step
        ge
        (State f (c_bind id_b t_b c_b c_c) k env locals s)
        Events.E0
        (State f c_b (Kbind id_b c_c k) env locals s)
  | step_with_var: forall ge f t e_init c_next k env locals s v st' sg' nm
                          (EVAL: eval e_init env = Some v)
                          (PUSH: push (store s) (scnt s) (encode v) = Some (st', sg', nm))
    , step
        ge
        (State f (c_with_var t e_init c_next) k env locals s)
        Events.E0
        (State f c_next (Kscope scope_store k) env (locals++[nm])
           (state_push s PUSH))

  | step_builtin_call_cont: forall ge f c k k0 env locals s v s' s''
                                   (CALLK: resolve_call_cont k k0)
                                   (BUILTIN: builtin c ge env locals s v s')
                                   (POP_STACK: pop_stack locals s' = Some s'')
    , step
        ge
        (State f c k env locals s)
        Events.E0
        (Returnstate v k0 s'')
  | step_builtin_seq_cont: forall ge f c k env locals s c_next k' env' s' s'' v n
                                  (RESOLVE: resolve_seq_cont k env v c_next env' k' n)
                                  (BUILTIN: builtin c ge env locals s v s')
                                  (POPS: pop_stack_n n s' = Some s'')
    , step
        ge
        (State f c k env locals s)
        Events.E0
        (State f c_next k' env' (removelast_n n locals) s'')

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
                                   (WT_ARGS: Forall2 (wt_value (Pt := Pt)) args (List.map snd f.(fn_params)))
                                   (* NOTE Unlike C, we don't need to set the locals/temporary variables because wt_expr implies read after write *)
                                   (SET_PARAMS: set_params f.(fn_params) args = env)
                                   (CALLK: is_call_cont k)
    , step
        ge
        (Callstate (AST.Internal f) args k s)
        Events.E0
        (State f f.(fn_body) k env [] s)
  | step_return_call_seq: forall ge v f env locals k s s' c_next k' env' n
                                 (RESOLVE: resolve_seq_cont k env v c_next env' k' n)
                                 (POPS: pop_stack_n n s = Some s')
    , step
        ge
        (Returnstate v (Kcall f env locals k) s)
        Events.E0
        (State f c_next k' env' (removelast_n n locals) s')
  .

  Definition semantics (p: program) :=
    Smallstep.Semantics step (initial_state p) final_state (Globalenvs.Genv.globalenv p).

  Definition step_star := Smallstep.star step.

End State.

Module Typing.

Section Wt.

  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).

  Record wt_env (f: function) (ty_env: Maps.PTree.t (type * bool)) (val_env: Maps.PTree.t (value Pt)): Prop :=
    {
      wt_val_env: forall var_id t,
        List.In (var_id, t) (f.(fn_params) ++ f.(fn_temps)) ->
        Maps.PTree.get var_id ty_env =
          Some (t, match Maps.PTree.get var_id val_env with Some _ => true | None => false end)
        /\ (forall v, Maps.PTree.get var_id val_env = Some v -> wt_value v t);
      wv_ty_env: forall var_id t b,
        Maps.PTree.get var_id ty_env = Some (t, b) ->
        (if b
         then exists2 v, Maps.PTree.get var_id val_env = Some v & wt_value v t
         else Maps.PTree.get var_id val_env = None)
        /\ List.In (var_id, t) (f.(fn_params) ++ f.(fn_temps));
    }.

  (* For typing and value environments which "agree", evaluation of well-typed
  terms yields a value with the correct type. *)
  Lemma eval_preserves_wt_env f ty_env val_env (WTenv: wt_env f ty_env val_env)
    e t v (WTe: wt_expr ty_env e t) (EVAL: eval e val_env = Some v) :
    wt_value v t.
  Proof using Type.
    eapply (Expr.Facts.eval_preservation WTe); [| exact EVAL].
    intros id t' GET.
    destruct (wv_ty_env _ _ _ WTenv id t' true GET) as [[v' GET' WTV'] _].
    exists v'; assumption.
  Qed.

  (* Same as [eval_preserves_wt_env], but for evaluations of argument lists used by [c_app]. *)
  Lemma eval_list_preserves_wt_env f ty_env val_env (WT: wt_env f ty_env val_env)
    args ts v_args (WTargs: Forall2 (wt_expr ty_env) args ts)
    (EVAL: map_opt (fun e => eval e val_env) args = Some v_args) :
    Forall2 (wt_value (Pt := Pt)) v_args ts.
  Proof using Type.
    revert v_args EVAL.
    induction WTargs as [| e t args ts WTe WTargs IH]; intros v_args EVAL; cbn in EVAL.
    - inversion EVAL; subst; constructor.
    - destruct (eval e val_env) as [v|] eqn:Ee; cbn in EVAL; [| discriminate].
      destruct (map_opt (fun e => eval e val_env) args) as [vs|] eqn:Eargs; cbn in EVAL; [| discriminate].
      inversion EVAL; subst.
      constructor.
      + exact (eval_preserves_wt_env f ty_env val_env WT e t v WTe Ee).
      + (* The [destruct] simplified IH, can just pass [eq_refl] now. *)
        exact (IH vs eq_refl).
  Qed.

  (* Binding a fresh value flips its [ty_env] bit to [true] and stores it in the
  value environment *)
  Lemma wt_env_set [f ty_env val_env]
    (WTenv: wt_env f ty_env val_env)
    [id_b t_b v]
    (UNBOUND: Maps.PTree.get id_b ty_env = Some (t_b, false))
    (WTv: wt_value v t_b) :
    wt_env f (Maps.PTree.set id_b (t_b, true) ty_env) (Maps.PTree.set id_b v val_env).
  Proof using Type.
    destruct (wv_ty_env _ _ _ WTenv id_b t_b false UNBOUND) as [_ INb].
    refine {| wt_val_env := _; wv_ty_env := _ |}.
    - intros var_id t IN.
      destruct (Pos.eq_dec var_id id_b) as [->|NE].
      + destruct (wt_val_env _ _ _ WTenv id_b t IN) as [GET _].
        rewrite UNBOUND in GET; inversion GET; subst t.
        rewrite Maps.PTree.gss Maps.PTree.gss; cbn.
        split; [reflexivity |].
        intros v' EQv'; inversion EQv'; subst; exact WTv.
      + rewrite (Maps.PTree.gso _ _ NE) (Maps.PTree.gso _ _ NE).
        exact (wt_val_env _ _ _ WTenv var_id t IN).
    - intros var_id t b GET.
      destruct (Pos.eq_dec var_id id_b) as [->|NE].
      + rewrite Maps.PTree.gss in GET; inversion GET; subst t b.
        rewrite Maps.PTree.gss.
        split; [exists v; [reflexivity | exact WTv] | exact INb].
      + rewrite (Maps.PTree.gso _ _ NE) in GET.
        rewrite (Maps.PTree.gso _ _ NE).
        exact (wv_ty_env _ _ _ WTenv var_id t b GET).
  Qed.

  (* Well-typedness preservation when dropping a temporary amounts to flipping
  the boundness-bit in the type environment and removing the value from the
  value environment. *)
  Lemma wt_env_unset [f ty_env val_env]
    (WTenv: wt_env f ty_env val_env)
    [id t]
    (BOUND: Maps.PTree.get id ty_env = Some (t, true)) :
    wt_env f (Maps.PTree.set id (t, false) ty_env) (Maps.PTree.remove id val_env).
  Proof using Type.
    destruct (wv_ty_env _ _ _ WTenv id t true BOUND) as [_ IN].
    refine {| wt_val_env := _; wv_ty_env := _ |}.
    - intros var_id t' IN'.
      destruct (Pos.eq_dec var_id id) as [->|NE].
      + destruct (wt_val_env _ _ _ WTenv id t' IN') as [GET _].
        rewrite BOUND in GET; inversion GET; subst t'.
        rewrite Maps.PTree.gss Maps.PTree.grs; cbn.
        split; [reflexivity |].
        intros v' EQ'; discriminate EQ'.
      + rewrite (Maps.PTree.gso _ _ NE) (Maps.PTree.gro _ NE).
        exact (wt_val_env _ _ _ WTenv var_id t' IN').
    - intros var_id t' b GET.
      destruct (Pos.eq_dec var_id id) as [->|NE].
      + rewrite Maps.PTree.gss in GET; inversion GET; subst t' b.
        rewrite Maps.PTree.grs.
        split; [reflexivity | exact IN].
      + rewrite (Maps.PTree.gso _ _ NE) in GET.
        rewrite (Maps.PTree.gro _ NE).
        exact (wv_ty_env _ _ _ WTenv var_id t' b GET).
  Qed.

  (* The value returned by a built-in is well-typed wrt the command's type *)
  Lemma builtin_wt_value [ctx f c ge env locals s v s' t]
    (BUILTIN: builtin c ge env locals s v s')
    (WTc: wt_cmd ctx c t)
    (WTenv: wt_env f ctx.(ctxt_pure) env) :
    wt_value v t.
  Proof using Type.
    now destruct BUILTIN;
      inversion WTc; subst;
      first [ exact WT | now constructor | eapply eval_preserves_wt_env; eauto ].
  Qed.

  (* Continuations can be viewed as functions with type t -> k, where
   * * t is the type expected by the continuation
   *   * For Kstop it is t_nat
   *   * For Kcall it is the return type of the function
   *   * For Kbind it is the type of the variable to be bound
   *   * For Kloop1 it is t_bool
   *   * For Kloop2 it is t_unit
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
   * The continuation will be `Kcall f_main env_main locals_main Kstop`
   * This continuation is only well-typed if
   * returning from it produces exactly the type expected by the lower continuation
   *
   * Kbind is a continuation similar to Kseq in C-languages
   * We are currently evaluating a command, but when it "terminates", we don't exit the function
   * Instead, we bind the result to the provided variable
   * Typically, if when calling `int helper(int, int)` from `main` we enter a bind
   * The continuation could look like
   * `Kbind id_b_helper c_rest_helper
        (Kcall f_main env_main locals_main
          (Kbind id_b_main c_rest_main
            Kstop))`
   * This continuation is well-typed, iff
   * Executing the current command returns a value matching `id_b_helper`
   * Executing `c_rest_helper` produces a value match matching `id_b_main`
   * Executing `c_rest_main` produces a value of type `t_nat`
   * Thus Kbind is only well-type if
   * * Returning from it produces the type of id
   * * Executing c produces the type expected by k
   *
   * Kloop1 is a continuation similar to Kloop* in C-languages
   * We are currently in the "condition" part of a loop
   * Similarly as with Kbind, we don't exit the function when the command terminates
   * Instead, we inspect the mandatory boolean returned by the command
   * If it is false, we exit the loop
   * If it is true, we enter the loop body, the continuation is replaced by a Kloop2
   *
   * Kloop2 is the continuation responsible for the execution of loop bodies
   * As we are inside a loop body, we necessarily expect a unit value
   *)
  Inductive wt_cont_call: ctxt Empty_set Empty_set Empty_set fundef vardef -> cont -> type -> Prop :=
  | wt_Kstop: forall ctx,
      wt_cont_call ctx Kstop t_nat
  | wt_Kcall: forall ctx f e locals k t ty_env
                     (WTf: wt_function ctx f)
                     (WTenv: wt_env f ty_env e)
                     (WTcont: wt_cont (with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty) (with_pure ty_env (with_stack (List.map (fun _ => tt) locals) ctx))) k t),
      wt_cont_call ctx (Kcall f e locals k) t

  with wt_cont: ctxt (type * bool) (type * bool) unit fundef vardef -> cont -> type -> Prop :=
  | wt_cont_Kbind: forall ctx id c k t_b t_c
                          (GET: get_pure id ctx = Some (t_b, false))
                          (WTcmd: wt_cmd (set_pure id (t_b, true) ctx) c t_c)
                          (WTcont: wt_cont ctx k t_c),
      wt_cont ctx (Kbind id c k) t_b
  | wt_cont_Kloop1: forall ctx c_cond c_body k
                           (WTcond: wt_cmd ctx c_cond t_bool)
                           (WTbody: wt_cmd ctx c_body t_unit)
                           (WTcont: wt_cont ctx k t_unit),
      wt_cont ctx (Kloop1 c_cond c_body k) t_bool
  | wt_cont_Kloop2: forall ctx c_cond c_body k
                           (WTcond: wt_cmd ctx c_cond t_bool)
                           (WTbody: wt_cmd ctx c_body t_unit)
                           (WTcont: wt_cont ctx k t_unit),
      wt_cont ctx (Kloop2 c_cond c_body k) t_unit
  (* A call continuation is only well-typed if the current context has dropped
  all its temporaries. In other words, we expect that before reaching a call
  continuation, [Kscope] continuations drop the store variables. We can drop the
  temporary "for free" because they don't correspond to "real" memory.

   In proof scripts, this tactic can be taken aggressively by [econstructor] and
   [inversion] doesn't immediately see that it is dead code ([inversion WTcont]
   should fix it). *)
  | wt_cont_other: forall ctx k tret
                          (STACK_EMPTY: ctxt_stack ctx = [])
                          (WTcont: wt_cont_call (to_glob_ctxt ctx) k tret),
      wt_cont ctx k tret
  | wt_cont_Kscope_unbind: forall ctx id k t t'
                            (GET: get_pure id ctx = Some (t, true))
                            (WTcont: wt_cont (set_pure id (t, false) ctx) k t'),
      wt_cont ctx (Kscope (scope_bind id) k) t'
  | wt_cont_Kscope_pop: forall ctx k t s0 sl0
                               (STACK_NONEMPTY: ctxt_stack ctx = s0 :: sl0)
                               (WTcont: wt_cont (with_stack (removelast (ctxt_stack ctx)) ctx) k t),
      wt_cont ctx (Kscope scope_store k) t
  .

  (* When performing a [resolve_seq_cont], we can infer that for a new [ctx']
  and [t'] such that:
   - The [ctx'] stack is [ctx] stack with variables dropped according to [RESOLVE]
   - The global environment is unchanged
   - The new environment [ctx'] agrees with [ctx'] pure environment
  That
   - The new command [c'] is well-typed with type [t']
   - The new continuation [k'] well-typed with type [t']
   *)
  Lemma resolve_seq_preservation [f ctx t k env v c' env' k' n]
    (RESOLVE: resolve_seq_cont k env v c' env' k' n)
    (WTk: wt_cont ctx k t)
    (WTv: wt_value v t)
    (WTenv: wt_env f ctx.(ctxt_pure) env) :
    exists ctx' t',
      ctxt_stack ctx' = removelast_n n (ctxt_stack ctx) /\
      ctxt_global ctx' = ctxt_global ctx /\
      ctxt_internal ctx' = ctxt_internal ctx /\
      wt_cmd ctx' c' t' /\
      wt_cont ctx' k' t' /\
      wt_env f ctx'.(ctxt_pure) env'.
  Proof using Type.
    revert ctx t WTk WTv WTenv.
    induction RESOLVE as
      [ id_b c_next k0 env0 v0
      | c_cond c_body k0 env0 b
      | c_cond c_body k0 env0
      | id k0 env0 v0 c'0 env'0 k'0 n0 RES IH
      | k0 env0 v0 c'0 env'0 k'0 n0 RES IH
      ]; intros ctx t WTk WTv WTenv.
    - inversion WTk; subst; [| now inversion WTcont].
      exists (set_pure id_b (t, true) ctx), t_c.
      assert (EQctx: set_pure id_b (t, false) (set_pure id_b (t, true) ctx) = ctx).
      { apply Ctxt.Facts.ctxt_ext; [| reflexivity | reflexivity | reflexivity].
        cbn [ctxt_pure set_pure with_pure].
        rewrite Maps.PTree.set2.
        apply Maps.PTree.gsident, GET. }
      split; [| split; [| split; [| split; [| split]]]].
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + exact WTcmd.
      + apply wt_cont_Kscope_unbind with (t := t);
          [ apply Ctxt.Facts.get_set_pure | rewrite EQctx; exact WTcont ].
      + exact (wt_env_set WTenv GET WTv).
    - inversion WTk; subst; [| solve [inversion WTcont]].
      exists ctx, t_unit.
      split; [| split; [| split; [| split; [| split]]]].
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + destruct b; [ exact WTbody | constructor; constructor ].
      + destruct b; [ apply wt_cont_Kloop2; assumption | exact WTcont ].
      + exact WTenv.
    - inversion WTk; subst; [| solve [inversion WTcont]].
      exists ctx, t_bool.
      split; [| split; [| split; [| split; [| split]]]].
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + exact WTcond.
      + apply wt_cont_Kloop1; assumption.
      + exact WTenv.
    - inversion WTk; subst; [solve [inversion WTcont] |].
      destruct (IH (set_pure id (t0, false) ctx) t WTcont WTv
                  (wt_env_unset WTenv GET))
        as [ctx' [t' [STACK [GLOBEQ [INTERNAL [WTCMD [WTCONT WTENV]]]]]]].
      exists ctx', t'.
      split; [| split; [| split; [| split; [| split]]]].
      + rewrite STACK; reflexivity.
      + rewrite GLOBEQ; reflexivity.
      + rewrite INTERNAL; reflexivity.
      + exact WTCMD.
      + exact WTCONT.
      + exact WTENV.
    - inversion WTk; subst; [solve [inversion WTcont] |].
      destruct (IH (with_stack (removelast (ctxt_stack ctx)) ctx) t WTcont WTv WTenv)
        as [ctx' [t' [STACK [GLOBEQ [INTERNAL [WTCMD [WTCONT WTENV]]]]]]].
      exists ctx', t'.
      now split; [| split; [| split; [| split; [| split]]]].
  Qed.

  (* When performing a [resolve_call_cont], the resulting continuation is
  well-typed and awaits the same type *)
  Lemma resolve_call_preservation [k k0] (RESOLVE: resolve_call_cont k k0)
    [ctx t] (WTk: wt_cont ctx k t) :
    wt_cont_call (to_glob_ctxt ctx) k0 t.
  Proof using Type.
    revert ctx t WTk.
    induction RESOLVE as [ k CALLK | sx k k' RESOLVE IH ]; intros ctx t WTk.
    - inversion WTk; subst;
        [ solve [inversion CALLK] | solve [inversion CALLK] | solve [inversion CALLK]
        | | solve [inversion CALLK] | solve [inversion CALLK] ].
      exact WTcont.
    - inversion WTk; subst; [ solve [inversion WTcont] | | ].
      + exact (IH _ _ WTcont).
      + exact (IH _ _ WTcont).
  Qed.

  (* Removing the pure and stack contexts yields equal contexts, if their global
  environments are equal *)
  Lemma glob_ctxt_eq [P I S GF GV] [ctx1 ctx2: ctxt P I S GF GV]
    (GLOB: ctxt_global ctx1 = ctxt_global ctx2) :
    to_glob_ctxt ctx1
    = to_glob_ctxt ctx2 :> ctxt Empty_set Empty_set Empty_set GF GV.
  Proof using Type.
    now apply Ctxt.Facts.ctxt_ext.
  Qed.

  Lemma mk_glob_ctxt_eq [P I S] [p: program] [ctx: ctxt P I S fundef vardef]
    (GLOB: Globalenvs.Genv.globalenv p = ctxt_global ctx) :
    to_glob_ctxt ctx = mk_glob_ctxt p.
  Proof using Type.
    apply Ctxt.Facts.ctxt_ext; cbn [ctxt_pure ctxt_internal ctxt_stack ctxt_global with_pure with_stack to_glob_ctxt with_internal mk_glob_ctxt with_global];
      [reflexivity | reflexivity | reflexivity | symmetry; exact GLOB].
  Qed.

  Record wt_State (f: function) (c: cmd) (k: cont)
    (e: Maps.PTree.t (value Pt)) (locals: list Nm) (s: Sm)
    (ctx: ctxt (type * bool) (type * bool) unit fundef vardef) (t: type): Prop :=
    {
      State_wt_function: wt_function (to_glob_ctxt ctx) f;
      State_wt_cmd: wt_cmd ctx c t;
      State_wt_cont: wt_cont ctx k t;
      State_wt_env: wt_env f ctx.(ctxt_pure) e;
      State_wt_stack: ctxt_stack ctx = List.map (fun _ => tt) locals;
      State_internals: ctxt_internal ctx = mk_typing_tree false f.(fn_internals) Maps.PTree.Empty;
    }.

  Inductive wt_state (p: program): state -> Prop :=
  | wt_State_intro: forall f c k e locals s ctx t
                           (WTstate: wt_State f c k e locals s ctx t)
                           (GLOB: Globalenvs.Genv.globalenv p = ctxt_global ctx),
      wt_state p (State f c k e locals s)
  | wt_Callstate: forall f args k s sig (ctx: ctxt Empty_set Empty_set Empty_set fundef vardef)
                         (WTfundef: wt_fundef (mk_glob_ctxt p) f)
                         (WTargs: wt_fundef_call args f)
                         (SIG: funsig f sig)
                         (WTcont: wt_cont_call ctx k sig.(sig_res))
                         (GLOB: Globalenvs.Genv.globalenv p = ctxt_global ctx),
      wt_state p (Callstate f args k s)
  | wt_Returnstate: forall v k s (ctx: ctxt Empty_set Empty_set Empty_set fundef vardef) t
                           (WTres: wt_value v t)
                           (WTcont: wt_cont_call ctx k t)
                           (GLOB: Globalenvs.Genv.globalenv p = ctxt_global ctx),
      wt_state p (Returnstate v k s)
  .

  Lemma set_params_in_some_wt:
    forall [params: list (AST.ident * type)] [args: list (value Pt)]
           (SBINDS: ListExt.SBinds params)
           (WTargs: Forall2 (wt_value (Pt := Pt)) args (List.map snd params))
           [id t] (IN: In (id, t) params),
      exists v, Maps.PTree.get id (set_params params args) = Some v /\ wt_value v t.
  Proof using Type.
    induction params as [|[id1 t1] params IH]; cbn; intros args SBp WTARGS id t IN.
    - contradiction.
    - inversion WTARGS as [|v ? args' ? WTV WTARGSrest]; subst.
      destruct IN as [EQ | IN].
      + inversion EQ; subst id1 t1.
        exists v; split; [ apply Maps.PTree.gss | exact WTV ].
      + assert (NE: id <> id1)
          by (eapply ListExt.SBinds_tl_neq with (a := id1) (b := t1) (a' := id) (b' := t);
              [ exact SBp | exact IN ]).
        assert (SB': ListExt.SBinds params) by (inversion SBp; assumption).
        destruct (IH _ SB' WTARGSrest _ _ IN) as [v' [GET WT]].
        exists v'; split; [| exact WT ].
        rewrite (Maps.PTree.gso _ _ NE); exact GET.
  Qed.

  Lemma set_params_get_not_in:
    forall [params: list (AST.ident * type)] [args: list (value Pt)] [id]
      (NI: ~ In id (map fst params)),
      Maps.PTree.get id (set_params params args) = None.
  Proof using Type.
    induction params as [|[id1 t1] params IH]; intros args id NI.
    - destruct args; cbn; apply Maps.PTree.gempty.
    - destruct args as [|v args']; cbn; [apply Maps.PTree.gempty |].
      rewrite Maps.PTree.gso; [ intros EQ; subst; apply NI; now left |].
      apply IH. intros IN; apply NI; now right.
  Qed.


  Lemma wt_env_init
    [ctx: ctxt Empty_set Empty_set Empty_set fundef vardef]
    [f: function] [args: list (value Pt)] [internals]
    (WTfn: wt_function ctx f)
    (WTargs: Forall2 (wt_value (Pt := Pt)) args (List.map snd f.(fn_params))) :
    wt_env f (ctxt_pure (mk_function_ctxt f.(fn_params) f.(fn_temps) internals ctx))
              (set_params f.(fn_params) args).
  Proof.
    pose proof (wt_fn_params_sbinds WTfn) as SBp.
    pose proof (wt_fn_temps_sbinds WTfn) as SBt.
    pose proof (wt_fn_params_temps_distinct WTfn) as DIST.
    assert (TEMPNOTPARAM: forall id t,
               In (id, t) f.(fn_temps) -> ~ In id (map fst f.(fn_params))).
    { intros id t INt INpfst.
      apply in_map_iff in INpfst as [[ip tp] [FST INp]]; cbn in FST; subst ip.
      exact (ListExt.AbsBind_In_False (ListExt.DBinds_In_AbsBind DIST INp) INt). }
    refine {|
      wt_val_env := _;
      wv_ty_env := _;
    |}.
    - intros id t IN.
      destruct (in_dec (ReflectExt.sumbool_of_reflect (@Algebra.eqb_spec (AST.ident * type)%type)) (id, t) f.(fn_params)) as [INp | NOTP].
      + destruct (set_params_in_some_wt SBp WTargs INp) as [v [GET WT]].
        rewrite GET; split.
        * exact (Facts.mk_function_ctxt_pure_get_param _ _ _ _ SBp SBt DIST _ _ INp).
        * intros v' TYv'; inversion TYv'; subst; exact WT.
      + assert (INt: In (id, t) f.(fn_temps)).
        { apply in_app_or in IN as [|]; [contradiction | assumption]. }
        rewrite (set_params_get_not_in (TEMPNOTPARAM _ _ INt)); split.
        * exact (Facts.mk_function_ctxt_pure_get_temp _ _ _ _ SBp SBt DIST _ _ INt).
        * intros v' TYv'; discriminate TYv'.
    - intros id t b GET.
      destruct b.
      + assert (INp: In (id, t) f.(fn_params)).
        { pose proof (Facts.mk_function_ctxt_pure_get_inv _ _ _ _ SBp SBt _ _ _ GET) as CASE.
          destruct CASE as [[_ INp] | [BITf _]]; [exact INp | discriminate]. }
        split; [| apply in_or_app; now left ].
        destruct (Maps.PTree.get id (set_params f.(fn_params) args)) as [v|] eqn:E.
        * exists v; [reflexivity |].
          destruct (set_params_in_some_wt SBp WTargs INp) as [v' [GET' WT]].
          rewrite GET' in E; inversion E; subst; exact WT.
        * exfalso.
          destruct (set_params_in_some_wt SBp WTargs INp) as [v [GET' _]].
          rewrite GET' in E; discriminate.
      + assert (INt: In (id, t) f.(fn_temps)).
        { pose proof (Facts.mk_function_ctxt_pure_get_inv _ _ _ _ SBp SBt _ _ _ GET) as CASE.
          destruct CASE as [[BITt _] | [_ INt]]; [discriminate | exact INt]. }
        split; [| apply in_or_app; now right ].
        apply set_params_get_not_in.
        exact (TEMPNOTPARAM _ _ INt).
  Defined.

  Lemma fold_set_bit_get_other {V: Type} (entries: list (AST.ident * V))
    (bit: AST.ident -> bool) (id: AST.ident) (init: Maps.PTree.t (V * bool))
    (ABS: ListExt.AbsBind id entries) :
    Maps.PTree.get id
      (List.fold_left (fun c idt => Maps.PTree.set (fst idt) (snd idt, bit (fst idt)) c) entries init) =
    Maps.PTree.get id init.
  Proof using Type.
    revert init.
    induction entries as [ | [k v] rest IH ]; intros init; cbn.
    - reflexivity.
    - inversion ABS as [ | ? ? ? ? NE ABS' ]; subst.
      rewrite (IH ABS').
      apply Maps.PTree.gso. cbn. exact NE.
  Qed.

  Lemma fold_set_bit_get_in {V: Type} (entries: list (AST.ident * V))
    (bit: AST.ident -> bool) (id: AST.ident) (v: V) (init: Maps.PTree.t (V * bool))
    (SB: ListExt.SBinds entries) (IN: In (id, v) entries) :
    Maps.PTree.get id
      (List.fold_left (fun c idt => Maps.PTree.set (fst idt) (snd idt, bit (fst idt)) c) entries init) =
    Some (v, bit id).
  Proof using Type.
    revert init.
    induction SB as [ | k v' rest ABS SB' IH ]; intros init; cbn in IN;
      [ contradiction | ].
    destruct IN as [ EQ | IN' ].
    - inversion EQ; subst k v'; clear EQ.
      cbn [List.fold_left fst snd].
      rewrite (fold_set_bit_get_other rest bit id _ ABS).
      apply Maps.PTree.gss.
    - cbn [List.fold_left fst snd]. apply IH; exact IN'.
  Qed.

  Definition type_env_bit (e: Maps.PTree.t (value Pt)) (id: AST.ident) : bool :=
    match Maps.PTree.get id e with Some _ => true | None => false end.

  Definition type_env_ok (binders: list (AST.ident * type)) (e: Maps.PTree.t (value Pt)) : bool :=
    forallb (fun idt => match Maps.PTree.get (fst idt) e with
                        | Some v => type_eqb (type_of_value v) (snd idt)
                        | None => true
                        end) binders.

  Definition type_env_tree (f: function) (e: Maps.PTree.t (value Pt)) : Maps.PTree.t (type * bool) :=
    List.fold_left
      (fun c idt => Maps.PTree.set (fst idt) (snd idt, type_env_bit e (fst idt)) c)
      (f.(fn_params) ++ f.(fn_temps)) (Maps.PTree.empty (type * bool)).

  Definition type_env (f: function) (e: Maps.PTree.t (value Pt)) : option (Maps.PTree.t (type * bool)) :=
    if type_env_ok (f.(fn_params) ++ f.(fn_temps)) e
    then Some (type_env_tree f e)
    else None.

  Lemma type_env_tree_get_param (f: function) (e: Maps.PTree.t (value Pt))
    (SBp: ListExt.SBinds f.(fn_params)) (DIST: ListExt.DBinds f.(fn_params) f.(fn_temps))
    id t (IN: In (id, t) f.(fn_params)) :
    Maps.PTree.get id (type_env_tree f e) = Some (t, type_env_bit e id).
  Proof using Type.
    unfold type_env_tree; rewrite List.fold_left_app.
    rewrite (fold_set_bit_get_other f.(fn_temps) (type_env_bit e) id _
               (ListExt.DBinds_In_AbsBind DIST IN)).
    apply (fold_set_bit_get_in f.(fn_params) (type_env_bit e) id t _ SBp IN).
  Qed.

  Lemma type_env_tree_get_temp (f: function) (e: Maps.PTree.t (value Pt))
    (SBt: ListExt.SBinds f.(fn_temps))
    id t (IN: In (id, t) f.(fn_temps)) :
    Maps.PTree.get id (type_env_tree f e) = Some (t, type_env_bit e id).
  Proof using Type.
    unfold type_env_tree; rewrite List.fold_left_app.
    apply (fold_set_bit_get_in f.(fn_temps) (type_env_bit e) id t _ SBt IN).
  Qed.

  Lemma type_env_tree_get_none (f: function) (e: Maps.PTree.t (value Pt))
    id (NI: ~ In id (List.map fst (f.(fn_params) ++ f.(fn_temps)))) :
    Maps.PTree.get id (type_env_tree f e) = None.
  Proof using Type.
    rewrite List.map_app in NI.
    unfold type_env_tree; rewrite List.fold_left_app.
    rewrite (fold_set_bit_get_other f.(fn_temps) (type_env_bit e) id _
               (Facts.not_In_fst_AbsBind _ _ (fun H => NI (in_or_app _ _ _ (or_intror H))))).
    rewrite (fold_set_bit_get_other f.(fn_params) (type_env_bit e) id _
               (Facts.not_In_fst_AbsBind _ _ (fun H => NI (in_or_app _ _ _ (or_introl H))))).
    apply Maps.PTree.gempty.
  Qed.

  Lemma type_env_tree_get_inv (f: function) (e: Maps.PTree.t (value Pt))
    (SBp: ListExt.SBinds f.(fn_params)) (SBt: ListExt.SBinds f.(fn_temps))
    id t b (GET: Maps.PTree.get id (type_env_tree f e) = Some (t, b)) :
    In (id, t) (f.(fn_params) ++ f.(fn_temps)) /\ b = type_env_bit e id.
  Proof using Type.
    unfold type_env_tree in GET; rewrite List.fold_left_app in GET.
    destruct (List.in_dec Pos.eq_dec id (List.map fst f.(fn_temps))) as [INtfst | NOTt].
    - apply in_map_iff in INtfst as [ [id' t'] [FST INt] ]; cbn in FST; subst id'.
      rewrite (fold_set_bit_get_in f.(fn_temps) (type_env_bit e) id t' _ SBt INt) in GET.
      inversion GET; subst; split; [ apply in_or_app; now right | reflexivity ].
    - rewrite (fold_set_bit_get_other f.(fn_temps) (type_env_bit e) id _
                 (Facts.not_In_fst_AbsBind _ _ NOTt)) in GET.
      destruct (List.in_dec Pos.eq_dec id (List.map fst f.(fn_params))) as [INpfst | NOTp].
      + apply in_map_iff in INpfst as [ [id' t'] [FST INp] ]; cbn in FST; subst id'.
        rewrite (fold_set_bit_get_in f.(fn_params) (type_env_bit e) id t' _ SBp INp) in GET.
        inversion GET; subst; split; [ apply in_or_app; now left | reflexivity ].
      + rewrite (fold_set_bit_get_other f.(fn_params) (type_env_bit e) id _
                   (Facts.not_In_fst_AbsBind _ _ NOTp)) in GET.
        rewrite Maps.PTree.gempty in GET; discriminate GET.
  Qed.

  (* Value environment setting commutes with [type_env_tree] *)
  Lemma type_env_tree_set (f: function) (e: Maps.PTree.t (value Pt))
    (SBp: ListExt.SBinds f.(fn_params)) (SBt: ListExt.SBinds f.(fn_temps))
    (DIST: ListExt.DBinds f.(fn_params) f.(fn_temps))
    id t a (IN: In (id, t) (f.(fn_params) ++ f.(fn_temps))) :
    type_env_tree f (Maps.PTree.set id a e)
    = Maps.PTree.set id (t, true) (type_env_tree f e).
  Proof using Type.
    apply Maps.PTree.extensionality. intro k.
    destruct (Pos.eq_dec k id) as [->|NE].
    - rewrite Maps.PTree.gss.
      apply in_app_or in IN as [INp | INt].
      + rewrite (type_env_tree_get_param f (Maps.PTree.set id a e) SBp DIST _ _ INp).
        unfold type_env_bit. rewrite Maps.PTree.gss. reflexivity.
      + rewrite (type_env_tree_get_temp f (Maps.PTree.set id a e) SBt _ _ INt).
        unfold type_env_bit. rewrite Maps.PTree.gss. reflexivity.
    - rewrite (Maps.PTree.gso _ _ NE).
      destruct (List.in_dec Pos.eq_dec k (List.map fst f.(fn_params))) as [INp|NINp].
      + apply List.in_map_iff in INp as [[id' t'] [FST INp]]; cbn in FST; subst id'.
        rewrite (type_env_tree_get_param f (Maps.PTree.set id a e) SBp DIST _ _ INp).
        rewrite (type_env_tree_get_param f e SBp DIST _ _ INp).
        unfold type_env_bit. rewrite (Maps.PTree.gso _ _ NE). reflexivity.
      + destruct (List.in_dec Pos.eq_dec k (List.map fst f.(fn_temps))) as [INt|NINt].
        * apply List.in_map_iff in INt as [[id' t'] [FST INt]]; cbn in FST; subst id'.
          rewrite (type_env_tree_get_temp f (Maps.PTree.set id a e) SBt _ _ INt).
          rewrite (type_env_tree_get_temp f e SBt _ _ INt).
          unfold type_env_bit. rewrite (Maps.PTree.gso _ _ NE). reflexivity.
        * assert (NI: ~ List.In k (List.map fst (f.(fn_params) ++ f.(fn_temps)))).
          { rewrite List.map_app List.in_app_iff. tauto. }
          rewrite (type_env_tree_get_none f (Maps.PTree.set id a e) _ NI).
          rewrite (type_env_tree_get_none f e _ NI). reflexivity.
  Qed.

  (* Value environment unsetting commutes with [type_env_tree] *)
  Lemma type_env_tree_remove (f: function) (e: Maps.PTree.t (value Pt))
    (SBp: ListExt.SBinds f.(fn_params)) (SBt: ListExt.SBinds f.(fn_temps))
    (DIST: ListExt.DBinds f.(fn_params) f.(fn_temps))
    id t (IN: In (id, t) (f.(fn_params) ++ f.(fn_temps))) :
    type_env_tree f (Maps.PTree.remove id e)
    = Maps.PTree.set id (t, false) (type_env_tree f e).
  Proof using Type.
    apply Maps.PTree.extensionality. intro k.
    destruct (Pos.eq_dec k id) as [->|NE].
    - rewrite Maps.PTree.gss.
      apply in_app_or in IN as [INp | INt].
      + rewrite (type_env_tree_get_param f (Maps.PTree.remove id e) SBp DIST _ _ INp).
        unfold type_env_bit. rewrite Maps.PTree.grs. reflexivity.
      + rewrite (type_env_tree_get_temp f (Maps.PTree.remove id e) SBt _ _ INt).
        unfold type_env_bit. rewrite Maps.PTree.grs. reflexivity.
    - rewrite (Maps.PTree.gso _ _ NE).
      destruct (List.in_dec Pos.eq_dec k (List.map fst f.(fn_params))) as [INp|NINp].
      + apply List.in_map_iff in INp as [[id' t'] [FST INp]]; cbn in FST; subst id'.
        rewrite (type_env_tree_get_param f (Maps.PTree.remove id e) SBp DIST _ _ INp).
        rewrite (type_env_tree_get_param f e SBp DIST _ _ INp).
        unfold type_env_bit. rewrite (Maps.PTree.gro _ NE). reflexivity.
      + destruct (List.in_dec Pos.eq_dec k (List.map fst f.(fn_temps))) as [INt|NINt].
        * apply List.in_map_iff in INt as [[id' t'] [FST INt]]; cbn in FST; subst id'.
          rewrite (type_env_tree_get_temp f (Maps.PTree.remove id e) SBt _ _ INt).
          rewrite (type_env_tree_get_temp f e SBt _ _ INt).
          unfold type_env_bit. rewrite (Maps.PTree.gro _ NE). reflexivity.
        * assert (NI: ~ List.In k (List.map fst (f.(fn_params) ++ f.(fn_temps)))).
          { rewrite List.map_app List.in_app_iff. tauto. }
          rewrite (type_env_tree_get_none f (Maps.PTree.remove id e) _ NI).
          rewrite (type_env_tree_get_none f e _ NI). reflexivity.
  Qed.

  Lemma type_env_ok_wt (binders: list (AST.ident * type)) (e: Maps.PTree.t (value Pt))
    (OK: type_env_ok binders e = true)
    id t v (IN: In (id, t) binders) (EV: Maps.PTree.get id e = Some v) :
    type_of_value v = t.
  Proof using Type.
    unfold type_env_ok in OK; rewrite forallb_forall in OK.
    specialize (OK (id, t) IN); cbn in OK; rewrite EV in OK.
    destruct (type_eqb_spec (type_of_value v) t); [ assumption | discriminate OK ].
  Qed.

  Lemma fold_set_bit_get_inv_gen {V: Type} (entries: list (AST.ident * V))
    (bit: AST.ident -> bool) (id: AST.ident) (init: Maps.PTree.t (V * bool)) (t: V) (b: bool)
    (GET: Maps.PTree.get id
             (List.fold_left (fun c idt => Maps.PTree.set (fst idt) (snd idt, bit (fst idt)) c) entries init)
           = Some (t, b)) :
    (In (id, t) entries /\ b = bit id) \/ Maps.PTree.get id init = Some (t, b).
  Proof using Type.
    revert init GET.
    induction entries as [ | [k v] rest IH ]; intros init GET;
      cbn [List.fold_left fst snd] in GET.
    - right; exact GET.
    - specialize (IH _ GET); destruct IH as [ [IN BIT] | INIT ].
      + left; split; [ right; exact IN | exact BIT ].
      + rewrite Maps.PTree.gsspec in INIT.
        destruct (Coqlib.peq id k) as [ -> | NE ].
        * inversion INIT; subst; left; split; [ left; reflexivity | reflexivity ].
        * right; exact INIT.
  Qed.

  Lemma type_env_get_value_spec [f] [e] [ty_env] (EQ: type_env f e = Some ty_env)
    [id] [t] (GET: Maps.PTree.get id ty_env = Some (t, true)) :
    exists v, Maps.PTree.get id e = Some v /\ type_of_value v = t.
  Proof using Type.
    unfold type_env in EQ.
    destruct (type_env_ok (f.(fn_params) ++ f.(fn_temps)) e) eqn:OK; [ | discriminate EQ ].
    injection EQ as <-.
    assert (INb: In (id, t) (f.(fn_params) ++ f.(fn_temps)) /\ type_env_bit e id = true).
    { unfold type_env_tree in GET.
      destruct (fold_set_bit_get_inv_gen _ _ _ _ _ _ GET) as [ [IN EQb] | EMPTY ].
      - split; [ exact IN | symmetry; exact EQb ].
      - rewrite Maps.PTree.gempty in EMPTY; discriminate EMPTY. }
    destruct INb as [IN BIT].
    unfold type_env_bit in BIT.
    destruct (Maps.PTree.get id e) as [v|] eqn:EV; [ | discriminate BIT ].
    exists v; split; [ reflexivity | exact (type_env_ok_wt _ _ OK id t v IN EV) ].
  Qed.

  Definition type_env_get_value [f] [e] [ty_env] (EQ: type_env f e = Some ty_env)
    [id] [t] (GET: Maps.PTree.get id ty_env = Some (t, true)) :
    { v & Maps.PTree.get id e = Some v & type_of_value v = t }.
  Proof.
    refine (match Maps.PTree.get id e as o
                  return (Maps.PTree.get id e = o ->
                          { v & Maps.PTree.get id e = Some v & type_of_value v = t })
            with
            | Some v => fun EV =>
                match ReflectExt.sumbool_of_reflect eqb_spec (type_of_value v) t with
                | left EQt => existT2 _ _ v EV EQt
                | right NE => _
                end
            | None => fun EV => _
            end eq_refl).
    - exfalso. destruct (type_env_get_value_spec EQ GET) as [v' [TYv' TY']].
      rewrite EV in TYv'; injection TYv' as <-; exact (NE TY').
    - exfalso. destruct (type_env_get_value_spec EQ GET) as [v' [TYv' _]].
      rewrite EV in TYv'; discriminate TYv'.
  Defined.

  Lemma type_env_correct (f: function) (e: Maps.PTree.t (value Pt)) (ty_env: Maps.PTree.t (type * bool))
    (SBp: ListExt.SBinds f.(fn_params)) (SBt: ListExt.SBinds f.(fn_temps))
    (DIST: ListExt.DBinds f.(fn_params) f.(fn_temps))
    (EQ: type_env f e = Some ty_env) :
    wt_env f ty_env e.
  Proof using Type.
    unfold type_env in EQ.
    destruct (type_env_ok (f.(fn_params) ++ f.(fn_temps)) e) eqn:OK; [ | discriminate EQ ].
    injection EQ as <-.
    refine {| wt_val_env := _; wv_ty_env := _ |}.
    - intros id t IN; split.
      + apply in_app_or in IN as [INp | INt].
        * exact (type_env_tree_get_param f e SBp DIST id t INp).
        * exact (type_env_tree_get_temp f e SBt id t INt).
      + intros v EV.
        rewrite <- (type_env_ok_wt _ _ OK id t v IN EV).
        apply Value.Facts.type_of_value_correct.
    - intros id t b GET.
      destruct (type_env_tree_get_inv f e SBp SBt id t b GET) as [IN BIT]; subst b.
      split; [ | exact IN ].
      unfold type_env_bit; destruct (Maps.PTree.get id e) as [v|] eqn:EV.
      + exists v; [ reflexivity | ].
        rewrite <- (type_env_ok_wt _ _ OK id t v IN EV).
        apply Value.Facts.type_of_value_correct.
      + reflexivity.
  Qed.

  Lemma type_env_complete (f: function) (e: Maps.PTree.t (value Pt)) (ty_env: Maps.PTree.t (type * bool))
    (SBp: ListExt.SBinds f.(fn_params)) (SBt: ListExt.SBinds f.(fn_temps))
    (DIST: ListExt.DBinds f.(fn_params) f.(fn_temps))
    (WT: wt_env f ty_env e) :
    type_env f e = Some ty_env.
  Proof using Type.
    unfold type_env.
    assert (OK: type_env_ok (f.(fn_params) ++ f.(fn_temps)) e = true).
    { unfold type_env_ok; apply forallb_forall; intros [id t] IN; cbn.
      destruct (Maps.PTree.get id e) as [v|] eqn:EV; [ | reflexivity ].
      destruct (wt_val_env _ _ _ WT id t IN) as [_ WTV].
      rewrite (Value.Facts.type_of_value_complete (WTV v EV)); apply (ReflectExt.reflect_refl type_eqb_spec _). }
    rewrite OK; f_equal.
    apply Maps.PTree.extensionality; intros id.
    destruct (Maps.PTree.get id ty_env) as [ [t b] |] eqn:GET.
    - destruct (wv_ty_env _ _ _ WT id t b GET) as [_ IN].
      destruct (wt_val_env _ _ _ WT id t IN) as [GET' _].
      apply in_app_or in IN as [INp | INt].
      + rewrite (type_env_tree_get_param f e SBp DIST id t INp).
        rewrite GET' in GET; unfold type_env_bit in *; congruence.
      + rewrite (type_env_tree_get_temp f e SBt id t INt).
        rewrite GET' in GET; unfold type_env_bit in *; congruence.
    - apply type_env_tree_get_none.
      intros INfst; apply in_map_iff in INfst as [ [id' t'] [FST IN'] ]; cbn in FST; subst id'.
      destruct (wt_val_env _ _ _ WT id t' IN') as [GET' _].
      rewrite GET' in GET; discriminate GET.
  Qed.

  Definition type_cont_call' (type_cont: ctxt (type * bool) (type * bool) unit fundef vardef -> cont -> option type) (ctx: ctxt Empty_set Empty_set Empty_set fundef vardef) (k: cont)
    : option type :=
    match k with
    | Kstop => Some t_nat
    | Kcall f e locals k' =>
        if type_function ctx f
        then match type_env f e with
             | Some ty_env =>
                 type_cont (with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty) (with_pure ty_env (with_stack (List.map (fun _: Nm => tt) locals) ctx))) k'
             | None => None
             end
        else None
    | _ => None
    end.

  Fixpoint type_cont (ctx: ctxt (type * bool) (type * bool) unit fundef vardef) (k: cont)
    {struct k} : option type :=
    match k with
    | Kbind id c k' =>
        match get_pure id ctx with
        | Some (t_b, false) =>
            match type_cmd (set_pure id (t_b, true) ctx) c, type_cont ctx k' with
            | Some t_c, Some t_c' => if type_eqb t_c t_c' then Some t_b else None
            | _, _ => None
            end
        | _ => None
        end
    | Kloop1 c_cond c_body k' =>
        match type_cmd ctx c_cond, type_cmd ctx c_body, type_cont ctx k' with
        | Some t_bool, Some t_unit, Some t_unit => Some t_bool
        | _, _, _ => None
        end
    | Kloop2 c_cond c_body k' =>
        match type_cmd ctx c_cond, type_cmd ctx c_body, type_cont ctx k' with
        | Some t_bool, Some t_unit, Some t_unit => Some t_unit
        | _, _, _ => None
        end
    | Kstop =>
        match ctxt_stack ctx with
        | [] => Some t_nat
        | _ :: _ => None
        end
    | Kcall f e locals k' =>
        match ctxt_stack ctx with
        | [] =>
            if type_function (to_glob_ctxt ctx) f
            then match type_env f e with
                 | Some ty_env =>
                     type_cont (with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty) (with_pure ty_env (with_stack (List.map (fun _ => tt) locals) ctx))) k'
                 | None => None
                 end
            else None
        | _ :: _ => None
        end
    | Kscope sx k' =>
        match sx with
        | scope_bind id =>
            match get_pure id ctx with
            | Some (t, true) => type_cont (set_pure id (t, false) ctx) k'
            | _ => None
            end
        | scope_store =>
            match ctxt_stack ctx with
            | [] => None
            | _ :: _ => type_cont (with_stack (removelast (ctxt_stack ctx)) ctx) k'
            end
        end
    end.

  Notation type_cont_call := (type_cont_call' type_cont).

  Scheme wt_cont_mind := Induction for wt_cont Sort Prop
    with wt_cont_call_mind := Induction for wt_cont_call Sort Prop.
  Combined Scheme wt_cont_mutind from wt_cont_mind, wt_cont_call_mind.

  Lemma type_cont_and_call_complete :
    (forall ctx k t (W: wt_cont ctx k t), type_cont ctx k = Some t)
    /\ (forall ctx k t (W: wt_cont_call ctx k t), type_cont_call ctx k = Some t).
  Proof using Type.
    apply (wt_cont_mutind
             (fun ctx k t _ => type_cont ctx k = Some t)
             (fun ctx k t _ => type_cont_call ctx k = Some t)).
    - intros ctx id c k t_b t_c GET WTCMD WTcont IH.
      cbn [type_cont]; rewrite GET (type_cmd_complete WTCMD) IH (ReflectExt.reflect_refl type_eqb_spec).
      reflexivity.
    - intros ctx c_cond c_body k WTcond WTBODY WTcont IH.
      cbn [type_cont]; rewrite (type_cmd_complete WTcond) (type_cmd_complete WTBODY) IH.
      reflexivity.
    - intros ctx c_cond c_body k WTcond WTBODY WTcont IH.
      cbn [type_cont]; rewrite (type_cmd_complete WTcond) (type_cmd_complete WTBODY) IH.
      reflexivity.
    - intros ctx k tret STACKEMPTY WTcont IH.
      destruct k; cbn [type_cont type_cont_call] in IH |- *; try rewrite STACKEMPTY;
        first [ exact IH | discriminate IH ].
    - intros ctx id k t t' GET WTcont IH.
      cbn [type_cont]; rewrite GET. exact IH.
    - intros ctx k t s0 sl0 STACKNONEMPTY WTcont IH.
      cbn [type_cont]. rewrite STACKNONEMPTY in IH |- *. exact IH.
    - intros ctx; reflexivity.
    - intros ctx f e locals k t ty_env WTfn WTENV WTcont IH.
      cbn [type_cont_call].
      rewrite (type_function_complete _ _ WTfn).
      rewrite (type_env_complete _ _ _
                 (wt_fn_params_sbinds WTfn) (wt_fn_temps_sbinds WTfn)
                 (wt_fn_params_temps_distinct WTfn) WTENV).
      exact IH.
  Qed.

  Lemma type_cont_complete [ctx] [k] [t] (W: wt_cont ctx k t) :
    type_cont ctx k = Some t.
  Proof using Type. exact (proj1 type_cont_and_call_complete ctx k t W). Qed.

  Lemma type_cont_call_complete [ctx] [k] [t] (W: wt_cont_call ctx k t) :
    type_cont_call ctx k = Some t.
  Proof using Type. exact (proj2 type_cont_and_call_complete ctx k t W). Qed.

  Lemma type_cont_and_call_correct (k: cont) :
    (forall ctx t (WT: type_cont ctx k = Some t), wt_cont ctx k t)
    /\ (forall ctx t (WT: type_cont_call ctx k = Some t), wt_cont_call ctx k t).
  Proof using Type.
    induction k as [ | id c k' IH | c_cond c_body k' IH | c_cond c_body k' IH
                   | f e locals k' IH | sx k' IH ];
      split; intros ctx t WT.
    - cbn [type_cont] in WT.
      destruct (ctxt_stack ctx) eqn:STK; [ | discriminate WT ].
      injection WT as <-.
      exact (wt_cont_other ctx Kstop t_nat STK
               (wt_Kstop (to_glob_ctxt ctx))).
    - cbn [type_cont_call] in WT. injection WT as <-.
      exact (wt_Kstop ctx).
    - cbn [type_cont] in WT.
      destruct (get_pure id ctx) as [ [ t_b [ | ] ] | ] eqn:GETP;
        [ discriminate WT | | discriminate WT ].
      destruct (type_cmd (set_pure id (t_b, true) ctx) c) as [t_c|] eqn:WTc;
        [ | discriminate WT ].
      destruct (type_cont ctx k') as [t_c'|] eqn:WTk; [ | discriminate WT ].
      destruct (type_eqb_spec t_c t_c'); [ subst t_c'; injection WT as <- | discriminate WT ].
      exact (wt_cont_Kbind ctx id c k' t_b t_c GETP
               (type_cmd_correct WTc) (proj1 IH ctx t_c WTk)).
    - cbn [type_cont_call] in WT. discriminate WT.
    - cbn [type_cont] in WT.
      destruct (type_cmd ctx c_cond) as [ [ | | | | ] | ] eqn:WTcond; try discriminate WT.
      destruct (type_cmd ctx c_body) as [ [ | | | | ] | ] eqn:WTbody; try discriminate WT.
      destruct (type_cont ctx k') as [ [ | | | | ] | ] eqn:WTk; try discriminate WT.
      injection WT as <-.
      exact (wt_cont_Kloop1 ctx c_cond c_body k'
               (type_cmd_correct WTcond) (type_cmd_correct WTbody)
               (proj1 IH ctx t_unit WTk)).
    - cbn [type_cont_call] in WT. discriminate WT.
    - cbn [type_cont] in WT.
      destruct (type_cmd ctx c_cond) as [ [ | | | | ] | ] eqn:WTcond; try discriminate WT.
      destruct (type_cmd ctx c_body) as [ [ | | | | ] | ] eqn:WTbody; try discriminate WT.
      destruct (type_cont ctx k') as [ [ | | | | ] | ] eqn:WTk; try discriminate WT.
      injection WT as <-.
      exact (wt_cont_Kloop2 ctx c_cond c_body k'
               (type_cmd_correct WTcond) (type_cmd_correct WTbody)
               (proj1 IH ctx t_unit WTk)).
    - cbn [type_cont_call] in WT. discriminate WT.
    - cbn [type_cont] in WT.
      destruct (ctxt_stack ctx) eqn:STK; [ | discriminate WT ].
      destruct (type_function (to_glob_ctxt ctx) f)
        eqn:TF; [ | discriminate WT ].
      destruct (type_env f e) as [ty_env|] eqn:TE; [ | discriminate WT ].
      pose proof (type_function_correct _ _ TF) as WTFN.
      exact (wt_cont_other ctx (Kcall f e locals k') t STK
               (wt_Kcall _ f e locals k' t ty_env WTFN
                  (type_env_correct f e ty_env
                     (wt_fn_params_sbinds WTFN) (wt_fn_temps_sbinds WTFN)
                     (wt_fn_params_temps_distinct WTFN) TE)
                  (proj1 IH _ t WT))).
    - cbn [type_cont_call] in WT.
      destruct (type_function ctx f) eqn:TF; [ | discriminate WT ].
      destruct (type_env f e) as [ty_env|] eqn:TE; [ | discriminate WT ].
      pose proof (type_function_correct _ _ TF) as WTFN.
      exact (wt_Kcall ctx f e locals k' t ty_env WTFN
               (type_env_correct f e ty_env
                  (wt_fn_params_sbinds WTFN) (wt_fn_temps_sbinds WTFN)
                  (wt_fn_params_temps_distinct WTFN) TE)
               (proj1 IH _ t WT)).
    - destruct sx as [id | ].
      + cbn [type_cont] in WT.
        destruct (get_pure id ctx) as [ [ t0 [ | ] ] | ] eqn:GETP;
          [ | discriminate WT | discriminate WT ].
        exact (wt_cont_Kscope_unbind ctx id k' t0 t GETP (proj1 IH _ t WT)).
      + cbn [type_cont] in WT.
        destruct (ctxt_stack ctx) as [|s0 sl0] eqn:STK; [ discriminate WT | ].
        apply (wt_cont_Kscope_pop ctx k' t s0 sl0 STK).
        rewrite STK. exact (proj1 IH _ t WT).
    - cbn [type_cont_call] in WT. discriminate WT.
  Qed.

  Lemma type_cont_correct [ctx] [k: cont] [t]
    (WT: type_cont ctx k = Some t) : wt_cont ctx k t.
  Proof using Type. exact (proj1 (type_cont_and_call_correct k) ctx t WT). Qed.

  Lemma type_cont_call_correct [ctx] [k: cont] [t]
    (WT: type_cont_call ctx k = Some t) : wt_cont_call ctx k t.
  Proof using Type. exact (proj2 (type_cont_and_call_correct k) ctx t WT). Qed.

  Definition state_ctxt (p: program) (f: function)
    (ty_env: Maps.PTree.t (type * bool)) (locals: list Nm)
    : ctxt (type * bool) (type * bool) unit fundef vardef :=
    with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty)
      (with_pure ty_env (with_stack (List.map (fun _ => tt) locals) (mk_glob_ctxt p))).

  Lemma state_ctxt_internal p f ty_env locals:
    ctxt_internal (state_ctxt p f ty_env locals) = mk_typing_tree false f.(fn_internals) Maps.PTree.Empty.
  Proof using Type.
    reflexivity.
  Qed.

  Lemma ptree_Empty_set (t: Maps.PTree.t Empty_set): t = Maps.PTree.empty Empty_set.
  Proof using Type.
    apply Maps.PTree.extensionality; intro k; rewrite Maps.PTree.gempty.
    destruct (Maps.PTree.get k t) as [e|]; [destruct e | reflexivity].
  Qed.

  Lemma list_Empty_set (l: list Empty_set): l = [].
  Proof using Type. destruct l as [|e l]; [reflexivity | destruct e]. Qed.

  Lemma glob_ctx_unique (p: program) (ctx: ctxt Empty_set Empty_set Empty_set fundef vardef):
    Globalenvs.Genv.globalenv p = ctxt_global ctx -> ctx = mk_glob_ctxt p.
  Proof using Type.
    intro H. apply Ctxt.Facts.ctxt_ext.
    - rewrite (ptree_Empty_set (ctxt_pure ctx)); reflexivity.
    - rewrite (ptree_Empty_set (ctxt_internal ctx)); reflexivity.
    - rewrite (list_Empty_set (ctxt_stack ctx)); reflexivity.
    - cbn; symmetry; exact H.
  Qed.

  Definition type_state (p: program) (s: state)
    : option type :=
    match s with
    | State f c k e locals _ =>
        if type_function (mk_glob_ctxt p) f
        then match type_env f e with
             | Some ty_env =>
                 match type_cmd (state_ctxt p f ty_env locals) c,
                       type_cont (state_ctxt p f ty_env locals) k with
                 | Some t_c, Some t_k => if type_eqb t_c t_k then Some t_c else None
                 | _, _ => None
                 end
             | None => None
             end
        else None
    | Callstate f args k _ =>
        match type_funsig f with
        | Some sig =>
            if type_fundef (mk_glob_ctxt p) f
            then if type_call_args args sig.(sig_args)
                 then match type_cont_call (mk_glob_ctxt p) k with
                      | Some t => if type_eqb t sig.(sig_res) then Some t else None
                      | None => None
                      end
                 else None
            else None
        | None => None
        end
    | Returnstate v k _ =>
        match type_cont_call (mk_glob_ctxt p) k with
        | Some t => if type_eqb (type_of_value v) t then Some t else None
        | None => None
        end
    end.

  Lemma type_state_complete_ex (p: program) (s: state):
    wt_state p s -> exists t, type_state p s = Some t.
  Proof using Type.
    intro WTs. destruct WTs as
      [ f c k e locals s' ctx t WTSTATE GLOB
      | f args k s' sig ctx WTFUNDEF WTARGS SIG WTcont GLOB
      | v k s' ctx t WTRES WTcont GLOB ].
    - destruct WTSTATE as [WTFN WTCMD WTCONT WTENV STK INTERNAL].
      exists t. cbn [type_state].
      rewrite <- (glob_ctx_unique p (to_glob_ctxt ctx) GLOB),
              (type_function_complete _ _ WTFN).
      rewrite (type_env_complete f e (ctxt_pure ctx)
                 (wt_fn_params_sbinds WTFN) (wt_fn_temps_sbinds WTFN)
                 (wt_fn_params_temps_distinct WTFN) WTENV).
      assert (CTX: state_ctxt p f (ctxt_pure ctx) locals = ctx).
      { apply Ctxt.Facts.ctxt_ext.
        - reflexivity.
        - cbn; symmetry; exact INTERNAL.
        - cbn; symmetry; exact STK.
        - cbn; exact GLOB. }
      rewrite CTX (type_cmd_complete WTCMD) (type_cont_complete WTCONT) (ReflectExt.reflect_refl type_eqb_spec).
      reflexivity.
    - exists sig.(sig_res). cbn [type_state].
      rewrite (type_funsig_complete _ _ SIG) (type_fundef_complete _ _ WTFUNDEF).
      rewrite (type_call_args_complete f sig args WTARGS (type_funsig_complete _ _ SIG)).
      rewrite <- (glob_ctx_unique p ctx GLOB).
      rewrite (type_cont_call_complete WTcont) (ReflectExt.reflect_refl type_eqb_spec).
      reflexivity.
    - exists t. cbn [type_state].
      rewrite <- (glob_ctx_unique p ctx GLOB).
      rewrite (type_cont_call_complete WTcont)
              (Value.Facts.type_of_value_complete WTRES) (ReflectExt.reflect_refl type_eqb_spec).
      reflexivity.
  Qed.

  Lemma type_state_complete (p: program) (s: state)
    (WTs: wt_state p s) : { t & type_state p s = Some t }.
  Proof using Type.
    destruct (type_state p s) as [t|] eqn:E.
    - now exists t.
    - exfalso. destruct (type_state_complete_ex p s WTs) as [t' TY']; congruence.
  Qed.

  Lemma type_state_correct {p} {s: state} {t}
    (WT: type_state p s = Some t): wt_state p s.
  Proof using Type.
    destruct s as [ f c k e locals mem | f args k mem | v k mem ].
    - cbn [type_state] in WT.
      destruct (type_function (mk_glob_ctxt p) f) eqn:TF; [ | discriminate WT ].
      destruct (type_env f e) as [ty_env|] eqn:TE; [ | discriminate WT ].
      destruct (type_cmd (state_ctxt p f ty_env locals) c) as [t_c|] eqn:WTc;
        [ | discriminate WT ].
      destruct (type_cont (state_ctxt p f ty_env locals) k) as [t_k|] eqn:WTk;
        [ | discriminate WT ].
      destruct (type_eqb_spec t_c t_k); [ subst t_k; injection WT as <- | discriminate WT ].
      pose proof (type_function_correct _ _ TF) as WTFN.
      apply (wt_State_intro p f c k e locals mem (state_ctxt p f ty_env locals) t_c);
        [ | reflexivity ].
      refine {| State_wt_function := _; State_wt_cmd := type_cmd_correct WTc;
                State_wt_cont := type_cont_correct WTk;
                State_wt_env := _; State_wt_stack := eq_refl;
                State_internals := eq_refl |}.
      + rewrite (glob_ctx_unique p
                   (to_glob_ctxt ((state_ctxt p f ty_env locals)))
                   eq_refl).
        exact WTFN.
      + exact (type_env_correct f e ty_env
                 (wt_fn_params_sbinds WTFN) (wt_fn_temps_sbinds WTFN)
                 (wt_fn_params_temps_distinct WTFN) TE).
    - cbn [type_state] in WT.
      destruct (type_funsig f) as [sig|] eqn:SIG; [ | discriminate WT ].
      destruct (type_fundef (mk_glob_ctxt p) f) eqn:TFD; [ | discriminate WT ].
      destruct (type_call_args args sig.(sig_args)) eqn:TA; [ | discriminate WT ].
      destruct (type_cont_call (mk_glob_ctxt p) k) as [t_k|] eqn:WTk;
        [ | discriminate WT ].
      destruct (type_eqb_spec t_k sig.(sig_res)); [ subst t_k | discriminate WT ].
      apply (wt_Callstate p f args k mem sig (mk_glob_ctxt p)).
      + exact (type_fundef_correct _ _ TFD).
      + exact (type_call_args_correct f sig args SIG TA).
      + exact (type_funsig_correct f sig SIG).
      + exact (type_cont_call_correct WTk).
      + reflexivity.
    - cbn [type_state] in WT.
      destruct (type_cont_call (mk_glob_ctxt p) k) as [t_k|] eqn:WTk;
        [ | discriminate WT ].
      destruct (type_eqb_spec (type_of_value v) t_k); [ subst t_k | discriminate WT ].
      apply (wt_Returnstate p v k mem (mk_glob_ctxt p) (type_of_value v)).
      + exact Value.Facts.type_of_value_correct.
      + exact (type_cont_call_correct WTk).
      + reflexivity.
  Qed.

  (* Type preservation/Subject reduction under [step] *)
  Theorem step_preservation (p: program) (s s': state) tr
    (WTp: wt_program p)
    (WTs: wt_state p s)
    (STEP: step (Globalenvs.Genv.globalenv p) s tr s') :
    wt_state p s'.
  Proof using Type.
    inversion STEP; subst.
    - inversion WTs; subst.
      destruct WTstate as [WTFN WTCMD WTCONT WTENV STK INTERNAL].
      inversion WTCMD; subst.
      eapply wt_State_intro; [ | exact GLOB ].
      constructor.
      + exact WTFN.
      + exact WTm.
      + eapply wt_cont_Kbind; [exact UNBOUND | exact WTf | exact WTCONT].
      + exact WTENV.
      + exact STK.
      + exact INTERNAL.
    - inversion WTs; subst.
      destruct WTstate as [WTFN WTCMD WTCONT WTENV STK INTERNAL].
      inversion WTCMD; subst.
      assert (POP: with_stack (removelast (ctxt_stack (push_stack tt ctx))) (push_stack tt ctx) = ctx).
      { unfold push_stack.
        apply Ctxt.Facts.ctxt_ext; cbn [ctxt_pure ctxt_internal ctxt_stack ctxt_global with_stack].
        - reflexivity.
        - reflexivity.
        - rewrite removelast_last; reflexivity.
        - reflexivity. }
      assert (NE: exists u0 ul0, ctxt_stack (push_stack tt ctx) = u0 :: ul0).
      { unfold push_stack; cbn [ctxt_stack with_stack].
        destruct (ctxt_stack ctx) as [|h l]; [exists tt, [] | exists h, (l++[tt])]; reflexivity. }
      destruct NE as [u0 [ul0 NE]].
      apply (wt_State_intro p f c_next (Kscope scope_store k) env (locals ++ [nm])
               _ (push_stack tt ctx) t0).
      + refine {| State_wt_function := _; State_wt_cmd := _; State_wt_cont := _;
                  State_wt_env := _; State_wt_stack := _;
                  State_internals := _ |}.
        * exact WTFN.
        * exact WTcont.
        * eapply wt_cont_Kscope_pop; [exact NE | rewrite POP; exact WTCONT].
        * exact WTENV.
        * unfold push_stack; cbn [ctxt_stack with_stack].
          rewrite map_app; cbn [List.map]; rewrite STK; reflexivity.
        * unfold push_stack; cbn [ctxt_internal with_stack]; exact INTERNAL.
      + exact GLOB.
    - inversion WTs; subst.
      destruct WTstate as [WTFN WTCMD WTCONT WTENV STK INTERNAL].
      eapply wt_Returnstate.
      + eapply builtin_wt_value; [exact BUILTIN | exact WTCMD | exact WTENV].
      + eapply resolve_call_preservation; [exact CALLK | exact WTCONT].
      + exact GLOB.
    - inversion WTs; subst.
      destruct WTstate as [WTFN WTCMD WTCONT WTENV STK INTERNAL].
      assert (WTv: wt_value v t) by (eapply builtin_wt_value; [exact BUILTIN | exact WTCMD | exact WTENV]).
      destruct (resolve_seq_preservation RESOLVE WTCONT WTv WTENV)
        as [ctx' [t' [STACK [GLOBEQ [INTERNAL' [WTCMD' [WTCONT' WTENV']]]]]]].
      eapply wt_State_intro.
      + refine {| State_wt_function := _; State_wt_cmd := _; State_wt_cont := _;
                  State_wt_env := _; State_wt_stack := _;
                  State_internals := _ |}.
        * erewrite (glob_ctxt_eq GLOBEQ); exact WTFN.
        * exact WTCMD'.
        * exact WTCONT'.
        * exact WTENV'.
        * rewrite STACK STK ListExt.map_removelast_n; reflexivity.
        * rewrite INTERNAL'; exact INTERNAL.
      + rewrite GLOBEQ; exact GLOB.
    - inversion WTs; subst.
      destruct WTstate as [WTFN WTCMD WTCONT WTENV STK INTERNAL].
      inversion WTCMD; subst.
      + assert (FS2: Globalenvs.Genv.find_symbol (ctxt_global ctx) id_f = Some b).
        { rewrite <- GLOB. exact FIND_SYMB. }
        assert (Efd: fd = AST.Internal fn).
        { assert (FIND_FUNC': Globalenvs.Genv.find_def (ctxt_global ctx) b = Some (AST.Gfun fd)).
          { rewrite <- GLOB. apply Globalenvs.Genv.find_funct_ptr_iff. exact FIND_FUNC. }
          assert (UNFOLD: get_global id_f ctx
                            = match Globalenvs.Genv.find_symbol (ctxt_global ctx) id_f with
                              | Some b' => Globalenvs.Genv.find_def (ctxt_global ctx) b'
                              | None => None
                              end) by reflexivity.
          rewrite UNFOLD FS2 FIND_FUNC' in FINDFN.
          congruence. }
        subst fd.
        assert (GEQ: ctxt_global ctx = ctxt_global (mk_glob_ctxt p)).
        { cbn [ctxt_global mk_glob_ctxt with_global]. symmetry; exact GLOB. }
        assert (GETGLOB: get_global id_f (mk_glob_ctxt p) = Some (AST.Gfun (AST.Internal fn))).
        { unfold get_global in *. rewrite GEQ in FINDFN. exact FINDFN. }
        pose proof (wt_glob_fundef p WTp id_f (AST.Internal fn) GETGLOB) as WTFD.
        eapply wt_Callstate.
        * exact WTFD.
        * eapply wt_call_Internal.
          eapply eval_list_preserves_wt_env; [exact WTENV | exact WT_args | exact EVAL].
        * eapply funsig_Internal.
        * eapply wt_Kcall.
          -- rewrite (mk_glob_ctxt_eq GLOB) in WTFN; exact WTFN.
          -- exact WTENV.
          -- assert (EQ2: with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty)
                             (with_pure (ctxt_pure ctx)
                                (with_stack (List.map (fun _ => tt) locals) (mk_glob_ctxt p))) = ctx).
             { apply Ctxt.Facts.ctxt_ext; cbn [ctxt_pure ctxt_internal ctxt_stack ctxt_global with_pure with_stack to_glob_ctxt with_internal].
               - reflexivity.
               - symmetry; exact INTERNAL.
               - symmetry; exact STK.
               - symmetry; exact GEQ. }
             rewrite EQ2; cbn [fn_signature sig_res]; exact WTCONT.
        * cbn [ctxt_global mk_glob_ctxt with_global]; reflexivity.
      + assert (FS2: Globalenvs.Genv.find_symbol (ctxt_global ctx) id_f = Some b).
        { rewrite <- GLOB. exact FIND_SYMB. }
        assert (Efd: fd = AST.External (AST.EF_external nm sg)).
        { assert (FIND_FUNC': Globalenvs.Genv.find_def (ctxt_global ctx) b = Some (AST.Gfun fd)).
          { rewrite <- GLOB. apply Globalenvs.Genv.find_funct_ptr_iff. exact FIND_FUNC. }
          assert (UNFOLD: get_global id_f ctx
                            = match Globalenvs.Genv.find_symbol (ctxt_global ctx) id_f with
                              | Some b' => Globalenvs.Genv.find_def (ctxt_global ctx) b'
                              | None => None
                              end) by reflexivity.
          rewrite UNFOLD FS2 FIND_FUNC' in FINDFN.
          congruence. }
        subst fd.
        assert (GEQ: ctxt_global ctx = ctxt_global (mk_glob_ctxt p)).
        { cbn [ctxt_global mk_glob_ctxt with_global]. symmetry; exact GLOB. }
        assert (GETGLOB: get_global id_f (mk_glob_ctxt p)
                         = Some (AST.Gfun (AST.External (AST.EF_external nm sg)))).
        { unfold get_global in *. rewrite GEQ in FINDFN. exact FINDFN. }
        pose proof (wt_glob_fundef p WTp id_f (AST.External (AST.EF_external nm sg)) GETGLOB) as WTFD.
        eapply wt_Callstate.
        * exact WTFD.
        * eapply wt_call_external; [exact SIG | ].
          eapply eval_list_preserves_wt_env; [exact WTENV | exact WT_args | exact EVAL].
        * eapply funsig_External; exact SIG.
        * eapply wt_Kcall.
          -- rewrite (mk_glob_ctxt_eq GLOB) in WTFN; exact WTFN.
          -- exact WTENV.
          -- assert (EQ2: with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty)
                             (with_pure (ctxt_pure ctx)
                                (with_stack (List.map (fun _ => tt) locals) (mk_glob_ctxt p))) = ctx).
             { apply Ctxt.Facts.ctxt_ext; cbn [ctxt_pure ctxt_internal ctxt_stack ctxt_global with_pure with_stack to_glob_ctxt with_internal].
               - reflexivity.
               - symmetry; exact INTERNAL.
               - symmetry; exact STK.
               - symmetry; exact GEQ. }
             rewrite EQ2; exact WTCONT.
        * cbn [ctxt_global mk_glob_ctxt with_global]; reflexivity.
    - inversion WTs; subst.
      destruct WTstate as [WTFN WTCMD WTCONT WTENV STK INTERNAL].
      inversion WTCMD; subst.
      eapply wt_State_intro; [ | exact GLOB ].
      constructor.
      + exact WTFN.
      + destruct b; [ exact WTthen | exact WTelse ].
      + exact WTCONT.
      + exact WTENV.
      + exact STK.
      + exact INTERNAL.
    - inversion WTs; subst.
      destruct WTstate as [WTFN WTCMD WTCONT WTENV STK INTERNAL].
      inversion WTCMD; subst.
      eapply wt_State_intro; [ | exact GLOB ].
      constructor.
      + exact WTFN.
      + exact WTcond.
      + eapply wt_cont_Kloop1; [exact WTcond | exact WTbody | exact WTCONT].
      + exact WTENV.
      + exact STK.
      + exact INTERNAL.
    - inversion WTs; subst.
      inversion WTfundef; subst.
      assert (EQsig: sig = fn_signature f) by (inversion SIG; subst; reflexivity).
      subst sig.
      assert (GENV: Globalenvs.Genv.globalenv p
                       = ctxt_global (mk_function_ctxt f.(fn_params) f.(fn_temps) f.(fn_internals) (mk_glob_ctxt p)))
        by (unfold mk_function_ctxt; reflexivity).
      eapply wt_State_intro.
      + refine {| State_wt_function := _; State_wt_cmd := _; State_wt_cont := _;
                  State_wt_env := _; State_wt_stack := _;
                  State_internals := _ |}.
        * erewrite (mk_glob_ctxt_eq GENV); exact WTFUNCTION.
        * exact (wt_fn_cmd WTFUNCTION).
        * eapply wt_cont_other.
          -- unfold mk_function_ctxt; cbn [ctxt_stack with_pure with_stack]; reflexivity.
          -- rewrite (mk_glob_ctxt_eq GENV).
             assert (CTX0: ctx = mk_glob_ctxt p) by exact (glob_ctx_unique p ctx GLOB).
             rewrite <- CTX0; cbn [fn_signature sig_res]; exact WTcont.
        * exact (wt_env_init WTFUNCTION WT_ARGS).
        * unfold mk_function_ctxt; cbn [ctxt_stack with_pure with_stack]; reflexivity.
        * unfold mk_function_ctxt; cbn [ctxt_internal with_pure with_stack mk_glob_ctxt with_global]; reflexivity.
      + exact GENV.
    - inversion WTs; subst.
      inversion WTcont; subst.
      destruct (resolve_seq_preservation
                  RESOLVE WTcont0 WTres WTenv)
        as [ctx' [t' [STACK [GLOBEQ [INTERNAL' [WTCMD' [WTCONT' WTENV']]]]]]].
      eapply wt_State_intro.
      + refine {| State_wt_function := _; State_wt_cmd := _; State_wt_cont := _;
                  State_wt_env := _; State_wt_stack := _;
                  State_internals := _ |}.
        * assert (CTXEQ: ctx = mk_glob_ctxt p) by exact (glob_ctx_unique p ctx GLOB).
          assert (GLOBEQ': Globalenvs.Genv.globalenv p = ctxt_global ctx')
            by (rewrite GLOBEQ; exact GLOB).
          erewrite (mk_glob_ctxt_eq GLOBEQ'), <- CTXEQ; exact WTf.
        * exact WTCMD'.
        * exact WTCONT'.
        * exact WTENV'.
        * rewrite STACK; cbn [ctxt_stack with_pure with_stack to_glob_ctxt with_internal];
            rewrite ListExt.map_removelast_n; reflexivity.
        * rewrite INTERNAL'; reflexivity.
      + rewrite GLOBEQ; cbn [ctxt_global with_pure with_stack to_glob_ctxt with_internal]; exact GLOB.
  Qed.

  (* Lift subject reduction over [step_star] *)
  Theorem step_star_preservation (p: program) (s s': state) tr
    (WTp: wt_program p)
    (WTs: wt_state p s)
    (STAR: step_star (Globalenvs.Genv.globalenv p) s tr s') :
    wt_state p s'.
  Proof using Type.
    induction STAR as [ s | s1 t1 s2 t2 s3 t STEP STAR IH ETrace ].
    - exact WTs.
    - apply IH. exact (step_preservation p s1 s2 t1 WTp WTs STEP).
  Qed.

  (* Initial states are well-typed *)
  Lemma wt_initial_state (p: program) (s0: state)
    (INIT: initial_state p s0) : wt_state p s0.
  Proof using Type.
    inversion INIT as [ge0 f b WT GE0 FIND_SYMB FIND_FUNC MAIN_SIG]; subst.
    apply (wt_Callstate p f [] Kstop emp_state (mk_signature [] t_nat)
             (mk_glob_ctxt p)).
    - apply (wt_glob_fundef p WT p.(prog_main)).
      unfold get_global.
      change (ctxt_global (mk_glob_ctxt p)) with (Globalenvs.Genv.globalenv p).
      rewrite (Prog.Facts.prog_main_is_prog_main p).
      rewrite FIND_SYMB.
      apply (proj1 (Globalenvs.Genv.find_funct_ptr_iff (Globalenvs.Genv.globalenv p) b f)).
      exact FIND_FUNC.
    - destruct f as [fn|ef].
      + inversion MAIN_SIG; subst.
        apply wt_call_Internal.
        match goal with
        | H: List.map snd (fn_params fn) = [] |- _ => rewrite H
        end.
        constructor.
      + inversion MAIN_SIG as [ | ef' sig SIG ]; subst.
        exact (wt_call_external _ _ ef _ [] SIG (List.Forall2_nil _)).
    - exact MAIN_SIG.
    - apply wt_Kstop.
    - reflexivity.
  Qed.

End Wt.

Notation type_cont_call := (@type_cont_call' _ (@type_cont _)).

End Typing.

Module Facts.

Section Wf.

  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).

  Lemma resolve_seq_cont_fun [k: @cont Sm] [env v c' env' k' n c'' env'' k'' n'']
    (RESOLVE1: resolve_seq_cont k env v c' env' k' n)
    (RESOLVE2: resolve_seq_cont k env v c'' env'' k'' n'')
    : c'' = c' /\ env'' = env' /\ k'' = k' /\ n'' = n.
  Proof using Type.
    revert c'' env'' k'' n'' RESOLVE2.
    induction RESOLVE1; intros c'' env'' k'' n'' RESOLVE2;
      inversion RESOLVE2; subst;
      try (edestruct (IHRESOLVE1 _ _ _ _ RES) as (-> & -> & -> & ->));
      auto.
  Qed.

  Lemma resolve_call_cont_fun [k k0 k0': @cont Sm]
    (C1: resolve_call_cont k k0)
    (C2: resolve_call_cont k k0')
    : k0' = k0.
  Proof using Type.
    revert k0' C2.
    induction C1; intros k0' C2; inversion C2; subst; auto;
      match goal with
      | IH: forall _, resolve_call_cont _ _ -> _ = _, H: resolve_call_cont _ _ |- _ =>
          apply IH; exact H
      | H: is_call_cont (Kscope _ _) |- _ => inversion H
      end.
  Qed.

  Lemma resolve_call_cont_not_resolve_seq [k k0: @cont Sm] [env v c'' env'' kt n]
    (C: resolve_call_cont k k0)
    (R: resolve_seq_cont k env v c'' env'' kt n) : False.
  Proof using Type.
    revert env v c'' env'' kt n R.
    induction C; intros env v c'' env'' kt n R.
    - inversion R; subst; inversion CALLK.
    - inversion R; subst; eapply IHC; eassumption.
  Qed.

  Lemma pop_stack_n_length (locals: list Nm) (s: Sm) :
    pop_stack locals s = pop_stack_n (length locals) s.
  Proof using Type. reflexivity. Qed.

End Wf.

End Facts.

Ltac guess_heap_substate :=
  apply (ssrbool.elimT
           (@Algebra.relb_spec _ (Algebra.DecRel.clone _ (@Algebra.Substate _) _) _ _));
  vm_compute; reflexivity.

Ltac guess_wvalid :=
  apply (ssrbool.elimT (weakly_valid_spec _ _));
  vm_compute; reflexivity.

Ltac guess_cmpvalid :=
  apply (ssrbool.elimT (cmp_valid_spec _ _ _));
  vm_compute; reflexivity.

Ltac builtin_step :=
  first
    [ apply: builtin_ret; reflexivity
    | apply: builtin_read_var; [ reflexivity | reflexivity | reflexivity | now constructor ]
    | apply: builtin_write_var; [ reflexivity | reflexivity | reflexivity | now constructor ]
    | apply: builtin_alloc_ptr;
      [ reflexivity | reflexivity | now constructor
      | apply (proj1 (N.leb_le _ _)); vm_compute; reflexivity
      | reflexivity ]
    | apply: builtin_read_ptr; [ reflexivity | reflexivity | now constructor | reflexivity ]
    | apply: builtin_write_ptr; now constructor
    | apply: builtin_shift_fw_ptr; [ reflexivity | reflexivity | now constructor | now guess_wvalid | now guess_wvalid ]
    | apply: builtin_eq_ptr; [ reflexivity | reflexivity | guess_cmpvalid | reflexivity ]
    | apply: builtin_div; [ reflexivity | reflexivity | reflexivity ]
    | apply: builtin_mod; [ reflexivity | reflexivity | reflexivity ]
    ].

Ltac norm_state :=
  match goal with
  | |- Smallstep.star _ _ ?s1 _ _ =>
      let s1' := eval vm_compute in s1 in
      change s1 with s1'
  end.

Ltac one_step :=
  first
    [ apply Smallstep.star_refl
    | eapply Smallstep.star_step with (t1 := Events.E0) (t2 := Events.E0);
      [ first
          [ apply step_bind
          | apply: step_with_var; [ reflexivity | reflexivity ]
          | apply: step_builtin_call_cont; [ now repeat constructor | builtin_step | reflexivity ]
          | apply: step_builtin_seq_cont; [ now repeat constructor | builtin_step | reflexivity ]
          | apply: step_app ; [ reflexivity | vm_compute; reflexivity
                             | vm_compute; reflexivity | now constructor ]
          | apply: step_ifthenelse; reflexivity
          | apply: step_while
          | apply: step_internal_function; [ now repeat constructor | reflexivity | now constructor ]
          | apply: step_return_call_seq; now repeat constructor
          ]
      | auto
      | reflexivity]
    ];
  (try norm_state);
  cbn -[Globalenvs.Genv.globalenv].
