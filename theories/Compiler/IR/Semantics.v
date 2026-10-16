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

From Stdlib Require Import ZArith List.
Import ListNotations.

From compcert.common Require AST Events Globalenvs Smallstep.
From compcert.lib Require Import Integers Maps.
Import Globalenvs(Genv.globalenv, Genv.find_symbol, Genv.find_funct_ptr).

From Corelib Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

From GallinaC.Utils Require Import ListExt CompCertExt.

From GallinaC.Imp Require Heap Store Primitives Intops.
From GallinaC.Imp Require Import Uint32 Addr Heap Store Storable State.

From GallinaC.Compiler.Common Require Import Value CCInj Types.
From GallinaC.Compiler.Common Require Import Semantics.
From GallinaC.Compiler.IR Require Import Cmd Prog Typing.

Local Open Scope separation_scope.

Section Semantics.
  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).

  Definition env := PTree.t (value Pt).

  Definition alloc_global (s: Sm) (g: globdef): option Sm :=
    match g with
    | AST.Gfun _ => Some s
    | AST.Gvar {|
          AST.gvar_info := mkvardef var_type;
          AST.gvar_init := init;
          AST.gvar_readonly := false;
          AST.gvar_volatile := false;
        |} =>
        match value_of_init_data var_type init with
        | Some init_v =>
            match push (store s) (scnt s) init_v with
            | Some (st, sg, _) => mk_state_opt st sg (heap s) (alc s)
            | None => None
            end
        | None => None
        end
    | AST.Gvar _ => None
    end.

  Fixpoint alloc_globals (s: Sm) (gl: list (AST.ident * globdef)): option Sm :=
    match gl with
    | [] => Some s
    | (_, g)::gl =>
        match alloc_global s g with
        | Some s => alloc_globals s gl
        | None => None
        end
    end.

  Definition init_state (p: program): option Sm :=
    alloc_globals emp_state p.(prog_defs).

  Inductive cont: Type :=
  (* 1. To return from the program execution
   * /!\ Remember that even C evaluation is simply CPS to return to a caller *)
  | Kstop:
    cont

  (* 2. To bind the result in a temporary variable *)
  | Kbind:
    forall (b_id: AST.ident)          (* identifier to bind *)
           (c: cmd)                   (* command to execute next *)
           (k: cont)                  (* then continue with k *)
    , cont

  (* 3. To evaluate the condition of a while loop *)
  | Kloop1:
    forall (c_cond: cmd)
           (id_cond: AST.ident)
           (c_body: cmd)
           (id_body: AST.ident)
           (k: cont)
    , cont

  (* 4. To execute the body of a while loop *)
  | Kloop2:
    forall (c_cond: cmd)
           (id_cond: AST.ident)
           (c_body: cmd)
           (id_body: AST.ident)
           (k: cont)
    , cont

  (* 5. As a sub-function call *)
  | Kcall:
    forall (fn: function)             (* calling function f *)
           (e: env)                   (* execution environment of f *)
           (locals: list Nm)  (* stack variables of f *)
           (k: cont)                  (* then continue with k *)
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

  Inductive resolve_seq_cont: cont -> value Pt -> cmd -> cont -> Prop :=
  | resolve_seq_Kbind: forall b_id c_next k v, resolve_seq_cont (Kbind b_id c_next k) v c_next k
  | resolve_seq_Kloop1: forall c_cond id_cond c_body id_body k b,
      resolve_seq_cont
        (Kloop1 c_cond id_cond c_body id_body k)
        (v_bool b)
        (if b then c_body else (c_ret e_tt t_unit))
        (if b then Kloop2 c_cond id_cond c_body id_body k else k)
  | resolve_seq_Kloop2: forall c_cond id_cond c_body id_body k, resolve_seq_cont (Kloop2 c_cond id_cond c_body id_body k) v_tt c_cond (Kloop1 c_cond id_cond c_body id_body k)
  .

  Inductive is_call_cont: cont -> Prop :=
  | call_cont_Kstop: is_call_cont Kstop
  | call_cont_Kcall: forall fn e locals k, is_call_cont (Kcall fn e locals k)
  .

  Definition cont_target (k: cont): option AST.ident :=
    match k with
    | Kbind b_id _ _ => Some b_id
    | Kloop1 _ id_cond _ _ _ => Some id_cond
    | Kloop2 _ _ _ id_body _ => Some id_body
    | Kcall _ _ _ _ => None
    | Kstop => None
    end.

  Definition is_call_contb (k: cont): bool :=
    match k with
    | Kstop | Kcall _ _ _ _ => true
    | _ => false
    end.

  Inductive state: Type :=
  | State:                              (* Execution within a function *)
    forall (fn: function)               (* currently executing function *)
           (c: cmd)                     (* command under consideration *)
           (k: cont)                    (* its continuation -- what to do next *)
           (e: env)                     (* current local environment *)
           (locals: list Nm)    (* List of stack variables *)
           (s: Sm)  (* current memory and register states as viewed by GallinaC *)
    , state
  | Callstate:                          (* Invocation of a function *)
    forall (f: fundef)                  (* function to invoke *)
           (arg: list (value Pt))            (* arguments provided by the caller *)
           (k: cont)                    (* what to do next *)
           (s: Sm)  (* current memory and register states as viewed by GallinaC *)
    , state
  | Returnstate:                        (* Return from a function *)
    forall (v: value Pt)                   (* Return value *)
           (k: cont)                    (* what to do next *)
           (s: Sm)  (* current memory and register states *)
    , state
  .

  Definition state_of_state (s: state): Sm :=
    match s with
    | State _ _ _ _ _ s => s
    | Callstate _ _ _ s => s
    | Returnstate _ _ s => s
    end.

  Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro:
    forall ge b f s0
           (WTp: wt_program p)
           (INITgenv: Genv.globalenv p = ge)
           (INITstate: init_state p = Some s0)
           (FINDmainb: Genv.find_symbol ge (AST.prog_main p) = Some b)
           (FINDmainf: Genv.find_funct_ptr ge b = Some f)
           (MAINsig: funsig f (mk_signature [] t_nat) ),
      initial_state p (Callstate f [] Kstop s0)
  .

  Inductive final_state: state -> Integers.int -> Prop :=
  | final_state_intro: forall r s,
      final_state (Returnstate (v_nat r) Kstop s) (Integers.Int.repr (Z.of_nat r))
  .

  Fixpoint set_params {A: Type} (params: list (AST.ident * A)) (inits: list (value Pt)): env :=
    match params, inits with
    | [], [] => PTree.empty (value Pt)
    | (id, _)::params, v::inits => PTree.set id v (set_params params inits)
    | _, _ => PTree.empty _
    end.

  Definition pop_stack stackspace (s: Sm): option Sm :=
    state_pop_n (Z.to_N stackspace) s.

  (* "Primitive" operations *)
  Inductive builtin: cmd -> genv -> Maps.PTree.t (value Pt) -> list Nm -> Sm -> value Pt -> Sm -> Prop :=
  | builtin_ret: forall e t genv env locals s v
                        (EVAL: eval e env = Some v)
                        (WT: wt_value v t)
    , builtin
        (c_ret e t) genv env locals s v s

  | builtin_read_var: forall n t genv env locals s v nm
                             (DEREF: List.nth_error locals n = Some nm)
                             (LOOKUP: lookup (store s) nm = Some (encode v))
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

  | builtin_alloc_ptr: forall e_size t e_init id_ptr id_count id_init genv env locals s ptr hp' alc' v_size v_init
                              (EVAL_SIZE: eval e_size env = Some (v_ofst v_size))
                              (EVAL_INIT: eval e_init env = Some v_init)
                              (WT: wt_value v_init t)
                              (BND: (v_size <= alloc_max_size)%N)
                              (ALLOC_GC: alloc (heap s) (alc s) v_size (encode v_init) = Some (hp', alc', ptr))
    , builtin
        (c_alloc_ptr e_size t e_init id_ptr id_count id_init) genv env locals
        s
        (v_ptr ptr)
        (state_alloc s ALLOC_GC)
  | builtin_read_ptr: forall e_ptr t genv env locals s v_read v_ptr
                             (EVAL: eval e_ptr env = Some (Value.v_ptr v_ptr))
                             (LOOKUP: lookup (heap s) v_ptr = Some (encode v_read))
                             (WT: wt_value v_read t)
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
  | builtin_free_ptr: forall e_ptr genv env locals s hp' ptr
                             (EVAL: eval e_ptr env = Some (Value.v_ptr ptr))
                             (FREE_GC: free (heap s) ptr = Some hp')
    , builtin
        (c_free_ptr e_ptr) genv env locals
        s
        v_tt
        (state_free s FREE_GC)

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
  | step_bind: forall ge f id_b t_b c_b c_c t_c k env locals s,
      step
        ge
        (State f (c_bind id_b t_b c_b c_c t_c) k env locals s)
        Events.E0
        (State f c_b (Kbind id_b c_c k) env locals s)

  (* N/A | step_builtin_(call|sep)_cont *)
  | step_builtin_call_cont: forall ge f c k env locals s v s' s''
                                   (CONTcall: is_call_cont k)
                                   (BUILTIN: builtin c ge env locals s v s')
                                   (POPSTACK: pop_stack f.(fn_extra).(fn_stackspace) s' = Some s'')
    , step
        ge
        (State f c k env locals s)
        Events.E0
        (Returnstate v k s'')
  | step_builtin_seq_cont: forall ge f c k env locals s c_next k' target_id v s'
                                  (SEQtarget: seq_cont_target k target_id)
                                  (SEQresolve: resolve_seq_cont k v c_next k')
                                  (BUILTIN: builtin c ge env locals s v s')
    , step
        ge
        (State f c k env locals s)
        Events.E0
        (State f c_next k' (PTree.set target_id v env) locals s')

  (* step_call | step_app *)
  | step_app: forall
      ge fn id t_out args k env locals s v_args b fd
      (EVALargs: map_opt (fun e => eval e env) (List.map fst args) = Some v_args)
      (FINDsymb: Globalenvs.Genv.find_symbol ge id = Some b)
      (FINDfunct: Globalenvs.Genv.find_funct_ptr ge b = Some fd)
      (CONTseq: is_seq_cont k),
      step
        ge
        (State fn (c_app id t_out args) k env locals s)
        Events.E0
        (Callstate fd v_args (Kcall fn env locals k) s)

  (* step_tailcall | N/A *)
  | step_tailapp: forall
      ge fn f_id t_out args k env locals s fd v_args s' b
      (EVALargs: map_opt (fun e => eval e env) (List.map fst args) = Some v_args)
      (FINDsymb: Globalenvs.Genv.find_symbol ge f_id = Some b)
      (FINDfunct: Globalenvs.Genv.find_funct_ptr ge b = Some fd)
      (POPSTACK: pop_stack fn.(fn_extra).(fn_stackspace) s = Some s')
      (CONTcall: is_call_cont k)
    , step
        ge
        (State fn (c_app f_id t_out args) k env locals s)
        Events.E0
        (Callstate fd v_args k s')

  (* step_ifthenelse | step_ifthenelse *)
  | step_ifthenelse: forall ge fn e_i c_t c_e t k env locals s b
      (EVALif: eval e_i env = Some (v_bool b)),
      step
        ge
        (State fn (c_if e_i c_t c_e t) k env locals s)
        Events.E0
        (State fn (if b then c_t else c_e) k env locals s)

  (* step_loop | step_while *)
  | step_while: forall ge fn c_cond id_cond c_body id_body k env locals s,
      step
        ge
        (State fn (c_while c_cond id_cond c_body id_body) k env locals s)
        Events.E0
        (State fn c_cond (Kloop1 c_cond id_cond c_body id_body k) env locals s)

  (* step_internal_function | step_internal_functions *)
  | step_internal_function: forall ge fn args k locals s s' env st sg
      (WTargs: Forall2 (wt_value (Pt := Pt)) args (List.map snd fn.(fn_params)))
      (PARAMS: set_params fn.(fn_params) args = env)
      (LOCALS: stack_block_alloc (encode (v_tt: value Pt)) (Z.to_N fn.(fn_extra).(fn_stackspace))
                 (store s) (scnt s) = Some (st, sg, locals))
      (STACKBL: mk_state_opt st sg (heap s) (alc s) = Some s')
      (CONTcall: is_call_cont k),
      step
        ge
        (Callstate (AST.Internal fn) args k s)
        Events.E0
        (State fn fn.(fn_body) k env locals s')

  (* step_return | N/A *)
  (* return from a function into a binding *)
  | step_return_call_seq: forall ge v fn env locals k s c_next k' target_id
                                 (SEQtarget: seq_cont_target k target_id)
                                 (SEQresolve: resolve_seq_cont k v c_next k'),
      step
        ge
        (Returnstate v (Kcall fn env locals k) s)
        Events.E0
        (State fn c_next k' (PTree.set target_id v env) locals s)
.

  Definition semantics (p : program) :=
    Smallstep.Semantics step (initial_state p) final_state (Globalenvs.Genv.globalenv p).

End Semantics.

Arguments Kstop {Sm}.
Arguments state {Sm}.

Section Typing.
  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).

  Record wt_env (f: function) (ty_env: Maps.PTree.t (type * bool)) (val_env: @env Sm): Prop :=
    {
      wt_val_env: forall var_id t,
        In (var_id,t) (f.(fn_params) ++ f.(fn_temps)) ->
        exists t,
          match PTree.get var_id val_env with
          | Some v => wt_value v t \/ (PTree.get var_id ty_env = Some (t,true))
          | None => PTree.get var_id ty_env = Some (t, false)
          end;
      wv_ty_env: forall var_id t b, PTree.get var_id ty_env = Some (t, b) -> (if b then exists v, PTree.get var_id val_env = Some v /\ wt_value v t else PTree.get var_id val_env = None) /\ In (var_id,t) (f.(fn_params) ++ f.(fn_temps));
    }.

  Inductive wt_cont_call: ctxt Empty_set Empty_set Empty_set fundef vardef -> @cont Sm -> type -> Prop :=
  | wt_Kstop: forall ctx, wt_cont_call ctx Kstop t_nat
  | wt_Kcall: forall ctx f env locals k t ty_env int_env
                     (WTFN: wt_function ctx f)
                     (WTENV: wt_env f ty_env env)
                     (FINT: function_internals (with_internal int_env (with_pure ty_env (with_stack (List.map (fun _ => tt) locals) ctx))) f)
                     (WTk: wt_cont (with_internal int_env (with_pure ty_env (with_stack (List.map (fun _ => tt) locals) ctx))) k t),
      wt_cont_call ctx (Kcall f env locals k) t

  with wt_cont: ctxt (type * bool) (type * bool) unit fundef vardef -> @cont Sm -> type -> Prop :=
  | wt_cont_Kbind: forall ctx id c k t_b t_c b
                          (BINDABLE: get_pure id ctx = Some (t_b, b))
                          (WTCMD: wt_cmd (set_pure id (t_b, true) ctx) c t_c)
                          (WTk: wt_cont ctx k t_c),
      wt_cont ctx (Kbind id c k) t_b
  | wt_cont_Kloop1: forall ctx c_cond id_cond c_body id_body k b_cond b_unit
                           (WTCOND: wt_cmd ctx c_cond t_bool)
                           (WTBODY: wt_cmd ctx c_body t_unit)
                           (WTk: wt_cont ctx k t_unit)
                           (GETcond: get_internal id_cond ctx = Some (t_bool, b_cond))
                           (GETbody: get_internal id_body ctx = Some (t_unit, b_unit)),
      wt_cont ctx (Kloop1 c_cond id_cond c_body id_body k) t_bool
  | wt_cont_Kloop2: forall ctx c_cond id_cond c_body id_body k b_cond b_unit
                           (WTCOND: wt_cmd ctx c_cond t_bool)
                           (WTBODY: wt_cmd ctx c_body t_unit)
                           (WTk: wt_cont ctx k t_unit)
                           (GETcond: get_internal id_cond ctx = Some (t_bool, b_cond))
                           (GETbody: get_internal id_body ctx = Some (t_unit, b_unit)),
      wt_cont ctx (Kloop2 c_cond id_cond c_body id_body k) t_unit
  | wt_cont_other: forall ctx k tret
                          (WTKCALL: wt_cont_call (to_glob_ctxt ctx) k tret),
      wt_cont ctx k tret
  .

  Record wt_State (f: function) (c: cmd) (k: @cont Sm) (e: @env Sm) (locals: list Nm) (s: @Sm) (ctx: ctxt (type * bool) (type * bool) unit fundef vardef) (t: type) : Prop :=
    {
      State_wt_function: wt_function (to_glob_ctxt ctx) f;
      State_wt_cmd: wt_cmd ctx c t;
      State_wt_cont: wt_cont ctx k t;
      State_wt_env: wt_env f ctx.(ctxt_pure) e;
      State_function_internals: function_internals ctx f;
    }.

  Inductive wt_state (p: program): state -> Prop :=
  | wt_State_intro: forall f c k e locals s ctx t
                     (WTp: wt_program p)
                     (WTstate: wt_State f c k e locals s ctx t)
                     (EGLOB: Ctxt.ctxt_global ctx = Ctxt.ctxt_global (mk_glob_ctxt p))
    , wt_state p (State f c k e locals s)
  | wt_Callstate: forall f args k s sig ctx
                         (WTp: wt_program p)
                         (WTfundef: wt_fundef (mk_glob_ctxt p) f)
                         (WTargs: wt_fundef_call args f)
                         (WTcont: wt_cont ctx k sig.(sig_res))
                         (SIG: funsig f sig)
                         (EGLOB: Ctxt.ctxt_global ctx = Ctxt.ctxt_global (mk_glob_ctxt p))
    , wt_state p (Callstate f args k s)
  | wt_Returnstate: forall v k s t ctx
                           (WTp: wt_program p)
                           (WTres: wt_value v t)
                           (WTcont: wt_cont ctx k t)
                           (EGLOB: Ctxt.ctxt_global ctx = Ctxt.ctxt_global (mk_glob_ctxt p))
    , wt_state p (Returnstate v k s)
  .

End Typing.

Arguments wt_val_env {Sm} [f ty_env val_env]: rename.
Arguments wv_ty_env {Sm} [f ty_env val_env]: rename.

Module Facts.

  Lemma cont_target_seq_cont_target_Some [Sm: State.type]: forall k target_id, cont_target k = (Some target_id) -> @seq_cont_target Sm k target_id.
  Proof.
    induction k; intros target_id CT;
      try (inversion CT);
      subst;
      now constructor.
  Qed.

  Lemma cont_target_seq_cont_target_None [Sm: State.type]: forall k, cont_target k = None -> forall target_id, ~@seq_cont_target Sm k target_id.
  Proof.
    induction k; intros CT;
      try (inversion CT; subst);
      intros target_id ST;
      inversion ST.
  Qed.

  Lemma seq_cont_target_cont_target [Sm: State.type]: forall k target_id, @seq_cont_target Sm k target_id -> cont_target k = (Some target_id).
    intros k target_id ST;
      inversion ST; subst; reflexivity.
  Qed.

  Lemma call_cont_target [Sm: State.type] [k]
    (CONTcall: @is_call_cont Sm k)
    : cont_target k = None.
  Proof.
    now destruct CONTcall.
  Qed.

End Facts.

(* Tactics to reduce program states - don't include all cases, only used in the examples *)

Ltac read_var_step :=
  lazymatch goal with
  | |- builtin (c_read_var ?n _) _ _ ?locals ?s _ _ =>
      let r := eval vm_compute in
        (match List.nth_error locals n with
         | Some nm => lookup (store s) nm
         | None => None
         end) in
      lazymatch r with
      | Some v_tt => eapply builtin_read_var with (v := v_tt)
      | Some (v_bool ?b) => eapply builtin_read_var with (v := v_bool b)
      | Some (v_nat ?k) => eapply builtin_read_var with (v := v_nat k)
      | Some (v_ofst ?o) => eapply builtin_read_var with (v := v_ofst o)
      | Some (v_ptr ?p) => eapply builtin_read_var with (v := v_ptr p)
      end;
      [ reflexivity | reflexivity | now constructor ]
  end.

Ltac builtin_step :=
  first
    [ apply: builtin_ret; [ reflexivity | now constructor ]
    | read_var_step
    | apply: builtin_write_var; [ reflexivity | reflexivity | reflexivity | now constructor ]
    ].

Ltac in_defs :=
  repeat (hnf; first [ left; reflexivity | right ]).

Ltac call_step :=
  lazymatch goal with
  | |- step (Globalenvs.Genv.globalenv (Common.Prog.program_of_program ?q)) (State _ (c_app ?id _ _) _ _ _ _) _ _ =>
      let WTp := fresh "WTp" in
      assert (WTp: wt_program q) by (apply: (elimT (type_program_spec q)); reflexivity);
      let IN := fresh "IN" in
      eassert (IN: In (id, AST.Gfun _) (AST.prog_defs q)) by in_defs;
      lazymatch type of IN with
      | In (_, AST.Gfun ?f_def) _ =>
          let DEF := fresh "DEF" in
          assert (DEF: Maps.PTree.get id (AST.prog_defmap q) = Some (AST.Gfun f_def))
            by exact (Maps.PTree_Properties.of_list_norepet _ _ _
                        (proj1 (ListExt.SBinds_list_norepet _) (Common.Prog.wt_prog_defs_sbinds WTp))
                        IN);
          let blk := fresh "b" in
          let SYMB := fresh "SYMB" in
          let FDEF := fresh "FDEF" in
          destruct (proj1 (Globalenvs.Genv.find_def_symbol _ _ _) DEF) as (blk & SYMB & FDEF);
          first
            [ eapply step_app with (b := blk) (fd := f_def);
                [ reflexivity | exact SYMB
                | exact (proj2 (Globalenvs.Genv.find_funct_ptr_iff _ _ _) FDEF) | now constructor ]
            | eapply step_tailapp with (b := blk) (fd := f_def);
                [ reflexivity | exact SYMB
                | exact (proj2 (Globalenvs.Genv.find_funct_ptr_iff _ _ _) FDEF)
                | reflexivity | now constructor ] ]
      end
  end.

Ltac one_step :=
  first
    [ apply Smallstep.star_refl
    | eapply Smallstep.star_step with (t1 := Events.E0) (t2 := Events.E0);
      [ first
          [ apply step_bind
          | apply: step_builtin_call_cont; [ now repeat constructor | builtin_step | reflexivity ]
          | apply: step_builtin_seq_cont; [ now repeat constructor | now repeat constructor | builtin_step ]
          | call_step
          | apply: step_ifthenelse; reflexivity
          | apply step_while
          | apply: step_internal_function;
              [ now repeat constructor | reflexivity | reflexivity | reflexivity | now constructor ]
          | apply: step_return_call_seq; [ now repeat constructor | now repeat constructor ]
          ]
      | auto
      | reflexivity ]
    ];
  (try norm_state); cbn -[Globalenvs.Genv.globalenv].
