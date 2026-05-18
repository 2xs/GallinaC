From Stdlib Require Import Psatz Arith NArith ZArith Bool.

From GallinaC.Utils Require Import ListExt PTreeExt.
From GallinaC.Imp Require Export Monad Primitives Pointer Intops Uint32 Uintptr.
Import Unsigned.Notations.
From GallinaC.Compiler.Common Require Export Types Ctxt Expr CCInj.
From GallinaC.Compiler.Deep Require Import Cmd Prog OpSem(state, step, cont) Typing.
Import OpSem.Typing(wt_state).

From Corelib Require Derive.

Local Open Scope program_scope.

Local Obligation Tactic := idtac.

Fixpoint type_depth (t: type): nat :=
  match t with
  | t_unit => 1
  | t_bool => 1
  | t_nat => 1
  | t_ofst => 1
  | t_ptr => 1
  | t_fun t_args t_out =>
      S ((List.fold_right Nat.add 0 (List.map type_depth t_args)) + (type_depth t_out))
  end.

Lemma type_depth_pos: forall t, 1 <= type_depth t.
Proof.
  induction t; cbn; lia.
Qed.

Section State.
  Context [St: Store.Store].
  Context [Hp: Heap.Heap].

  Fixpoint denote_type_list (denote: type -> Type) (tl: list type) (tout: Type): Type :=
    match tl with
    | [] => Monad.program (State St Hp) tout
    | t::tl => (denote t) -> (denote_type_list denote tl tout)
    end.

  Fixpoint denote_type (t: type) : Type :=
    match t with
    | t_unit => unit
    | t_bool => bool
    | t_nat => nat
    | t_ofst => N.t
    | t_ptr => Pointer.t
    | t_fun t_args t_out => denote_type_list denote_type t_args (denote_type t_out)
    end.

  Definition denote_type_memval {t: type}: Ground t -> Memval.MemStorable :=
    match t with
    | t_unit => fun _ => Memval.StorableUnit.unit_storable
    | t_bool => fun _ => Memval.StorableBool.bool_storable
    | t_nat => fun _ => Memval.StorableNat.nat_storable
    | t_ofst => fun _ => Memval.StorableOfst.ofst_storable
    | t_ptr => fun _ => Memval.StorablePtr.ptr_storable
    | t_fun ti to =>
        fun GROUND =>
        match ground_nonground_exclude _ GROUND (nonground_t_fun ti to) with
        end
    end.

  Lemma denote_types_agree: forall {t: type} (GROUND: Ground t), denote_type t = Memval.obj (denote_type_memval GROUND).
  Proof using St Hp.
    destruct t; intros; cbn; try reflexivity.
    exfalso; apply (ground_nonground_exclude _ GROUND ltac:(constructor)).
  Qed.

  Definition add_to_denote_ctxt (A: Type) (_: positive) (x: type * bool): Type :=
    match x with
    | (t, b) => if b then A * (denote_type t) else A
    end.

  Fixpoint denote_map' [A: Type] (denote: A -> Type) (ctx: Maps.PTree.tree' A): Type :=
    match ctx with
    | Maps.PTree.Node001 r => denote_map' denote r
    | Maps.PTree.Node010 a => denote a
    | Maps.PTree.Node011 a r => denote a * (denote_map' denote r)
    | Maps.PTree.Node100 l => denote_map' denote l
    | Maps.PTree.Node101 l r => denote_map' denote l * denote_map' denote r
    | Maps.PTree.Node110 l a => denote_map' denote l * denote a
    | Maps.PTree.Node111 l a r => denote_map' denote l * denote a * denote_map' denote r
    end.

  Definition denote_map [A: Type] (denote: A -> Type) (ctx: Maps.PTree.t A): Type :=
    match ctx with
    | Maps.PTree.Empty => unit
    | Maps.PTree.Nodes ctx => denote_map' denote ctx
    end.

  Definition denote_map_lookup [A: Type] (denote: A -> Type)
    {m: Maps.PTree.t A}:
    forall {id} {a}
           (GET: Maps.PTree.get id m = Some a)
           (d_m: denote_map denote m),
      denote a.
  Proof using St Hp.
    induction m using Maps.PTree.tree_ind; [ intros id a GET; discriminate GET | ].
    intros id a GET d_m.
    rewrite Maps.PTree.gNode in GET.
    destruct id.
    - eapply IHm0; [ exact GET | ].
      destruct l, o, r; cbn in d_m;
        try (now constructor);
        try (exact (snd d_m));
        try (exact d_m).
    - eapply IHm; [ exact GET | ].
      destruct l, o, r; cbn in d_m;
        try (now constructor);
        try (exact (fst d_m));
        try (exact (fst (fst d_m)));
        try (exact d_m).
    - subst o.
      destruct l, r; cbn in d_m.
      exact d_m.
      exact (fst d_m).
      exact (snd d_m).
      exact (snd (fst d_m)).
  Defined.

  Definition denote_map_of_lookup [A: Type] (denote: A -> Type)
    (m: Maps.PTree.t A)
    (lookup: forall id a, Maps.PTree.get id m = Some a -> denote a)
    : denote_map denote m.
  Proof using St Hp.
    revert lookup.
    induction m using Maps.PTree.tree_ind; intros lookup.
    - exact tt.
    - assert (lookup_l: forall id a, Maps.PTree.get id l = Some a -> denote a).
      { intros id a GET. apply (lookup (id~0)%positive a). rewrite Maps.PTree.gNode; assumption. }
      assert (lookup_r: forall id a, Maps.PTree.get id r = Some a -> denote a).
      { intros id a GET. apply (lookup (id~1)%positive a). rewrite Maps.PTree.gNode; assumption. }
      assert (lookup_h: forall a, o = Some a -> denote a).
      { intros a EQ. apply (lookup xH a). rewrite Maps.PTree.gNode; assumption. }
      specialize (IHm lookup_l); specialize (IHm0 lookup_r).
      clear lookup lookup_l lookup_r.
      destruct l, o as [ a_o | ], r; cbn in *;
        first
          [ exact tt
          | exact (lookup_h a_o eq_refl)
          | exact IHm
          | exact IHm0
          | exact (IHm, IHm0)
          | exact (lookup_h a_o eq_refl, IHm0)
          | exact (IHm, lookup_h a_o eq_refl)
          | exact (IHm, lookup_h a_o eq_refl, IHm0)
          ].
  Defined.

  Definition denote_map_set [A: Type] (denote: A -> Type)
    (i: positive) (a: A) (d_a: denote a)
    (m: Maps.PTree.t A) (d_m: denote_map denote m)
    : denote_map denote (Maps.PTree.set i a m).
  Proof using St Hp.
    apply (denote_map_of_lookup denote (Maps.PTree.set i a m)).
    intros id b GET.
    destruct (Pos.eq_dec id i) as [ EQ | NE ].
    - subst id.
      rewrite Maps.PTree.gss in GET.
      injection GET as <-.
      exact d_a.
    - rewrite Maps.PTree.gso in GET by assumption.
      exact (denote_map_lookup denote GET d_m).
  Defined.

  Fixpoint denote_pure_ctxt' (ctx: Maps.PTree.tree' (type * bool)): Type :=
    match ctx with
    | Maps.PTree.Node001 r => denote_pure_ctxt' r
    | Maps.PTree.Node010 (t,true) => denote_type t
    | Maps.PTree.Node010 (_,false) => unit
    | Maps.PTree.Node011 (t,true) r => denote_type t * (denote_pure_ctxt' r)
    | Maps.PTree.Node011 (_,false) r => denote_pure_ctxt' r
    | Maps.PTree.Node100 l => denote_pure_ctxt' l
    | Maps.PTree.Node101 l r => denote_pure_ctxt' l * denote_pure_ctxt' r
    | Maps.PTree.Node110 l (t,true) => denote_pure_ctxt' l * denote_type t
    | Maps.PTree.Node110 l (_,false) => denote_pure_ctxt' l
    | Maps.PTree.Node111 l (t,true) r => denote_pure_ctxt' l * denote_type t * denote_pure_ctxt' r
    | Maps.PTree.Node111 l (_,false) r => denote_pure_ctxt' l * denote_pure_ctxt' r
    end.

  Definition denote_pure_ctxt (ctx: map_ctxt (type * bool)): Type :=
    match ctx with
    | Maps.PTree.Empty => unit
    | Maps.PTree.Nodes ctx => denote_pure_ctxt' ctx
    end.

  Fixpoint denote_stack_ctxt (ctx: list unit): Type :=
    match ctx with
    | [] => unit
    | tt::ctx => (denote_stack_ctxt ctx * @Store.name St)%type
    end.

  Definition denote_globdef (g: globdef): Type :=
    match g with
    | AST.Gfun (AST.Internal fn) => denote_type (t_fun (List.map snd fn.(fn_params)) fn.(fn_return))
    | AST.Gfun (AST.External ef) =>
        match Facts.ef_sig_dec ef with
        | Some sig => denote_type (t_fun sig.(sig_args) sig.(sig_res))
        | None => Empty_set
        end
    | AST.Gvar {| AST.gvar_info := t; |} => denote_type t.(var_type)
    end.

  Definition denote_glob_ctxt (ctx: genv): Type :=
    denote_map denote_globdef (Globalenvs.Genv.genv_defs ctx).

  Definition denote_ctxt (ctx: ctxt (type * bool) unit fundef vardef): Type :=
    (denote_pure_ctxt ctx * denote_stack_ctxt ctx.(ctxt_stack) * denote_glob_ctxt ctx.(ctxt_global))%type.

  Definition denote_pure_ctxt_lookup:
    forall {ctx: map_ctxt (type * bool)} {v t}
    (GET: Maps.PTree.get v ctx = Some (t, true))
    (env: denote_pure_ctxt ctx),
      denote_type t.
  Proof using St Hp.
    induction ctx using Maps.PTree.tree_ind; [ intros; discriminate | ].
    intros v t GET env.
    rewrite Maps.PTree.gNode in GET.
    destruct v.
    - eapply IHctx0; [ apply GET | ].
      destruct l, o as [ [ t' b' ] | ], r; cbn in *;
        try (now constructor);
        try (exact env);
        try (exact (snd env));
        try (destruct b'; first [ exact env | exact (snd env) ] ).
    - eapply IHctx; [ apply GET | ].
      destruct l, o as [ [ t' b' ] | ], r; cbn in *;
        try (now constructor);
        try (exact env);
        try (exact (fst env));
        try (destruct b'; first [ exact env | exact (fst env) | exact (fst (fst env)) ]).
    - subst.
      destruct l, r; cbn in *.
      exact env.
      exact (fst env).
      exact (snd env).
      exact (snd (fst env)).
  Defined.

  Definition denote_pure_ctxt_set {ctx: map_ctxt (type * bool)}: forall
      {v t}
      (GET: Maps.PTree.get v ctx = Some (t, false))
      (env: denote_pure_ctxt ctx)
      (x: denote_type t),
      denote_pure_ctxt (Maps.PTree.set v (t, true) ctx).
  Proof using St Hp.
    induction ctx using Maps.PTree.tree_ind; [ intros v t GET; discriminate GET | ].
    intros.
    rewrite Maps.PTree.gNode in GET.
    destruct v.
    - destruct l, o as [ [ t' [ | ] ] | ], r;
        first
          [ now apply IHctx0
          | exact (fst env, IHctx0 v t GET (snd env) x)
          | exact (env, IHctx0 v t GET tt x)
          ].
    - destruct l, o as [ [ t' [ | ] ] | ], r;
        first
          [ now apply IHctx
          | exact (IHctx v t GET tt x, env)
          | exact (IHctx v t GET tt x, fst env, snd env)
          | exact (IHctx v t GET (fst env) x, snd env)
          | exact (IHctx v t GET (fst (fst env)) x, snd (fst env), snd env) ].
    - subst.
      destruct l, r; cbn.
      exact x.
      exact (x, env).
      exact (env, x).
      exact (fst env, x, snd env).
  Defined.

  Definition denote_stack_ctxt_lookup
    {n: nat}:
    forall {ctx: list unit}
           (GET: List.nth_error ctx n = Some tt)
           (env: denote_stack_ctxt ctx)
    , @Store.name St.
  Proof using St Hp.
    induction n; destruct ctx as [ | [ ] ctx ]; try discriminate; cbn.
    intros _ [ _ nm ]; exact nm.
    intros GET [ env _ ].
    apply (IHn ctx GET env).
  Defined.

  Definition denote_stack_ctxt_push
    {ctx: list unit}:
    forall
      (env: denote_stack_ctxt ctx)
      (nm: @Store.name St),
      denote_stack_ctxt (ctx++[tt]).
  Proof using St.
    induction ctx as [ | [ ] ctx ]; cbn; intros.
    - exact (tt, nm).
    - split; [ exact (IHctx (fst env) nm) | exact (snd env) ].
  Defined.

  Definition denote_glob_ctxt_lookup_gdef
    {ctx: genv}:
    forall {b} {gdef}
           (GET: Globalenvs.Genv.find_def ctx b = Some gdef)
           (env: denote_glob_ctxt ctx)
    , denote_globdef gdef.
  Proof using St Hp.
    unfold Globalenvs.Genv.find_def, denote_glob_ctxt;
      destruct ctx as [ F0 F1 ctx F2 F3 F4 F5 ];
      cbn in *;
      clear F0 F1 F2 F3 F4 F5.
    induction ctx using Maps.PTree.tree_ind; [ discriminate | cbn; intros ].
    rewrite Maps.PTree.gNode in GET.
    destruct b.
    - eapply IHctx0; [ exact GET | ].
      destruct l, o, r;
        try (now constructor);
        try (exact (snd env));
        try (exact env).
    - eapply IHctx; [ exact GET | ].
      destruct l, o, r; cbn in *;
        try (now constructor);
        try (exact (fst env));
        try (exact (fst (fst env)));
        try (exact env).
    - subst o.
      destruct l, r.
      exact env.
      exact (fst env).
      exact (snd env).
      exact (snd (fst env)).
  Defined.

  Definition denote_ctxt_lookup_pure
    {ctx: ctxt (type * bool) unit fundef vardef} {v t}
    (GET: get_pure v ctx = Some (t, true))
    (env: denote_ctxt ctx) : denote_type t :=
    denote_pure_ctxt_lookup GET (fst (fst env)).

  Definition denote_ctxt_set_pure
    {ctx: ctxt (type * bool) unit fundef vardef} {v t}
    (GET: get_pure v ctx = Some (t, false))
    (env: denote_ctxt ctx)
    (x: denote_type t)
    : denote_ctxt (set_pure v (t, true) ctx) :=
    (denote_pure_ctxt_set GET (fst (fst env)) x, (snd (fst env)), snd env).

  Definition denote_ctxt_lookup_stack
    {n: nat}
    {ctx: ctxt (type * bool) unit fundef vardef}
    (GET: List.nth_error (ctxt_stack ctx) n = Some tt)
    (env: denote_ctxt ctx): @Store.name St :=
    denote_stack_ctxt_lookup GET (snd (fst env)).

  Definition denote_ctxt_push_stack
    {ctx: ctxt (type * bool) unit fundef vardef}
    (env: denote_ctxt ctx)
    (nm: @Store.name St)
    : denote_ctxt (push_stack tt ctx) :=
    (fst (fst env), denote_stack_ctxt_push (snd (fst env)) nm, snd env).

  Definition denote_ctxt_lookup_global
    {b: Values.block} {gdef: globdef}
    {ctx: ctxt (type * bool) unit fundef vardef}
    (GET: get_global b ctx = Some gdef)
    (env: denote_ctxt ctx)
    : denote_globdef gdef.
    unfold get_global in GET.
    destruct (Globalenvs.Genv.find_symbol (ctxt_global ctx) b); [ | discriminate ].
    exact (denote_glob_ctxt_lookup_gdef GET (snd env)).
  Defined.

  Fixpoint denote_expr
    {ctx: map_ctxt (type * bool)} {e: expr} {t: type}
    (WT: wt_expr ctx e t)
    (env: denote_pure_ctxt ctx) :
    denote_type t :=
    match WT in wt_expr _ e t return denote_type t with
    | wt_var var_id t GET GROUND =>
        denote_pure_ctxt_lookup GET env
    | wt_tt => tt
    | wt_bool b => b
    | wt_nat n _ => n
    | wt_ofst o _ => o
    | wt_nullptr => Pointer.NULL
    | wt_neg WT => negb (denote_expr WT env)
    | wt_plus WTl WTr => (denote_expr WTl env + denote_expr WTr env)%int
    | wt_nat_eq WTl WTr => (denote_expr WTl env =? denote_expr WTr env)
    end.

  Definition denote_value (v: Value.value) : denote_type (Value.type_of_value v) :=
    match v with
    | Value.v_tt => tt
    | Value.v_bool b => b
    | Value.v_nat n => n
    | Value.v_ofst o => o
    | Value.v_ptr p => p
    end.

  Definition convert_eq [A B: Type] (EQ: A = B) (a : A) : B :=
    match EQ with eq_refl => a end.

  Definition denote_value_typed {v t} (WT: Value.wt_value v t) : denote_type t :=
    convert_eq (f_equal denote_type (Value.Facts.type_of_value_complete WT)) (denote_value v).

  Definition denote_pure_ctxt_of_lookup
    (ctx: map_ctxt (type * bool))
    (lookup: forall id t, Maps.PTree.get id ctx = Some (t, true) -> denote_type t)
    : denote_pure_ctxt ctx.
  Proof using St Hp.
    revert lookup.
    induction ctx using Maps.PTree.tree_ind; intros lookup.
    - exact tt.
    - assert (lookup_l: forall id t, Maps.PTree.get id l = Some (t, true) -> denote_type t).
      {
        intros id t Hget.
        apply (lookup (id~0)%positive t).
        rewrite Maps.PTree.gNode; exact Hget.
      }
      assert (lookup_r: forall id t, Maps.PTree.get id r = Some (t, true) -> denote_type t).
      {
        intros id t Hget.
        apply (lookup (id~1)%positive t).
        rewrite Maps.PTree.gNode; exact Hget.
      }
      specialize (IHctx lookup_l).
      specialize (IHctx0 lookup_r).
      assert (lookup_h: forall t, o = Some (t, true) -> denote_type t).
      {
        intros t Heq.
        apply (lookup xH t).
        rewrite Maps.PTree.gNode; cbn; exact Heq.
      }
      clear lookup lookup_l lookup_r.
      destruct l, o as [ [ t_o [ | ] ] | ], r; cbn in *;
        first
          [ exact tt
          | exact (lookup_h t_o eq_refl)
          | exact IHctx
          | exact IHctx0
          | exact (IHctx, IHctx0)
          | exact (lookup_h t_o eq_refl, IHctx0)
          | exact (IHctx, lookup_h t_o eq_refl)
          | exact (IHctx, lookup_h t_o eq_refl, IHctx0)
          ].
  Defined.

  Definition denote_pure_ctxt_of_env
    {f: function} {ty_env: map_ctxt (type * bool)} {val_env: map_ctxt Value.value}
    (WT: OpSem.Typing.wt_env f ty_env val_env)
    : denote_pure_ctxt ty_env :=
    denote_pure_ctxt_of_lookup ty_env (fun id t Hget =>
      match OpSem.Typing.wv_ty_env _ _ _ WT id t true Hget with
      | (existT2 _ _ _ _ Hwt, _) => denote_value_typed Hwt
      end).

  Fixpoint denote_stack_ctxt_of_locals (locals: list (@Store.name St))
    : denote_stack_ctxt (List.map (fun _: @Store.name St => tt) locals) :=
    match locals with
    | [] => tt
    | nm :: locals' => (denote_stack_ctxt_of_locals locals', nm)
    end.

  Fixpoint denote_function_loop (targs: list type) (tout: type)
    : denote_type_list denote_type targs (denote_type tout) :=
    match targs with
    | [] => Monad.loop
    | t :: rest =>
        fun _: denote_type t => denote_function_loop rest tout
    end.

  (* Stub for now *)
  Definition denote_function
    {ctx: ctxt Empty_set Empty_set fundef vardef} {fn: function}
    (_: wt_function ctx fn)
    (_: denote_glob_ctxt ctx.(ctxt_global))
    : denote_type (t_fun (List.map snd fn.(fn_params)) fn.(fn_return))
    := denote_function_loop (List.map snd fn.(fn_params)) fn.(fn_return).

  Definition denote_app {ctxt: ctxt (type * bool) unit fundef vardef} {fn: Deep.Prog.function} {args: list expr}
    (d_fn: denote_type (t_fun (List.map snd fn.(fn_params)) (fn.(fn_return))))
    (env: denote_pure_ctxt ctxt)
    (WTargs: Forall2T (wt_expr ctxt) args (map snd (fn_params fn)))
    : Monad.program (State St Hp) (denote_type fn.(fn_return)).
    destruct fn; cbn in *.
    revert args WTargs d_fn.
    induction fn_params as [ | [ id_param t_param ] fn_params IH ]; [ intros; exact d_fn | intros ].
    inversion WTargs as [ | arg ?y ?args' ?l' WTarg ?WTargs' ]; subst.
    eapply IH.
    eassumption.
    cbn in d_fn.
    apply d_fn.
    eapply denote_expr.
    exact WTarg.
    exact env.
  Defined.

  Definition convert [A B: Type] (EQ: A = B) (a : A) : B :=
    match EQ with
    | eq_refl => a
    end.

  Fixpoint denote_cmd
    {ctxt} {c : cmd} {t : type} (wt : wt_cmd ctxt c t):
    denote_ctxt ctxt -> Monad.program (State St Hp) (denote_type t) :=
    match wt in wt_cmd ctxt _ t return denote_ctxt ctxt -> Monad.program (State St Hp) (denote_type t) with
    | wt_ret WTe => fun env => ret (denote_expr WTe (fst (fst env)))
    | wt_bind UNBOUND WTe WTf =>
        fun env => do v <- (denote_cmd WTe env); (denote_cmd WTf (denote_ctxt_set_pure UNBOUND env v))
    | wt_app FINDfn GROUND WTargs =>
        fun env =>
          denote_app (denote_ctxt_lookup_global FINDfn env) (fst (fst env)) WTargs
    | wt_if WTcond WTthen WTelse =>
        fun env =>
          if denote_expr WTcond (fst (fst env)) then denote_cmd WTthen env else denote_cmd WTelse env
    | wt_while WTcond WTbody =>
        fun env =>
          while (denote_cmd WTcond env) (denote_cmd WTbody env)
    | wt_alloc_ptr WTsize WTinit GROUND =>
        fun env =>
          alloc_ptr (MS := denote_type_memval GROUND) (denote_expr WTsize (fst (fst env))) (convert (denote_types_agree GROUND) (denote_expr WTinit (fst (fst env))))
    | wt_read_ptr WTptr GROUND =>
        fun env =>
          convert (eq_sym (f_equal (fun t => Monad.program (State St Hp) t) (denote_types_agree GROUND))) (read_ptr (MS := denote_type_memval GROUND) (denote_expr WTptr (fst (fst env))))
    | wt_write_ptr WTptr WTval GROUND =>
        fun env =>
          write_ptr (MS := denote_type_memval GROUND) (denote_expr WTptr (fst (fst env))) (convert (denote_types_agree GROUND) (denote_expr WTval (fst (fst env))))
    | wt_free_ptr WTptr =>
        fun env =>
          free_ptr (denote_expr WTptr (fst (fst env)))
    | wt_shift_fw_ptr WTptr WTofst =>
        fun env => shift_fw_ptr (denote_expr WTptr (fst (fst env))) (denote_expr WTofst (fst (fst env)))
    | wt_shift_bw_ptr WTptr WTofst =>
        fun env => shift_bw_ptr (denote_expr WTptr (fst (fst env))) (denote_expr WTofst (fst (fst env)))
    | wt_ptr_eq WTl WTr =>
        fun env => eq_ptr (denote_expr WTl (fst (fst env))) (denote_expr WTr (fst (fst env)))
    | wt_with_var WTinit WTcont =>
        fun env =>
          with_var (MS := denote_type_memval (Facts.wt_expr_ground WTinit)) (convert (denote_types_agree (Facts.wt_expr_ground WTinit)) (denote_expr WTinit (fst (fst env)))) (fun x => denote_cmd WTcont (denote_ctxt_push_stack env x))
    | wt_read_var GROUND NTH =>
        fun env =>
          convert (eq_sym (f_equal (fun t => Monad.program (State St Hp) t) (denote_types_agree GROUND))) (read_var (MS := denote_type_memval GROUND) (denote_ctxt_lookup_stack NTH env))
    | wt_write_var WTval GROUND NTH =>
        fun env =>
          write_var (MS := denote_type_memval GROUND) (denote_ctxt_lookup_stack NTH env) (convert (denote_types_agree GROUND) (denote_expr WTval (fst (fst env))))
    end.

  Axiom TODO: forall {A: Type}, A.

  Definition denote_glob_ctxt_empty (pub: list AST.ident)
    : denote_glob_ctxt (Globalenvs.Genv.empty_genv fundef vardef pub) := tt.

  (* Extend an existing denote_glob_ctxt with one more (id, gd) entry. *)
  Definition denote_glob_ctxt_extend
    (ge: genv) (id: AST.ident) (gd: globdef)
    (d_gd: denote_globdef gd)
    (glob: denote_glob_ctxt ge)
    : denote_glob_ctxt (Globalenvs.Genv.add_global ge (id, gd))
    := denote_map_set denote_globdef
         (Globalenvs.Genv.genv_next ge) gd d_gd
         (Globalenvs.Genv.genv_defs ge) glob.

  Definition denote_init_data_value
    (init: list AST.init_data) (t: type)
    (EQ: type_init_data init t = true) : denote_type t.
  Proof.
    destruct t.
    - exact tt.
    - destruct init as [|i1 init1]; [discriminate|].
      destruct i1; try discriminate.
      destruct init1 as [|i2 init2]; [discriminate|].
      destruct i2; try discriminate.
      destruct init2; [|discriminate].
      exact (Z.eqb (Integers.Int.unsigned i) 1%Z).
    - destruct init as [|i1 init1]; [discriminate|].
      destruct i1; try discriminate.
      destruct init1 as [|i2 init2]; [discriminate|].
      destruct i2; try discriminate.
      destruct init2; [|discriminate].
      exact (Z.to_nat (Integers.Int.unsigned i)).
    - discriminate.
    - destruct init as [|i1 init1]; [discriminate|].
      destruct i1; try discriminate.
      all: destruct init1; [ exact Pointer.NULL | discriminate ].
    - discriminate.
  Defined.

  (* Stub for now *)
  Definition denote_external_function (ef: AST.external_function)
    (H: type_external_function ef = true)
    : match Facts.ef_sig_dec ef with
      | Some sig => denote_type (t_fun sig.(sig_args) sig.(sig_res))
      | None => Empty_set
      end.
  Proof.
    unfold type_external_function in H.
    destruct (Facts.ef_sig_dec ef) as [sig|]; [| discriminate].
    exact (denote_function_loop sig.(sig_args) sig.(sig_res)).
  Defined.

  (* Denote any kind of globdef *)
  Definition denote_globdef_value
    (ctx: ctxt Empty_set Empty_set fundef vardef)
    (id: AST.ident) (gd: globdef)
    (H: type_globdef ctx id gd = true)
    (glob: denote_glob_ctxt ctx.(ctxt_global))
    : denote_globdef gd.
  Proof.
    destruct gd as [f | v]; cbn [denote_globdef].
    - destruct f as [fn | ef];
        unfold type_globdef, Prog.type_globdef, type_fundef, Prog.type_fundef in H.
      + (* Internal fn *)
        refine (denote_function (fn := fn) _ glob).
        apply type_function_correct. exact H.
      + (* External ef *)
        exact (denote_external_function ef H).
    - (* Gvar v *)
      unfold type_globdef, Prog.type_globdef, type_globvar, Prog.type_globvar in H.
      apply Bool.andb_true_iff in H as [H _].
      apply Bool.andb_true_iff in H as [H _].
      apply Bool.andb_true_iff in H as [_ H].
      destruct v as [vinfo vinit vread vvol]; cbn in *.
      destruct vinfo as [t]; cbn in *.
      exact (denote_init_data_value vinit t H).
  Defined.

  (* Denote the program, denoting the globdefs in order and adding them to the environment one-by-one *)
  Fixpoint denote_prog_defs_fold (defs: list (AST.ident * globdef))
    (ctx: ctxt Empty_set Empty_set fundef vardef)
    (H: type_prog_defs ctx defs = true)
    (glob: denote_glob_ctxt ctx.(ctxt_global))
    {struct defs}
    : denote_glob_ctxt
        (List.fold_left
           (fun ge idg => Globalenvs.Genv.add_global ge idg)
           defs ctx.(ctxt_global)).
  Proof.
    destruct defs as [|[id gd] rest]; cbn in *.
    - exact glob.
    - unfold type_prog_defs, Prog.type_prog_defs in H. cbn in H.
      apply Bool.andb_true_iff in H as [Hgd Hrest].
      pose (gd_val := denote_globdef_value ctx id gd Hgd glob).
      pose (glob1 := denote_glob_ctxt_extend ctx.(ctxt_global) id gd gd_val glob).
      exact (denote_prog_defs_fold rest
               (Ctxt.add_global ctx (id, gd)) Hrest glob1).
  Defined.

  Definition denote_glob_ctxt_of_program
    (p: Prog.program) (WTp: wt_program p)
    : denote_glob_ctxt (Globalenvs.Genv.globalenv p).
  Proof.
    pose proof (proj1 (Bool.reflect_iff _ _ (type_program_spec p)) WTp) as Hbool.
    unfold type_program, Prog.type_program in Hbool.
    apply Bool.andb_true_iff in Hbool as [Hbool _].
    apply Bool.andb_true_iff in Hbool as [Hbool _].
    apply Bool.andb_true_iff in Hbool as [Hbool _].
    apply Bool.andb_true_iff in Hbool as [Hbool _].
    apply Bool.andb_true_iff in Hbool as [Hdefs _].
    unfold Globalenvs.Genv.globalenv, Globalenvs.Genv.add_globals.
    refine (denote_prog_defs_fold p.(prog_defs)
              (ctxt_emp _ _ _ _ p.(prog_public)) _ _).
    - exact Hdefs.
    - cbn. apply denote_glob_ctxt_empty.
  Defined.

  (* Because continuations are a mutual inductive, their denotation is a mutual fixpoint *)
  Fixpoint denote_cont
    {ctx} {k: @cont St} {t}
    (WT: @OpSem.Typing.wt_cont St ctx k t)
    (env: denote_pure_ctxt ctx)
    (stack: denote_stack_ctxt ctx.(ctxt_stack))
    (glob: denote_glob_ctxt ctx.(ctxt_global))
    (v: denote_type t)
    {struct WT}
    : Monad.program (State St Hp) nat
  with denote_cont_call
    {ctx} {k: @cont St} {t}
    (WT: @OpSem.Typing.wt_cont_call St ctx k t)
    (glob: denote_glob_ctxt ctx.(ctxt_global))
    (v: denote_type t)
    {struct WT}
    : Monad.program (State St Hp) nat.
  Proof using St Hp.
    - (* denote_cont *)
      destruct WT as
        [ ctx' id c' k' t_b t_c Hget Hwt_c Hwt_k
        | ctx' c_cond c_body k' Hwt_cond Hwt_body Hwt_k
        | ctx' c_cond c_body k' Hwt_cond Hwt_body Hwt_k
        | ctx' k' tret Hwt_cc
        ]; cbn in *.
      + (* Kbind: rebind v as id, run c, thread result through k *)
        exact (do v' <- denote_cmd Hwt_c (denote_ctxt_set_pure Hget (env, stack, glob) v);
               denote_cont _ _ _ Hwt_k env stack glob v').
      + (* Kloop1: input is bool *)
        exact
          (if v
           then
             do _ <- denote_cmd Hwt_body (env, stack, glob);
             do _ <- while
                       (denote_cmd Hwt_cond (env, stack, glob))
                       (denote_cmd Hwt_body (env, stack, glob));
             denote_cont _ _ _ Hwt_k env stack glob tt
           else denote_cont _ _ _ Hwt_k env stack glob tt).
      + (* Kloop2: input is unit *)
        exact
          (do _ <- while
                     (denote_cmd Hwt_cond (env, stack, glob))
                     (denote_cmd Hwt_body (env, stack, glob));
           denote_cont _ _ _ Hwt_k env stack glob tt).
      + (* wt_cont_other: forward to denote_cont_call; pure/stack envs dropped *)
        exact (denote_cont_call _ _ _ Hwt_cc glob v).
    - (* denote_cont_call *)
      destruct WT as
        [ ctx'
        | ctx' f e locals k' t' ty_env Hwt_fn Hwt_env Hwt_k
        ]; cbn in *.
      + (* Kstop: v : nat, return it *)
        exact (ret v).
      + (* Kcall: rebuild caller env from Hwt_env and locals, forward to denote_cont *)
        pose (caller_env := denote_pure_ctxt_of_env Hwt_env).
        pose (caller_stack := denote_stack_ctxt_of_locals locals).
        exact (denote_cont _ _ _ Hwt_k caller_env caller_stack glob v).
  Defined.

  Definition denote_state {p: Prog.program} {s: @state St Hp}
    (WTp: wt_program p) (WTs: wt_state p s)
    : Monad.program (State St Hp) nat.
  Proof using St Hp.
    pose (glob := denote_glob_ctxt_of_program p WTp).
    destruct WTs as
      [ f c k env_v locals s' ctx t Hwt_State
      | f args k s' sig ctx Hwt_fundef Hwt_args Hsig Hwt_cont
      | v k s' ctx t Hwt_res Hwt_cont
      ].
    - destruct Hwt_State as
        [ State_wt_function State_wt_cmd State_wt_cont State_wt_env State_wt_stack ].
      pose (env_pure := denote_pure_ctxt_of_env State_wt_env).
      assert (stack_d : denote_stack_ctxt ctx.(ctxt_stack)).
      {
        rewrite State_wt_stack.
        exact (denote_stack_ctxt_of_locals locals).
      }
      exact (do v <- denote_cmd State_wt_cmd (env_pure, stack_d, TODO);
             denote_cont State_wt_cont env_pure stack_d TODO v).
    - exact TODO.
    - exact (denote_cont Hwt_cont TODO TODO TODO (denote_value_typed Hwt_res)).
  Defined.

End State.
