From Stdlib Require Import Psatz Arith NArith.

From GallinaC.Utils Require Import ListExt PTreeExt.
From GallinaC.Imp Require Export Monad Primitives Pointer Intops Uint32 Uintptr.
Import Unsigned.Notations.
From GallinaC.Compiler.Common Require Export Types Ctxt Expr CCInj.
From GallinaC.Compiler.Deep Require Import Cmd Prog OpSem(state, step) Typing.

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

  Definition denote_type_memval {t: type} (GROUND: ground t): Memval.MemStorable :=
    match GROUND with
    | ground_unit => Memval.StorableUnit.unit_storable
    | ground_bool => Memval.StorableBool.bool_storable
    | ground_nat => Memval.StorableNat.nat_storable
    | ground_ofst => Memval.StorableOfst.ofst_storable
    | ground_ptr => Memval.StorablePtr.ptr_storable
    end.

  Lemma denote_types_agree: forall {t: type} (GROUND: ground t), denote_type t = Memval.obj (denote_type_memval GROUND).
  Proof using St Hp.
    now induction GROUND.
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

  (* Definition denote_ctxt (ctxt: map_ctxt (type * bool)): Type := *)
  (*   Maps.PTree.fold add_to_denote_ctxt ctxt unit. *)
    (* List.fold_right add_to_denote_ctxt unit (Maps.PTree.elements ctxt). *)
  (* Definition denote_ctxt (ctxt: ctxt (type * bool) Empty_set fundef vardef): Type := denote_pure_ctxt ctxt. *)

  Definition denote_pure_ctxt_lookup:
    forall {ctx: map_ctxt (type * bool)} {v t}
    (GET: Maps.PTree.get v ctx = Some (t, true))
    (env: denote_pure_ctxt ctx),
      denote_type t.
  Proof using St Hp.
    induction ctx using Maps.PTree.tree_ind; [ intros v t H; discriminate H | ].
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

  (* Definition denote_function {ctxt: Globalenvs.Genv.t fundef vardef} (f: function): denote_type (t_fun (List.map snd f.(fn_params)) (f.(fn_return))). *)

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

  (* Definition denote_function *)
  (*   {ctxt} {fn} *)
  (*   (WT: wt_function ctxt fn) *)
  (*   : denote_type (t_fun (List.map snd fn.(fn_params)) fn.(fn_return)). *)
  (*   destruct WT. *)
  (*   Definition denote_function' {ctxt params} *)
  (*     (WT_params: . *)

  Axiom TODO: forall {A: Type}, A.

  Definition denote_state
    (s: @state St Hp)
    : Monad.program (State St Hp) nat :=
    match s with
    | OpSem.State f c k env locals s => TODO
    | OpSem.Callstate f args k s => TODO
    | OpSem.Returnstate v k s => TODO
    end.

End State.
