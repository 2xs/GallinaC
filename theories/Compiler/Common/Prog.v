From Corelib Require Derive.
From Stdlib Require Import ZArith PArith Bool.

From compcert.common Require AST Globalenvs Events.
Import Globalenvs(Genv.t).

From GallinaC.Utils Require Import ListExt.

From GallinaC.Compiler.Common Require Import Types Value CCInj Ctxt.

Record function (cmd extra: Set): Set :=
  mkfunction
    {
      fn_return: type;
      fn_params: list (AST.ident * type);
      fn_temps: list (AST.ident * type);
      fn_body: cmd;
      fn_extra: extra;
    }.
Arguments fn_return [cmd extra].
Arguments fn_params [cmd extra].
Arguments fn_temps [cmd extra].
Arguments fn_body [cmd extra].
Arguments fn_extra [cmd extra].

Definition fundef (cmd extra: Set): Set := AST.fundef (function cmd extra).
Strategy expand [ fundef ].

Record vardef :=
  mkvardef
    {
      var_type: type;
    }.

Record signature: Set :=
  mk_signature
    {
      sig_args: list type;
      sig_res: type;
    }.

Definition signature_of_signature (s: signature): AST.signature :=
  AST.mksignature
    (ListExt.filter_map type_to_xtype s.(sig_args))
    (ssrfun.Option.default AST.Xvoid (type_to_xtype s.(sig_res)))
    AST.cc_default.
Coercion signature_of_signature: signature >-> AST.signature.

Definition fn_signature [cmd extra: Set] (f: function cmd extra): signature :=
  mk_signature
    (List.map snd f.(fn_params))
    f.(fn_return)
.

Inductive ext_funsig: AST.external_function -> signature -> Prop :=
| funsig_external: forall nm t_arg xt, CCInj.type_to_xtype t_arg = Some xt ->  ext_funsig (AST.EF_external nm (AST.mksignature [xt] AST.Xvoid AST.cc_default)) {| sig_args := [t_arg]; sig_res := t_unit; |}
| funsig_malloc: ext_funsig AST.EF_malloc {| sig_args := [t_ofst]; sig_res := t_ptr; |}
| funsig_free: ext_funsig AST.EF_free {| sig_args := [t_ptr]; sig_res := t_unit; |}
.

Inductive funsig {cmd extra: Set}: (fundef cmd extra) -> signature -> Prop :=
| funsig_Internal: forall f, funsig (AST.Internal f) (fn_signature f)
| funsig_External: forall ef sig (SIG: ext_funsig ef sig), funsig (AST.External ef) sig
(* | funsig_External: forall ef t_args t_out *)
(*                           (ToX_args: List.Forall2 type_of_xtype (AST.ef_sig ef).(AST.sig_args) t_args) *)
(*                           (ToX_out: type_of_xtype (AST.ef_sig ef).(AST.sig_res) t_out), *)
(*     funsig (AST.External ef) (mk_signature t_args t_out) *)
.

Definition globdef cmd extra := (AST.globdef (fundef cmd extra) vardef).
Definition genv cmd extra := (Genv.t (fundef cmd extra) vardef).

Record program (cmd f_extra p_extra: Set) :=
  mkprogram
    {
      prog_defs: list (AST.ident * (globdef cmd f_extra));
      prog_public: list AST.ident;
      prog_main: AST.ident;
      prog_extra: p_extra;
    }.
Arguments mkprogram [cmd f_extra p_extra] .
Arguments prog_defs [cmd f_extra p_extra].
Arguments prog_public [cmd f_extra p_extra].
Arguments prog_main [cmd f_extra p_extra].
Arguments prog_extra [cmd f_extra p_extra].

Definition program_of_program [cmd f_extra p_extra] (p: program cmd f_extra p_extra): AST.program (fundef cmd f_extra) vardef :=
  {|
    AST.prog_defs := p.(prog_defs);
    AST.prog_public := p.(prog_public);
    AST.prog_main := p.(prog_main);
  |}
.
#[global] Coercion program_of_program : program >-> AST.program.

(* ctx is the "global" context *)
(* global should be set to whatever
 * we overwrite stack since it should be empty
 * pure should be empty as well
 *)
#[local] Definition mk_pair_with_false [A: Type] (a: A):= (a,false).
#[local] Definition mk_uninit_pair (idt: AST.ident*type) := (fst idt, mk_pair_with_false (snd idt)).
#[local] Definition mk_pair_with_true [A: Type] (a: A):= (a,true).
#[local] Definition mk_init_pair (idt: AST.ident*type) := (fst idt, mk_pair_with_true (snd idt)).
Definition mk_function_ctxt [cmd f_extra] (params: list (AST.ident * type)) (temps: list (AST.ident * type)) (ctx: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef): ctxt (type * bool) unit (fundef cmd f_extra) vardef :=
  Ctxt.with_pure
    (Maps.PTree_Properties.of_list (List.map mk_init_pair params ++ List.map mk_uninit_pair temps))
    (Ctxt.with_stack [] ctx).

Definition mk_glob_ctxt [cmd f_extra p_extra] (p: program cmd f_extra p_extra): ctxt Empty_set Empty_set (fundef cmd f_extra) vardef :=
  with_global (Globalenvs.Genv.globalenv p) (ctxt_emp Empty_set Empty_set Empty_set Empty_set []).

(* ctx here is the global program context *)
Record wt_function [cmd: Set] (f_extra: Set) (wt_f_extra: f_extra -> Type) (wt_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Type) (ctx: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef) (func: (function cmd f_extra)): Type :=
  {
    wt_fn_return: Ground func.(fn_return);
    wt_fn_params: Forall (fun idt => Ground (snd idt)) func.(fn_params);
    wt_fn_temps: Forall (fun idt => Ground (snd idt)) func.(fn_temps);
    wt_fn_cmd: wt_cmd (mk_function_ctxt func.(fn_params) func.(fn_temps) ctx) func.(fn_body) func.(fn_return);
    wt_fn_extra: wt_f_extra func.(fn_extra);

    wt_fn_params_sbinds: SBinds func.(fn_params);
    wt_fn_temps_sbinds: SBinds func.(fn_temps);
    wt_fn_params_temps_distinct: List.Forall (fun idt => ~exists idt', (In idt' func.(fn_temps) /\ fst idt' = fst idt)) func.(fn_params);
  }.
Arguments wt_fn_return [cmd f_extra wt_f_extra wt_cmd ctx func]: rename.
Arguments wt_fn_params [cmd f_extra wt_f_extra wt_cmd ctx func]: rename.
Arguments wt_fn_temps [cmd f_extra wt_f_extra wt_cmd ctx func]: rename.
Arguments wt_fn_cmd [cmd f_extra wt_f_extra wt_cmd ctx func]: rename.
Arguments wt_fn_extra [cmd f_extra wt_f_extra wt_cmd ctx func]: rename.
Arguments wt_fn_params_sbinds [cmd f_extra wt_f_extra wt_cmd ctx func]: rename.
Arguments wt_fn_temps_sbinds [cmd f_extra wt_f_extra wt_cmd ctx func]: rename.
Arguments wt_fn_params_temps_distinct [cmd f_extra wt_f_extra wt_cmd ctx func]: rename.

Inductive wt_external_function: AST.external_function -> Prop :=
| wt_EF_malloc: wt_external_function AST.EF_malloc
| wt_EF_free: wt_external_function AST.EF_free
| wt_EF_external: forall nm sig_cc sig_gc (SIG: ext_funsig (AST.EF_external nm sig_cc) sig_gc), wt_external_function (AST.EF_external nm sig_cc)
.

Inductive wt_fundef [cmd: Set] (f_extra: Set) (wt_f_extra: f_extra -> Type) (wt_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Type): ctxt Empty_set Empty_set (fundef cmd f_extra) vardef -> (fundef cmd f_extra) -> Type :=
| wt_Internal:
  forall ctx func
         (Hwt_function: wt_function f_extra wt_f_extra wt_cmd ctx func),
    wt_fundef f_extra wt_f_extra wt_cmd ctx (AST.Internal func)
| wt_External: forall ctx ef, wt_external_function ef -> wt_fundef f_extra wt_f_extra wt_cmd ctx (AST.External ef)
.

Inductive wt_fundef_call cmd f_extra: list value -> (fundef cmd f_extra) -> Prop :=
| wt_call_Internal: forall args f, Forall2 wt_value args (List.map snd f.(fn_params)) -> wt_fundef_call cmd f_extra args (AST.Internal f)
| wt_call_malloc: forall o, wt_fundef_call cmd f_extra [v_ofst o] (AST.External AST.EF_malloc)
| wt_call_free: forall p, wt_fundef_call cmd f_extra [v_ptr p] (AST.External AST.EF_free)
.

Inductive wt_init_data: list AST.init_data -> type -> Prop :=
| wt_init_data_unit:
  wt_init_data [ AST.Init_space (Z.of_nat memval_memsize) ] t_unit
| wt_init_data_bool: forall n,
    (Integers.Int.unsigned n = 0%Z \/ Integers.Int.unsigned n = 1%Z) ->
    wt_init_data
      [ AST.Init_int8 n; AST.Init_space (Z.of_nat memval_memsize - 1) ]
      t_bool
| wt_init_data_nat: forall n,
    wt_init_data
      [ AST.Init_int32 n; AST.Init_space (Z.of_nat memval_memsize - 4) ]
      t_nat
| wt_init_data_ptr64:
  Archi.ptr64 = true ->
  wt_init_data [ AST.Init_int64 Integers.Int64.zero ] t_ptr
| wt_init_data_ptr32:
  Archi.ptr64 = false ->
  wt_init_data [ AST.Init_int32 Integers.Int.zero ] t_ptr
.

Definition type_init_data (init: list AST.init_data) (t: type) : bool :=
  match t, init with
  | t_unit, [ AST.Init_space sz ] =>
      Z.eqb sz (Z.of_nat memval_memsize)
  | t_bool, [ AST.Init_int8 n; AST.Init_space pad ] =>
      (Z.eqb (Integers.Int.unsigned n) 0%Z || Z.eqb (Integers.Int.unsigned n) 1%Z)
      && Z.eqb pad (Z.of_nat memval_memsize - 1)
  | t_nat, [ AST.Init_int32 _; AST.Init_space pad ] =>
      Z.eqb pad (Z.of_nat memval_memsize - 4)
  | t_ptr, [ AST.Init_int64 n ] =>
      Archi.ptr64 && Z.eqb (Integers.Int64.unsigned n) 0%Z
  | t_ptr, [ AST.Init_int32 n ] =>
      negb Archi.ptr64 && Z.eqb (Integers.Int.unsigned n) 0%Z
  | _, _ => false
  end.

Record wt_globvar cmd f_extra (ctx: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef) (id: AST.ident) (globvar: AST.globvar vardef): Prop :=
  {
    wt_globvar_type_ground: Types.Ground globvar.(AST.gvar_info).(var_type);
    wt_globvar_init_type: wt_init_data globvar.(AST.gvar_init) globvar.(AST.gvar_info).(var_type);
    wt_globvar_readonly: globvar.(AST.gvar_readonly) = false;
    wt_globvar_volatile: globvar.(AST.gvar_volatile) = false;
  }.
Arguments wt_globvar_type_ground [cmd f_extra ctx id globvar]: rename.
Arguments wt_globvar_init_type [cmd f_extra ctx id globvar]: rename.
Arguments wt_globvar_readonly [cmd f_extra ctx id globvar]: rename.
Arguments wt_globvar_volatile [cmd f_extra ctx id globvar]: rename.

Inductive wt_globdef [cmd] f_extra wt_f_extra wt_cmd: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef -> AST.ident -> (globdef cmd f_extra) -> Prop :=
| wt_Gfun: forall ctx id f, wt_fundef f_extra wt_f_extra wt_cmd ctx f -> wt_globdef f_extra wt_f_extra wt_cmd ctx id (AST.Gfun f)
| wt_Gvar: forall ctx id v, wt_globvar cmd f_extra ctx id v -> wt_globdef f_extra wt_f_extra wt_cmd ctx id (AST.Gvar v)
.

Record wt_program [cmd f_extra p_extra: Set] wt_f_extra wt_cmd (wt_p_extra: program cmd f_extra p_extra -> Prop) (p: program cmd f_extra p_extra): Prop :=
  {
    wt_prog_defs:
      (* Similar to typing Rocq modules *)
      (* Global definitions are typed one-by-one and added to the environment *)
    ListExt.FoldLeft
      (fun ctx idg => wt_globdef f_extra wt_f_extra wt_cmd ctx (fst idg) (snd idg))
      (fun ctx idg => Ctxt.add_global ctx idg)
      (ctxt_emp _ _ _ _ p.(prog_public))
      p.(prog_defs);
    wt_prog_public: forall id, In id p.(prog_public) -> exists gdef, In (id,gdef) p.(prog_defs);
    wt_prog_main: exists f_main, In (p.(prog_main), AST.Gfun f_main) p.(prog_defs);
    wt_prog_defs_sbinds: SBinds p.(prog_defs);
    wt_prog_public_nodup: Sorted Pos.lt p.(prog_public);
    wt_prog_extra: wt_p_extra p;
  }.
Arguments wt_prog_defs [cmd f_extra p_extra wt_f_extra wt_cmd wt_p_extra p]: rename.
Arguments wt_prog_public [cmd f_extra p_extra wt_f_extra wt_cmd wt_p_extra p]: rename.
Arguments wt_prog_main [cmd f_extra p_extra wt_f_extra wt_cmd wt_p_extra p]: rename.
Arguments wt_prog_defs_sbinds [cmd f_extra p_extra wt_f_extra wt_cmd wt_p_extra p]: rename.
Arguments wt_prog_public_nodup [cmd f_extra p_extra wt_f_extra wt_cmd wt_p_extra p]: rename.
Arguments wt_prog_extra [cmd f_extra p_extra wt_f_extra wt_cmd wt_p_extra p]: rename.

Module Facts.

  Lemma mk_uninit_pair_inj idt1 idt2 (Heq: mk_uninit_pair idt1 = mk_uninit_pair idt2): idt1 = idt2.
  Proof.
    destruct idt1 as [ id1 t1 ], idt2 as [ id2 t2 ].
    unfold mk_uninit_pair in Heq;
      cbn in Heq;
      unfold mk_pair_with_false in Heq.
    congruence.
  Qed.

  Lemma mk_uninit_pair_list_is_uninit {l ident t b}
    (HIn: In (ident, (t, b)) (map mk_uninit_pair l))
    : b = false.
  Proof.
    induction l; [ contradiction | cbn in HIn ].
    destruct HIn as [ Heq | HIn ]; [ cbv in Heq; congruence | apply IHl, HIn ].
  Qed.

  Lemma mk_init_pair_inj idt1 idt2 (Heq: mk_init_pair idt1 = mk_init_pair idt2): idt1 = idt2.
  Proof.
    destruct idt1, idt2.
    unfold mk_init_pair, mk_pair_with_true in Heq; cbn in Heq; congruence.
  Qed.

  Lemma map_fst_mk_init_pair l : map fst (map mk_init_pair l) = map fst l.
  Proof.
    induction l as [| [id t] l IH]; cbn; [ reflexivity | now f_equal ].
  Qed.

  Lemma map_fst_mk_uninit_pair l : map fst (map mk_uninit_pair l) = map fst l.
  Proof.
    induction l as [| [id t] l IH]; cbn; [ reflexivity | now f_equal ].
  Qed.

  Lemma in_mk_init_pair_iff l id t :
    In (id, (t, true)) (map mk_init_pair l) <-> In (id, t) l.
  Proof.
    induction l as [| [id' t'] l IH]; cbn; [ tauto |].
    unfold mk_init_pair at 1, mk_pair_with_true at 1; cbn.
    split; intros [Heq | HIn];
      try (left; inversion Heq; subst; reflexivity);
      try (right; apply IH; assumption).
  Qed.

  Lemma in_mk_uninit_pair_iff l id t :
    In (id, (t, false)) (map mk_uninit_pair l) <-> In (id, t) l.
  Proof.
    induction l as [| [id' t'] l IH]; cbn; [ tauto |].
    unfold mk_uninit_pair at 1, mk_pair_with_false at 1; cbn.
    split; intros [Heq | HIn];
      try (left; inversion Heq; subst; reflexivity);
      try (right; apply IH; assumption).
  Qed.

  Lemma mk_function_ctxt_keys_norepet
    (params temps: list (AST.ident * type))
    (Hpsb: ListExt.SBinds params)
    (Htsb: ListExt.SBinds temps)
    (Hdist: List.Forall (fun idt =>
              ~ exists idt', In idt' temps /\ fst idt' = fst idt) params) :
    Coqlib.list_norepet
      (map fst (map mk_init_pair params ++ map mk_uninit_pair temps)).
  Proof.
    rewrite List.map_app, map_fst_mk_init_pair, map_fst_mk_uninit_pair.
    apply Coqlib.list_norepet_app; repeat split.
    - apply ListExt.SBinds_list_norepet, Hpsb.
    - apply ListExt.SBinds_list_norepet, Htsb.
    - intros idp idt HInp HInt; cbn.
      intros Heq; subst idt.
      apply in_map_iff in HInp as [[ip tp] [Hfst HInp]]; cbn in Hfst; subst ip.
      apply in_map_iff in HInt as [[it tt] [Hfst HInt]]; cbn in Hfst; subst it.
      rewrite Forall_forall in Hdist.
      apply (Hdist _ HInp).
      exists (idp, tt); split; [exact HInt | reflexivity].
  Qed.

  Lemma mk_function_ctxt_pure_get_param [cmd f_extra]
    (params temps: list (AST.ident * type))
    (ctx: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef)
    (Hpsb: ListExt.SBinds params)
    (Htsb: ListExt.SBinds temps)
    (Hdist: List.Forall (fun idt =>
              ~ exists idt', In idt' temps /\ fst idt' = fst idt) params)
    id t (HIn: In (id, t) params) :
    Maps.PTree.get id
      (ctxt_pure (mk_function_ctxt params temps ctx)) = Some (t, true).
  Proof.
    unfold mk_function_ctxt; cbn [ctxt_pure with_pure].
    apply Maps.PTree_Properties.of_list_norepet.
    - apply mk_function_ctxt_keys_norepet; assumption.
    - apply in_or_app; left.
      apply in_mk_init_pair_iff; exact HIn.
  Qed.

  Lemma mk_function_ctxt_pure_get_temp [cmd f_extra]
    (params temps: list (AST.ident * type))
    (ctx: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef)
    (Hpsb: ListExt.SBinds params)
    (Htsb: ListExt.SBinds temps)
    (Hdist: List.Forall (fun idt =>
              ~ exists idt', In idt' temps /\ fst idt' = fst idt) params)
    id t (HIn: In (id, t) temps) :
    Maps.PTree.get id
      (ctxt_pure (mk_function_ctxt params temps ctx)) = Some (t, false).
  Proof.
    unfold mk_function_ctxt; cbn [ctxt_pure with_pure].
    apply Maps.PTree_Properties.of_list_norepet.
    - apply mk_function_ctxt_keys_norepet; assumption.
    - apply in_or_app; right.
      apply in_mk_uninit_pair_iff; exact HIn.
  Qed.

  Lemma mk_function_ctxt_pure_get_inv [cmd f_extra]
    (params temps: list (AST.ident * type))
    (ctx: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef)
    id t b
    (Hget: Maps.PTree.get id (ctxt_pure (mk_function_ctxt params temps ctx))
             = Some (t, b)) :
    (b = true /\ In (id, t) params) \/ (b = false /\ In (id, t) temps).
  Proof.
    unfold mk_function_ctxt in Hget; cbn [ctxt_pure with_pure] in Hget.
    apply Maps.PTree_Properties.in_of_list in Hget.
    apply in_app_or in Hget as [HIn | HIn].
    - left.
      apply in_map_iff in HIn as [[id' t'] [Heq HIn]].
      unfold mk_init_pair, mk_pair_with_true in Heq; cbn in Heq.
      inversion Heq; subst; split; [reflexivity | exact HIn].
    - right.
      apply in_map_iff in HIn as [[id' t'] [Heq HIn]].
      unfold mk_uninit_pair, mk_pair_with_false in Heq; cbn in Heq.
      inversion Heq; subst; split; [reflexivity | exact HIn].
  Qed.

  Lemma prog_main_is_prog_main [cmd f_extra p_extra]:
    forall (p: program cmd f_extra p_extra),
      prog_main p = AST.prog_main (program_of_program p).
  Proof.
    reflexivity.
  Qed.

  Lemma program_of_program_sound [cmd f_extra p_extra]:
    forall (p: program cmd f_extra p_extra) p',
      p' = (program_of_program p) -> p = (mkprogram p'.(AST.prog_defs) p'.(AST.prog_public) p'.(AST.prog_main) p.(prog_extra)).
  Proof.
    intros.
    destruct p, p'.
    f_equal; inversion H; auto.
  Qed.

  Lemma wt_program_public_NoDupA [cmd f_extra p_extra wt_f_extra wt_cmd wt_p_extra] (p: program cmd f_extra p_extra) (WT: wt_program wt_f_extra wt_cmd wt_p_extra p)
    : NoDupA eq p.(prog_public).
  Proof.
    destruct p as [x public y z ], WT as [_ _ _ _ SORTED _]; cbn in *; clear x y z.
    eapply SortA_NoDupA; [ apply eq_equivalence | apply Pos.lt_strorder | apply Pos.lt_compat | assumption ].
  Qed.

  Lemma wt_program_public_NoDup [cmd f_extra p_extra wt_f_extra wt_cmd wt_p_extra] (p: program cmd f_extra p_extra) (WT: wt_program wt_f_extra wt_cmd wt_p_extra p)
    : NoDup p.(prog_public).
  Proof.
    eapply NoDupA_NoDup, wt_program_public_NoDupA, WT.
  Qed.

  Lemma wt_function_mono [cmd f_extra: Set]
    [wt_f_extra: f_extra -> Type]
    [wt_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Type]
    (wt_cmd_mono:
       forall ctx ctx',
         Ctxt.ctxt_pure ctx = Ctxt.ctxt_pure ctx' ->
         Ctxt.ctxt_stack ctx = Ctxt.ctxt_stack ctx' ->
         (forall id g, Ctxt.get_global id ctx = Some g ->
                       Ctxt.get_global id ctx' = Some g) ->
         forall c t, wt_cmd ctx c t -> wt_cmd ctx' c t)
    ctx ctx' func
    (Hmono: forall id g, Ctxt.get_global id ctx = Some g ->
                         Ctxt.get_global id ctx' = Some g):
    wt_function f_extra wt_f_extra wt_cmd ctx func ->
    wt_function f_extra wt_f_extra wt_cmd ctx' func.
  Proof.
    intros WT.
    refine {|
      wt_fn_return := WT.(wt_fn_return);
      wt_fn_params := WT.(wt_fn_params);
      wt_fn_temps := WT.(wt_fn_temps);
      wt_fn_cmd := _;
      wt_fn_extra := WT.(wt_fn_extra);
      wt_fn_params_sbinds := WT.(wt_fn_params_sbinds);
      wt_fn_temps_sbinds := WT.(wt_fn_temps_sbinds);
      wt_fn_params_temps_distinct := WT.(wt_fn_params_temps_distinct);
    |}.
    eapply wt_cmd_mono; [ | | | exact WT.(wt_fn_cmd) ]; try reflexivity.
    intros id g HG.
    unfold mk_function_ctxt in *.
    rewrite Ctxt.Facts.get_global_with_pure, Ctxt.Facts.get_global_with_stack in HG.
    rewrite Ctxt.Facts.get_global_with_pure, Ctxt.Facts.get_global_with_stack.
    now apply Hmono.
  Qed.

  Lemma wt_fundef_mono [cmd f_extra: Set]
    [wt_f_extra: f_extra -> Type]
    [wt_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Type]
    (wt_cmd_mono:
       forall ctx ctx',
         Ctxt.ctxt_pure ctx = Ctxt.ctxt_pure ctx' ->
         Ctxt.ctxt_stack ctx = Ctxt.ctxt_stack ctx' ->
         (forall id g, Ctxt.get_global id ctx = Some g ->
                       Ctxt.get_global id ctx' = Some g) ->
         forall c t, wt_cmd ctx c t -> wt_cmd ctx' c t)
    ctx ctx' f
    (Hmono: forall id g, Ctxt.get_global id ctx = Some g ->
                         Ctxt.get_global id ctx' = Some g):
    wt_fundef f_extra wt_f_extra wt_cmd ctx f ->
    wt_fundef f_extra wt_f_extra wt_cmd ctx' f.
  Proof.
    intros WT.
    destruct WT as [ ? func Hf | ? ef Hef ].
    - constructor; eapply wt_function_mono; eauto.
    - constructor; assumption.
  Qed.

  Lemma wt_globdef_mono [cmd f_extra: Set]
    [wt_f_extra: f_extra -> Type]
    [wt_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Type]
    (wt_cmd_mono:
       forall ctx ctx',
         Ctxt.ctxt_pure ctx = Ctxt.ctxt_pure ctx' ->
         Ctxt.ctxt_stack ctx = Ctxt.ctxt_stack ctx' ->
         (forall id g, Ctxt.get_global id ctx = Some g ->
                       Ctxt.get_global id ctx' = Some g) ->
         forall c t, wt_cmd ctx c t -> wt_cmd ctx' c t)
    ctx ctx' id g
    (Hmono: forall id' g', Ctxt.get_global id' ctx = Some g' ->
                           Ctxt.get_global id' ctx' = Some g'):
    wt_globdef f_extra wt_f_extra wt_cmd ctx id g ->
    wt_globdef f_extra wt_f_extra wt_cmd ctx' id g.
  Proof.
    intros WT.
    destruct WT as [ ? ? fn Hf | ? ? v Hv ].
    - constructor; eapply wt_fundef_mono; eauto.
    - constructor; destruct Hv; constructor; assumption.
  Qed.

  Lemma globdef_in_mk_glob_ctxt [cmd f_extra p_extra: Set]
    (p: program cmd f_extra p_extra) (SBINDS: SBinds p.(prog_defs))
    [id g] (HIn: In (id, g) p.(prog_defs))
    : get_global id (mk_glob_ctxt p) = Some g.
  Proof.
    edestruct (proj1 (Globalenvs.Genv.find_def_symbol p id g)) as (b & Hsym & Hdef);
      [ apply AST.prog_defmap_norepet;
          [ apply ListExt.SBinds_list_norepet, SBINDS | exact HIn ]
      | unfold mk_glob_ctxt, get_global, with_global; cbn [ctxt_global];
        now rewrite Hsym, Hdef ].
  Qed.

  Lemma wt_prog_defs_Forall_aux [cmd f_extra p_extra: Set]
    [wt_f_extra: f_extra -> Type]
    [wt_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Type]
    (wt_cmd_mono:
       forall ctx ctx',
         Ctxt.ctxt_pure ctx = Ctxt.ctxt_pure ctx' ->
         Ctxt.ctxt_stack ctx = Ctxt.ctxt_stack ctx' ->
         (forall id g, Ctxt.get_global id ctx = Some g ->
                       Ctxt.get_global id ctx' = Some g) ->
         forall c t, wt_cmd ctx c t -> wt_cmd ctx' c t)
    (p: program cmd f_extra p_extra) (SBINDS: SBinds p.(prog_defs))
    defs ctx
    (HIn: forall idg, In idg defs -> In idg p.(prog_defs))
    (Hsub: forall id g, get_global id ctx = Some g ->
                        get_global id (mk_glob_ctxt p) = Some g)
    (FF: ListExt.FoldLeft
           (fun c idg => wt_globdef f_extra wt_f_extra wt_cmd c (fst idg) (snd idg))
           (fun c idg => Ctxt.add_global c idg) ctx defs)
    : Forall (fun idg => wt_globdef f_extra wt_f_extra wt_cmd
                           (mk_glob_ctxt p) (fst idg) (snd idg)) defs.
  Proof.
    revert HIn Hsub.
    induction FF as [ | acc [id g] rest Hwt _ IH ]; intros HIn Hsub; constructor;
      [ eapply wt_globdef_mono; [ exact wt_cmd_mono | exact Hsub | exact Hwt ] | ].
    apply IH; [ now intros ??; apply HIn; right | ].
    intros id' g' HG'; destruct (BinPos.Pos.eq_dec id id') as [ <- | Hne ];
      [ rewrite Ctxt.Facts.get_global_add_global_eq in HG'; injection HG' as <-;
        apply globdef_in_mk_glob_ctxt; [ exact SBINDS | apply HIn; now left ]
      | rewrite Ctxt.Facts.get_global_add_global_neq in HG' by (cbn; congruence);
        now apply Hsub ].
  Qed.

  Lemma wt_prog_defs_Forall [cmd f_extra p_extra: Set]
    [wt_f_extra: f_extra -> Type]
    [wt_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Type]
    [wt_p_extra: program cmd f_extra p_extra -> Prop]
    (wt_cmd_mono:
       forall ctx ctx',
         Ctxt.ctxt_pure ctx = Ctxt.ctxt_pure ctx' ->
         Ctxt.ctxt_stack ctx = Ctxt.ctxt_stack ctx' ->
         (forall id g, Ctxt.get_global id ctx = Some g ->
                       Ctxt.get_global id ctx' = Some g) ->
         forall c t, wt_cmd ctx c t -> wt_cmd ctx' c t)
    (p: program cmd f_extra p_extra)
    (WT: wt_program wt_f_extra wt_cmd wt_p_extra p)
    : Forall
        (fun idglob => wt_globdef f_extra wt_f_extra wt_cmd (mk_glob_ctxt p) (fst idglob) (snd idglob))
        p.(prog_defs).
  Proof.
    destruct WT as [ FOLD _ _ SBINDS _ _ ].
    apply wt_prog_defs_Forall_aux
      with (ctx := ctxt_emp _ _ _ _ p.(prog_public));
      [ exact wt_cmd_mono | exact SBINDS | tauto
      | intros ?? HG;
        unfold get_global, ctxt_emp, Globalenvs.Genv.find_symbol,
               Globalenvs.Genv.empty_genv in HG; cbn in HG; discriminate
      | exact FOLD ].
  Qed.

  Definition ef_sig_dec (ef: AST.external_function) : option signature :=
    match ef with
    | AST.EF_external
        nm
        {| AST.sig_args := [xt]; AST.sig_res := AST.Xvoid; AST.sig_cc := {| AST.cc_vararg := None; AST.cc_unproto := false; AST.cc_structret := false |}; |} =>
        match xtype_to_type xt with
        | Some t => Some {| sig_args := [ t ]; sig_res := t_unit; |}
        | None => None
        end
    | AST.EF_malloc => Some {| sig_args := [t_ofst]; sig_res := t_ptr; |}
    | AST.EF_free => Some {| sig_args := [t_ptr]; sig_res := t_unit; |}
    | _ => None
    end.

  Lemma ef_sig_dec_spec: forall ef sig, ext_funsig ef sig <-> ef_sig_dec ef = Some sig.
  Proof.
    intros.
    split; intros SIG.
    - destruct SIG; cbn.
      + destruct t_arg, xt; cbn in H; try discriminate; try reflexivity.
      + reflexivity.
      + reflexivity.
    - destruct ef; cbn in SIG; try discriminate.
      destruct sg; try discriminate;
        destruct sig_args0 as [| ? [ | ] ] ; try discriminate;
        destruct sig_res0; try discriminate.
      destruct sig_cc as [ [ | ] [ | ] [ | ] ]; try discriminate;
        destruct x; try discriminate; cbn in SIG; inversion SIG; subst;
        try discriminate;
        (try (constructor; reflexivity)).
      inversion SIG; subst; constructor.
      inversion SIG; subst; constructor.
  Qed.

  Lemma type_init_data_spec: forall init t,
      Bool.reflect (wt_init_data init t) (type_init_data init t).
  Proof.
    intros init t.
    destruct t; cbn.
    - destruct init as [ | [ | | | | | |sz| ] [ | ? ? ] ];
        try (apply ReflectF; intros H; inversion H); cbn.
      destruct (Z.eqb_spec sz (Z.of_nat memval_memsize));
        [ subst; left; constructor | right; intros contra; inversion contra; congruence ].
    - destruct init
        as [ | [i| | | | | | | ] [ | [ | | | | | |pad| ] [ | ? ? ] ] ];
        try (apply ReflectF; intros H; inversion H; congruence).
      destruct (Z.eqb_spec pad (Z.of_nat memval_memsize -1)%Z); [ | rewrite Bool.andb_false_r; right; intros contra; inversion contra as [ | ?b [ | ] | | | ]; congruence ].
      destruct (Z.eqb_spec (Integers.Int.unsigned i) 0%Z); [ now subst; repeat constructor | ].
      destruct (Z.eqb_spec (Integers.Int.unsigned i) 1%Z); [ now subst; repeat constructor | right; intros contra; inversion contra; firstorder ].
    - destruct init
        as [ | [ | |i| | | | | ] [ | [ | | | | | |pad|] [ | ? ? ] ] ];
        try (apply ReflectF; intros H; inversion H; congruence).
      destruct (Z.eqb_spec pad (Z.of_nat memval_memsize - 4));
        [ subst; now repeat constructor | right; intros contra; inversion contra; congruence ].
    - right; intros contra; inversion contra.
    - destruct Archi.ptr64 eqn:E;
        destruct init as [ | [ | |i|i| | | | ] [ | ? ? ] ]; cbn;
        try (apply ReflectF; intros H; inversion H; congruence).
      + destruct (Z.eqb_spec (Integers.Int64.unsigned i) 0%Z) as [ EQ0 | NE0 ]; [ left; rewrite (Integers.Int64.same_if_eq i Integers.Int64.zero); [ now constructor | now unfold Integers.Int64.eq, Coqlib.zeq; rewrite EQ0, Integers.Int64.unsigned_zero ] | right; intros contra; inversion contra; subst; apply NE0, Integers.Int64.unsigned_zero ].
      + destruct (Z.eqb_spec (Integers.Int.unsigned i) 0%Z) as [ EQ0 | NE0]; [ left; rewrite (Integers.Int.same_if_eq i Integers.Int.zero); [ now constructor | now unfold Integers.Int.eq, Coqlib.zeq; rewrite EQ0, Integers.Int.unsigned_zero] | right; intros contra; inversion contra; subst; apply NE0, Integers.Int.unsigned_zero ].
    - right; intros contra; inversion contra.
  Qed.

  Lemma wt_globvar_init_size [cmd f_extra ctx id globvar]
    (WT: wt_globvar cmd f_extra ctx id globvar)
    : AST.init_data_list_size globvar.(AST.gvar_init) = Z.of_nat memval_memsize.
  Proof.
    destruct WT as [_ [ ] _ _];
      first [ reflexivity | discriminate ].
  Qed.

End Facts.

Definition type_external_function (ef: AST.external_function) : bool :=
  match Facts.ef_sig_dec ef with
  | Some _ => true
  | None => false
  end.

Definition type_function [cmd f_extra: Set]
  (type_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (ctx: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef)
  (func: function cmd f_extra) : bool :=
  ground func.(fn_return)
  && forallb (fun idt => ground (snd idt)) func.(fn_params)
  && forallb (fun idt => ground (snd idt)) func.(fn_temps)
  && (match type_cmd (mk_function_ctxt func.(fn_params) func.(fn_temps) ctx)
                     func.(fn_body) with
      | Some t => type_eqb t func.(fn_return)
      | None => false
      end)
  && type_f_extra func.(fn_extra)
  && ListExt.sbinds Pos.eqb func.(fn_params)
  && ListExt.sbinds Pos.eqb func.(fn_temps)
  && forallb (fun idt => negb (existsb (fun idt' => Pos.eqb (fst idt') (fst idt))
                                        func.(fn_temps)))
             func.(fn_params).

Definition type_fundef [cmd f_extra: Set]
  (type_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (ctx: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef)
  (fd: fundef cmd f_extra) : bool :=
  match fd with
  | AST.Internal func => type_function type_cmd type_f_extra ctx func
  | AST.External ef => type_external_function ef
  end.

Definition type_globvar [cmd f_extra: Set]
  (ctx: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef)
  (id: AST.ident) (gv: AST.globvar vardef) : bool :=
  ground gv.(AST.gvar_info).(var_type)
  && type_init_data gv.(AST.gvar_init) gv.(AST.gvar_info).(var_type)
  && negb gv.(AST.gvar_readonly)
  && negb gv.(AST.gvar_volatile).

Definition type_globdef [cmd f_extra: Set]
  (type_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (ctx: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef)
  (id: AST.ident) (gd: globdef cmd f_extra) : bool :=
  match gd with
  | AST.Gfun f => type_fundef type_cmd type_f_extra ctx f
  | AST.Gvar v => type_globvar ctx id v
  end.

Definition type_prog_defs [cmd f_extra: Set]
  (type_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (ctx: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef)
  (defs: list (AST.ident * globdef cmd f_extra)) : bool :=
  ListExt.fold_left_b
    (fun ctx idg => type_globdef type_cmd type_f_extra ctx (fst idg) (snd idg))
    (fun ctx idg => Ctxt.add_global ctx idg)
    ctx defs.

Definition type_program [cmd f_extra p_extra: Set]
  (type_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (type_p_extra: program cmd f_extra p_extra -> bool)
  (p: program cmd f_extra p_extra) : bool :=
  type_prog_defs type_cmd type_f_extra
                 (ctxt_emp _ _ _ _ p.(prog_public)) p.(prog_defs)
  && forallb
       (fun id => existsb (fun idg => Pos.eqb (fst idg) id) p.(prog_defs))
       p.(prog_public)
  && existsb
       (fun idg => Pos.eqb (fst idg) p.(prog_main)
                   && match snd idg with AST.Gfun _ => true | _ => false end)
       p.(prog_defs)
  && ListExt.sbinds Pos.eqb p.(prog_defs)
  && ListExt.sorted_strict_b Pos.ltb p.(prog_public)
  && type_p_extra p.

Lemma type_external_function_spec ef:
  Bool.reflect (wt_external_function ef) (type_external_function ef).
Proof.
  unfold type_external_function.
  destruct (Facts.ef_sig_dec ef) as [sig|] eqn:E.
  - apply Facts.ef_sig_dec_spec in E.
    apply ReflectT.
    destruct E as [nm t_arg xt H | | ];
      first [ econstructor; econstructor; eassumption
            | constructor
            | constructor ].
  - apply ReflectF.
    intros W.
    enough (exists sig, ext_funsig ef sig) as [sig Hsig].
    { apply Facts.ef_sig_dec_spec in Hsig; rewrite Hsig in E; discriminate. }
    destruct W as [ | | nm sig_cc sig_gc SIG ].
    + eexists; constructor.
    + eexists; constructor.
    + eexists; eassumption.
Qed.

Lemma type_function_complete [cmd f_extra: Set]
  [wt_f_extra: f_extra -> Type]
  [wt_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Type]
  (type_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (HCMD: forall ctx c t, wt_cmd ctx c t -> type_cmd ctx c = Some t)
  (HFE: forall fx, wt_f_extra fx -> type_f_extra fx = true)
  ctx func
  (WT: wt_function f_extra wt_f_extra wt_cmd ctx func):
  type_function type_cmd type_f_extra ctx func = true.
Proof.
  destruct WT as [HR HP HT Hcmd Hextra Hpsb Htsb Hdist].
  unfold type_function.
  apply Bool.andb_true_iff; split;
    [ apply Bool.andb_true_iff; split;
      [ apply Bool.andb_true_iff; split;
        [ apply Bool.andb_true_iff; split;
          [ apply Bool.andb_true_iff; split;
            [ apply Bool.andb_true_iff; split;
              [ apply Bool.andb_true_iff; split |] |] |] |] |] |].
  - exact (proj1 (Bool.reflect_iff _ _ (ground_spec _)) HR).
  - apply forallb_forall; intros idt HIn.
    exact (proj1 (Bool.reflect_iff _ _ (ground_spec _))
                 (proj1 (Forall_forall _ _) HP idt HIn)).
  - apply forallb_forall; intros idt HIn.
    exact (proj1 (Bool.reflect_iff _ _ (ground_spec _))
                 (proj1 (Forall_forall _ _) HT idt HIn)).
  - rewrite (HCMD _ _ _ Hcmd); apply type_eqb_refl.
  - exact (HFE _ Hextra).
  - exact (proj1 (Bool.reflect_iff _ _ (ListExt.sbinds_spec _ Pos.eqb_spec _)) Hpsb).
  - exact (proj1 (Bool.reflect_iff _ _ (ListExt.sbinds_spec _ Pos.eqb_spec _)) Htsb).
  - apply forallb_forall; intros idt HIn.
    apply Bool.negb_true_iff, Bool.not_true_iff_false.
    intros contra.
    apply existsb_exists in contra as [idt' [HIn' Heqb]].
    apply Pos.eqb_eq in Heqb.
    apply (proj1 (Forall_forall _ _) Hdist idt HIn).
    exists idt'; split; assumption.
Qed.

Lemma type_function_correct [cmd f_extra: Set]
  [wt_f_extra: f_extra -> Type]
  [wt_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Type]
  (type_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (HCMD: forall ctx c t, type_cmd ctx c = Some t -> wt_cmd ctx c t)
  (HFE: forall fx, type_f_extra fx = true -> wt_f_extra fx)
  ctx func
  (H: type_function type_cmd type_f_extra ctx func = true):
  wt_function f_extra wt_f_extra wt_cmd ctx func.
Proof.
  unfold type_function in H.
  apply Bool.andb_true_iff in H; destruct H as [H Hdist].
  apply Bool.andb_true_iff in H; destruct H as [H Htsb].
  apply Bool.andb_true_iff in H; destruct H as [H Hpsb].
  apply Bool.andb_true_iff in H; destruct H as [H Hextra].
  apply Bool.andb_true_iff in H; destruct H as [H Hmatch].
  apply Bool.andb_true_iff in H; destruct H as [H HT].
  apply Bool.andb_true_iff in H; destruct H as [HR HP].
  destruct (type_cmd (mk_function_ctxt _ _ _) (fn_body func)) as [t|] eqn:ETC;
    [| discriminate Hmatch].
  apply type_eqb_eq in Hmatch; subst t.
  refine {|
    wt_fn_return := _;
    wt_fn_params := _;
    wt_fn_temps := _;
    wt_fn_cmd := HCMD _ _ _ ETC;
    wt_fn_extra := HFE _ Hextra;
    wt_fn_params_sbinds := _;
    wt_fn_temps_sbinds := _;
    wt_fn_params_temps_distinct := _;
  |}.
  - exact (proj2 (Bool.reflect_iff _ _ (ground_spec _)) HR).
  - apply Forall_forall; intros idt HIn.
    apply (proj2 (Bool.reflect_iff _ _ (ground_spec _))).
    revert idt HIn. apply forallb_forall, HP.
  - apply Forall_forall; intros idt HIn.
    apply (proj2 (Bool.reflect_iff _ _ (ground_spec _))).
    revert idt HIn. apply forallb_forall, HT.
  - exact (proj2 (Bool.reflect_iff _ _ (ListExt.sbinds_spec _ Pos.eqb_spec _)) Hpsb).
  - exact (proj2 (Bool.reflect_iff _ _ (ListExt.sbinds_spec _ Pos.eqb_spec _)) Htsb).
  - apply Forall_forall; intros idt HIn [idt' [HIn' Heq]].
    pose proof (proj1 (forallb_forall _ _) Hdist idt HIn) as HD.
    apply Bool.negb_true_iff, Bool.not_true_iff_false in HD.
    apply HD, existsb_exists.
    exists idt'; split; [exact HIn' | apply Pos.eqb_eq; auto].
Qed.

Lemma type_fundef_complete [cmd f_extra: Set]
  [wt_f_extra: f_extra -> Type]
  [wt_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Type]
  (type_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (HCMD: forall ctx c t, wt_cmd ctx c t -> type_cmd ctx c = Some t)
  (HFE: forall fx, wt_f_extra fx -> type_f_extra fx = true)
  ctx fd
  (WT: wt_fundef f_extra wt_f_extra wt_cmd ctx fd):
  type_fundef type_cmd type_f_extra ctx fd = true.
Proof.
  destruct WT as [? func Hfn | ? ef Hef]; cbn [type_fundef].
  - eapply type_function_complete; eassumption.
  - exact (proj1 (Bool.reflect_iff _ _ (type_external_function_spec _)) Hef).
Qed.

Lemma type_fundef_correct [cmd f_extra: Set]
  [wt_f_extra: f_extra -> Type]
  [wt_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Type]
  (type_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (HCMD: forall ctx c t, type_cmd ctx c = Some t -> wt_cmd ctx c t)
  (HFE: forall fx, type_f_extra fx = true -> wt_f_extra fx)
  ctx fd
  (H: type_fundef type_cmd type_f_extra ctx fd = true):
  wt_fundef f_extra wt_f_extra wt_cmd ctx fd.
Proof.
  destruct fd as [func | ef]; cbn [type_fundef] in H.
  - apply wt_Internal. eapply type_function_correct; eassumption.
  - apply wt_External.
    exact (proj2 (Bool.reflect_iff _ _ (type_external_function_spec _)) H).
Qed.

Lemma type_globvar_spec [cmd f_extra: Set] ctx id (gv: AST.globvar vardef):
  Bool.reflect (wt_globvar cmd f_extra ctx id gv) (type_globvar ctx id gv).
Proof.
  unfold type_globvar.
  destruct (ground_spec gv.(AST.gvar_info).(var_type)) as [HG | HnG]; cbn [andb];
    [| apply ReflectF; intros [HG _ _ _]; contradiction ].
  destruct (Facts.type_init_data_spec gv.(AST.gvar_init) gv.(AST.gvar_info).(var_type))
    as [HI | HnI]; cbn [andb];
    [| apply ReflectF; intros [_ HI _ _]; contradiction ].
  destruct gv.(AST.gvar_readonly) eqn:ER; cbn [negb andb];
    [ apply ReflectF; intros [_ _ HR _]; rewrite ER in HR; discriminate |].
  destruct gv.(AST.gvar_volatile) eqn:EV; cbn [negb];
    [ apply ReflectF; intros [_ _ _ HV]; rewrite EV in HV; discriminate |].
  apply ReflectT; constructor; assumption.
Qed.

Lemma type_globdef_spec [cmd f_extra: Set]
  [wt_f_extra: f_extra -> Type]
  [wt_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Type]
  (type_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (HCMD_complete: forall ctx c t, wt_cmd ctx c t -> type_cmd ctx c = Some t)
  (HCMD_correct: forall ctx c t, type_cmd ctx c = Some t -> wt_cmd ctx c t)
  (HFE_complete: forall fx, wt_f_extra fx -> type_f_extra fx = true)
  (HFE_correct: forall fx, type_f_extra fx = true -> wt_f_extra fx)
  ctx id gd:
  Bool.reflect (wt_globdef f_extra wt_f_extra wt_cmd ctx id gd)
               (type_globdef type_cmd type_f_extra ctx id gd).
Proof.
  destruct gd as [f | v]; cbn [type_globdef].
  - destruct (type_fundef type_cmd type_f_extra ctx f) eqn:E.
    + apply ReflectT, wt_Gfun.
      eapply type_fundef_correct; eassumption.
    + apply ReflectF. intros W; inversion W as [? ? f' Hf | ]; subst.
      pose proof (type_fundef_complete type_cmd type_f_extra HCMD_complete HFE_complete _ _ Hf) as Heq.
      congruence.
  - destruct (type_globvar_spec ctx id v).
    + apply ReflectT, wt_Gvar; assumption.
    + apply ReflectF. intros W; inversion W as [ | ? ? v' Hv]; subst.
      contradiction.
Qed.

Lemma type_prog_defs_complete [cmd f_extra: Set]
  [wt_f_extra: f_extra -> Type]
  [wt_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Type]
  (type_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (HCMD_complete: forall ctx c t, wt_cmd ctx c t -> type_cmd ctx c = Some t)
  (HCMD_correct: forall ctx c t, type_cmd ctx c = Some t -> wt_cmd ctx c t)
  (HFE_complete: forall fx, wt_f_extra fx -> type_f_extra fx = true)
  (HFE_correct: forall fx, type_f_extra fx = true -> wt_f_extra fx)
  ctx defs
  (FF: ListExt.FoldLeft
         (fun ctx idg => wt_globdef f_extra wt_f_extra wt_cmd ctx (fst idg) (snd idg))
         (fun ctx idg => Ctxt.add_global ctx idg) ctx defs) :
  type_prog_defs type_cmd type_f_extra ctx defs = true.
Proof.
  unfold type_prog_defs.
  induction FF as [| acc x rest Hx HFFrest IH]; cbn.
  - reflexivity.
  - apply Bool.andb_true_iff; split; [| exact IH ].
    exact (proj1 (Bool.reflect_iff _ _
                    (type_globdef_spec type_cmd type_f_extra
                       HCMD_complete HCMD_correct HFE_complete HFE_correct _ _ _)) Hx).
Qed.

Lemma type_prog_defs_correct [cmd f_extra: Set]
  [wt_f_extra: f_extra -> Type]
  [wt_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Type]
  (type_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (HCMD_complete: forall ctx c t, wt_cmd ctx c t -> type_cmd ctx c = Some t)
  (HCMD_correct: forall ctx c t, type_cmd ctx c = Some t -> wt_cmd ctx c t)
  (HFE_complete: forall fx, wt_f_extra fx -> type_f_extra fx = true)
  (HFE_correct: forall fx, type_f_extra fx = true -> wt_f_extra fx)
  ctx defs
  (H: type_prog_defs type_cmd type_f_extra ctx defs = true) :
  ListExt.FoldLeft
    (fun ctx idg => wt_globdef f_extra wt_f_extra wt_cmd ctx (fst idg) (snd idg))
    (fun ctx idg => Ctxt.add_global ctx idg) ctx defs.
Proof.
  unfold type_prog_defs in H.
  revert ctx H. induction defs as [| idg rest IH]; intros ctx H; cbn in H.
  - constructor.
  - apply Bool.andb_true_iff in H as [Hidg Hrest].
    constructor.
    + exact (proj2 (Bool.reflect_iff _ _
                      (type_globdef_spec type_cmd type_f_extra
                         HCMD_complete HCMD_correct HFE_complete HFE_correct _ _ _)) Hidg).
    + apply IH; exact Hrest.
Qed.

Lemma type_program_spec [cmd f_extra p_extra: Set]
  [wt_f_extra: f_extra -> Type]
  [wt_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Type]
  [wt_p_extra: program cmd f_extra p_extra -> Prop]
  (type_cmd: ctxt (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (type_p_extra: program cmd f_extra p_extra -> bool)
  (HCMD_complete: forall ctx c t, wt_cmd ctx c t -> type_cmd ctx c = Some t)
  (HCMD_correct: forall ctx c t, type_cmd ctx c = Some t -> wt_cmd ctx c t)
  (HFE_complete: forall fx, wt_f_extra fx -> type_f_extra fx = true)
  (HFE_correct: forall fx, type_f_extra fx = true -> wt_f_extra fx)
  (HPE_spec: forall p, Bool.reflect (wt_p_extra p) (type_p_extra p))
  p:
  Bool.reflect (wt_program wt_f_extra wt_cmd wt_p_extra p)
               (type_program type_cmd type_f_extra type_p_extra p).
Proof.
  unfold type_program.
  apply Bool.iff_reflect; split.
  - intros [Hdefs Hpub Hmain Hsb Hsort Hpe].
    repeat (apply Bool.andb_true_iff; split).
    + eapply type_prog_defs_complete; eassumption.
    + apply forallb_forall; intros id HId.
      destruct (Hpub id HId) as [gd HIn].
      apply existsb_exists. exists (id, gd); split; [exact HIn |].
      apply Pos.eqb_eq; reflexivity.
    + destruct Hmain as [f_main Hmain].
      apply existsb_exists. exists (prog_main p, AST.Gfun f_main).
      split; [exact Hmain |].
      apply Bool.andb_true_iff; split.
      * apply Pos.eqb_eq; reflexivity.
      * reflexivity.
    + exact (proj1 (Bool.reflect_iff _ _ (ListExt.sbinds_spec _ Pos.eqb_spec _)) Hsb).
    + exact (proj1 (Bool.reflect_iff _ _ (ListExt.sorted_strict_b_spec _ _ Pos.ltb_spec0 _)) Hsort).
    + exact (proj1 (Bool.reflect_iff _ _ (HPE_spec p)) Hpe).
  - intros H.
    apply Bool.andb_true_iff in H as [H Hpe].
    apply Bool.andb_true_iff in H as [H Hsort].
    apply Bool.andb_true_iff in H as [H Hsb].
    apply Bool.andb_true_iff in H as [H Hmain].
    apply Bool.andb_true_iff in H as [Hdefs Hpub].
    refine {|
      wt_prog_defs := _;
      wt_prog_public := _;
      wt_prog_main := _;
      wt_prog_defs_sbinds := _;
      wt_prog_public_nodup := _;
      wt_prog_extra := _;
    |}.
    + eapply type_prog_defs_correct; eassumption.
    + intros id HId.
      pose proof (proj1 (forallb_forall _ _) Hpub id HId) as Hex.
      apply existsb_exists in Hex as [[id' gd] [HIn Heq]].
      cbn in Heq; apply Pos.eqb_eq in Heq; subst id'.
      exists gd; exact HIn.
    + apply existsb_exists in Hmain as [[id gd] [HIn Heq]].
      cbn in Heq.
      apply Bool.andb_true_iff in Heq as [Hid Hgf].
      apply Pos.eqb_eq in Hid; subst id.
      destruct gd as [f | v]; [| discriminate Hgf].
      exists f; exact HIn.
    + exact (proj2 (Bool.reflect_iff _ _ (ListExt.sbinds_spec _ Pos.eqb_spec _)) Hsb).
    + exact (proj2 (Bool.reflect_iff _ _ (ListExt.sorted_strict_b_spec _ _ Pos.ltb_spec0 _)) Hsort).
    + exact (proj2 (Bool.reflect_iff _ _ (HPE_spec p)) Hpe).
Qed.
