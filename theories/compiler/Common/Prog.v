From Stdlib Require Import ZArith.

From compcert.common Require AST Globalenvs.
Import Globalenvs(Genv.t).

From Utils Require Import ListExt.

From Compiler.Common Require Import Types Value CCInj Ctxt.

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
    (ListExt.filter_map xtype_of_type s.(sig_args))
    (ssrfun.Option.default AST.Xvoid (xtype_of_type s.(sig_res)))
    AST.cc_default.
Coercion signature_of_signature: signature >-> AST.signature.

Definition fn_signature [cmd extra: Set] (f: function cmd extra): signature :=
  mk_signature
    (List.map snd f.(fn_params))
    f.(fn_return)
.

Inductive funsig {cmd extra: Set}: (fundef cmd extra) -> signature -> Prop :=
| funsig_Internal: forall f, funsig (AST.Internal f) (fn_signature f)
| funsig_malloc: funsig (AST.External AST.EF_malloc) (mk_signature [t_ofst] t_ptr)
| funsig_free: funsig (AST.External AST.EF_free) (mk_signature [t_ptr] t_unit)
.

Definition globdef cmd extra := (AST.globdef (fundef cmd extra) vardef).
Definition genv cmd extra := (Genv.t (fundef cmd extra) vardef).

Record program (cmd f_extra p_extra: Set) :=
  mkprogram
    {
      prog_defs: list (AST.ident * (globdef cmd f_extra));
      prog_public: list AST.ident;
      prog_main: AST.ident;
      (* prog_malloc: option AST.ident; *)
      (* prog_free: option AST.ident; *)
      (* prog_next_id : AST.ident; *)
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
Definition mk_function_ctxt [cmd f_extra] (temps: list (AST.ident * type)) (ctx: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef): ctxt (type * bool) Empty_set (fundef cmd f_extra) vardef :=
  Ctxt.with_pure
    (Maps.PTree_Properties.of_list (List.map mk_uninit_pair temps))
    ctx.

Definition globdef_type [cmd f_extra] (gdef: globdef cmd f_extra): type :=
  match gdef with
  | AST.Gfun (AST.Internal f) => t_fun (List.map snd f.(fn_params)) f.(fn_return)
  | AST.Gfun (AST.External AST.EF_malloc) => t_fun [t_nat] t_ptr
  | AST.Gfun (AST.External AST.EF_free) => t_fun [t_ptr] t_unit
  | AST.Gfun (AST.External _) => t_fun [] t_unit
  | AST.Gvar v => v.(AST.gvar_info).(var_type)
  end.

Definition mk_glob_ctxt [cmd f_extra p_extra] (p: program cmd f_extra p_extra): ctxt Empty_set Empty_set (fundef cmd f_extra) vardef :=
  with_global (Globalenvs.Genv.globalenv p) (ctxt_emp Empty_set Empty_set Empty_set Empty_set []).

(* ctx here is the global program context *)
Record wt_function [cmd: Set] (f_extra: Set) (wt_f_extra: f_extra -> Prop) (wt_cmd: ctxt (type * bool) Empty_set (fundef cmd f_extra) vardef -> cmd -> type -> Prop) (ctx: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef) (func: (function cmd f_extra)): Prop :=
  {
    wt_fn_return: ground func.(fn_return);
    wt_fn_params: List.Forall (fun idt => ground (snd idt)) func.(fn_params);
    wt_fn_temps: List.Forall (fun idt => ground (snd idt)) func.(fn_temps);
    wt_fn_cmd: wt_cmd (mk_function_ctxt func.(fn_temps) ctx) func.(fn_body) func.(fn_return);
    wt_fn_extra: wt_f_extra func.(fn_extra);

    wt_fn_params_sbinds: SBinds func.(fn_params);
    wt_fn_temps_sbinds: SBinds func.(fn_temps);
    wt_fn_params_temps_distinct: List.Forall (fun idt => ~exists idt', (In idt' func.(fn_temps) /\ fst idt' = fst idt)) func.(fn_params);
  }.

Inductive wt_external_function: AST.external_function -> Prop :=
| wt_EF_malloc: wt_external_function AST.EF_malloc
| wt_EF_free: wt_external_function AST.EF_free
.

Inductive wt_fundef [cmd: Set] (f_extra: Set) (wt_f_extra: f_extra -> Prop) (wt_cmd: ctxt (type * bool) Empty_set (fundef cmd f_extra) vardef -> cmd -> type -> Prop): ctxt Empty_set Empty_set (fundef cmd f_extra) vardef -> (fundef cmd f_extra) -> Prop :=
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
| wt_init_data_unit: wt_init_data [ AST.Init_space 0%Z ] t_unit
| wt_init_data_bool: forall n, (Integers.Int.unsigned n = 0%Z \/ Integers.Int.unsigned n = 1%Z) -> wt_init_data [ AST.Init_int8 n ] t_bool
| wt_init_data_nat: forall n, wt_init_data [ AST.Init_int32 n ] t_nat
| wt_init_data_ptr64: forall n, Archi.ptr64 = true -> wt_init_data [ AST.Init_int64 n ] t_ptr
| wt_init_data_ptr32: forall n, Archi.ptr64 = false -> wt_init_data [ AST.Init_int32 n ] t_ptr
.

Record wt_globvar cmd f_extra (ctx: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef) (id: AST.ident) (globvar: AST.globvar vardef): Prop :=
  {
    wt_globvar_type_ground: Types.ground globvar.(AST.gvar_info).(var_type);
    wt_globvar_ctx: get_global id ctx = Some (AST.Gvar globvar);
    wt_globvar_init_len: List.length globvar.(AST.gvar_init) = 1;
    wt_globvar_init_type: wt_init_data globvar.(AST.gvar_init) globvar.(AST.gvar_info).(var_type);
    wt_globvar_readonly: globvar.(AST.gvar_readonly) = false;
    wt_globvar_volatile: globvar.(AST.gvar_volatile) = false;
  }.

Inductive wt_globdef [cmd] f_extra wt_f_extra wt_cmd: ctxt Empty_set Empty_set (fundef cmd f_extra) vardef -> AST.ident -> (globdef cmd f_extra) -> Prop :=
| wt_Gfun: forall ctx id f, wt_fundef f_extra wt_f_extra wt_cmd ctx f -> wt_globdef f_extra wt_f_extra wt_cmd ctx id (AST.Gfun f)
| wt_Gvar: forall ctx id v, wt_globvar cmd f_extra ctx id v -> wt_globdef f_extra wt_f_extra wt_cmd ctx id (AST.Gvar v)
.

Record wt_program [cmd f_extra p_extra: Set] wt_f_extra wt_cmd (wt_p_extra: program cmd f_extra p_extra -> Prop) (p: program cmd f_extra p_extra): Prop :=
  {
    wt_prog_defs: List.Forall (fun idglob => wt_globdef f_extra wt_f_extra wt_cmd (mk_glob_ctxt p) (fst idglob) (snd idglob)) p.(prog_defs);
    wt_prog_public: forall id, In id p.(prog_public) -> exists gdef, In (id,gdef) p.(prog_defs);
    wt_prog_main: exists f_main, In (p.(prog_main), AST.Gfun f_main) p.(prog_defs);
    wt_prog_defs_sbinds: SBinds p.(prog_defs);
    wt_prog_public_nodup: Sorted Pos.lt p.(prog_public);
    wt_prog_extra: wt_p_extra p
  }.

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

End Facts.
