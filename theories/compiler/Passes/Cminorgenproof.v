From Stdlib Require Import ZArith List Arith.
From Stdlib Require Import String.
Import ListNotations.

From compcert.common Require Linking Values.
From compcert.common Require Import Errors Globalenvs.
From compcert.lib Require Import Coqlib Integers Maps.
From compcert.cfrontend Require Cminorgenproof.
From compcert.backend Require Cminor.

From Imp Require Import Store Heap Intops Uint32 Uintptr.

From Compiler.Common Require Import Types(t_nat).
From Compiler.Common Require CCInj Value.
Import CCInj.Facts Value.Facts.
From Compiler.Passes Require Import Cminorgen.
From Compiler.Common Require Expr Ctxt.
From Compiler.IR Require Cmd Semantics Lemmas.
From Compiler.IR Require Import Prog Linker Typing.
(* Import Cmd.Facts Expr.Facts Ctxt.Facts Semantics.Facts. *)

Local Open Scope error_monad_scope.

Section Match.

  Inductive match_fundef (p: program) : IR.Prog.fundef -> Cminor.fundef -> Prop :=
  | match_fundef_internal: forall fn tfn,
      transl_function p.(prog_extra).(prog_malloc) p.(prog_extra).(Prog.prog_free) fn = OK tfn ->
      match_fundef p (AST.Internal fn) (AST.Internal tfn)
  | match_fundef_external: forall ef,
      match_fundef p (AST.External ef) (AST.External ef)
  .

  Definition match_varinfo (_: vardef) (_: unit) := True.

  Definition match_prog (p: program) (tp: Cminor.program) :=
    (* Matching succeeds, if *)
    Linking.match_program_gen
      match_fundef
      match_varinfo
      p
      (Prog.program_of_program p)
      tp
  .
  Lemma transf_program_match:
    forall p tp, transl_program p = OK tp -> match_prog p tp.
  Proof.
    unfold transl_program.
    intros p tp Htransl.
    eapply Linking.match_transform_partial_program2; [ exact Htransl | clear Htransl | clear Htransl ].
    - intros i fd tfd Htransl.
      destruct fd as [ fn | ef ];
        cbn in Htransl.
      + apply bind_inversion in Htransl as ( tfn & Htransl_fn & Htransl);
          inversion Htransl; subst; clear Htransl.
        now constructor.
      + inversion Htransl; subst.
        constructor.
    - intros i v tv Htransl.
      now constructor.
  Qed.

  Lemma match_program_main {p tp}:
    match_prog p tp -> AST.prog_main tp = Prog.prog_main p.
  Proof.
    intros Hmatch_prog.
    destruct Hmatch_prog as ( _ & Hmain & _ ).
    auto.
  Qed.

  Definition match_temps {St} inj (env: Semantics.env) (tenv: Cminor.env): Prop :=
    forall id v, Maps.PTree.get id env = Some v -> v = Value.v_tt \/ exists v', Maps.PTree.get id tenv = Some v' /\ @CCInj.inj_value St inj v v'.

  Inductive match_cont {St} (prog: Prog.program) (inj: @CCInj.injection St): compilenv -> @Semantics.cont St -> Cminor.cont -> Prop :=
  | match_cont_Kbind_Kseq: forall {cenv id_b c k tc tk}
                                  (TC: transl_cmd cenv (Semantics.cont_target k) c = OK tc)
                                  (MK: match_cont prog inj cenv k tk)
    , match_cont prog inj cenv (Semantics.Kbind id_b c k) (Cminor.Kseq tc tk)
  | match_cont_Kloop1: forall {cenv c_cond id_cond c_body id_body k tk tc_cond tc_body}
                              (TC_cond: transl_cmd cenv (Some id_cond) c_cond = OK tc_cond)
                              (TC_body: transl_cmd cenv (Some id_body) c_body = OK tc_body)
                              (MK: match_cont prog inj cenv k tk)
    , match_cont prog inj cenv
        (Semantics.Kloop1 c_cond id_cond c_body id_body k)
        (Cminor.Kseq (Cminor.Sifthenelse (Cminor.Evar id_cond) tc_body (Cminor.Sexit 0))
           (Cminor.Kseq
              (Cminor.Sloop
                 (Cminor.Sseq
                    tc_cond
                    (Cminor.Sifthenelse (Cminor.Evar id_cond) tc_body (Cminor.Sexit 0))))
              (Cminor.Kblock (Cminor.Kseq (return_or_assign_unsized (Semantics.cont_target k)) tk))))
  | match_cont_Kloop2: forall {cenv c_cond id_cond c_body id_body k tk tc_cond tc_body}
                              (TC_cond: transl_cmd cenv (Some id_cond) c_cond = OK tc_cond)
                              (TC_body: transl_cmd cenv (Some id_body) c_body = OK tc_body)
                              (MK: match_cont prog inj cenv k tk)
    , match_cont prog inj cenv
        (Semantics.Kloop2 c_cond id_cond c_body id_body k)
        (Cminor.Kseq
           (Cminor.Sloop
              (Cminor.Sseq
                 tc_cond
                 (Cminor.Sifthenelse (Cminor.Evar id_cond) tc_body (Cminor.Sexit 0))))
           (Cminor.Kblock (Cminor.Kseq (return_or_assign_unsized (Semantics.cont_target k)) tk)))
  | match_cont_Kcall: forall {fn e locals sp k target_id optid tfn te tk id_malloc id_free cenv'}
                             (TF: transl_funbody id_malloc id_free fn = OK tfn)
                             (ST: Semantics.seq_cont_target k target_id)
                             (OI: match ListExt.sfind Pos.eq_dec target_id fn.(fn_temps) with
                                  | Some Types.t_unit => optid = None
                                  | Some _ => optid = Some target_id
                                  | None => False
                                  end)
                             (MTEMPS: match_temps inj e te)
                             (MK: match_cont prog inj (mkcompilenv fn.(fn_temps) id_malloc id_free) k tk)
    , match_cont prog inj cenv' (Semantics.Kcall fn e locals sp k) (Cminor.Kcall optid tfn (Values.Vptr sp Ptrofs.zero) te tk)
  | match_cont_Kstop: forall cenv, match_cont prog inj cenv Semantics.Kstop Cminor.Kstop
  .

  Definition match_ctxt {P S} (ctx: Ctxt.ctxt P S _ _) (ge: genv): Prop :=
    Ctxt.ctxt_global ctx = ge.

  Record match_cenv (cenv: compilenv) (ctx: Ctxt.map_ctxt (Types.type * bool)) :=
    {
      temps_of_ty_ctxt: forall id t b, Maps.PTree.get id ctx = Some (t,b) -> List.In (id,t) cenv.(temps);
      temps_sbinds: ListExt.SBinds cenv.(temps);
    }.

  Inductive match_args {St} (inj: @CCInj.injection St): list Value.value -> list Values.val -> Prop :=
  | MARGS_nil: match_args inj [] []
  | MARGS_unit: forall v_args tv_args (MARGS: match_args inj v_args tv_args), match_args inj (Value.v_tt::v_args) tv_args
  | MARGS_sized: forall v_arg tv_arg v_args tv_args
                        (MARGS: match_args inj v_args tv_args)
                        (Hinj: CCInj.inj_value inj v_arg tv_arg),
      match_args inj (v_arg::v_args) (tv_arg::tv_args)
  .

  Inductive match_states {St Hp} (p: Prog.program): @Semantics.state St Hp -> Cminor.state -> Prop :=
  | match_state:
    forall fn c k e locals sp s m inj tfn tc tk te ctx t id_malloc id_free
           (WT: Semantics.wt_State fn c k e locals sp s m inj ctx t)
           (TFB: Cminorgen.transl_funbody id_malloc id_free fn = OK tfn)
           (TC: transl_cmd (mkcompilenv fn.(fn_temps) id_malloc id_free) (Semantics.cont_target k) c = OK tc)
           (MK: match_cont p inj (mkcompilenv fn.(fn_temps) id_malloc id_free) k tk)
           (MTEMPS: match_temps inj e te)
           (MCENV: match_cenv (mkcompilenv fn.(fn_temps) id_malloc id_free) (Ctxt.ctxt_pure ctx))
           (MCTXT: match_ctxt ctx (Globalenvs.Genv.globalenv (Prog.program_of_program p)))
    , match_states p (Semantics.State fn c k e locals sp s m inj) (Cminor.State tfn tc tk (Values.Vptr sp Ptrofs.zero) te m)
  | match_callstate:
    forall fd args k m s inj tfd targs tk i cenv
           (WT: Semantics.wt_state p (Semantics.Callstate fd args k s m inj))
           (TFD: Cminorgen.transl_fundef p.(prog_extra).(prog_malloc) p.(prog_extra).(prog_free) i fd = OK tfd)
           (MARGS: match_args inj args targs)
           (MK: match_cont p inj cenv k tk)
    ,
      match_states p (Semantics.Callstate fd args k s m inj)
        (Cminor.Callstate tfd targs tk m)
  | match_returnstate:
    forall r k m s inj tr tk cenv
           (WT: Semantics.wt_state p (Semantics.Returnstate r k s m inj))
           (MRET: r = Value.v_tt \/ CCInj.inj_value inj r tr)
           (MK: match_cont p inj cenv k tk),
      match_states p (Semantics.Returnstate r k s m inj)
        (Cminor.Returnstate tr tk m)
  .

End Match.

Arguments temps_of_ty_ctxt {cenv ctx}.
Arguments temps_sbinds {cenv ctx}.

Section EXPRESSIONS_HELPER.

  (* Import Intops.CompCert. *)

  Lemma transl_expr_maybe_sized_mem_chunk_correct:
    forall {e t ctx cenv}
           (MCENV: match_cenv cenv ctx)
           (Hwt_expr: Expr.wt_expr ctx e t),
    exists r, transl_expr_maybe_sized cenv e t = OK r /\
                (t = Types.t_unit /\ r = None \/ exists e' mc, CCInj.type_mem_chunk t = Some mc /\ r = Some (e',mc)).
  Proof.
    intros e t ctx cenv MCENV Hwt_expr.
    induction Hwt_expr; cbn.
    - specialize (ListExt.BindIn_findA_reflect_eq Pos.eqb_spec
                    (ListExt.SBindIn_BindIn
                       (ListExt.SBinds_In
                          MCENV.(temps_sbinds)
                                  (MCENV.(temps_of_ty_ctxt) var_id t true Hget_env))
                 ))
        as Hrewrite;
        rewrite Hrewrite, Types.type_eqb_refl; clear Hrewrite.
      destruct Hground; cbn;
        eexists; split; try reflexivity; now repeat econstructor.
    - eexists; split; auto; now constructor.
    - eexists; (split; [ auto | right; eexists; eexists; eauto ]).
    - eexists; (split; [ auto | right; eexists; eexists; eauto ]).
    - eexists; (split; [ auto | right; eexists; eexists; eauto ]).
    - eexists; (split; [ auto | right; eexists; eexists; eauto ]).
    - destruct IHHwt_expr as ( [ ( e' & mc ) | ] & Htransl_b & [ ( Hneq & _ ) | ( e'' & mc'' & Htype_mc & Heq )  ]);
        try discriminate.
      inversion Heq; subst; clear Heq.
      cbn in Htype_mc; inversion Htype_mc; subst; clear Htype_mc.
      exists (Some (make_bool_not e'', AST.Mbool)).
      rewrite Htransl_b; cbn.
      split; [ auto | right; eexists; eexists; split; auto ].
    - destruct IHHwt_expr1 as ( [ ( n1' & mc1 ) | ] & Htransl_n1 & [ ( H1 & H2 ) | (n1'' & mc1'' & Htype_mc1 & Heq ) ] );
        try discriminate;
        inversion Heq; subst n1'' mc1''; clear Heq;
        inversion Htype_mc1; subst; clear Htype_mc1.
      destruct IHHwt_expr2 as ( [ ( n2' & mc2 ) | ] & Htransl_n2 & [ ( H1 & H2 ) | (n2'' & mc2'' & Htype_mc2 & Heq ) ] );
        try discriminate;
        inversion Heq; subst n2'' mc2''; clear Heq;
        inversion Htype_mc2; subst; clear Htype_mc2.
      rewrite Htransl_n1; cbn.
      rewrite Htransl_n2; cbn.
      eexists; split; [ auto | right; eauto ].
    - destruct IHHwt_expr1 as ( [ ( n1' & mc1 ) | ] & Htransl_n1 & [ ( H1 & H2 ) | (n1'' & mc1'' & Htype_mc1 & Heq ) ] );
        try discriminate;
        inversion Heq; subst n1'' mc1''; clear Heq;
        inversion Htype_mc1; subst; clear Htype_mc1.
      destruct IHHwt_expr2 as ( [ ( n2' & mc2 ) | ] & Htransl_n2 & [ ( H1 & H2 ) | (n2'' & mc2'' & Htype_mc2 & Heq ) ] );
        try discriminate;
        inversion Heq; subst n2'' mc2''; clear Heq;
        inversion Htype_mc2; subst; clear Htype_mc2.
      rewrite Htransl_n1; cbn.
      rewrite Htransl_n2; cbn.
      eexists; split; [ auto | right; eauto ].
  Qed.

  Lemma transl_expr_sized_progress {St ctx e t cenv e' mc f env v inj tenv}
    (Hwt_expr: Expr.wt_expr ctx e t)
    (Htransl_sized: transl_expr_sized cenv e t = OK (e', mc))
    (Hwt_env: Semantics.wt_env f ctx env)
    (MCENV: match_cenv cenv ctx)
    (Hmatch_temps: match_temps inj env tenv)
    (Heval: Semantics.eval e env = Some v):
    exists tv, (forall tge sp m, Cminor.eval_expr tge sp tenv m e' tv) /\ @CCInj.inj_value St inj v tv.
  Proof.
    revert e' mc v Htransl_sized Heval.
    induction Hwt_expr; simpl; intros.
    - destruct (Maps.PTree.get var_id env) eqn:Eget_val_env; [ inversion Heval; subst; clear Heval | discriminate ].
      specialize (MCENV.(temps_of_ty_ctxt) var_id t true Hget_env) as HIn.
      unfold transl_expr_sized in Htransl_sized;
        cbn in Htransl_sized.
      apply bind_inversion in Htransl_sized as ( [  | ] & Htransl_sized & Heq );
        inversion Heq; subst; clear Heq.
      rewrite (ListExt.BindIn_findA_reflect_eq
                 Pos.eqb_spec
                 (ListExt.SBindIn_BindIn
                    (ListExt.SBinds_In MCENV.(temps_sbinds) HIn)
              )),
        Types.type_eqb_refl
        in Htransl_sized.
      destruct (CCInj.type_mem_chunk t) eqn:Etype_mc; try discriminate.
      inversion Htransl_sized; subst; clear Htransl_sized.
      specialize (Hmatch_temps var_id v Eget_val_env) as [ Heq | ( tv & Htenv_get & Hval_cc ) ]; subst.
      {
        exfalso.
        specialize (Hwt_env.(Semantics.wv_ty_env) var_id t true Hget_env) as ( (v & Eget_val_env' & Hwt_val ) & Hfn_temps ).
        assert (v = Value.v_tt) by congruence; subst.
        now inversion Hwt_val; subst.
      }
      exists tv.
      split; [ | assumption ].
      now econstructor.
    - now cbn in Htransl_sized.
    - inversion Htransl_sized; subst.
      inversion Heval; subst; clear Heval.
      exists (if b then Values.Vint Int.one else Values.Vint Int.zero).
      split; [ constructor; destruct b; reflexivity | constructor ].
    - inversion Htransl_sized; subst; clear Htransl_sized.
      inversion Heval; subst; clear Heval.
      exists (Values.Vint (Int.repr (Z.of_nat n))).
      split.
      now constructor.
      constructor.
      auto.
      apply Int.unsigned_repr.
      eauto with ints.
    - inversion Htransl_sized; subst; clear Htransl_sized.
      inversion Heval; subst.
      destruct (Archi.ptr64) eqn:Earchi;
        eexists; (split; [ unfold make_size_t; rewrite Earchi; now constructor | ];
                  specialize Uintptr.CompCert.unsigned_range_cc as Hrange; rewrite Earchi in Hrange).
      constructor; [ auto | rewrite Earchi; eexists; split; [ | eauto ]; now apply Int64.unsigned_repr, Hrange ].
      constructor; [ auto | rewrite Earchi; eexists; split; [ | eauto ]; now apply Int.unsigned_repr, Hrange ].
    - inversion Htransl_sized; subst.
      inversion Heval; subst; clear Heval.
      exists Values.Vnullptr.
      split.
      now constructor.
      constructor.
    - unfold transl_expr_sized in Htransl_sized.
      apply bind_inversion in Htransl_sized.
      destruct Htransl_sized as ( [ ( e'' & mc' ) | ] & Htransl_maybe_sized & Htransl ); [ | discriminate ].
      inversion Htransl; subst; clear Htransl.
      cbn in Htransl_maybe_sized.
      apply bind_inversion in Htransl_maybe_sized.
      destruct Htransl_maybe_sized as ( [ ( e'' & mc' ) | ] & Htransl_maybe_sized & Htransl ); [ | discriminate ].
      destruct mc'; try discriminate; inversion Htransl; subst; clear Htransl.
      destruct (Semantics.eval b env) as [ [ | | | | ] | ] eqn:Eeval; try discriminate.
      inversion Heval; subst; clear Heval.
      unfold transl_expr_sized in IHHwt_expr.
      specialize (IHHwt_expr e'' AST.Mbool (Value.v_bool b0) ltac:(rewrite Htransl_maybe_sized; now eauto) ltac:(auto)) as (tv & Heval_expr & Hvalue_cc ).
      exists (Values.Val.notbool tv).
      inversion Hvalue_cc; subst; clear Hvalue_cc.
      split.
      + unfold make_bool_not.
        econstructor.
        * apply Heval_expr.
        * now econstructor.
        * cbn.
          unfold Values.Val.notbool.
          (destruct b0; cbn); [
              rewrite Int.eq_false; [ reflexivity | apply Int.one_not_zero ]
            | now rewrite Int.eq_true ].
      + destruct b0; now constructor.
    - unfold transl_expr_sized in Htransl_sized.
      apply bind_inversion in Htransl_sized;
        destruct Htransl_sized as ( [ ( e'' & mc' ) | ] & Htransl_maybe_sized & Htransl ); [ | discriminate ].
      inversion Htransl; subst; clear Htransl.
      cbn in Htransl_maybe_sized;
        apply bind_inversion in Htransl_maybe_sized;
        destruct Htransl_maybe_sized as ( [ ( l' & mc_l' ) | ] & Htransl_maybe_sized_n1 & Htransl_maybe_sized' );
        apply bind_inversion in Htransl_maybe_sized';
        destruct Htransl_maybe_sized' as ( [ ( r' & mc_r' ) | ] & Htransl_maybe_sized_n2 & Htransl );
        try discriminate;
        destruct mc_l'; try discriminate; destruct mc_r'; try discriminate;
        inversion Htransl; subst; clear Htransl.
      unfold transl_expr_sized in IHHwt_expr1, IHHwt_expr2.
      destruct (Semantics.eval l env) as [ v' | ]; try discriminate;
        destruct v'; try discriminate;
        destruct (Semantics.eval r env) as [ v' | ]; try discriminate;
        destruct v'; try discriminate;
        inversion Heval; subst; clear Heval.
      specialize (IHHwt_expr1 l' _ _ ltac:(now rewrite Htransl_maybe_sized_n1) ltac:(reflexivity))
        as ( tv_n1 & Heval_tv_n1 & Hinj_tv_n1 ).
      specialize (IHHwt_expr2 r' _ _ ltac:(now rewrite Htransl_maybe_sized_n2) ltac:(reflexivity))
        as ( tv_n2 & Heval_tv_n2 & Hinj_tv_n2 ).
      exists (Values.Val.add tv_n1 tv_n2).
      split; [ econstructor; [ apply Heval_tv_n1 | apply Heval_tv_n2 | auto ] | ].
      inversion Hinj_tv_n1 as [ | ?n ?i HBounded_n1 Heq_n1 | | | ]; subst;
        inversion Hinj_tv_n2 as [ | ?n ?i HBounded_n2 Heq_n2 | | | ]; subst.
      constructor.
      now eauto with ints.
      symmetry; now eauto with ints.
    - unfold transl_expr_sized in Htransl_sized.
      apply bind_inversion in Htransl_sized;
        destruct Htransl_sized as ( [ ( e'' & mc' ) | ] & Htransl_maybe_sized & Htransl ); [ | discriminate ];
        inversion Htransl; subst; clear Htransl;
        cbn in Htransl_maybe_sized.
      apply bind_inversion in Htransl_maybe_sized;
        destruct Htransl_maybe_sized as ( [ ( l' & mc_l' ) | ] & Htransl_maybe_sized_l & Htransl_maybe_sized' );
        apply bind_inversion in Htransl_maybe_sized';
        destruct Htransl_maybe_sized' as ( [ ( r' & mc_r' ) | ] & Htransl_maybe_sized_r & Htransl_maybe_sized' );
        try discriminate;
        destruct mc_l'; try discriminate; destruct mc_r'; try discriminate.
      inversion Htransl_maybe_sized'; subst; clear Htransl_maybe_sized'.
      unfold transl_expr_sized in IHHwt_expr1, IHHwt_expr2.
      destruct (Semantics.eval l env) as [ v' | ]; try discriminate;
        destruct v'; try discriminate;
        destruct (Semantics.eval r env) as [ v' | ]; try discriminate;
        destruct v'; try discriminate;
        inversion Heval; subst; clear Heval.
      specialize (IHHwt_expr1 l' _ _ ltac:(now rewrite Htransl_maybe_sized_l) ltac:(reflexivity)) as ( tv_l & Heval_tv_l & Hinj_tv_l ).
      specialize (IHHwt_expr2 r' _ _ ltac:(now rewrite Htransl_maybe_sized_r) ltac:(reflexivity)) as ( tv_r & Heval_tv_r & Hinj_tv_r ).
      exists (Values.Val.cmpu (fun _ _ => false) Ceq tv_l tv_r).
      split; [ econstructor; [ eauto | eauto | eauto ] | ].
      inversion Hinj_tv_l; subst.
      inversion Hinj_tv_r; subst.
      now eapply CCInj.Facts.value_compcert_nat_eq.
  Qed.

  Lemma transl_expr_maybe_sized_sized {cenv e t te mc}
    (Htransl: transl_expr_maybe_sized cenv e t = OK (Some (te, mc))):
    transl_expr_sized cenv e t = OK (te, mc).
  Proof.
    unfold transl_expr_sized.
    now rewrite Htransl.
  Qed.

  Lemma transl_expr_sized_maybe_sized {cenv e t te mc}
    (Htransl: transl_expr_sized cenv e t = OK (te, mc)):
    transl_expr_maybe_sized cenv e t = OK (Some (te, mc)).
  Proof.
    unfold transl_expr_sized in Htransl.
    apply bind_inversion in Htransl as ( e' & H & Heq ).
    destruct e'; inversion Heq; now subst.
  Qed.

  Lemma transl_expr_unsized {cenv ctx e t}
    (Hwt_expr: Expr.wt_expr ctx e t)
    (Htransl: transl_expr_maybe_sized cenv e t = OK None):
    (t = Types.t_unit /\ (e = Expr.e_tt \/ exists var_id, e = Expr.e_var var_id)).
  Proof.
    induction Hwt_expr; cbn in Htransl; try discriminate.
    - cbn in Htransl.
      destruct (SetoidList.findA (Pos.eqb var_id) (temps cenv)) eqn:EfindA; [ | discriminate ].
      destruct (Types.type_eqb_spec t0 t); [ subst | discriminate ].
      destruct t; cbn in Htransl; try discriminate; try (now inversion Hground).
      split; [ reflexivity | right; now eexists ].
    - split; [ reflexivity | now left ].
    - cbn in Htransl.
      apply bind_inversion in Htransl as ( [ [ e' mc ] | ] & Htransl & Heq );
        try discriminate;
        destruct mc; try discriminate.
    - apply bind_inversion in Htransl as ( [ [ l' mc_l ] | ] & Htransl_l & Heq );
        try discriminate;
        apply bind_inversion in Heq as ( [ [ r' mc_r ] | ] & Htransl_r & Heq );
        try discriminate;
        destruct mc_l; try discriminate;
        destruct mc_r; try discriminate.
    - apply bind_inversion in Htransl as ( [ [ l' mc_l ] | ] & Htransl_l & Heq );
        try discriminate;
        apply bind_inversion in Heq as ( [ [ r' mc_r ] | ] & Htransl_r & Heq );
        try discriminate;
        destruct mc_l; try discriminate;
        destruct mc_r; try discriminate.
  Qed.

  Lemma transl_args_correct
    {St te args ctx cenv t_args f e inj v_args}
    (WT_args: List.Forall2 (Expr.wt_expr ctx) (map fst args) (map snd args))
    (WT_env: Semantics.wt_env f ctx e)
    (MCENV: match_cenv cenv ctx)
    (MTEMPS: @match_temps St inj e te)
    (TE_args: mmap (uncurry (transl_expr_maybe_sized cenv)) args = OK t_args)
    (E_args:  ListExt.map_opt (fun expr : Expr.expr => Semantics.eval expr e) (map fst args) = Some v_args)
    : exists tv_args, (forall tge sp m, Cminor.eval_exprlist tge sp te m (map fst (ListExt.filter_map Datatypes.id t_args)) tv_args) /\ match_args inj v_args tv_args.
  Proof.
    revert t_args v_args WT_args TE_args E_args.
    induction args as [ | [ expr t ] args ]; intros.
    - cbn in TE_args; inversion TE_args; subst;
        cbn in E_args; inversion E_args; subst;
        now repeat econstructor.
    - cbn in WT_args, TE_args, E_args.
      inversion WT_args as [ | ?x ?y ?l ?l' ?WT_hd ?WT_tl ]; subst.
      apply bind_inversion in TE_args as ( hd' & TE_args_hd & TE_args ).
      apply bind_inversion in TE_args as ( tl' & TE_args_tl & TE_args ).
      inversion TE_args; subst; clear TE_args.
      destruct (ListExt.map_opt _ _) as [ v_args_tl | ] eqn:Eq_eval_tl; [ | now destruct (Semantics.eval expr e) ].
      specialize (IHargs tl' v_args_tl ltac:(inversion WT_args; subst; eauto) ltac:(assumption) eq_refl) as ( v_args'_tl & Heval_exprlist & Hv_cc ).
      destruct hd' as [ [ e' mc ] | ].
      + specialize (transl_expr_maybe_sized_mem_chunk_correct MCENV ltac:(inversion WT_args; subst; eauto)) as ( r & Heq1 & [ ( _ & contra ) | ( e'' & mc' & Hmc & Heq2 )  ] ); [ congruence | ].
        subst r;
          assert (mc' = mc) by congruence; subst;
          assert (e'' = e') by congruence; subst;
          clear Heq1.
        destruct (Semantics.eval expr e) as [ v_args_hd | ] eqn:Eq_eval_hd; [ | discriminate ].
        inversion E_args; subst; clear E_args.
        specialize (transl_expr_sized_progress ltac:(inversion WT_args; subst; eauto) ltac:(unfold transl_expr_sized; now rewrite TE_args_hd) WT_env MCENV MTEMPS Eq_eval_hd) as ( v_args'_hd & Heval'_hd & Hinj_hd ).
        exists ( v_args'_hd :: v_args'_tl ).
        split.
        intros; specialize (Heval'_hd tge sp m); specialize (Heval_exprlist tge sp m).
        now constructor.
        cbn.
        destruct (sized_or_unit_dec v_args_hd) as [ ( Hsized & Hneq ) | Heq ]; subst.
        * constructor; auto.
        * inversion Hinj_hd; subst.
      + destruct (Semantics.eval expr e) as [ v_args_hd | ] eqn:E_eval_hd; [ | discriminate ].
        inversion E_args; subst; clear E_args.
        cbn.
        eapply transl_expr_unsized in TE_args_hd as ( Heq_t & Heq_e ); eauto; subst.
        rewrite (Lemmas.eval_t_unit WT_hd WT_env) in E_eval_hd;
          inversion E_eval_hd; subst; clear E_eval_hd.
        destruct (sized_or_unit_dec Value.v_tt) as [ ( _ & contra ) | _ ]; [ contradiction | subst ].
        exists v_args'_tl.
        split; [ intros; now eauto | now constructor ].
  Qed.

End EXPRESSIONS_HELPER.

(* Semantics.pop_stack sp (fn_stackspace (fn_extra f)) s m inj = Some (s', m', inj') *)

Local Ltac simpl_pop_stack :=
  match goal with
  | Hpop_stack : Semantics.pop_stack ?sp ?stackspace ?s ?m ?inj = Some (?s', ?m', ?inj') |- _ =>
      unfold Semantics.pop_stack in Hpop_stack;
      destruct (Memory.Mem.free m sp _ _) as [ m_free | ] eqn:Efree; [ | discriminate ];
      destruct (NatExt.iter_opt _ _ _) as [ st' | ] eqn:Eiter_opt; [ | discriminate ];
      inversion Hpop_stack; subst; clear Hpop_stack
  end.
(* match goal with *)
(* | Hpop_stack : @Semantics.pop_stack _ _ ?sp _ ?s ?m ?inj = Some (?s', ?m', ?inj') |- _ => *)
(*     unfold Semantics.pop_stack in Hpop_stack; *)
(*     destruct (Memory.Mem.free m sp _ _) as [ m_free | ] eqn:Efree; [ | discriminate ]; *)
(*     destruct (ListExt.fold_left_opt _ _ _) as [ st' | ] eqn:fold_left_pop; [ | discriminate ]; *)
(*     inversion Hpop_stack; subst; clear Hpop_stack *)
(* end. *)

Section TRANSLATION_HELPER.

  Lemma stackspace_preserved {St Hp p f c k e locals sp s m inj tf tc tk te}
    (Hmatch: @match_states St Hp p
               (Semantics.State f c k e locals sp s m inj)
               (Cminor.State tf tc tk (Values.Vptr sp Ptrofs.zero) te m)):
    tf.(Cminor.fn_stackspace) = CCInj.offset_to_offset f.(fn_extra).(fn_stackspace).
  Proof.
    inversion Hmatch; subst.
    unfold transl_funbody in TFB.
    apply bind_inversion in TFB as (stmt & _ & H).
    inversion H; now subst.
  Qed.

  Lemma pop_stack_value_cc
    {St Hp sp} {f: function} {s m inj s' m' inj'}
    (WF_inj: CCInj.wf s m inj)
    (Hpop_stack: @Semantics.pop_stack St Hp sp f.(fn_extra).(fn_stackspace) s m inj = Some (s', m', inj'))
    : forall v tv, CCInj.inj_value inj v tv -> CCInj.inj_value inj' v tv.
  Proof.
    simpl_pop_stack.
    intros v tv Hinj.
    inversion Hinj; subst;
      now constructor.
  Qed.

  (* Lemma push_stack_value_cc *)
  (*   {St Hp sp} {f: function} { s m inj} *)
  (*   (WF_inj: @CCInj.wf St Hp s m inj) *)
  (*   : forall (v : Value.value) (tv : Values.val), *)
  (*     CCInj.inj_value inj v tv -> *)
  (*     CCInj.inj_value *)
  (*       {| *)
  (*         CCInj.inj_hp_map := CCInj.inj_hp_map inj; *)
  (*         CCInj.inj_st_map := *)
  (*           fold_left *)
  (*             (fun (st_map : list (name * (Values.block * nat * bool))) (loc : Defs.local) => *)
  (*                (Defs.local_name loc, (sp, Defs.local_ofst loc, true)) :: st_map) *)
  (*             (Defs.fn_locals f) (CCInj.inj_st_map inj); *)
  (*         CCInj.inj_fn_map := CCInj.inj_fn_map inj *)
  (*       |} v tv. *)
  (* Proof. *)
  (*   intros v tv INJ; inversion INJ; subst; now constructor. *)
  (* Qed. *)

  Lemma symbols_preserved
    {prog: Prog.program} {tprog: Cminor.program}
    (TRANSL: match_prog prog tprog):
    forall (s: AST.ident), Globalenvs.Genv.find_symbol (Genv.globalenv tprog) s = Globalenvs.Genv.find_symbol (Genv.globalenv (Prog.program_of_program prog)) s.
  Proof.
    apply (Genv.find_symbol_match TRANSL).
  Qed.

  Lemma function_ptr_translated {prog: Prog.program} {tprog: Cminor.program}
    (TRANSL: match_prog prog tprog):
    forall {b: Values.block} {f: fundef},
      Genv.find_funct_ptr (Genv.globalenv (Prog.program_of_program prog)) b = Some f ->
      exists cu tf, Genv.find_funct_ptr (Genv.globalenv tprog) b = Some tf /\ match_fundef cu f tf /\ linkorder cu prog.
  Proof.
    apply (Genv.find_funct_ptr_match TRANSL).
  Qed.

  Lemma functions_translated {prog: Prog.program} {tprog: Cminor.program}
    (TRANSL: match_prog prog tprog):
    forall {v: Values.val} {f: fundef},
      Genv.find_funct (Genv.globalenv (Prog.program_of_program prog)) v = Some f ->
      exists cu tf, Genv.find_funct (Genv.globalenv tprog) v = Some tf /\ match_fundef cu f tf /\ linkorder cu prog.
  Proof.
    apply (Genv.find_funct_match TRANSL).
  Qed.

  Lemma wt_app_make_signature_correct
    {prog: Prog.program}
    {ctx f_id t_out args b fd tfd cu}
    (Hmatch_ctxt: match_ctxt ctx (Genv.globalenv (Prog.program_of_program prog)))
    (Hfind_symbol: Genv.find_symbol (Genv.globalenv (Prog.program_of_program prog)) f_id = Some b)
    (Hfind_funct_ptr: Genv.find_funct_ptr (Genv.globalenv (Prog.program_of_program prog)) b = Some fd)
    (MFD: match_fundef cu fd tfd)
    (LO: linkorder cu prog)
    (Hwt_app: @Typing.wt_cmd ctx (Cmd.c_app f_id t_out args) t_out)
    : Cminor.funsig tfd = make_signature (map snd args) t_out.
  Proof.
    inversion MFD as [ ?f ?tf ?Htransl | ]; subst.
    - apply bind_inversion in Htransl as ( tbody & Htransl_body & Htransl ).
      inversion Hwt_app; subst.
      inversion Hmatch_ctxt as ( Eglob_ctxt ); subst; clear Hmatch_ctxt.
      assert (fn = f) by
        (unfold Ctxt.get_global in Hfind_fn;
         unfold fundef, Common.Prog.fundef in *;
         rewrite Eglob_ctxt in Hfind_fn;
         rewrite Hfind_symbol in Hfind_fn;
         unfold Genv.find_funct_ptr in Hfind_funct_ptr;
         rewrite Hfind_fn in Hfind_funct_ptr;
         congruence); subst.
      destruct tf, f; unfold make_signature, Prog.signature_of_signature in *; cbn in *;
        inversion Htransl; subst; clear Htransl.
      congruence.
    - inversion Hwt_app; subst.
      inversion Hmatch_ctxt as ( Eglob_ctxt ); subst; clear Hmatch_ctxt.
      unfold Ctxt.get_global in Hfind_fn.
      unfold fundef, Common.Prog.fundef in *.
      rewrite Eglob_ctxt in Hfind_fn.
      rewrite Hfind_symbol in Hfind_fn.
      unfold Genv.find_funct_ptr in Hfind_funct_ptr.
      rewrite Hfind_fn in Hfind_funct_ptr.
      congruence.
  Qed.

  Lemma make_call_call_cont {St k f_id args sig} (Hcall_cont: Semantics.is_call_cont k):
    make_call (@Semantics.cont_target St k) f_id args sig = Cminor.Stailcall sig (global_ptr f_id) args.
  Proof.
    now inversion Hcall_cont.
  Qed.

  Lemma match_args_impl {St inj1 inj2} (inj_impl: forall v tv, @CCInj.inj_value St inj1 v tv -> CCInj.inj_value inj2 v tv): forall args targs (MARGS: match_args inj1 args targs), @match_args St inj2 args targs.
  Proof.
    intros; induction MARGS;
      constructor; auto.
  Qed.

  Lemma match_cont_call_cont
    {St k tk prog inj cenv}
    (Hcall_cont: Semantics.is_call_cont k)
    (MK: match_cont prog inj cenv k tk)
    : @match_cont St prog inj cenv k (Cminor.call_cont tk).
  Proof.
    inversion Hcall_cont; subst;
      inversion MK; subst;
      now repeat constructor.
  Qed.

  (* Lemma margs_has_argtype_list *)
  (*   {St Hp prog s m inj f args targs tbody k} *)
  (*   (WT: @Semantics.wt_state St Hp prog (Semantics.Callstate (AST.Internal f) args k s m inj)) *)
  (*   (MARGS: match_args inj args targs) *)
  (*   :   Values.Val.has_argtype_list targs *)
  (*         (AST.sig_args *)
  (*            (Cminor.fn_sig *)
  (*               {| *)
  (*                 Cminor.fn_sig := Prog.signature_of_signature (Prog.fn_signature f); *)
  (*                 Cminor.fn_params := params_of_function f; *)
  (*                 Cminor.fn_vars := vars_of_function f; *)
  (*                 Cminor.fn_stackspace := Z.of_nat (Defs.fn_stackspace St (@Cmd.cmd St) f); *)
  (*                 Cminor.fn_body := tbody *)
  (*               |})). *)
  (* Proof. *)
  (*   inversion WT; subst; cbn; clear WT. *)
  (*   inversion Hwt_args as [ ?args ?f WT | | ]; subst. *)
  (*   clear tbody k Hwt_cont ctx Hwt_fundef sig Hsig Hwf_inj Hwt_args. *)
  (*   destruct f; cbn; cbn in WT. *)
  (*   clear fn_return fn_temps fn_locals fn_body fn_stackspace. *)
  (*   revert fn_params WT. *)
  (*   induction MARGS; intros. *)
  (*   - inversion WT; subst; clear WT; constructor. *)
  (*   - inversion WT as [ | ?x ?y ?l ?l' WT_hd WT_tl ]; subst. *)
  (*     destruct fn_params as [ | [ fn_params_hd_id fn_params_hd_ty ] fn_params_tl ] > [ discriminate | cbn in H1; inversion H1; subst; clear H1 ]. *)
  (*     inversion WT_hd; subst. *)
  (*     apply IHMARGS. *)
  (*     now inversion WT; subst. *)
  (*   - inversion WT as [ | ?x ?y ?l ?l' WT_hd WT_tl ]; subst. *)
  (*     destruct fn_params as [ | [ fn_params_hd_id fn_params_hd_ty ] fn_params_tl ] > [ discriminate | cbn in H1; inversion H1; subst; clear H1 ]. *)
  (*     cbn. *)
  (*     destruct (Lemmas.xtype_of_type_sized fn_params_hd_ty) as ( fn_params_hd_xt & Hrewrite ); eauto with deep_gallinac. *)
  (*     rewrite Hrewrite. *)
  (*     constructor. *)
  (*     eapply Lemmas.inj_has_argtype; now eauto. *)
  (*     apply IHMARGS; now eauto. *)
  (* Qed. *)

  (* Lemma Cm_set_locals_set_params_get {St par_id par_ty f} *)
  (*   (Disjoint: List.Forall (fun idt => ~exists idt', (In idt' f.(Genv.fn_temps) /\ fst idt' = fst idt)) f.(Genv.fn_params)) *)
  (*   (HIn_params: In (par_id, par_ty)) *)
  (*   : (Cminor.set_locals (map fst f.(Genv.fn_temps)) *)
  (*        (Cminor.set_params tv_args *)
  (*           (map fst (f.(Genv.fn_params))))) ! par_id = Some  *)
  (*       (Cminor.set_locals (map fst fn_temps) *)
  (*    (Cminor.set_params (tv_arg :: tv_args) *)
  (*       (fn_param_hd_id *)
  (*        :: ListExt.filter_map *)
  (*             (fun idt : AST.ident * Types.type => *)
  (*              let (id, y) := idt in match y with *)
  (*                                    | Types.t_unit => None *)
  (*                                    | _ => Some id *)
  (*                                    end) fn_params_tl))) ! fn_param_hd_id =  *)
  (* Some tv_arg *)

  Lemma set_params_nth {A: Type} {params vals ident val} (Hlookup: (@Semantics.set_params A params vals) ! ident = Some val): exists n ty, nth_error params n = Some (ident, ty) /\ nth_error vals n = Some val.
  Proof.
    revert ident vals val Hlookup.
    induction params as [ | [ params_hd_id params_hd_ty ] params_tl ];
      cbn; intros;
      destruct vals; (try (rewrite PTree.gempty in Hlookup; discriminate)).
    rewrite PTree.gsspec in Hlookup.
    destruct (peq ident params_hd_id) as [ | Hneq ]; subst.
    * inversion Hlookup; subst; clear Hlookup.
      exists 0%nat, params_hd_ty.
      split; reflexivity.
    * destruct (IHparams_tl ident vals val Hlookup) as ( n & ty & Hnth1 & Hnth2 ) .
      exists (S n), ty.
      split; auto.
  Qed.

  Lemma set_optid_match_temps {St inj target_id v env optid tv te t}
    (MT: match_temps inj env te)
    (OI : match t with
          | Types.t_unit => optid = None
          | _ => optid = Some target_id
          end)
    (INJ: CCInj.inj_value inj v tv \/ v = Value.v_tt)
    (WT: Value.wt_value v t)
    : @match_temps St inj (PTree.set target_id v env) (Cminor.set_optvar optid tv te).
  Proof.
    intros any_id any_v Hget.
    specialize (MT any_id any_v).
    rewrite PTree.gsspec in Hget.
    destruct (peq any_id target_id) as [ Heq | Hneq ]; subst.
    - inversion Hget; subst; clear Hget.
      destruct INJ as [ INJ | H ]; [ | now left ].
      right.
      exists tv.
      destruct t;
        try (now inversion INJ; subst; inversion WT);
        subst; cbn;
        rewrite PTree.gss; auto.
    - specialize (MT Hget) as [ H | (tv' & Htget & HInj) ].
      now left.
      right.
      exists tv'.
      destruct t;
        try (now inversion HInj; subst; inversion WT);
        subst; cbn;
        rewrite PTree.gso; auto.
  Qed.

  Lemma set_params_match_temps {St} {ctx} {f: function} {inj args targs}
    (WT: wt_function ctx f)
    (WTcall: wt_fundef_call args (AST.Internal f))
    (MARGS: match_args inj args targs)
    : @match_temps St inj
        (Semantics.set_params (fn_params f) args)
        (Cminor.set_locals (vars_of_function f) (Cminor.set_params targs (params_of_function f))).
  Proof.
    remember (AST.Internal f) as fd eqn:Efd.
    destruct WTcall as [ ?args ?f WTargs | | ];
      try discriminate; inversion Efd; subst; clear Efd.

    destruct WT as [ _ _ _ _ _ SBinds_params SBinds_temps Disjoint ].
    destruct f as [ fn_return fn_params fn_temps fn_body [ fn_stackspace ] ]; cbn; cbn in SBinds_params, SBinds_temps, Disjoint, WTargs.
    clear fn_return fn_body fn_stackspace.
    intros ident v Hlookup.
    revert args targs MARGS WTargs Hlookup Disjoint.
    induction fn_params as [ | [ fn_param_hd_id fn_param_hd_ty ] fn_params_tl ];
      cbn; intros.
    - destruct args as [ | [ ] ]; now rewrite PTree.gempty in Hlookup.
    - inversion MARGS.
      + subst; cbn in Hlookup; now rewrite PTree.gempty in Hlookup.
      + inversion WTargs as [ | args_hd ?y args_tl ?l' WT_hd WT_tl ];
          subst; inversion H1; subst; clear H1.
        inversion Disjoint as [ | [ ] ?l Disjoint_hd Disjoint_tl ]; subst.
        rewrite PTree.gsspec in Hlookup.
        destruct (peq ident fn_param_hd_id) as [ | Hneq ]; [ inversion Hlookup; subst; now left | subst ].
        specialize (IHfn_params_tl ltac:(now inversion SBinds_params) v_args targs MARGS0 WT_tl Hlookup Disjoint_tl) as [ Heq | (tv & Hlookup' & Hinj ) ]; [ now left | ].
        right.
        exists tv.
        split; [ | now auto ].
        now inversion WT_hd; subst.
      + inversion WTargs as [ | args_hd ?y args_tl ?l' WT_hd WT_tl ];
          subst; inversion H1; subst; clear H1.
        inversion Disjoint as [ | [ ] ?l Disjoint_hd Disjoint_tl ]; subst.
        rewrite PTree.gsspec in Hlookup.
        specialize (Lemmas.value_compcert_sized Hinj) as Hsized.
        destruct (peq ident fn_param_hd_id) as [ | Hneq ]; subst.
        * inversion Hlookup; subst; clear Hlookup.
          right; exists tv_arg.
          split; [ | now auto ].
          assert (Hrewrite: match fn_param_hd_ty with
                            | Types.t_unit => None
                            | _ => Some fn_param_hd_id
                            end = Some fn_param_hd_id) by (inversion WT_hd; subst; now inversion Hsized);
            rewrite Hrewrite; clear Hrewrite.
          rewrite Cminorgenproof.set_locals_outside.
          cbn.
          rewrite PTree.gsspec.
          now destruct (peq fn_param_hd_id fn_param_hd_id).
          intros contra.
          apply Disjoint_hd.
          inversion SBinds_temps as [ | fn_temps_hd_id fn_temps_hd_ty fn_temps_tl _ SBinds_temps_tl ]; [ subst; contradiction | subst ].
          specialize (ListExt.SBinds_map_fst_SIns SBinds_temps) as SIns_temps.
          specialize (ListExt.SIns_In SIns_temps contra) as contra'.
          specialize (ListExt.SIn_map_fst_SBindIn SBinds_temps contra') as (b & HSBindIn_temps).
          exists (fn_param_hd_id, b).
          split; auto. apply ListExt.BindIn_In. apply ListExt.SBindIn_BindIn. auto.
        * inversion SBinds_params as [ | ?a ?b ?l _ SBinds_params_tl ]; subst.
          inversion WTargs as [ | ?x ?y ?l ?l' WTargs_hd WTargs_tl ]; subst.
          specialize (set_params_nth Hlookup) as (n & ty & HIn_params & _).
          apply nth_error_In in HIn_params.
          apply ListExt.SBinds_In in HIn_params; auto.
          specialize (IHfn_params_tl SBinds_params_tl v_args tv_args MARGS0 WTargs_tl Hlookup Disjoint_tl) as [ Heq | ( tv & Hset & INJ ) ]; [ now left | right ].
          assert (Abs_ident: ~ In ident (map fst fn_temps)).
          {
            intros contra.
            specialize (ListExt.SBinds_map_fst_SIns SBinds_temps) as SIns_temps.
            specialize (ListExt.SIns_In SIns_temps contra) as SIn_ident.
            specialize (ListExt.SIn_map_fst_SBindIn SBinds_temps SIn_ident) as (t & SBindIn).
            eapply (ListExt.Forall_forall_l Disjoint_tl).
            eapply ListExt.BindIn_In, ListExt.SBindIn_BindIn; eauto.
            exists (ident, t).
            split; [ now eapply ListExt.BindIn_In, ListExt.SBindIn_BindIn | auto ].
          }
          exists tv; split; [ | assumption ].
          assert (Hrewrite: match fn_param_hd_ty with
                            | Types.t_unit => None
                            | _ => Some fn_param_hd_id
                            end = Some fn_param_hd_id) by (inversion WT_hd; subst; now inversion Hsized);
            rewrite Hrewrite; clear Hrewrite.
          rewrite Cminorgenproof.set_locals_outside; cbn; auto.
          rewrite PTree.gsspec.
          destruct (peq ident fn_param_hd_id); [ congruence | ].
          rewrite Cminorgenproof.set_locals_outside in Hset; auto.
  Qed.

  (* Lemma match_temps_push_stack {St} {inj e te sp locs} *)
  (*   (MTEMPS: @match_temps St inj e te) *)
  (*   : @match_temps St {| *)
  (*         CCInj.inj_hp_map := CCInj.inj_hp_map inj; *)
  (*         CCInj.inj_st_map := *)
  (*           fold_left *)
  (*             (fun (st_map : list (name * (Values.block * nat * bool))) (loc : Defs.local) => *)
  (*                (Defs.local_name loc, (sp, Defs.local_ofst loc, true)) :: st_map) *)
  (*             locs (CCInj.inj_st_map inj); *)
  (*         CCInj.inj_fn_map := CCInj.inj_fn_map inj *)
  (*       |} e te. *)
  (* Proof. *)
  (*   intros any_id any_v Hget. *)
  (*   specialize (MTEMPS any_id any_v Hget). *)
  (*   destruct MTEMPS as [ Heq | (v' & Hget' & INJ) ] > [ subst; now left | right ]. *)
  (*   exists v'; split > [ assumption | ]. *)
  (*   destruct INJ; now constructor. *)
  (* Qed. *)

  Lemma match_temps_pop_stack {St Hp} {inj e te sp n s m s' m' inj'}
    (MTEMPS: @match_temps St inj e te)
    (Hpop_stack: @Semantics.pop_stack St Hp sp n s m inj = Some (s', m', inj'))
    : @match_temps St inj' e te.
  Proof.
    simpl_pop_stack.
    intros any_id any_v Hget.
    specialize (MTEMPS any_id any_v Hget).
    destruct MTEMPS as [ Heq | (v' & Hget' & Hinj) ]; [ subst; now left | right ].
    exists v'; split; eauto.
    inversion Hinj; subst; constructor; eauto.
  Qed.

  (* Lemma match_cont_push_stack {St} {prog} {inj cenv k tk sp locs} *)
  (*   (MK: @match_cont St prog inj cenv k tk) *)
  (*   : @match_cont St prog {| *)
  (*                    CCInj.inj_hp_map := CCInj.inj_hp_map inj; *)
  (*                    CCInj.inj_st_map := *)
  (*                      fold_left *)
  (*                        (fun (st_map : list (name * (Values.block * nat * bool))) (loc : Defs.local) => *)
  (*                           (Defs.local_name loc, (sp, Defs.local_ofst loc, true)) :: st_map) *)
  (*                        locs (CCInj.inj_st_map inj); *)
  (*                    CCInj.inj_fn_map := CCInj.inj_fn_map inj *)
  (*                  |} cenv k tk. *)
  (* Proof. *)
  (*   induction MK; econstructor; eauto. *)
  (*   eapply match_temps_push_stack; eauto. *)
  (* Qed. *)

  Lemma match_cont_pop_stack {St Hp} {prog} {inj cenv k tk sp n s m s' m' inj'}
    (MK: @match_cont St prog inj cenv k tk)
    (Hpop_stack: @Semantics.pop_stack St Hp sp n s m inj = Some (s', m', inj'))
    : @match_cont St prog inj' cenv k tk.
  Proof.
    revert Hp sp s s' inj' n m m' Hpop_stack.
    induction MK; intros.
    - specialize (IHMK Hp sp s s' inj' n m m' Hpop_stack).
      econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
      eapply match_temps_pop_stack; eauto.
    - econstructor.
  Qed.

  Lemma SIns_list_norepet {A: Type} {l: list A} (HSIns: ListExt.SIns l): list_norepet l.
  Proof.
    induction HSIns as [ | a l HAbsIn HSIns ].
    constructor.
    constructor; eauto using ListExt.AbsIn_In_contra.
  Qed.

  Lemma SBinds_list_norepet {A B: Type} {l: list (A*B)} (HSBinds: ListExt.SBinds l): list_norepet l.
  Proof.
    induction HSBinds as [ | a b l HAbsBind HSBinds ].
    constructor.
    constructor; eauto using ListExt.AbsBind_In_False.
  Qed.

  Lemma transl_prim_correct {St Hp prog tprog f c k e locals sp s m inj t S2 v s' m' inj'}
    (TRANSL: match_prog prog tprog)
    (Hprim: Semantics.builtin c
              (Globalenvs.Genv.globalenv (Prog.program_of_program prog)) e locals sp
              s m inj
              v
              s' m' inj')
    (Hstep: Semantics.step (Globalenvs.Genv.globalenv (Prog.program_of_program prog))
              (Semantics.State f c k e locals sp s m inj)
              t
              S2)
    T1
    (Hmatch_states: match_states prog (Semantics.State f c k e locals sp s m inj) T1):
    exists (SN : Semantics.state) (T2 : Cminor.state),
      Smallstep.star Semantics.step (Globalenvs.Genv.globalenv (Prog.program_of_program prog)) S2 Events.E0 SN /\
        Smallstep.plus Cminor.step (Globalenvs.Genv.globalenv tprog) T1 Events.E0 T2 /\ @match_states St Hp prog SN T2.
  Proof.
  Admitted.

End TRANSLATION_HELPER.

Section TRANSLATION.

  Context {St: Store}.
  Context {Hp: Heap}.
  Variable prog: Prog.program.
  Variable tprog: Cminor.program.
  Hypothesis TRANSL: match_prog prog tprog.

  Lemma senv_preserved:
    Globalenvs.Senv.equiv (Genv.globalenv (Prog.program_of_program prog)) (Genv.globalenv tprog).
  Proof using TRANSL.
    apply (Genv.senv_match TRANSL).
  Qed.

  Lemma sig_preserved_transl_body:
    forall f tf id_malloc id_free,
      Cminorgen.transl_funbody id_malloc id_free f = OK tf ->
      Cminor.fn_sig tf = (Prog.signature_of_signature (Prog.fn_signature f)).
  Proof using TRANSL.
    intros f tf id_malloc id_free Htransl.
    unfold Cminorgen.transl_funbody in Htransl.
    apply bind_inversion in Htransl as ( stmt & Htransl & Heq );
      inversion Heq; subst; clear Heq.
    reflexivity.
  Qed.

  Lemma sig_preserved_transl:
    forall f i tf sig,
      Prog.funsig f sig ->
      Cminorgen.transl_fundef prog.(prog_extra).(Prog.prog_malloc) prog.(prog_extra).(Prog.prog_free) i f = OK tf ->
      Cminor.funsig tf = (Prog.signature_of_signature sig).
  Proof using TRANSL.
    intros f i tf sig Hfunsig; destruct f; cbn. (* > [ | inversion Hfunsig; subst; intros H; inversion H; subst; reflexivity ]; cbn. *)
    - unfold Cminorgen.transl_function.
      inversion Hfunsig; subst.
      intros Htransl.
      apply bind_inversion in Htransl as (f' & Htransl & Heq );
        inversion Heq; subst; clear Heq.
      eapply sig_preserved_transl_body; eauto.
    - intros Heq; inversion Heq; subst; clear Heq.
      now inversion Hfunsig; subst.
  Qed.

  Lemma sig_preserved_match:
    forall p f tf sig, Prog.funsig f sig -> match_fundef p f tf -> Cminor.funsig tf = Prog.signature_of_signature sig.
  Proof using TRANSL.
    intros p f tf sig Hsig Hmatch.
    inversion Hmatch; subst; inversion Hsig; subst; try reflexivity.
    unfold transl_function in H.
    eapply sig_preserved_transl_body; eauto.
  Qed.

  Lemma transl_initial_states:
    forall S, Semantics.initial_state prog S ->
              exists R, Cminor.initial_state tprog R /\ @match_states St Hp prog S R.
  Proof using TRANSL.
    intros S Hinit.
    destruct Hinit as [ ?ge ?b ?f ?s0 ?m0 ?inj_0 Hwt_prog Hge Hinit_state Hwf_inject Hfind_symbol Hfind_funct_ptr Hfunsig ]; subst.
    destruct (function_ptr_translated TRANSL Hfind_funct_ptr) as ( cu & tf & Hfind_funct_ptr' & Hmatch_fundef & Hlo ).
    exists (Cminor.Callstate tf [] Cminor.Kstop m0).
    split.
    - eapply Cminor.initial_state_intro with (b := b).
      + apply (Genv.init_mem_match TRANSL); eauto.
        eapply Lemmas.init_state_correct_mem; eauto.
      + rewrite (match_program_main TRANSL ).
        now rewrite (symbols_preserved TRANSL).
      + exact Hfind_funct_ptr'.
      + rewrite Lemmas.signature_main.
        eapply sig_preserved_match; eauto.
    - inversion Hwt_prog; subst.
      eapply match_callstate with
        (cenv := mkcompilenv match f with AST.Internal f => f.(fn_temps) | _ => [] end prog.(prog_extra).(Prog.prog_malloc) prog.(prog_extra).(Prog.prog_free))
        (i := 1%positive).
      + eapply Semantics.wt_Callstate with (sig := Prog.mk_signature [] t_nat) (ctx := Ctxt.with_pure (Maps.PTree.empty _) (Prog.mk_glob_ctxt prog)); auto.
        * destruct wt_prog_main as (gdef_main & HIn_main).
          specialize (proj1 (Forall_forall _ _) wt_prog_defs _ HIn_main) as Hwt_main.
          cbn in Hwt_main.
          apply Genv.find_funct_ptr_inversion in Hfind_funct_ptr as (ident & HIn).
          specialize (proj1 (Forall_forall _ (Prog.prog_defs prog)) wt_prog_defs (ident, AST.Gfun f) HIn) as Hwt_fmain.
          cbn in Hwt_fmain.
          inversion Hwt_fmain; subst.
          apply H2.
        * inversion Hfunsig; subst.
          destruct f0; cbn in *; subst.
          destruct fn_params; [ | discriminate ]; clear H1.
          constructor.
          constructor.
        * constructor; constructor.
      + (inversion Hmatch_fundef; subst); [ | reflexivity ].
        inversion Hlo; subst.
        destruct H1; subst.
        unfold id_malloc, id_free.
        unfold transl_fundef.
        cbn.
        rewrite H1, H2 in H.
        rewrite H.
        reflexivity.
      + constructor.
      + now repeat constructor.
  Qed.

  Lemma transl_final_states: forall s1 s2 r,
      match_states prog s1 s2 -> Smallstep.final_state (@Semantics.semantics St Hp prog) s1 r ->
      Smallstep.final_state (Cminor.semantics tprog) s2 r.
  Proof using TRANSL.
    cbn.
    intros s1 s2 r Hmatch_states Hfinal.
    destruct Hfinal as [r m s inj ].
    inversion Hmatch_states as [ | | ?r ?k ?m ?s ?inj ?tr ?tk ?cenv WT [ Heq | Hvalue_compcert ] Hmatch_cont ]; [ discriminate | subst ].
    inversion Hvalue_compcert; subst.
    inversion Hmatch_cont; subst.
    rewrite <- Heq, Int.repr_unsigned.
    econstructor.
  Qed.

  Theorem transl_step_correct:
    forall (S1 : Semantics.state) (t : Events.trace) (S2 : Semantics.state),
      Semantics.step (Genv.globalenv (Prog.program_of_program prog)) S1 t S2 ->
      forall T1 : Cminor.state,
        match_states prog S1 T1 ->
        exists (SN : Semantics.state) (T2 : Cminor.state),
          Smallstep.star Semantics.step (Genv.globalenv (Prog.program_of_program prog)) S2 Events.E0 SN /\
            Smallstep.plus Cminor.step (Genv.globalenv tprog) T1 t T2 /\ @match_states St Hp prog SN T2.
  Proof.
    intros S1 t S2 Hstep;
      inversion Hstep; subst.

    - intros T1 Hmatch_states.
      inversion Hmatch_states; subst;
        inversion WT; subst;
        inversion State_wt_cmd; subst.
      cbn in TC.
      apply bind_inversion in TC as ( c_b' & TC_b & TC ).
      apply bind_inversion in TC as ( c_c' & TC_c & TC ).
      inversion TC; subst; clear TC.
      specialize (Lemmas.preservation_State_State WT Hstep ctx t_b ltac:(econstructor) Hwt_cmd_bind) as WT'.
      eexists ?[SN], ?[T2].
      split; [ eapply Smallstep.star_refl | split ].
      eapply Smallstep.plus_one; apply Cminor.step_seq.
      eapply match_state with (id_malloc := id_malloc) (id_free := id_free) (ctx := ctx); auto.
      + eapply Lemmas.preservation_State_State; [ apply WT | apply Hstep | constructor | apply Hwt_cmd_bind ].
      + eapply match_cont_Kbind_Kseq; eauto.
    - eapply transl_prim_correct; now eauto.
    - eapply transl_prim_correct; now eauto.
    - intros T1 Hmatch_states.
      inversion Hmatch_states; subst.
      inversion WT; subst.
      inversion MCTXT as ( Eglob_ctxt ).
      apply bind_inversion in TC as (targs & TE_args & TC).
      inversion TC; subst; clear TC.
      specialize (transl_args_correct ltac:(inversion State_wt_cmd; eauto) State_wt_env MCENV MTEMPS TE_args Heval_args) as ( tv_args & Heval_args' & Hinj_args ).
      specialize (Heval_args' (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      specialize (function_ptr_translated TRANSL Hfind_funct_ptr) as ( cu & tfd & Hfind_funct & Hmatch_fundef & Hlinkorder ).
      rewrite <- Genv.find_funct_find_funct_ptr in Hfind_funct.
      assert (t = t_out) by (now inversion State_wt_cmd); subst t.
      assert (Heq: exists fn_callee, fd = AST.Internal fn_callee) by admit;
        (* (inversion State_wt_cmd; subst; *)
        (*  unfold Ctxt.get_global in Hfind_fn; *)
        (*  rewrite Eglob_ctxt in Hfind_fn; *)
        (*  unfold fundef,fundef in *; *)
        (*  rewrite Hfind_symbol in Hfind_fn; *)
        (*  unfold Genv.find_funct_ptr in Hfind_funct_ptr; *)
        (*  rewrite Hfind_fn in Hfind_funct_ptr; *)
        (*  exists fn0; congruence) ; *)
        destruct Heq as ( fn_callee & Heq ); subst fd.
      assert (H: exists target, Semantics.seq_cont_target k target)
        by (inversion Hseq_cont; eexists; constructor);
        destruct H as (target_id & Hseq_cont_target).
      assert (t_out = fn_return fn_callee).
      {
        inversion State_wt_cmd; subst.
        unfold Ctxt.get_global in Hfind_fn.
        unfold Genv.find_funct_ptr in Hfind_funct_ptr.
        admit.
        (* rewrite Eglob_ctxt in Hfind_fn. *)
        (* unfold Defs.fundef in *. *)
        (* rewrite Hfind_symbol in Hfind_fn. *)
        (* rewrite Hfind_fn in Hfind_funct_ptr. *)
        (* now inversion Hfind_funct_ptr; subst. *)
      }
      subst.
      eexists ?[SN], ?[T2].
      split; [ eapply Smallstep.star_refl | split ].
      eapply Smallstep.plus_one.
      + unfold make_call; erewrite Semantics.Facts.seq_cont_target_cont_target; [ | now eauto ].
        eapply Cminor.step_call with ( fd := tfd ).
        * inversion State_wt_cmd; subst.
          unfold global_ptr.
          constructor; cbn.
          reflexivity.
        * apply Heval_args'.
        * unfold Genv.symbol_address.
          now rewrite (symbols_preserved TRANSL), Hfind_symbol, Genv.find_funct_find_funct_ptr.
        * eapply @wt_app_make_signature_correct with
            (prog := prog) (ctx := ctx) (f_id := id); now eauto.
      + inversion Hmatch_fundef as [ ?f ?tf ?Htransl_f | ]; subst.
        eapply match_callstate with (i := 1%positive) (cenv := (mkcompilenv fn.(fn_temps) id_malloc id_free)); [ | | now eauto | ].
        -- eapply Lemmas.preservation; [ | eapply Hstep ];
             econstructor; eauto.
        -- erewrite <- IR.Linker.linkorder_program_free, <- IR.Linker.linkorder_program_malloc;
             eauto;
             unfold transl_fundef; cbn;
             now rewrite Htransl_f.
        -- econstructor; eauto.
           cbn.
           destruct (ListExt.sfind Pos.eq_dec target_id (fn_temps fn))
             as [ t | ] eqn:Esfind;
             [
             |
               inversion Hseq_cont_target; subst;
               inversion State_wt_cont; subst;
               try (now inversion Hwt_cont_call);
               (eapply ListExt.sfind_None_In; [ eapply Esfind | admit ])(* ; *)
                 (* (eapply Semantics.wv_ty_env in State_wt_env; [ | eapply Hget_pure ]); *)
                 (* now (eapply State_wt_env) *)
             ].
           admit.
    (* inversion Hseq_cont_target; subst; *)
    (*   inversion State_wt_cont; subst; *)
    (*   try (now inversion Hwt_cont_call); *)
    (* (eapply ListExt.sbinds_sfind in Esfind; [ | now inversion State_wt_function; subst ]); *)
    (*   specialize (Semantics.wv_ty_env State_wt_env _ _ _ Hget_pure) as [ _ H ]; *)
    (*   assert (t = fn_return fn_callee) by *)
    (*   (match goal with *)
    (*   | [ h : _ = fn_return fn_callee |- _ ] => *)
    (*       rewrite h in * *)
    (*   | [ |- _ ] => () *)
    (*   end; eapply ListExt.BindIn_fun; [ eapply ListExt.SBindIn_BindIn, ListExt.SBinds_In; [ eapply Prog.wt_fn_temps_sbinds, State_wt_function | eapply H ] | now eapply ListExt.SBindIn_BindIn ]); subst; clear H; *)
    (*   destruct (fn_return fn_callee); now cbn. *)
    - intros T1 Hmatch_states.
      inversion Hmatch_states; subst.
      inversion WT; subst.
      inversion MCTXT as ( Eglob_ctxt ).
      apply bind_inversion in TC as ( targs & TE_args & TC ).
      cbn in TC;
        inversion TC; subst; clear TC.
      specialize (transl_args_correct ltac:(inversion State_wt_cmd; eauto) State_wt_env MCENV MTEMPS TE_args Heval_args) as ( tv_args & Heval_args' & Hinj_args ).
      specialize (Heval_args' (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      specialize (function_ptr_translated TRANSL Hfind_funct_ptr) as ( cu & tfd & Hfind_funct & Hmatch_fundef & Hlinkorder ).
      rewrite <- Genv.find_funct_find_funct_ptr in Hfind_funct.
      assert (t = t_out) by (now inversion State_wt_cmd); subst t.
      assert (Heq: exists f, fd = AST.Internal f) by admit
      (* (inversion State_wt_cmd; subst; *)
      (*  unfold Ctxt.get_global in Hfind_fn; *)
      (*  unfold fundef in *; *)
      (*  rewrite Eglob_ctxt in Hfind_fn; *)
      (*  rewrite Hfind_symbol in Hfind_fn; *)
      (*  unfold Genv.find_funct_ptr in Hfind_funct_ptr; *)
      (*  rewrite Hfind_fn in Hfind_funct_ptr; *)
      (*  exists fn0; congruence) *);
        destruct Heq as ( f & Heq ); subst fd.
      rewrite make_call_call_cont; auto.
      eexists ?[SN], ?[T2].
      split; [ eapply Smallstep.star_refl | split ].
      eapply Smallstep.plus_one.
      + eapply Cminor.step_tailcall with ( fd := tfd ).
        * inversion State_wt_cmd; subst.
          unfold global_ptr.
          constructor; cbn.
          reflexivity.
        * apply Heval_args'.
        * unfold Genv.symbol_address.
          now rewrite (symbols_preserved TRANSL), Hfind_symbol, Genv.find_funct_find_funct_ptr.
        * eapply @wt_app_make_signature_correct with
            (prog := prog) (ctx := ctx) (f_id := f_id); now eauto.
        * simpl_pop_stack.
          erewrite stackspace_preserved; eauto.
          admit.
      + inversion Hmatch_fundef as [ ?f ?tf ?Htransl_f | ]; subst.
        eapply match_callstate with (i := 1%positive) (cenv := mkcompilenv fn.(fn_temps) id_malloc id_free); [ | cbn | eauto | ].
        -- eapply Lemmas.preservation; [ | eapply Hstep ];
             econstructor; eauto.
        -- now erewrite <- IR.Linker.linkorder_program_free, <- IR.Linker.linkorder_program_malloc, Htransl_f.
        -- eapply match_args_impl; [ eapply pop_stack_value_cc | ]; eauto.
        -- (inversion Hcall_cont; subst; inversion MK; subst); [ constructor | (econstructor; eauto); [ now eapply match_temps_pop_stack; eauto | now eapply match_cont_pop_stack; eauto ] ].
    - intros T1 Hmatch_states.
      inversion Hmatch_states; subst.
      cbn in TC.
      apply bind_inversion in TC as ( ( te_if & mc_if ) & TE_if & TC ).
      destruct (AST.chunk_eq mc_if AST.Mbool); [ subst; cbn in TC | discriminate ].
      apply bind_inversion in TC as ( tc_then & TC_then & TC ).
      apply bind_inversion in TC as ( tc_else & TC_else & TC ).
      inversion TC; subst; clear TC.
      assert (WT_if: Expr.wt_expr (Ctxt.ctxt_pure ctx) e_i Types.t_bool)
        by (inversion WT; subst; inversion State_wt_cmd; now subst).
      assert (WT_env: Semantics.wt_env fn (Ctxt.ctxt_pure ctx) env)
        by (inversion WT; now subst).
      specialize (transl_expr_sized_progress WT_if TE_if WT_env MCENV MTEMPS Heval_if) as
        ( tv & Hteval & Hinj ).
      specialize (Hteval (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      (* inversion WT; subst; inversion State_wt_cmd; subst. *)
      eexists ?[SN], ?[T2].
      split; [ apply Smallstep.star_refl | split ].
      + apply Smallstep.plus_one; eapply Cminor.step_ifthenelse with (b := b); eauto with deep_gallinac.
      + eapply match_state with (ctx := ctx) (t := t) (id_malloc := id_malloc) (id_free := id_free); auto.
        * (eapply Lemmas.preservation_State_State; eauto); [ admit | inversion WT; subst; inversion State_wt_cmd; now destruct b ].
        * now destruct b.
    - intros T1 Hmatch_states.
      inversion Hmatch_states; subst.
      cbn in TC.
      apply bind_inversion in TC as ( c_cond' & TC_cond & TC ).
      apply bind_inversion in TC as ( c_body' & TC_body & TC ).
      unfold perform_then_ret_unsized in TC;
        inversion TC; subst; clear TC.
      eexists ?[SN], ?[T2].
      split; [ eapply Smallstep.star_refl | split ].
      eapply Smallstep.plus_four with
        (t1 := Events.E0)
        (t2 := Events.E0)
        (t3 := Events.E0)
        (t4 := Events.E0);

        [ apply Cminor.step_seq
        | eapply Cminor.step_block
        | eapply Cminor.step_loop
        | eapply Cminor.step_seq
        | reflexivity
        ].
      eapply match_state with (id_malloc := id_malloc) (id_free := id_free) (ctx := ctx) (t := Types.t_bool); auto.
      + eapply Lemmas.preservation_State_State; eauto.
        admit.
        inversion WT; subst; inversion State_wt_cmd; now subst.
      + eapply match_cont_Kloop1; now eauto.
    - intros T1 Hmatch_states.
      inversion Hmatch_states; subst.
      apply bind_inversion in TFD as ( tf & TF & TFD ).
      inversion TFD; subst; clear TFD.
      unfold transl_function in TF.
      specialize TF as TFB.
      apply bind_inversion in TF as ( tbody & TC & TF ).
      inversion TF; subst; clear TF.
      assert (WTf: (* Prog. *)wt_function (Prog.mk_glob_ctxt prog) fn) by (now inversion WT; subst; inversion Hwt_fundef).
      assert (WTcall: wt_fundef_call args (AST.Internal fn)) by (now inversion WT).
      assert (WTbody: exists t, wt_cmd (Prog.mk_function_ctxt fn.(fn_temps) (Prog.mk_glob_ctxt prog)) fn.(fn_body) t)
        by (inversion WT; subst; inversion Hwt_fundef; subst;
            inversion Hwt_function;
            eexists; apply wt_fn_cmd);
        destruct WTbody as (t_body & WTbody).
      assert (WTinj: CCInj.wf s m inj) by (now inversion WT).
      assert (SBinds_temps: ListExt.SBinds fn.(fn_temps)) by (now inversion WTf).
      specialize
        (@match_state St Hp prog
           fn (fn_body fn) k (Semantics.set_params (fn_params fn) args)
           locals sp
           {|
             Primitives.store := st;
             Primitives.heap := Primitives.heap s
           |}
           m'
           {|
             CCInj.inj_hp_map := CCInj.inj_hp_map inj;
             CCInj.inj_st_map := ListExt.mapi (fun local ofst => (local, (sp, (CCInj.memval_memsize * ofst)%nat, true))) locals ++ CCInj.inj_st_map inj;
             CCInj.inj_fn_map := CCInj.inj_fn_map inj
           |}
           (Cminor.mkfunction
              (Prog.signature_of_signature (Prog.fn_signature fn))
              (params_of_function fn)
              (vars_of_function fn)
              (Z.of_nat fn.(fn_extra).(fn_stackspace))
              tbody)
           tbody tk
        (* (Cminor.set_locals (vars_of_function f) (Cminor.set_params vargs f.(fn_params))) *)
        ) as match_next_state.
      eexists ?[SN], ?[T2].
      split; [ eapply Smallstep.star_refl | split ].
      + eapply Smallstep.plus_one; eapply Cminor.step_internal_function with (m' := m') (sp := sp); [ | | reflexivity ].
        * admit. (* eapply margs_has_argtype_list; eauto. *)
        * apply Halloc_sp.
      + admit.
    - intros T1 Hmatch_states.
      inversion Hmatch_states; subst.
      inversion MK; subst.

      inversion WT; subst;
        inversion Hwt_cont; subst;
        inversion Hwt_cont_call; subst.

  Admitted.

  Theorem transl_program_correct:
    Smallstep.forward_simulation (@Semantics.semantics St Hp prog) (Cminor.semantics tprog).
  Proof using TRANSL.
    eapply Smallstep.forward_simulation_determ_plus with (match_states := match_states prog); eauto.
    - apply Lemmas.determinate.
    - apply senv_preserved.
    - eapply transl_initial_states.
    - apply transl_final_states.
    - cbn.
      intros S1 t S2 Hstep T1 Hmatch.
      specialize (transl_step_correct S1 t S2 Hstep T1 Hmatch) as (S3 & T2 & Hstar & Hplus & Hmatch').
      exists S3, T2.
      now split; [ | split ].
  Qed.

End TRANSLATION.

Global Instance TransfCminorgenLink: TransfLink match_prog.
Proof.
  red.
  intros p1 p2 tp1 tp2 p L MP1 MP2.
  specialize (link_linkorder _ _ _ L) as (LO1 & LO2).
  generalize L.
  Local Transparent IR.Linker.Linker_program.
  simpl; unfold link_program.
  destruct (link (Prog.program_of_program p1) (Prog.program_of_program p2)) as [ pp | ] eqn:LP; try discriminate.
  Local Transparent Linker.Linker_fundef Linking.Linker_fundef.
  destruct p1 as [defs1 public1 main1 [malloc1 free1]], p2 as [defs2 public2 main2 [malloc2 free2]];
    cbn in *.
  destruct (malloc1) as [ m1 | ];
    destruct (malloc2) as [ m2 | ];
    try discriminate;
    try (destruct (Pos.eqb_spec m1 m2) as [ | Hneq ]; subst; try discriminate);
    destruct (free1) as [ f1 | ];
    destruct (free2) as [ f2 | ];
    try discriminate;
    (try (destruct (Pos.eqb_spec f1 f2) as [ | Hneq ]; subst; try discriminate));
    intros E;
    ((eapply Linking.link_match_program;
      eauto);
     admit).
    (*  [ (intros ctx1 ctx2 fd1 tfd1 fd2 tfd2 fd Lfd MFD1 MFD2; *)
    (*     inversion MFD1; subst; inversion MFD2; subst; *)
    (*     simpl in Lfd); *)
    (*    [ discriminate *)
    (*   | destruct ef; inversion Lfd; subst; econstructor; split; [ now eauto | now left; constructor; auto ] *)
    (*   | destruct ef; inversion Lfd; subst; econstructor; split; [ now eauto | now right; constructor; auto ] *)
    (*   | destruct (AST.external_function_eq ef ef0) eqn:E'; inversion Lfd; subst; *)
    (*     econstructor; split; [ now simpl; rewrite dec_eq_true; eauto | now left; constructor ] *)
    (*   ] *)
    (* | now exists tt *)
    (*       | replace (Prog.program_of_program p) with pp; [ now auto | inversion E; subst; destruct pp; auto ] *)
    (* ]. *)
Admitted.
