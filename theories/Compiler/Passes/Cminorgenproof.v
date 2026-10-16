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

From compcert.common Require Linking Values.
From compcert.common Require Import Errors Globalenvs.
From compcert.lib Require Import Coqlib Integers Maps.
From compcert.cfrontend Require Cminorgenproof.
From compcert.backend Require Cminor.

From GallinaC.Utils Require NatExt NExt CompCertExt.
From GallinaC.Utils Require Import PosExt.

From GallinaC.Imp Require Import Store Heap Intops Uint32 Uintptr.

From GallinaC.Compiler.Common Require CCInj Value.
From GallinaC.Compiler.Common Require Expr Ctxt.
From GallinaC.Compiler.Common Require Import Types(t_nat).
From GallinaC.Imp Require Import Storable State.
Import CCInj.Facts Value.Facts.
From GallinaC.Compiler.Passes Require Import Cminorgen.
From GallinaC.Compiler.Common Require Import Semantics.
From GallinaC.Compiler.IR Require Cmd Semantics Lemmas.
From GallinaC.Compiler.IR Require Import Prog Linker Typing.

Local Open Scope error_monad_scope.

Section Match.

  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).

  Definition match_fundef (cu: program) (fd: IR.Prog.fundef) (tfd: Cminor.fundef) : Prop :=
    exists idm idf, exf_declared (Prog.program_of_program cu) idm AST.EF_malloc
                    /\ exf_declared (Prog.program_of_program cu) idf AST.EF_free
                    /\ tfd = transl_fundef idm idf fd.

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
  Lemma transf_program_match [p: program] [tp: Cminor.program]
    (T: transl_program p = OK tp)
    : match_prog p tp.
  Proof using Type.
    unfold transl_program, lookup_exf in T.
    destruct (find_exf_defmap _ AST.EF_malloc) as [ idm | ] eqn:EM; [ | discriminate T ].
    destruct (find_exf_defmap _ AST.EF_free) as [ idf | ] eqn:EF; [ | discriminate T ].
    cbn in T; injection T as <-.
    eapply Linking.match_transform_partial_program2
      with (transf_fun := fun _ fd => OK (transl_fundef idm idf fd))
           (transf_var := fun _ _ => OK tt).
    - unfold AST.transform_partial_program2; cbn.
      induction (Prog.prog_defs p) as [ | [ id [ fd | v ] ] defs IH ];
        cbn; [ reflexivity | | ];
        (destruct (AST.transf_globdefs _ _ defs); [ | discriminate ]);
        cbn in *; injection IH as <-; reflexivity.
    - intros i fd tfd TRANSL.
      injection TRANSL as <-.
      exists idm, idf; split; [ exact (find_exf_defmap_correct EM) | ].
      split; [ exact (find_exf_defmap_correct EF) | ].
      destruct fd; reflexivity.
    - intros i v tv TRANSL.
      now constructor.
  Qed.

  Lemma match_program_main [p tp]
    (MATCH: match_prog p tp)
    : AST.prog_main tp = Prog.prog_main p.
  Proof using Type.
    now destruct MATCH as ( _ & MAIN & _ ).
  Qed.

  Lemma match_fundef_linkorder [cu p: program] [fd tfd]
    (LO: linkorder cu p) (MFD: match_fundef cu fd tfd)
    : match_fundef p fd tfd.
  Proof using Type.
    destruct MFD as ( idm & idf & DECLm & DECLf & ETFD ).
    assert (LOp: Linking.linkorder (Prog.program_of_program cu) (Prog.program_of_program p))
      by exact LO.
    exists idm, idf; split; [ | split; [ | exact ETFD ] ];
      (eapply exf_declared_linkorder; [ intros nm sg E; discriminate E | eassumption | exact LOp ]).
  Qed.

  Lemma exf_declared_match [p: program] [tp: Cminor.program] [id ef]
    (MATCH: match_prog p tp) (DECL: exf_declared (Prog.program_of_program p) id ef)
    : exf_declared tp id ef.
  Proof using Type.
    pose proof (Linking.match_program_defmap _ _ _ _ _ MATCH id) as R.
    unfold exf_declared in *; rewrite DECL in R.
    inversion R as [ | x y MG E1 E2 ]; subst.
    inversion MG as [ ctx' fd tfd LO MF | ]; subst.
    destruct MF as ( ? & ? & _ & _ & -> ); symmetry; assumption.
  Qed.

  Definition match_temps (f: function) (inj: CCInj.injection Ad) (env: @Semantics.env Sm) (tenv: Cminor.env): Prop :=
    forall id t v, In (id, t) (f.(fn_params) ++ f.(fn_temps)) ->
                   Maps.PTree.get id env = Some v ->
                   v = Value.v_tt \/ exists v', Maps.PTree.get id tenv = Some v' /\ CCInj.InjValue inj v v'.

  Record match_stack_block_shape (inj: CCInj.injection Ad) (locals: list Nm) (st: St)
    (sp: Values.block) (base: St) (fe: f_extra): Prop :=
    { MSBrows: CCInj.stack_block_st_rows inj sp locals;
      MSBsize: List.length locals = Z.to_nat fe.(fn_stackspace);
      MSBlayered: layered base locals st;
      MSBmap: locals = [] \/ CCInj.stack_block_st_map inj sp locals }.

  Record match_stack_block_env (inj: CCInj.injection Ad) (f: function) (e: @Semantics.env Sm)
    (locals: list Nm) (st: St) (sp: Values.block) (base: St) (te: Cminor.env): Prop :=
    { MSBshape :> match_stack_block_shape inj locals st sp base f.(fn_extra);
      MSBtemps: match_temps f inj e te }.

  Inductive match_cont (prog: Prog.program) (inj: CCInj.injection Ad) (idm idf: AST.ident)
    : St -> @Semantics.cont Sm -> Cminor.cont -> Prop :=
  | match_cont_Kbind_Kseq: forall [base id_b c k tk]
                                  (MK: match_cont prog inj idm idf base k tk)
    , match_cont prog inj idm idf base (Semantics.Kbind id_b c k)
        (Cminor.Kseq (transl_cmd idm idf (Semantics.cont_target k) c) tk)
  | match_cont_Kloop1: forall [base c_cond id_cond c_body id_body k tk]
                              (MK: match_cont prog inj idm idf base k tk)
    , match_cont prog inj idm idf base
        (Semantics.Kloop1 c_cond id_cond c_body id_body k)
        (Cminor.Kseq
           (Cminor.Sifthenelse (Cminor.Evar id_cond)
              (transl_cmd idm idf (Some id_body) c_body) (Cminor.Sexit 0))
           (Cminor.Kseq
              (Cminor.Sloop
                 (Cminor.Sseq
                    (transl_cmd idm idf (Some id_cond) c_cond)
                    (Cminor.Sifthenelse (Cminor.Evar id_cond)
                       (transl_cmd idm idf (Some id_body) c_body) (Cminor.Sexit 0))))
              (Cminor.Kblock (Cminor.Kseq (return_or_assign_unsized (Semantics.cont_target k)) tk))))
  | match_cont_Kloop2: forall [base c_cond id_cond c_body id_body k tk]
                              (MK: match_cont prog inj idm idf base k tk)
    , match_cont prog inj idm idf base
        (Semantics.Kloop2 c_cond id_cond c_body id_body k)
        (Cminor.Kseq
           (Cminor.Sloop
              (Cminor.Sseq
                 (transl_cmd idm idf (Some id_cond) c_cond)
                 (Cminor.Sifthenelse (Cminor.Evar id_cond)
                    (transl_cmd idm idf (Some id_body) c_body) (Cminor.Sexit 0))))
           (Cminor.Kblock (Cminor.Kseq (return_or_assign_unsized (Semantics.cont_target k)) tk)))
  | match_cont_Kcall: forall [idm' idf' fn e locals sp k target_id optid tfn te tk base st]
                             (TF: transl_funbody idm' idf' fn = tfn)
                             (ST: Semantics.seq_cont_target k target_id)
                             (OI: match ListExt.sfind target_id
                                          ((fn.(fn_params) ++ fn.(fn_temps)) ++ fn.(fn_internals)) with
                                  | Some Types.t_unit => optid = None
                                  | Some _ => optid = Some target_id
                                  | None => False
                                  end)
                             (STACKBL: match_stack_block_env inj fn e locals st sp base te)
                             (MK: match_cont prog inj idm' idf' base k tk)
                             (DECLm: exf_declared (Prog.program_of_program prog) idm' AST.EF_malloc)
                             (DECLf: exf_declared (Prog.program_of_program prog) idf' AST.EF_free)
    , match_cont prog inj idm idf st (Semantics.Kcall fn e locals k) (Cminor.Kcall optid tfn (Values.Vptr sp Ptrofs.zero) te tk)
  | match_cont_Kstop: forall base, match_cont prog inj idm idf base Semantics.Kstop Cminor.Kstop
  .

  Record match_stack_block (prog: Prog.program) (inj: CCInj.injection Ad) (idm idf: AST.ident)
    (f: function) (e: @Semantics.env Sm) (locals: list Nm) (st: St) (sp: Values.block) (base: St)
    (te: Cminor.env) (k: @Semantics.cont Sm) (tk: Cminor.cont): Prop :=
    { MSBenv :> match_stack_block_env inj f e locals st sp base te;
      MSBcont: match_cont prog inj idm idf base k tk }.

  Definition match_ctxt [Pu Iu Sa] (ctx: Ctxt.ctxt Pu Iu Sa _ _) (ge: genv): Prop :=
    Ctxt.ctxt_global ctx = ge.

  Inductive match_args (inj: CCInj.injection Ad): list (Value.value Pt) -> list Values.val -> Prop :=
  | MARGS_nil: match_args inj [] []
  | MARGS_unit: forall [v_args tv_args] (MARGS: match_args inj v_args tv_args), match_args inj (Value.v_tt::v_args) tv_args
  | MARGS_sized: forall [v_arg tv_arg v_args tv_args]
                        (MARGS: match_args inj v_args tv_args)
                        (INJ: CCInj.InjValue inj v_arg tv_arg),
      match_args inj (v_arg::v_args) (tv_arg::tv_args)
  .

  Inductive match_states (p: Prog.program): @Semantics.state Sm -> Cminor.state -> Prop :=
  | match_state:
    forall [idm idf fn c k e locals sp s m inj tfn tk te ctx t base]
           (WT: Semantics.wt_State fn c k e locals s ctx t)
           (WFINJ: CCInj.wf s m inj)
           (STACKBL: match_stack_block p inj idm idf fn e locals (store s) sp base te k tk)
           (TFB: Cminorgen.transl_funbody idm idf fn = tfn)
           (MCTXT: match_ctxt ctx (Globalenvs.Genv.globalenv (Prog.program_of_program p)))
           (DECLm: exf_declared (Prog.program_of_program p) idm AST.EF_malloc)
           (DECLf: exf_declared (Prog.program_of_program p) idf AST.EF_free)
    , match_states p (Semantics.State fn c k e locals s)
        (Cminor.State tfn
           (transl_cmd idm idf (Semantics.cont_target k) c)
           tk (Values.Vptr sp Ptrofs.zero) te m)
  | match_callstate:
    forall [idm idf idm' idf' fd args k m s inj tfd targs tk]
           (WT: Semantics.wt_state p (Semantics.Callstate fd args k s))
           (WFINJ: CCInj.wf s m inj)
           (TFD: Cminorgen.transl_fundef idm idf fd = tfd)
           (MARGS: match_args inj args targs)
           (MK: match_cont p inj idm' idf' (store s) k tk)
           (DECLm: exf_declared (Prog.program_of_program p) idm AST.EF_malloc)
           (DECLf: exf_declared (Prog.program_of_program p) idf AST.EF_free)
    ,
      match_states p (Semantics.Callstate fd args k s)
        (Cminor.Callstate tfd targs tk m)
  | match_returnstate:
    forall [idm idf r k m s inj tr tk]
           (WT: Semantics.wt_state p (Semantics.Returnstate r k s))
           (WFINJ: CCInj.wf s m inj)
           (MRET: r = Value.v_tt \/ CCInj.InjValue inj r tr)
           (MK: match_cont p inj idm idf (store s) k tk),
      match_states p (Semantics.Returnstate r k s)
        (Cminor.Returnstate tr tk m)
  .

End Match.

Arguments MSBrows {Sm} [inj locals st sp base fe] _.
Arguments MSBsize {Sm} [inj locals st sp base fe] _.
Arguments MSBlayered {Sm} [inj locals st sp base fe] _.
Arguments MSBmap {Sm} [inj locals st sp base fe] _.
Arguments MSBshape {Sm} [inj f e locals st sp base te] _.
Arguments MSBtemps {Sm} [inj f e locals st sp base te] _.
Arguments MSBenv {Sm} [prog inj idm idf f e locals st sp base te k tk] _.
Arguments MSBcont {Sm} [prog inj idm idf f e locals st sp base te k tk] _.

Section EXPRESSIONS_HELPER.

  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).

  Lemma transl_expr_progress [ctx e t f] [env: @Semantics.env Sm] [v] [inj: CCInj.injection Ad] [tenv]
    (WTexpr: Expr.wt_expr ctx e t)
    (NUNIT: t <> Types.t_unit)
    (WTenv: Semantics.wt_env f ctx env)
    (MATCHtemps: match_temps f inj env tenv)
    (EVAL: Expr.eval e env = Some v):
    exists tv, (forall tge sp m, Cminor.eval_expr tge sp tenv m (transl_expr e) tv) /\ CCInj.InjValue inj v tv.
  Proof using Type.
    revert v NUNIT EVAL.
    induction WTexpr; intros v NUNIT EVAL; cbn in EVAL; cbn [transl_expr].
    - destruct (Maps.PTree.get var_id env) eqn:Eget_val_env; [ inversion EVAL; subst; clear EVAL | discriminate ].
      destruct (WTenv.(Semantics.wv_ty_env) var_id t true GET) as [ HASval INtemps ].
      specialize (MATCHtemps var_id t v INtemps Eget_val_env) as [ EQ | ( tv & TGET & VCC ) ]; subst.
      {
        exfalso.
        destruct HASval as [ w [GETenv WTval] ].
        assert (w = Value.v_tt) by congruence; subst.
        inversion WTval; subst.
        now apply NUNIT.
      }
      exists tv.
      split; [ | assumption ].
      now econstructor.
    -
      exfalso; now apply NUNIT.
    - inversion EVAL; subst; clear EVAL.
      exists (if b then Values.Vint Int.one else Values.Vint Int.zero).
      split; [ constructor; destruct b; reflexivity | now repeat constructor ].
    - inversion EVAL; subst; clear EVAL.
      exists (Values.Vint (Int.repr (Z.of_nat n))).
      split.
      now constructor.
      constructor.
      exact BOUNDED.
      apply Int.unsigned_repr.
      eauto with ints.
    - inversion EVAL; subst; clear EVAL.
      destruct (Archi.ptr64) eqn:Earchi;
        eexists; (split; [ unfold make_ofst; rewrite Earchi; now constructor | constructor; [ assumption | rewrite Earchi ] ]).
      specialize (Unsigned.CompCert.Ptrofs.unsigned_range_cc_64 (UInt := n_ofst_t) eq_refl Earchi) as RANGE; eexists; split; [ | eauto ]; now apply Int64.unsigned_repr, RANGE.
      specialize (Unsigned.CompCert.Ptrofs.unsigned_range_cc_32 (UInt := n_ofst_t) eq_refl Earchi) as RANGE; eexists; split; [ | eauto ]; now apply Int.unsigned_repr, RANGE.
    - inversion EVAL; subst; clear EVAL.
      exists Values.Vnullptr.
      split.
      now constructor.
      constructor.
    -
      destruct (Expr.eval b env) as [ [ | | | | ] | ] eqn:Eeval; try discriminate.
      inversion EVAL; subst; clear EVAL.
      specialize (IHWTexpr (Value.v_bool b0) ltac:(discriminate) eq_refl) as (tv & EVALexpr & VALCC ).
      exists (Values.Val.notbool tv).
      inversion VALCC; subst; clear VALCC.
      split.
      + unfold make_bool_not.
        econstructor.
        * apply EVALexpr.
        * now econstructor.
        * cbn.
          unfold Values.Val.notbool.
          (destruct b0; cbn); [
              rewrite Int.eq_false; [ reflexivity | apply Int.one_not_zero ]
            | now rewrite Int.eq_true ].
      + destruct b0; now constructor.
    -
      destruct (Expr.eval l env) as [ v' | ]; try discriminate;
        destruct v'; try discriminate;
        destruct (Expr.eval r env) as [ v' | ]; try discriminate;
        destruct v'; try discriminate;
        inversion EVAL; subst; clear EVAL.
      specialize (IHWTexpr1 _ ltac:(discriminate) eq_refl) as ( tv_n1 & EVALtv_n1 & INJn1 ).
      specialize (IHWTexpr2 _ ltac:(discriminate) eq_refl) as ( tv_n2 & EVALtv_n2 & INJn2 ).
      exists (Values.Val.add tv_n1 tv_n2).
      split; [ econstructor; [ apply EVALtv_n1 | apply EVALtv_n2 | auto ] | ].
      inversion INJn1 as [ | ?n ?i BOUNDEDn1 EQn1 | | | ]; subst;
        inversion INJn2 as [ | ?n ?i BOUNDEDn2 EQn2 | | | ]; subst.
      constructor.
      now eauto with ints.
      now symmetry; apply Unsigned.CompCert.BW32.add_cc.
    -
      destruct (Expr.eval l env) as [ v' | ]; try discriminate;
        destruct v'; try discriminate;
        destruct (Expr.eval r env) as [ v' | ]; try discriminate;
        destruct v'; try discriminate;
        inversion EVAL; subst; clear EVAL.
      specialize (IHWTexpr1 _ ltac:(discriminate) eq_refl) as ( tv_n1 & EVALtv_n1 & INJn1 ).
      specialize (IHWTexpr2 _ ltac:(discriminate) eq_refl) as ( tv_n2 & EVALtv_n2 & INJn2 ).
      exists (Values.Val.mul tv_n1 tv_n2).
      split; [ econstructor; [ apply EVALtv_n1 | apply EVALtv_n2 | auto ] | ].
      inversion INJn1 as [ | ?n ?i BOUNDEDn1 EQn1 | | | ]; subst;
        inversion INJn2 as [ | ?n ?i BOUNDEDn2 EQn2 | | | ]; subst.
      constructor.
      now eauto with ints.
      now symmetry; apply Unsigned.CompCert.BW32.mul_cc.
    -
      destruct (Expr.eval l env) as [ v' | ]; try discriminate;
        destruct v'; try discriminate;
        destruct (Expr.eval r env) as [ v' | ]; try discriminate;
        destruct v'; try discriminate;
        inversion EVAL; subst; clear EVAL.
      specialize (IHWTexpr1 _ ltac:(discriminate) eq_refl) as ( tv_l & EVALtv_l & INJtvl ).
      specialize (IHWTexpr2 _ ltac:(discriminate) eq_refl) as ( tv_r & EVALtv_r & INJtvr ).
      exists (Values.Val.cmpu (fun _ _ => false) Ceq tv_l tv_r).
      split; [ econstructor; [ eauto | eauto | eauto ] | ].
      inversion INJtvl; subst.
      inversion INJtvr; subst.
      now eapply CCInj.Facts.InjValue_nat_eq.
  Qed.

  Lemma transl_args_cons e t args:
    transl_args ((e,t)::args)
    = if arg_is_sized (e,t) then transl_expr e :: transl_args args else transl_args args.
  Proof using Type.
    unfold transl_args; cbn [List.filter].
    now destruct (arg_is_sized (e,t)).
  Qed.

  Lemma transl_args_correct
    [te args ctx f] [e: @Semantics.env Sm] [v_args] [inj: CCInj.injection Ad]
    (WT_args: Forall2 (Expr.wt_expr ctx) (map fst args) (map snd args))
    (WT_env: Semantics.wt_env f ctx e)
    (MTEMPS: match_temps f inj e te)
    (E_args:  ListExt.map_opt (fun expr : Expr.expr => Expr.eval expr e) (map fst args) = Some v_args)
    : exists tv_args, (forall tge sp m, Cminor.eval_exprlist tge sp te m (transl_args args) tv_args) /\ match_args inj v_args tv_args.
  Proof using Type.
    revert v_args WT_args E_args.
    induction args as [ | [ expr t ] args ]; intros.
    - cbn in E_args; inversion E_args; subst;
        now repeat econstructor.
    - cbn in WT_args, E_args.
      inversion WT_args as [ | ?x ?y ?l ?l' WT_hd WT_tl ]; subst.
      destruct (ListExt.map_opt _ _) as [ v_args_tl | ] eqn:Eq_eval_tl; [ | now destruct (Expr.eval expr e) ].
      destruct (Expr.eval expr e) as [ v_args_hd | ] eqn:Eq_eval_hd; [ | discriminate ].
      inversion E_args; subst; clear E_args.
      specialize (IHargs v_args_tl WT_tl eq_refl) as ( tv_args_tl & EVALexprlist & VCC ).
      rewrite transl_args_cons; unfold arg_is_sized; cbn [snd].
      destruct (CCInj.type_mem_chunk t) eqn:MC.
      + specialize (transl_expr_progress WT_hd
                      ltac:(intros ->; cbn in MC; discriminate MC)
                      WT_env MTEMPS Eq_eval_hd)
          as ( tv_hd & EVAL_hd & INJ_hd ).
        exists (tv_hd :: tv_args_tl).
        split.
        * intros tge tsp tm; specialize (EVAL_hd tge tsp tm); specialize (EVALexprlist tge tsp tm).
          now constructor.
        * now apply MARGS_sized.
      + destruct t; try discriminate MC.
        rewrite (Lemmas.eval_t_unit WT_hd WT_env) in Eq_eval_hd;
          inversion Eq_eval_hd; subst; clear Eq_eval_hd.
        exists tv_args_tl.
        split; [ exact EVALexprlist | now apply MARGS_unit ].
  Qed.

End EXPRESSIONS_HELPER.


(** This tactic simplifies [Semantics.pop_stack] expressions by exploiting the property

    [Semantics.pop_stack (fn_stackspace (fn_extra f)) s = Some s'] *)

Local Ltac simpl_pop_stack :=
  match goal with
  | POPSTACK : Semantics.pop_stack ?stackspace ?s = Some ?s' |- _ =>
      unfold Semantics.pop_stack, state_pop_n in POPSTACK;
      destruct (NExt.iter_opt _ _ _) as [ st' | ] eqn:Eiter_opt; [ | discriminate ];
      destruct (State.mk_state_opt _ _ _ _) as [ s_pop | ] eqn:Emk_state; [ | discriminate ];
      inversion POPSTACK; subst; clear POPSTACK
  end.

Local Ltac wf_keep_inj WF :=
  constructor;
  [ exact (CCInj.heap_block_bmap WF)
  | exact (CCInj.store_block_map_sbinds2 WF)
  | exact (CCInj.fun_block_map_sbinds2 WF)
  | exact (CCInj.heap_store_distinct WF)
  | exact (CCInj.heap_fun_distinct WF)
  | exact (CCInj.store_fun_distinct WF)
  | idtac.. ].

Section TRANSLATION_HELPER.

  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).

  Lemma match_temps_hp_le [f] [inj inj': CCInj.injection Ad]
    (LEHP: CCInj.inj_hp_le inj inj')
    [e: @Semantics.env Sm] [te]
    (MTEMPS: match_temps f inj e te)
    : match_temps f inj' e te.
  Proof using Type.
    intros id t v IN GET.
    destruct (MTEMPS id t v IN GET) as [ EV | ( tv & GETt & INJ ) ];
      [ now left
      | right; exists tv; split; [ exact GETt | exact (InjValue_hp_le LEHP INJ) ] ].
  Qed.

  Lemma match_cont_inj_map [prog] [inj inj': CCInj.injection Ad] [st_top: St]
    (LEHP: CCInj.inj_hp_le inj inj')
    (NONEW: CCInj.inj_st_nonew inj inj')
    (KEEP: CCInj.inj_st_keep st_top inj inj')
    [idm idf] [base: St] [k: @Semantics.cont Sm] [tk]
    (MK: match_cont prog inj idm idf base k tk)
    (SUB: (base $<= st_top)%sep)
    : match_cont prog inj' idm idf base k tk.
  Proof using Type.
    revert SUB.
    induction MK as [ idm idf base id_b c k tk MK IH
                    | idm idf base c_cond id_cond c_body id_body k tk MK IH
                    | idm idf base c_cond id_cond c_body id_body k tk MK IH
                    | idm idf idm' idf' fn e locals sp k target_id optid tfn te tk base st
                      TF ST OI STACKBL MK IH DECLm DECLf
                    | idm idf base ];
      intros SUB.
    - apply match_cont_Kbind_Kseq; exact (IH SUB).
    - apply match_cont_Kloop1; exact (IH SUB).
    - apply match_cont_Kloop2; exact (IH SUB).
    - destruct STACKBL as [ [ KWTSTACK KLOCALSSZ LAYERED KSTACKBLMAP ] MTEMPS ].
      assert (SUBbase: (base $<= st_top)%sep)
        by exact (substate_tran _ _ _ (layered_sub LAYERED) SUB).
      assert (KCELL: forall n loc (a: Ad),
                 List.nth_error locals n = Some loc -> References loc a ->
                 exists w, (((a |-> w)%mem) $<= st_top)%sep).
      { intros n loc a NTH REF.
        destruct (layered_nth LAYERED n loc NTH) as ( a' & w & REF' & _ & CELL ).
        assert (EA: a' = a) by congruence.
        subst a'; exists w; exact (substate_tran _ _ _ CELL SUB). }
      assert (KWTSTACK': CCInj.stack_block_st_rows inj' sp locals).
      { intros n loc a NTH REF.
        exact (KEEP a (sp, n, true)
                 (KWTSTACK n loc a NTH REF) (KCELL n loc a NTH REF)). }
      assert (KSTACKBLMAP': locals = [] \/ CCInj.stack_block_st_map inj' sp locals).
      { destruct (List.nth_error locals 0%nat) as [ loc0 | ] eqn:E0.
        - right.
          destruct KSTACKBLMAP as [ ENIL | FM ];
            [ rewrite ENIL in E0; cbn in E0; discriminate E0 | ].
          destruct (layered_nth LAYERED 0%nat loc0 E0) as ( a0 & w0 & REF0 & _ & _ ).
          intros a o f IN.
          refine (FM a o f (NONEW sp a o f _ IN)).
          exists a0, 0%nat, true.
          exact (KWTSTACK 0%nat loc0 a0 E0 REF0).
        - left.
          destruct locals as [ | x l ]; [ reflexivity | cbn in E0; discriminate E0 ]. }
      assert (MTEMPS': match_temps fn inj' e te)
        by exact (match_temps_hp_le LEHP MTEMPS).
      assert (MK': match_cont prog inj' idm' idf' base k tk) by exact (IH SUBbase).
      assert (STACKBL': match_stack_block_env inj' fn e locals st sp base te)
        by exact {| MSBshape := {| MSBrows := KWTSTACK'; MSBsize := KLOCALSSZ;
                                    MSBlayered := LAYERED; MSBmap := KSTACKBLMAP' |};
                    MSBtemps := MTEMPS' |}.
      eapply match_cont_Kcall; eassumption.
    - apply match_cont_Kstop.
  Qed.

  Lemma match_cont_hp_le [prog] [inj inj': CCInj.injection Ad]
    (LEHP: CCInj.inj_hp_le inj inj')
    (ESTMAP: inj'.(CCInj.inj_st_map) = inj.(CCInj.inj_st_map))
    [idm idf] [base: St] [k: @Semantics.cont Sm] [tk]
    (MK: match_cont prog inj idm idf base k tk)
    : match_cont prog inj' idm idf base k tk.
  Proof using Type.
    refine (match_cont_inj_map (st_top := base) LEHP _ _ MK (substate_refl base)).
    - intros b a o f _ IN; rewrite ESTMAP in IN; exact IN.
    - intros a x IN _; rewrite ESTMAP; exact IN.
  Qed.

  Lemma match_stack_block_shape_st_map [inj inj': CCInj.injection Ad]
    (ESTMAP: inj'.(CCInj.inj_st_map) = inj.(CCInj.inj_st_map))
    [locals: list Nm] [st: St] [sp base fe]
    (STACKBL: match_stack_block_shape inj locals st sp base fe)
    : match_stack_block_shape inj' locals st sp base fe.
  Proof using Type.
    destruct STACKBL as [ ROWS SIZE LAYERED MAP ].
    constructor.
    - unfold CCInj.stack_block_st_rows; rewrite ESTMAP; exact ROWS.
    - exact SIZE.
    - exact LAYERED.
    - destruct MAP as [ ENIL | FM ];
        [ now left | right; unfold CCInj.stack_block_st_map; rewrite ESTMAP; exact FM ].
  Qed.

  Lemma match_stack_block_env_hp_le [inj inj': CCInj.injection Ad]
    (LEHP: CCInj.inj_hp_le inj inj')
    (ESTMAP: inj'.(CCInj.inj_st_map) = inj.(CCInj.inj_st_map))
    [f] [e: @Semantics.env Sm] [locals st sp base te]
    (STACKBL: match_stack_block_env inj f e locals st sp base te)
    : match_stack_block_env inj' f e locals st sp base te.
  Proof using Type.
    exact {| MSBshape := match_stack_block_shape_st_map ESTMAP STACKBL;
             MSBtemps := match_temps_hp_le LEHP STACKBL.(MSBtemps) |}.
  Qed.

  Lemma match_stack_block_hp_le [prog] [inj inj': CCInj.injection Ad]
    (LEHP: CCInj.inj_hp_le inj inj')
    (ESTMAP: inj'.(CCInj.inj_st_map) = inj.(CCInj.inj_st_map))
    [idm idf f] [e: @Semantics.env Sm] [locals st sp base te k tk]
    (STACKBL: match_stack_block prog inj idm idf f e locals st sp base te k tk)
    : match_stack_block prog inj' idm idf f e locals st sp base te k tk.
  Proof using Type.
    exact {| MSBenv := match_stack_block_env_hp_le LEHP ESTMAP STACKBL;
             MSBcont := match_cont_hp_le LEHP ESTMAP STACKBL.(MSBcont) |}.
  Qed.

  Lemma stackspace_preserved [p f c k e locals sp s m tf tc tk te]
    (MS: @match_states Sm p
               (Semantics.State f c k e locals s)
               (Cminor.State tf tc tk (Values.Vptr sp Ptrofs.zero) te m)):
    tf.(Cminor.fn_stackspace) = CCInj.offset_to_offset f.(fn_extra).(fn_stackspace).
  Proof using Type.
    inversion MS; subst.
    reflexivity.
  Qed.

  Lemma symbols_preserved
    {prog: Prog.program} {tprog: Cminor.program}
    (TRANSL: match_prog prog tprog):
    forall (s: AST.ident), Globalenvs.Genv.find_symbol (Genv.globalenv tprog) s = Globalenvs.Genv.find_symbol (Genv.globalenv (Prog.program_of_program prog)) s.
  Proof using Type.
    apply (Genv.find_symbol_match TRANSL).
  Qed.

  Lemma function_ptr_translated {prog: Prog.program} {tprog: Cminor.program}
    (TRANSL: match_prog prog tprog):
    forall {b: Values.block} {f: fundef},
      Genv.find_funct_ptr (Genv.globalenv (Prog.program_of_program prog)) b = Some f ->
      exists cu tf, Genv.find_funct_ptr (Genv.globalenv tprog) b = Some tf /\ match_fundef cu f tf /\ linkorder cu prog.
  Proof using Type.
    apply (Genv.find_funct_ptr_match TRANSL).
  Qed.

  Lemma functions_translated {prog: Prog.program} {tprog: Cminor.program}
    (TRANSL: match_prog prog tprog):
    forall {v: Values.val} {f: fundef},
      Genv.find_funct (Genv.globalenv (Prog.program_of_program prog)) v = Some f ->
      exists cu tf, Genv.find_funct (Genv.globalenv tprog) v = Some tf /\ match_fundef cu f tf /\ linkorder cu prog.
  Proof using Type.
    apply (Genv.find_funct_match TRANSL).
  Qed.

  Lemma wt_app_make_signature_correct
    {prog: Prog.program}
    {ctx f_id t_out args b fd tfd cu}
    (MCTXT: match_ctxt ctx (Genv.globalenv (Prog.program_of_program prog)))
    (FINDSYMB: Genv.find_symbol (Genv.globalenv (Prog.program_of_program prog)) f_id = Some b)
    (FINDFUNCTPTR: Genv.find_funct_ptr (Genv.globalenv (Prog.program_of_program prog)) b = Some fd)
    (MFD: match_fundef cu fd tfd)
    (LO: linkorder cu prog)
    (WTAPP: @Typing.wt_cmd ctx (Cmd.c_app f_id t_out args) t_out)
    : Cminor.funsig tfd = mk_signature (map snd args) t_out.
  Proof using Type.
    destruct MFD as ( idm & idf & _ & _ & -> ).
    destruct fd as [ f | ef ].
    - inversion WTAPP; subst.
      + inversion MCTXT as ( Eglob_ctxt ); subst; clear MCTXT.
        assert (fn = f) by
          (unfold Ctxt.get_global in FINDfn;
           rewrite Eglob_ctxt in FINDfn;
           rewrite FINDSYMB in FINDfn;
           unfold Genv.find_funct_ptr in FINDFUNCTPTR;
           rewrite FINDfn in FINDFUNCTPTR;
           congruence); subst.
        destruct f;
          unfold Prog.signature_of_signature, Cminorgen.transl_fundef, Cminorgen.transl_function,
            Cminorgen.transl_funbody in *;
          cbn in *.
        unfold Prog.fn_signature; cbn.
        now rewrite EQargs.
      + inversion MCTXT as ( Eglob_ctxt ); subst; clear MCTXT.
        unfold Ctxt.get_global in FINDfn.
        rewrite Eglob_ctxt in FINDfn.
        rewrite FINDSYMB in FINDfn.
        unfold Genv.find_funct_ptr in FINDFUNCTPTR.
        rewrite FINDfn in FINDFUNCTPTR.
        congruence.
    - inversion WTAPP; subst.
      + inversion MCTXT as ( Eglob_ctxt ); subst; clear MCTXT.
        unfold Ctxt.get_global in FINDfn.
        rewrite Eglob_ctxt in FINDfn.
        rewrite FINDSYMB in FINDfn.
        unfold Genv.find_funct_ptr in FINDFUNCTPTR.
        rewrite FINDfn in FINDFUNCTPTR.
        congruence.
      + inversion MCTXT as ( Eglob_ctxt ); subst; clear MCTXT.
        unfold Ctxt.get_global in FINDfn.
        rewrite Eglob_ctxt in FINDfn.
        rewrite FINDSYMB in FINDfn.
        unfold Genv.find_funct_ptr in FINDFUNCTPTR.
        rewrite FINDfn in FINDFUNCTPTR.
        inversion FINDFUNCTPTR; subst.
        inversion SIG; subst; reflexivity.
  Qed.

  Lemma make_call_call_cont [k: @Semantics.cont Sm] [f_id args sig] (CALLCONT: Semantics.is_call_cont k):
    make_call (Semantics.cont_target k) f_id args sig = Cminor.Stailcall sig (global_ptr f_id) args.
  Proof using Type.
    now inversion CALLCONT.
  Qed.

  Lemma match_args_impl [inj1 inj2: CCInj.injection Ad] (INJIMPL: forall (v: Value.value Pt) tv, CCInj.InjValue inj1 v tv -> CCInj.InjValue inj2 v tv): forall (args: list (Value.value Pt)) targs (MARGS: match_args inj1 args targs), match_args inj2 args targs.
  Proof using Type.
    intros; induction MARGS;
      constructor; auto.
  Qed.

  Lemma match_cont_reindex
    [k: @Semantics.cont Sm] [tk prog] [inj: CCInj.injection Ad] [idm idf idm2 idf2] [base: St]
    (CALLCONT: Semantics.is_call_cont k)
    (MK: match_cont prog inj idm idf base k tk)
    : match_cont prog inj idm2 idf2 base k tk.
  Proof using Type.
    inversion CALLCONT; subst; inversion MK; subst; econstructor; eauto.
  Qed.

  Lemma match_cont_call_cont
    [k: @Semantics.cont Sm] [tk prog] [inj: CCInj.injection Ad] [idm idf idm2 idf2] [base: St]
    (CALLCONT: Semantics.is_call_cont k)
    (MK: match_cont prog inj idm idf base k tk)
    : match_cont prog inj idm2 idf2 base k (Cminor.call_cont tk).
  Proof using Type.
    inversion CALLCONT; subst; inversion MK; subst; cbn [Cminor.call_cont]; econstructor; eauto.
  Qed.

  Lemma set_optid_match_temps [f] [inj: CCInj.injection Ad] [target_id v] [env: @Semantics.env Sm] [optid tv te t]
    (MT: match_temps f inj env te)
    (OI : match t with
          | Types.t_unit => optid = None
          | _ => optid = Some target_id
          end)
    (INJ: CCInj.InjValue inj v tv \/ v = Value.v_tt)
    (WT: Value.wt_value v t)
    : match_temps f inj (PTree.set target_id v env) (Cminor.set_optvar optid tv te).
  Proof using Type.
    intros any_id any_t any_v any_IN GET.
    specialize (MT any_id any_t any_v any_IN).
    rewrite PTree.gsspec in GET.
    destruct (peq any_id target_id) as [ EQ | NE ]; subst.
    - inversion GET; subst; clear GET.
      destruct INJ as [ INJ | H ]; [ | now left ].
      right.
      exists tv.
      destruct t;
        try (now inversion INJ; subst; inversion WT);
        subst; cbn;
        rewrite PTree.gss; auto.
    - specialize (MT GET) as [ H | (tv' & TGET & INJ') ].
      now left.
      right.
      exists tv'.
      destruct t;
        try (now inversion INJ'; subst; inversion WT);
        subst; cbn;
        rewrite PTree.gso; auto.
  Qed.

  Lemma set_params_match_temps [ctx] [f: function] [inj: CCInj.injection Ad] [args: list (Value.value Pt)] [targs]
    (WT: wt_function ctx f)
    (WTcall: wt_fundef_call args (AST.Internal f))
    (MARGS: match_args inj args targs)
    : match_temps f inj
        (Semantics.set_params (fn_params f) args)
        (Cminor.set_locals (vars_of_function f) (Cminor.set_params targs (params_of_function f))).
  Proof using Type.
    remember (AST.Internal f) as fd eqn:Efd.
    destruct WTcall as [ ?args ?f WTargs | ];
      try discriminate; inversion Efd; subst; clear Efd.

    assert (IDSJ: forall id, In id (List.map fst (fn_params f)) ->
                             ~ In id (List.map fst f.(fn_internals))).
    { intros id INp INi.
      refine (proj1 (ListExt.DBinds_iff_disjoint_fst _ _)
                (wt_fn_locals_internals_distinct WT) id _ INi).
      rewrite List.map_app; apply List.in_or_app; left; exact INp. }
    destruct WT as [ _ _ SBinds_params SBinds_temps Disjoint _ _ ].
    unfold vars_of_function.
    set (IL := f.(fn_internals)) in *; clearbody IL.
    destruct f as [ fn_return fn_params fn_temps fn_internals fn_body [ fn_stackspace ] ];
      cbn; cbn in SBinds_params, SBinds_temps, Disjoint, WTargs, IDSJ.
    apply ListExt.DBinds_Forall in Disjoint.
    intros ident ident_ty v _ LOOKUP.
    clear fn_return fn_body fn_stackspace.
    revert args targs MARGS WTargs LOOKUP Disjoint.
    induction fn_params as [ | [ fn_param_hd_id fn_param_hd_ty ] fn_params_tl ];
      cbn; intros.
    - destruct args as [ | [ ] ]; now rewrite PTree.gempty in LOOKUP.
    - inversion MARGS.
      + subst; cbn in LOOKUP; now rewrite PTree.gempty in LOOKUP.
      + inversion WTargs as [ | args_hd ?y args_tl ?l' WT_hd WT_tl ];
          subst; inversion H1; subst; clear H1.
        inversion Disjoint as [ | [ ] ?l Disjoint_hd Disjoint_tl ]; subst.
        rewrite PTree.gsspec in LOOKUP.
        destruct (peq ident fn_param_hd_id) as [ | NE ]; [ inversion LOOKUP; subst; now left | subst ].
        specialize (IHfn_params_tl ltac:(now inversion SBinds_params) (fun id H => IDSJ id (or_intror H)) v_args targs MARGS0 WT_tl LOOKUP Disjoint_tl) as [ EQ | (tv & LOOKUP' & INJtv ) ]; [ now left | ].
        right.
        exists tv.
        split; [ | now auto ].
        now inversion WT_hd; subst.
      + inversion WTargs as [ | args_hd ?y args_tl ?l' WT_hd WT_tl ];
          subst; inversion H1; subst; clear H1.
        inversion Disjoint as [ | [ ] ?l Disjoint_hd Disjoint_tl ]; subst.
        rewrite PTree.gsspec in LOOKUP.
        specialize (value_compcert_sized INJ) as SIZED.
        destruct (peq ident fn_param_hd_id) as [ | NE ]; subst.
        * inversion LOOKUP; subst; clear LOOKUP.
          right; exists tv_arg.
          split; [ | now auto ].
          assert (REWRITE: match fn_param_hd_ty with
                            | Types.t_unit => None
                            | _ => Some fn_param_hd_id
                            end = Some fn_param_hd_id) by (inversion WT_hd; subst; now inversion SIZED);
            rewrite REWRITE; clear REWRITE.
          rewrite Cminorgenproof.set_locals_outside.
          cbn.
          rewrite PTree.gsspec.
          now destruct (peq fn_param_hd_id fn_param_hd_id).
          intros contra.
          apply List.in_app_or in contra as [ contra | contra ];
            [ | exact (IDSJ fn_param_hd_id (or_introl eq_refl) contra) ].
          apply Disjoint_hd.
          inversion SBinds_temps as [ | fn_temps_hd_id fn_temps_hd_ty fn_temps_tl _ SBinds_temps_tl ]; [ subst; contradiction | subst ].
          specialize (ListExt.SBinds_map_fst_SIns SBinds_temps) as SIns_temps.
          specialize (ListExt.SIns_In SIns_temps contra) as contra'.
          specialize (ListExt.SIn_map_fst_SBindIn SBinds_temps contra') as (b & SBINDINtemps).
          exists (fn_param_hd_id, b).
          split; auto. apply ListExt.BindIn_In. apply ListExt.SBindIn_BindIn. auto.
        * inversion SBinds_params as [ | ?a ?b ?l _ SBinds_params_tl ]; subst.
          inversion WTargs as [ | ?x ?y ?l ?l' WTargs_hd WTargs_tl ]; subst.
          specialize (Lemmas.set_params_nth LOOKUP) as (n & ty & INparams & _).
          apply nth_error_In in INparams.
          apply ListExt.SBinds_In in INparams; auto.
          specialize (IHfn_params_tl SBinds_params_tl (fun id H => IDSJ id (or_intror H)) v_args tv_args MARGS0 WTargs_tl LOOKUP Disjoint_tl) as [ EQ | ( tv & SET & INJ' ) ]; [ now left | right ].
          assert (Abs_ident: ~ In ident (map fst fn_temps)).
          {
            intros contra.
            specialize (ListExt.SBinds_map_fst_SIns SBinds_temps) as SIns_temps.
            specialize (ListExt.SIns_In SIns_temps contra) as SIn_ident.
            specialize (ListExt.SIn_map_fst_SBindIn SBinds_temps SIn_ident) as (t & SBindIn).
            pose proof (Disjoint_tl_fwd :=
              fun x INx => (proj1 (List.Forall_forall _ _) Disjoint_tl x INx));
              eapply Disjoint_tl_fwd.
            eapply ListExt.BindIn_In, ListExt.SBindIn_BindIn; eauto.
            exists (ident, t).
            split; [ now eapply ListExt.BindIn_In, ListExt.SBindIn_BindIn | auto ].
          }
          exists tv; split; [ | assumption ].
          assert (REWRITE: match fn_param_hd_ty with
                            | Types.t_unit => None
                            | _ => Some fn_param_hd_id
                            end = Some fn_param_hd_id) by (inversion WT_hd; subst; now inversion SIZED);
            rewrite REWRITE; clear REWRITE.
          assert (ABSID: ~ In ident (List.map fst fn_temps ++ List.map fst IL)).
          { intros contra.
            apply List.in_app_or in contra as [ contra | contra ];
              [ exact (Abs_ident contra) | ].
            refine (IDSJ ident (or_intror _) contra).
            apply List.in_map_iff; exists (ident, ty); split;
              [ reflexivity
              | exact (ListExt.BindIn_In (ListExt.SBindIn_BindIn INparams)) ]. }
          rewrite Cminorgenproof.set_locals_outside; cbn; auto.
          rewrite PTree.gsspec.
          destruct (peq ident fn_param_hd_id); [ congruence | ].
          rewrite Cminorgenproof.set_locals_outside in SET; auto.
  Qed.

  Lemma read_var_load [inj: CCInj.injection Ad] [s: Sm] [m sp] [locals: list Nm] [n nm] [v: Vl] [t mc base fe]
    (WFINJ: CCInj.wf s m inj)
    (STACKBL: match_stack_block_shape inj locals (store s) sp base fe)
    (WTE: wt_f_extra fe)
    (DEREF: List.nth_error locals n = Some nm)
    (LOOKUP: lookup (store s) nm = Some (encode v))
    (WTv: Value.wt_value v t)
    (MC: CCInj.type_mem_chunk t = Some mc)
    : exists tv,
        Memory.Mem.loadv mc m
          (Values.Vptr sp (Ptrofs.repr (CCInj.offset_to_offset (Z.of_nat n)))) = Some tv
        /\ CCInj.InjValue inj v tv.
  Proof using Type.
    destruct STACKBL as [ WTSTACK LOCALSSZ LAYERED STACKBLMAP ].
    assert (ENC: encode v = v) by reflexivity.
    rewrite ENC in LOOKUP.
    destruct (proj2 (lookup_iff (store s) nm v) LOOKUP) as ( a & REF & _ & SUB ).
    destruct (CCInj.mem_contents_of_store WFINJ a v SUB) as ( b & o & fr & INmap & LOADS ).
    specialize (WTSTACK n nm a DEREF REF) as INstack.
    specialize (ListExt.SBinds2_fun (CCInj.store_block_map_sbinds2 WFINJ) a _ _ INmap INstack) as EQ.
    inversion EQ; subst b o fr.
    assert (MCv: CCInj.type_mem_chunk (Value.type_of_value v) = Some mc)
      by (rewrite (Value.Facts.type_of_value_complete WTv); exact MC).
    destruct (LOADS mc MCv) as ( tv & INJ & LOAD ).
    exists tv; split; [ | exact INJ ].
    cbn [Memory.Mem.loadv].
    rewrite Ptrofs.unsigned_repr by exact (Lemmas.stack_slot_bound WTE LOCALSSZ DEREF).
    exact LOAD.
  Qed.

  Lemma stack_block_range_perm
    [inj: CCInj.injection Ad] [s: Sm] [m sp] [locals: list Nm] [base] [fe: f_extra]
    (WFINJ: CCInj.wf s m inj)
    (STACKBL: match_stack_block_shape inj locals (store s) sp base fe)
    : Memory.Mem.range_perm m sp 0 (CCInj.offset_to_offset fe.(fn_stackspace))
        Memtype.Cur Memtype.Freeable.
  Proof using Type.
    destruct STACKBL as [ WTSTACK LOCALSSZ LAYERED STACKBLMAP ].
    specialize memword_bytes_pos as MSPOS.
    assert (MSZ: (0 < Z.of_nat memword_bytes)%Z) by lia.
    intros ofs RNG.
    destruct (offset_to_offset_slot (proj1 RNG)) as ( n & BND ).
    unfold CCInj.offset_to_offset in RNG, BND.
    assert (SSPOS: (0 <= fe.(fn_stackspace))%Z) by nia.
    assert (ELEN: Z.of_nat (List.length locals) = fe.(fn_stackspace))
      by (rewrite LOCALSSZ; exact (Z2Nat.id _ SSPOS)).
    assert (NLT: (n < List.length locals)%nat) by nia.
    destruct (List.nth_error locals n) as [ nm | ] eqn:NTH;
      [ | exfalso; apply List.nth_error_None in NTH; lia ].
    destruct (layered_nth LAYERED n nm NTH) as ( a & w & REF & _ & _ ).
    refine (CCInj.mem_perm_of_store WFINJ a sp n true
              (WTSTACK n nm a NTH REF) ofs _).
    unfold CCInj.offset_to_offset.
    lia.
  Qed.

  Lemma pop_stack_block_wf
    [inj: CCInj.injection Ad] [s s'': Sm] [m sp] [locals: list Nm] [base] [fe: f_extra]
    (WFINJ: CCInj.wf s m inj)
    (STACKBL: match_stack_block_shape inj locals (store s) sp base fe)
    (POP: Semantics.pop_stack fe.(fn_stackspace) s = Some s'')
    : exists m' inj',
        Memory.Mem.free m sp 0 (CCInj.offset_to_offset fe.(fn_stackspace)) = Some m'
        /\ inj'.(CCInj.inj_hp_map) = inj.(CCInj.inj_hp_map)
        /\ CCInj.wf s'' m' inj'
        /\ (forall (a: Ad) b o f, In (a, (b, o, f)) inj'.(CCInj.inj_st_map) ->
              In (a, (b, o, f)) inj.(CCInj.inj_st_map))
        /\ CCInj.inj_st_keep base inj inj'.
  Proof using Type.
    pose proof STACKBL as FR; destruct FR as [ WTSTACK LOCALSSZ LAYERED STACKBLMAP ].
    specialize memword_bytes_pos as MSPOS.
    assert (MSZ: (0 < Z.of_nat memword_bytes)%Z) by lia.
    destruct (Memory.Mem.range_perm_free m sp 0
                (CCInj.offset_to_offset fe.(fn_stackspace))
                (stack_block_range_perm WFINJ STACKBL)) as ( m' & FREE ).
    assert (ESTORE: store s'' = base)
      by exact (Lemmas.pop_stack_base LAYERED LOCALSSZ POP).
    assert (EHEAP: heap s'' = heap s).
    { unfold Semantics.pop_stack in POP.
      now destruct (proj1 State.state_pop_n_some POP) as ( _ & _ & EH & _ ). }
    assert (EALC: State.alc s'' = State.alc s).
    { unfold Semantics.pop_stack in POP.
      now destruct (proj1 State.state_pop_n_some POP) as ( _ & _ & _ & EA ). }
    set (rest := CCInj.drop_stack_block_rows locals inj.(CCInj.inj_st_map)).
    assert (BASEFRESH: forall (a: Ad) w,
               (((a |-> w)%mem) $<= base)%sep -> ref_addr_inb locals a = false).
    { intros a w SUB.
      destruct (ref_addr_inb locals a) as [ | ] eqn:EIN; [ exfalso | reflexivity ].
      destruct (ref_addr_inb_elim EIN) as ( i & nm & NTH & REF ).
      exact (layered_base_addr_neq LAYERED SUB NTH REF eq_refl). }
    assert (INrest: forall a b o f, In (a, (b, o, f)) rest ->
                      In (a, (b, o, f)) inj.(CCInj.inj_st_map))
      by (intros a b o f IN; exact (CCInj.drop_stack_block_rows_in IN)).
    assert (NErest: forall a b o f, In (a, (b, o, f)) rest ->
               b <> sp \/ (CCInj.offset_to_offset fe.(fn_stackspace) <= 0)%Z).
    { destruct STACKBLMAP as [ ENIL | FM ].
      - intros a b o f _; right.
        rewrite ENIL in LOCALSSZ; cbn [List.length] in LOCALSSZ.
        assert (SS: (fe.(fn_stackspace) <= 0)%Z) by lia.
        unfold CCInj.offset_to_offset; nia.
      - intros a b o f IN; left; intros EB; subst b.
        destruct (FM a o f (INrest a sp o f IN)) as ( n & nm & NTH & REF & _ ).
        pose proof (ref_addr_inb_intro NTH REF) as TRUE.
        rewrite (CCInj.drop_stack_block_rows_notlocal IN) in TRUE; discriminate TRUE. }
    assert (SPCASE: (exists a o f, In (a, (sp, o, f)) inj.(CCInj.inj_st_map))
                    \/ (CCInj.offset_to_offset fe.(fn_stackspace) <= 0)%Z).
    { destruct locals as [ | loc0 locs ].
      - right.
        cbn [List.length] in LOCALSSZ.
        assert (SS: (fe.(fn_stackspace) <= 0)%Z) by lia.
        unfold CCInj.offset_to_offset; nia.
      - left.
        destruct (layered_nth LAYERED 0%nat loc0 eq_refl) as ( a & w & REF & _ & _ ).
        exists a, 0%nat, true.
        exact (WTSTACK 0%nat loc0 a eq_refl REF). }
    assert (DISJhp: forall bh bh' szh lvh,
               ListExt.BindIn bh (bh', (szh, lvh)) inj.(CCInj.inj_hp_map) ->
               bh' <> sp \/ (CCInj.offset_to_offset fe.(fn_stackspace) <= 0)%Z).
    { intros bh bh' szh lvh HIN.
      destruct SPCASE as [ ( a & o & f & IN ) | LE ]; [ left | now right ].
      exact (CCInj.heap_store_distinct WFINJ bh bh' szh lvh a sp o f
               (ListExt.BindIn_In HIN) IN). }
    assert (DISJfn: forall id bf, In (id, bf) inj.(CCInj.inj_fn_map) ->
               bf <> sp \/ (CCInj.offset_to_offset fe.(fn_stackspace) <= 0)%Z).
    { intros id bf IN.
      destruct SPCASE as [ ( a & o & f & INst ) | LE ]; [ left | now right ].
      exact (not_eq_sym (CCInj.store_fun_distinct WFINJ a sp o id bf f INst IN)). }
    exists m', (CCInj.Build_injection Ad inj.(CCInj.inj_hp_map) rest
                                      inj.(CCInj.inj_fn_map)).
    split; [ exact FREE | split; [ reflexivity | ] ].
    split; [ | split ];
      [ | cbn [CCInj.inj_st_map]; exact INrest
        | cbn [CCInj.inj_st_map]; intros a x IN ( w & SUB );
          destruct x as [ [ b o ] f ];
          exact (CCInj.drop_stack_block_rows_keep IN (BASEFRESH a w SUB)) ].
    constructor;
      cbn [CCInj.inj_hp_map CCInj.inj_st_map CCInj.inj_fn_map].
    - exact (CCInj.heap_block_bmap WFINJ).
    - exact (ListExt.SBinds2_filter _ (CCInj.store_block_map_sbinds2 WFINJ)).
    - exact (CCInj.fun_block_map_sbinds2 WFINJ).
    - intros bh bh' szh lvh a b2 o f INh INr.
      exact (CCInj.heap_store_distinct WFINJ bh bh' szh lvh a b2 o f INh
               (INrest a b2 o f INr)).
    - exact (CCInj.heap_fun_distinct WFINJ).
    - intros a b1 o id b2 f INst INfn.
      exact (CCInj.store_fun_distinct WFINJ a b1 o id b2 f
               (INrest a b1 o f INst) INfn).
    - intros bh oh w SUB.
      rewrite EHEAP in SUB.
      destruct (CCInj.mem_contents_of_heap WFINJ SUB) as ( bh' & szh & HIN & LOADS ).
      exists bh', szh; split; [ exact HIN | ].
      intros mcc MCC.
      destruct (LOADS mcc MCC) as ( w' & INJ & LOAD ).
      exists w'; split; [ refine (InjValue_hp_le (CCInj.inj_hp_le_eq _) INJ); reflexivity | ].
      rewrite (CompCertExt.CCMem.free_stack_block_load FREE (DISJhp bh bh' szh true HIN)); exact LOAD.
    - intros a w SUB.
      rewrite ESTORE in SUB.
      destruct (CCInj.mem_contents_of_store WFINJ a w
                  (substate_tran _ _ _ SUB (layered_sub LAYERED)))
        as ( b & o & f & IN & LOADS ).
      assert (INr: In (a, (b, o, f)) rest)
        by exact (CCInj.drop_stack_block_rows_keep IN (BASEFRESH a w SUB)).
      exists b, o, f; split; [ exact INr | ].
      intros mcc MCC.
      destruct (LOADS mcc MCC) as ( w' & INJ & LOAD ).
      exists w'; split; [ refine (InjValue_hp_le (CCInj.inj_hp_le_eq _) INJ); reflexivity | ].
      rewrite (CompCertExt.CCMem.free_stack_block_load FREE (NErest a b o f INr)); exact LOAD.
    - intros id b IN.
      destruct (CCInj.mem_contents_of_fun WFINJ id b IN) as ( CONT & ACC ).
      split.
      + rewrite (CompCertExt.CCMem.free_stack_block_contents FREE); exact CONT.
      + rewrite (CompCertExt.CCMem.free_stack_block_access FREE (DISJfn id b IN)); exact ACC.
    - intros bh bh' szh HIN.
      rewrite (CompCertExt.CCMem.free_stack_block_load FREE (DISJhp bh bh' szh true HIN)).
      exact (CCInj.mem_header_of_heap WFINJ bh bh' szh HIN).
    - intros bh bh' szh lvh HIN.
      destruct (CCInj.mem_extent_of_heap WFINJ bh bh' szh lvh HIN)
        as ( BND & VB & RP ).
      split; [ exact BND | split ].
      + exact (Memory.Mem.valid_block_free_1 _ _ _ _ _ FREE _ VB).
      + intros ELV.
        exact (CompCertExt.CCMem.free_stack_block_perm FREE (DISJhp bh bh' szh lvh HIN) (RP ELV)).
    - intros bh oh w bh' szh lvh SUB HIN.
      rewrite EHEAP in SUB.
      exact (CCInj.heap_contents_compact WFINJ bh oh w bh' szh lvh SUB HIN).
    - intros a b o f IN.
      exact (CompCertExt.CCMem.free_stack_block_perm FREE (NErest a b o f IN)
               (CCInj.mem_perm_of_store WFINJ a b o f (INrest a b o f IN))).
    - intros bh bh' szh lvh bid INh GET.
      rewrite EALC in GET.
      exact (CCInj.heap_block_below_alc WFINJ bh bh' szh lvh bid INh GET).
  Qed.

  Lemma push_stack_block_wf
    [inj: CCInj.injection Ad] [s s': Sm] [m m' sp] [locals: list Nm] [st sg]
    [fe: f_extra]
    (WFINJ: CCInj.wf s m inj)
    (ALLOC: Memory.Mem.alloc m 0 (CCInj.offset_to_offset fe.(fn_stackspace)) = (m', sp))
    (LOCALS: stack_block_alloc (encode (v_tt: Vl)) (Z.to_N fe.(fn_stackspace)) (store s) (scnt s)
             = Some (st, sg, locals))
    (STACKBL: mk_state_opt st sg (heap s) (alc s) = Some s')
    : exists inj': CCInj.injection Ad,
        inj'.(CCInj.inj_hp_map) = inj.(CCInj.inj_hp_map)
        /\ CCInj.wf s' m' inj'
        /\ match_stack_block_shape inj' locals (store s') sp (store s) fe
        /\ CCInj.inj_st_nonew inj inj'
        /\ CCInj.inj_st_keep (store s) inj inj'.
  Proof using Type.
    specialize memword_bytes_pos as MSPOS.
    destruct (stack_block_alloc_inv (state_store_dominates s) (encode (v_tt: Vl))
                (Z.to_N fe.(fn_stackspace)) st sg locals LOCALS)
      as ( LEN & _ & LAYERED & DEC ).
    destruct (proj1 (mk_state_opt_some _ _ _ _ _) STACKBL)
      as ( ESTORE & _ & EHEAP & EALC ).
    pose proof (Memory.Mem.fresh_block_alloc _ _ _ _ _ ALLOC) as SPFRESH.
    assert (LENn: List.length locals = Z.to_nat fe.(fn_stackspace))
      by (rewrite LEN; exact (Z_N_nat _)).
    assert (NESTORE: forall (a: Ad) b o f,
               In (a, (b, o, f)) inj.(CCInj.inj_st_map) -> b <> sp).
    { intros a b o f IN EB; subst b.
      exact (SPFRESH (wf_store_block_valid WFINJ IN)). }
    assert (NEFUN: forall id b, In (id, b) inj.(CCInj.inj_fn_map) -> b <> sp).
    { intros id b IN EB; subst b.
      exact (SPFRESH (wf_fun_block_valid WFINJ IN)). }
    assert (NEHEAP: forall bh bh' szh lvh,
               ListExt.BindIn bh (bh', (szh, lvh)) inj.(CCInj.inj_hp_map) -> bh' <> sp).
    { intros bh bh' szh lvh HIN EB; subst bh'.
      destruct (CCInj.mem_extent_of_heap WFINJ bh sp szh lvh HIN) as ( _ & VB & _ ).
      exact (SPFRESH VB). }
    assert (BASEFRESH: forall (a: Ad) w,
               (((a |-> w)%mem) $<= (store s))%sep -> ref_addr_inb locals a = false).
    { intros a w SUB.
      destruct (ref_addr_inb locals a) as [ | ] eqn:EIN; [ exfalso | reflexivity ].
      destruct (ref_addr_inb_elim EIN) as ( i & nm & NTH & REF ).
      exact (layered_base_addr_neq LAYERED SUB NTH REF eq_refl). }
    set (newrows := CCInj.st_map_of_locals sp locals).
    set (rest := CCInj.drop_stack_block_rows locals inj.(CCInj.inj_st_map)).
    assert (INrest: forall (a: Ad) b o f, In (a, (b, o, f)) rest ->
                      In (a, (b, o, f)) inj.(CCInj.inj_st_map))
      by (intros a b o f IN; exact (CCInj.drop_stack_block_rows_in IN)).
    assert (NEWSTACK: forall n loc (a: Ad),
               List.nth_error locals n = Some loc -> References loc a ->
               In (a, (sp, n, true)) newrows)
      by (intros n loc a NTH REF; exact (CCInj.st_map_of_locals_In NTH REF)).
    assert (NEWPERM: forall (a: Ad) b o f, In (a, (b, o, f)) newrows ->
               b = sp /\ f = true
               /\ (o < List.length locals)%nat).
    { intros a b o f IN.
      destruct (CCInj.st_map_of_locals_inv IN) as ( EB & EF & ( n & nm & NTH & _ & EO ) ).
      split; [ exact EB | split; [ exact EF | ] ].
      subst o; apply List.nth_error_Some; rewrite NTH; discriminate. }
    exists (CCInj.Build_injection Ad inj.(CCInj.inj_hp_map) (newrows ++ rest)
              inj.(CCInj.inj_fn_map)).
    cbn [CCInj.inj_hp_map CCInj.inj_st_map CCInj.inj_fn_map].
    split; [ reflexivity | ].
    split; [ | split; [ | split ] ].
    - constructor;
        cbn [CCInj.inj_hp_map CCInj.inj_st_map CCInj.inj_fn_map].
      + exact (CCInj.heap_block_bmap WFINJ).
      + refine (ListExt.SBinds2_app_intro (CCInj.st_map_of_locals_sbinds2 LAYERED)
                  (ListExt.SBinds2_filter _ (CCInj.store_block_map_sbinds2 WFINJ)) _).
        intros a x a' y IN1 IN2.
        destruct x as [ [ bx ox ] fx ].
        destruct (CCInj.st_map_of_locals_inv IN1)
          as ( EB & EF & ( n & nm & NTH & REF & EO ) ); subst bx fx ox.
        destruct y as [ [ by0 oy ] fy ].
        split.
        * intros EA; subst a'.
          pose proof (ref_addr_inb_intro NTH REF) as TRUE.
          rewrite (CCInj.drop_stack_block_rows_notlocal IN2) in TRUE; discriminate TRUE.
        * intros EQ.
          apply (f_equal (fun z: Values.block * nat * bool => fst (fst z))) in EQ.
          cbn [fst] in EQ.
          exact (NESTORE a' by0 oy fy (INrest a' by0 oy fy IN2) (eq_sym EQ)).
      + exact (CCInj.fun_block_map_sbinds2 WFINJ).
      + intros bh bh' szh lvh a b2 o f INh INst.
        destruct (in_app_or _ _ _ INst) as [ INn | INr ].
        * destruct (NEWPERM a b2 o f INn) as ( EB & _ & _ ); subst b2.
          exact (NEHEAP bh bh' szh lvh
                   (ListExt.BMap_In_BindIn (CCInj.heap_block_bmap WFINJ) INh)).
        * exact (CCInj.heap_store_distinct WFINJ bh bh' szh lvh a b2 o f INh
                   (INrest a b2 o f INr)).
      + exact (CCInj.heap_fun_distinct WFINJ).
      + intros a b1 o id b2 f INst INfn.
        destruct (in_app_or _ _ _ INst) as [ INn | INr ].
        * destruct (NEWPERM a b1 o f INn) as ( EB & _ & _ ); subst b1.
          exact (not_eq_sym (NEFUN id b2 INfn)).
        * exact (CCInj.store_fun_distinct WFINJ a b1 o id b2 f
                   (INrest a b1 o f INr) INfn).
      + intros bh oh w SUB.
        rewrite EHEAP in SUB.
        destruct (CCInj.mem_contents_of_heap WFINJ SUB) as ( bh' & szh & HIN & LOADS ).
        exists bh', szh; split; [ exact HIN | ].
        intros mcc MCC.
        destruct (LOADS mcc MCC) as ( w' & INJ & LOAD ).
        exists w'; split;
          [ refine (InjValue_hp_le (CCInj.inj_hp_le_eq _) INJ); reflexivity | ].
        destruct (CCInj.mem_extent_of_heap WFINJ bh bh' szh true HIN) as ( _ & VB & _ ).
        rewrite (Memory.Mem.load_alloc_unchanged _ _ _ _ _ ALLOC _ _ _ VB).
        exact LOAD.
      + intros a w SUB.
        rewrite ESTORE in SUB.
        destruct (DEC a w SUB) as [ SUB0 | ( i & nm & NTH & REF & EW ) ].
        * destruct (CCInj.mem_contents_of_store WFINJ a w SUB0)
            as ( b & o & f & IN & LOADS ).
          exists b, o, f; split.
          { apply in_or_app; right.
            exact (CCInj.drop_stack_block_rows_keep IN (BASEFRESH a w SUB0)). }
          intros mcc MCC.
          destruct (LOADS mcc MCC) as ( w' & INJ & LOAD ).
          exists w'; split;
            [ refine (InjValue_hp_le (CCInj.inj_hp_le_eq _) INJ); reflexivity | ].
          rewrite (Memory.Mem.load_alloc_unchanged _ _ _ _ _ ALLOC _ _ _
                     (wf_store_block_valid WFINJ IN)).
          exact LOAD.
        * exists sp, i, true; split.
          { apply in_or_app; left; exact (NEWSTACK i nm a NTH REF). }
          intros mcc MCC; exfalso; subst w.
          cbn in MCC; discriminate MCC.
      + intros id b IN.
        destruct (CCInj.mem_contents_of_fun WFINJ id b IN) as ( CONT & ACC ).
        split.
        * rewrite (CompCertExt.CCMem.alloc_contents_other ALLOC (NEFUN id b IN)); exact CONT.
        * rewrite (CompCertExt.CCMem.alloc_access_other ALLOC (NEFUN id b IN)); exact ACC.
      + intros bh bh' szh HIN.
        destruct (CCInj.mem_extent_of_heap WFINJ bh bh' szh true HIN) as ( _ & VB & _ ).
        rewrite (Memory.Mem.load_alloc_unchanged _ _ _ _ _ ALLOC _ _ _ VB).
        exact (CCInj.mem_header_of_heap WFINJ bh bh' szh HIN).
      + intros bh bh' szh lvh HIN.
        destruct (CCInj.mem_extent_of_heap WFINJ bh bh' szh lvh HIN)
          as ( BND & VB & RP ).
        split; [ exact BND | split ].
        * exact (Memory.Mem.valid_block_alloc _ _ _ _ _ ALLOC _ VB).
        * intros ELV ofs RNG.
          exact (Memory.Mem.perm_alloc_1 _ _ _ _ _ ALLOC _ _ _ _ (RP ELV ofs RNG)).
      + intros bh oh w bh' szh lvh SUB HIN.
        rewrite EHEAP in SUB.
        exact (CCInj.heap_contents_compact WFINJ bh oh w bh' szh lvh SUB HIN).
      + intros a b o f IN.
        destruct (in_app_or _ _ _ IN) as [ INn | INr ].
        * destruct (NEWPERM a b o f INn) as ( EB & EF & LTn ).
          subst b f.
          intros ofs RNG.
          refine (Memory.Mem.perm_alloc_2 _ _ _ _ _ ALLOC ofs _ _).
          rewrite LENn in LTn.
          assert (SSPOS: (0 <= fe.(fn_stackspace))%Z) by lia.
          assert (NZ: (Z.of_nat o < fe.(fn_stackspace))%Z)
            by (rewrite <- (Z2Nat.id _ SSPOS); apply Nat2Z.inj_lt; exact LTn).
          unfold CCInj.offset_to_offset in RNG |- *.
          nia.
        * intros ofs RNG.
          refine (Memory.Mem.perm_alloc_1 _ _ _ _ _ ALLOC _ _ _ _ _).
          exact (CCInj.mem_perm_of_store WFINJ a b o f (INrest a b o f INr) ofs RNG).
      + intros bh bh' szh lvh bid INh GET.
        rewrite EALC in GET.
        exact (CCInj.heap_block_below_alc WFINJ bh bh' szh lvh bid INh GET).
    - constructor.
      + intros n loc a NTH REF.
        apply in_or_app; left; exact (NEWSTACK n loc a NTH REF).
      + exact LENn.
      + rewrite ESTORE; exact LAYERED.
      + right; intros a o f IN.
        cbn [CCInj.inj_st_map] in IN.
        destruct (in_app_or _ _ _ IN) as [ INn | INr ];
          [ exact (proj2 (proj2 (CCInj.st_map_of_locals_inv INn)))
          | exact (False_ind _ (NESTORE a sp o f (INrest a sp o f INr) eq_refl)) ].
    - intros b a o f ( a' & o' & f' & INb ) IN.
      cbn [CCInj.inj_st_map] in IN.
      destruct (in_app_or _ _ _ IN) as [ INn | INr ];
        [ destruct (NEWPERM a b o f INn) as ( EB & _ & _ );
          exact (False_ind _ (NESTORE a' b o' f' INb EB))
        | exact (INrest a b o f INr) ].
    - intros a x IN ( w & SUB ).
      cbn [CCInj.inj_st_map].
      apply in_or_app; right.
      exact (CCInj.drop_stack_block_rows_keep IN (BASEFRESH a w SUB)).
  Qed.

  Lemma wf_free_gc [inj: CCInj.injection Ad] [s: Sm] [m] [p: Pt] [hp']
    (WFINJ: CCInj.wf s m inj)
    (FREE: free (heap s) p = Some hp')
    : CCInj.wf (State.state_free s FREE) m inj.
  Proof using Type.
    pose proof (State.heap_state_free s p hp' FREE) as EHEAP.
    pose proof (State.store_state_free s p hp' FREE) as ESTORE.
    wf_keep_inj WFINJ.
    - intros bh oh w SUB.
      rewrite EHEAP in SUB.
      exact (CCInj.mem_contents_of_heap WFINJ (free_heap_cell_sub FREE SUB)).
    - intros a w SUB.
      rewrite ESTORE in SUB.
      exact (CCInj.mem_contents_of_store WFINJ a w SUB).
    - exact (CCInj.mem_contents_of_fun WFINJ).
    - exact (CCInj.mem_header_of_heap WFINJ).
    - exact (CCInj.mem_extent_of_heap WFINJ).
    - intros bh oh w bh' szh lvh SUB HIN.
      rewrite EHEAP in SUB.
      exact (CCInj.heap_contents_compact WFINJ bh oh w bh' szh lvh
               (free_heap_cell_sub FREE SUB) HIN).
    - exact (CCInj.mem_perm_of_store WFINJ).
    - intros bh bh' szh lvh bid INh GET.
      rewrite (State.alc_state_free s p hp' FREE) in GET.
      exact (CCInj.heap_block_below_alc WFINJ bh bh' szh lvh bid INh GET).
  Qed.

  Lemma wf_free_heap [inj: CCInj.injection Ad] [s: Sm] [m] [bg b' sz]
    (WFINJ: CCInj.wf s m inj)
    (HIN: ListExt.BindIn bg (b', (sz, true)) inj.(CCInj.inj_hp_map))
    (NOCELL: forall o (w: Vl),
        ~ ((((mkAddr bg (N.of_nat o)) |-> w)%mem) $<= State.heap s)%sep)
    : exists m',
        Memory.Mem.free m b' (- Memdata.size_chunk AST.Mptr)%Z
          (CCInj.offset_to_offset (Z.of_N sz)) = Some m'
        /\ CCInj.wf s m'
             (CCInj.Build_injection Ad (CCInj.heap_map_free bg inj.(CCInj.inj_hp_map))
                inj.(CCInj.inj_st_map) inj.(CCInj.inj_fn_map)).
  Proof using Type.
    destruct (CCInj.mem_extent_of_heap WFINJ bg b' sz true HIN)
      as ( BNDg & VBg & RPg ).
    specialize (RPg eq_refl) as RPgt.
    destruct (Memory.Mem.range_perm_free m b'
                (- Memdata.size_chunk AST.Mptr)%Z
                (CCInj.offset_to_offset (Z.of_N sz)) RPgt) as ( m' & FREE ).
    assert (INV: forall bh bh' szh lvh,
               ListExt.BindIn bh (bh', (szh, lvh))
                 (CCInj.heap_map_free bg inj.(CCInj.inj_hp_map)) ->
               (bh <> bg /\ ListExt.BindIn bh (bh', (szh, lvh)) inj.(CCInj.inj_hp_map))
               \/ (bh = bg /\ bh' = b' /\ szh = sz /\ lvh = false)).
    { intros bh bh' szh lvh HINk.
      destruct (ListExt.bmap_update_a_BindIn_inv Nat.eqb_spec HINk)
        as ( c & HIN0 & [ ( NE & EC ) | ( EB & EC ) ] ).
      - left; split; [ exact NE | rewrite EC; exact HIN0 ].
      - right; subst bh.
        assert (EROW: (b', (sz, true)) = (bh', c))
          by exact (ListExt.BindIn_fun _ _ _ _ HIN0 HIN).
        injection EROW as Eb Ec; subst bh' c.
        cbn in EC; injection EC as Esz Elv; subst szh lvh.
        now repeat split. }
    assert (INold: forall bh bh' pc,
               In (bh, (bh', pc)) (CCInj.heap_map_free bg inj.(CCInj.inj_hp_map)) ->
               exists pc0, In (bh, (bh', pc0)) inj.(CCInj.inj_hp_map)).
    { intros bh bh' pc IN; exact (ListExt.bmap_update_a_In_inv IN). }
    assert (NEblk: forall bh bh' szh lvh,
               ListExt.BindIn bh (bh', (szh, lvh)) inj.(CCInj.inj_hp_map) ->
               bh <> bg -> bh' <> b').
    { intros bh bh' szh lvh HINh NE EQ; subst bh'.
      apply NE.
      exact (CCInj.Facts.heap_block_inj WFINJ (ListExt.BindIn_In HINh)
               (ListExt.BindIn_In HIN)). }
    assert (NEst: forall a bs os fr,
               In (a, (bs, os, fr)) inj.(CCInj.inj_st_map) -> bs <> b').
    { intros a bs os fr IN.
      exact (not_eq_sym (CCInj.heap_store_distinct WFINJ bg b' sz true a bs os fr
                           (ListExt.BindIn_In HIN) IN)). }
    assert (NEfn: forall id bf, In (id, bf) inj.(CCInj.inj_fn_map) -> bf <> b').
    { intros id bf IN.
      exact (not_eq_sym (CCInj.heap_fun_distinct WFINJ bg b' sz true id bf
                           (ListExt.BindIn_In HIN) IN)). }
    exists m'; split; [ exact FREE | ].
    constructor; cbn [CCInj.inj_hp_map CCInj.inj_st_map CCInj.inj_fn_map].
    - exact (ListExt.bmap_update_a_BMap (CCInj.heap_block_bmap WFINJ)).
    - exact (CCInj.store_block_map_sbinds2 WFINJ).
    - exact (CCInj.fun_block_map_sbinds2 WFINJ).
    - intros bh bh1 szh lvh a bs os fr INh INs.
      destruct (INold bh bh1 (szh, lvh) INh) as ( pc0 & INh0 ).
      destruct pc0 as ( sz0 & lv0 ).
      exact (CCInj.heap_store_distinct WFINJ bh bh1 sz0 lv0 a bs os fr INh0 INs).
    - intros bh bh1 szh lvh id bf INh INf.
      destruct (INold bh bh1 (szh, lvh) INh) as ( pc0 & INh0 ).
      destruct pc0 as ( sz0 & lv0 ).
      exact (CCInj.heap_fun_distinct WFINJ bh bh1 sz0 lv0 id bf INh0 INf).
    - exact (CCInj.store_fun_distinct WFINJ).
    - intros bh oh w SUB.
      assert (NEh: bh <> bg)
        by (intro EQ; subst bh; exact (NOCELL oh w SUB)).
      destruct (CCInj.mem_contents_of_heap WFINJ SUB) as ( bh' & szh & HINh & LOADS ).
      exists bh', szh; split.
      { exact (ListExt.bmap_update_a_BindIn_neq Nat.eqb_spec NEh HINh). }
      intros mcc MCC.
      destruct (LOADS mcc MCC) as ( w' & INJ & LOAD ).
      exists w'; split.
      { refine (InjValue_hp_le _ INJ).
        intros b1 b1' sz1 lv1 HIN1.
        destruct (Nat.eq_dec b1 bg) as [ EB | NEB ].
        - subst b1; exists false; cbn [CCInj.inj_hp_map].
          assert (EROW: (b', (sz, true)) = (b1', (sz1, lv1)))
            by exact (ListExt.BindIn_fun _ _ _ _ HIN1 HIN).
          injection EROW as Eb Esz Elv; subst b1' sz1.
          exact (ListExt.bmap_update_a_BindIn_eq (f := fun szlv => (fst szlv, false))
                   Nat.eqb_spec HIN).
        - exists lv1; cbn [CCInj.inj_hp_map].
          exact (ListExt.bmap_update_a_BindIn_neq Nat.eqb_spec NEB HIN1). }
      rewrite (CompCertExt.CCMem.free_stack_block_load FREE (or_introl (NEblk bh bh' szh true HINh NEh))).
      exact LOAD.
    - intros a w SUB.
      destruct (CCInj.mem_contents_of_store WFINJ a w SUB)
        as ( bs & os & fr & IN & LOADS ).
      exists bs, os, fr; split; [ exact IN | ].
      intros mcc MCC.
      destruct (LOADS mcc MCC) as ( w' & INJ & LOAD ).
      exists w'; split.
      { refine (InjValue_hp_le _ INJ).
        intros b1 b1' sz1 lv1 HIN1.
        destruct (Nat.eq_dec b1 bg) as [ EB | NEB ].
        - subst b1; exists false; cbn [CCInj.inj_hp_map].
          assert (EROW: (b', (sz, true)) = (b1', (sz1, lv1)))
            by exact (ListExt.BindIn_fun _ _ _ _ HIN1 HIN).
          injection EROW as Eb Esz Elv; subst b1' sz1.
          exact (ListExt.bmap_update_a_BindIn_eq (f := fun szlv => (fst szlv, false))
                   Nat.eqb_spec HIN).
        - exists lv1; cbn [CCInj.inj_hp_map].
          exact (ListExt.bmap_update_a_BindIn_neq Nat.eqb_spec NEB HIN1). }
      rewrite (CompCertExt.CCMem.free_stack_block_load FREE (or_introl (NEst a bs os fr IN))).
      exact LOAD.
    - intros id bf IN.
      destruct (CCInj.mem_contents_of_fun WFINJ id bf IN) as ( CONT & ACC ).
      split.
      + rewrite (CompCertExt.CCMem.free_stack_block_contents FREE); exact CONT.
      + rewrite (CompCertExt.CCMem.free_stack_block_access FREE (or_introl (NEfn id bf IN))); exact ACC.
    - intros bh bh' szh HINk.
      destruct (INV bh bh' szh true HINk) as [ ( NEh & HINh ) | ( _ & _ & _ & ABS ) ];
        [ | discriminate ABS ].
      rewrite (CompCertExt.CCMem.free_stack_block_load FREE (or_introl (NEblk bh bh' szh true HINh NEh))).
      exact (CCInj.mem_header_of_heap WFINJ bh bh' szh HINh).
    - intros bh bh' szh lvh HINk.
      destruct (INV bh bh' szh lvh HINk) as [ ( NEh & HINh ) | ( EB & Eb & Esz & Elv ) ].
      + destruct (CCInj.mem_extent_of_heap WFINJ bh bh' szh lvh HINh)
          as ( BND & VB & RP ).
        split; [ exact BND | split ].
        * exact (Memory.Mem.valid_block_free_1 _ _ _ _ _ FREE _ VB).
        * intros ELV.
          exact (CompCertExt.CCMem.free_stack_block_perm FREE
                   (or_introl (NEblk bh bh' szh lvh HINh NEh)) (RP ELV)).
      + subst bh bh' szh lvh.
        split; [ exact BNDg | split ].
        * exact (Memory.Mem.valid_block_free_1 _ _ _ _ _ FREE _ VBg).
        * intros ABS; discriminate ABS.
    - intros bh oh w bh' szh lvh SUB HINk.
      assert (NEh: bh <> bg)
        by (intro EQ; subst bh; exact (NOCELL oh w SUB)).
      destruct (INV bh bh' szh lvh HINk) as [ ( _ & HINh ) | ( EB & _ ) ];
        [ | exfalso; exact (NEh EB) ].
      exact (CCInj.heap_contents_compact WFINJ bh oh w bh' szh lvh SUB HINh).
    - intros a bs os fr IN.
      exact (CompCertExt.CCMem.free_stack_block_perm FREE (or_introl (NEst a bs os fr IN))
               (CCInj.mem_perm_of_store WFINJ a bs os fr IN)).
    - intros bh bh' szh lvh bid INh GET.
      destruct (INold bh bh' (szh, lvh) INh) as ( pc0 & INh0 ).
      destruct pc0 as ( sz0 & lv0 ).
      exact (CCInj.heap_block_below_alc WFINJ bh bh' sz0 lv0 bid INh0 GET).
  Qed.

  Lemma store_local_progress
    [inj: CCInj.injection Ad] [s: Sm] [m sp] [a: Ad] [n: nat] [tv mc t]
    (WFINJ: CCInj.wf s m inj)
    (INnm: In (a, (sp, n, true)) inj.(CCInj.inj_st_map))
    (MC: CCInj.type_mem_chunk t = Some mc)
    : exists m',
        Memory.Mem.store mc m sp (CCInj.offset_to_offset (Z.of_nat n)) tv = Some m'.
  Proof using Type.
    specialize (memword_bytes_size_chunk MC) as SZ.
    assert (VA: Memory.Mem.valid_access m mc sp
                  (CCInj.offset_to_offset (Z.of_nat n)) Memtype.Writable).
    { split.
      - intros ofs RNG.
        apply (Memory.Mem.perm_implies _ _ _ _ Memtype.Freeable); [ | constructor ].
        apply (CCInj.mem_perm_of_store WFINJ a sp n true INnm ofs).
        lia.
      - exact (offset_to_offset_align MC _). }
    destruct (Memory.Mem.valid_access_store m mc sp
                (CCInj.offset_to_offset (Z.of_nat n)) tv VA) as ( m' & EQ ).
    exists m'; exact EQ.
  Qed.

  Lemma wf_store_local
    [inj: CCInj.injection Ad] [s: Sm] [m m'] [sp] [nm: Nm] [a: Ad] [o0]
    [v: Vl] [tv mc st']
    (WFINJ: CCInj.wf s m inj)
    (REFnm: References nm a)
    (INnm: In (a, (sp, o0, true)) inj.(CCInj.inj_st_map))
    (MUTATE: mutate (store s) nm v = Some st')
    (INJv: CCInj.InjValue inj v tv)
    (MC: CCInj.type_mem_chunk (Value.type_of_value v) = Some mc)
    (STORE: Memory.Mem.store mc m sp (CCInj.offset_to_offset (Z.of_nat o0)) tv = Some m')
    (DSJ: forall a' b' o' f',
        a' <> a ->
        In (a', (b', o', f')) inj.(CCInj.inj_st_map) ->
        b' <> sp \/ o' <> o0)
    : CCInj.wf (State.state_mutate_store s MUTATE) m' inj.
  Proof using Type.
    assert (NEsp: forall bh bh' szh lvh,
               ListExt.BindIn bh (bh', (szh, lvh)) inj.(CCInj.inj_hp_map) ->
               bh' <> sp).
    { intros bh bh' szh lvh HIN.
      exact (CCInj.heap_store_distinct WFINJ bh bh' szh lvh a sp o0 true
               (ListExt.BindIn_In HIN) INnm). }
    assert (NEfn: forall id bf, In (id, bf) inj.(CCInj.inj_fn_map) -> bf <> sp).
    { intros id bf IN.
      exact (not_eq_sym (CCInj.store_fun_distinct WFINJ a sp o0 id bf true INnm IN)). }
    pose proof (State.store_state_mutate_store s nm v st' MUTATE) as ESTORE.
    pose proof (State.heap_state_mutate_store s nm v st' MUTATE) as EHEAP.
    wf_keep_inj WFINJ.
    - intros bh oh w SUB.
      rewrite EHEAP in SUB.
      destruct (CCInj.mem_contents_of_heap WFINJ SUB) as ( bh' & szh & HIN & LOADS ).
      exists bh', szh; split; [ exact HIN | ].
      intros mcc MCC.
      destruct (LOADS mcc MCC) as ( w' & INJ & LOAD ).
      exists w'; split; [ exact INJ | ].
      rewrite (Memory.Mem.load_store_other _ _ _ _ _ _ STORE mcc bh'
                 (CCInj.offset_to_offset (Z.of_nat oh))
                 (or_introl (NEsp _ _ _ _ HIN))).
      exact LOAD.
    - intros a' w SUB.
      rewrite ESTORE in SUB.
      destruct (proj1 (mutate_mem_iff (store s) nm v st' a REFnm MUTATE a' w) SUB)
        as [ ( EA & EV ) | ( NEA & SUBo ) ]; subst.
      + exists sp, o0, true; split; [ exact INnm | ].
        intros mcc MCC.
        assert (EMC: mcc = mc) by congruence; subst mcc.
        exists tv; split; [ exact INJv | ].
        rewrite (Memory.Mem.load_store_same _ _ _ _ _ _ STORE).
        rewrite (CCInj.Facts.InjValue_load_result INJv MC); reflexivity.
      + destruct (CCInj.mem_contents_of_store WFINJ a' w SUBo)
          as ( b' & o' & f' & IN & LOADS ).
        exists b', o', f'; split; [ exact IN | ].
        intros mcc MCC.
        destruct (LOADS mcc MCC) as ( w' & INJ & LOAD ).
        exists w'; split; [ exact INJ | ].
        specialize (memword_bytes_size_chunk MCC) as SZ1.
        specialize (memword_bytes_size_chunk MC) as SZ2.
        assert (DZ: b' <> sp
                    \/ (CCInj.offset_to_offset (Z.of_nat o') + Memdata.size_chunk mcc
                        <= CCInj.offset_to_offset (Z.of_nat o0))%Z
                    \/ (CCInj.offset_to_offset (Z.of_nat o0) + Memdata.size_chunk mc
                        <= CCInj.offset_to_offset (Z.of_nat o'))%Z).
        { destruct (DSJ a' b' o' f' NEA IN) as [ NEB | NEO ]; [ now left | right ].
          destruct (offset_to_offset_dsj NEO) as [ LE | LE ];
            [ left | right ]; lia. }
        rewrite (Memory.Mem.load_store_other _ _ _ _ _ _ STORE mcc b'
                   (CCInj.offset_to_offset (Z.of_nat o')) DZ).
        exact LOAD.
    - intros id b IN.
      destruct (CCInj.mem_contents_of_fun WFINJ id b IN) as ( CONT & ACC ).
      split.
      + rewrite (Memory.Mem.store_mem_contents _ _ _ _ _ _ STORE).
        rewrite Maps.PMap.gso by exact (NEfn _ _ IN).
        exact CONT.
      + rewrite (Memory.Mem.store_access _ _ _ _ _ _ STORE); exact ACC.
    - intros bh bh' szh HIN.
      rewrite (Memory.Mem.load_store_other _ _ _ _ _ _ STORE AST.Mptr bh'
                 (- Memdata.size_chunk AST.Mptr)%Z (or_introl (NEsp _ _ _ _ HIN))).
      exact (CCInj.mem_header_of_heap WFINJ bh bh' szh HIN).
    - intros bh bh' szh lvh HIN.
      destruct (CCInj.mem_extent_of_heap WFINJ bh bh' szh lvh HIN)
        as ( BND & VB & RP ).
      split; [ exact BND | split ].
      + exact (Memory.Mem.store_valid_block_1 _ _ _ _ _ _ STORE _ VB).
      + intros ELV ofs RNG.
        eapply Memory.Mem.perm_store_1; [ exact STORE | exact (RP ELV ofs RNG) ].
    - intros bh oh w bh' szh lvh SUB HIN.
      rewrite EHEAP in SUB.
      exact (CCInj.heap_contents_compact WFINJ bh oh w bh' szh lvh SUB HIN).
    - intros a' b' o' f' IN ofs RNG.
      eapply Memory.Mem.perm_store_1; [ exact STORE | ].
      exact (CCInj.mem_perm_of_store WFINJ a' b' o' f' IN ofs RNG).
    - intros bh bh' szh lvh bid INh GET.
      rewrite (State.alc_state_mutate_store s nm v st' MUTATE) in GET.
      exact (CCInj.heap_block_below_alc WFINJ bh bh' szh lvh bid INh GET).
  Qed.

  Lemma wf_mutate_store_unsized
    [inj: CCInj.injection Ad] [s: Sm] [m] [nm: Nm] [v: Vl] [st']
    (WFINJ: CCInj.wf s m inj)
    (MUTATE: mutate (store s) nm v = Some st')
    (MC: CCInj.type_mem_chunk (Value.type_of_value v) = None)
    : CCInj.wf (State.state_mutate_store s MUTATE) m inj.
  Proof using Type.
    destruct (proj2 (mutate_some_iff (store s) nm v) (ex_intro _ st' MUTATE))
      as ( a0 & v0 & REF0 & _ & SUB0 ).
    pose proof (State.store_state_mutate_store s nm v st' MUTATE) as ESTORE.
    pose proof (State.heap_state_mutate_store s nm v st' MUTATE) as EHEAP.
    wf_keep_inj WFINJ.
    - intros bh oh w SUB.
      rewrite EHEAP in SUB.
      exact (CCInj.mem_contents_of_heap WFINJ SUB).
    - intros a' w SUB.
      rewrite ESTORE in SUB.
      destruct (proj1 (mutate_mem_iff (store s) nm v st' a0 REF0 MUTATE a' w) SUB)
        as [ ( EA & EV ) | ( NEA & SUBo ) ]; subst.
      + destruct (CCInj.mem_contents_of_store WFINJ a0 v0 SUB0)
          as ( b & o & fr & IN & _ ).
        exists b, o, fr; split; [ exact IN | ].
        intros mcc MCC; rewrite MC in MCC; discriminate MCC.
      + exact (CCInj.mem_contents_of_store WFINJ a' w SUBo).
    - exact (CCInj.mem_contents_of_fun WFINJ).
    - exact (CCInj.mem_header_of_heap WFINJ).
    - exact (CCInj.mem_extent_of_heap WFINJ).
    - intros bh oh w bh' szh lvh SUB HIN.
      rewrite EHEAP in SUB.
      exact (CCInj.heap_contents_compact WFINJ bh oh w bh' szh lvh SUB HIN).
    - exact (CCInj.mem_perm_of_store WFINJ).
    - intros bh bh' szh lvh bid INh GET.
      rewrite (State.alc_state_mutate_store s nm v st' MUTATE) in GET.
      exact (CCInj.heap_block_below_alc WFINJ bh bh' szh lvh bid INh GET).
  Qed.

  Lemma write_var_store
    [inj: CCInj.injection Ad] [s: Sm] [m sp] [locals: list Nm] [base]
    [n nm] [v: Vl] [t mc tv fe] [st']
    (WFINJ: CCInj.wf s m inj)
    (STACKBL: match_stack_block_shape inj locals (store s) sp base fe)
    (WTE: wt_f_extra fe)
    (DEREF: List.nth_error locals n = Some nm)
    (MUTATE: mutate (store s) nm (encode v) = Some st')
    (INJv: CCInj.InjValue inj v tv)
    (WTv: Value.wt_value v t)
    (MC: CCInj.type_mem_chunk t = Some mc)
    : exists m',
        Memory.Mem.storev mc m
          (Values.Vptr sp (Ptrofs.repr (CCInj.offset_to_offset (Z.of_nat n)))) tv
          = Some m'
        /\ CCInj.wf (State.state_mutate_store s MUTATE) m' inj.
  Proof using Type.
    destruct STACKBL as [ WTSTACK LOCALSSZ LAYERED STACKBLMAP ].
    destruct (layered_nth LAYERED n nm DEREF) as ( a & w & REF & _ & _ ).
    specialize (WTSTACK n nm a DEREF REF) as INnm.
    assert (MCv: CCInj.type_mem_chunk (Value.type_of_value v) = Some mc)
      by (rewrite (Value.Facts.type_of_value_complete WTv); exact MC).
    destruct (store_local_progress (tv := tv) WFINJ INnm MC) as ( m2 & STORE ).
    exists m2; split.
    - cbn [Memory.Mem.storev].
      rewrite Ptrofs.unsigned_repr by exact (Lemmas.stack_slot_bound WTE LOCALSSZ DEREF).
      exact STORE.
    - exact (wf_store_local WFINJ REF INnm MUTATE INJv MCv STORE
               (CCInj.write_var_dsj STACKBLMAP DEREF REF)).
  Qed.

  Lemma read_ptr_load [inj: CCInj.injection Ad] [s: Sm] [m] [p: Pt] [v: Vl] [t mc tvp]
    (WFINJ: CCInj.wf s m inj)
    (INJp: CCInj.InjValue inj (Value.v_ptr p) tvp)
    (LOOKUP: lookup (heap s) p = Some (encode v))
    (WTv: Value.wt_value v t)
    (MC: CCInj.type_mem_chunk t = Some mc)
    : exists tv,
        Memory.Mem.loadv mc m tvp = Some tv
        /\ CCInj.InjValue inj v tv.
  Proof using Type.
    assert (ENC: encode v = v) by reflexivity.
    rewrite ENC in LOOKUP.
    inversion INJp as [ | | | ?pp ?bb ?oo ?szz ?lvz bres ores HIN EXTp BNDp USGp REFp | ];
      subst; [ | now specialize (read_null_ptr LOOKUP) ].
    destruct (proj2 (lookup_iff (heap s) p v) LOOKUP) as ( a & REF & _ & SUB ).
    assert (EA: Some a = Some (mkAddr bb oo))
      by (etransitivity; [ symmetry; exact REF | exact REFp ]).
    injection EA as EA; subst a.
    rewrite <- (Nnat.N2Nat.id oo) in SUB.
    destruct (CCInj.mem_contents_of_heap WFINJ SUB) as ( bh & szh & HINh & LOADS ).
    assert (EPAIR: (bh, (szh, true)) = (bres, (szz, lvz)))
      by exact (ListExt.BindIn_fun _ _ _ _ HIN HINh).
    injection EPAIR as Eb Esz Elv; subst bh szh.
    assert (MCv: CCInj.type_mem_chunk (Value.type_of_value v) = Some mc)
      by (rewrite (Value.Facts.type_of_value_complete WTv); exact MC).
    destruct (LOADS mc MCv) as ( tv & INJ & LOAD ).
    exists tv; split; [ | exact INJ ].
    cbn [Memory.Mem.loadv].
    rewrite USGp, <- N_nat_Z.
    exact LOAD.
  Qed.

  Lemma shift_bw_inj [inj: CCInj.injection Ad] [p p': Pt] [nn: N] [b' o']
    (INJp: CCInj.InjValue inj (v_ptr p) (Values.Vptr b' o'))
    (SHIFT: ptr_shift_bw p nn = Some p')
    : (0 <= CCInj.offset_to_offset (Z.of_N nn) <= Ptrofs.max_unsigned)%Z
      /\ forall d, Ptrofs.unsigned d = CCInj.offset_to_offset (Z.of_N nn) ->
                   CCInj.InjValue inj (v_ptr p') (Values.Vptr b' (Ptrofs.sub o' d)).
  Proof using Type.
    unfold CCInj.offset_to_offset.
    inversion INJp as [ | | | ?pp ?bb ?oo ?szz ?lvz ?bb' ?oo' HIN EXTp BNDp USGp REFp | ];
      subst; try (destruct Archi.ptr64; discriminate).
    unfold CCInj.offset_to_offset in USGp.
    specialize CCInj.Facts.store_memsize_bounded as MSLE.
    specialize memword_bytes_pos as MSPOS.
    specialize (Ptrofs.unsigned_range_2 o') as URANGE.
    rewrite USGp in URANGE.
    destruct (ptr_shift_bw_references _ _ _ SHIFT _ REFp) as ( a' & SHA & REF' ).
    unfold shift_bw in SHA.
    rewrite mkAddr_block, mkAddr_offset in SHA.
    destruct (N.leb_spec nn oo) as [ LE | LT ]; [ | discriminate SHA ].
    injection SHA as EA'; subst a'.
    assert (LEZ: (Z.of_N nn <= Z.of_N oo)%Z) by (apply N2Z.inj_le; exact LE).
    assert (OPOS: (0 <= Z.of_N oo)%Z) by lia.
    assert (NBND: (0 <= Z.of_N nn * Z.of_nat memword_bytes <= Ptrofs.max_unsigned)%Z)
      by nia.
    split; [ exact NBND | ].
    intros d EQd.
    eapply CCInj.inj_ptr with (b := bb) (o := (oo - nn)%N) (sz := szz).
    - exact HIN.
    - intro z; rewrite (ptr_shift_bw_reaches _ _ _ SHIFT (mkAddr bb z)); exact (EXTp z).
    - unfold Intops.Unsigned.Bounded, Intops.Unsigned.min_unsigned in BNDp |- *.
      change (@IntCarrier.to_Z (Intops.Unsigned.carrier n_ofst_t)) with Z.of_N in BNDp |- *.
      rewrite N2Z.inj_sub by exact LE; lia.
    - unfold Ptrofs.sub, CCInj.offset_to_offset.
      rewrite USGp, EQd.
      rewrite N2Z.inj_sub by exact LE.
      rewrite Ptrofs.unsigned_repr; [ ring | split; nia ].
    - exact REF'.
  Qed.

  Lemma shift_fw_inj [s: Sm] [m] [inj: CCInj.injection Ad] [p p': Pt] [nn: N] [b' o']
    (WFINJ: CCInj.wf s m inj)
    (INJp: CCInj.InjValue inj (v_ptr p) (Values.Vptr b' o'))
    (SHIFT: ptr_shift_fw p nn = Some p')
    : (0 <= CCInj.offset_to_offset (Z.of_N nn) <= Ptrofs.max_unsigned)%Z
      /\ forall d, Ptrofs.unsigned d = CCInj.offset_to_offset (Z.of_N nn) ->
                   CCInj.InjValue inj (v_ptr p') (Values.Vptr b' (Ptrofs.add o' d)).
  Proof using Type.
    unfold CCInj.offset_to_offset.
    inversion INJp as [ | | | ?pp ?bb ?oo ?szz ?lvz ?bb' ?oo' HIN EXTp BNDp USGp REFp | ];
      subst; try (destruct Archi.ptr64; discriminate).
    unfold CCInj.offset_to_offset in USGp.
    specialize CCInj.Facts.store_memsize_bounded as MSLE.
    specialize memword_bytes_pos as MSPOS.
    destruct (proj2 (ptr_shift_fw_some p nn) (ex_intro _ p' SHIFT))
      as ( a & REFa & _ & RCHsh ).
    assert (EA: Some a = Some (mkAddr bb oo))
      by (etransitivity; [ symmetry; exact REFa | exact REFp ]).
    injection EA as EA; subst a.
    unfold shift_fw in RCHsh; rewrite mkAddr_block, mkAddr_offset in RCHsh.
    specialize (proj1 (EXTp (oo + nn)%N) RCHsh) as REACH.
    destruct (CCInj.mem_extent_of_heap WFINJ _ _ _ _ HIN) as ( SZBND & _ ).
    unfold CCInj.offset_to_offset in SZBND.
    assert (LEZ: (Z.of_N oo + Z.of_N nn <= Z.of_N szz)%Z)
      by (rewrite <- N2Z.inj_add; apply N2Z.inj_le; exact REACH).
    assert (OPOS: (0 <= Z.of_N oo)%Z) by lia.
    assert (NPOS: (0 <= Z.of_N nn)%Z) by lia.
    assert (NBND: (0 <= Z.of_N nn * Z.of_nat memword_bytes <= Ptrofs.max_unsigned)%Z)
      by nia.
    assert (TOTBND: (0 <= (Z.of_N oo + Z.of_N nn) * Z.of_nat memword_bytes
                     <= Ptrofs.max_unsigned)%Z)
      by nia.
    split; [ exact NBND | ].
    intros d EQd.
    eapply CCInj.inj_ptr with (b := bb) (o := (oo + nn)%N) (sz := szz).
    - exact HIN.
    - intro z; rewrite (ptr_shift_fw_reaches _ _ _ SHIFT (mkAddr bb z)); exact (EXTp z).
    - unfold Intops.Unsigned.Bounded, Intops.Unsigned.min_unsigned.
      change (@IntCarrier.to_Z (Intops.Unsigned.carrier n_ofst_t)) with Z.of_N.
      rewrite (Unsigned.CompCert.Ptrofs.max_unsigned_eq (UInt := n_ofst_t) eq_refl).
      rewrite N2Z.inj_add; nia.
    - unfold Ptrofs.add, CCInj.offset_to_offset.
      rewrite USGp, EQd, N2Z.inj_add.
      rewrite Ptrofs.unsigned_repr; [ ring | split; nia ].
    - specialize (ptr_shift_fw_references _ _ _ SHIFT _ REFp) as REF'.
      unfold shift_fw in REF'; rewrite mkAddr_block, mkAddr_offset in REF'; exact REF'.
  Qed.

  Lemma wf_mutate_heap_unsized
    [inj: CCInj.injection Ad] [s: Sm] [m] [p: Pt] [v: Vl] [hp']
    (WFINJ: CCInj.wf s m inj)
    (MUTATE: mutate (heap s) p v = Some hp')
    (MC: CCInj.type_mem_chunk (Value.type_of_value v) = None)
    : CCInj.wf (State.state_mutate_heap s MUTATE) m inj.
  Proof using Type.
    destruct (proj2 (mutate_some_iff (heap s) p v) (ex_intro _ hp' MUTATE))
      as ( a0 & v0 & REF0 & _ & SUB0 ).
    pose proof (State.store_state_mutate_heap s p v hp' MUTATE) as ESTORE.
    pose proof (State.heap_state_mutate_heap s p v hp' MUTATE) as EHEAP.
    assert (OLD: forall bh oh (w: Vl),
               (((mkAddr bh (N.of_nat oh)) |-> w)%mem
                  $<= State.heap (State.state_mutate_heap s MUTATE))%sep ->
               exists w0, (((mkAddr bh (N.of_nat oh)) |-> w0)%mem
                           $<= State.heap s)%sep).
    { intros bh oh w SUB.
      rewrite EHEAP in SUB.
      destruct (proj1 (mutate_mem_iff (heap s) p v hp' a0 REF0 MUTATE _ w) SUB)
        as [ ( EA & _ ) | ( _ & SUBo ) ].
      - exists v0; rewrite EA; exact SUB0.
      - exists w; exact SUBo. }
    wf_keep_inj WFINJ.
    - intros bh oh w SUB.
      pose proof SUB as SUB'.
      rewrite EHEAP in SUB'.
      destruct (proj1 (mutate_mem_iff (heap s) p v hp' a0 REF0 MUTATE _ w) SUB')
        as [ ( EA & EV ) | ( _ & SUBo ) ].
      + subst w.
        assert (SUBv0: (((mkAddr bh (N.of_nat oh)) |-> v0)%mem
                        $<= State.heap s)%sep)
          by (rewrite EA; exact SUB0).
        destruct (CCInj.mem_contents_of_heap WFINJ SUBv0) as ( bh' & szh & HINh & _ ).
        exists bh', szh; split; [ exact HINh | ].
        intros mcc MCC; rewrite MC in MCC; discriminate MCC.
      + exact (CCInj.mem_contents_of_heap WFINJ SUBo).
    - intros a w SUB.
      rewrite ESTORE in SUB.
      exact (CCInj.mem_contents_of_store WFINJ a w SUB).
    - exact (CCInj.mem_contents_of_fun WFINJ).
    - exact (CCInj.mem_header_of_heap WFINJ).
    - exact (CCInj.mem_extent_of_heap WFINJ).
    - intros bh oh w bh' szh lvh SUB HINh.
      destruct (OLD bh oh w SUB) as ( w0 & SUBo ).
      exact (CCInj.heap_contents_compact WFINJ bh oh w0 bh' szh lvh SUBo HINh).
    - exact (CCInj.mem_perm_of_store WFINJ).
    - intros bh bh' szh lvh bid INh GET.
      rewrite (State.alc_state_mutate_heap s p v hp' MUTATE) in GET.
      exact (CCInj.heap_block_below_alc WFINJ bh bh' szh lvh bid INh GET).
  Qed.

  Lemma wf_store_heap
    [inj: CCInj.injection Ad] [s: Sm] [m m'] [p: Pt] [b' o'] [v: Vl] [tv mc hp']
    (WFINJ: CCInj.wf s m inj)
    (INJp: CCInj.InjValue inj (Value.v_ptr p) (Values.Vptr b' o'))
    (MUTATE: mutate (heap s) p v = Some hp')
    (INJv: CCInj.InjValue inj v tv)
    (MC: CCInj.type_mem_chunk (Value.type_of_value v) = Some mc)
    (STORE: Memory.Mem.store mc m b' (Ptrofs.unsigned o') tv = Some m')
    : CCInj.wf (State.state_mutate_heap s MUTATE) m' inj.
  Proof using Type.
    inversion INJp as [ | | | ?pp bg og szg lvg ?bb ?oo HIN EXTp BNDp USGp REFp | ];
      subst; try (destruct Archi.ptr64; discriminate).
    destruct (proj2 (mutate_some_iff (heap s) p v) (ex_intro _ hp' MUTATE))
      as ( a0 & v0 & REF0 & _ & SUB0 ).
    assert (EA0: Some a0 = Some (mkAddr bg og))
      by (etransitivity; [ symmetry; exact REF0 | exact REFp ]).
    injection EA0 as EA0; subst a0.
    assert (SUB0': (((mkAddr bg (N.of_nat (N.to_nat og))) |-> v0)%mem
                     $<= State.heap s)%sep)
      by (rewrite Nnat.N2Nat.id; exact SUB0).
    assert (LIVE: lvg = true).
    { destruct (CCInj.mem_contents_of_heap WFINJ SUB0')
        as ( bb0 & sz0 & HIN0 & _ ).
      injection (ListExt.BindIn_fun _ _ _ _ HIN HIN0) as E1 E2 E3.
      exact (eq_sym E3). }
    subst lvg.
    pose proof (State.store_state_mutate_heap s p v hp' MUTATE) as ESTORE.
    pose proof (State.heap_state_mutate_heap s p v hp' MUTATE) as EHEAP.
    assert (NEst: forall a bs os fr,
               In (a, (bs, os, fr)) inj.(CCInj.inj_st_map) -> bs <> b').
    { intros a bs os fr IN.
      exact (not_eq_sym (CCInj.heap_store_distinct WFINJ bg b' szg true a bs os fr
                           (ListExt.BindIn_In HIN) IN)). }
    assert (NEfn: forall id bf, In (id, bf) inj.(CCInj.inj_fn_map) -> bf <> b').
    { intros id bf IN.
      exact (not_eq_sym (CCInj.heap_fun_distinct WFINJ bg b' szg true id bf
                           (ListExt.BindIn_In HIN) IN)). }
    assert (NEhp: forall bh bh' szh lvh,
               ListExt.BindIn bh (bh', (szh, lvh)) inj.(CCInj.inj_hp_map) ->
               bh <> bg -> bh' <> b').
    { intros bh bh' szh lvh HINh NEh EQ; subst bh'.
      exact (NEh (CCInj.Facts.heap_block_inj WFINJ (ListExt.BindIn_In HINh) (ListExt.BindIn_In HIN))). }
    assert (OLD: forall bh oh (w: Vl),
               (((mkAddr bh (N.of_nat oh)) |-> w)%mem
                  $<= State.heap (State.state_mutate_heap s MUTATE))%sep ->
               exists w0, (((mkAddr bh (N.of_nat oh)) |-> w0)%mem
                           $<= State.heap s)%sep).
    { intros bh oh w SUB.
      rewrite EHEAP in SUB.
      destruct (proj1 (mutate_mem_iff (heap s) p v hp' (mkAddr bg og) REF0 MUTATE _ w)
                  SUB)
        as [ ( EA & _ ) | ( _ & SUBo ) ].
      - exists v0; rewrite EA; exact SUB0.
      - exists w; exact SUBo. }
    assert (DHDR: (- Memdata.size_chunk AST.Mptr + Memdata.size_chunk AST.Mptr
                   <= Ptrofs.unsigned o')%Z)
      by (specialize (Ptrofs.unsigned_range o') as R; lia).
    wf_keep_inj WFINJ.
    - intros bh oh w SUB.
      pose proof SUB as SUB'.
      rewrite EHEAP in SUB'.
      destruct (proj1 (mutate_mem_iff (heap s) p v hp' (mkAddr bg og) REF0 MUTATE _ w)
                  SUB')
        as [ ( EA & EV ) | ( NEA & SUBo ) ].
      + subst w.
        destruct (mkAddr_inj _ _ _ _ EA) as ( EB & EO ); subst bh.
        assert (EOH: Ptrofs.unsigned o' = CCInj.offset_to_offset (Z.of_nat oh))
          by (rewrite USGp, <- EO, nat_N_Z; reflexivity).
        exists b', szg; split; [ exact HIN | ].
        intros mcc MCC.
        assert (Emc: mcc = mc) by congruence; subst mcc.
        exists tv; split; [ exact INJv | ].
        rewrite <- EOH, (Memory.Mem.load_store_same _ _ _ _ _ _ STORE).
        rewrite (CCInj.Facts.InjValue_load_result INJv MC); reflexivity.
      + destruct (CCInj.mem_contents_of_heap WFINJ SUBo)
          as ( bh' & szh & HINh & LOADS ).
        exists bh', szh; split; [ exact HINh | ].
        intros mcc MCC.
        destruct (LOADS mcc MCC) as ( w' & INJ & LOAD ).
        exists w'; split; [ exact INJ | ].
        assert (DZ: bh' <> b'
                    \/ (CCInj.offset_to_offset (Z.of_nat oh)
                        + Memdata.size_chunk mcc <= Ptrofs.unsigned o')%Z
                    \/ (Ptrofs.unsigned o' + Memdata.size_chunk mc
                        <= CCInj.offset_to_offset (Z.of_nat oh))%Z).
        { destruct (Nat.eq_dec bh bg) as [ EB | NEB ];
            [ | now left; exact (NEhp bh bh' szh true HINh NEB) ].
          subst bh.
          assert (EBB: bh' = b')
            by (injection (ListExt.BindIn_fun _ _ _ _ HIN HINh) as E1 E2;
                exact E1).
          subst bh'.
          assert (NEO: oh <> N.to_nat og).
          { intro EO; apply NEA; rewrite EO, Nnat.N2Nat.id; reflexivity. }
          specialize (memword_bytes_size_chunk MCC) as SZ1.
          specialize (memword_bytes_size_chunk MC) as SZ2.
          destruct (offset_to_offset_dsj NEO) as [ LE | LE ];
            rewrite USGp, <- N_nat_Z; [ right; left | right; right ]; lia. }
        rewrite (Memory.Mem.load_store_other _ _ _ _ _ _ STORE mcc bh'
                   (CCInj.offset_to_offset (Z.of_nat oh)) DZ).
        exact LOAD.
    - intros a w SUB.
      rewrite ESTORE in SUB.
      destruct (CCInj.mem_contents_of_store WFINJ a w SUB)
        as ( bs & os & fr & IN & LOADS ).
      exists bs, os, fr; split; [ exact IN | ].
      intros mcc MCC.
      destruct (LOADS mcc MCC) as ( w' & INJ & LOAD ).
      exists w'; split; [ exact INJ | ].
      rewrite (Memory.Mem.load_store_other _ _ _ _ _ _ STORE mcc bs
                 (CCInj.offset_to_offset (Z.of_nat os))
                 (or_introl (NEst a bs os fr IN))).
      exact LOAD.
    - intros id bf IN.
      destruct (CCInj.mem_contents_of_fun WFINJ id bf IN) as ( CONT & ACC ).
      split.
      + rewrite (Memory.Mem.store_mem_contents _ _ _ _ _ _ STORE).
        rewrite Maps.PMap.gso by exact (NEfn id bf IN).
        exact CONT.
      + rewrite (Memory.Mem.store_access _ _ _ _ _ _ STORE); exact ACC.
    - intros bh bh' szh HINh.
      rewrite (Memory.Mem.load_store_other _ _ _ _ _ _ STORE AST.Mptr bh'
                 (- Memdata.size_chunk AST.Mptr)%Z (or_intror (or_introl DHDR))).
      exact (CCInj.mem_header_of_heap WFINJ bh bh' szh HINh).
    - intros bh bh' szh lvh HINh.
      destruct (CCInj.mem_extent_of_heap WFINJ bh bh' szh lvh HINh)
        as ( BND & VB & RP ).
      split; [ exact BND | split ].
      + exact (Memory.Mem.store_valid_block_1 _ _ _ _ _ _ STORE _ VB).
      + intros ELV ofs RNG.
        eapply Memory.Mem.perm_store_1; [ exact STORE | exact (RP ELV ofs RNG) ].
    - intros bh oh w bh' szh lvh SUB HINh.
      destruct (OLD bh oh w SUB) as ( w0 & SUBo ).
      exact (CCInj.heap_contents_compact WFINJ bh oh w0 bh' szh lvh SUBo HINh).
    - intros a bs os fr IN ofs RNG.
      eapply Memory.Mem.perm_store_1; [ exact STORE | ].
      exact (CCInj.mem_perm_of_store WFINJ a bs os fr IN ofs RNG).
    - intros bh bh' szh lvh bid INh GET.
      rewrite (State.alc_state_mutate_heap s p v hp' MUTATE) in GET.
      exact (CCInj.heap_block_below_alc WFINJ bh bh' szh lvh bid INh GET).
  Qed.

  Lemma store_heap_progress
    [inj: CCInj.injection Ad] [s: Sm] [m] [p: Pt] [b' o'] [v: Vl] [tv mc hp']
    (WFINJ: CCInj.wf s m inj)
    (INJp: CCInj.InjValue inj (Value.v_ptr p) (Values.Vptr b' o'))
    (MUTATE: mutate (heap s) p v = Some hp')
    (MC: CCInj.type_mem_chunk (Value.type_of_value v) = Some mc)
    : exists m', Memory.Mem.store mc m b' (Ptrofs.unsigned o') tv = Some m'.
  Proof using Type.
    inversion INJp as [ | | | ?pp bg og szg lvg ?bb ?oo HIN EXTp BNDp USGp REFp | ];
      subst; try (destruct Archi.ptr64; discriminate).
    destruct (proj2 (mutate_some_iff (heap s) p v) (ex_intro _ hp' MUTATE))
      as ( a0 & v0 & REF0 & _ & SUB0 ).
    assert (EA0: Some a0 = Some (mkAddr bg og))
      by (etransitivity; [ symmetry; exact REF0 | exact REFp ]).
    injection EA0 as EA0; subst a0.
    assert (SUBo: (((mkAddr bg (N.of_nat (N.to_nat og))) |-> v0)%mem
                   $<= State.heap s)%sep)
      by (rewrite Nnat.N2Nat.id; exact SUB0).
    specialize (CCInj.Facts.heap_cell_perm WFINJ SUBo HIN)
      as RP.
    rewrite N_nat_Z in RP.
    specialize (memword_bytes_size_chunk MC) as SZ.
    assert (VA: Memory.Mem.valid_access m mc b' (Ptrofs.unsigned o') Memtype.Writable).
    { split.
      - intros ofs RNG.
        apply (Memory.Mem.perm_implies _ _ _ _ Memtype.Freeable);
          [ | constructor ].
        apply RP.
        rewrite USGp in RNG; lia.
      - rewrite USGp.
        exact (offset_to_offset_align MC _). }
    destruct (Memory.Mem.valid_access_store m mc b' (Ptrofs.unsigned o') tv VA)
      as ( m' & EQ ).
    exists m'; exact EQ.
  Qed.

  Lemma write_ptr_store [inj: CCInj.injection Ad] [s: Sm] [m] [p: Pt] [tvp]
    [v: Vl] [t mc tv] [hp']
    (WFINJ: CCInj.wf s m inj)
    (INJp: CCInj.InjValue inj (Value.v_ptr p) tvp)
    (MUTATE: mutate (heap s) p v = Some hp')
    (INJv: CCInj.InjValue inj v tv)
    (WTv: Value.wt_value v t)
    (MC: CCInj.type_mem_chunk t = Some mc)
    : exists m',
        Memory.Mem.storev mc m tvp tv = Some m'
        /\ CCInj.wf (State.state_mutate_heap s MUTATE) m' inj.
  Proof using Type.
    assert (MCv: CCInj.type_mem_chunk (Value.type_of_value v) = Some mc)
      by (rewrite (Value.Facts.type_of_value_complete WTv); exact MC).
    inversion INJp as [ | | | ?pp ?bg ?og ?szg ?lvg ?bres ?ores HIN EXTp BNDp USGp REFp | ];
      subst; [ | now specialize (mutate_null_heap MUTATE) ].
    destruct (store_heap_progress (tv := tv) WFINJ INJp MUTATE MCv) as ( m' & STORE ).
    exists m'; split.
    - cbn [Memory.Mem.storev]; exact STORE.
    - exact (wf_store_heap WFINJ INJp MUTATE INJv MCv STORE).
  Qed.

  Lemma valid_pointer_of_cell [inj: CCInj.injection Ad] [s: Sm] [m]
    [bg: nat] [og: N] [w: Vl] [b' sz live] [z]
    (WFINJ: CCInj.wf s m inj)
    (SUB: (((mkAddr bg og) |-> w)%mem $<= State.heap s)%sep)
    (HIN: ListExt.BindIn bg (b', (sz, live)) inj.(CCInj.inj_hp_map))
    (LO: (CCInj.offset_to_offset (Z.of_N og) <= z)%Z)
    (HI: (z < CCInj.offset_to_offset (Z.of_N og)
              + Z.of_nat memword_bytes)%Z)
    : Memory.Mem.valid_pointer m b' z = true.
  Proof using Type.
    assert (SUB': (((mkAddr bg (N.of_nat (N.to_nat og))) |-> w)%mem
                   $<= State.heap s)%sep)
      by (rewrite Nnat.N2Nat.id; exact SUB).
    specialize (CCInj.Facts.heap_cell_perm WFINJ SUB' HIN z)
      as PERM.
    apply Memory.Mem.valid_pointer_nonempty_perm.
    apply (Memory.Mem.perm_implies _ _ _ _ Memtype.Freeable); [ | constructor ].
    apply PERM.
    rewrite N_nat_Z.
    lia.
  Qed.

  Lemma valid_pointer_of_valid [inj: CCInj.injection Ad] [s: Sm] [m] [p: Pt] [b' o']
    (WFINJ: CCInj.wf s m inj)
    (INJp: CCInj.InjValue inj (Value.v_ptr p) (Values.Vptr b' o'))
    (VAL: Valid (heap s) p)
    : Memory.Mem.valid_pointer m b' (Ptrofs.unsigned o') = true.
  Proof using Type.
    specialize memword_bytes_pos as MSPOS.
    inversion INJp as [ | | | ?pp bg og szg lvg ?bb ?oo HIN EXTp BNDp USGp REFp | ];
      subst; try (destruct Archi.ptr64; discriminate).
    destruct VAL as ( a & w & REF & SUB ).
    assert (EA: Some a = Some (mkAddr bg og))
      by (etransitivity; [ symmetry; exact REF | exact REFp ]).
    injection EA as EA; subst a.
    apply (valid_pointer_of_cell WFINJ SUB HIN);
      rewrite USGp; unfold CCInj.offset_to_offset; lia.
  Qed.

  Lemma weak_valid_pointer_of_wvalid [inj: CCInj.injection Ad] [s: Sm] [m]
    [p: Pt] [b' o']
    (WFINJ: CCInj.wf s m inj)
    (INJp: CCInj.InjValue inj (Value.v_ptr p) (Values.Vptr b' o'))
    (WVAL: WValid (heap s) p)
    : (Memory.Mem.valid_pointer m b' (Ptrofs.unsigned o')
       || Memory.Mem.valid_pointer m b' (Ptrofs.unsigned o' - 1))%bool = true.
  Proof using Type.
    specialize memword_bytes_pos as MSPOS.
    destruct WVAL as [ VAL | [ POVAL | ISNULL ] ].
    - rewrite (valid_pointer_of_valid WFINJ INJp VAL); reflexivity.
    - inversion INJp as [ | | | ?pp bg og szg lvg ?bb ?oo HIN EXTp BNDp USGp REFp | ];
        subst; try (destruct Archi.ptr64; discriminate).
      destruct POVAL as ( a & a' & w & REF & SH & SUB ).
      assert (EA: Some a' = Some (mkAddr bg og))
        by (etransitivity; [ symmetry; exact REF | exact REFp ]).
      injection EA as EA; subst a'.
      unfold Shift, shift_fw in SH.
      destruct (mkAddr_inj _ _ _ _ SH) as ( EB & EO ).
      assert (EAa: mkAddr bg (og - 1)%N = a).
      { rewrite <- EB.
        replace (og - 1)%N with (offset a) by lia.
        exact (mkAddr_ext a). }
      subst a.
      rewrite (valid_pointer_of_cell (z := (Ptrofs.unsigned o' - 1)%Z)
                 WFINJ SUB HIN);
        [ apply Bool.orb_true_r
        | rewrite USGp; unfold CCInj.offset_to_offset;
          rewrite N2Z.inj_sub by lia; nia ..].
    - inversion INJp as [ | | | ?pp bg og szg lvg ?bb ?oo HIN EXTp BNDp USGp REFp | ];
        subst; try (destruct Archi.ptr64; discriminate).
      exfalso.
      assert (NONE: @Some Ad (mkAddr bg og) = None)
        by (etransitivity;
            [ symmetry; exact REFp | exact (proj2 (null_addr (null: Pt)) eq_refl) ]).
      discriminate NONE.
  Qed.

  Lemma eval_binop_of_cmp_bool m v1 v2 b
    (CB: (if Archi.ptr64
          then Values.Val.cmplu_bool (Memory.Mem.valid_pointer m) Ceq v1 v2
          else Values.Val.cmpu_bool (Memory.Mem.valid_pointer m) Ceq v1 v2) = Some b)
    : Cminor.eval_binop (if Archi.ptr64 then Cminor.Ocmplu Ceq else Cminor.Ocmpu Ceq) v1 v2 m
      = Some (Values.Val.of_bool b).
  Proof using Type.
    destruct Archi.ptr64; cbn [Cminor.eval_binop];
      [ unfold Values.Val.cmplu | unfold Values.Val.cmpu ]; rewrite CB; reflexivity.
  Qed.

  Lemma cmp_bool_inj [inj: CCInj.injection Ad] [s: Sm] [m] [pl pr: Pt] [tvl tvr]
    (WFINJ: CCInj.wf s m inj)
    (INJl: CCInj.InjValue inj (Value.v_ptr pl) tvl)
    (INJr: CCInj.InjValue inj (Value.v_ptr pr) tvr)
    (CMPVALID: CmpValid (heap s) pl pr)
    : (if Archi.ptr64
       then Values.Val.cmplu_bool (Memory.Mem.valid_pointer m) Ceq tvl tvr
       else Values.Val.cmpu_bool (Memory.Mem.valid_pointer m) Ceq tvl tvr)
      = Some (ptr_addr_eqb pl pr).
  Proof using Type.
    destruct CMPVALID as ( WVl & WVr & CROSS ).
    assert (ERA: ref_addr (null: Pt) = None) by exact (proj2 (null_addr (null: Pt)) eq_refl).
    inversion INJl as [ | | | ?ppl bl ofstl szl lvl b1 o1 HINl EXTl BNDl USGl REFl | ]; subst;
      [ specialize (weak_valid_pointer_of_wvalid WFINJ INJl WVl) as WVPl | ];
      inversion INJr as [ | | | ?ppr br ofstr szr lvr b2 o2 HINr EXTr BNDr USGr REFr | ]; subst;
      try (specialize (weak_valid_pointer_of_wvalid WFINJ INJr WVr) as WVPr).
    - rewrite (ptr_addr_eqb_mkAddr REFl REFr).
      destruct (Nat.eqb_spec bl br) as [ <- | NEB ].
      + destruct (proj2 (CCInj.Facts.inj_block_eq WFINJ HINl HINr) eq_refl); cbn [andb].
        destruct Archi.ptr64 eqn:ARCHI;
          [ unfold Values.Val.cmplu_bool | unfold Values.Val.cmpu_bool ];
          rewrite ARCHI; cbn [negb]; rewrite WVPl, WVPr;
          (destruct (Values.eq_block b1 b1) as [ _ | NEBB ]; [ | exfalso; exact (NEBB eq_refl) ]);
          unfold Ptrofs.cmpu; rewrite (CCInj.Ptrofs_eq_of_offsets USGl USGr); reflexivity.
      + assert (NEB': b1 <> b2)
          by (intro E; exact (NEB (proj1 (CCInj.Facts.inj_block_eq WFINJ HINl HINr) E))).
        assert (NEBLK: block (mkAddr (s := Ad) bl ofstl) <> block (mkAddr (s := Ad) br ofstr))
          by (rewrite !mkAddr_block; exact NEB).
        destruct (CROSS _ _ REFl REFr NEBLK) as ( VALl & VALr ).
        specialize (valid_pointer_of_valid WFINJ INJl VALl) as VPl.
        specialize (valid_pointer_of_valid WFINJ INJr VALr) as VPr.
        destruct Archi.ptr64 eqn:ARCHI;
          [ unfold Values.Val.cmplu_bool | unfold Values.Val.cmpu_bool ];
          rewrite ARCHI; cbn [negb];
          (destruct (Values.eq_block b1 b2) as [ EBB | _ ]; [ exfalso; exact (NEB' EBB) | ]);
          rewrite VPl, VPr; reflexivity.
    - unfold ptr_addr_eqb; rewrite REFl, ERA; unfold Values.Vnullptr.
      destruct Archi.ptr64 eqn:ARCHI;
        [ unfold Values.Val.cmplu_bool | unfold Values.Val.cmpu_bool ];
        rewrite ARCHI; cbn [negb]; rewrite WVPl;
        [ rewrite Int64.eq_true | rewrite Int.eq_true ]; reflexivity.
    - unfold ptr_addr_eqb; rewrite REFr, ERA; unfold Values.Vnullptr.
      destruct Archi.ptr64 eqn:ARCHI;
        [ unfold Values.Val.cmplu_bool | unfold Values.Val.cmpu_bool ];
        rewrite ARCHI; cbn [negb]; rewrite WVPr;
        [ rewrite Int64.eq_true | rewrite Int.eq_true ]; reflexivity.
    - unfold ptr_addr_eqb; rewrite ERA; unfold Values.Vnullptr.
      destruct Archi.ptr64 eqn:ARCHI;
        [ unfold Values.Val.cmplu_bool | unfold Values.Val.cmpu_bool ];
        [ rewrite Int64.eq_true | rewrite Int.eq_true ]; reflexivity.
  Qed.

  Lemma ptr_eq_inj [inj: CCInj.injection Ad] [s: Sm] [m] [pl pr: Pt] [tvl tvr] [bres]
    (WFINJ: CCInj.wf s m inj)
    (INJl: CCInj.InjValue inj (Value.v_ptr pl) tvl)
    (INJr: CCInj.InjValue inj (Value.v_ptr pr) tvr)
    (CMPVALID: CmpValid (heap s) pl pr)
    (CMP: cmp pl pr = Some bres)
    : exists tv,
        Cminor.eval_binop
          (if Archi.ptr64 then Cminor.Ocmplu Ceq else Cminor.Ocmpu Ceq) tvl tvr m
        = Some tv
        /\ CCInj.InjValue inj (Value.v_bool (Pt := Pt) bres) tv.
  Proof using Type.
    assert (Ebres: bres = ptr_addr_eqb pl pr).
    { unfold cmp in CMP; destruct (allows pl Operation.Cmp && allows pr Operation.Cmp)%bool;
        [ injection CMP as CMP; symmetry; exact CMP | discriminate CMP ]. }
    subst bres.
    exists (Values.Val.of_bool (ptr_addr_eqb pl pr)); split.
    - exact (eval_binop_of_cmp_bool _ _ _ _ (cmp_bool_inj WFINJ INJl INJr CMPVALID)).
    - destruct (ptr_addr_eqb pl pr); constructor.
  Qed.

  Lemma eval_make_ptr_eq [tge] [sp2] [te] [m el er tvl tvr tv]
    (EVl: Cminor.eval_expr tge sp2 te m el tvl)
    (EVr: Cminor.eval_expr tge sp2 te m er tvr)
    (EVBIN: Cminor.eval_binop
              (if Archi.ptr64 then Cminor.Ocmplu Ceq else Cminor.Ocmpu Ceq) tvl tvr m
            = Some tv)
    : Cminor.eval_expr tge sp2 te m (make_ptr_eq el er) tv.
  Proof using Type.
    unfold make_ptr_eq.
    revert EVBIN; destruct Archi.ptr64; intro EVBIN;
      eapply Cminor.eval_Ebinop; eassumption.
  Qed.


  Lemma free_ptr_live_row [inj: CCInj.injection Ad] [s: Sm] [m] [p: Pt] [hp'] [b' o']
    (WFINJ: CCInj.wf s m inj)
    (INJp: CCInj.InjValue inj (Value.v_ptr p) (Values.Vptr b' o'))
    (FREE_GC: free (heap s) p = Some hp')
    : exists bg sz,
        Extent p bg sz
        /\ Ptrofs.unsigned o' = 0%Z
        /\ ListExt.BindIn bg (b', (sz, true)) inj.(CCInj.inj_hp_map).
  Proof using Type.
    destruct (proj2 (free_some (heap s) p)
                (ex_intro _ hp' FREE_GC)) as ( AF & CELLS ).
    inversion INJp as [ | | | ?pp bg og szg lvg ?bb ?oo HIN EXTp BNDp USGp REFp | ];
      subst; try (destruct Archi.ptr64; discriminate).
    assert (EOG: og = 0%N).
    { specialize (Extent_free_offset p bg szg _ EXTp AF REFp) as EO.
      rewrite mkAddr_offset in EO; exact EO. }
    subst og.
    specialize (Extent_free_pos p bg szg EXTp AF) as SZPOS.
    assert (R0: Reaches p (mkAddr bg 0%N)) by (apply (proj2 (EXTp 0%N)); lia).
    assert (R1: Reaches p (shift_fw (mkAddr bg 0%N) 1%N)).
    { unfold shift_fw; rewrite mkAddr_block, mkAddr_offset.
      apply (proj2 (EXTp (0 + 1)%N)); lia. }
    destruct (CELLS (mkAddr bg 0%N) R0 R1) as ( w & SUB ).
    assert (SUB0: ((((mkAddr bg (N.of_nat 0)) |-> w)%mem) $<= State.heap s)%sep)
      by exact SUB.
    destruct (CCInj.mem_contents_of_heap WFINJ SUB0) as ( bb0 & sz0 & HIN0 & _ ).
    assert (EROW: (bb0, (sz0, true)) = (b', (szg, lvg)))
      by exact (ListExt.BindIn_fun _ _ _ _ HIN HIN0).
    injection EROW as Eb Esz Elv; subst bb0 sz0 lvg.
    exists bg, szg; split; [ exact EXTp | split ].
    - rewrite USGp; unfold CCInj.offset_to_offset; reflexivity.
    - exact HIN.
  Qed.

  Lemma free_ptr_extcall [prog: Prog.program] [tprog] [idf]
    [inj: CCInj.injection Ad] [S: Sm] [m] [p: Pt] [hp0 hp'] [b' o'] [bg sz]
    (TRANSL: match_prog prog tprog)
    (DECLf: exf_declared (Prog.program_of_program prog) idf AST.EF_free)
    (WFINJ: CCInj.wf S m inj)
    (EXT: Extent p bg sz)
    (OFS: Ptrofs.unsigned o' = 0%Z)
    (HINlive: ListExt.BindIn bg (b', (sz, true)) inj.(CCInj.inj_hp_map))
    (FREE_GC: free hp0 p = Some hp')
    (EHEAP: State.heap S = hp')
    : exists bfree m' inj',
        Genv.find_symbol (Genv.globalenv tprog) idf = Some bfree
        /\ Genv.find_funct (Genv.globalenv tprog) (Values.Vptr bfree Ptrofs.zero)
           = Some (AST.External AST.EF_free)
        /\ Events.external_call AST.EF_free (Genv.globalenv tprog)
             [Values.Vptr b' o'] m Events.E0 Values.Vundef m'
        /\ CCInj.inj_hp_le inj inj'
        /\ inj'.(CCInj.inj_st_map) = inj.(CCInj.inj_st_map)
        /\ CCInj.wf S m' inj'.
  Proof using Type.
    assert (NOCELL: forall o (w: Vl),
               ~ ((((mkAddr bg (N.of_nat o)) |-> w)%mem) $<= State.heap S)%sep).
    { intros o w SUB.
      specialize (CCInj.heap_contents_compact WFINJ bg o w b' sz true SUB HINlive) as LT.
      rewrite EHEAP in SUB.
      destruct (free_interval hp0 hp' p bg sz FREE_GC EXT) as ( NOC & _ ).
      exact (NOC (N.of_nat o) LT (ex_intro _ w SUB)). }
    destruct (wf_free_heap WFINJ HINlive NOCELL) as ( m' & FREE & WF' ).
    destruct (exf_declared_symbol (exf_declared_match TRANSL DECLf))
      as ( bfree & SYMB & FUNCT ).
    specialize (CCInj.mem_extent_of_heap WFINJ bg b' sz true HINlive)
      as ( BND & _ & _ ).
    assert (SZNN: (0 <= CCInj.offset_to_offset (Z.of_N sz))%Z).
    { unfold CCInj.offset_to_offset; specialize (N2Z.is_nonneg sz) as P; nia. }
    assert (EUNS: Ptrofs.unsigned (Ptrofs.repr (CCInj.offset_to_offset (Z.of_N sz)))
                  = CCInj.offset_to_offset (Z.of_N sz))
      by (apply Ptrofs.unsigned_repr; split; [ exact SZNN | exact BND ]).
    exists bfree, m',
      (CCInj.Build_injection Ad (CCInj.heap_map_free bg inj.(CCInj.inj_hp_map))
         inj.(CCInj.inj_st_map) inj.(CCInj.inj_fn_map)).
    split; [ exact SYMB | split; [ exact FUNCT | split; [ | split; [ | split ] ] ] ].
    - cbn [Events.external_call].
      apply Events.extcall_free_sem_ptr
        with (sz := Ptrofs.repr (CCInj.offset_to_offset (Z.of_N sz))).
      + rewrite OFS.
        replace (0 - Memdata.size_chunk AST.Mptr)%Z
          with (- Memdata.size_chunk AST.Mptr)%Z by lia.
        exact (CCInj.mem_header_of_heap WFINJ bg b' sz HINlive).
      + rewrite OFS, EUNS.
        replace (0 - Memdata.size_chunk AST.Mptr)%Z
          with (- Memdata.size_chunk AST.Mptr)%Z by lia.
        replace (0 + CCInj.offset_to_offset (Z.of_N sz))%Z
          with (CCInj.offset_to_offset (Z.of_N sz))%Z by lia.
        exact FREE.
    - exact (CCInj.inj_hp_le_free bg).
    - reflexivity.
    - exact WF'.
  Qed.

  Lemma kbind_next_state_match_parts
    [prog] [inj: CCInj.injection Ad] [idm idf f b_id c_next k0 tk0]
    [e: @Semantics.env Sm] [locals] [s2 m2 sp ctx ty base] [v: Vl] [tv optid te]
    (WTCONT: Semantics.wt_cont ctx (Semantics.Kbind b_id c_next k0) ty)
    (WTFN: wt_function (Ctxt.to_glob_ctxt ctx) f)
    (WTENV: Semantics.wt_env f ctx.(Ctxt.ctxt_pure) e)
    (FINT: function_internals ctx f)
    (WFINJ: CCInj.wf s2 m2 inj)
    (DECLm: exf_declared (Prog.program_of_program prog) idm AST.EF_malloc)
    (DECLf: exf_declared (Prog.program_of_program prog) idf AST.EF_free)
    (STACKBL: match_stack_block prog inj idm idf f e locals (store s2) sp base te k0 tk0)
    (MCTXT: match_ctxt ctx (Genv.globalenv (Prog.program_of_program prog)))
    (WTv: Value.wt_value v ty)
    (INJ: CCInj.InjValue inj v tv \/ v = Value.v_tt)
    (OI: match ty with
         | Types.t_unit => optid = None
         | _ => optid = Some b_id
         end)
    : match_states prog
        (Semantics.State f c_next k0 (Maps.PTree.set b_id v e) locals s2)
        (Cminor.State
           (Cminorgen.transl_funbody idm idf f)
           (transl_cmd idm idf (Semantics.cont_target k0) c_next)
           tk0 (Values.Vptr sp Ptrofs.zero) (Cminor.set_optvar optid tv te) m2).
  Proof using Type.
    inversion WTCONT as [ ?ctx ?id ?c' ?k' ?t_b ?t_c ?b BINDABLE WTCMD WTk | | | ?ctx ?k' ?tret WTKCALL ];
      subst; [ | now inversion WTKCALL ].
    eapply match_state with (ctx := Ctxt.set_pure b_id (ty, true) ctx) (t := t_c).
    - exact (Lemmas.kbind_next_state_wt WTFN BINDABLE WTCMD WTk WTv WTENV FINT).
    - exact WFINJ.
    - exact {| MSBenv := {| MSBshape := STACKBL;
                           MSBtemps := set_optid_match_temps STACKBL.(MSBtemps) OI INJ WTv |};
               MSBcont := STACKBL.(MSBcont) |}.
    - reflexivity.
    - exact MCTXT.
    - exact DECLm.
    - exact DECLf.
  Qed.

  Lemma kbind_next_state_match
    [prog] [inj: CCInj.injection Ad] [idm idf f b_id c c_next k0 tk0]
    [e: @Semantics.env Sm] [locals] [s s2 m2 sp ctx ty base] [v: Vl] [tv optid te]
    (WT: Semantics.wt_State f c (Semantics.Kbind b_id c_next k0) e locals s ctx ty)
    (WFINJ: CCInj.wf s2 m2 inj)
    (DECLm: exf_declared (Prog.program_of_program prog) idm AST.EF_malloc)
    (DECLf: exf_declared (Prog.program_of_program prog) idf AST.EF_free)
    (STACKBL: match_stack_block prog inj idm idf f e locals (store s2) sp base te k0 tk0)
    (MCTXT: match_ctxt ctx (Genv.globalenv (Prog.program_of_program prog)))
    (WTv: Value.wt_value v ty)
    (INJ: CCInj.InjValue inj v tv \/ v = Value.v_tt)
    (OI: match ty with
         | Types.t_unit => optid = None
         | _ => optid = Some b_id
         end)
    : match_states prog
        (Semantics.State f c_next k0 (Maps.PTree.set b_id v e) locals s2)
        (Cminor.State
           (Cminorgen.transl_funbody idm idf f)
           (transl_cmd idm idf (Semantics.cont_target k0) c_next)
           tk0 (Values.Vptr sp Ptrofs.zero) (Cminor.set_optvar optid tv te) m2).
  Proof using Type.
    destruct WT as [ WTFN WTCMD WTCONT WTENV FINT ].
    exact (kbind_next_state_match_parts WTCONT WTFN WTENV FINT WFINJ DECLm DECLf STACKBL MCTXT WTv INJ OI).
  Qed.


  Lemma call_cont_next_state_match
    [prog] [inj inj': CCInj.injection Ad] [idm idf] [ge] [f c k] [e: @Semantics.env Sm]
    [locals] [s s' s'': Sm] [m' ctx t sp base tk] [v: Vl] [tv] [S2]
    (WTp: wt_program prog)
    (MCTXT: match_ctxt ctx (Globalenvs.Genv.globalenv (Prog.program_of_program prog)))
    (WT: Semantics.wt_State f c k e locals s ctx t)
    (STEP: Semantics.step ge (Semantics.State f c k e locals s) Events.E0 S2)
    (BUILTIN: Semantics.builtin c ge e locals s v s')
    (CONTcall: Semantics.is_call_cont k)
    (STACKBL: match_stack_block_shape inj locals (store s') sp base f.(fn_extra))
    (POP: Semantics.pop_stack f.(fn_extra).(fn_stackspace) s' = Some s'')
    (EHP: CCInj.inj_hp_le inj inj')
    (STNEW: forall (a: Ad) b o fl, In (a, (b, o, fl)) inj'.(CCInj.inj_st_map) ->
              In (a, (b, o, fl)) inj.(CCInj.inj_st_map))
    (STKEEP: CCInj.inj_st_keep base inj inj')
    (WFINJ: CCInj.wf s'' m' inj')
    (MK: match_cont prog inj idm idf base k tk)
    (INJ: CCInj.InjValue inj v tv \/ v = Value.v_tt)
    : match_states prog (Semantics.Returnstate v k s'')
        (Cminor.Returnstate tv (Cminor.call_cont tk) m').
  Proof using Type.
    destruct STACKBL as [ WTSTACK LOCALSSZ LAYERED STACKBLMAP ].
    pose proof (Lemmas.builtin_wt_value WT BUILTIN) as WTv.
    pose proof WT as WTS; destruct WTS as [ WTFN WTCMD WTCONT WTENV FINT ].
    eapply match_returnstate with (idm := idm) (idf := idf).
    - exact (Semantics.wt_Returnstate prog v k s'' t ctx WTp WTv WTCONT MCTXT).
    - exact WFINJ.
    - destruct INJ as [ IV | EV ];
        [ right; exact (InjValue_hp_le EHP IV) | left; exact EV ].
    - rewrite (Lemmas.pop_stack_base LAYERED LOCALSSZ POP).
      refine (match_cont_call_cont CONTcall
                (match_cont_inj_map (st_top := base) EHP _ STKEEP MK
                   (substate_refl base))).
      intros b a o fl _ IN; exact (STNEW a b o fl IN).
  Qed.

  Lemma kloop1_next_state_set
    [prog] [tge: Cminor.genv] [inj: CCInj.injection Ad]
    [idm idf f c_cond id_cond c_body id_body] [k0: @Semantics.cont Sm] [tk0]
    [e: @Semantics.env Sm] [locals] [s m sp ctx te base] [bb: bool] [tv]
    (WTCONT: Semantics.wt_cont ctx
               (Semantics.Kloop1 c_cond id_cond c_body id_body k0) Types.t_bool)
    (WTFN: wt_function (Ctxt.to_glob_ctxt ctx) f)
    (WTENV: Semantics.wt_env f ctx.(Ctxt.ctxt_pure) e)
    (FINT: function_internals ctx f)
    (WFINJ: CCInj.wf s m inj)
    (DECLm: exf_declared (Prog.program_of_program prog) idm AST.EF_malloc)
    (DECLf: exf_declared (Prog.program_of_program prog) idf AST.EF_free)
    (STACKBL: match_stack_block prog inj idm idf f e locals (store s) sp base te k0 tk0)
    (MCTXT: match_ctxt ctx (Genv.globalenv (Prog.program_of_program prog)))
    (INJ: CCInj.InjValue inj (v_bool (Pt := Pt) bb) tv)
    : exists T2,
        Smallstep.plus Cminor.step tge
          (Cminor.State
             (Cminorgen.transl_funbody idm idf f)
             Cminor.Sskip
             (Cminor.Kseq
                (Cminor.Sifthenelse (Cminor.Evar id_cond)
                   (transl_cmd idm idf (Some id_body) c_body)
                   (Cminor.Sexit 0))
                (Cminor.Kseq
                   (Cminor.Sloop
                      (Cminor.Sseq
                         (transl_cmd idm idf (Some id_cond) c_cond)
                         (Cminor.Sifthenelse (Cminor.Evar id_cond)
                            (transl_cmd idm idf (Some id_body) c_body)
                            (Cminor.Sexit 0))))
                   (Cminor.Kblock
                      (Cminor.Kseq (return_or_assign_unsized (Semantics.cont_target k0)) tk0))))
             (Values.Vptr sp Ptrofs.zero) (Maps.PTree.set id_cond tv te) m)
          Events.E0 T2
        /\ match_states prog
             (Semantics.State f
                (if bb then c_body else Cmd.c_ret Expr.e_tt Types.t_unit)
                (if bb then Semantics.Kloop2 c_cond id_cond c_body id_body k0 else k0)
                (Maps.PTree.set id_cond (v_bool bb) e) locals s) T2.
  Proof using Type.
    destruct bb.
    - eexists; split.
      + eapply Smallstep.plus_two;
          [ apply Cminor.step_skip_seq
          | eapply Cminor.step_ifthenelse;
            [ apply Cminor.eval_Evar; apply Maps.PTree.gss
            | exact (InjValue_bool_val INJ) ]
          | reflexivity ].
      + eapply match_state with (ctx := ctx) (t := Types.t_unit).
        * exact (Lemmas.kloop1_next_state_wt (bb := true) WTCONT WTFN WTENV FINT).
        * exact WFINJ.
        * constructor; [ constructor; [ exact STACKBL | ] | apply match_cont_Kloop2; exact STACKBL.(MSBcont) ].
          eapply (set_optid_match_temps (t := Types.t_bool) (optid := Some id_cond));
            [ exact STACKBL.(MSBtemps) | reflexivity | left; exact INJ | exact (Value.wt_v_bool true) ].
        * reflexivity.
        * exact MCTXT.
        * exact DECLm.
        * exact DECLf.
    - eexists; split.
      + eapply Smallstep.plus_star_trans;
          [ eapply Smallstep.plus_two;
            [ apply Cminor.step_skip_seq
            | eapply Cminor.step_ifthenelse;
              [ apply Cminor.eval_Evar; apply Maps.PTree.gss
              | exact (InjValue_bool_val INJ) ]
            | reflexivity ]
          | eapply Smallstep.star_three;
            [ apply Cminor.step_exit_seq
            | apply Cminor.step_exit_block_0
            | apply Cminor.step_skip_seq
            | reflexivity ]
          | reflexivity ].
      + change (return_or_assign_unsized (Semantics.cont_target k0))
          with (transl_cmd idm idf (Semantics.cont_target k0)
                  (Cmd.c_ret Expr.e_tt Types.t_unit)).
        eapply match_state with (ctx := ctx) (t := Types.t_unit).
        * exact (Lemmas.kloop1_next_state_wt (bb := false) WTCONT WTFN WTENV FINT).
        * exact WFINJ.
        * constructor; [ constructor; [ exact STACKBL | ] | exact STACKBL.(MSBcont) ].
          eapply (set_optid_match_temps (t := Types.t_bool) (optid := Some id_cond));
            [ exact STACKBL.(MSBtemps) | reflexivity | left; exact INJ | exact (Value.wt_v_bool false) ].
        * reflexivity.
        * exact MCTXT.
        * exact DECLm.
        * exact DECLf.
  Qed.

  Lemma kloop1_next_state
    [prog] [tge: Cminor.genv] [inj: CCInj.injection Ad]
    [idm idf f c_cond id_cond c_body id_body] [k0: @Semantics.cont Sm] [tk0]
    [e: @Semantics.env Sm] [locals] [s m sp ctx te a base] [bb: bool] [tv]
    (WTCONT: Semantics.wt_cont ctx
               (Semantics.Kloop1 c_cond id_cond c_body id_body k0) Types.t_bool)
    (WTFN: wt_function (Ctxt.to_glob_ctxt ctx) f)
    (WTENV: Semantics.wt_env f ctx.(Ctxt.ctxt_pure) e)
    (FINT: function_internals ctx f)
    (WFINJ: CCInj.wf s m inj)
    (DECLm: exf_declared (Prog.program_of_program prog) idm AST.EF_malloc)
    (DECLf: exf_declared (Prog.program_of_program prog) idf AST.EF_free)
    (STACKBL: match_stack_block prog inj idm idf f e locals (store s) sp base te k0 tk0)
    (MCTXT: match_ctxt ctx (Genv.globalenv (Prog.program_of_program prog)))
    (EVALa: Cminor.eval_expr tge (Values.Vptr sp Ptrofs.zero) te m a tv)
    (INJ: CCInj.InjValue inj (v_bool (Pt := Pt) bb) tv)
    : exists T2,
        Smallstep.plus Cminor.step tge
          (Cminor.State
             (Cminorgen.transl_funbody idm idf f)
             (Cminor.Sassign id_cond a)
             (Cminor.Kseq
                (Cminor.Sifthenelse (Cminor.Evar id_cond)
                   (transl_cmd idm idf (Some id_body) c_body)
                   (Cminor.Sexit 0))
                (Cminor.Kseq
                   (Cminor.Sloop
                      (Cminor.Sseq
                         (transl_cmd idm idf (Some id_cond) c_cond)
                         (Cminor.Sifthenelse (Cminor.Evar id_cond)
                            (transl_cmd idm idf (Some id_body) c_body)
                            (Cminor.Sexit 0))))
                   (Cminor.Kblock
                      (Cminor.Kseq (return_or_assign_unsized (Semantics.cont_target k0)) tk0))))
             (Values.Vptr sp Ptrofs.zero) te m)
          Events.E0 T2
        /\ match_states prog
             (Semantics.State f
                (if bb then c_body else Cmd.c_ret Expr.e_tt Types.t_unit)
                (if bb then Semantics.Kloop2 c_cond id_cond c_body id_body k0 else k0)
                (Maps.PTree.set id_cond (v_bool bb) e) locals s) T2.
  Proof using Type.
    destruct (kloop1_next_state_set (tge := tge) WTCONT WTFN WTENV FINT WFINJ DECLm DECLf STACKBL MCTXT INJ)
      as ( T2 & PLUS & MATCH ).
    exists T2; split; [ | exact MATCH ].
    eapply Smallstep.plus_left;
      [ apply Cminor.step_assign; exact EVALa
      | apply Smallstep.plus_star; exact PLUS
      | reflexivity ].
  Qed.

  Lemma kloop2_next_state
    [prog] [tge: Cminor.genv] [inj: CCInj.injection Ad]
    [idm idf f c_cond id_cond c_body id_body] [k0: @Semantics.cont Sm] [tk0]
    [e: @Semantics.env Sm] [locals] [s m sp ctx te base]
    (WTCONT: Semantics.wt_cont ctx
               (Semantics.Kloop2 c_cond id_cond c_body id_body k0) Types.t_unit)
    (WTFN: wt_function (Ctxt.to_glob_ctxt ctx) f)
    (WTENV: Semantics.wt_env f ctx.(Ctxt.ctxt_pure) e)
    (FINT: function_internals ctx f)
    (WFINJ: CCInj.wf s m inj)
    (DECLm: exf_declared (Prog.program_of_program prog) idm AST.EF_malloc)
    (DECLf: exf_declared (Prog.program_of_program prog) idf AST.EF_free)
    (STACKBL: match_stack_block prog inj idm idf f e locals (store s) sp base te k0 tk0)
    (MCTXT: match_ctxt ctx (Genv.globalenv (Prog.program_of_program prog)))
    : exists T2,
        Smallstep.plus Cminor.step tge
          (Cminor.State
             (Cminorgen.transl_funbody idm idf f)
             Cminor.Sskip
             (Cminor.Kseq
                (Cminor.Sloop
                   (Cminor.Sseq
                      (transl_cmd idm idf (Some id_cond) c_cond)
                      (Cminor.Sifthenelse (Cminor.Evar id_cond)
                         (transl_cmd idm idf (Some id_body) c_body)
                         (Cminor.Sexit 0))))
                (Cminor.Kblock
                   (Cminor.Kseq (return_or_assign_unsized (Semantics.cont_target k0)) tk0)))
             (Values.Vptr sp Ptrofs.zero) te m)
          Events.E0 T2
        /\ match_states prog
             (Semantics.State f c_cond
                (Semantics.Kloop1 c_cond id_cond c_body id_body k0)
                (Maps.PTree.set id_body v_tt e) locals s) T2.
  Proof using Type.
    eexists; split.
    - eapply Smallstep.plus_three;
        [ apply Cminor.step_skip_seq
        | apply Cminor.step_loop
        | apply Cminor.step_seq
        | reflexivity ].
    - eapply match_state with (ctx := ctx) (t := Types.t_bool).
      + exact (Lemmas.kloop2_next_state_wt WTCONT WTFN WTENV FINT).
      + exact WFINJ.
      + constructor; [ constructor; [ exact STACKBL | ] | apply match_cont_Kloop1; exact STACKBL.(MSBcont) ].
        eapply (set_optid_match_temps
                  (t := Types.t_unit) (optid := None) (tv := Values.Vundef));
          [ exact STACKBL.(MSBtemps) | reflexivity | right; reflexivity | exact Value.wt_v_tt ].
      + reflexivity.
      + exact MCTXT.
      + exact DECLm.
      + exact DECLf.
  Qed.

  Definition ofst_val (n: N): Values.val :=
    if Archi.ptr64
    then Values.Vlong (Int64.repr (Z.of_N n))
    else Values.Vint (Int.repr (Z.of_N n)).

  Lemma eval_make_ofst [tge sp te m] (n: N)
    : Cminor.eval_expr tge sp te m (make_ofst n) (ofst_val n).
  Proof using Type.
    unfold make_ofst, ofst_val; destruct Archi.ptr64;
      apply Cminor.eval_Econst; reflexivity.
  Qed.

  Lemma InjValue_ofst_val [inj: CCInj.injection Ad] [n: N] [tv]
    (INJ: CCInj.InjValue inj (Value.v_ofst n: Vl) tv)
    : tv = ofst_val n.
  Proof using Type.
    inversion INJ as [ | | ?n0 ?v0 BND EQ | | ]; subst.
    unfold ofst_val; destruct Archi.ptr64;
      destruct EQ as ( i & EQi & EV ); subst tv;
      [ rewrite <- EQi, Int64.repr_unsigned
      | rewrite <- EQi, Int.repr_unsigned ];
      reflexivity.
  Qed.

  Lemma ofst_val_range [n: N]
    (BND: (CCInj.offset_to_offset (Z.of_N n) <= Ptrofs.max_unsigned)%Z)
    : (0 <= Z.of_N n <= Ptrofs.max_unsigned)%Z.
  Proof using Type.
    specialize memword_bytes_pos as MSPOS.
    specialize (N2Z.is_nonneg n) as NN.
    unfold CCInj.offset_to_offset in BND; nia.
  Qed.

  Lemma eval_ofst_lt [tge sp te m] [l r: Cminor.expr] [a c: N]
    (EVl: Cminor.eval_expr tge sp te m l (ofst_val a))
    (EVr: Cminor.eval_expr tge sp te m r (ofst_val c))
    (BNDa: (0 <= Z.of_N a <= Ptrofs.max_unsigned)%Z)
    (BNDc: (0 <= Z.of_N c <= Ptrofs.max_unsigned)%Z)
    : exists v, Cminor.eval_expr tge sp te m (make_ofst_lt l r) v
                /\ Values.Val.bool_of_val v (a <? c)%N.
  Proof using Type.
    exists (Values.Val.of_bool (a <? c)%N).
    split; [ | exact (CompCertExt.CCMem.bool_of_val_of_bool _) ].
    unfold make_ofst_lt, ofst_val in *.
    destruct (Archi.ptr64) eqn:ARCHI;
      (eapply Cminor.eval_Ebinop; [ exact EVl | exact EVr | ]).
    - specialize (CompCertExt.Ints.Ptrofs.bound_int64 ARCHI BNDa) as Ba.
      specialize (CompCertExt.Ints.Ptrofs.bound_int64 ARCHI BNDc) as Bc.
      replace (Cminor.eval_binop (Cminor.Ocmplu Clt)
                 (Values.Vlong (Int64.repr (Z.of_N a)))
                 (Values.Vlong (Int64.repr (Z.of_N c))) m)
        with (Some (Values.Val.of_bool
                      (Int64.ltu (Int64.repr (Z.of_N a)) (Int64.repr (Z.of_N c)))))
        by reflexivity.
      unfold Int64.ltu.
      rewrite (Int64.unsigned_repr _ Ba), (Int64.unsigned_repr _ Bc).
      destruct (N.ltb_spec a c) as [ LT | GE ];
        [ destruct (Coqlib.zlt (Z.of_N a) (Z.of_N c)) | destruct (Coqlib.zlt (Z.of_N a) (Z.of_N c)) ];
        try reflexivity; lia.
    - specialize (CompCertExt.Ints.Ptrofs.bound_int32 ARCHI BNDa) as Ba.
      specialize (CompCertExt.Ints.Ptrofs.bound_int32 ARCHI BNDc) as Bc.
      replace (Cminor.eval_binop (Cminor.Ocmpu Clt)
                 (Values.Vint (Int.repr (Z.of_N a)))
                 (Values.Vint (Int.repr (Z.of_N c))) m)
        with (Some (Values.Val.of_bool
                      (Int.ltu (Int.repr (Z.of_N a)) (Int.repr (Z.of_N c)))))
        by reflexivity.
      unfold Int.ltu.
      rewrite (Int.unsigned_repr _ Ba), (Int.unsigned_repr _ Bc).
      destruct (N.ltb_spec a c) as [ LT | GE ];
        [ destruct (Coqlib.zlt (Z.of_N a) (Z.of_N c)) | destruct (Coqlib.zlt (Z.of_N a) (Z.of_N c)) ];
        try reflexivity; lia.
  Qed.

  Lemma eval_ofst_succ [tge sp te m] [i: AST.ident] [j: N]
    (GET: Maps.PTree.get i te = Some (ofst_val j))
    : Cminor.eval_expr tge sp te m
        (make_ofst_add (Cminor.Evar i) (make_ofst 1)) (ofst_val (j + 1)).
  Proof using Type.
    assert (EZ: Z.of_N (j + 1) = (Z.of_N j + 1)%Z) by lia.
    unfold make_ofst_add, ofst_add_op, make_ofst, ofst_val in *.
    destruct (Archi.ptr64) eqn:ARCHI;
      (eapply Cminor.eval_Ebinop;
       [ apply Cminor.eval_Evar; eassumption
       | apply Cminor.eval_Econst; reflexivity
       | ]).
    - cbn [Cminor.eval_binop Values.Val.addl].
      rewrite EZ, CompCertExt.Ints.int64_add_repr; reflexivity.
    - cbn [Cminor.eval_binop Values.Val.add].
      rewrite EZ, CompCertExt.Ints.int_add_repr; reflexivity.
  Qed.

  Lemma eval_cell_addr [tge sp te m] [id_ptr id_count: AST.ident]
    [b: Values.block] [j: N]
    (GETp: Maps.PTree.get id_ptr te = Some (Values.Vptr b Ptrofs.zero))
    (GETc: Maps.PTree.get id_count te = Some (ofst_val j))
    (BND: (0 <= CCInj.offset_to_offset (Z.of_N j) <= Ptrofs.max_unsigned)%Z)
    : exists o, Cminor.eval_expr tge sp te m
                  (make_ptr_shift_fw (Cminor.Evar id_ptr) (Cminor.Evar id_count))
                  (Values.Vptr b o)
                /\ Ptrofs.unsigned o = CCInj.offset_to_offset (Z.of_N j).
  Proof using Type.
    unfold make_ptr_shift_fw, ptr_shift_fw_op, ofst_add_op, adjust_offset,
      make_ofst, ofst_val in *.
    destruct (Archi.ptr64) eqn:ARCHI.
    - eexists; split.
      + eapply Cminor.eval_Ebinop;
          [ apply Cminor.eval_Evar; eassumption
          | (eapply Cminor.eval_Ebinop;
             [ apply Cminor.eval_Evar; eassumption | apply Cminor.eval_Econst; reflexivity | reflexivity ])
          | ].
        cbn [Cminor.eval_binop Values.Val.addl Values.Val.mull]; reflexivity.
      + rewrite Ptrofs.add_zero_l.
        exact (ofst_delta_64 ARCHI
                 (Int64.unsigned_repr _ (CompCertExt.Ints.Ptrofs.bound_int64 ARCHI (ofst_val_range (proj2 BND))))
                 BND).
    - eexists; split.
      + eapply Cminor.eval_Ebinop;
          [ apply Cminor.eval_Evar; eassumption
          | (eapply Cminor.eval_Ebinop;
             [ apply Cminor.eval_Evar; eassumption | apply Cminor.eval_Econst; reflexivity | reflexivity ])
          | ].
        cbn [Cminor.eval_binop Values.Val.add Values.Val.mul]; rewrite ARCHI; reflexivity.
      + rewrite Ptrofs.add_zero_l.
        exact (ofst_delta_32 ARCHI
                 (Int.unsigned_repr _ (CompCertExt.Ints.Ptrofs.bound_int32 ARCHI (ofst_val_range (proj2 BND))))
                 BND).
  Qed.

  Lemma match_temps_set_internal [f: function] [id]
    (NOTLOCAL: forall t, ~ In (id, t) (f.(fn_params) ++ f.(fn_temps)))
    [inj: CCInj.injection Ad] [e: @Semantics.env Sm] [te]
    (MT: match_temps f inj e te) [tv]
    : match_temps f inj e (Maps.PTree.set id tv te).
  Proof using Type.
    intros x t v INx GETx.
    destruct (Coqlib.peq x id) as [ -> | NE ];
      [ exact (False_ind _ (NOTLOCAL t INx)) | ].
    destruct (MT x t v INx GETx) as [ -> | ( v' & GETv' & INJ ) ]; [ now left | ].
    right; exists v'; rewrite Maps.PTree.gso by exact NE; now split.
  Qed.

  Definition alloc_loop_body (id_ptr id_count id_init: AST.ident)
    (mc: AST.memory_chunk) (stop: Cminor.expr): Cminor.stmt :=
    Cminor.Sifthenelse
      (make_ofst_lt (Cminor.Evar id_count) stop)
      (Cminor.Sseq
         (Cminor.Sstore mc
            (make_ptr_shift_fw (Cminor.Evar id_ptr) (Cminor.Evar id_count))
            (Cminor.Evar id_init))
         (Cminor.Sassign id_count
            (make_ofst_add (Cminor.Evar id_count) (make_ofst 1))))
      (Cminor.Sexit 0).

  Lemma make_for_ofst_shape (id_ptr id_count id_init: AST.ident)
    (mc: AST.memory_chunk) (stop: Cminor.expr)
    : make_for_ofst id_count (make_ofst 0) (make_ofst 1) stop
        (fun i => store_ptr_stmt
                    (make_ptr_shift_fw (Cminor.Evar id_ptr) i)
                    (Cminor.Evar id_init, mc))
      = Cminor.Sblock
          (Cminor.Sseq
             (Cminor.Sassign id_count (make_ofst 0))
             (Cminor.Sloop (alloc_loop_body id_ptr id_count id_init mc stop))).
  Proof using Type. reflexivity. Qed.

  Lemma alloc_loop_iter
    [tge: Cminor.genv] [tf: Cminor.function] [sp: Values.block]
    [id_ptr id_count id_init: AST.ident] [mc: AST.memory_chunk]
    [bh: Values.block] [stop: Cminor.expr] [tv_init: Values.val]
    [fn: function] [inj: CCInj.injection Ad] [env: @Semantics.env Sm]
    [count: N]
    (NEpc: id_ptr <> id_count) (NEic: id_init <> id_count)
    (NOTLOCAL: forall t, ~ In (id_count, t) (fn.(fn_params) ++ fn.(fn_temps)))
    (BNDc: (CCInj.offset_to_offset (Z.of_N count) <= Ptrofs.max_unsigned)%Z)
    (SZmc: (Memdata.size_chunk mc <= Z.of_nat memword_bytes)%Z)
    (ALmc: (Memdata.align_chunk mc | Z.of_nat memword_bytes)%Z)
    (LRES: Values.Val.load_result mc tv_init = tv_init)
    (EVSTOP: forall te0 mm, match_temps fn inj env te0 ->
                            Cminor.eval_expr tge (Values.Vptr sp Ptrofs.zero) te0 mm
                              stop (ofst_val count))
    (r: nat)
    : forall (j: N) (tk: Cminor.cont) (te: Cminor.env) (mj: Memory.mem)
             (EJ: (N.to_nat j + r)%nat = N.to_nat count)
             (GETp: Maps.PTree.get id_ptr te = Some (Values.Vptr bh Ptrofs.zero))
             (GETi: Maps.PTree.get id_init te = Some tv_init)
             (GETc: Maps.PTree.get id_count te = Some (ofst_val j))
             (MT: match_temps fn inj env te)
             (RP: Memory.Mem.range_perm mj bh 0
                    (CCInj.offset_to_offset (Z.of_N count))
                    Memtype.Cur Memtype.Freeable),
      exists te' mf,
        Smallstep.star Cminor.step tge
          (Cminor.State tf
             (Cminor.Sloop (alloc_loop_body id_ptr id_count id_init mc stop))
             (Cminor.Kblock tk) (Values.Vptr sp Ptrofs.zero) te mj)
          Events.E0
          (Cminor.State tf Cminor.Sskip tk (Values.Vptr sp Ptrofs.zero) te' mf)
        /\ Maps.PTree.get id_ptr te' = Some (Values.Vptr bh Ptrofs.zero)
        /\ match_temps fn inj env te'
        /\ Memory.Mem.mem_access mf = Memory.Mem.mem_access mj
        /\ Memory.Mem.nextblock mf = Memory.Mem.nextblock mj
        /\ (forall mcc b' ofs',
               b' <> bh \/ (ofs' + Memdata.size_chunk mcc
                            <= CCInj.offset_to_offset (Z.of_N j))%Z ->
               Memory.Mem.load mcc mf b' ofs' = Memory.Mem.load mcc mj b' ofs')
        /\ (forall b', b' <> bh ->
               Maps.PMap.get b' (Memory.Mem.mem_contents mf)
               = Maps.PMap.get b' (Memory.Mem.mem_contents mj))
        /\ (forall i: N, (j <= i)%N -> (i < count)%N ->
               Memory.Mem.load mc mf bh (CCInj.offset_to_offset (Z.of_N i))
               = Some tv_init).
  Proof using Type.
    specialize memword_bytes_pos as MSPOS.
    specialize (Memdata.size_chunk_pos mc) as SCPOS.
    induction r as [ | r IH ]; intros j tk te mj EJ GETp GETi GETc MT RP.
    -
      assert (Ejc: j = count)
        by (apply Nnat.N2Nat.inj; lia).
      subst count.
      assert (LTB: (j <? j)%N = false) by (apply N.ltb_irrefl).
      destruct (eval_ofst_lt (a := j) (c := j)
                  (Cminor.eval_Evar tge (Values.Vptr sp Ptrofs.zero) te mj
                     id_count (ofst_val j) GETc)
                  (EVSTOP te mj MT)
                  (ofst_val_range BNDc) (ofst_val_range BNDc))
        as ( vg & EVg & BVg ).
      rewrite LTB in BVg.
      exists te, mj.
      split; [ | split; [ exact GETp | split; [ exact MT | ] ] ].
      + eapply Smallstep.star_step; [ apply Cminor.step_loop | | reflexivity ].
        eapply Smallstep.star_step;
          [ unfold alloc_loop_body; eapply Cminor.step_ifthenelse;
            [ exact EVg | exact BVg ]
          | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_exit_seq | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_exit_block_0 | | reflexivity ].
        apply Smallstep.star_refl.
      + split; [ reflexivity | split; [ reflexivity | ] ].
        split; [ reflexivity | split; [ reflexivity | ] ].
        intros i LEi LTi; lia.
    -
      assert (LTjc: (j < count)%N) by lia.
      assert (LTB: (j <? count)%N = true) by (apply N.ltb_lt; exact LTjc).
      assert (BNDj: (0 <= CCInj.offset_to_offset (Z.of_N j) <= Ptrofs.max_unsigned)%Z).
      { specialize (N2Z.is_nonneg j) as NN.
        unfold CCInj.offset_to_offset in BNDc |- *.
        assert (LEz: (Z.of_N j <= Z.of_N count)%Z) by lia.
        nia. }
      assert (LEj1: (Z.of_N (j + 1) <= Z.of_N count)%Z) by lia.
      destruct (eval_ofst_lt (a := j) (c := count)
                  (Cminor.eval_Evar tge (Values.Vptr sp Ptrofs.zero) te mj
                     id_count (ofst_val j) GETc)
                  (EVSTOP te mj MT)
                  (ofst_val_range (Z.le_trans _ _ _ (offset_to_offset_mono
                                                       (proj1 (N2Z.inj_le _ _) (N.lt_le_incl _ _ LTjc))) BNDc))
                  (ofst_val_range BNDc))
        as ( vg & EVg & BVg ).
      rewrite LTB in BVg.
      destruct (eval_cell_addr (tge := tge) (sp := Values.Vptr sp Ptrofs.zero)
                  (m := mj) GETp GETc BNDj)
        as ( o & EVa & EUo ).
      assert (VA: Memory.Mem.valid_access mj mc bh
                    (CCInj.offset_to_offset (Z.of_N j)) Memtype.Writable).
      { split.
        - intros ofs RNG.
          apply (Memory.Mem.perm_implies _ _ _ _ Memtype.Freeable);
            [ | constructor ].
          apply RP.
          unfold CCInj.offset_to_offset in RNG |- *.
          specialize (N2Z.is_nonneg j) as NN.
          assert (LEz: (Z.of_N j + 1 <= Z.of_N count)%Z) by lia.
          nia.
        - unfold CCInj.offset_to_offset.
          rewrite Z.mul_comm.
          exact (Z.divide_mul_l _ _ _ ALmc). }
      destruct (Memory.Mem.valid_access_store mj mc bh
                  (CCInj.offset_to_offset (Z.of_N j)) tv_init VA)
        as ( m1 & STORE ).
      assert (STOREV: Memory.Mem.storev mc mj (Values.Vptr bh o) tv_init = Some m1)
        by (cbn [Memory.Mem.storev]; rewrite EUo; exact STORE).
      specialize (IH (j + 1)%N tk
                    (Maps.PTree.set id_count (ofst_val (j + 1)) te) m1
                    ltac:(lia)
                    ltac:(rewrite Maps.PTree.gso by exact NEpc; exact GETp)
                    ltac:(rewrite Maps.PTree.gso by exact NEic; exact GETi)
                    ltac:(apply Maps.PTree.gss)
                    (match_temps_set_internal NOTLOCAL MT (tv := ofst_val (j + 1)))
                    ltac:(intros ofs RNG;
                          eapply Memory.Mem.perm_store_1;
                          [ exact STORE | exact (RP ofs RNG) ]))
        as ( te' & mf & STAR & GETp' & MT' & EACC & ENB & LOADO & CONT & CELLS ).
      exists te', mf.
      split.
      + eapply Smallstep.star_step; [ apply Cminor.step_loop | | reflexivity ].
        eapply Smallstep.star_step;
          [ unfold alloc_loop_body; eapply Cminor.step_ifthenelse;
            [ exact EVg | exact BVg ]
          | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_seq | | reflexivity ].
        eapply Smallstep.star_step;
          [ eapply Cminor.step_store;
            [ exact EVa
            | apply Cminor.eval_Evar; exact GETi
            | exact STOREV ]
          | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_skip_seq | | reflexivity ].
        eapply Smallstep.star_step;
          [ apply Cminor.step_assign; exact (eval_ofst_succ GETc) | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_skip_seq | | reflexivity ].
        exact STAR.
      + split; [ exact GETp' | split; [ exact MT' | ] ].
        split; [ rewrite EACC; exact (Memory.Mem.store_access _ _ _ _ _ _ STORE) | ].
        split; [ rewrite ENB; exact (Memory.Mem.nextblock_store _ _ _ _ _ _ STORE) | ].
        assert (LOADj: forall mcc b' ofs',
                   b' <> bh \/ (ofs' + Memdata.size_chunk mcc
                                <= CCInj.offset_to_offset (Z.of_N j))%Z ->
                   Memory.Mem.load mcc mf b' ofs'
                   = Memory.Mem.load mcc mj b' ofs').
        { intros mcc b' ofs' DSJ.
          assert (DSJ1: b' <> bh \/ (ofs' + Memdata.size_chunk mcc
                                      <= CCInj.offset_to_offset (Z.of_N (j + 1)))%Z).
          { destruct DSJ as [ NE | LE ]; [ now left | right ].
            refine (Z.le_trans _ _ _ LE (offset_to_offset_mono _)); lia. }
          rewrite (LOADO mcc b' ofs' DSJ1).
          refine (Memory.Mem.load_store_other _ _ _ _ _ _ STORE mcc b' ofs' _).
          destruct DSJ as [ NE | LE ]; [ now left | right; now left ]. }
        split; [ exact LOADj | ].
        split.
        { intros b' NE.
          rewrite (CONT b' NE).
          rewrite (Memory.Mem.store_mem_contents _ _ _ _ _ _ STORE).
          apply Maps.PMap.gso; exact NE. }
        intros i LEi LTi.
        destruct (N.eq_dec j i) as [ EQ | NE ].
        * subst i.
          assert (DJ: (CCInj.offset_to_offset (Z.of_N j) + Memdata.size_chunk mc
                       <= CCInj.offset_to_offset (Z.of_N (j + 1)))%Z).
          { assert (EZ: Z.of_N (j + 1) = (Z.of_N j + 1)%Z) by lia.
            unfold CCInj.offset_to_offset; rewrite EZ; nia. }
          rewrite (LOADO mc bh (CCInj.offset_to_offset (Z.of_N j)) (or_intror DJ)).
          rewrite (Memory.Mem.load_store_same _ _ _ _ _ _ STORE), LRES; reflexivity.
        * refine (CELLS i _ LTi); lia.
  Qed.

  Lemma alloc_malloc_mem (m: Memory.mem) (sz: N)
    : exists bh m1 m2,
        Memory.Mem.alloc m (- Memdata.size_chunk AST.Mptr)
          (CCInj.offset_to_offset (Z.of_N sz)) = (m1, bh)
        /\ Memory.Mem.store AST.Mptr m1 bh (- Memdata.size_chunk AST.Mptr)
             (Values.Vptrofs (Ptrofs.repr (CCInj.offset_to_offset (Z.of_N sz))))
           = Some m2.
  Proof using Type.
    specialize memword_bytes_pos as MSPOS.
    specialize (N2Z.is_nonneg sz) as SZNN.
    assert (HINN: (0 <= CCInj.offset_to_offset (Z.of_N sz))%Z)
      by (unfold CCInj.offset_to_offset; nia).
    destruct (Memory.Mem.alloc m (- Memdata.size_chunk AST.Mptr)
                (CCInj.offset_to_offset (Z.of_N sz))) as ( m1 & bh ) eqn:CALLOC.
    assert (VA: Memory.Mem.valid_access m1 AST.Mptr bh
                  (- Memdata.size_chunk AST.Mptr)%Z Memtype.Writable).
    { split.
      - intros ofs RNG.
        apply (Memory.Mem.perm_implies _ _ _ _ Memtype.Freeable); [ | constructor ].
        refine (Memory.Mem.perm_alloc_2 _ _ _ _ _ CALLOC ofs _ _); lia.
      - exact CompCertExt.CCMem.mptr_align_neg. }
    destruct (Memory.Mem.valid_access_store m1 AST.Mptr bh
                (- Memdata.size_chunk AST.Mptr)%Z
                (Values.Vptrofs (Ptrofs.repr (CCInj.offset_to_offset (Z.of_N sz)))) VA)
      as ( m2 & CSTORE ).
    exists bh, m1, m2; split; [ reflexivity | exact CSTORE ].
  Qed.

  Lemma wf_alloc_ptr
    [inj: CCInj.injection Ad] [s: Sm] [m m1 m2 mf] [sz: N] [v_init: Vl]
    [hp': Hp] [alc'] [ptr: Pt] [bh]
    (WFINJ: CCInj.wf s m inj)
    (ALLOC_GC: alloc (heap s) (alc s) sz (encode v_init) = Some (hp', alc', ptr))
    (BND: (sz <= alloc_max_size)%N)
    (NEWLOAD: forall mcc, CCInj.type_mem_chunk (Value.type_of_value v_init) = Some mcc ->
        exists tv, CCInj.InjValue inj v_init tv
                   /\ forall i: N, (i < sz)%N ->
                        Memory.Mem.load mcc mf bh (CCInj.offset_to_offset (Z.of_N i))
                        = Some tv)
    (CALLOC: Memory.Mem.alloc m (- Memdata.size_chunk AST.Mptr)
               (CCInj.offset_to_offset (Z.of_N sz)) = (m1, bh))
    (CSTORE: Memory.Mem.store AST.Mptr m1 bh (- Memdata.size_chunk AST.Mptr)
               (Values.Vptrofs (Ptrofs.repr (CCInj.offset_to_offset (Z.of_N sz))))
             = Some m2)
    (EACC: Memory.Mem.mem_access mf = Memory.Mem.mem_access m2)
    (ENB: Memory.Mem.nextblock mf = Memory.Mem.nextblock m2)
    (LOADO: forall mcc b' ofs',
        b' <> bh \/ (ofs' + Memdata.size_chunk mcc <= 0)%Z ->
        Memory.Mem.load mcc mf b' ofs' = Memory.Mem.load mcc m2 b' ofs')
    (CONTf: forall b', b' <> bh ->
        Maps.PMap.get b' (Memory.Mem.mem_contents mf)
        = Maps.PMap.get b' (Memory.Mem.mem_contents m2))
    : exists inj2,
        inj2.(CCInj.inj_st_map) = inj.(CCInj.inj_st_map)
        /\ CCInj.inj_hp_le inj inj2
        /\ CCInj.InjValue inj2 (Value.v_ptr ptr) (Values.Vptr bh Ptrofs.zero)
        /\ CCInj.wf (State.state_alloc s ALLOC_GC) mf inj2.
  Proof using Type.
    specialize memword_bytes_pos as MSPOS.
    specialize (N2Z.is_nonneg sz) as SZNN.
    specialize (Memdata.size_chunk_pos AST.Mptr) as SCPOS.
    assert (HINN: (0 <= CCInj.offset_to_offset (Z.of_N sz))%Z)
      by (unfold CCInj.offset_to_offset; nia).
    destruct (proj2 (alloc_some (heap s) (alc s) sz (encode v_init))
                (ex_intro _ hp' (ex_intro _ alc' (ex_intro _ ptr ALLOC_GC))))
      as ( bid & GETbid & SZPOS & ABS ).
    pose proof (alloc_Extent (heap s) (alc s) sz (encode v_init) hp' alc' ptr bid
                  ALLOC_GC GETbid) as EXT.
    pose proof (alloc_references (heap s) (alc s) sz (encode v_init) hp' alc' ptr bid
                  ALLOC_GC GETbid) as REFptr.
    pose proof (alloc_reaches (heap s) (alc s) sz (encode v_init) hp' alc' ptr bid
                  ALLOC_GC GETbid) as RCHptr.
    pose proof (alloc_mem (heap s) (alc s) sz (encode v_init) hp' alc' ptr ALLOC_GC)
      as MEMptr.
    pose proof (alloc_alc (heap s) (alc s) sz (encode v_init) hp' alc' ptr ALLOC_GC)
      as EALC.
    pose proof (State.heap_state_alloc s sz (encode v_init) hp' alc' ptr ALLOC_GC)
      as EHEAP.
    pose proof (State.store_state_alloc s sz (encode v_init) hp' alc' ptr ALLOC_GC)
      as ESTORE.
    pose proof (State.alc_state_alloc s sz (encode v_init) hp' alc' ptr ALLOC_GC)
      as EALCST.
    assert (FRESHbid: forall b b' szh lvh,
               In (b, (b', (szh, lvh))) inj.(CCInj.inj_hp_map) -> b <> bid).
    { intros b b' szh lvh IN EQ; subst b.
      exact (Nat.lt_irrefl bid
               (CCInj.heap_block_below_alc WFINJ bid b' szh lvh bid IN GETbid)). }
    assert (NOTVALID: ~ Memory.Mem.valid_block m bh)
      by exact (Memory.Mem.fresh_block_alloc _ _ _ _ _ CALLOC).
    assert (NEhp: forall b b' szh lvh,
               In (b, (b', (szh, lvh))) inj.(CCInj.inj_hp_map) -> b' <> bh).
    { intros b b' szh lvh IN EQ; subst b'.
      exact (NOTVALID (wf_heap_block_valid WFINJ IN)). }
    assert (NEst: forall a b' o fr,
               In (a, (b', o, fr)) inj.(CCInj.inj_st_map) -> b' <> bh).
    { intros a b' o fr IN EQ; subst b'.
      exact (NOTVALID (wf_store_block_valid WFINJ IN)). }
    assert (NEfn: forall id b',
               In (id, b') inj.(CCInj.inj_fn_map) -> b' <> bh).
    { intros id b' IN EQ; subst b'.
      exact (NOTVALID (wf_fun_block_valid WFINJ IN)). }
    assert (LOAD2: forall mcc b' ofs', Memory.Mem.valid_block m b' ->
               Memory.Mem.load mcc m2 b' ofs' = Memory.Mem.load mcc m b' ofs').
    { intros mcc b' ofs' VB.
      assert (NE: b' <> bh) by (intro EQ; subst b'; exact (NOTVALID VB)).
      rewrite (Memory.Mem.load_store_other _ _ _ _ _ _ CSTORE mcc b' ofs'
                 (or_introl NE)).
      exact (Memory.Mem.load_alloc_unchanged _ _ _ _ _ CALLOC mcc b' ofs' VB). }
    assert (PERM2: forall b' ofs k p,
               Memory.Mem.perm m b' ofs k p -> Memory.Mem.perm m2 b' ofs k p).
    { intros b' ofs k p P.
      eapply Memory.Mem.perm_store_1; [ exact CSTORE | ].
      eapply Memory.Mem.perm_alloc_1; [ exact CALLOC | exact P ]. }
    assert (ACC2: forall b', b' <> bh ->
               Maps.PMap.get b' (Memory.Mem.mem_access m2)
               = Maps.PMap.get b' (Memory.Mem.mem_access m)).
    { intros b' NE.
      rewrite (Memory.Mem.store_access _ _ _ _ _ _ CSTORE).
      exact (CompCertExt.CCMem.alloc_access_other CALLOC NE). }
    assert (CONT2: forall b', b' <> bh ->
               Maps.PMap.get b' (Memory.Mem.mem_contents m2)
               = Maps.PMap.get b' (Memory.Mem.mem_contents m)).
    { intros b' NE.
      rewrite (Memory.Mem.store_mem_contents _ _ _ _ _ _ CSTORE).
      rewrite Maps.PMap.gso by exact NE.
      exact (CompCertExt.CCMem.alloc_contents_other CALLOC NE). }
    assert (VB2: forall b', Memory.Mem.valid_block m b' -> Memory.Mem.valid_block m2 b').
    { intros b' VB.
      eapply Memory.Mem.store_valid_block_1; [ exact CSTORE | ].
      eapply Memory.Mem.valid_block_alloc; [ exact CALLOC | exact VB ]. }
    assert (VBnew: Memory.Mem.valid_block m2 bh).
    { eapply Memory.Mem.store_valid_block_1; [ exact CSTORE | ].
      exact (Memory.Mem.valid_new_block _ _ _ _ _ CALLOC). }
    assert (RPnew: Memory.Mem.range_perm m2 bh (- Memdata.size_chunk AST.Mptr)
                     (CCInj.offset_to_offset (Z.of_N sz))
                     Memtype.Cur Memtype.Freeable).
    { intros ofs RNG.
      eapply Memory.Mem.perm_store_1; [ exact CSTORE | ].
      refine (Memory.Mem.perm_alloc_2 _ _ _ _ _ CALLOC ofs _ _); lia. }
    assert (HDR2: Memory.Mem.load AST.Mptr m2 bh (- Memdata.size_chunk AST.Mptr)
                  = Some (Values.Vptrofs
                            (Ptrofs.repr (CCInj.offset_to_offset (Z.of_N sz))))).
    { rewrite (Memory.Mem.load_store_same _ _ _ _ _ _ CSTORE).
      rewrite CompCertExt.CCMem.vptrofs_load_result; reflexivity. }
    assert (PERMf: forall b' ofs k p,
               Memory.Mem.perm m2 b' ofs k p -> Memory.Mem.perm mf b' ofs k p)
      by (intros b' ofs k p P; unfold Memory.Mem.perm in *; rewrite EACC; exact P).
    assert (VBf: forall b', Memory.Mem.valid_block m2 b' -> Memory.Mem.valid_block mf b')
      by (intros b' VB; unfold Memory.Mem.valid_block in *; rewrite ENB; exact VB).
    assert (LOADf: forall mcc b' ofs', Memory.Mem.valid_block m b' ->
               Memory.Mem.load mcc mf b' ofs' = Memory.Mem.load mcc m b' ofs').
    { intros mcc b' ofs' VB.
      assert (NE: b' <> bh) by (intro EQ; subst b'; exact (NOTVALID VB)).
      rewrite (LOADO mcc b' ofs' (or_introl NE)); exact (LOAD2 mcc b' ofs' VB). }
    assert (LE: CCInj.inj_hp_le inj
                  (CCInj.Build_injection Ad
                     ((bid, (bh, (sz, true))) :: inj.(CCInj.inj_hp_map))
                     inj.(CCInj.inj_st_map) inj.(CCInj.inj_fn_map))).
    { intros b b' szh lvh HIN; exists lvh; cbn [CCInj.inj_hp_map].
      exact (ListExt.BindIn_tl _ _ _ _ _
               (FRESHbid b b' szh lvh (ListExt.BindIn_In HIN)) HIN). }
    assert (HINnew: ListExt.BindIn bid (bh, (sz, true))
                      ((bid, (bh, (sz, true))) :: inj.(CCInj.inj_hp_map)))
      by apply ListExt.BindIn_hd.
    assert (INVnew: forall b b' szh lvh,
               ListExt.BindIn b (b', (szh, lvh))
                 ((bid, (bh, (sz, true))) :: inj.(CCInj.inj_hp_map)) ->
               (b = bid /\ b' = bh /\ szh = sz /\ lvh = true)
               \/ (b <> bid /\ ListExt.BindIn b (b', (szh, lvh)) inj.(CCInj.inj_hp_map))).
    { intros b b' szh lvh HIN.
      destruct (Nat.eq_dec b bid) as [ EQ | NE ].
      - subst b; left.
        assert (EROW: (b', (szh, lvh)) = (bh, (sz, true)))
          by exact (ListExt.BindIn_fun _ _ _ _ HINnew HIN).
        injection EROW as Eb Esz Elv; subst; now repeat split.
      - right; split; [ exact NE | exact (ListExt.BindIn_cons_inv NE HIN) ]. }
    assert (INold: forall b b' pc,
               In (b, (b', pc)) ((bid, (bh, (sz, true))) :: inj.(CCInj.inj_hp_map)) ->
               (b = bid /\ b' = bh) \/ In (b, (b', pc)) inj.(CCInj.inj_hp_map)).
    { intros b b' pc [ EQ | IN ];
        [ injection EQ as Eb Eb' Epc; subst; now left | now right ]. }
    assert (NEWCELL: forall b o (w: Vl),
               (((mkAddr b (N.of_nat o)) |-> w)%mem
                  $<= State.heap (State.state_alloc s ALLOC_GC))%sep ->
               (b = bid /\ w = v_init /\ (N.of_nat o < sz)%N)
               \/ (b <> bid /\ (((mkAddr b (N.of_nat o)) |-> w)%mem
                                $<= State.heap s)%sep)).
    { intros b o w SUB.
      rewrite EHEAP in SUB.
      destruct (proj1 (MEMptr (mkAddr b (N.of_nat o)) w) SUB)
        as [ ( RCH1 & RCH2 & EW ) | ( _ & SUBo ) ].
      - left.
        assert (EB: b = bid).
        { specialize (Extent_block ptr bid sz EXT _ RCH1) as EBl.
          rewrite mkAddr_block in EBl; exact EBl. }
        subst b.
        split; [ reflexivity | ].
        assert (EWv: w = v_init) by exact EW.
        split; [ exact EWv | ].
        unfold shift_fw in RCH2; rewrite mkAddr_block, mkAddr_offset in RCH2.
        specialize (proj2 (RCHptr (N.of_nat o + 1)%N) RCH2) as LE1.
        lia.
      - right.
        assert (NEB: b <> bid)
          by (intro EQ; subst b; exact (ABS (N.of_nat o) w SUBo)).
        split; [ exact NEB | exact SUBo ]. }
    exists (CCInj.Build_injection Ad
              ((bid, (bh, (sz, true))) :: inj.(CCInj.inj_hp_map))
              inj.(CCInj.inj_st_map) inj.(CCInj.inj_fn_map)).
    split; [ reflexivity | split; [ exact LE | split ] ].
    - refine (CCInj.inj_ptr
                (CCInj.Build_injection Ad
                   ((bid, (bh, (sz, true))) :: inj.(CCInj.inj_hp_map))
                   inj.(CCInj.inj_st_map) inj.(CCInj.inj_fn_map))
                ptr bid 0%N sz true bh Ptrofs.zero HINnew EXT _ _ REFptr).
      + unfold Intops.Unsigned.Bounded.
        rewrite (Intops.Unsigned.CompCert.Ptrofs.max_unsigned_eq
                   (UInt := n_ofst_t) eq_refl).
        assert (TZ: @IntCarrier.to_Z (Intops.Unsigned.carrier n_ofst_t) 0%N = 0%Z)
          by reflexivity.
        rewrite TZ.
        unfold Intops.Unsigned.min_unsigned.
        unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize,
          Wordsize_Ptrofs.wordsize.
        destruct Archi.ptr64; cbn; lia.
      + cbn; unfold CCInj.offset_to_offset; cbn; apply Ptrofs.unsigned_zero.
    - constructor; cbn [CCInj.inj_hp_map CCInj.inj_st_map CCInj.inj_fn_map].
      + constructor; [ | exact (CCInj.heap_block_bmap WFINJ) ].
        apply ListExt.AbsBMap_intro; intros b b' c IN.
        split; [ exact (not_eq_sym (FRESHbid b b' (fst c) (snd c)
                                      ltac:(destruct c; exact IN)))
               | exact (not_eq_sym (NEhp b b' (fst c) (snd c)
                                      ltac:(destruct c; exact IN))) ].
      + exact (CCInj.store_block_map_sbinds2 WFINJ).
      + exact (CCInj.fun_block_map_sbinds2 WFINJ).
      + intros b b1 szh lvh a b2 o fr INh INs.
        destruct (INold b b1 (szh, lvh) INh) as [ ( _ & Eb1 ) | INh0 ];
          [ subst b1; exact (not_eq_sym (NEst a b2 o fr INs)) | ].
        exact (CCInj.heap_store_distinct WFINJ b b1 szh lvh a b2 o fr INh0 INs).
      + intros b b1 szh lvh id b2 INh INf.
        destruct (INold b b1 (szh, lvh) INh) as [ ( _ & Eb1 ) | INh0 ];
          [ subst b1; exact (not_eq_sym (NEfn id b2 INf)) | ].
        exact (CCInj.heap_fun_distinct WFINJ b b1 szh lvh id b2 INh0 INf).
      + exact (CCInj.store_fun_distinct WFINJ).
      + intros b o w SUB.
        destruct (NEWCELL b o w SUB) as [ ( EB & EW & LT ) | ( NEB & SUBo ) ].
        * subst b w.
          exists bh, sz; split; [ exact HINnew | ].
          intros mcc MCC.
          destruct (NEWLOAD mcc MCC) as ( tv & INJv & LDS ).
          exists tv; split; [ exact (InjValue_hp_le LE INJv) | ].
          specialize (LDS (N.of_nat o) LT) as LD.
          rewrite nat_N_Z in LD; exact LD.
        * destruct (CCInj.mem_contents_of_heap WFINJ SUBo)
            as ( b' & szh & HINh & LOADS ).
          exists b', szh; split;
            [ exact (ListExt.BindIn_tl _ _ _ _ _ NEB HINh) | ].
          intros mcc MCC.
          destruct (LOADS mcc MCC) as ( w' & INJ & LOAD ).
          exists w'; split; [ exact (InjValue_hp_le LE INJ) | ].
          rewrite (LOADf mcc b' _
                     (wf_heap_block_valid WFINJ (ListExt.BindIn_In HINh))).
          exact LOAD.
      + intros a w SUB.
        rewrite ESTORE in SUB.
        destruct (CCInj.mem_contents_of_store WFINJ a w SUB)
          as ( b' & o & fr & IN & LOADS ).
        exists b', o, fr; split; [ exact IN | ].
        intros mcc MCC.
        destruct (LOADS mcc MCC) as ( w' & INJ & LOAD ).
        exists w'; split; [ exact (InjValue_hp_le LE INJ) | ].
        rewrite (LOADf mcc b' _ (wf_store_block_valid WFINJ IN)).
        exact LOAD.
      + intros id b' IN.
        destruct (CCInj.mem_contents_of_fun WFINJ id b' IN) as ( CONT & ACC ).
        specialize (NEfn id b' IN) as NE.
        split.
        * rewrite (CONTf b' NE), (CONT2 b' NE); exact CONT.
        * rewrite EACC, (ACC2 b' NE); exact ACC.
      + intros b b' szh HINh.
        destruct (INVnew b b' szh true HINh)
          as [ ( Eb & Eb' & Esz & _ ) | ( _ & HINh0 ) ].
        * subst b b' szh.
          assert (DH: (- Memdata.size_chunk AST.Mptr
                       + Memdata.size_chunk AST.Mptr <= 0)%Z) by lia.
          rewrite (LOADO AST.Mptr bh (- Memdata.size_chunk AST.Mptr) (or_intror DH)).
          exact HDR2.
        * rewrite (LOADf AST.Mptr b' _
                     (wf_heap_block_valid WFINJ (ListExt.BindIn_In HINh0))).
          exact (CCInj.mem_header_of_heap WFINJ b b' szh HINh0).
      + intros b b' szh lvh HINh.
        destruct (INVnew b b' szh lvh HINh)
          as [ ( Eb & Eb' & Esz & Elv ) | ( _ & HINh0 ) ].
        * subst b b' szh lvh.
          split; [ exact (alloc_count_extent BND) | split ].
          -- exact (VBf bh VBnew).
          -- intros _ ofs RNG; exact (PERMf bh ofs _ _ (RPnew ofs RNG)).
        * destruct (CCInj.mem_extent_of_heap WFINJ b b' szh lvh HINh0)
            as ( BNDh & VBh & RPh ).
          split; [ exact BNDh | split ].
          -- exact (VBf b' (VB2 b' VBh)).
          -- intros ELV ofs RNG.
             exact (PERMf b' ofs _ _ (PERM2 b' ofs _ _ (RPh ELV ofs RNG))).
      + intros b o w b' szh lvh SUB HINh.
        destruct (NEWCELL b o w SUB) as [ ( EB & _ & LT ) | ( NEB & SUBo ) ].
        * subst b.
          destruct (INVnew bid b' szh lvh HINh)
            as [ ( _ & _ & Esz & _ ) | ( NE & _ ) ];
            [ subst szh; exact LT | now contradiction NE ].
        * destruct (INVnew b b' szh lvh HINh)
            as [ ( EB & _ ) | ( _ & HINh0 ) ];
            [ now contradiction NEB | ].
          exact (CCInj.heap_contents_compact WFINJ b o w b' szh lvh SUBo HINh0).
      + intros a b' o fr IN ofs RNG.
        exact (PERMf b' ofs _ _
                 (PERM2 b' ofs _ _ (CCInj.mem_perm_of_store WFINJ a b' o fr IN ofs RNG))).
      + intros b b' szh lvh bid2 INh GET.
        rewrite EALCST, EALC in GET.
        specialize (cnext_lt (alc s) bid bid2 GETbid GET) as LTb.
        destruct (INold b b' (szh, lvh) INh) as [ ( Eb & _ ) | INh0 ];
          [ subst b; exact LTb | ].
        exact (Nat.lt_trans _ _ _
                 (CCInj.heap_block_below_alc WFINJ b b' szh lvh bid INh0 GETbid) LTb).
  Qed.

  Lemma eval_ofst_from_count [tge sp te m] [ec: Cminor.expr] [sz: N]
    (EV: Cminor.eval_expr tge sp te m ec (ofst_val sz))
    (BND: (0 <= CCInj.offset_to_offset (Z.of_N sz) <= Ptrofs.max_unsigned)%Z)
    : Cminor.eval_expr tge sp te m (make_ofst_from_count ec)
        (Values.Vptrofs (Ptrofs.repr (CCInj.offset_to_offset (Z.of_N sz)))).
  Proof using Type.
    specialize (ofst_val_range (proj2 BND)) as BNDsz.
    unfold make_ofst_from_count, adjust_offset.
    destruct (Archi.ptr64) eqn:ARCHI;
      (eapply Cminor.eval_Ebinop;
       [ exact EV | exact (eval_make_ofst (N.of_nat memword_bytes)) | ]);
      unfold ofst_val, Values.Vptrofs; rewrite ARCHI.
    - cbn [Cminor.eval_binop Values.Val.mull].
      unfold Ptrofs.to_int64, Int64.mul.
      rewrite (Int64.unsigned_repr _ (CompCertExt.Ints.Ptrofs.bound_int64 ARCHI BNDsz)).
      rewrite (Int64.unsigned_repr _ (memword_bytes_small64 ARCHI)).
      rewrite (Ptrofs.unsigned_repr _ BND).
      unfold CCInj.offset_to_offset; rewrite nat_N_Z; reflexivity.
    - cbn [Cminor.eval_binop Values.Val.mul].
      unfold Ptrofs.to_int, Int.mul.
      rewrite (Int.unsigned_repr _ (CompCertExt.Ints.Ptrofs.bound_int32 ARCHI BNDsz)).
      rewrite (Int.unsigned_repr _ (memword_bytes_small32 ARCHI)).
      rewrite (Ptrofs.unsigned_repr _ BND).
      unfold CCInj.offset_to_offset; rewrite nat_N_Z; reflexivity.
  Qed.

  Lemma alloc_ptr_run
    [prog: Prog.program] [tprog] [ctx: Ctxt.ctxt (Types.type * bool) (Types.type * bool) unit fundef vardef]
    [idm idf] [inj: CCInj.injection Ad] [s: Sm] [m] [sp] [tf: Cminor.function]
    [tk: Cminor.cont] [target]
    [f: function] [env: @Semantics.env Sm] [te]
    [e_count e_init: Expr.expr] [t: Types.type] [id_ptr id_count id_init: AST.ident]
    [sz: N] [v_init: Vl] [hp': Hp] [alc'] [ptr: Pt]
    (TRANSL: match_prog prog tprog)
    (DECLm: exf_declared (Prog.program_of_program prog) idm AST.EF_malloc)
    (WFINJ: CCInj.wf s m inj)
    (MTEMPS: match_temps f inj env te)
    (WTENV: Semantics.wt_env f ctx.(Ctxt.ctxt_pure) env)
    (WTcount: Expr.wt_expr ctx.(Ctxt.ctxt_pure) e_count Types.t_ofst)
    (WTinit: Expr.wt_expr ctx.(Ctxt.ctxt_pure) e_init t)
    (EVAL_SIZE: Expr.eval e_count env = Some (Value.v_ofst sz))
    (EVAL_INIT: Expr.eval e_init env = Some v_init)
    (WTv: Value.wt_value v_init t)
    (BNDsz: (sz <= alloc_max_size)%N)
    (ALLOC_GC: alloc (heap s) (alc s) sz (encode v_init) = Some (hp', alc', ptr))
    (NEpc: id_ptr <> id_count) (NEic: id_init <> id_count) (NEip: id_init <> id_ptr)
    (NOTLOCALp: forall t', ~ In (id_ptr, t') (f.(fn_params) ++ f.(fn_temps)))
    (NOTLOCALc: forall t', ~ In (id_count, t') (f.(fn_params) ++ f.(fn_temps)))
    (NOTLOCALi: forall t', ~ In (id_init, t') (f.(fn_params) ++ f.(fn_temps)))
    : exists te' mf inj2 bh,
        Smallstep.plus Cminor.step (Genv.globalenv tprog)
          (Cminor.State tf
             (transl_cmd idm idf target
                (Cmd.c_alloc_ptr e_count t e_init id_ptr id_count id_init))
             tk (Values.Vptr sp Ptrofs.zero) te m)
          Events.E0
          (Cminor.State tf (return_or_assign_sized target (Cminor.Evar id_ptr))
             tk (Values.Vptr sp Ptrofs.zero) te' mf)
        /\ Maps.PTree.get id_ptr te' = Some (Values.Vptr bh Ptrofs.zero)
        /\ match_temps f inj2 env te'
        /\ inj2.(CCInj.inj_st_map) = inj.(CCInj.inj_st_map)
        /\ CCInj.inj_hp_le inj inj2
        /\ CCInj.InjValue inj2 (Value.v_ptr ptr) (Values.Vptr bh Ptrofs.zero)
        /\ CCInj.wf (State.state_alloc s ALLOC_GC) mf inj2.
  Proof using Type.
    specialize memword_bytes_pos as MSPOS.
    specialize (N2Z.is_nonneg sz) as SZNN.
    specialize (Memdata.size_chunk_pos AST.Mptr) as SCPOS.
    specialize (alloc_count_extent BNDsz) as BNDX.
    assert (MBZ: (0 < Z.of_nat memword_bytes)%Z) by lia.
    assert (BNDX0: (0 <= CCInj.offset_to_offset (Z.of_N sz) <= Ptrofs.max_unsigned)%Z)
      by (unfold CCInj.offset_to_offset in BNDX |- *; nia).
    destruct (transl_expr_progress WTcount ltac:(discriminate) WTENV MTEMPS EVAL_SIZE)
      as ( tvc & EVc & INJc ).
    pose proof (InjValue_ofst_val INJc) as EVAL_c; subst tvc.
    destruct (exf_declared_symbol (exf_declared_match TRANSL DECLm))
      as ( bm & SYMB & FUNCT ).
    destruct (alloc_malloc_mem m sz) as ( bh & m1 & m2 & CALLOC & CSTORE ).
    assert (EXTCALL: Events.external_call AST.EF_malloc (Genv.globalenv tprog)
                       [Values.Vptrofs
                          (Ptrofs.repr (CCInj.offset_to_offset (Z.of_N sz)))]
                       m Events.E0 (Values.Vptr bh Ptrofs.zero) m2).
    { cbn [Events.external_call].
      apply Events.extcall_malloc_sem_intro with (m' := m1).
      - rewrite (Ptrofs.unsigned_repr _ BNDX0); exact CALLOC.
      - exact CSTORE. }
    assert (RP2: Memory.Mem.range_perm m2 bh 0
                   (CCInj.offset_to_offset (Z.of_N sz))
                   Memtype.Cur Memtype.Freeable).
    { intros ofs RNG.
      eapply Memory.Mem.perm_store_1; [ exact CSTORE | ].
      refine (Memory.Mem.perm_alloc_2 _ _ _ _ _ CALLOC ofs _ _); lia. }
    assert (CALLSTEP: forall (te0: Cminor.env) (tk0: Cminor.cont),
               match_temps f inj env te0 ->
               Smallstep.star Cminor.step (Genv.globalenv tprog)
                 (Cminor.State tf
                    (make_call (Some id_ptr) idm
                       [ make_ofst_from_count (transl_expr e_count) ]
                       (AST.ef_sig AST.EF_malloc))
                    tk0 (Values.Vptr sp Ptrofs.zero) te0 m)
                 Events.E0
                 (Cminor.State tf Cminor.Sskip tk0 (Values.Vptr sp Ptrofs.zero)
                    (Maps.PTree.set id_ptr (Values.Vptr bh Ptrofs.zero) te0) m2)).
    { intros te0 tk0 MT0.
      destruct (transl_expr_progress WTcount ltac:(discriminate) WTENV MT0 EVAL_SIZE)
        as ( tv0 & EV0 & INJ0 ).
      pose proof (InjValue_ofst_val INJ0) as E0; subst tv0.
      cbn [make_call AST.ef_sig AST.sig_res].
      eapply Smallstep.star_step;
        [ eapply Cminor.step_call;
          [ apply Cminor.eval_Econst;
            cbn [Cminor.eval_constant];
            unfold Genv.symbol_address; rewrite (SYMB: Genv.find_symbol (Genv.globalenv tprog) idm = Some bm); reflexivity
          | econstructor;
            [ exact (eval_ofst_from_count
                       (EV0 (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m)
                       BNDX0)
            | econstructor ]
          | exact FUNCT
          | reflexivity ]
        | | reflexivity ].
      eapply Smallstep.star_step;
        [ apply Cminor.step_external_function; exact EXTCALL | | reflexivity ].
      eapply Smallstep.star_step; [ apply Cminor.step_return | | reflexivity ].
      apply Smallstep.star_refl. }
    destruct (CCInj.type_mem_chunk t) as [ mc | ] eqn:MC.
    -
      assert (NUNIT: t <> Types.t_unit) by (destruct t; [ discriminate MC | discriminate .. ]).
      destruct (transl_expr_progress WTinit NUNIT WTENV MTEMPS EVAL_INIT)
        as ( tvi & EVi & INJi ).
      assert (MCv: CCInj.type_mem_chunk (Value.type_of_value v_init) = Some mc)
        by (rewrite (Value.Facts.type_of_value_complete WTv); exact MC).
      specialize (CCInj.Facts.InjValue_load_result INJi MCv) as LRES.
      set (te1 := Maps.PTree.set id_init tvi te).
      set (te2 := Maps.PTree.set id_ptr (Values.Vptr bh Ptrofs.zero) te1).
      set (te3 := Maps.PTree.set id_count (ofst_val 0) te2).
      assert (MT1: match_temps f inj env te1)
        by exact (match_temps_set_internal NOTLOCALi MTEMPS (tv := tvi)).
      assert (MT2: match_temps f inj env te2)
        by exact (match_temps_set_internal NOTLOCALp MT1
                    (tv := Values.Vptr bh Ptrofs.zero)).
      assert (MT3: match_temps f inj env te3)
        by exact (match_temps_set_internal NOTLOCALc MT2 (tv := ofst_val 0)).
      assert (GETp3: Maps.PTree.get id_ptr te3 = Some (Values.Vptr bh Ptrofs.zero)).
      { unfold te3, te2; rewrite Maps.PTree.gso by exact NEpc; apply Maps.PTree.gss. }
      assert (GETi3: Maps.PTree.get id_init te3 = Some tvi).
      { unfold te3, te2, te1.
        rewrite Maps.PTree.gso by exact NEic.
        rewrite Maps.PTree.gso by exact NEip.
        apply Maps.PTree.gss. }
      assert (GETc3: Maps.PTree.get id_count te3 = Some (ofst_val 0))
        by (unfold te3; apply Maps.PTree.gss).
      assert (EVSTOP: forall te0 mm, match_temps f inj env te0 ->
                 Cminor.eval_expr (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero)
                   te0 mm (transl_expr e_count) (ofst_val sz)).
      { intros te0 mm MT0.
        destruct (transl_expr_progress WTcount ltac:(discriminate) WTENV MT0 EVAL_SIZE)
          as ( tv0 & EV0 & INJ0 ).
        pose proof (InjValue_ofst_val INJ0) as E0; subst tv0.
        exact (EV0 (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) mm). }
      destruct (alloc_loop_iter (tf := tf) (sp := sp) (bh := bh) (mc := mc)
                  (id_ptr := id_ptr) (id_count := id_count) (id_init := id_init)
                  (stop := transl_expr e_count) (tv_init := tvi)
                  (fn := f) (inj := inj) (env := env) (count := sz)
                  NEpc NEic NOTLOCALc BNDX (memword_bytes_size_chunk MC) (memword_bytes_align MC)
                  LRES EVSTOP (N.to_nat sz) 0%N (Cminor.Kseq
                    (return_or_assign_sized target (Cminor.Evar id_ptr)) tk)
                  te3 m2 ltac:(reflexivity) GETp3 GETi3 GETc3 MT3 RP2)
        as ( te' & mf & STAR & GETp' & MT' & EACC & ENB & LOADO & CONTf & CELLS ).
      assert (LOADO0: forall mcc b' ofs',
                 b' <> bh \/ (ofs' + Memdata.size_chunk mcc <= 0)%Z ->
                 Memory.Mem.load mcc mf b' ofs' = Memory.Mem.load mcc m2 b' ofs').
      { intros mcc b' ofs' DSJ.
        apply LOADO.
        destruct DSJ as [ NE | LE ]; [ now left | right ].
        unfold CCInj.offset_to_offset; cbn; lia. }
      destruct (wf_alloc_ptr WFINJ ALLOC_GC BNDsz
                  ltac:(intros mcc MCC; rewrite MCv in MCC; injection MCC as <-;
                        exists tvi; split; [ exact INJi | ];
                        intros i LTi; exact (CELLS i (N.le_0_l i) LTi))
                  CALLOC CSTORE EACC ENB LOADO0 CONTf)
        as ( inj2 & EST & LE & INJptr & WF2 ).
      exists te', mf, inj2, bh.
      split; [ | split; [ exact GETp' | split; [ | split; [ exact EST |
               split; [ exact LE | split; [ exact INJptr | exact WF2 ] ] ] ] ] ].
      + cbn [transl_cmd]; unfold ret_expr; rewrite MC.
        cbn [return_or_assign_sized return_or_assign_unsized].
        eapply Smallstep.plus_left; [ apply Cminor.step_seq | | reflexivity ].
        eapply Smallstep.star_step;
          [ apply Cminor.step_assign;
            exact (EVi (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m)
          | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_skip_seq | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_seq | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_seq | | reflexivity ].
        eapply Smallstep.star_trans;
          [ exact (CALLSTEP te1 (Cminor.Kseq
                     (make_for_ofst id_count (make_ofst 0) (make_ofst 1)
                        (transl_expr e_count)
                        (fun i => store_ptr_stmt
                                    (make_ptr_shift_fw (Cminor.Evar id_ptr) i)
                                    (Cminor.Evar id_init, mc)))
                     (Cminor.Kseq
                        (return_or_assign_sized target (Cminor.Evar id_ptr)) tk))
                     MT1)
          | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_skip_seq | | reflexivity ].
        rewrite make_for_ofst_shape.
        eapply Smallstep.star_step; [ apply Cminor.step_block | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_seq | | reflexivity ].
        eapply Smallstep.star_step;
          [ apply Cminor.step_assign; exact (eval_make_ofst 0) | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_skip_seq | | reflexivity ].
        eapply Smallstep.star_trans; [ exact STAR | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_skip_seq | | reflexivity ].
        apply Smallstep.star_refl.
      + exact (match_temps_hp_le LE MT').
    -
      assert (ETU: t = Types.t_unit) by (destruct t; [ reflexivity | discriminate MC .. ]).
      subst t.
      assert (EV: v_init = Value.v_tt) by (inversion WTv; reflexivity).
      subst v_init.
      set (te2 := Maps.PTree.set id_ptr (Values.Vptr bh Ptrofs.zero) te).
      assert (MT2: match_temps f inj env te2)
        by exact (match_temps_set_internal NOTLOCALp MTEMPS
                    (tv := Values.Vptr bh Ptrofs.zero)).
      destruct (wf_alloc_ptr WFINJ ALLOC_GC BNDsz
                  ltac:(intros mcc MCC; cbn in MCC; discriminate MCC)
                  CALLOC CSTORE (eq_refl (Memory.Mem.mem_access m2))
                  (eq_refl (Memory.Mem.nextblock m2))
                  ltac:(intros mcc b' ofs' _; reflexivity)
                  ltac:(intros b' _; reflexivity))
        as ( inj2 & EST & LE & INJptr & WF2 ).
      exists te2, m2, inj2, bh.
      split; [ | split; [ | split; [ | split; [ exact EST |
               split; [ exact LE | split; [ exact INJptr | exact WF2 ] ] ] ] ] ].
      + cbn [transl_cmd]; unfold ret_expr; rewrite MC.
        cbn [return_or_assign_sized return_or_assign_unsized].
        eapply Smallstep.plus_left; [ apply Cminor.step_seq | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_skip_seq | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_seq | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_seq | | reflexivity ].
        eapply Smallstep.star_trans;
          [ exact (CALLSTEP te (Cminor.Kseq Cminor.Sskip
                     (Cminor.Kseq
                        (return_or_assign_sized target (Cminor.Evar id_ptr)) tk))
                     MTEMPS)
          | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_skip_seq | | reflexivity ].
        eapply Smallstep.star_step; [ apply Cminor.step_skip_seq | | reflexivity ].
        apply Smallstep.star_refl.
      + unfold te2; apply Maps.PTree.gss.
      + exact (match_temps_hp_le LE MT2).
  Qed.

  Inductive builtin_epilogue (tge: Cminor.genv) (target: option AST.ident) (t: Types.type)
    (sp: Values.block) (te: Cminor.env) (m: Memory.mem) (inj: CCInj.injection Ad)
    (s': Sm) (v: Vl): Cminor.stmt -> Prop :=
  | epilogue_unsized: forall (EV: v = Value.v_tt) (ET: t = Types.t_unit)
    , builtin_epilogue tge target t sp te m inj s' v (return_or_assign_unsized target)
  | epilogue_sized: forall [a tv]
                           (NEUNIT: t <> Types.t_unit)
                           (EVAL: Cminor.eval_expr tge (Values.Vptr sp Ptrofs.zero) te m a tv)
                           (INJ: CCInj.InjValue inj v tv)
    , builtin_epilogue tge target t sp te m inj s' v (return_or_assign_sized target a)
  | epilogue_free: forall [a tvp idf bfree]
                          (EV: v = Value.v_tt) (ET: t = Types.t_unit)
                          (SYMB: Genv.find_symbol tge idf = Some bfree)
                          (FUNCT: Genv.find_funct tge (Values.Vptr bfree Ptrofs.zero)
                                  = Some (AST.External AST.EF_free))
                          (EVAL: Cminor.eval_expr tge (Values.Vptr sp Ptrofs.zero) te m a tvp)
                          (EXTCALL: forall (S: Sm) mx (injx: CCInj.injection Ad)
                                           (WFx: CCInj.wf S mx injx)
                                           (EHEAP: State.heap S = State.heap s')
                                           (EHPx: injx.(CCInj.inj_hp_map) = inj.(CCInj.inj_hp_map)),
                              exists m' inj',
                                Events.external_call AST.EF_free tge [tvp] mx Events.E0 Values.Vundef m'
                                /\ CCInj.inj_hp_le injx inj'
                                /\ inj'.(CCInj.inj_st_map) = injx.(CCInj.inj_st_map)
                                /\ CCInj.wf S m' inj')
    , builtin_epilogue tge target t sp te m inj s' v
        (make_call target idf [ a ] (AST.ef_sig AST.EF_free))
  .

  Lemma builtin_sim [prog tprog idm idf f c k e locals s ctx t] [v: Vl] [s': Sm]
    [inj: CCInj.injection Ad] [m sp base te] [target tk]
    (TRANSL: match_prog prog tprog)
    (DECLm: exf_declared (Prog.program_of_program prog) idm AST.EF_malloc)
    (DECLf: exf_declared (Prog.program_of_program prog) idf AST.EF_free)
    (WTState: Semantics.wt_State f c k e locals s ctx t)
    (WFINJ: CCInj.wf s m inj)
    (STACKBL: match_stack_block_env inj f e locals (store s) sp base te)
    (MCTXT: match_ctxt ctx (Genv.globalenv (Prog.program_of_program prog)))
    (BUILTIN: Semantics.builtin c (Genv.globalenv (Prog.program_of_program prog)) e locals s v s')
    : exists te' m' inj' epi,
        Smallstep.star Cminor.step (Genv.globalenv tprog)
          (Cminor.State
             (Cminorgen.transl_funbody idm idf f)
             (transl_cmd idm idf target c)
             tk (Values.Vptr sp Ptrofs.zero) te m)
          Events.E0
          (Cminor.State
             (Cminorgen.transl_funbody idm idf f)
             epi tk (Values.Vptr sp Ptrofs.zero) te' m')
        /\ CCInj.wf s' m' inj'
        /\ CCInj.inj_hp_le inj inj'
        /\ inj'.(CCInj.inj_st_map) = inj.(CCInj.inj_st_map)
        /\ match_stack_block_env inj' f e locals (store s') sp base te'
        /\ builtin_epilogue (Genv.globalenv tprog) target t sp te' m' inj' s' v epi.
  Proof using Type.
    pose proof STACKBL as FR; destruct FR as [ [ WTSTACK LOCALSSZ LAYERED STACKBLMAP ] MTEMPS ].
    pose proof WTState as WTS; destruct WTS as [ WTFN WTCMD WTCONT WTENV FINT ].
    inversion BUILTIN; subst; inversion WTCMD; subst.
    - cbn [transl_cmd]; unfold ret_expr.
      destruct t;
        [ inversion WT; subst; cbn [CCInj.type_mem_chunk];
          exists te, m, inj; eexists; repeat apply conj;
          [ apply Smallstep.star_refl | exact WFINJ | apply CCInj.inj_hp_le_eq; reflexivity
          | reflexivity | exact STACKBL
          | apply epilogue_unsized; reflexivity ]
        | destruct (transl_expr_progress WTexpr ltac:(discriminate) WTENV MTEMPS EVAL)
            as ( tv & EVALtv & INJ );
          specialize (EVALtv (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m);
          cbn [CCInj.type_mem_chunk];
          exists te, m, inj; eexists; repeat apply conj;
          [ apply Smallstep.star_refl | exact WFINJ | apply CCInj.inj_hp_le_eq; reflexivity
          | reflexivity | exact STACKBL
          | eapply epilogue_sized; [ discriminate | exact EVALtv | exact INJ ] ] .. ].
    - cbn [transl_cmd]; unfold ret_load_ptr, stack_ptr, load_ptr_expr.
      destruct t;
        [ inversion WT; subst; cbn [CCInj.type_mem_chunk];
          exists te, m, inj; eexists; repeat apply conj;
          [ apply Smallstep.star_refl | exact WFINJ | apply CCInj.inj_hp_le_eq; reflexivity
          | reflexivity | exact STACKBL
          | apply epilogue_unsized; reflexivity ]
        | destruct (read_var_load WFINJ STACKBL (wt_fn_extra WTFN) DEREF LOOKUP WT eq_refl)
            as ( tv & LOADV & INJ );
          cbn [CCInj.type_mem_chunk];
          exists te, m, inj; eexists; repeat apply conj;
          [ apply Smallstep.star_refl | exact WFINJ | apply CCInj.inj_hp_le_eq; reflexivity
          | reflexivity | exact STACKBL
          | eapply epilogue_sized;
            [ discriminate
            | eapply Cminor.eval_Eload;
              [ apply Cminor.eval_Econst; reflexivity
              | cbn [Values.Val.offset_ptr]; rewrite Ptrofs.add_zero_l; exact LOADV ]
            | exact INJ ] ] .. ].
    - assert (LAYERED': layered base locals (store (State.state_mutate_store s MUTATE)))
        by (rewrite (State.store_state_mutate_store s _ _ _ MUTATE);
            exact (layered_mutate LAYERED DEREF MUTATE)).
      pose proof {| MSBshape := {| MSBrows := WTSTACK; MSBsize := LOCALSSZ;
                                    MSBlayered := LAYERED'; MSBmap := STACKBLMAP |};
                    MSBtemps := MTEMPS |}
        as STACKBL'.
      assert (EVALaddr: Cminor.eval_expr (Genv.globalenv tprog)
                          (Values.Vptr sp Ptrofs.zero) te m (stack_ptr n)
                          (Values.Vptr sp (Ptrofs.repr (CCInj.offset_to_offset (Z.of_nat n))))).
      { unfold stack_ptr.
        apply Cminor.eval_Econst;
          cbn [Cminor.eval_constant Values.Val.offset_ptr];
          rewrite Ptrofs.add_zero_l; reflexivity. }
      cbn [transl_cmd]; unfold ret_store_ptr, perform_then_ret_unsized.
      destruct t0;
        [ inversion WT; subst; cbn [CCInj.type_mem_chunk];
          exists te, m, inj; eexists; repeat apply conj;
          [ eapply Smallstep.star_two;
            [ apply Cminor.step_seq | apply Cminor.step_skip_seq | reflexivity ]
          | exact (wf_mutate_store_unsized WFINJ MUTATE eq_refl)
          | apply CCInj.inj_hp_le_eq; reflexivity
          | reflexivity | exact STACKBL'
          | apply epilogue_unsized; reflexivity ]
        | destruct (transl_expr_progress WTval ltac:(discriminate) WTENV MTEMPS EVAL)
            as ( tvd & EVALd & INJd );
          specialize (EVALd (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m);
          destruct (write_var_store WFINJ STACKBL (wt_fn_extra WTFN) DEREF MUTATE INJd WT eq_refl)
            as ( m2 & STOREV & WF2 );
          cbn [CCInj.type_mem_chunk];
          exists te, m2, inj; eexists; repeat apply conj;
          [ eapply Smallstep.star_three;
            [ apply Cminor.step_seq
            | eapply Cminor.step_store; [ exact EVALaddr | exact EVALd | exact STOREV ]
            | apply Cminor.step_skip_seq
            | reflexivity ]
          | exact WF2
          | apply CCInj.inj_hp_le_eq; reflexivity
          | reflexivity | exact STACKBL'
          | apply epilogue_unsized; reflexivity ] .. ].
    - destruct (alloc_ptr_run
                  (tf := Cminorgen.transl_funbody idm idf f) (idf := idf)
                  (tk := tk) (sp := sp) (target := target)
                  TRANSL DECLm WFINJ MTEMPS WTENV WTcount WTinit
                  EVAL_SIZE EVAL_INIT WT BND ALLOC_GC
                  NEptrcount (fun E => NEcountinit (eq_sym E)) (fun E => NEptrinit (eq_sym E))
                  (Lemmas.function_internals_not_local WTFN FINT INTptr)
                  (Lemmas.function_internals_not_local WTFN FINT INTcount)
                  (Lemmas.function_internals_not_local WTFN FINT INTinit))
        as ( te2 & m2 & inj2 & bh & PLUS & GETptr & MTEMPS2 & ESTMAP & EHP2
             & INJptr & WF2 ).
      assert (LAYERED2: layered base locals (store (State.state_alloc s ALLOC_GC)))
        by (rewrite (State.store_state_alloc s v_size (encode v_init) hp' alc' ptr ALLOC_GC);
            exact LAYERED).
      exists te2, m2, inj2; eexists; repeat apply conj.
      + apply Smallstep.plus_star; exact PLUS.
      + exact WF2.
      + exact EHP2.
      + exact ESTMAP.
      + exact {| MSBshape := match_stack_block_shape_st_map ESTMAP
                                {| MSBrows := WTSTACK; MSBsize := LOCALSSZ;
                                   MSBlayered := LAYERED2; MSBmap := STACKBLMAP |};
                 MSBtemps := MTEMPS2 |}.
      + eapply epilogue_sized;
          [ discriminate | apply Cminor.eval_Evar; exact GETptr | exact INJptr ].
    - destruct (transl_expr_progress WTptr ltac:(discriminate) WTENV MTEMPS EVAL)
        as ( tvp & EVALp & INJp ).
      specialize (EVALp (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      cbn [transl_cmd]; unfold ret_load_ptr, load_ptr_expr.
      destruct t;
        [ inversion WT; subst; cbn [CCInj.type_mem_chunk];
          exists te, m, inj; eexists; repeat apply conj;
          [ apply Smallstep.star_refl | exact WFINJ | apply CCInj.inj_hp_le_eq; reflexivity
          | reflexivity | exact STACKBL
          | apply epilogue_unsized; reflexivity ]
        | destruct (read_ptr_load WFINJ INJp LOOKUP WT eq_refl) as ( tv & LOADV & INJ );
          cbn [CCInj.type_mem_chunk];
          exists te, m, inj; eexists; repeat apply conj;
          [ apply Smallstep.star_refl | exact WFINJ | apply CCInj.inj_hp_le_eq; reflexivity
          | reflexivity | exact STACKBL
          | eapply epilogue_sized;
            [ discriminate
            | eapply Cminor.eval_Eload; [ exact EVALp | exact LOADV ]
            | exact INJ ] ] .. ].
    - assert (LAYERED': layered base locals (store (State.state_mutate_heap s MUTATE)))
        by (rewrite (State.store_state_mutate_heap s _ _ _ MUTATE); exact LAYERED).
      pose proof {| MSBshape := {| MSBrows := WTSTACK; MSBsize := LOCALSSZ;
                                    MSBlayered := LAYERED'; MSBmap := STACKBLMAP |};
                    MSBtemps := MTEMPS |}
        as STACKBL'.
      destruct (transl_expr_progress WTptr ltac:(discriminate) WTENV MTEMPS EVAL_ptr)
        as ( tvp & EVALp & INJp ).
      specialize (EVALp (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      cbn [transl_cmd]; unfold ret_store_ptr, perform_then_ret_unsized.
      destruct t0;
        [ inversion WT; subst; cbn [CCInj.type_mem_chunk];
          exists te, m, inj; eexists; repeat apply conj;
          [ eapply Smallstep.star_two;
            [ apply Cminor.step_seq | apply Cminor.step_skip_seq | reflexivity ]
          | exact (wf_mutate_heap_unsized WFINJ MUTATE eq_refl)
          | apply CCInj.inj_hp_le_eq; reflexivity
          | reflexivity | exact STACKBL'
          | apply epilogue_unsized; reflexivity ]
        | destruct (transl_expr_progress WTval ltac:(discriminate) WTENV MTEMPS EVAL_data)
            as ( tvd & EVALd & INJd );
          specialize (EVALd (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m);
          destruct (write_ptr_store WFINJ INJp MUTATE INJd WT eq_refl)
            as ( m2 & STOREV & WF2 );
          cbn [CCInj.type_mem_chunk];
          exists te, m2, inj; eexists; repeat apply conj;
          [ eapply Smallstep.star_three;
            [ apply Cminor.step_seq
            | eapply Cminor.step_store; [ exact EVALp | exact EVALd | exact STOREV ]
            | apply Cminor.step_skip_seq
            | reflexivity ]
          | exact WF2
          | apply CCInj.inj_hp_le_eq; reflexivity
          | reflexivity | exact STACKBL'
          | apply epilogue_unsized; reflexivity ] .. ].
    - destruct (transl_expr_progress WTptr ltac:(discriminate) WTENV MTEMPS EVAL)
        as ( tvp & EVALp & INJp ).
      specialize (EVALp (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      inversion INJp as [ | | | ?pp ?bb ?oo ?szz ?lvz bres ores
                                HINp EXTp BNDp USGp REFp | ];
        subst; [ | now specialize (free_null_heap FREE_GC) ].
      destruct (free_ptr_live_row WFINJ INJp FREE_GC)
        as ( bg & szg & EXTg & OFSg & HINlive ).
      destruct (exf_declared_symbol (exf_declared_match TRANSL DECLf))
        as ( bfree & SYMB & FUNCT ).
      cbn [transl_cmd].
      exists te, m, inj; eexists; repeat apply conj.
      + apply Smallstep.star_refl.
      + exact (wf_free_gc WFINJ FREE_GC).
      + apply CCInj.inj_hp_le_eq; reflexivity.
      + reflexivity.
      + rewrite (State.store_state_free s _ hp' FREE_GC); exact STACKBL.
      + eapply epilogue_free;
          [ reflexivity | reflexivity | exact SYMB | exact FUNCT | exact EVALp | ].
        intros S mx injx WFx EHEAP EHPx.
        rewrite (State.heap_state_free s _ hp' FREE_GC) in EHEAP.
        rewrite <- EHPx in HINlive.
        destruct (free_ptr_extcall TRANSL DECLf WFx EXTg OFSg HINlive FREE_GC EHEAP)
          as ( _ & m' & inj' & _ & _ & EXTC & LE & EST & WF' ).
        exists m', inj'; repeat apply conj; assumption.
    - destruct (transl_expr_progress WTptr ltac:(discriminate) WTENV MTEMPS EVAL_ptr)
        as ( tvp & EVALp & INJp ).
      destruct (transl_expr_progress WTofst ltac:(discriminate) WTENV MTEMPS EVAL_shift)
        as ( tvn & EVALn & INJn ).
      specialize (EVALp (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      specialize (EVALn (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      inversion INJp as [ | | | ?pp ?bb ?oo ?szz ?lvz bh oh HIN EXTp BNDp USGp REFp | ];
        subst; [ | now specialize (ptr_shift_fw_null SHIFT) ].
      destruct (shift_fw_inj WFINJ INJp SHIFT) as ( NBND & MKINJ ).
      inversion INJn as [ | | ?n0 ?v0 BNDn EQn | | ]; subst.
      cbn [transl_cmd].
      unfold make_ptr_shift_fw, ptr_shift_fw_op, ofst_add_op, adjust_offset, make_ofst.
      destruct (Archi.ptr64) eqn:ARCHI;
        cbn in EQn;
        destruct EQn as ( i & EQi & Etvn ); subst tvn;
        exists te, m, inj; eexists;
        (repeat apply conj;
         [ apply Smallstep.star_refl | exact WFINJ | apply CCInj.inj_hp_le_eq; reflexivity
         | reflexivity | exact STACKBL
         | eapply epilogue_sized;
           [ discriminate
           | eapply Cminor.eval_Ebinop;
             [ exact EVALp
             | (eapply Cminor.eval_Ebinop;
                [ exact EVALn | apply Cminor.eval_Econst; reflexivity | reflexivity ])
             | reflexivity ]
           | ] ]).
      + cbn [Values.Val.addl Values.Val.mull]; rewrite ARCHI.
        exact (MKINJ _ (ofst_delta_64 ARCHI EQi NBND)).
      + cbn [Values.Val.add Values.Val.mul]; rewrite ARCHI.
        exact (MKINJ _ (ofst_delta_32 ARCHI EQi NBND)).
    - destruct (transl_expr_progress WTptr ltac:(discriminate) WTENV MTEMPS EVAL_ptr)
        as ( tvp & EVALp & INJp ).
      destruct (transl_expr_progress WTofst ltac:(discriminate) WTENV MTEMPS EVAL_shift)
        as ( tvn & EVALn & INJn ).
      specialize (EVALp (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      specialize (EVALn (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      inversion INJp as [ | | | ?pp ?bb ?oo ?szz ?lvz bh oh HIN EXTp BNDp SGNp REFp | ];
        subst; [ | now specialize (ptr_shift_bw_null SHIFT) ].
      destruct (shift_bw_inj INJp SHIFT) as ( NBND & MKINJ ).
      inversion INJn as [ | | ?n0 ?v0 BNDn EQn | | ]; subst.
      cbn [transl_cmd].
      unfold make_ptr_shift_bw, ptr_shift_bw_op, ofst_sub_op, adjust_offset, make_ofst.
      destruct (Archi.ptr64) eqn:ARCHI;
        cbn in EQn;
        destruct EQn as ( i & EQi & Etvn ); subst tvn;
        exists te, m, inj; eexists;
        (repeat apply conj;
         [ apply Smallstep.star_refl | exact WFINJ | apply CCInj.inj_hp_le_eq; reflexivity
         | reflexivity | exact STACKBL
         | eapply epilogue_sized;
           [ discriminate
           | eapply Cminor.eval_Ebinop;
             [ exact EVALp
             | (eapply Cminor.eval_Ebinop;
                [ exact EVALn | apply Cminor.eval_Econst; reflexivity | reflexivity ])
             | reflexivity ]
           | ] ]).
      + cbn [Values.Val.subl Values.Val.mull]; rewrite ARCHI.
        exact (MKINJ _ (ofst_delta_64 ARCHI EQi NBND)).
      + cbn [Values.Val.sub Values.Val.mul]; rewrite ARCHI.
        exact (MKINJ _ (ofst_delta_32 ARCHI EQi NBND)).
    - destruct (transl_expr_progress WTptr_l ltac:(discriminate) WTENV MTEMPS EVAL_l)
        as ( tvl & EVALl & INJl ).
      destruct (transl_expr_progress WTptr_r ltac:(discriminate) WTENV MTEMPS EVAL_r)
        as ( tvr & EVALr & INJr ).
      specialize (EVALl (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      specialize (EVALr (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      destruct (ptr_eq_inj WFINJ INJl INJr CMPVALID CMP) as ( tvb & EVBIN & INJb ).
      cbn [transl_cmd].
      exists te, m, inj; eexists; repeat apply conj;
        [ apply Smallstep.star_refl | exact WFINJ | apply CCInj.inj_hp_le_eq; reflexivity
        | reflexivity | exact STACKBL
        | eapply epilogue_sized;
          [ discriminate | exact (eval_make_ptr_eq EVALl EVALr EVBIN) | exact INJb ] ].
    - destruct (transl_expr_progress WTl ltac:(discriminate) WTENV MTEMPS EVAL_l)
        as ( tvl & EVALl & INJl ).
      destruct (transl_expr_progress WTr ltac:(discriminate) WTENV MTEMPS EVAL_r)
        as ( tvr & EVALr & INJr ).
      specialize (EVALl (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      specialize (EVALr (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      inversion INJl as [ | ?n ?i ?BNDl ?EQil | | | ]; subst.
      inversion INJr as [ | ?n ?i ?BNDr ?EQir | | | ]; subst.
      destruct (InjValue_nat_div INJl INJr DIV) as ( EVBIN & INJq ).
      cbn [transl_cmd make_nat_div].
      exists te, m, inj; eexists; repeat apply conj;
        [ apply Smallstep.star_refl | exact WFINJ | apply CCInj.inj_hp_le_eq; reflexivity
        | reflexivity | exact STACKBL
        | eapply epilogue_sized;
          [ discriminate
          | eapply Cminor.eval_Ebinop; [ exact EVALl | exact EVALr | exact EVBIN ]
          | exact INJq ] ].
    - destruct (transl_expr_progress WTl ltac:(discriminate) WTENV MTEMPS EVAL_l)
        as ( tvl & EVALl & INJl ).
      destruct (transl_expr_progress WTr ltac:(discriminate) WTENV MTEMPS EVAL_r)
        as ( tvr & EVALr & INJr ).
      specialize (EVALl (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      specialize (EVALr (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      inversion INJl as [ | ?n ?i ?BNDl ?EQil | | | ]; subst.
      inversion INJr as [ | ?n ?i ?BNDr ?EQir | | | ]; subst.
      destruct (InjValue_nat_mdl INJl INJr MDL) as ( EVBIN & INJq ).
      cbn [transl_cmd make_nat_mod].
      exists te, m, inj; eexists; repeat apply conj;
        [ apply Smallstep.star_refl | exact WFINJ | apply CCInj.inj_hp_le_eq; reflexivity
        | reflexivity | exact STACKBL
        | eapply epilogue_sized;
          [ discriminate
          | eapply Cminor.eval_Ebinop; [ exact EVALl | exact EVALr | exact EVBIN ]
          | exact INJq ] ].
  Qed.

  Lemma transl_builtin_correct [prog tprog f c k e locals s t S2 v s']
    (TRANSL: match_prog prog tprog)
    (WTp: wt_program prog)
    (BUILTIN: Semantics.builtin c
              (Globalenvs.Genv.globalenv (Prog.program_of_program prog)) e locals
              s
              v
              s')
    (STEP: Semantics.step (Globalenvs.Genv.globalenv (Prog.program_of_program prog))
              (Semantics.State f c k e locals s)
              t
              S2)
    T1
    (MS: match_states prog (Semantics.State f c k e locals s) T1):
    exists (SN : Semantics.state) (T2 : Cminor.state),
      Smallstep.star (@Semantics.step Sm) (Globalenvs.Genv.globalenv (Prog.program_of_program prog)) S2 Events.E0 SN /\
        Smallstep.plus Cminor.step (Globalenvs.Genv.globalenv tprog) T1 Events.E0 T2 /\ @match_states Sm prog SN T2.
  Proof using Type.
    inversion MS; subst.
    rename WT into WTState.
    pose proof (Lemmas.builtin_wt_value WTState BUILTIN) as WTv.
    inversion STEP; subst; try (now inversion BUILTIN);
      destruct (Lemmas.builtin_deterministic BUILTIN BUILTIN0) as [ Ev Es ]; subst;
      clear BUILTIN0.
    - rewrite (Semantics.Facts.call_cont_target CONTcall).
      destruct (builtin_sim (target := None) (tk := tk) TRANSL DECLm DECLf WTState WFINJ STACKBL MCTXT BUILTIN)
        as ( te' & m' & inj' & epi & STAR & WF' & EHP & EST & STACKBL' & EPI ).
      destruct (pop_stack_block_wf WF' STACKBL' POPSTACK)
        as ( m'' & inj'' & FREE & EHP'' & WF'' & POPNEW & POPKEEP ).
      pose proof (match_cont_hp_le EHP EST STACKBL.(MSBcont)) as MK'.
      inversion EPI; subst.
      + eexists; eexists; split; [ apply Smallstep.star_refl | split ].
        * eapply Smallstep.star_plus_trans;
            [ exact STAR
            | apply Smallstep.plus_one; apply Cminor.step_return_0; exact FREE
            | reflexivity ].
        * exact (call_cont_next_state_match WTp MCTXT WTState STEP BUILTIN CONTcall
                   STACKBL' POPSTACK
                   (CCInj.inj_hp_le_eq EHP'') POPNEW POPKEEP WF'' MK' (or_intror eq_refl)).
      + eexists; eexists; split; [ apply Smallstep.star_refl | split ].
        * eapply Smallstep.star_plus_trans;
            [ exact STAR
            | apply Smallstep.plus_one; eapply Cminor.step_return_1; [ exact EVAL | exact FREE ]
            | reflexivity ].
        * exact (call_cont_next_state_match WTp MCTXT WTState STEP BUILTIN CONTcall
                   STACKBL' POPSTACK
                   (CCInj.inj_hp_le_eq EHP'') POPNEW POPKEEP WF'' MK' (or_introl INJ)).
      + cbn [make_call].
        destruct (EXTCALL s'' m'' inj'' WF'' (Lemmas.pop_stack_heap POPSTACK) EHP'')
          as ( m3 & inj3 & EXTC & LE3 & EST3 & WF3 ).
        eexists; eexists; split; [ apply Smallstep.star_refl | split ].
        * eapply Smallstep.star_plus_trans;
            [ exact STAR
            | eapply Smallstep.plus_two;
              [ eapply Cminor.step_tailcall;
                [ apply Cminor.eval_Econst;
                  cbn [Cminor.eval_constant];
                  unfold Genv.symbol_address; rewrite SYMB; reflexivity
                | econstructor; [ exact EVAL | econstructor ]
                | exact FUNCT
                | reflexivity
                | exact FREE ]
              | apply Cminor.step_external_function; exact EXTC
              | reflexivity ]
            | reflexivity ].
        * exact (call_cont_next_state_match WTp MCTXT WTState STEP BUILTIN CONTcall
                   STACKBL' POPSTACK
                   (CCInj.inj_hp_le_trans (CCInj.inj_hp_le_eq EHP'') LE3)
                   ltac:(intros a0 b0 o0 f0 IN0; rewrite EST3 in IN0;
                         exact (POPNEW a0 b0 o0 f0 IN0))
                   ltac:(intros a0 x0 IN0 CELL0; rewrite EST3;
                         exact (POPKEEP a0 x0 IN0 CELL0))
                   WF3 MK' (or_intror eq_refl)).
    - pose proof WTState as WTS; destruct WTS as [ WTFN WTCMD WTCONT WTENV FINT ].
      pose proof STACKBL.(MSBcont) as MK.
      inversion SEQresolve as [ b_id c_nxt k_0 v_x
                              | c_cond id_cond c_body id_body k_0 bb
                              | c_cond id_cond c_body id_body k_0 ];
        subst; inversion SEQtarget; subst;
        cbn [Semantics.cont_target] in *;
        destruct (builtin_sim (target := Some target_id) (tk := tk)
                    TRANSL DECLm DECLf WTState WFINJ STACKBL MCTXT BUILTIN)
          as ( te' & m' & inj' & epi & STAR & WF' & EHP & EST & STACKBL' & EPI );
        inversion MK; subst;
        pose proof {| MSBenv := STACKBL'; MSBcont := match_cont_hp_le EHP EST MK0 |} as STACKBL0.
      + inversion EPI; subst.
        * eexists; eexists; split; [ apply Smallstep.star_refl | split ].
          -- eapply Smallstep.star_plus_trans;
               [ exact STAR
               | apply Smallstep.plus_one; apply Cminor.step_skip_seq
               | reflexivity ].
          -- exact (kbind_next_state_match (tv := Values.Vundef) (optid := None)
                      WTState WF' DECLm DECLf STACKBL0 MCTXT WTv (or_intror eq_refl) eq_refl).
        * eexists; eexists; split; [ apply Smallstep.star_refl | split ].
          -- eapply Smallstep.star_plus_trans;
               [ exact STAR
               | eapply Smallstep.plus_two;
                 [ apply Cminor.step_assign; exact EVAL
                 | apply Cminor.step_skip_seq
                 | reflexivity ]
               | reflexivity ].
          -- exact (kbind_next_state_match (optid := Some target_id)
                      WTState WF' DECLm DECLf STACKBL0 MCTXT WTv (or_introl INJ)
                      ltac:(destruct t0; [ exact (False_ind _ (NEUNIT eq_refl)) | reflexivity.. ])).
        * cbn [make_call AST.ef_sig AST.sig_res].
          destruct (EXTCALL s' m' inj' WF' eq_refl eq_refl)
            as ( m'' & inj'' & EXTC & LE'' & EST'' & WF'' ).
          eexists; eexists; split; [ apply Smallstep.star_refl | split ].
          -- eapply Smallstep.star_plus_trans;
               [ exact STAR
               | eapply Smallstep.plus_four;
                 [ eapply Cminor.step_call;
                   [ apply Cminor.eval_Econst;
                     cbn [Cminor.eval_constant];
                     unfold Genv.symbol_address; rewrite SYMB; reflexivity
                   | econstructor; [ exact EVAL | econstructor ]
                   | exact FUNCT
                   | reflexivity ]
                 | apply Cminor.step_external_function; exact EXTC
                 | apply Cminor.step_return
                 | apply Cminor.step_skip_seq
                 | reflexivity ]
               | reflexivity ].
          -- exact (kbind_next_state_match (tv := Values.Vundef) (optid := None)
                      WTState WF'' DECLm DECLf (match_stack_block_hp_le LE'' EST'' STACKBL0) MCTXT WTv
                      (or_intror eq_refl) eq_refl).
      + inversion WTv; subst.
        inversion EPI; subst; [ discriminate ET | | discriminate ET ].
        destruct (kloop1_next_state WTCONT WTFN WTENV FINT WF' DECLm DECLf STACKBL0 MCTXT EVAL INJ)
          as ( T2 & PLUS & MATCH ).
        eexists; eexists; split; [ apply Smallstep.star_refl | split; [ | exact MATCH ] ].
        eapply Smallstep.star_plus_trans; [ exact STAR | exact PLUS | reflexivity ].
      + inversion WTv; subst.
        inversion EPI; subst; [ | exact (False_ind _ (NEUNIT eq_refl)) | ].
        * destruct (kloop2_next_state (tge := Genv.globalenv tprog)
                      WTCONT WTFN WTENV FINT WF' DECLm DECLf STACKBL0 MCTXT)
            as ( T2 & PLUS & MATCH ).
          eexists; eexists; split; [ apply Smallstep.star_refl | split; [ | exact MATCH ] ].
          eapply Smallstep.star_plus_trans; [ exact STAR | exact PLUS | reflexivity ].
        * cbn [make_call AST.ef_sig AST.sig_res].
          destruct (EXTCALL s' m' inj' WF' eq_refl eq_refl)
            as ( m'' & inj'' & EXTC & LE'' & EST'' & WF'' ).
          destruct (kloop2_next_state (tge := Genv.globalenv tprog)
                      WTCONT WTFN WTENV FINT WF'' DECLm DECLf (match_stack_block_hp_le LE'' EST'' STACKBL0) MCTXT)
            as ( T2 & PLUS & MATCH ).
          eexists; eexists; split; [ apply Smallstep.star_refl | split; [ | exact MATCH ] ].
          eapply Smallstep.star_plus_trans;
            [ exact STAR
            | eapply Smallstep.plus_trans;
              [ eapply Smallstep.plus_three;
                [ eapply Cminor.step_call;
                  [ apply Cminor.eval_Econst;
                    cbn [Cminor.eval_constant];
                    unfold Genv.symbol_address; rewrite SYMB; reflexivity
                  | econstructor; [ exact EVAL | econstructor ]
                  | exact FUNCT
                  | reflexivity ]
                | apply Cminor.step_external_function; exact EXTC
                | apply Cminor.step_return
                | reflexivity ]
              | exact PLUS
              | reflexivity ]
            | reflexivity ].
  Qed.

End TRANSLATION_HELPER.

Section TRANSLATION.

  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).
  Variable prog: Prog.program.
  Variable tprog: Cminor.program.
  Hypothesis TRANSL: match_prog prog tprog.

  Lemma senv_preserved:
    Globalenvs.Senv.equiv (Genv.globalenv (Prog.program_of_program prog)) (Genv.globalenv tprog).
  Proof using TRANSL.
    apply (Genv.senv_match TRANSL).
  Qed.

  Lemma sig_preserved_external:
    forall ef sig,
      exf_funsig ef sig -> Cminor.funsig (AST.External ef) = sig.
  Proof using TRANSL.
    intros ef sig SIG.
    inversion SIG; subst; reflexivity.
  Qed.

  Lemma sig_preserved_match:
    forall p f tf sig, Prog.funsig f sig -> match_fundef p f tf -> Cminor.funsig tf = Prog.signature_of_signature sig.
  Proof using TRANSL.
    intros p f tf sig SIG MS.
    destruct MS as ( idm & idf & _ & _ & -> ).
    inversion SIG; subst; try reflexivity.
    now apply sig_preserved_external.
  Qed.

  Lemma global_init_content [F V] [ge: Genv.t F V] [id gv m0 b] [v: Vl]
    [inj: CCInj.injection Ad]
    (WTgv: wt_globvar id gv)
    (LSID: Genv.load_store_init_data ge m0 b 0 gv.(AST.gvar_init))
    (VAL: value_of_init_data (var_type gv.(AST.gvar_info)) gv.(AST.gvar_init) = Some v)
    : forall mc, CCInj.type_mem_chunk (Value.type_of_value v) = Some mc ->
                 exists v', CCInj.InjValue inj v v'
                            /\ Memory.Mem.load mc m0 b 0 = Some v'.
  Proof using Type.
    destruct gv as [ [ vt ] init ro vol ];
      cbn [AST.gvar_info AST.gvar_init var_type] in LSID, VAL.
    pose proof (WTinit := wt_globvar_init_type WTgv);
      cbn [AST.gvar_info AST.gvar_init var_type] in WTinit.
    destruct WTinit as [ | n BOOL | n | P64 | P32 ];
      cbn [value_of_init_data] in VAL;
      cbn [Genv.load_store_init_data] in LSID.
    - rewrite Z.eqb_refl in VAL; injection VAL as <-.
      intros mc MC; discriminate MC.
    - destruct LSID as ( LD & _ ).
      rewrite Z.eqb_refl, Bool.andb_true_r in VAL.
      destruct BOOL as [ E | E ]; rewrite E in VAL; cbn in VAL; injection VAL as <-;
        intros mc MC; cbn in MC; injection MC as <-.
      + exists Values.Vfalse; split;
          [ exact (CCInj.inj_bool inj false)
          | rewrite (CompCertExt.CCMem.load_bool_init (or_introl E) LD), E; reflexivity ].
      + exists Values.Vtrue; split;
          [ exact (CCInj.inj_bool inj true)
          | rewrite (CompCertExt.CCMem.load_bool_init (or_intror E) LD), E; reflexivity ].
    - destruct LSID as ( LD & _ ).
      rewrite Z.eqb_refl in VAL; injection VAL as <-.
      intros mc MC; cbn in MC; injection MC as <-.
      pose proof (RANGE := Int.unsigned_range_2 n).
      exists (Values.Vint n); split; [ | exact LD ].
      apply CCInj.inj_nat.
      + unfold Unsigned.Bounded, Unsigned.min_unsigned.
        rewrite (Unsigned.CompCert.BW32.max_unsigned_eq (UInt := nat_uint32_t) eq_refl).
        change (IntCarrier.to_Z (Z.to_nat (Int.unsigned n)))
          with (Z.of_nat (Z.to_nat (Int.unsigned n))).
        rewrite Z2Nat.id by lia; lia.
      + rewrite Z2Nat.id by lia; reflexivity.
    - destruct LSID as ( LD & _ ).
      rewrite P64, Int64.unsigned_zero in VAL; cbn in VAL; injection VAL as <-.
      intros mc MC; cbn in MC; injection MC as <-.
      exists Values.Vnullptr; split; [ constructor | ].
      unfold AST.Mptr, Values.Vnullptr; rewrite P64; exact LD.
    - destruct LSID as ( LD & _ ).
      rewrite P32, Int.unsigned_zero in VAL; cbn in VAL; injection VAL as <-.
      intros mc MC; cbn in MC; injection MC as <-.
      exists Values.Vnullptr; split; [ constructor | ].
      unfold AST.Mptr, Values.Vnullptr; rewrite P32; exact LD.
  Qed.

  Definition glob_block (id: AST.ident): Values.block :=
    match Genv.find_symbol (Genv.globalenv (Prog.program_of_program prog)) id with
    | Some b => b
    | None => 1%positive
    end.

  Definition glob_st_map (slots: list (Ad * (AST.ident * Vl))): CCInj.store_block_map Ad :=
    List.map (fun x => (fst x, (glob_block (fst (snd x)), 0%nat, false))) slots.

  Lemma AbsBind2_glob_st_map (l: list (Ad * (AST.ident * Vl))) a bb
    (NEW: forall a' id' v', In (a', (id', v')) l ->
                            a <> a' /\ bb <> (glob_block id', 0%nat, false))
    : ListExt.AbsBind2 a bb (glob_st_map l).
  Proof using Type.
    induction l as [ | [ a' [ id' v' ] ] l IH ]; cbn; [ constructor | ].
    destruct (NEW a' id' v' (or_introl eq_refl)) as ( NEa & NEb ).
    constructor; [ exact NEa | exact NEb | ].
    apply IH; intros a'' id'' v'' IN.
    exact (NEW a'' id'' v'' (or_intror IN)).
  Qed.

  Lemma glob_st_map_sbinds2 (slots: list (Ad * (AST.ident * Vl)))
    (BLK: forall a1 id1 v1 a2 id2 v2,
        In (a1, (id1, v1)) slots -> In (a2, (id2, v2)) slots ->
        id1 <> id2 -> glob_block id1 <> glob_block id2)
    (NDA: List.NoDup (List.map fst slots))
    (NDI: List.NoDup (List.map (fun x => fst (snd x)) slots))
    : ListExt.SBinds2 (glob_st_map slots).
  Proof using Type.
    induction slots as [ | [ a1 [ id1 v1 ] ] slots IH ]; [ constructor | ].
    cbn in NDA, NDI.
    apply NoDup_cons_iff in NDA as ( NINa & NDA ).
    apply NoDup_cons_iff in NDI as ( NINi & NDI ).
    cbn; constructor.
    - apply AbsBind2_glob_st_map.
      intros a' id' v' IN; split.
      + intros EQ; subst a'.
        exact (NINa (in_map fst slots (a1, (id', v')) IN)).
      + intros EQ.
        assert (NEid: id1 <> id')
          by (intros EQid; subst id';
              exact (NINi (in_map (fun x => fst (snd x)) slots (a', (id1, v')) IN))).
        exact (BLK a1 id1 v1 a' id' v' (or_introl eq_refl) (or_intror IN) NEid
                 ltac:(congruence)).
    - apply IH; [ | exact NDA | exact NDI ].
      intros ? ? ? ? ? ? IN1 IN2 NE.
      exact (BLK _ _ _ _ _ _ (or_intror IN1) (or_intror IN2) NE).
  Qed.

  Lemma init_state_correct_mem [s0]
    (WTp: wt_program prog)
    (INITstate: Semantics.init_state (Sm := Sm) prog = Some s0)
    : exists m0 inj0, Genv.init_mem (Prog.program_of_program prog) = Some m0
                      /\ @CCInj.wf Sm s0 m0 inj0.
  Proof using TRANSL.
    pose proof (WTdefs := Prog.Facts.wt_prog_defs_Forall Typing.wt_cmd_incl_global_stack _ WTp).
    assert (WTGV: forall id gv, In (id, AST.Gvar gv) prog.(prog_defs) -> wt_globvar id gv).
    { intros id gv IN.
      specialize (proj1 (Forall_forall _ _) WTdefs _ IN) as WTg; cbn in WTg.
      now inversion WTg. }
    assert (NOREPET: Coqlib.list_norepet (List.map fst prog.(prog_defs))).
    { apply ListExt.SIns_list_norepet.
      now apply ListExt.SBinds_map_fst_SIns, (wt_prog_defs_sbinds WTp). }
    destruct (Genv.init_mem_exists (Prog.program_of_program prog)) as ( m0 & INITMEM ).
    { intros id gv IN.
      pose proof (WTinit := wt_globvar_init_type (WTGV id gv IN)).
      destruct WTinit as [ | n BOOL | n | P64 | P32 ]; cbn; split;
        try (repeat split; try apply Z.divide_0_r; try apply Z.divide_1_l);
        intros i o INo;
        exfalso;
        repeat (destruct INo as [ D | INo ]; [ discriminate D | ]);
        exact INo. }
    unfold Semantics.init_state in INITstate.
    destruct (Lemmas.alloc_globals_slots _ _ _ (wt_prog_defs_sbinds WTp) INITstate)
      as ( slots & FWD & INDEFS & _ & NDA & NDI ).
    assert (SYMB: forall id gv, In (id, AST.Gvar gv) prog.(prog_defs) ->
               Genv.find_symbol (Genv.globalenv (Prog.program_of_program prog)) id
               = Some (glob_block id)
               /\ Genv.find_var_info (Genv.globalenv (Prog.program_of_program prog))
                    (glob_block id) = Some gv).
    { intros id gv IN.
      assert (DM: (AST.prog_defmap (Prog.program_of_program prog)) ! id
                  = Some (AST.Gvar gv))
        by (apply AST.prog_defmap_norepet; [ exact NOREPET | exact IN ]).
      destruct (proj1 (Genv.find_def_symbol _ _ _) DM) as ( b & FS & FD ).
      unfold glob_block; rewrite FS.
      split; [ reflexivity | now apply Genv.find_var_info_iff ]. }
    assert (GLOB: forall id gv, In (id, AST.Gvar gv) prog.(prog_defs) ->
               Genv.load_store_init_data (Genv.globalenv (Prog.program_of_program prog))
                 m0 (glob_block id) 0 gv.(AST.gvar_init)
               /\ Memory.Mem.range_perm m0 (glob_block id) 0
                    (Z.of_nat memword_bytes) Memtype.Cur Memtype.Writable).
    { intros id gv IN.
      destruct (SYMB id gv IN) as ( FS & FVI ).
      pose proof (WTgv := WTGV id gv IN).
      destruct (Genv.init_mem_characterization _ _ FVI INITMEM)
        as ( RP & _ & LSID & _ ).
      rewrite (Prog.Facts.wt_globvar_init_size WTgv) in RP.
      unfold Genv.perm_globvar in RP.
      rewrite (wt_globvar_volatile WTgv), (wt_globvar_readonly WTgv) in RP.
      split; [ exact (LSID (wt_globvar_volatile WTgv)) | exact RP ]. }
    destruct (Lemmas.alloc_globals_state
                (s := (emp_state: Sm)) (k := 0)
                ltac:(unfold emp_state; exact (scnt_emp_with_alc _ _)) INITstate)
      as ( EHEAP & _ & _ ).
    exists m0, (CCInj.Build_injection Ad [] (glob_st_map slots) []).
    split; [ exact INITMEM | ].
    constructor; cbn [CCInj.inj_hp_map CCInj.inj_st_map CCInj.inj_fn_map].
    - constructor.
    - apply glob_st_map_sbinds2; [ | exact NDA | exact NDI ].
      intros a1 id1 v1 a2 id2 v2 IN1 IN2 NE.
      destruct (INDEFS a1 id1 v1 IN1) as ( gv1 & INd1 & _ ).
      destruct (INDEFS a2 id2 v2 IN2) as ( gv2 & INd2 & _ ).
      exact (Genv.global_addresses_distinct _ NE
               (proj1 (SYMB id1 gv1 INd1)) (proj1 (SYMB id2 gv2 INd2))).
    - constructor.
    - intros ? ? ? ? ? ? ? ? [].
    - intros ? ? ? ? ? ? [].
    - intros ? ? ? ? ? ? _ [].
    - intros bl o v SUB; exfalso.
      rewrite EHEAP in SUB; unfold emp_state in SUB.
      rewrite heap_emp_with_alc in SUB.
      exact (emp_no_sub _ v SUB).
    - intros a v SUB.
      destruct (FWD a v SUB) as [ SUB0 | ( id & INsl ) ].
      { exfalso; unfold emp_state in SUB0.
        rewrite store_emp_with_alc in SUB0.
        exact (emp_no_sub a v SUB0). }
      destruct (INDEFS a id v INsl) as ( gv & INdefs & EVAL ).
      exists (glob_block id), 0%nat, false; split.
      + exact (in_map (fun x => (fst x, (glob_block (fst (snd x)), 0%nat, false)))
                 slots (a, (id, v)) INsl).
      + destruct (GLOB id gv INdefs) as ( LSID & _ ).
        intros mc MC.
        change (CCInj.offset_to_offset (Z.of_nat 0)) with 0%Z.
        exact (global_init_content (WTGV id gv INdefs) LSID EVAL mc MC).
    - intros ? ? [].
    - intros ? ? ? BIND; inversion BIND.
    - intros ? ? ? ? BIND; inversion BIND.
    - intros bl o v b' sz live SUB _; exfalso.
      rewrite EHEAP in SUB; unfold emp_state in SUB.
      rewrite heap_emp_with_alc in SUB.
      exact (emp_no_sub _ v SUB).
    - intros a b o freeable IN.
      unfold glob_st_map in IN.
      destruct (proj1 (in_map_iff _ _ _) IN) as ( [ a' [ id' v' ] ] & EQ & INsl ).
      cbn in EQ.
      destruct (INDEFS a' id' v' INsl) as ( gv & INdefs & _ ).
      destruct (GLOB id' gv INdefs) as ( _ & RP ).
      assert (EB: b = glob_block id') by congruence.
      assert (EO: o = 0%nat) by congruence.
      assert (EF: freeable = false) by congruence.
      subst b o freeable.
      change (CCInj.offset_to_offset (Z.of_nat 0)) with 0%Z.
      exact RP.
    - intros ? ? ? ? ? [].
  Qed.

  Lemma transl_initial_states [S] (INIT: @Semantics.initial_state Sm prog S)
    : exists R, Cminor.initial_state tprog R /\ @match_states Sm prog S R.
  Proof using TRANSL.
    pose proof (Lemmas.wt_initial_state INIT) as WTinit.
    destruct INIT as [ ge b fd s0 WTp GE INITstate FINDsymbol FINDfunct_ptr FUNSIG ];
      subst.
    destruct (function_ptr_translated TRANSL FINDfunct_ptr) as ( cu & tf & FINDfunct_ptr' & MATCHfd & LINK ).
    destruct (init_state_correct_mem WTp INITstate) as ( m0 & inj0 & INITmem & WFINJ0 ).
    exists (Cminor.Callstate tf [] Cminor.Kstop m0).
    split.
    - eapply Cminor.initial_state_intro with (b := b).
      + eapply (Genv.init_mem_match TRANSL); eassumption.
      + now rewrite (match_program_main TRANSL), (symbols_preserved TRANSL).
      + exact FINDfunct_ptr'.
      + rewrite Lemmas.signature_main;
          eapply sig_preserved_match; eassumption.
    - pose proof (WTdefs := Prog.Facts.wt_prog_defs_Forall Typing.wt_cmd_incl_global_stack _ WTp).
      destruct WTp as [ _ INpublic [fd_main INmain] SBINDSdefs _ ].
      specialize (proj1 (Forall_forall _ _) WTdefs _ INmain) as WTmain;
        cbn in WTmain.
      inversion WTmain as [ ?ctx ?id ?f WTfmain | ]; subst.
      assert (fd = fd_main).
      {
        assert (FINDdef : Genv.find_def (Genv.globalenv prog) b = Some (AST.Gfun fd))
          by
          (unfold Genv.find_funct_ptr in FINDfunct_ptr;
           destruct (Genv.find_def (Genv.globalenv prog) b) as [[f|]|];
           congruence).
        assert (DEFMAPfd : (AST.prog_defmap prog) ! (prog_main prog) = Some (AST.Gfun fd))
          by (apply Genv.find_def_symbol; eauto).
        assert (DEFMAPfd_main : (AST.prog_defmap prog) ! (prog_main prog) = Some (AST.Gfun fd_main)).
        { apply AST.prog_defmap_norepet.
          - apply ListExt.SIns_list_norepet.
            now apply ListExt.SBinds_map_fst_SIns.
          - exact INmain. }
        congruence.
      }
      subst fd.
      destruct (match_fundef_linkorder LINK MATCHfd) as ( idm & idf & DECLm & DECLf & ETF ).
      eapply match_callstate with (idm := idm) (idf := idf) (idm' := idm) (idf' := idf).
      + exact WTinit.
      + exact WFINJ0.
      + symmetry; exact ETF.
      + constructor.
      + now repeat constructor.
      + exact DECLm.
      + exact DECLf.
  Qed.

  Lemma transl_final_states: forall s1 s2 r,
      match_states prog s1 s2 -> Smallstep.final_state (@Semantics.semantics Sm prog) s1 r ->
      Smallstep.final_state (Cminor.semantics tprog) s2 r.
  Proof using TRANSL.
    cbn.
    intros s1 s2 r MS FINAL.
    destruct FINAL as [r s ].
    inversion MS as [ | | ?idm ?idf ?r ?k ?m ?s ?inj ?tr ?tk WT WFINJ [ EQr | VALCC ] MC ]; [ discriminate | subst ].
    inversion VALCC; subst.
    inversion MC; subst.
    rewrite <- EQ, Int.repr_unsigned.
    econstructor.
  Qed.

  Lemma match_args_has_argtype [inj: CCInj.injection Ad] [args: list Vl] [targs] [ts]
    (MARGS: match_args inj args targs)
    (WTARGS: Forall2 (@Value.wt_value Ad Pt) args ts)
    : Values.Val.has_argtype_list targs
        (List.map CCInj.type_to_xtype (List.filter Types.sized ts)).
  Proof using Type.
    revert ts WTARGS.
    induction MARGS as [ | ?v_args ?tv_args MARGS IH | ?v_arg ?tv_arg ?v_args ?tv_args MARGS IH INJ ];
      intros ts WTARGS;
      inversion WTARGS as [ | ?v ?t ?vs ?ts' WTv WTvs ]; subst; cbn.
    - constructor.
    - inversion WTv; subst; cbn.
      apply IH; exact WTvs.
    - assert (SZ: Types.Sized t) by exact (wt_value_sized WTv (value_compcert_sized INJ)).
      destruct SZ; cbn;
        (constructor; [ exact (inj_has_argtype WTv INJ eq_refl) | apply IH; exact WTvs ]).
  Qed.

  Theorem transl_step_correct:
    wt_program prog ->
    forall (S1 : Semantics.state) (t : Events.trace) (S2 : Semantics.state),
      Semantics.step (Genv.globalenv (Prog.program_of_program prog)) S1 t S2 ->
      forall T1 : Cminor.state,
        match_states prog S1 T1 ->
        exists (SN : Semantics.state) (T2 : Cminor.state),
          Smallstep.star (@Semantics.step Sm) (Genv.globalenv (Prog.program_of_program prog)) S2 Events.E0 SN /\
            Smallstep.plus Cminor.step (Genv.globalenv tprog) T1 t T2 /\ @match_states Sm prog SN T2.
  Proof using TRANSL.
    intros WTp S1 t S2 STEP.
    inversion STEP; subst.

    - intros T1 MS.
      inversion MS; subst;
        inversion WT; subst.
      inversion State_wt_cmd; subst.
      cbn [transl_cmd] in *.
      eexists ?[SN], ?[T2].
      split; [ eapply Smallstep.star_refl | split ].
      eapply Smallstep.plus_one; apply Cminor.step_seq.
      eapply match_state with (ctx := ctx).
      + exact (Lemmas.bind_next_state_wt WT).
      + exact WFINJ.
      + constructor; [ exact STACKBL | apply match_cont_Kbind_Kseq; exact STACKBL.(MSBcont) ].
      + reflexivity.
      + exact MCTXT.
      + exact DECLm.
      + exact DECLf.
    - eapply transl_builtin_correct; now eauto.
    - eapply transl_builtin_correct; now eauto.
    - intros T1 MS.
      inversion MS; subst.
      pose proof STACKBL as FR; destruct FR as [ [ [ WTSTACK LOCALSSZ LAYERED STACKBLMAP ] MTEMPS ] MK ].
      inversion WT; subst.
      inversion State_wt_cmd ; subst.
      2: {
        inversion MCTXT as ( Eglob_ctxt ).
        cbn [transl_cmd] in *.
        specialize (transl_args_correct WTargs State_wt_env MTEMPS EVALargs)
          as ( tv_args & EVALargs' & INJARGS ).
        specialize (EVALargs' (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
        specialize (function_ptr_translated TRANSL FINDfunct)
          as ( cu & tfd & FINDFUNCT & MFD & LINKORDER ).
        rewrite <- Genv.find_funct_find_funct_ptr in FINDFUNCT.
        pose proof (Ctxt.Facts.get_global_find_funct_ptr_inv Eglob_ctxt FINDfn FINDsymb FINDfunct)
          as EQ; subst fd.
        assert (H: exists target, Semantics.seq_cont_target k target)
          by (inversion CONTseq; eexists; constructor);
          destruct H as (target_id & SEQTARGET).
        eexists ?[SN], ?[T2].
        split; [ eapply Smallstep.star_refl | split ].
        eapply Smallstep.plus_one.
        + unfold make_call;
            erewrite Semantics.Facts.seq_cont_target_cont_target; [ | now eauto ].
          eapply Cminor.step_call with ( fd := tfd ).
          * unfold global_ptr; constructor; cbn; reflexivity.
          * apply EVALargs'.
          * unfold Genv.symbol_address.
            now rewrite (symbols_preserved TRANSL), FINDsymb,
              Genv.find_funct_find_funct_ptr.
          * eapply @wt_app_make_signature_correct with
              (prog := prog) (ctx := ctx) (f_id := id); now eauto.
        + destruct MFD as ( idmc & idfc & _ & _ & -> ).
          eapply match_callstate
            with (idm := idm) (idf := idf) (idm' := idm) (idf' := idf);
            [ | | reflexivity | now eauto | | exact DECLm | exact DECLf ].
          -- exact (Lemmas.wt_Callstate_app WTp Eglob_ctxt WT FINDfn EVALargs).
          -- exact WFINJ.
          -- eapply match_cont_Kcall with (idm' := idm) (idf' := idf); eauto; [ | exact STACKBL ].
             cbn.
             rewrite (Lemmas.wt_State_seq_target_sfind WT SEQTARGET).
             now destruct t.
      }
      inversion MCTXT as ( Eglob_ctxt ).
      cbn [transl_cmd] in *.
      specialize (transl_args_correct ltac:(eauto) State_wt_env MTEMPS EVALargs) as ( tv_args & EVALargs' & INJARGS ).
      specialize (EVALargs' (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      specialize (function_ptr_translated TRANSL FINDfunct) as ( cu & tfd & FINDFUNCT & MFD & LINKORDER ).
      rewrite <- Genv.find_funct_find_funct_ptr in FINDFUNCT.
      assert (EQ: fd = AST.Internal fn0)
        by exact (Ctxt.Facts.get_global_find_funct_ptr_inv Eglob_ctxt FINDfn FINDsymb FINDfunct);
        subst fd.
      assert (H: exists target, Semantics.seq_cont_target k target)
        by (inversion CONTseq; eexists; constructor);
        destruct H as (target_id & SEQTARGET).
      subst.
      eexists ?[SN], ?[T2].
      split; [ eapply Smallstep.star_refl | split ].
      eapply Smallstep.plus_one.
      + unfold make_call; erewrite Semantics.Facts.seq_cont_target_cont_target; [ | now eauto ].
        eapply Cminor.step_call with ( fd := tfd ).
        * unfold global_ptr.
          constructor; cbn.
          reflexivity.
        * apply EVALargs'.
        * unfold Genv.symbol_address.
          now rewrite (symbols_preserved TRANSL), FINDsymb, Genv.find_funct_find_funct_ptr.
        * eapply @wt_app_make_signature_correct with
            (prog := prog) (ctx := ctx) (f_id := id); now eauto.
      + destruct (match_fundef_linkorder LINKORDER MFD) as ( idmc & idfc & DECLmc & DECLfc & ETFD ).
        eapply match_callstate
          with (idm := idmc) (idf := idfc) (idm' := idm) (idf' := idf);
          [ | | | now eauto | | exact DECLmc | exact DECLfc ].
        -- exact (Lemmas.wt_Callstate_app WTp Eglob_ctxt WT FINDfn EVALargs).
        -- exact WFINJ.
        -- symmetry; exact ETFD.
        -- eapply match_cont_Kcall with (idm' := idm) (idf' := idf); eauto; [ | exact STACKBL ].
           cbn.
           rewrite (Lemmas.wt_State_seq_target_sfind WT SEQTARGET).
           now destruct (fn_return fn0).
    - intros T1 MS.
      inversion MS; subst.
      pose proof STACKBL as FR; destruct FR as [ [ [ WTSTACK LOCALSSZ LAYERED STACKBLMAP ] MTEMPS ] MK ].
      inversion WT; subst.
      inversion State_wt_cmd; subst.
      2: {
        inversion MCTXT as ( Eglob_ctxt ).
        cbn [transl_cmd] in *.
        specialize (transl_args_correct WTargs State_wt_env MTEMPS EVALargs)
          as ( tv_args & EVALargs' & INJARGS ).
        specialize (EVALargs' (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
        specialize (function_ptr_translated TRANSL FINDfunct)
          as ( cu & tfd & FINDFUNCT & MFD & LINKORDER ).
        rewrite <- Genv.find_funct_find_funct_ptr in FINDFUNCT.
        pose proof (Ctxt.Facts.get_global_find_funct_ptr_inv Eglob_ctxt FINDfn FINDsymb FINDfunct)
          as EQ; subst fd.
        destruct (pop_stack_block_wf WFINJ STACKBL POPSTACK)
          as ( m' & inj' & FREE & EHP & WFINJ' & POPNEW & POPKEEP ).
        rewrite make_call_call_cont; auto.
        eexists ?[SN], ?[T2].
        split; [ eapply Smallstep.star_refl | split ].
        eapply Smallstep.plus_one.
        + eapply Cminor.step_tailcall with ( fd := tfd ).
          * unfold global_ptr; constructor; cbn; reflexivity.
          * apply EVALargs'.
          * unfold Genv.symbol_address.
            now rewrite (symbols_preserved TRANSL), FINDsymb,
              Genv.find_funct_find_funct_ptr.
          * eapply @wt_app_make_signature_correct with
              (prog := prog) (ctx := ctx) (f_id := f_id); now eauto.
          * simpl_pop_stack.
            erewrite stackspace_preserved by exact MS.
            exact FREE.
        + destruct MFD as ( idmc & idfc & _ & _ & -> ).
          eapply match_callstate
            with (inj := inj') (idm := idm) (idf := idf) (idm' := idm) (idf' := idf).
          -- exact (Lemmas.wt_Callstate_tailapp WTp Eglob_ctxt WT FINDfn EVALargs).
          -- exact WFINJ'.
          -- reflexivity.
          -- exact (match_args_impl
                      (fun v tv INJ => InjValue_hp_le (CCInj.inj_hp_le_eq EHP) INJ)
                      _ _ INJARGS).
          -- rewrite (Lemmas.pop_stack_base LAYERED LOCALSSZ POPSTACK).
             refine (match_cont_call_cont CONTcall
                       (match_cont_inj_map (st_top := base)
                          (CCInj.inj_hp_le_eq EHP) _ POPKEEP MK (substate_refl base))).
             intros b0 a0 o0 fl0 _ IN0; exact (POPNEW a0 b0 o0 fl0 IN0).
          -- exact DECLm.
          -- exact DECLf.
      }
      inversion MCTXT as ( Eglob_ctxt ).
      cbn [transl_cmd] in *.
      specialize (transl_args_correct ltac:(eauto) State_wt_env MTEMPS EVALargs) as ( tv_args & EVALargs' & INJARGS ).
      specialize (EVALargs' (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      specialize (function_ptr_translated TRANSL FINDfunct) as ( cu & tfd & FINDFUNCT & MFD & LINKORDER ).
      rewrite <- Genv.find_funct_find_funct_ptr in FINDFUNCT.
      assert (EQ: fd = AST.Internal fn0)
        by exact (Ctxt.Facts.get_global_find_funct_ptr_inv Eglob_ctxt FINDfn FINDsymb FINDfunct);
        subst fd.
      destruct (pop_stack_block_wf WFINJ STACKBL POPSTACK)
        as ( m' & inj' & FREE & EHP & WFINJ' & POPNEW & POPKEEP ).
      rewrite make_call_call_cont; auto.
      eexists ?[SN], ?[T2].
      split; [ eapply Smallstep.star_refl | split ].
      eapply Smallstep.plus_one.
      + eapply Cminor.step_tailcall with ( fd := tfd ).
        * unfold global_ptr.
          constructor; cbn.
          reflexivity.
        * apply EVALargs'.
        * unfold Genv.symbol_address.
          now rewrite (symbols_preserved TRANSL), FINDsymb, Genv.find_funct_find_funct_ptr.
        * eapply @wt_app_make_signature_correct with
            (prog := prog) (ctx := ctx) (f_id := f_id); now eauto.
        * simpl_pop_stack.
          erewrite stackspace_preserved by exact MS.
          exact FREE.
      + destruct (match_fundef_linkorder LINKORDER MFD) as ( idmc & idfc & DECLmc & DECLfc & ETFD ).
        eapply match_callstate
          with (inj := inj') (idm := idmc) (idf := idfc) (idm' := idm) (idf' := idf).
        -- exact (Lemmas.wt_Callstate_tailapp WTp Eglob_ctxt WT FINDfn EVALargs).
        -- exact WFINJ'.
        -- symmetry; exact ETFD.
        -- exact (match_args_impl
                    (fun v tv INJ => InjValue_hp_le (CCInj.inj_hp_le_eq EHP) INJ)
                    _ _ INJARGS).
        -- rewrite (Lemmas.pop_stack_base LAYERED LOCALSSZ POPSTACK).
           refine (match_cont_call_cont CONTcall
                     (match_cont_inj_map (st_top := base)
                        (CCInj.inj_hp_le_eq EHP) _ POPKEEP MK (substate_refl base))).
           intros b0 a0 o0 fl0 _ IN0; exact (POPNEW a0 b0 o0 fl0 IN0).
        -- exact DECLmc.
        -- exact DECLfc.
    - intros T1 MS.
      inversion MS; subst.
      pose proof STACKBL as FR; destruct FR as [ [ [ WTSTACK LOCALSSZ LAYERED STACKBLMAP ] MTEMPS ] MK ].
      inversion WT as [ _ WTcmd _ WTenv ]; subst.
      inversion WTcmd as [ | | ?ty_ctxt ?e ?c1 ?c2 ?t WTif ?WTthen ?WTelse | | | | | | | | | | | | | | ]; subst.
      cbn [transl_cmd] in *.
      specialize (transl_expr_progress WTif ltac:(discriminate) WTenv MTEMPS EVALif) as
        ( tv & TEVAL & INJtv ).
      specialize (TEVAL (Genv.globalenv tprog) (Values.Vptr sp Ptrofs.zero) m).
      eexists ?[SN], ?[T2].
      split; [ apply Smallstep.star_refl | split ].
      + apply Smallstep.plus_one; eapply Cminor.step_ifthenelse with (b := b); eauto with deep_gallinac.
      + destruct b;
          eapply match_state with (ctx := ctx) (t := t); try exact STACKBL; auto;
          first [ exact (Lemmas.if_next_state_wt true WT) | exact (Lemmas.if_next_state_wt false WT) ].
    - intros T1 MS.
      inversion MS; subst.
      pose proof STACKBL as FR; destruct FR as [ [ [ WTSTACK LOCALSSZ LAYERED STACKBLMAP ] MTEMPS ] MK ].
      inversion WT as [ _ WTcmd _ _ ]; subst.
      inversion WTcmd as [ | | | ?ty_ctxt ?c_cond ?c_body ?id_cond ?id_body WTcond ?WTbody | | | | | | | | | | | | | ] ; subst.
      cbn [transl_cmd] in *.
      unfold perform_then_ret_unsized.
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
      eapply match_state with (ctx := ctx) (t := Types.t_bool).
      + exact (Lemmas.while_next_state_wt WT).
      + exact WFINJ.
      + constructor; [ exact STACKBL | apply match_cont_Kloop1; exact MK ].
      + reflexivity.
      + exact MCTXT.
      + exact DECLm.
      + exact DECLf.
    - intros T1 MS.
      inversion MS; subst.
      inversion WT as [ | ?f ?args ?k ?s ?sig ?ctx WTp' WTfd WTcall WTKcont FUNSIG EGLOBc | ];
        subst.
      inversion WTfd as [ ?ctx ?func WTf | | ]; subst.
      cbn [Cminorgen.transl_fundef AST.transf_fundef].
      specialize (wt_fn_cmd WTf) as WTbody.
      assert (SBinds_temps: ListExt.SBinds fn.(fn_temps)) by (now inversion WTf).
      destruct (Memory.Mem.alloc m 0 (CCInj.offset_to_offset fn.(fn_extra).(fn_stackspace))) as [ m' sp ] eqn:ALLOCsp.
      eexists ?[SN], ?[T2].
      split; [ eapply Smallstep.star_refl | split ].
      assert (WTARGS: Forall2 (@Value.wt_value Ad Pt) args (List.map snd fn.(fn_params)))
        by (now inversion WTcall).
      + eapply Smallstep.plus_one; eapply Cminor.step_internal_function with (m' := m') (sp := sp); [ | | reflexivity ].
        * exact (match_args_has_argtype MARGS WTARGS).
        * apply ALLOCsp.
      + destruct (push_stack_block_wf WFINJ ALLOCsp LOCALS STACKBL)
          as ( inj' & EHP & WF' & STACKBL' & PUSHNEW & PUSHKEEP ).
        replace (Cminor.fn_body (transl_function idm idf fn))
          with (transl_cmd idm idf (Semantics.cont_target k) fn.(fn_body))
          by (rewrite (Semantics.Facts.call_cont_target CONTcall); reflexivity).
        eapply match_state with
          (inj := inj')
          (base := store s)
          (ctx := Prog.mk_function_ctxt fn.(fn_params) fn.(fn_temps) fn.(fn_internals)
                    (Prog.mk_glob_ctxt prog))
          (t := fn.(fn_return)).
        * exact (Lemmas.wt_State_call_internal WTfd WTcall FUNSIG WTKcont EGLOBc CONTcall).
        * exact WF'.
        * exact {| MSBenv := {| MSBshape := STACKBL';
                               MSBtemps := set_params_match_temps WTf WTcall
                                              (match_args_impl
                                                 (fun v tv INJ => InjValue_hp_le (CCInj.inj_hp_le_eq EHP) INJ)
                                                 _ _ MARGS) |};
                   MSBcont := match_cont_reindex CONTcall
                                (match_cont_inj_map (st_top := store s)
                                   (CCInj.inj_hp_le_eq EHP) PUSHNEW PUSHKEEP MK
                                   (substate_refl (store s))) |}.
        * reflexivity.
        * reflexivity.
        * exact DECLm.
        * exact DECLf.
    - intros T1 MS.
      inversion MS; subst.
      inversion MK; subst.

      inversion WT; subst;
        inversion WTcont; subst;
        inversion WTKCALL; subst.
      pose proof WTk as WTC.
      assert (WTF: wt_function
                     (Ctxt.with_internal (PTree.empty Empty_set) (Ctxt.with_pure (PTree.empty Empty_set)
                        (Ctxt.with_stack (@nil Empty_set)
                           (Ctxt.with_internal int_env
                              (Ctxt.with_pure ty_env
                                 (Ctxt.with_stack (List.map (fun _ => tt) locals)
                                    (Ctxt.with_pure (PTree.empty Empty_set)
                                       (Ctxt.with_stack (@nil Empty_set) ctx))))))))
                     fn)
        by (refine (Lemmas.wt_function_ctxt_eq_global _ WTFN); reflexivity).
      assert (SFIND: ListExt.sfind target_id0
                       ((fn.(fn_params) ++ fn.(fn_temps)) ++ fn.(fn_internals)) = Some t)
        by exact (Lemmas.seq_target_sfind WTk WTF WTENV FINT ST).
      inversion SEQresolve; subst;
        inversion ST; subst;
        inversion SEQtarget; subst;
        inversion MK0; subst;
        rewrite SFIND in OI.
      + eexists; eexists; split; [ apply Smallstep.star_refl | split ].
        * eapply Smallstep.plus_two;
            [ apply Cminor.step_return
            | apply Cminor.step_skip_seq
            | reflexivity ].
        * refine (kbind_next_state_match_parts WTC WTF WTENV FINT
                    WFINJ DECLm DECLf {| MSBenv := STACKBL; MSBcont := MK1 |}
                    EGLOB WTres _ OI).
          destruct MRET as [ EV | IV ]; [ right; exact EV | left; exact IV ].
      + pose proof (Value.Facts.type_of_value_complete WTres) as ET;
          cbn [Value.type_of_value] in ET; subst t.
        cbn in OI; subst optid.
        destruct MRET as [ EV | IV ]; [ discriminate EV | ].
        destruct (kloop1_next_state_set (tge := Genv.globalenv tprog)
                    WTC WTF WTENV FINT WFINJ DECLm DECLf {| MSBenv := STACKBL; MSBcont := MK1 |} EGLOB IV)
          as ( T2 & PLUS & MATCH ).
        eexists; exists T2; split; [ apply Smallstep.star_refl | split ].
        * eapply Smallstep.plus_left;
            [ apply Cminor.step_return
            | apply Smallstep.plus_star; exact PLUS
            | reflexivity ].
        * exact MATCH.
      + pose proof (Value.Facts.type_of_value_complete WTres) as ET;
          cbn [Value.type_of_value] in ET; subst t.
        cbn in OI; subst optid.
        destruct (kloop2_next_state (tge := Genv.globalenv tprog)
                    WTC WTF WTENV FINT WFINJ DECLm DECLf {| MSBenv := STACKBL; MSBcont := MK1 |} EGLOB)
          as ( T2 & PLUS & MATCH ).
        eexists; exists T2; split; [ apply Smallstep.star_refl | split ].
        * eapply Smallstep.plus_left;
            [ apply Cminor.step_return
            | apply Smallstep.plus_star; exact PLUS
            | reflexivity ].
        * exact MATCH.
  Qed.

  Theorem transl_program_correct:
    Smallstep.forward_simulation (@Semantics.semantics Sm prog) (Cminor.semantics tprog).
  Proof using TRANSL.
    eapply Smallstep.forward_simulation_determ_plus
      with (match_states := fun S T => wt_program prog /\ match_states prog S T).
    - apply Lemmas.determinate.
    - apply senv_preserved.
    - intros S1 INIT.
      destruct (transl_initial_states INIT) as ( R & INITt & MATCH ).
      exists R; split;
        [ exact INITt
        | split; [ exact (Lemmas.initial_wt_program INIT) | exact MATCH ] ].
    - intros s1 s2 r ( _ & MATCH ) FINAL.
      exact (transl_final_states s1 s2 r MATCH FINAL).
    - cbn.
      intros S1 t S2 STEP T1 ( WTPX & MS ).
      specialize (transl_step_correct WTPX S1 t S2 STEP T1 MS)
        as ( S3 & T2 & STAR & PLUS & MS' ).
      exists S3, T2.
      split; [ exact STAR | split; [ exact PLUS | split ] ];
        [ exact WTPX | exact MS' ].
  Qed.

End TRANSLATION.

Section Link.

  Local Transparent Linker.Linker_fundef Linking.Linker_fundef.

  Local Lemma link_match_fundef (ctx1 ctx2: program) (f1: IR.Prog.fundef) (tf1: Cminor.fundef)
    (f2: IR.Prog.fundef) (tf2: Cminor.fundef) (f: IR.Prog.fundef)
    (LINK: Linking.link f1 f2 = Some f)
    (MF1: match_fundef ctx1 f1 tf1) (MF2: match_fundef ctx2 f2 tf2)
    : exists tf, Linking.link tf1 tf2 = Some tf /\ (match_fundef ctx1 f tf \/ match_fundef ctx2 f tf).
  Proof.
    destruct MF1 as ( m1 & fr1 & D1 & E1 & -> ), MF2 as ( m2 & fr2 & D2 & E2 & -> ).
    destruct f1 as [ fn1 | ef1 ], f2 as [ fn2 | ef2 ]; cbn in LINK |- *.
    - discriminate LINK.
    - destruct ef2; try discriminate LINK; injection LINK as <-.
      eexists; split; [ reflexivity | left; exists m1, fr1; auto ].
    - destruct ef1; try discriminate LINK; injection LINK as <-.
      eexists; split; [ reflexivity | right; exists m2, fr2; auto ].
    - destruct (AST.external_function_eq ef1 ef2) as [ <- | NE ]; [ | discriminate LINK ].
      injection LINK as <-.
      eexists; split;
        [ cbn; destruct (AST.external_function_eq ef1 ef1) as [ _ | NE ];
          [ reflexivity | contradiction NE; reflexivity ]
        | left; exists m1, fr1; auto ].
  Qed.

  Local Lemma link_match_varinfo (v1: vardef) (tv1: unit) (v2: vardef) (tv2: unit) (v: vardef)
    (LINK: Linking.link v1 v2 = Some v)
    (MV1: match_varinfo v1 tv1) (MV2: match_varinfo v2 tv2)
    : exists tv, Linking.link tv1 tv2 = Some tv /\ match_varinfo v tv.
  Proof.
    exists tt; split; [ reflexivity | exact I ].
  Qed.

  Global Instance TransfCminorgenLink: TransfLink match_prog.
  Proof.
    intros p1 p2 tp1 tp2 p LINK MATCH1 MATCH2.
    destruct (Linking.link_linkorder _ _ _ LINK) as [ LO1 LO2 ].
    exact (Linking.link_match_program match_fundef match_varinfo
             link_match_fundef link_match_varinfo
             p1 p2 p _ _ _ _ _ (Linker.link_program_inv LINK)
             MATCH1 MATCH2 LO1 LO2).
  Qed.

End Link.
