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

From Stdlib Require Import ZArith PArith Arith List Psatz.
Import ListNotations.

From compcert.common Require Globalenvs.
From compcert.common Require Import Errors.
From compcert.lib Require Import Maps.

From HB Require Import structures.

From GallinaC.Utils Require ReflectExt.
From GallinaC.Utils Require Import ListExt NExt CompCertExt Algebra.

From GallinaC.Imp Require Import Intops.
From GallinaC.Imp Require Import Store Heap Storable State.

From GallinaC.Compiler.Common Require CCInj Value Linker.
From GallinaC.Compiler.Common Require Import Types Ctxt Expr.
From GallinaC.Compiler.Common Require Import Semantics.
From GallinaC.Compiler.Deep Require Typing OpSem Lemmas.
From GallinaC.Compiler.Deep Require Import Cmd Prog Linker.
From GallinaC.Compiler.IR Require Prog Cmd Typing Semantics Lemmas.
From GallinaC.Compiler.IR Require Import Linker.
From GallinaC.Compiler.Passes Require Import IRgen.
From GallinaC.Compiler.Passes Require Import IRgenspec.

Local Open Scope separation_scope.

Definition match_prog: program -> IR.Prog.program -> Prop := IRgenspec.match_prog.

Lemma transf_program_match:
  forall p tp, transl_program p = OK tp -> match_prog p tp.
Proof.
  intros p tp TRANSL.
  exact (IRgenspec.transf_program_match p tp TRANSL).
Qed.

Lemma match_program_main {p tp}:
  match_prog p tp -> AST.prog_main tp = Prog.prog_main p.
Proof.
  intros MATCHPROG.
  destruct MATCHPROG as ( _ & MAIN & _ ).
  auto.
Qed.

Section TRANSLATION.

  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).

  Section STORE_MATCH.

    Record stack_block := mkstack_block {
                        sb_deep: list Nm;
                        sb_ir: list Nm;
                        sb_ss: Z;
                      }.

    Record wf_stack_block (sb: stack_block): Prop :=
      mk_wf_stack_block {
          wf_sb_ir_len: List.length sb.(sb_ir) = Z.to_nat sb.(sb_ss);
          wf_sb_deep_le: (List.length sb.(sb_deep) <= List.length sb.(sb_ir))%nat;
        }.

    Lemma wf_stack_block_removelast_n [locals_d locals_i: list Nm] [ss: Z] (n: nat)
      (WF: wf_stack_block (mkstack_block locals_d locals_i ss)):
      wf_stack_block (mkstack_block (ListExt.removelast_n n locals_d) locals_i ss).
    Proof using Type.
      pose proof (wf_sb_deep_le _ WF) as DLE; cbn [sb_deep sb_ir] in DLE.
      constructor; cbn [sb_deep sb_ir sb_ss];
        [ exact (wf_sb_ir_len _ WF)
        | rewrite ListExt.length_removelast_n; lia ].
    Qed.

    Lemma wf_stack_block_app [locals_d locals_i: list Nm] [ss: Z] (l: list Nm)
      (WF: wf_stack_block (mkstack_block locals_d locals_i ss))
      (ROOM: (List.length locals_d + List.length l
              <= List.length locals_i)%nat):
      wf_stack_block (mkstack_block (locals_d ++ l) locals_i ss).
    Proof using Type.
      constructor; cbn [sb_deep sb_ir sb_ss];
        [ exact (wf_sb_ir_len _ WF)
        | rewrite List.length_app; exact ROOM ].
    Qed.

    Local Open Scope mem_scope.

    Fixpoint smatch (F: list stack_block) (st_d st_i: St): Prop :=
      match F with
      | [] => st_d = $0
      | sb :: F' =>
          exists st_d0 st_i0: St,
            smatch F' st_d0 st_i0
            /\ layered st_d0 sb.(sb_deep) st_d
            /\ layered st_i0 sb.(sb_ir) st_i
            /\ (forall n nm_d (DEREF: List.nth_error sb.(sb_deep) n = Some nm_d),
                 exists nm_i,
                   List.nth_error sb.(sb_ir) n = Some nm_i
                   /\ lookup st_d nm_d = lookup st_i nm_i)
      end.

    Local Close Scope mem_scope.

    Lemma smatch_init:
      forall (tp: IR.Prog.program) (s_i: Sm)
             (INIT: Semantics.init_state tp = Some s_i),
        smatch [] (store (emp_state: Sm)) (store s_i).
    Proof using Type.
      intros tp s_i INIT.
      exact (store_emp_with_alc _ _).
    Qed.

    Lemma smatch_stack_block_alloc:
      forall F (s_d s_i: Sm) SS
             (SM: smatch F (store s_d) (store s_i))
             (CNT: exists k, scnt s_i = Owned (mk_cnt k None))
             (NONNEG: (0 <= SS)%Z),
      exists st sg locals,
        stack_block_alloc (encode (v_tt: Vl)) (Z.to_N SS) (store s_i) (scnt s_i)
        = Some (st, sg, locals)
        /\ List.length locals = Z.to_nat SS
        /\ dominates st sg
        /\ (exists k, sg = Owned (mk_cnt k None))
        /\ smatch (mkstack_block [] locals SS :: F) (store s_d) st.
    Proof using Type.
      intros F s_d s_i SS SM ( k0 & ECNT ) NONNEG.
      assert (DOM0: dominates (store s_i) (Owned (mk_cnt k0 None): SCnt Sm))
        by (rewrite <- ECNT; exact (state_store_dominates s_i)).
      destruct (stack_block_alloc_some DOM0 (encode (v_tt: Vl)) (Z.to_N SS))
        as ( st & sg & locals & ITER ).
      destruct (stack_block_alloc_inv DOM0 (encode (v_tt: Vl)) _ _ _ _ ITER)
        as ( LEN & DOM & LAYERED & _ ).
      pose proof (stack_block_alloc_cnt _ _ ITER) as ECNT'.
      rewrite <- ECNT in ITER.
      exists st, sg, locals.
      split; [ exact ITER | ].
      split; [ rewrite LEN; exact (Z_N_nat SS) | ].
      split; [ exact DOM | split; [ exact ECNT' | ] ].
      cbn [smatch]; exists (store s_d), (store s_i).
      cbn [sb_deep sb_ir sb_ss].
      split; [ exact SM | split; [ exact (layered_nil (store s_d)) | ] ].
      split; [ exact LAYERED | ].
      intros n0 nm_d DEREF; destruct n0; discriminate.
    Qed.

    Lemma smatch_push_withvar:
      forall sb F (s_d: Sm) st_i (v: Vl) st_d sg_d nm
             (SM: smatch (sb :: F) (store s_d) st_i)
             (WF: wf_stack_block sb)
             (ROOM: (List.length sb.(sb_deep) < List.length sb.(sb_ir))%nat)
             (PUSH: push (store s_d) (scnt s_d) (encode v) = Some (st_d, sg_d, nm)),
      exists nm_i st_i',
        List.nth_error sb.(sb_ir) (List.length sb.(sb_deep)) = Some nm_i
        /\ mutate st_i nm_i (encode v) = Some st_i'
        /\ smatch (mkstack_block (sb.(sb_deep) ++ [nm]) sb.(sb_ir) sb.(sb_ss) :: F)
             st_d st_i'.
    Proof using Type.
      intros sb F s_d st_i v st_d sg_d nm SM WF ROOM PUSH.
      cbn [smatch] in SM.
      destruct SM as ( st_d0 & st_i0 & SMf & LAYd & LAYi & AGREE ).
      destruct (proj2 (push_some (store s_d) (scnt s_d) (encode v))
                  (ex_intro _ st_d (ex_intro _ sg_d (ex_intro _ nm PUSH))))
        as ( k & CGET & _ ).
      destruct (push_mem (store s_d) (scnt s_d) (encode v) st_d sg_d nm k PUSH CGET)
        as ( REFn & WRTn & SUMn ).
      destruct (List.nth_error sb.(sb_ir) (List.length sb.(sb_deep)))
        as [ nm_i | ] eqn:NTHi.
      2: { exfalso.
           pose proof (proj1 (List.nth_error_None _ _) NTHi) as LEN; lia. }
      destruct (layered_replace LAYi (List.length sb.(sb_deep)) nm_i NTHi (encode v))
        as ( st_i' & MUTi & LAYi' ).
      exists nm_i, st_i'; split; [ reflexivity | split; [ exact MUTi | ] ].
      pose proof (dominates_block_lt CGET (state_store_dominates s_d)
                    (mkAddr_block k 0%N)) as BLKn.
      destruct (layered_nth LAYi (List.length sb.(sb_deep)) nm_i NTHi)
        as ( ai1 & wi1 & REFi1 & WRTi1 & _ ).
      cbn [smatch]; exists st_d0, st_i0.
      cbn [sb_deep sb_ir sb_ss].
      split; [ exact SMf | split; [ | split; [ exact LAYi' | ] ] ].
      - exact (layered_snoc st_d0 sb.(sb_deep) (store s_d) nm (mkAddr k 0%N)
                                       (encode v) st_d LAYd REFn WRTn BLKn SUMn).
      - intros n0 nm_d DEREF.
        destruct (nth_error_snoc_inv DEREF)
          as [ INl | ( ELEN & ENMD ) ].
        + destruct (AGREE n0 nm_d INl) as ( nm_i0 & NTHi0 & AGRn ).
          exists nm_i0; split; [ exact NTHi0 | ].
          destruct (layered_nth LAYd n0 nm_d INl) as ( ad & wd & REFd & _ & CELLd ).
          destruct (layered_nth LAYi n0 nm_i0 NTHi0) as ( ai & wi & REFi & _ & _ ).
          assert (LTn: (n0 < List.length sb.(sb_deep))%nat)
            by (apply (proj1 (List.nth_error_Some _ _)); rewrite INl; discriminate).
          assert (NEPOS: n0 <> List.length sb.(sb_deep)) by lia.
          rewrite (lookup_mutate_other MUTi REFi1 REFi
                     (layered_addr_neq LAYi NTHi0 REFi NTHi REFi1 NEPOS)).
          rewrite <- AGRn.
          exact (lookup_mono (substate_of_partition_r SUMn) REFd CELLd).
        + subst nm_d.
          exists nm_i; split; [ rewrite ELEN; exact NTHi | ].
          rewrite (push_lookup_fresh (store s_d) st_d (scnt s_d) sg_d (encode v)
                     nm PUSH).
          rewrite (lookup_mutate_self MUTi
                     (allows_le nm_i Operation.Read Operation.Write
                        Operation.le_read_write WRTi1)).
          reflexivity.
    Qed.

    Lemma smatch_lookup:
      forall sb F (st_d st_i: St) n nm_d mv
             (SM: smatch (sb :: F) st_d st_i)
             (DEREF: List.nth_error sb.(sb_deep) n = Some nm_d)
             (LOOKUP: lookup st_d nm_d = Some mv),
      exists nm_i,
        List.nth_error sb.(sb_ir) n = Some nm_i
        /\ lookup st_i nm_i = Some mv.
    Proof using Type.
      intros sb F st_d st_i n nm_d mv SM DEREF LOOKUP.
      cbn [smatch] in SM.
      destruct SM as ( st_d0 & st_i0 & _ & _ & _ & AGREE ).
      destruct (AGREE n nm_d DEREF) as ( nm_i & NTHi & AGRn ).
      exists nm_i; split; [ exact NTHi | rewrite <- AGRn; exact LOOKUP ].
    Qed.

    Lemma smatch_mutate:
      forall sb F (st_d st_i: St) n nm_d mv st_d'
             (SM: smatch (sb :: F) st_d st_i)
             (DEREF: List.nth_error sb.(sb_deep) n = Some nm_d)
             (MUTATE: mutate st_d nm_d mv = Some st_d'),
      exists nm_i st_i',
        List.nth_error sb.(sb_ir) n = Some nm_i
        /\ mutate st_i nm_i mv = Some st_i'
        /\ smatch (sb :: F) st_d' st_i'.
    Proof using Type.
      intros sb F st_d st_i n nm_d mv st_d' SM DEREF MUTATE.
      cbn [smatch] in SM.
      destruct SM as ( st_d0 & st_i0 & SMf & LAYd & LAYi & AGREE ).
      destruct (AGREE n nm_d DEREF) as ( nm_i & NTHi & _ ).
      destruct (layered_replace LAYd n nm_d DEREF mv) as ( st_d'' & MUTd & LAYd' ).
      assert (Est: st_d'' = st_d') by congruence; subst st_d''.
      destruct (layered_replace LAYi n nm_i NTHi mv) as ( st_i' & MUTi & LAYi' ).
      destruct (layered_nth LAYd n nm_d DEREF) as ( ad & wd & REFd & WRTd & _ ).
      destruct (layered_nth LAYi n nm_i NTHi) as ( ai & wi & REFi & WRTi & _ ).
      exists nm_i, st_i'; split; [ exact NTHi | split; [ exact MUTi | ] ].
      cbn [smatch].
      exists st_d0, st_i0.
      split; [ exact SMf | split; [ exact LAYd' | split; [ exact LAYi' | ] ] ].
      intros n0 nm_d0 DEREF0.
      destruct (AGREE n0 nm_d0 DEREF0) as ( nm_i0 & NTHi0 & EQ0 ).
      exists nm_i0; split; [ exact NTHi0 | ].
      destruct (Nat.eq_dec n0 n) as [ EPOS | NE ].
      - subst n0.
        assert (ENMD: nm_d0 = nm_d) by congruence; subst nm_d0.
        assert (ENMI: nm_i0 = nm_i) by congruence; subst nm_i0.
        rewrite (lookup_mutate_self MUTATE
                   (allows_le nm_d Operation.Read Operation.Write
                      Operation.le_read_write WRTd)).
        rewrite (lookup_mutate_self MUTi
                   (allows_le nm_i Operation.Read Operation.Write
                      Operation.le_read_write WRTi)).
        reflexivity.
      - destruct (layered_nth LAYd n0 nm_d0 DEREF0) as ( ad0 & _ & REFd0 & _ & _ ).
        destruct (layered_nth LAYi n0 nm_i0 NTHi0) as ( ai0 & _ & REFi0 & _ & _ ).
        rewrite (lookup_mutate_other MUTATE REFd REFd0
                   (layered_addr_neq LAYd DEREF0 REFd0 DEREF REFd NE)).
        rewrite (lookup_mutate_other MUTi REFi REFi0
                   (layered_addr_neq LAYi NTHi0 REFi0 NTHi REFi NE)).
        exact EQ0.
    Qed.

    Lemma smatch_pop_n:
      forall sb F (st_d st_i: St) n st_d'
             (SM: smatch (sb :: F) st_d st_i)
             (LE: (n <= List.length sb.(sb_deep))%nat)
             (POP: NExt.iter_opt (fun st => pop st) (N.of_nat n) st_d = Some st_d'),
        smatch (mkstack_block (ListExt.removelast_n n sb.(sb_deep))
                  sb.(sb_ir) sb.(sb_ss) :: F) st_d' st_i.
    Proof using Type.
      intros sb F st_d st_i n st_d' SM LE POP.
      cbn [smatch] in SM.
      destruct SM as ( st_d0 & st_i0 & SMf & LAYd & LAYi & AGREE ).
      destruct (layered_pop_n n sb.(sb_deep) st_d LAYd LE)
        as ( st_d'' & POPn & LAYd' & SUBd ).
      assert (Est: st_d'' = st_d') by congruence; subst st_d''.
      cbn [smatch]; exists st_d0, st_i0.
      cbn [sb_deep sb_ir sb_ss].
      split; [ exact SMf | split; [ exact LAYd' | split; [ exact LAYi | ] ] ].
      intros k nm_d DEREF.
      assert (LTk: (k < List.length sb.(sb_deep) - n)%nat).
      { assert (LTk0: (k < List.length (ListExt.removelast_n n sb.(sb_deep)))%nat)
          by (apply (proj1 (List.nth_error_Some _ _)); rewrite DEREF; discriminate).
        rewrite ListExt.length_removelast_n in LTk0; exact LTk0. }
      assert (DEREF0: List.nth_error sb.(sb_deep) k = Some nm_d)
        by (rewrite <- (nth_error_removelast_n n sb.(sb_deep) k LTk); exact DEREF).
      destruct (AGREE k nm_d DEREF0) as ( nm_i & NTHi & AGRk ).
      exists nm_i; split; [ exact NTHi | ].
      destruct (layered_nth LAYd' k nm_d DEREF) as ( ad & wd & REFd & _ & CELLd ).
      rewrite <- AGRk.
      exact (eq_sym (lookup_mono SUBd REFd CELLd)).
    Qed.

    Lemma smatch_pop_return:
      forall sb F (st_d st_i: St) st_d'
             (SM: smatch (sb :: F) st_d st_i)
             (WF: wf_stack_block sb)
             (POP: NExt.iter_opt (fun st => pop st) (N.of_nat (List.length sb.(sb_deep))) st_d
                   = Some st_d'),
      exists st_i',
        NExt.iter_opt (fun st => pop st) (Z.to_N sb.(sb_ss)) st_i = Some st_i'
        /\ smatch F st_d' st_i'.
    Proof using Type.
      intros sb F st_d st_i st_d' SM WF POP.
      cbn [smatch] in SM.
      destruct SM as ( st_d0 & st_i0 & SMf & LAYd & LAYi & AGREE ).
      destruct (layered_pop_n (List.length sb.(sb_deep)) sb.(sb_deep) st_d LAYd
                                                              (le_n _)) as ( st_d'' & POPn & LAYd' & _ ).
      assert (Est: st_d'' = st_d') by congruence; subst st_d''.
      assert (ENILD: ListExt.removelast_n (List.length sb.(sb_deep)) sb.(sb_deep) = [])
        by exact (ListExt.removelast_n_app_length [] sb.(sb_deep)).
      rewrite ENILD in LAYd'.
      destruct (layered_pop_n (List.length sb.(sb_ir)) sb.(sb_ir) st_i LAYi
                                                            (le_n _)) as ( st_i' & POPI & LAYi' & _ ).
      assert (ENILI: ListExt.removelast_n (List.length sb.(sb_ir)) sb.(sb_ir) = [])
        by exact (ListExt.removelast_n_app_length [] sb.(sb_ir)).
      rewrite ENILI in LAYi'.
      assert (EN: Z.to_N sb.(sb_ss) = N.of_nat (List.length sb.(sb_ir))).
      { rewrite (wf_sb_ir_len sb WF), <- Z_N_nat, N2Nat.id; reflexivity. }
      exists st_i'; split.
      - rewrite EN; exact POPI.
      - rewrite (layered_nil_inv LAYd' eq_refl), (layered_nil_inv LAYi' eq_refl).
        exact SMf.
    Qed.

  End STORE_MATCH.

  Variable prog: program.
  Variable tprog: IR.Prog.program.
  Hypothesis TRANSL: match_prog prog tprog.

  Inductive match_call_cont:
    @OpSem.cont Sm -> @Semantics.cont Sm -> list stack_block -> Prop :=
  | mcc_stop:
    match_call_cont OpSem.Kstop Semantics.Kstop []
  | mcc_call: forall floor' SS' ctx' d' fn tfn e_d e_i locals_d locals_i k tk F
                     (TRf: tr_function_at floor' fn tfn)
                     (STACKSPACE: SS' = tfn.(fn_extra).(IR.Prog.fn_stackspace))
                     (ENV: env_incl e_d e_i)
                     (EDOM: env_dom (fn.(fn_params) ++ fn.(fn_temps)) e_d)
                     (DLEN: d' = List.length locals_d)
                     (WF: wf_stack_block (mkstack_block locals_d locals_i SS'))
                     (WTfnd: Deep.Typing.wt_function
                               (to_glob_ctxt ctx') fn)
                     (WTed: OpSem.Typing.wt_env fn (ctxt_pure ctx') e_d)
                     (STACKd: ctxt_stack ctx' = List.map (fun _ => tt) locals_d)
                     (INTd: ctxt_internal ctx' = mk_typing_tree false fn.(fn_internals) Maps.PTree.Empty)
                     (GLOBd: Globalenvs.Genv.globalenv prog = ctxt_global ctx')
                     (MK: match_cont floor' SS' ctx' d' k tk F),
      match_call_cont
        (OpSem.Kcall fn e_d locals_d k)
        (Semantics.Kcall tfn e_i locals_i tk)
        (mkstack_block locals_d locals_i SS' :: F)

  with match_cont:
    AST.ident -> Z -> ctxt (type * bool) (type * bool) unit fundef vardef -> nat ->
    @OpSem.cont Sm -> @Semantics.cont Sm -> list stack_block -> Prop :=
  | mc_other: forall floor SS ctx k tk F
                     (STACK_EMPTY: ctxt_stack ctx = [])
                     (MKC: match_call_cont k tk F),
      match_cont floor SS ctx 0 k tk F
  | mc_bind: forall floor SS ctx d id t_b c tc t k tk F
                    (GET: Ctxt.get_pure id ctx = Some (t_b, false))
                    (TRc: tr_cmd floor SS (ctxt_pure (Ctxt.set_pure id (t_b, true) ctx)) d
                            (Semantics.is_call_contb tk) c tc t)
                    (MK: match_cont floor SS ctx d k tk F),
      match_cont floor SS ctx d
        (OpSem.Kbind id c k) (Semantics.Kbind id tc tk) F
  | mc_loop1: forall floor SS ctx d c_cond c_body tc_cond tc_body id_cond id_body k tk F
                     (FRESHc: (floor <= id_cond)%positive)
                     (FRESHb: (floor <= id_body)%positive)
                     (NEQ: id_cond <> id_body)
                     (TRcond: tr_cmd floor SS (ctxt_pure ctx) d false c_cond tc_cond t_bool)
                     (TRbody: tr_cmd floor SS (ctxt_pure ctx) d false c_body tc_body t_unit)
                     (MK: match_cont floor SS ctx d k tk F),
      match_cont floor SS ctx d
        (OpSem.Kloop1 c_cond c_body k)
        (Semantics.Kloop1 tc_cond id_cond tc_body id_body tk) F
  | mc_loop2: forall floor SS ctx d c_cond c_body tc_cond tc_body id_cond id_body k tk F
                     (FRESHc: (floor <= id_cond)%positive)
                     (FRESHb: (floor <= id_body)%positive)
                     (NEQ: id_cond <> id_body)
                     (TRcond: tr_cmd floor SS (ctxt_pure ctx) d false c_cond tc_cond t_bool)
                     (TRbody: tr_cmd floor SS (ctxt_pure ctx) d false c_body tc_body t_unit)
                     (MK: match_cont floor SS ctx d k tk F),
      match_cont floor SS ctx d
        (OpSem.Kloop2 c_cond c_body k)
        (Semantics.Kloop2 tc_cond id_cond tc_body id_body tk) F
  | mc_scope_unbind: forall floor SS ctx d id t k tk F
                            (GET: Ctxt.get_pure id ctx = Some (t, true))
                            (MK: match_cont floor SS (Ctxt.set_pure id (t, false) ctx) d k tk F),
      match_cont floor SS ctx d
        (OpSem.Kscope (OpSem.scope_bind id) k) tk F
  | mc_scope_pop: forall floor SS ctx d k tk F s0 sl0
                         (STACK_NONEMPTY: ctxt_stack ctx = s0 :: sl0)
                         (MK: match_cont floor SS
                                (Ctxt.with_stack (List.removelast (ctxt_stack ctx)) ctx) d k tk F),
      match_cont floor SS ctx (S d)
        (OpSem.Kscope OpSem.scope_store k) tk F
  .

  Inductive match_states:
    @OpSem.state Sm -> @Semantics.state Sm -> Prop :=
  | match_State: forall floor f c k e_d locals_d s_d
                        tf tc tk e_i locals_i s_i t t_d d ctx F
                        (WT: OpSem.Typing.wt_State f c k e_d locals_d s_d ctx t_d)
                        (GLOB: Globalenvs.Genv.globalenv prog = ctxt_global ctx)
                        (TRf: tr_function_at floor f tf)
                        (TRc: tr_cmd floor tf.(fn_extra).(IR.Prog.fn_stackspace) (ctxt_pure ctx) d
                                                           (Semantics.is_call_contb tk) c tc t)
                        (MK: match_cont floor tf.(fn_extra).(IR.Prog.fn_stackspace) ctx d k tk F)
                        (ENV: env_incl e_d e_i)
                        (EDOM: env_dom (f.(fn_params) ++ f.(fn_temps)) e_d)
                        (DLEN: d = List.length locals_d)
                        (WF: wf_stack_block
                               (mkstack_block locals_d locals_i tf.(fn_extra).(IR.Prog.fn_stackspace)))
                        (HEAP: heap s_d = heap s_i)
                        (ALC: alc s_d = alc s_i)
                        (CNT: exists n, scnt s_i = Owned (mk_cnt n None))
                        (SMATCH: smatch
                                   (mkstack_block locals_d locals_i
                                      tf.(fn_extra).(IR.Prog.fn_stackspace) :: F)
                                   (store s_d) (store s_i)),
      match_states
        (OpSem.State f c k e_d locals_d s_d)
        (Semantics.State tf tc tk e_i locals_i s_i)
  | match_Callstate: forall fd tfd args k tk s_d s_i F
                            (WT: OpSem.Typing.wt_state prog (OpSem.Callstate fd args k s_d))
                            (MFD: match_fundef fd tfd)
                            (MKC: match_call_cont k tk F)
                            (HEAP: heap s_d = heap s_i)
                            (ALC: alc s_d = alc s_i)
                            (CNT: exists n, scnt s_i = Owned (mk_cnt n None))
                            (SMATCH: smatch F (store s_d) (store s_i)),
      match_states
        (OpSem.Callstate fd args k s_d)
        (Semantics.Callstate tfd args tk s_i)
  | match_Returnstate: forall v k tk s_d s_i F
                              (WT: OpSem.Typing.wt_state prog (OpSem.Returnstate v k s_d))
                              (MKC: match_call_cont k tk F)
                              (HEAP: heap s_d = heap s_i)
                              (ALC: alc s_d = alc s_i)
                              (CNT: exists n, scnt s_i = Owned (mk_cnt n None))
                              (SMATCH: smatch F (store s_d) (store s_i)),
      match_states
        (OpSem.Returnstate v k s_d)
        (Semantics.Returnstate v tk s_i)
  .

  Lemma match_State_inv [f c k e_d locals_d s_d ts]
    (MS: match_states (OpSem.State f c k e_d locals_d s_d) ts):
    exists floor tf tc tk e_i locals_i s_i t t_d d ctx F,
      ts = Semantics.State tf tc tk e_i locals_i s_i
      /\ OpSem.Typing.wt_State f c k e_d locals_d s_d ctx t_d
      /\ Globalenvs.Genv.globalenv prog = ctxt_global ctx
      /\ tr_function_at floor f tf
      /\ tr_cmd floor tf.(fn_extra).(IR.Prog.fn_stackspace) (ctxt_pure ctx) d
                                      (Semantics.is_call_contb tk) c tc t
      /\ match_cont floor tf.(fn_extra).(IR.Prog.fn_stackspace) ctx d k tk F
      /\ env_incl e_d e_i
      /\ env_dom (f.(fn_params) ++ f.(fn_temps)) e_d
      /\ d = List.length locals_d
      /\ wf_stack_block
           (mkstack_block locals_d locals_i tf.(fn_extra).(IR.Prog.fn_stackspace))
      /\ heap s_d = heap s_i
      /\ alc s_d = alc s_i
      /\ (exists n, scnt s_i = Owned (mk_cnt n None))
      /\ smatch
           (mkstack_block locals_d locals_i
              tf.(fn_extra).(IR.Prog.fn_stackspace) :: F)
           (store s_d) (store s_i).
  Proof using Type.
    inversion MS; subst.
    eexists _, _, _, _, _, _, _, _, _, _, _, _.
    repeat apply conj; try reflexivity; eassumption.
  Qed.

  Lemma match_State_wt_state [f c k e_d locals_d s_d ts]
    (MS: match_states (OpSem.State f c k e_d locals_d s_d) ts):
    OpSem.Typing.wt_state prog (OpSem.State f c k e_d locals_d s_d).
  Proof using Type.
    inversion MS; subst.
    econstructor; eassumption.
  Qed.

  Lemma match_Callstate_inv [fd args k s_d ts]
    (MS: match_states (OpSem.Callstate fd args k s_d) ts):
    exists tfd tk s_i F,
      ts = Semantics.Callstate tfd args tk s_i
      /\ OpSem.Typing.wt_state prog (OpSem.Callstate fd args k s_d)
      /\ match_fundef fd tfd
      /\ match_call_cont k tk F
      /\ heap s_d = heap s_i
      /\ alc s_d = alc s_i
      /\ (exists n, scnt s_i = Owned (mk_cnt n None))
      /\ smatch F (store s_d) (store s_i).
  Proof using Type.
    inversion MS; subst.
    eexists _, _, _, _.
    repeat apply conj; try reflexivity; eassumption.
  Qed.

  Lemma match_Returnstate_inv [v k s_d ts]
    (MS: match_states (OpSem.Returnstate v k s_d) ts):
    exists tk s_i F,
      ts = Semantics.Returnstate v tk s_i
      /\ OpSem.Typing.wt_state prog (OpSem.Returnstate v k s_d)
      /\ match_call_cont k tk F
      /\ heap s_d = heap s_i
      /\ alc s_d = alc s_i
      /\ (exists n, scnt s_i = Owned (mk_cnt n None))
      /\ smatch F (store s_d) (store s_i).
  Proof using Type.
    inversion MS; subst.
    eexists _, _, _.
    repeat apply conj; try reflexivity; eassumption.
  Qed.

  Lemma match_cont_Kbind_inv [floor SS ctx d id c k tk F]
    (MC: match_cont floor SS ctx d (OpSem.Kbind id c k) tk F):
    exists t_b tc t tk',
      tk = Semantics.Kbind id tc tk'
      /\ Ctxt.get_pure id ctx = Some (t_b, false)
      /\ tr_cmd floor SS (ctxt_pure (Ctxt.set_pure id (t_b, true) ctx)) d
           (Semantics.is_call_contb tk') c tc t
      /\ match_cont floor SS ctx d k tk' F.
  Proof using Type.
    inversion MC as [ ?floor ?SS ?ctx ?k ?tk ?F EMPTY MKC | | | | | ]; subst;
      [ inversion MKC | ].
    eexists _, _, _, _.
    repeat apply conj; try reflexivity; eassumption.
  Qed.

  Lemma match_cont_Kloop1_inv [floor SS ctx d c_cond c_body k tk F]
    (MC: match_cont floor SS ctx d (OpSem.Kloop1 c_cond c_body k) tk F):
    exists tc_cond id_cond tc_body id_body tk',
      tk = Semantics.Kloop1 tc_cond id_cond tc_body id_body tk'
      /\ (floor <= id_cond)%positive /\ (floor <= id_body)%positive
      /\ id_cond <> id_body
      /\ tr_cmd floor SS (ctxt_pure ctx) d false c_cond tc_cond t_bool
      /\ tr_cmd floor SS (ctxt_pure ctx) d false c_body tc_body t_unit
      /\ match_cont floor SS ctx d k tk' F.
  Proof using Type.
    inversion MC as [ ?floor ?SS ?ctx ?k ?tk ?F EMPTY MKC | | | | | ]; subst;
      [ inversion MKC | ].
    eexists _, _, _, _, _.
    repeat apply conj; try reflexivity; eassumption.
  Qed.

  Lemma match_cont_Kloop2_inv [floor SS ctx d c_cond c_body k tk F]
    (MC: match_cont floor SS ctx d (OpSem.Kloop2 c_cond c_body k) tk F):
    exists tc_cond id_cond tc_body id_body tk',
      tk = Semantics.Kloop2 tc_cond id_cond tc_body id_body tk'
      /\ (floor <= id_cond)%positive /\ (floor <= id_body)%positive
      /\ id_cond <> id_body
      /\ tr_cmd floor SS (ctxt_pure ctx) d false c_cond tc_cond t_bool
      /\ tr_cmd floor SS (ctxt_pure ctx) d false c_body tc_body t_unit
      /\ match_cont floor SS ctx d k tk' F.
  Proof using Type.
    inversion MC as [ ?floor ?SS ?ctx ?k ?tk ?F EMPTY MKC | | | | | ]; subst;
      [ inversion MKC | ].
    eexists _, _, _, _, _.
    repeat apply conj; try reflexivity; eassumption.
  Qed.

  Lemma wt_env_pure_unique [f te1 te2] [e: Maps.PTree.t Vl]
    (WT1: OpSem.Typing.wt_env (Sm := Sm) f te1 e)
    (WT2: OpSem.Typing.wt_env (Sm := Sm) f te2 e):
    te1 = te2.
  Proof using Type.
    apply Maps.PTree.extensionality; intros id.
    assert (SIDE: forall ta tb,
               OpSem.Typing.wt_env f ta e ->
               OpSem.Typing.wt_env f tb e ->
               forall t b, Maps.PTree.get id ta = Some (t, b) ->
                           Maps.PTree.get id tb = Some (t, b)).
    { intros ta tb WTa WTb t b GETa.
      destruct (OpSem.Typing.wv_ty_env _ _ _ WTa id t b GETa) as ( VAL & IN ).
      pose proof (proj1 (OpSem.Typing.wt_val_env _ _ _ WTb id t IN)) as GETb.
      destruct b.
      - destruct VAL as [ v GETv _ ]; rewrite GETv in GETb; exact GETb.
      - rewrite VAL in GETb; exact GETb. }
    destruct (Maps.PTree.get id te1) as [ [ t1 b1 ] | ] eqn:E1.
    - rewrite (SIDE _ _ WT1 WT2 _ _ E1); reflexivity.
    - destruct (Maps.PTree.get id te2) as [ [ t2 b2 ] | ] eqn:E2;
        [ | reflexivity ].
      rewrite (SIDE _ _ WT2 WT1 _ _ E2) in E1; discriminate E1.
  Qed.

  Lemma match_call_cont_Kstop_inv [tk F]
    (MKC: match_call_cont OpSem.Kstop tk F):
    tk = Semantics.Kstop /\ F = [].
  Proof using Type.
    inversion MKC; subst; split; reflexivity.
  Qed.

  Lemma match_call_cont_is_call_cont [k tk F] (MKC: match_call_cont k tk F):
    Semantics.is_call_cont tk.
  Proof using Type.
    inversion MKC; subst;
      [ apply Semantics.call_cont_Kstop | apply Semantics.call_cont_Kcall ].
  Qed.

  Lemma match_call_cont_Kcall_inv [f e_d locals_d k tk F]
    (MKC: match_call_cont (OpSem.Kcall f e_d locals_d k) tk F):
    exists floor' ctx' tfn e_i locals_i tk' F',
      tk = Semantics.Kcall tfn e_i locals_i tk'
      /\ F = mkstack_block locals_d locals_i
               tfn.(fn_extra).(IR.Prog.fn_stackspace) :: F'
      /\ tr_function_at floor' f tfn
      /\ env_incl e_d e_i
      /\ env_dom (f.(fn_params) ++ f.(fn_temps)) e_d
      /\ wf_stack_block (mkstack_block locals_d locals_i
                     tfn.(fn_extra).(IR.Prog.fn_stackspace))
      /\ Deep.Typing.wt_function
           (to_glob_ctxt ctx') f
      /\ OpSem.Typing.wt_env f (ctxt_pure ctx') e_d
      /\ ctxt_stack ctx' = List.map (fun _ => tt) locals_d
      /\ ctxt_internal ctx' = mk_typing_tree false f.(fn_internals) Maps.PTree.Empty
      /\ Globalenvs.Genv.globalenv prog = ctxt_global ctx'
      /\ match_cont floor' tfn.(fn_extra).(IR.Prog.fn_stackspace) ctx'
                                            (List.length locals_d) k tk' F'.
  Proof using Type.
    inversion MKC; subst.
    eexists _, _, _, _, _, _, _.
    repeat apply conj; try reflexivity; eassumption.
  Qed.

  Lemma resolve_seq_match:
    forall [f t_k] [floor SS ctx d k tk F]
           [e_d e_i v c' e_d' k' n]
           (MC: match_cont floor SS ctx d k tk F)
           (ENV: env_incl e_d e_i)
           (EDOM: env_dom (f.(fn_params) ++ f.(fn_temps)) e_d)
           (SRCBOUND: forall id ty, In (id, ty) (f.(fn_params) ++ f.(fn_temps)) ->
                                    (id < floor)%positive)
           (WTk: OpSem.Typing.wt_cont ctx k t_k)
           (WTv: Value.wt_value v t_k)
           (WTe: OpSem.Typing.wt_env f (ctxt_pure ctx) e_d)
           (RES: OpSem.resolve_seq_cont k e_d v c' e_d' k' n),
    exists ctx' tc' tk' t' t_d' target_id,
      Semantics.resolve_seq_cont tk v tc' tk'
      /\ Semantics.seq_cont_target tk target_id
      /\ ctxt_stack ctx' = ListExt.removelast_n n (ctxt_stack ctx)
      /\ (n <= d)%nat
      /\ tr_cmd floor SS (ctxt_pure ctx') (d - n) (Semantics.is_call_contb tk') c' tc' t'
      /\ match_cont floor SS ctx' (d - n) k' tk' F
      /\ env_incl e_d' (Maps.PTree.set target_id v e_i)
      /\ ctxt_global ctx' = ctxt_global ctx
      /\ ctxt_internal ctx' = ctxt_internal ctx
      /\ Deep.Typing.wt_cmd ctx' c' t_d'
      /\ OpSem.Typing.wt_cont ctx' k' t_d'
      /\ OpSem.Typing.wt_env f (ctxt_pure ctx') e_d'
      /\ env_dom (f.(fn_params) ++ f.(fn_temps)) e_d'.
  Proof using Type.
    intros f t_k floor SS ctx d k tk F e_d e_i v c' e_d' k' n
      MC ENV EDOM SRCBOUND WTk WTv WTe RES.
    revert ctx d tk F e_i t_k MC ENV WTk WTv WTe.
    induction RES as
      [ id_b c_next k0 env0 v0
      | c_cond c_body k0 env0 b
      | c_cond c_body k0 env0
      | id k0 env0 v0 c'0 env'0 k'0 n0 RES IH
      | k0 env0 v0 c'0 env'0 k'0 n0 RES IH ];
      intros ctx d tk F e_i t_k MC ENV WTk WTv WTe.
    - destruct (match_cont_Kbind_inv MC) as ( t_b & tc & t & tk' & -> & GET & TRc & MK ).
      inversion WTk as [ ?ctx0 ?id0 ?c0 ?k1 ?t_b0 t_c GETd WTCMDd WTCONTd
                       | | | ?ctx0 ?k1 ?tret EMPTY WTCC | | ]; subst;
        [ | inversion WTCC ].
      assert (ETB: t_b = t_k) by congruence.
      subst t_k.
      exists (Ctxt.set_pure id_b (t_b, true) ctx), tc, tk', t, t_c, id_b.
      assert (EQctx: Ctxt.set_pure id_b (t_b, false)
                       (Ctxt.set_pure id_b (t_b, true) ctx) = ctx).
      { apply Ctxt.Facts.ctxt_ext; [ | reflexivity | reflexivity | reflexivity ].
        cbn [ctxt_pure Ctxt.set_pure].
        rewrite Maps.PTree.set2.
        apply Maps.PTree.gsident, GET. }
      repeat apply conj.
      + apply Semantics.resolve_seq_Kbind.
      + apply Semantics.seq_target_Kbind.
      + reflexivity.
      + apply Nat.le_0_l.
      + rewrite Nat.sub_0_r; exact TRc.
      + rewrite Nat.sub_0_r.
        apply mc_scope_unbind with (t := t_b);
          [ apply Ctxt.Facts.get_set_pure | rewrite EQctx; exact MK ].
      + exact (env_incl_set _ _ ENV).
      + reflexivity.
      + reflexivity.
      + exact WTCMDd.
      + apply OpSem.Typing.wt_cont_Kscope_unbind with (t := t_b);
          [ apply Ctxt.Facts.get_set_pure | rewrite EQctx; exact WTCONTd ].
      + exact (OpSem.Typing.wt_env_set WTe GET WTv).
      + exact (env_dom_set id_b t_b v0
                 (proj2 (OpSem.Typing.wv_ty_env _ _ _ WTe id_b t_b false GET))
                 EDOM).
    - destruct (match_cont_Kloop1_inv MC)
        as ( tc_cond & id_cond & tc_body & id_body & tk' & -> & FC & FB & NEQ
                                                              & TRcond & TRbody & MK ).
      inversion WTk as [ | ?ctx0 ?c_c0 ?c_b0 ?k1 WTCONDd WTBODYd WTCONTd
                       | | ?ctx0 ?k2 ?tret EMPTY WTCC | | ]; subst;
        [ | inversion WTCC ].
      exists ctx, (if b then tc_body else IR.Cmd.c_ret e_tt t_unit),
        (if b then Semantics.Kloop2 tc_cond id_cond tc_body id_body tk' else tk'),
        t_unit, t_unit, id_cond.
      assert (FRESH: Maps.PTree.get id_cond env0 = None).
      { refine (env_dom_fresh id_cond EDOM _).
        intros IN; apply List.in_map_iff in IN as ( [ id ty ] & EQ & IN ).
        cbn [fst] in EQ; subst id.
        exact (Pos.lt_irrefl _ (Pos.lt_le_trans _ _ _ (SRCBOUND _ _ IN) FC)). }
      repeat apply conj.
      + apply Semantics.resolve_seq_Kloop1.
      + apply Semantics.seq_target_Kloop1.
      + reflexivity.
      + apply Nat.le_0_l.
      + rewrite Nat.sub_0_r; destruct b; [ exact TRbody | ].
        apply tr_ret; intros t' TE; cbn in TE; injection TE as <-; reflexivity.
      + rewrite Nat.sub_0_r; destruct b; [ | exact MK ].
        exact (mc_loop2 _ _ _ _ _ _ _ _ _ _ _ _ _ FC FB NEQ TRcond TRbody MK).
      + exact (env_incl_set_fresh _ _ FRESH ENV).
      + reflexivity.
      + reflexivity.
      + destruct b; [ exact WTBODYd | constructor; constructor ].
      + destruct b;
          [ apply OpSem.Typing.wt_cont_Kloop2; assumption | exact WTCONTd ].
      + exact WTe.
      + exact EDOM.
    - destruct (match_cont_Kloop2_inv MC)
        as ( tc_cond & id_cond & tc_body & id_body & tk' & -> & FC & FB & NEQ
                                                              & TRcond & TRbody & MK ).
      inversion WTk as [ | | ?ctx0 ?c_c0 ?c_b0 ?k1 WTCONDd WTBODYd WTCONTd
                       | ?ctx0 ?k2 ?tret EMPTY WTCC | | ]; subst;
        [ | inversion WTCC ].
      exists ctx, tc_cond,
        (Semantics.Kloop1 tc_cond id_cond tc_body id_body tk'), t_bool, t_bool,
        id_body.
      assert (FRESH: Maps.PTree.get id_body env0 = None).
      { refine (env_dom_fresh id_body EDOM _).
        intros IN; apply List.in_map_iff in IN as ( [ id ty ] & EQ & IN ).
        cbn [fst] in EQ; subst id.
        exact (Pos.lt_irrefl _ (Pos.lt_le_trans _ _ _ (SRCBOUND _ _ IN) FB)). }
      repeat apply conj.
      + apply Semantics.resolve_seq_Kloop2.
      + apply Semantics.seq_target_Kloop2.
      + reflexivity.
      + apply Nat.le_0_l.
      + rewrite Nat.sub_0_r; exact TRcond.
      + rewrite Nat.sub_0_r.
        exact (mc_loop1 _ _ _ _ _ _ _ _ _ _ _ _ _ FC FB NEQ TRcond TRbody MK).
      + exact (env_incl_set_fresh _ _ FRESH ENV).
      + reflexivity.
      + reflexivity.
      + exact WTCONDd.
      + apply OpSem.Typing.wt_cont_Kloop1; assumption.
      + exact WTe.
      + exact EDOM.
    - inversion MC as [ ?floor ?SS ?ctx0 ?k1 ?tk1 ?F1 EMPTY MKC
                      | | | | ?floor ?SS ?ctx0 ?d0 ?id1 ?t1 ?k1 ?tk1 ?F1 GET MK
                      | ]; subst;
        [ inversion MKC | ].
      inversion WTk as [ | | | ?ctx0 ?k1 ?tret EMPTYd WTCC
                       | ?ctx0 ?id0 ?k2 ?t0 ?t0' GETd WTCONTd | ]; subst;
        [ inversion WTCC | ].
      assert (ETB: t1 = t0) by congruence.
      subst t0.
      destruct (IH (env_dom_remove _ EDOM) _ _ _ _ _ _ MK
                  (env_incl_remove_l _ ENV) WTCONTd WTv
                  (OpSem.Typing.wt_env_unset WTe GET))
        as ( ctx' & tc' & tk' & t' & t_d' & target_id
             & RSEQ & STGT & STK & LE & TRc & MK' & ENV' & GLOBc & INTc & WTCMDd
             & WTCONTd' & WTEd & EDOMd ).
      exists ctx', tc', tk', t', t_d', target_id.
      repeat apply conj; assumption.
    - inversion MC as [ ?floor ?SS ?ctx0 ?k1 ?tk1 ?F1 EMPTY MKC
                      | | | | | ?floor ?SS ?ctx0 ?d0 ?k1 ?tk1 ?F1 ?s0 ?sl0 NONEMPTY MK ];
        subst;
        [ inversion MKC | ].
      inversion WTk as [ | | | ?ctx0 ?k1 ?tret EMPTYd WTCC
                       | | ?ctx0 ?k2 ?t0 ?s0d ?sl0d NONEMPTYd WTCONTd ]; subst;
        [ inversion WTCC | ].
      destruct (IH EDOM _ _ _ _ _ _ MK ENV WTCONTd WTv WTe)
        as ( ctx' & tc' & tk' & t' & t_d' & target_id
             & RSEQ & STGT & STK & LE & TRc & MK' & ENV' & GLOBc & INTc & WTCMDd
             & WTCONTd' & WTEd & EDOMd ).
      exists ctx', tc', tk', t', t_d', target_id.
      repeat apply conj; try assumption.
      apply le_n_S; exact LE.
  Qed.

  Lemma resolve_call_match:
    forall [k k'] (RES: OpSem.resolve_call_cont k k')
           [floor SS ctx d tk F] (MC: match_cont floor SS ctx d k tk F),
      match_call_cont k' tk F.
  Proof using Type.
    intros k k' RES.
    induction RES as [ k0 CALLK | sx k0 k'0 RES IH ];
      intros floor SS ctx d tk F MC.
    - inversion MC as [ ?floor ?SS ?ctx0 ?k1 ?tk1 ?F1 EMPTY MKC | | | | | ];
        subst; [ exact MKC | | | | | ];
        inversion CALLK.
    - destruct sx as [ id | ].
      + inversion MC as [ ?floor ?SS ?ctx0 ?k1 ?tk1 ?F1 EMPTY MKC
                        | | | | ?floor ?SS ?ctx0 ?d0 ?id1 ?t1 ?k1 ?tk1 ?F1 GET MK
                        | ]; subst;
          [ inversion MKC | ].
        exact (IH _ _ _ _ _ _ MK).
      + inversion MC as [ ?floor ?SS ?ctx0 ?k1 ?tk1 ?F1 EMPTY MKC
                        | | | | | ?floor ?SS ?ctx0 ?d0 ?k1 ?tk1 ?F1 ?s0 ?sl0
                                    NONEMPTY MK ]; subst;
          [ inversion MKC | ].
        exact (IH _ _ _ _ _ _ MK).
  Qed.

  Lemma builtin_sim:
    forall [f: function] [floor SS ctx d tail c tc t t_d]
           [locals_d locals_i F] [ge_d ge_i e_d e_i] [s_d s_i: Sm] [v s_d']
           (TRc: tr_cmd floor SS (ctxt_pure ctx) d tail c tc t)
           (WTc: Deep.Typing.wt_cmd ctx c t_d)
           (WTenv: OpSem.Typing.wt_env f (ctxt_pure ctx) e_d)
           (ENV: env_incl e_d e_i)
           (HEAP: heap s_d = heap s_i)
           (ALC: alc s_d = alc s_i)
           (SM: smatch (mkstack_block locals_d locals_i SS :: F)
                  (store s_d) (store s_i))
           (BUILTIN: OpSem.builtin c ge_d e_d locals_d s_d v s_d'),
    exists (s_i': Sm),
      Semantics.builtin tc ge_i e_i locals_i s_i v s_i'
      /\ heap s_d' = heap s_i'
      /\ alc s_d' = alc s_i'
      /\ scnt s_i' = scnt s_i
      /\ smatch (mkstack_block locals_d locals_i SS :: F)
           (store s_d') (store s_i').
  Proof using Type.
    intros f floor SS ctx d tail c tc t t_d locals_d locals_i F
      ge_d ge_i e_d e_i s_d s_i v s_d' TRc WTc WTenv ENV HEAP ALC SM BUILTIN.
    destruct BUILTIN;
      inversion TRc; subst; inversion WTc; subst.
    - exists s_i.
      assert (WTv: Value.wt_value v t).
      { assert (ETY := Expr.Facts.type_expr_correct WTe).
        rewrite (TYPE _ ETY) in WTe.
        exact (OpSem.Typing.eval_preserves_wt_env _ _ _ WTenv _ _ _ WTe EVAL). }
      repeat apply conj; try assumption; try reflexivity.
      apply Semantics.builtin_ret; [ exact (eval_incl ENV EVAL) | exact WTv ].
    - destruct (smatch_lookup _ _ _ _ _ _ _ SM DEREF LOOKUP)
        as ( nm_i & DEREFi & LOOKUPi ).
      exists s_i.
      repeat apply conj; try assumption; try reflexivity.
      apply (Semantics.builtin_read_var _ _ _ _ _ _ _ nm_i DEREFi);
        [ rewrite (decode_encode _ _ VMV); exact LOOKUPi | exact WT ].
    - destruct (smatch_mutate _ _ _ _ _ _ _ _ SM DEREF MUTATE)
        as ( nm_i & st_i & DEREFi & MUTATEi & SM' ).
      exists (state_mutate_store s_i MUTATEi).
      repeat apply conj; autorewrite with seplog; try assumption; try reflexivity.
      apply (Semantics.builtin_write_var _ _ _ _ _ _ _ _ _ nm_i
               (eval_incl ENV EVAL) DEREFi MUTATEi WT).
    - pose proof ALLOC as ALLOCi; rewrite HEAP, ALC in ALLOCi.
      exists (state_alloc s_i ALLOCi).
      repeat apply conj; autorewrite with seplog; try assumption; try reflexivity.
      exact (Semantics.builtin_alloc_ptr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               (eval_incl ENV EVAL_SIZE) (eval_incl ENV EVAL_INIT) WT BND ALLOCi).
    - exists s_i.
      repeat apply conj; try assumption; try reflexivity.
      apply (Semantics.builtin_read_ptr _ _ _ _ _ _ _ _ (eval_incl ENV EVAL));
        [ rewrite <- HEAP, (decode_encode _ _ VMV); exact LOOKUP | exact WT ].
    - pose proof MUTATE as MUTATEi; rewrite HEAP in MUTATEi.
      exists (state_mutate_heap s_i MUTATEi).
      repeat apply conj; autorewrite with seplog; try assumption; try reflexivity.
      exact (Semantics.builtin_write_ptr _ _ _ _ _ _ _ _ _ _
               (eval_incl ENV EVAL_ptr) (eval_incl ENV EVAL_data) MUTATEi WT).
    - pose proof FREE as FREEi; rewrite HEAP in FREEi.
      exists (state_free s_i FREEi).
      repeat apply conj; autorewrite with seplog; try assumption; try reflexivity.
      exact (Semantics.builtin_free_ptr _ _ _ _ _ _ _
               (eval_incl ENV EVAL) FREEi).
    - exists s_i.
      repeat apply conj; try assumption; try reflexivity.
      apply (Semantics.builtin_shift_fw_ptr _ _ _ _ _ _ _ _ _
               (eval_incl ENV EVAL_ptr) (eval_incl ENV EVAL_shift) SHIFT);
        rewrite <- HEAP; assumption.
    - exists s_i.
      repeat apply conj; try assumption; try reflexivity.
      apply (Semantics.builtin_shift_bw_ptr _ _ _ _ _ _ _ _ _
               (eval_incl ENV EVAL_ptr) (eval_incl ENV EVAL_shift) SHIFT);
        rewrite <- HEAP; assumption.
    - exists s_i.
      repeat apply conj; try assumption; try reflexivity.
      apply (Semantics.builtin_eq_ptr _ _ _ _ _ _ _ _ _
               (eval_incl ENV EVAL_l) (eval_incl ENV EVAL_r));
        [ rewrite <- HEAP; exact CMPVALID
        | exact CMP ].
    - exists s_i.
      repeat apply conj; try assumption; try reflexivity.
      apply (Semantics.builtin_div _ _ _ _ _ _ _ _ _
               (eval_incl ENV EVAL_l) (eval_incl ENV EVAL_r)
               (Unsigned.Facts.div_state_indep DIV)).
    - exists s_i.
      repeat apply conj; try assumption; try reflexivity.
      apply (Semantics.builtin_mod _ _ _ _ _ _ _ _ _
               (eval_incl ENV EVAL_l) (eval_incl ENV EVAL_r)
               (Unsigned.Facts.mdl_state_indep MDL)).
  Qed.

  Lemma transl_init_state [s_i: Sm] (INIT: Semantics.init_state tprog = Some s_i):
    heap (emp_state: Sm) = heap s_i
    /\ alc (emp_state: Sm) = alc s_i
    /\ (exists k, scnt s_i = Owned (mk_cnt k None))
    /\ smatch [] (store (emp_state: Sm)) (store s_i).
  Proof using Type.
    unfold Semantics.init_state in INIT.
    assert (CNT0: scnt (emp_state: Sm) = Owned (mk_cnt 0 None))
      by (unfold emp_state; exact (scnt_emp_with_alc _ _)).
    destruct (IR.Lemmas.alloc_globals_state CNT0 INIT) as ( Ehp & Ealc & k & CNT ).
    repeat apply conj;
      [ exact (eq_sym Ehp) | exact (eq_sym Ealc) | exists k; exact CNT
      | exact (smatch_init tprog s_i INIT) ].
  Qed.

  Lemma transl_initial_states [s1]
    (INIT: @OpSem.initial_state Sm prog s1):
    exists s2, Semantics.initial_state tprog s2 /\ match_states s1 s2.
  Proof using TRANSL.
    inversion INIT as [ ge0 fd b WTd GE0 FINDSYMB FINDFUNC MAINSIG ]; subst.
    pose proof (match_prog_wt TRANSL WTd) as WTi.
    destruct (IR.Lemmas.init_state_wt (Sm := Sm) tprog WTi) as ( s0 & INITs ).
    destruct (function_ptr_translated TRANSL FINDFUNC) as ( tfd & FINDFUNCt & MFD ).
    assert (EMAIN: AST.prog_main tprog = prog_main prog)
      by (destruct TRANSL as ( _ & EM & _ ); exact EM).
    assert (FINDSYMBt: Globalenvs.Genv.find_symbol
                         (Globalenvs.Genv.globalenv tprog) (AST.prog_main tprog)
                       = Some b)
      by (rewrite EMAIN, (symbols_preserved TRANSL); exact FINDSYMB).
    assert (MAINSIGt: funsig tfd (mk_signature [] t_nat)).
    { inversion MFD as [ fn0 tfn0 TR EQa EQb | ef0 EQa EQb ]; subst.
      - inversion MAINSIG as [ fn1 sg1 EQs | ]; subst.
        exact (eq_rect _ (fun sg => funsig (AST.Internal tfn0) sg)
                 (funsig_Internal tfn0) _ (sig_preserved TR)).
      - inversion MAINSIG as [ | ef1 sg1 SIG EQs ]; subst.
        apply funsig_External; exact SIG. }
    destruct (transl_init_state INITs) as ( HEAPi & ALCi & CNTi & SMi ).
    exists (Semantics.Callstate tfd [] Semantics.Kstop s0).
    split.
    - exact (Semantics.initial_state_intro tprog _ b tfd s0
               WTi eq_refl INITs FINDSYMBt FINDFUNCt MAINSIGt).
    - exact (match_Callstate fd tfd [] OpSem.Kstop Semantics.Kstop _ s0 []
               (OpSem.Typing.wt_initial_state prog _ INIT)
               MFD mcc_stop HEAPi ALCi CNTi SMi).
  Qed.

  Lemma transl_final_states [s1 s2 r]
    (MS: match_states s1 s2) (FIN: OpSem.final_state s1 r):
    Semantics.final_state s2 r.
  Proof using Type.
    inversion FIN as [ r0 s_d EQ1 EQ2 ]; subst.
    destruct (match_Returnstate_inv MS) as ( tk & s_i & F & -> & _ & MKC & _ & _ & _ & _ ).
    destruct (match_call_cont_Kstop_inv MKC) as ( -> & _ ).
    apply Semantics.final_state_intro.
  Qed.

  Lemma step_bind_correct
    (WTp: Deep.Typing.wt_program prog)
    [f id_b t_b c_b c_c k e_d locals_d] [s_d: Sm] [s2]
    (MS: match_states
           (OpSem.State f (c_bind id_b t_b c_b c_c) k e_d locals_d s_d) s2):
    exists s2',
      Smallstep.plus (@Semantics.step Sm) (Globalenvs.Genv.globalenv tprog) s2 Events.E0 s2'
      /\ match_states
           (OpSem.State f c_b (OpSem.Kbind id_b c_c k) e_d locals_d s_d) s2'.
  Proof using TRANSL.
    destruct (match_State_inv MS) as
      ( floor & tf & tc & tk & e_i & locals_i & s_i & t & t_d & d & ctx & F
        & -> & WT & GLOB & TRf & TRc & MK & ENV & EDOM & DLEN & WF & HEAP & ALC & CNT & SM ).
    destruct WT as [ WTfn WTc WTk WTe WTs WTint ].
    inversion TRc as [ | ?ctx0 ?d ?tail ?b_id ?t_b1 ?c_b1 ?c_c1 tc_b tc_c ?t_c
                           BINDER TRb TRcc EQa EQb EQc EQd EQe
                     | | | | | | | | | | | | | | | ]; subst.
    inversion WTc as [ | ?ctx0 ?x ?c1 ?c2 ?t1 ?t2 UNBOUND WTm WTf EQa EQb
                     | | | | | | | | | | | | | | | | ]; subst.
    exists (Semantics.State tf tc_b (Semantics.Kbind id_b tc_c tk)
              e_i locals_i s_i).
    split.
    - apply Smallstep.plus_one.
      apply Semantics.step_bind.
    - eapply match_State with (floor := floor) (t := t_b) (ctx := ctx) (F := F).
      + constructor;
          [ exact WTfn
          | exact WTm
          | eapply OpSem.Typing.wt_cont_Kbind;
            [ exact UNBOUND | exact WTf | exact WTk ]
          | exact WTe
          | exact WTs
          | exact WTint ].
      + exact GLOB.
      + exact TRf.
      + exact TRb.
      + eapply mc_bind; [ exact UNBOUND | exact TRcc | exact MK ].
      + exact ENV.
      + exact EDOM.
      + reflexivity.
      + exact WF.
      + exact HEAP.
      + exact ALC.
      + exact CNT.
      + exact SM.
  Qed.

  Lemma step_ifthenelse_correct
    (WTp: Deep.Typing.wt_program prog)
    [f e_if c_then c_else k e_d locals_d] [s_d: Sm]
    [b] (EVAL: Expr.eval e_if e_d = Some (Value.v_bool b))
    [s2]
    (MS: match_states
           (OpSem.State f (c_if e_if c_then c_else) k e_d locals_d s_d) s2):
    exists s2',
      Smallstep.plus (@Semantics.step Sm) (Globalenvs.Genv.globalenv tprog)
        s2 Events.E0 s2'
      /\ match_states
           (OpSem.State f (if b then c_then else c_else) k e_d locals_d s_d) s2'.
  Proof using TRANSL.
    destruct (match_State_inv MS) as
      ( floor & tf & tc & tk & e_i & locals_i & s_i & t & t_d & d & ctx & F
        & -> & WT & GLOB & TRf & TRc & MK & ENV & EDOM & DLEN & WF & HEAP & ALC & CNT & SM ).
    destruct WT as [ WTfn WTc WTk WTe WTs WTint ].
    inversion TRc as [ | | ?ctx0 ?d0 ?tail ?e0 ?c_t ?c_e tc_t tc_e ?t0
                             TRt TRe EQa EQb EQc EQd EQe
                     | | | | | | | | | | | | | | ]; subst.
    inversion WTc as [ | | ?ctx0 ?e1 ?c1 ?c2 ?t1 WTcond WTthen WTelse EQa EQb
                     | | | | | | | | | | | | | | | ]; subst.
    exists (Semantics.State tf (if b then tc_t else tc_e) tk
              e_i locals_i s_i).
    split.
    - apply Smallstep.plus_one.
      apply Semantics.step_ifthenelse.
      exact (eval_incl ENV EVAL).
    - eapply match_State with (floor := floor) (t := t) (ctx := ctx) (F := F).
      + constructor;
          [ exact WTfn
          | destruct b; [ exact WTthen | exact WTelse ]
          | exact WTk
          | exact WTe
          | exact WTs
          | exact WTint ].
      + exact GLOB.
      + exact TRf.
      + destruct b; [ exact TRt | exact TRe ].
      + exact MK.
      + exact ENV.
      + exact EDOM.
      + reflexivity.
      + exact WF.
      + exact HEAP.
      + exact ALC.
      + exact CNT.
      + exact SM.
  Qed.

  Lemma step_while_correct
    (WTp: Deep.Typing.wt_program prog)
    [f c_cond c_body k e_d locals_d] [s_d: Sm] [s2]
    (MS: match_states
           (OpSem.State f (c_while c_cond c_body) k e_d locals_d s_d) s2):
    exists s2',
      Smallstep.plus (@Semantics.step Sm) (Globalenvs.Genv.globalenv tprog)
        s2 Events.E0 s2'
      /\ match_states
           (OpSem.State f c_cond (OpSem.Kloop1 c_cond c_body k)
              e_d locals_d s_d) s2'.
  Proof using TRANSL.
    destruct (match_State_inv MS) as
      ( floor & tf & tc & tk & e_i & locals_i & s_i & t & t_d & d & ctx & F
        & -> & WT & GLOB & TRf & TRc & MK & ENV & EDOM & DLEN & WF & HEAP & ALC & CNT & SM ).
    destruct WT as [ WTfn WTc WTk WTe WTs WTint ].
    inversion TRc as [ | | | ?ctx0 ?d0 ?tail ?c_c ?c_b tc_cond tc_body
                               id_cond id_body FRESHc FRESHb NEQ TRcond TRbody
                               EQa EQb EQc EQd EQe
                     | | | | | | | | | | | | | ]; subst.
    inversion WTc as [ | | | ?ctx0 ?c_c1 ?c_b1 WTcond WTbody EQa EQb
                     | | | | | | | | | | | | | | ]; subst.
    exists (Semantics.State tf tc_cond
              (Semantics.Kloop1 tc_cond id_cond tc_body id_body tk)
              e_i locals_i s_i).
    split.
    - apply Smallstep.plus_one.
      apply Semantics.step_while.
    - eapply match_State with (floor := floor) (t := t_bool) (ctx := ctx) (F := F).
      + constructor;
          [ exact WTfn
          | exact WTcond
          | eapply OpSem.Typing.wt_cont_Kloop1;
            [ exact WTcond | exact WTbody | exact WTk ]
          | exact WTe
          | exact WTs
          | exact WTint ].
      + exact GLOB.
      + exact TRf.
      + exact TRcond.
      + eapply mc_loop1;
          [ exact FRESHc | exact FRESHb | exact NEQ
          | exact TRcond | exact TRbody | exact MK ].
      + exact ENV.
      + exact EDOM.
      + reflexivity.
      + exact WF.
      + exact HEAP.
      + exact ALC.
      + exact CNT.
      + exact SM.
  Qed.

  Lemma step_app_correct
    (WTp: Deep.Typing.wt_program prog)
    [f id_f args k e_d locals_d] [s_d: Sm]
    [fd v_args b]
    (EVAL: ListExt.map_opt (fun e => Expr.eval e e_d) args = Some v_args)
    (FINDSYMB: Globalenvs.Genv.find_symbol (Globalenvs.Genv.globalenv prog) id_f
               = Some b)
    (FINDFUNC: Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv prog) b
               = Some fd)
    (SEQK: OpSem.is_seq_cont k)
    [s2]
    (MS: match_states
           (OpSem.State f (c_app id_f args) k e_d locals_d s_d) s2):
    exists s2',
      Smallstep.plus (@Semantics.step Sm) (Globalenvs.Genv.globalenv tprog)
        s2 Events.E0 s2'
      /\ match_states
           (OpSem.Callstate fd v_args (OpSem.Kcall f e_d locals_d k) s_d) s2'.
  Proof using TRANSL.
    pose proof (match_State_wt_state MS) as WTs0.
    destruct (match_State_inv MS) as
      ( floor & tf & tc & tk & e_i & locals_i & s_i & t & t_d & d & ctx & F
        & -> & WT & GLOB & TRf & TRc & MK & ENV & EDOM & DLEN & WF & HEAP & ALC & CNT & SM ).
    inversion TRc as [ | | | | | | | | | | | | | | ?ctx0 ?d0 ?f_id0 ?args0
                                                     t_out t_args LEN TARGS
                                                     EQa EQb NOTAIL EQc EQd EQe
                     | | ]; subst.
    destruct (function_ptr_translated TRANSL FINDFUNC) as ( tfd & FINDFUNCt & MFD ).
    exists (Semantics.Callstate tfd v_args
              (Semantics.Kcall tf e_i locals_i tk) s_i).
    split.
    - apply Smallstep.plus_one.
      eapply Semantics.step_app.
      + rewrite (map_fst_combine args t_args LEN).
        exact (eval_list_incl ENV EVAL).
      + rewrite (symbols_preserved TRANSL); exact FINDSYMB.
      + exact FINDFUNCt.
      + destruct (IR.Lemmas.is_call_contb_spec tk) as [ CALL | NOTCALL ];
          [ discriminate NOTAIL | ].
        destruct (IR.Lemmas.cont_call_or_seq tk) as [ CALL | SEQ ];
          [ contradiction (NOTCALL CALL) | exact SEQ ].
    - eapply match_Callstate.
      + exact (OpSem.Typing.step_preservation prog _ _ _ WTp WTs0
                 (OpSem.step_app _ f id_f args k e_d locals_d s_d fd v_args b
                    EVAL FINDSYMB FINDFUNC SEQK)).
      + exact MFD.
      + destruct WT as [ WTfn WTc WTk WTe WTs WTint ].
        eapply mcc_call;
          [ exact TRf | reflexivity | exact ENV | exact EDOM | reflexivity
          | exact WF | exact WTfn | exact WTe | exact WTs | exact WTint
          | exact GLOB | exact MK ].
      + exact HEAP.
      + exact ALC.
      + exact CNT.
      + exact SM.
  Qed.

  Lemma step_internal_function_correct
    (WTp: Deep.Typing.wt_program prog)
    [fn args k] [s_d: Sm]
    (WTargs: Forall2 (Value.wt_value (Pt := Pt)) args (List.map snd fn.(fn_params)))
    (CALLK: OpSem.is_call_cont k)
    [s2]
    (MS: match_states (OpSem.Callstate (AST.Internal fn) args k s_d) s2):
    exists s2',
      Smallstep.plus (@Semantics.step Sm) (Globalenvs.Genv.globalenv tprog)
        s2 Events.E0 s2'
      /\ match_states
           (OpSem.State fn fn.(fn_body) k
                                (OpSem.set_params fn.(fn_params) args) [] s_d) s2'.
  Proof using TRANSL.
    destruct (match_Callstate_inv MS) as
      ( tfd & tk & s_i & F & -> & WTs0 & MFD & MKC & HEAP & ALC & CNT & SM ).
    inversion MFD as [ fn0 tfn TRf0 EQa EQb | ]; subst.
    destruct TRf0 as ( floor & TRf ).
    assert (NONNEG: (0 <= tfn.(fn_extra).(IR.Prog.fn_stackspace))%Z).
    { rewrite (tr_fn_stackspace _ _ _ TRf). apply stack_usage_nonneg. }
    destruct (smatch_stack_block_alloc F s_d s_i _ SM CNT NONNEG)
      as ( st_i & sg_i & locals_i & ALLOC & LEN & DOM & CNT' & SM' ).
    inversion WTs0 as [ | ?fd0 ?args0 ?k0 ?s0 sg ctx0 WTfd WTCA SIGf
                            WTcont GLOB0 | ]; subst.
    inversion WTfd as [ ?ctx1 ?fn1 WTfn | | ]; subst.
    assert (GLOBf: Globalenvs.Genv.globalenv prog
                   = ctxt_global (mk_function_ctxt fn.(fn_params) fn.(fn_temps) fn.(fn_internals)
                                                                       (mk_glob_ctxt prog)))
      by reflexivity.
    assert (CTX0: ctx0 = mk_glob_ctxt prog)
      by exact (OpSem.Typing.glob_ctx_unique prog ctx0 GLOB0).
    assert (ESIG: sg = fn_signature fn) by (inversion SIGf; subst; reflexivity).
    exists (Semantics.State tfn tfn.(fn_body) tk
                                      (OpSem.set_params fn.(fn_params) args) locals_i
                                      (mk_state st_i sg_i (heap s_i) (alc s_i) DOM
                                         (state_heap_dominates s_i))).
    split.
    - apply Smallstep.plus_one.
      eapply Semantics.step_internal_function.
      + rewrite (tr_fn_params _ _ _ TRf); exact WTargs.
      + rewrite (tr_fn_params _ _ _ TRf); reflexivity.
      + exact ALLOC.
      + exact (mk_state_opt_of_dominates _ _ _ _ DOM (state_heap_dominates s_i)).
      + exact (match_call_cont_is_call_cont MKC).
    - eapply match_State with (floor := floor)
                              (ctx := mk_function_ctxt fn.(fn_params) fn.(fn_temps) fn.(fn_internals) (mk_glob_ctxt prog))
                              (F := F).
      + constructor.
        * rewrite (OpSem.Typing.mk_glob_ctxt_eq GLOBf); exact WTfn.
        * exact (Prog.wt_fn_cmd WTfn).
        * apply OpSem.Typing.wt_cont_other; [ reflexivity | ].
          rewrite (OpSem.Typing.mk_glob_ctxt_eq GLOBf), <- CTX0.
          rewrite ESIG in WTcont; cbn [fn_signature sig_res] in WTcont.
          exact WTcont.
        * exact (OpSem.Typing.wt_env_init WTfn WTargs).
        * reflexivity.
        * reflexivity.
      + exact GLOBf.
      + exact TRf.
      + rewrite (tr_fn_stackspace _ _ _ TRf),
          (ReflectExt.reflect_true_of_prop (IR.Lemmas.is_call_contb_spec tk)
             (match_call_cont_is_call_cont MKC)).
        apply (tr_fn_body _ _ _ TRf).
        * intros id ty GET.
          destruct (Prog.Facts.mk_function_ctxt_pure_get_inv
                      fn.(fn_params) fn.(fn_temps) fn.(fn_internals) (mk_glob_ctxt prog)
                                          (Prog.wt_fn_params_sbinds WTfn)
                                          (Prog.wt_fn_temps_sbinds WTfn) _ _ _ GET)
            as [ ( _ & IN ) | ( EQF & _ ) ]; [ exact IN | discriminate EQF ].
        * intros id [ ty b ] GET.
          destruct (Prog.Facts.mk_function_ctxt_pure_get_inv
                      fn.(fn_params) fn.(fn_temps) fn.(fn_internals) (mk_glob_ctxt prog)
                                          (Prog.wt_fn_params_sbinds WTfn)
                                          (Prog.wt_fn_temps_sbinds WTfn) _ _ _ GET)
            as [ ( _ & IN ) | ( _ & IN ) ];
            rewrite List.map_app; apply List.in_or_app;
            [ left | right ];
            exact (List.in_map fst _ _ IN).
      + apply mc_other; [ reflexivity | exact MKC ].
      + apply env_incl_refl.
      + intros x v GET.
        rewrite List.map_app; apply List.in_or_app; left.
        exact (env_dom_set_params fn.(fn_params) args x v GET).
      + reflexivity.
      + constructor; [ exact LEN | cbn [sb_deep sb_ir]; apply Nat.le_0_l ].
      + rewrite heap_mk_state; exact HEAP.
      + rewrite alc_mk_state; exact ALC.
      + rewrite scnt_mk_state; exact CNT'.
      + rewrite store_mk_state; exact SM'.
  Qed.

  Lemma step_with_var_correct
    (WTp: Deep.Typing.wt_program prog)
    [f t_v e_init c_next k e_d locals_d] [s_d: Sm]
    [v: Vl] [st_d' sg_d' nm]
    (EVAL: Expr.eval e_init e_d = Some v)
    (PUSH: push (store s_d) (scnt s_d) (encode v) = Some (st_d', sg_d', nm))
    [s2]
    (MS: match_states
           (OpSem.State f (c_with_var t_v e_init c_next) k e_d locals_d s_d) s2):
    exists s2',
      Smallstep.plus (@Semantics.step Sm) (Globalenvs.Genv.globalenv tprog)
        s2 Events.E0 s2'
      /\ match_states
           (OpSem.State f c_next (OpSem.Kscope OpSem.scope_store k) e_d
              (locals_d ++ [nm]) (state_push s_d PUSH)) s2'.
  Proof using TRANSL.
    destruct (match_State_inv MS) as
      ( floor & tf & tc & tk & e_i & locals_i & s_i & t & t_d & d & ctx & F
        & -> & WT & GLOB & TRf & TRc & MK & ENV & EDOM & DLEN & WF & HEAP & ALC & CNT & SM ).
    destruct WT as [ WTfn WTc WTk WTe WTs WTint ].
    inversion TRc as [ | | | | ?ctx0 ?d0 ?tail ?t_v0 ?e_v0 ?c_c0 tc_c ?t0 id_var
                                 LT FRESH TRcc EQa EQb EQc EQd EQe
                     | | | | | | | | | | | | ]; subst.
    inversion WTc as [ | | | | ?ctx0 ?t_v1 ?e_v1 ?c_c1 ?t_c1 WTinit WTcont
                     | | | | | | | | | | | | | ]; subst.
    assert (WTv: Value.wt_value v t_v)
      by exact (OpSem.Typing.eval_preserves_wt_env _ _ _ WTe _ _ _ WTinit EVAL).
    assert (SSNONNEG: (0 <= tf.(fn_extra).(IR.Prog.fn_stackspace))%Z).
    { rewrite (tr_fn_stackspace _ _ _ TRf). apply stack_usage_nonneg. }
    assert (ROOM: (List.length locals_d < List.length locals_i)%nat).
    { pose proof (wf_sb_ir_len _ WF) as LENir; cbn [sb_ir sb_ss] in LENir.
      rewrite LENir.
      apply (proj2 (Nat2Z.inj_lt _ _)).
      rewrite Z2Nat.id by exact SSNONNEG.
      exact LT. }
    destruct (smatch_push_withvar
                (mkstack_block locals_d locals_i tf.(fn_extra).(IR.Prog.fn_stackspace))
                F s_d (store s_i) v st_d' sg_d' nm
                SM WF ROOM PUSH)
      as ( nm_i & st_i & DEREF & MUTATE & SM' ).
    assert (POP: with_stack (List.removelast (ctxt_stack (push_stack tt ctx)))
                    (push_stack tt ctx) = ctx).
    { unfold push_stack.
      apply Ctxt.Facts.ctxt_ext;
        cbn [ctxt_pure ctxt_internal ctxt_stack ctxt_global with_stack];
        [ reflexivity | reflexivity | rewrite List.removelast_last; reflexivity
        | reflexivity ]. }
    assert (NE: exists u0 ul0, ctxt_stack (push_stack tt ctx) = u0 :: ul0).
    { unfold push_stack; cbn [ctxt_stack with_stack].
      destruct (ctxt_stack ctx) as [ | h l ];
        [ exists tt, [] | exists h, (l ++ [tt]) ]; reflexivity. }
    destruct NE as ( u0 & ul0 & NE ).
    exists (Semantics.State tf tc_c tk (Maps.PTree.set id_var Value.v_tt e_i)
              locals_i (state_mutate_store s_i MUTATE)).
    split.
    - eapply Smallstep.plus_left;
        [ apply Semantics.step_bind
        | apply Smallstep.star_one
        | reflexivity ].
      eapply Semantics.step_builtin_seq_cont;
        [ apply Semantics.seq_target_Kbind
        | apply Semantics.resolve_seq_Kbind
        | ].
      eapply Semantics.builtin_write_var;
        [ exact (eval_incl ENV EVAL)
        | cbn [sb_deep sb_ir] in DEREF; exact DEREF
        | exact WTv ].
    - eapply match_State with (floor := floor) (t := t)
                              (ctx := push_stack tt ctx) (F := F).
      + constructor.
        * exact WTfn.
        * exact WTcont.
        * eapply OpSem.Typing.wt_cont_Kscope_pop;
            [ exact NE | rewrite POP; exact WTk ].
        * exact WTe.
        * unfold push_stack; cbn [ctxt_stack with_stack].
          rewrite List.map_app; cbn [List.map]; rewrite WTs; reflexivity.
        * unfold push_stack; cbn [ctxt_internal with_stack]; exact WTint.
      + exact GLOB.
      + exact TRf.
      + exact TRcc.
      + eapply mc_scope_pop; [ exact NE | rewrite POP; exact MK ].
      + apply env_incl_set_fresh; [ | exact ENV ].
        apply (env_dom_fresh id_var EDOM).
        intros IN.
        destruct (proj1 (List.in_map_iff fst _ id_var) IN)
          as ( [ id0 ty0 ] & EQID & IN0 ).
        cbn [fst] in EQID; subst id0.
        assert (INB: In (id_var, ty0)
                       (f.(fn_params) ++ f.(fn_temps) ++ cmd_temps f.(fn_body))).
        { rewrite List.app_assoc.
          apply List.in_or_app; left; exact IN0. }
        pose proof (tr_fn_source_bound _ _ _ TRf _ _ INB) as LTf.
        exact (Pos.lt_irrefl id_var (Pos.lt_le_trans _ _ _ LTf FRESH)).
      + exact EDOM.
      + rewrite List.length_app; cbn [List.length]; lia.
      + exact (wf_stack_block_app [nm] WF ltac:(cbn [List.length]; lia)).
      + autorewrite with seplog; exact HEAP.
      + autorewrite with seplog; exact ALC.
      + autorewrite with seplog; exact CNT.
      + autorewrite with seplog; exact SM'.
  Qed.

  Lemma step_builtin_call_cont_correct
    (WTp: Deep.Typing.wt_program prog)
    [f c k k0 e_d locals_d] [s_d s_d' s_d'': Sm] [v]
    (CALLK: OpSem.resolve_call_cont k k0)
    (BUILTIN: OpSem.builtin c (Globalenvs.Genv.globalenv prog) e_d locals_d
                s_d v s_d')
    (POPSTACK: OpSem.pop_stack locals_d s_d' = Some s_d'')
    [s2]
    (MS: match_states (OpSem.State f c k e_d locals_d s_d) s2):
    exists s2',
      Smallstep.plus (@Semantics.step Sm) (Globalenvs.Genv.globalenv tprog)
        s2 Events.E0 s2'
      /\ match_states (OpSem.Returnstate v k0 s_d'') s2'.
  Proof using TRANSL.
    pose proof (match_State_wt_state MS) as WTs0.
    destruct (match_State_inv MS) as
      ( floor & tf & tc & tk & e_i & locals_i & s_i & t & t_d & d & ctx & F
        & -> & WT & GLOB & TRf & TRc & MK & ENV & EDOM & DLEN & WF & HEAP & ALC & CNT & SM ).
    destruct WT as [ WTfn WTc WTk WTe WTs WTint ].
    destruct (builtin_sim (ge_i := Globalenvs.Genv.globalenv tprog)
                TRc WTc WTe ENV HEAP ALC SM BUILTIN)
      as ( s_i' & BUILTINi & HEAPb & ALCb & CNTb & SMb ).
    pose proof POPSTACK as POPSTACKn.
    rewrite OpSem.Facts.pop_stack_n_length in POPSTACKn.
    unfold OpSem.pop_stack_n in POPSTACKn.
    destruct (proj1 state_pop_n_some POPSTACKn) as ( POPd & CNTd & HEAPd & ALCd ).
    destruct (smatch_pop_return
                (mkstack_block locals_d locals_i tf.(fn_extra).(IR.Prog.fn_stackspace))
                F (store s_d') (store s_i') (store s_d'') SMb WF POPd)
      as ( st_i & POPi & SMf ).
    cbn [sb_deep sb_ir sb_ss] in POPi.
    assert (DOMi: dominates st_i (scnt s_i'))
      by exact (dominates_iter_opt_pop _ _ _ _ POPi (state_store_dominates s_i')).
    exists (Semantics.Returnstate v tk
              (mk_state st_i (scnt s_i') (heap s_i') (alc s_i') DOMi
                 (state_heap_dominates s_i'))).
    split.
    - apply Smallstep.plus_one.
      eapply Semantics.step_builtin_call_cont.
      + exact (match_call_cont_is_call_cont (resolve_call_match CALLK MK)).
      + exact BUILTINi.
      + exact (state_pop_n_of_dominates DOMi POPi).
    - eapply match_Returnstate.
      + exact (OpSem.Typing.step_preservation prog _ _ _ WTp WTs0
                 (OpSem.step_builtin_call_cont _ f c k k0 e_d locals_d
                    s_d v s_d' s_d'' CALLK BUILTIN POPSTACK)).
      + exact (resolve_call_match CALLK MK).
      + rewrite heap_mk_state, HEAPd; exact HEAPb.
      + rewrite alc_mk_state, ALCd; exact ALCb.
      + rewrite scnt_mk_state, CNTb; exact CNT.
      + rewrite store_mk_state; exact SMf.
  Qed.

  Lemma step_builtin_seq_cont_correct
    (WTp: Deep.Typing.wt_program prog)
    [f c k e_d locals_d] [s_d s_d' s_d'': Sm]
    [c_next k' e_d' v n]
    (RESOLVE: OpSem.resolve_seq_cont k e_d v c_next e_d' k' n)
    (BUILTIN: OpSem.builtin c (Globalenvs.Genv.globalenv prog) e_d locals_d
                s_d v s_d')
    (POPS: OpSem.pop_stack_n n s_d' = Some s_d'')
    [s2]
    (MS: match_states (OpSem.State f c k e_d locals_d s_d) s2):
    exists s2',
      Smallstep.plus (@Semantics.step Sm) (Globalenvs.Genv.globalenv tprog)
        s2 Events.E0 s2'
      /\ match_states
           (OpSem.State f c_next k' e_d' (ListExt.removelast_n n locals_d) s_d'')
           s2'.
  Proof using TRANSL.
    destruct (match_State_inv MS) as
      ( floor & tf & tc & tk & e_i & locals_i & s_i & t & t_d & d & ctx & F
        & -> & WT & GLOB & TRf & TRc & MK & ENV & EDOM & DLEN & WF & HEAP & ALC & CNT & SM ).
    destruct WT as [ WTfn WTc WTk WTe WTs WTint ].
    destruct (builtin_sim (ge_i := Globalenvs.Genv.globalenv tprog)
                TRc WTc WTe ENV HEAP ALC SM BUILTIN)
      as ( s_i' & BUILTINi & HEAPb & ALCb & CNTb & SMb ).
    destruct (resolve_seq_match MK ENV EDOM (params_temps_bound TRf) WTk
                (OpSem.Typing.builtin_wt_value BUILTIN WTc WTe) WTe RESOLVE)
      as ( ctx' & tc' & tk' & t' & t_d' & target_id
           & RESi & TGTi & STK & LEn & TRc' & MK' & ENV' & GLOBc & INTc & WTcmd'
           & WTcont' & WTe' & EDOM' ).
    unfold OpSem.pop_stack_n in POPS.
    destruct (proj1 state_pop_n_some POPS) as ( POPd & CNTd & HEAPd & ALCd ).
    assert (LE: (n <= List.length locals_d)%nat) by (rewrite <- DLEN; exact LEn).
    pose proof (smatch_pop_n
                  (mkstack_block locals_d locals_i
                     tf.(fn_extra).(IR.Prog.fn_stackspace))
                  F (store s_d') (store s_i') n
                  (store s_d'') SMb LE POPd) as SMn.
    cbn [sb_deep sb_ir sb_ss] in SMn.
    assert (GLOB': Globalenvs.Genv.globalenv prog = ctxt_global ctx')
      by (rewrite GLOBc; exact GLOB).
    exists (Semantics.State tf tc' tk' (Maps.PTree.set target_id v e_i)
              locals_i s_i').
    split.
    - apply Smallstep.plus_one.
      eapply Semantics.step_builtin_seq_cont;
        [ exact TGTi | exact RESi | exact BUILTINi ].
    - eapply match_State with (floor := floor) (t := t') (t_d := t_d')
                              (ctx := ctx') (F := F).
      + constructor.
        * rewrite (OpSem.Typing.mk_glob_ctxt_eq GLOB'),
            <- (OpSem.Typing.mk_glob_ctxt_eq GLOB); exact WTfn.
        * exact WTcmd'.
        * exact WTcont'.
        * exact WTe'.
        * rewrite STK, WTs, ListExt.map_removelast_n; reflexivity.
        * rewrite INTc; exact WTint.
      + exact GLOB'.
      + exact TRf.
      + exact TRc'.
      + exact MK'.
      + exact ENV'.
      + exact EDOM'.
      + rewrite ListExt.length_removelast_n, <- DLEN; reflexivity.
      + exact (wf_stack_block_removelast_n _ WF).
      + rewrite HEAPd; exact HEAPb.
      + rewrite ALCd; exact ALCb.
      + rewrite CNTb; exact CNT.
      + exact SMn.
  Qed.

  Lemma step_return_call_seq_correct
    (WTp: Deep.Typing.wt_program prog)
    [v f e_d locals_d k] [s_d s_d': Sm] [c_next k' e_d' n]
    (RESOLVE: OpSem.resolve_seq_cont k e_d v c_next e_d' k' n)
    (POPS: OpSem.pop_stack_n n s_d = Some s_d')
    [s2]
    (MS: match_states
           (OpSem.Returnstate v (OpSem.Kcall f e_d locals_d k) s_d) s2):
    exists s2',
      Smallstep.plus (@Semantics.step Sm) (Globalenvs.Genv.globalenv tprog)
        s2 Events.E0 s2'
      /\ match_states
           (OpSem.State f c_next k' e_d' (ListExt.removelast_n n locals_d) s_d')
           s2'.
  Proof using TRANSL.
    destruct (match_Returnstate_inv MS) as
      ( tk & s_i & F & -> & WTs0 & MKC & HEAP & ALC & CNT & SM ).
    destruct (match_call_cont_Kcall_inv MKC) as
      ( floor' & ctx' & tfn & e_i & locals_i & tk' & F'
        & -> & -> & TRf & ENV & EDOM & WF & WTfnd & WTed & STACKd & INTd & GLOBd & MK ).
    inversion WTs0 as [ | | ?v0 ?k0 ?s0 ctx0 t WTres WTCC GLOB0 ]; subst.
    inversion WTCC as [ | ?ctx1 ?f0 ?e0 ?locals0 ?k1 ?t0 ty_env WTFd WTEd WTKd ];
      subst.
    assert (PURE: ctxt_pure ctx' = ty_env)
      by exact (wt_env_pure_unique WTed WTEd).
    assert (CTXEQ: ctx' = with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty)
                            (with_pure ty_env
                               (with_stack (List.map (fun _ => tt) locals_d) ctx0))).
    { apply Ctxt.Facts.ctxt_ext;
        cbn [ctxt_pure ctxt_internal ctxt_stack ctxt_global with_pure with_stack with_internal].
      - exact PURE.
      - exact INTd.
      - exact STACKd.
      - rewrite <- GLOBd; exact GLOB0. }
    assert (WTk: OpSem.Typing.wt_cont ctx' k t) by (rewrite CTXEQ; exact WTKd).
    destruct (resolve_seq_match MK ENV EDOM (params_temps_bound TRf) WTk
                WTres WTed RESOLVE)
      as ( ctx'' & tc'' & tk'' & t'' & t_d'' & target_id
           & RESi & TGTi & STK & LEn & TRc'' & MK'' & ENV'' & GLOBc & INTc & WTcmd''
           & WTcont'' & WTe'' & EDOM'' ).
    unfold OpSem.pop_stack_n in POPS.
    destruct (proj1 state_pop_n_some POPS) as ( POPd & CNTd & HEAPd & ALCd ).
    assert (LE: (n <= List.length locals_d)%nat) by exact LEn.
    pose proof (smatch_pop_n
                  (mkstack_block locals_d locals_i
                     tfn.(fn_extra).(IR.Prog.fn_stackspace))
                  F' (store s_d) (store s_i) n
                  (store s_d') SM LE POPd) as SMn.
    cbn [sb_deep sb_ir sb_ss] in SMn.
    assert (GLOB'': Globalenvs.Genv.globalenv prog = ctxt_global ctx'')
      by (rewrite GLOBc; exact GLOBd).
    exists (Semantics.State tfn tc'' tk'' (Maps.PTree.set target_id v e_i)
              locals_i s_i).
    split.
    - apply Smallstep.plus_one.
      eapply Semantics.step_return_call_seq; [ exact TGTi | exact RESi ].
    - eapply match_State with (floor := floor') (t := t'') (t_d := t_d'')
                              (ctx := ctx'') (F := F').
      + constructor.
        * rewrite (OpSem.Typing.mk_glob_ctxt_eq GLOB''),
            <- (OpSem.Typing.mk_glob_ctxt_eq GLOBd); exact WTfnd.
        * exact WTcmd''.
        * exact WTcont''.
        * exact WTe''.
        * exact (eq_trans STK
                   (eq_trans (f_equal (ListExt.removelast_n n) STACKd)
                      (ListExt.map_removelast_n (fun _ => tt) n locals_d))).
        * exact (eq_trans INTc INTd).
      + exact GLOB''.
      + exact TRf.
      + exact TRc''.
      + exact MK''.
      + exact ENV''.
      + exact EDOM''.
      + rewrite ListExt.length_removelast_n; reflexivity.
      + exact (wf_stack_block_removelast_n _ WF).
      + rewrite HEAPd; exact HEAP.
      + rewrite ALCd; exact ALC.
      + exact CNT.
      + exact SMn.
  Qed.

  Theorem transl_step_correct
    (WTp: Deep.Typing.wt_program prog)
    [s1 tr s1'] (STEP: OpSem.step (Globalenvs.Genv.globalenv prog) s1 tr s1')
    [s2] (MS: match_states s1 s2):
    exists s2',
      Smallstep.plus (@Semantics.step Sm) (Globalenvs.Genv.globalenv tprog)
        s2 tr s2'
      /\ match_states s1' s2'.
  Proof using TRANSL.
    inversion STEP; subst.
    - exact (step_bind_correct WTp MS).
    - exact (step_with_var_correct WTp EVAL PUSH MS).
    - exact (step_builtin_call_cont_correct WTp CALLK BUILTIN POP_STACK MS).
    - exact (step_builtin_seq_cont_correct WTp RESOLVE BUILTIN POPS MS).
    - exact (step_app_correct WTp EVAL FIND_SYMB FIND_FUNC SEQK MS).
    - exact (step_ifthenelse_correct WTp EVAL MS).
    - exact (step_while_correct WTp MS).
    - exact (step_internal_function_correct WTp WT_ARGS CALLK MS).
    - exact (step_return_call_seq_correct WTp RESOLVE POPS MS).
  Qed.

  Theorem transl_program_correct:
    Smallstep.forward_simulation (@OpSem.semantics Sm prog) (@Semantics.semantics Sm tprog).
  Proof using TRANSL.
    apply Smallstep.forward_simulation_plus
      with (match_states :=
              fun s1 s2 => Deep.Typing.wt_program prog /\ match_states s1 s2).
    - intros id.
      exact (proj1 (proj2 (senv_preserved TRANSL)) id).
    - intros s1 INIT.
      destruct (transl_initial_states INIT) as ( s2 & INITt & MS ).
      exists s2; split; [ exact INITt | split; [ | exact MS ] ].
      inversion INIT; assumption.
    - intros s1 s2 r ( WTp & MS ) FIN.
      exact (transl_final_states MS FIN).
    - intros s1 tr s1' STEP s2 ( WTp & MS ).
      destruct (transl_step_correct WTp STEP MS) as ( s2' & PLUS & MS' ).
      exists s2'; split; [ exact PLUS | split; [ exact WTp | exact MS' ] ].
  Qed.

End TRANSLATION.

Section Link.

  Local Transparent Deep.Linker.Linker_fundef IR.Linker.Linker_fundef IR.Linker.Linker_program.

  Local Lemma link_match_fundef (ctx1 ctx2: program) (f1: fundef) (tf1: IR.Prog.fundef)
    (f2: fundef) (tf2: IR.Prog.fundef) (f: fundef)
    (LINK: @Linking.link _ Deep.Linker.Linker_fundef f1 f2 = Some f)
    (MF1: match_fundef f1 tf1) (MF2: match_fundef f2 tf2)
    : exists tf, @Linking.link _ IR.Linker.Linker_fundef tf1 tf2 = Some tf
                 /\ (match_fundef f tf \/ match_fundef f tf).
  Proof.
    destruct MF1 as [ fn1 tfn1 TR1 | ef1 ], MF2 as [ fn2 tfn2 TR2 | ef2 ]; cbn in LINK |- *.
    - discriminate LINK.
    - destruct ef2; try discriminate LINK; injection LINK as <-.
      eexists; split; [ reflexivity | left; apply match_fundef_internal; exact TR1 ].
    - destruct ef1; try discriminate LINK; injection LINK as <-.
      eexists; split; [ reflexivity | left; apply match_fundef_internal; exact TR2 ].
    - destruct (AST.external_function_eq ef1 ef2) as [ <- | NE ]; [ | discriminate LINK ].
      injection LINK as <-.
      exists (AST.External ef1); split; [ | left; apply match_fundef_external ].
      destruct (AST.external_function_eq ef1 ef1) as [ _ | NE ];
        [ reflexivity | contradiction NE; reflexivity ].
  Qed.

  Global Instance TransfIRgenLink: TransfLink match_prog.
  Proof.
    intros p1 p2 tp1 tp2 p LINK MATCH1 MATCH2.
    destruct (Linking.link_linkorder _ _ _ LINK) as [ LO1 LO2 ].
    destruct (Linking.link_match_program (fun _: program => match_fundef) match_varinfo
                link_match_fundef Common.Linker.link_match_varinfo_eq
                p1 p2 p _ _ _ _ _ (proj1 (Deep.Linker.link_program_inv LINK))
                MATCH1 MATCH2 LO1 LO2)
      as ( tq & TLINK & TMATCH ).
    exists (Common.Prog.mkprogram (AST.prog_defs tq) (AST.prog_public tq) (AST.prog_main tq) tt).
    split.
    - cbn [ Linking.link IR.Linker.Linker_program ].
      unfold IR.Linker.link_program; rewrite TLINK; reflexivity.
    - destruct tq as [ defs public main ]; exact TMATCH.
  Qed.

End Link.
