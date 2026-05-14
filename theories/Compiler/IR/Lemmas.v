From Stdlib Require ZArith.

From GallinaC.Utils Require Import NatExt ListExt.

From GallinaC.Imp Require Heap Memval.
From GallinaC.Imp Require Import Store.

From GallinaC.Compiler.Common Require Import Types Value Expr CCInj.
From GallinaC.Compiler.IR Require Import Semantics Prog Typing.

Section Pure.

  Lemma eval_progress {ctx e t f env} (Hwt_expr: Expr.wt_expr ctx e t) (Hwt_env: wt_env f ctx env): { v & Value.wt_value v t & eval e env = Some v }.
  Proof.
    induction Hwt_expr; simpl;
      try (now (eexists; first [ now constructor | reflexivity ])).
    - specialize (Hwt_env.(wv_ty_env) var_id t true GET); cbn;
        intros ([ v GETval WTval] & IN).
      exists v; [ assumption | now rewrite GETval ].
    - destruct IHHwt_expr as [ v WTval EVAL ].
      apply Facts.type_of_value_complete in WTval.
      destruct v; try discriminate.
      exists (v_bool (negb b0)); [ now repeat constructor | now rewrite EVAL ].
    - destruct IHHwt_expr1 as [ v1 WTval1 EVAL1 ].
      destruct IHHwt_expr2 as [ v2 WTval2 EVAL2 ].
      apply Facts.type_of_value_complete in WTval1, WTval2.
      destruct v1, v2; try discriminate.
      now eexists; [ | rewrite EVAL1, EVAL2; reflexivity ]; constructor.
    - destruct IHHwt_expr1 as [ v1 WTval1 EVAL1 ].
      destruct IHHwt_expr2 as [ v2 WTval2 EVAL2 ].
      apply Facts.type_of_value_complete in WTval1, WTval2.
      destruct v1, v2; try discriminate.
      now eexists; [ | rewrite EVAL1, EVAL2; reflexivity ]; constructor.
  Qed.

  Lemma eval_t_unit {ctx e f env} (Hwt_expr: Expr.wt_expr ctx e Types.t_unit) (Hwt_env: wt_env f ctx env): eval e env = Some Value.v_tt.
  Proof.
    remember Types.t_unit as t.
    induction Hwt_expr; try discriminate; subst; cbn; try reflexivity.
    specialize (Hwt_env.(wv_ty_env) var_id Types.t_unit true GET); cbn;
      intros ( [ v GETval WTval ] & HIn ).
    inversion WTval; subst.
    now rewrite GETval.
  Qed.

  Lemma eval_v_tt
    {ctx e t f env}
    (Hwt_expr: Expr.wt_expr ctx e t)
    (Hwt_env: wt_env f ctx env)
    (Heval: eval e env = Some Value.v_tt)
    : t = Types.t_unit.
  Proof.
    induction Hwt_expr;
      auto;
      (try (simpl in Heval; congruence)).
    - cbn in Heval.
      destruct (Maps.PTree.get var_id env) as [ v | ] eqn:Eget_val_env; [ inversion Heval; subst; clear Heval | discriminate ].
      specialize (Hwt_env.(wv_ty_env) var_id t true GET) as ( [ v GETval WTval ] & HIntemps).
      assert (v = Value.v_tt) by congruence; subst.
      now inversion WTval.
    - simpl in Heval.
      destruct (eval _ _); (try (destruct v)); discriminate.
    - simpl in Heval.
      destruct (eval _ _); try discriminate;
        destruct v; try discriminate;
        destruct (eval _ _); try discriminate;
        destruct v; discriminate.
    - simpl in Heval;
        destruct (eval _ _); try discriminate;
        destruct v; try discriminate;
        destruct (eval _ _); try discriminate;
        destruct v; discriminate.
  Qed.

  Lemma value_compcert_sized {St inj v tv} (INJ: @CCInj.InjValue St inj v tv): Value.Sized v.
  Proof.
    apply Facts.inject_value_complete in INJ.
    destruct v; try constructor; discriminate.
  Qed.

End Pure.
#[global] Hint Resolve value_compcert_sized: deep_gallinac.

Section Typing.

  Lemma derive_wt_ret_tt {ctx c t}
    (WT: Typing.wt_cmd ctx c t)
    : Typing.wt_cmd ctx (Cmd.c_ret e_tt t_unit) t_unit.
  Proof.
    repeat constructor.
  Qed.

End Typing.
#[global] Hint Immediate derive_wt_ret_tt: deep_gallinac.

Section Rewriting.

  Lemma signature_main: AST.signature_main = mk_signature [] t_nat.
  Proof.
    reflexivity.
  Qed.

  Lemma call_cont_eq_inversion {St} {A: Type} {k} {a'} {a a0: A} (Hcall_cont: @is_call_cont St k):
    match k with
    | Semantics.Kbind b_id c k => (a' b_id c k)
    | _ => a
    end = a0 ->
    a = a0.
  Proof.
    now inversion Hcall_cont.
  Qed.

  Lemma cont_eq_inversion {St} {A: Type} {k: @cont St} {a'} {a a0: A}:
    match k with
    | Semantics.Kbind b_id c k => a' b_id c k
    | _ => a
    end = a0 ->
    (a = a0 \/ exists b_id c k', k = Semantics.Kbind b_id c k' /\ a' b_id c k' = a0).
  Proof.
    intros Hk.
    destruct k as [ | b_id c k' | | | ] eqn:Ek; try (now left).
    right.
    exists b_id, c, k'.
    split; auto.
  Qed.

  Lemma seq_cont_target_fun {St} {k target1 target2}
    (Hseq_target1: @seq_cont_target St k target1)
    (Hseq_target2: @seq_cont_target St k target2)
    : target2 = target1.
  Proof.
    now inversion Hseq_target1; subst; inversion Hseq_target2; subst.
  Qed.

  Lemma resolve_seq_cont_fun {St} {k v c_next1 c_next2 k'1 k'2}
    (Hseq_cont1: @resolve_seq_cont St k v c_next1 k'1)
    (Hseq_cont2: @resolve_seq_cont St k v c_next2 k'2)
    : c_next2 = c_next1 /\ k'2 = k'1.
  Proof.
    inversion Hseq_cont1; subst; inversion Hseq_cont2; subst;
      split; reflexivity.
  Qed.

  Lemma wt_app_fn_return {V f_id t_out args prog b} {f: function} {ctx}
    (Hfind_symbol: Globalenvs.Genv.find_symbol (Globalenvs.Genv.globalenv prog) f_id = Some b)
    (Hfind_funct_ptr: @Globalenvs.Genv.find_funct_ptr _ V (Globalenvs.Genv.globalenv prog) b = Some (AST.Internal f))
    (Hwt_cmd : Typing.wt_cmd ctx (Cmd.c_app f_id t_out args) t_out)
    : t_out = f.(fn_return).
  Proof.
    inversion Hwt_cmd; subst.

  Abort.

End Rewriting.

Section Determinism.

  Import Value.Facts.
  Import Expr.Facts.
  Import CCInj.Facts.

  Context {St: Store}.
  Context {Hp: Heap.Heap}.

  Lemma single_events (p: program): Smallstep.single_events (@semantics St Hp p).
  Proof using St Hp.
    unfold Smallstep.single_events; cbn;
      intros s t s' STEP.
    inversion STEP; subst; repeat constructor.
  Qed.

  Lemma receptive (p: program): Smallstep.receptive (@semantics St Hp p).
  Proof using St Hp.
    constructor.
    - intros s t1 s1 t2 Hstep1 Hmatch.
      inversion Hstep1; subst; inversion Hmatch; subst;
        eexists; eassumption.
    - apply single_events.
  Qed.

  Lemma strongly_receptive (p: program): Smallstep.strongly_receptive (@semantics St Hp p).
  Proof using St Hp.
    constructor.
    - intros s ev1 t1 s1 ev2 Hstep Hmatch_traces.
      inversion Hstep; subst; inversion X.
    - intros s t s' Hstep.
      inversion Hstep; now cbn.
  Qed.

  Lemma builtin_deterministic {c genv env locals sp m s inj v m' s' inj' v0 m'0 s'0 inj'0}
    (Hbuiltin : @builtin St Hp c genv env locals sp s m inj v s' m' inj')
    (Hbuiltin': @builtin St Hp c genv env locals sp s m inj v0 s'0 m'0 inj'0):
    v0 = v /\ m'0 = m' /\ s'0 = s' /\ inj'0 = inj'.
  Proof using St Hp.
    destruct Hbuiltin; inversion Hbuiltin'; subst.
    - repeat split; congruence.
    - repeat split; try (congruence).
      assert (nm0 = nm) by congruence; subst.
      destruct v0, v; cbn in *; congruence; subst.
    - split; [ reflexivity | ].
      assert (nm0 = nm) by congruence; subst; clear DEREF0.
      assert (v1 = v) by congruence; subst; clear EVAL0.
      assert (st'0 = st') by congruence; subst; clear MUTATE0.
      split; [ | now auto ].
      destruct STORE as [ (SIZED & (v_cc & mc & STORE & TMC & INJ)) | (NSIZED & EQ) ],
          STORE0 as [ (SIZED0 & (v_cc0 & mc0 & STORE0 & TMC0 & INJ0)) | (NSIZED0 & EQ0) ];
        [ clear WT0 | contradiction | contradiction | congruence ].
      assert (mc0 = mc) by congruence; subst; clear TMC0.
      specialize (InjValue_fun INJ INJ0) as EQ; subst; clear INJ0.
      congruence.
    - assert (v_size0 = v_size) by congruence; subst; clear EVAL_SIZE0.
      assert (v_init0 = v_init) by congruence; subst; clear EVAL_INIT0.
      assert (hp'0 = hp') by congruence; subst;
        assert (addr0 = addr) by congruence; subst;
        assert (prov0 = prov) by congruence; subst;
        clear ALLOC_GC0.
      assert (mc0 = mc) by congruence; subst; clear EQmc0.
      specialize (InjValue_fun INJ INJ0) as EQ; subst; clear INJ0.
      assert (m_i2 = m_i0) by congruence;
        assert (b_cc0 = b_cc) by congruence;
        subst; clear ALLOC_CC0.
      assert (m_i3 = m_i1) by congruence; subst; clear STORE_SIZE0.
      assert (m'0 = m') by congruence; subst; clear STORE_INIT0.
      now auto.
    - assert (v_ptr0 = v_ptr) by congruence; subst; clear EVAL0.
      assert (v0 = v_read) by (destruct v0, v_read; cbn in *; congruence); subst; clear LOOKUP0.
      now auto.
    - assert (v_ptr0 = v_ptr) by congruence; subst; clear EVAL_ptr0.
      assert (v_data0 = v_data) by congruence; subst; clear EVAL_data0.
      assert (hp'0 = hp') by congruence; subst; clear MUTATE0.
      destruct STORE as [ (SIZED & (v_ptr_b_cc & v_ptr_ofs_cc & v_data_cc & mc & STORE & TMC & INJptr & INJdata)) | (NSIZED & EQ) ],
          STORE0 as [ (SIZED0 & (v_ptr_b_cc0 & v_ptr_ofs_cc0 & v_data_cc0 & mc0 & STORE0 & TMC0 & INJptr0 & INJdata0)) | (NSIZED0 & EQ0) ]; [ | contradiction | contradiction | now subst ].
      specialize (InjValue_fun INJptr INJptr0) as EQ; inversion EQ; subst; clear EQ.
      specialize (InjValue_fun INJdata INJdata0) as EQ; subst.
      clear WT0 INJptr0 INJdata0.
      assert (mc0 = mc) by congruence; subst; clear TMC0.
      assert (m'0 = m') by congruence; subst; clear STORE0.
      now auto.
    - assert (addr0 = addr) by congruence; subst;
        assert (prov0 = prov) by congruence; subst;
        clear EVAL0.
      assert (hp'0 = hp') by congruence; subst; clear FREE_GC0.
      specialize (InjValue_fun INJ INJ0) as EQ; inversion EQ; subst; clear EQ INJ0.
      assert (m'0 = m') by congruence; subst; clear FREE_CC0.
 auto.
    - assert (v_ptr0 = v_ptr) by congruence; subst.
      assert (v_shift0 = v_shift) by congruence; subst.
      specialize (Pointer.Pointer.Shift_fw_fun _ _ _ _ SHIFT SHIFT0) as EQ; subst.
      now auto.
    - assert (v_ptr0 = v_ptr) by congruence; subst.
      assert (v_shift0 = v_shift) by congruence; subst.
      specialize (Pointer.Pointer.Shift_bw_fun _ _ _ _ SHIFT SHIFT0) as EQ; subst.
      now auto.
    - assert (v_ptr_l0 = v_ptr_l) by congruence; subst; clear EVAL_l0.
      assert (v_ptr_r0 = v_ptr_r) by congruence; subst; clear EVAL_r0.
      assert (b0 = b) by congruence; subst.
      now auto.
  Qed.

  Lemma determinate (p: program) : Smallstep.determinate (@semantics St Hp p).
  Proof using St Hp.
    constructor; cbn.
    - intros s t1 s1 t2 s2 Hstep1 Hstep2.
      split; [ | intros Heq; subst ].
      + inversion Hstep1; subst; inversion Hstep2; subst; try (apply Events.match_traces_E0).
      + inversion Hstep1; subst;
          inversion Hstep2; subst;
          (try (now inversion BUILTIN));
          (try (destruct (builtin_deterministic BUILTIN BUILTIN0) as (eqv & eqm' & eqs' & eqinj');
                subst));
          (try (specialize (seq_cont_target_fun Hseq_target Hseq_target0); subst));
          (try (specialize (resolve_seq_cont_fun Hresolve_seq Hresolve_seq0) as (eq1 & eq2); subst));
          (try (replace b0 with b by congruence));
          (try (replace sp0 with sp by congruence));
          (try (congruence));
          (try (now inversion Hcall_cont));
          (try (now inversion Hseq_cont));
          (try (now inversion Hcall_cont; subst; first [ inversion Hseq_cont | inversion Hseq_target ])).
    - eapply Smallstep.sr_traces.
      apply receptive.
    - intros s1 s2 Hinitial1 Hinitial2.
      inversion Hinitial1; subst; inversion Hinitial2; subst.
      congruence.
    - intros s r Hfinal t s' Hstep.
      inversion Hfinal; subst.
      inversion Hstep; subst.
    - intros s r1 r2 Hfinal1 Hfinal2.
      inversion Hfinal1; subst; inversion Hfinal2; subst.
      reflexivity.
  Qed.

End Determinism.

Section WT.

  Import Memory.
  Import ZArith.
  Import Heap.Facts Store.Facts.

  Lemma inj_has_argtype {St inj v tv t tt}
    (WT: wt_value v t)
    (INJ: @CCInj.InjValue St inj v tv)
    (XT: type_to_xtype t = Some tt)
    : Values.Val.has_argtype tv tt.
  Proof.
    induction WT;
      inversion INJ; subst;
      inversion XT; subst;
      (try (now constructor)).
    - destruct b; now constructor.
    - destruct (Archi.ptr64) eqn:Earchi;
        destruct Heq as (i & Hunsigned & Heq);
        subst;
        unfold Values.Val.has_argtype;
        unfold type_to_xtype;
        unfold AST.Xsize_t;
        now rewrite Earchi.
  Qed.

  Lemma xtype_of_type_sized t (Hsized: Types.Sized t): exists xt, type_to_xtype t = Some xt.
    destruct Hsized; now eexists.
  Qed.

  Lemma init_state_correct_mem {St Hp}:
    forall p st m inj,
      @init_state St Hp p = Some (st, m, inj) -> Globalenvs.Genv.init_mem p = Some m.
  Proof.
    unfold init_state, Globalenvs.Genv.init_mem.
    intros [ defs public id_main [ id_malloc id_free ] ]
      st m inj EQ.
    cbv [AST.prog_defs program_of_program prog_defs].
    cbn; fold fundef.
    generalize (Globalenvs.Genv.empty_genv fundef vardef public) as ge.
    (* generalize Mem.empty as m0. *)
    (* generalize (@Primitives.emp St Hp) as s0. *)
    (* induction defs as  [ | [ id g ] defs ]; *)
    (*   cbn; intros s0 m0 inj0 ge Halloc_globals. *)
    (* - congruence. *)
    (* - unfold alloc_global in Halloc_globals. *)
    (*   destruct g. *)
    (*   + destruct (Mem.alloc m0 0%Z 1) as [ m1 b ] eqn:Ealloc. *)
    (*     destruct (Mem.drop_perm m1 b 0 1 Memtype.Nonempty) as [ m2 | ] eqn:Edrop_perm; [ | discriminate ]. *)
    (*     specialize (IHdefs s0 m2 _ _ Halloc_globals). *)
    (*     eapply IHdefs; eauto. *)
    (*   + destruct v as [ [ vtype vname ] init readonly volatile ]. *)
    (*     destruct init as [ | init [ | ] ] > [ discriminate | | discriminate ]. *)
    (*     destruct readonly > [ discriminate | ]. *)
    (*     destruct volatile > [ discriminate | ]. *)
    (*     cbn; cbn in Halloc_globals. *)
    (*     repeat (rewrite (Z.add_0_r (AST.init_data_size init)) in * ). *)
    (*     destruct (Mem.alloc m0 0 (AST.init_data_size init)) as [ m1 b ] eqn:Ealloc. *)
    (*     destruct (Globalenvs.store_zeros m1 b 0 (AST.init_data_size init)) as [ m2 | ] eqn:Estore > [ | discriminate ]. *)
    (*     unfold store_init_data in Halloc_globals. *)
    (*     unfold Globalenvs.Genv.store_init_data. *)
    (*     destruct init; *)
    (*       cbn; cbn in Halloc_globals; *)
    (*       (try discriminate); *)
    (*       (try *)
    (*          ( *)
    (*            destruct (Mem.store _ m2 b 0 _) as [ m3 | ] eqn:Estore'; *)
    (*            try discriminate; *)
    (*            destruct (Mem.drop_perm m3 b 0 _ Memtype.Writable) as [ m4 | ] eqn:Edrop'; *)
    (*            try discriminate; *)
    (*            eapply IHdefs; *)
    (*            now eauto *)
    (*          ) *)
    (*       ). *)
  Admitted.

  Lemma empty_state_wf_inj {St Hp}: @CCInj.wf St Hp Primitives.emp Mem.empty (Build_injection St [] [] []).
  Proof.
    constructor; cbn; intros;
      (try (now constructor));
      (try (contradiction));
      exfalso.
    eapply Heap.emp_no_sub; eauto.
    eapply emp_spec; eauto.
  Qed.

  Lemma init_state_wf_inj
    {St Hp p s m inj}
    (Hwt_prog: Typing.wt_program p) (Einit_state: init_state p = Some (s, m, inj))
    : @CCInj.wf St Hp s m inj.
  Proof.
    destruct p as [ defs public main [ malloc free ] ].
    revert Hwt_prog Einit_state.
    unfold init_state.
    specialize (@empty_state_wf_inj St Hp).
    generalize (Build_injection St [] [] []) as inj0.
    generalize Mem.empty as m0.
    generalize (@Primitives.emp St Hp) as s0.
    revert public.
    induction defs as [ | ( gid & [ f | v ] )  defs ].
    - cbn; intros; inversion Einit_state; subst; auto.
    - cbn; intros.
      destruct (Mem.alloc m0 0 1) as ( m1 & b ).
      destruct (Mem.drop_perm m1 b 0 1 Nonempty) as [ m2 | ]; [ | discriminate ].
      cbn in IHdefs.
      specialize (IHdefs public s0 m2 {| inj_hp_map := inj_hp_map inj0; inj_st_map := inj_st_map inj0; inj_fn_map := (gid, b) :: inj_fn_map inj0 |}).
      assert (Hwf': CCInj.wf s0 m2 {|
                                   inj_hp_map := inj_hp_map inj0;
                                   inj_st_map := inj_st_map inj0;
                                   inj_fn_map := (gid, b) :: inj_fn_map inj0
                                 |}).
      {
        constructor; cbn;
          (try (inversion H; now auto)).
        -
  Admitted.

  Lemma wt_initial_state {St Hp prog S}
    (Hinit: @initial_state St Hp prog S)
    : wt_state prog S.
  Proof.
    inversion Hinit; subst.
    destruct init_main_sig;
        (try
           (unfold signature_of_signature in init_main_sig_is_sig_main;
            cbn in init_main_sig_is_sig_main;
            inversion init_main_sig_is_sig_main)).
    eapply wt_Callstate with (sig := {| sig_args := []; sig_res := t_nat |}); auto.
    - admit.
    - admit.
    - admit.
    - now repeat constructor.
  Admitted.

End WT.

Section Free.
  Import Arith ZArith List.
  Import ListExt.
  Import Coqlib.

  Local Open Scope nat_scope.

  Lemma sp_free_success_State {St Hp fn c k env locals sp s m inj ctx t}
    (WT: @Semantics.wt_State St Hp fn c k env locals sp s m inj ctx t)
    : exists m', Memory.Mem.free m sp 0%Z fn.(fn_extra).(fn_stackspace) = Some m'.
  Proof.
    destruct (Memory.Mem.range_perm_free m sp 0 fn.(fn_extra).(fn_stackspace)) as (m' & Heq); [ | now exists m' ].

    destruct fn as [ fn_return fn_params fn_temps fn_body [ fn_stackspace ] ].
    revert fn_stackspace WT.
    induction locals using rev_ind; admit.
    (* - intros; cbn in *; *)
    (*     inversion WT; subst; *)
    (*     inversion State_wt_function; subst; *)
    (*     cbn in *; subst; *)
    (*     cbn in *. *)
    (*   intros lo HFalse; lia. *)

    (* - intros; *)
    (*     cbn in *; *)
    (*     inversion WT; subst; *)
    (*     inversion State_wt_function; subst; *)
    (*     inversion State_wf_inj; subst; *)
    (*     cbn in *; subst; *)
    (*     rewrite last_length in *. *)
    (*   assert (IHHwt_state: wt_State *)
    (*                          {| *)
    (*                            fn_return := &fn_return; *)
    (*                            fn_params := &fn_params; *)
    (*                            fn_temps := &fn_temps; *)
    (*                            fn_locals := &fn_locals; *)
    (*                            fn_body := &fn_body; *)
    (*                            fn_stackspace := (Datatypes.length &fn_locals) * store_memsize; *)
    (*                          |} c k &env sp s m inj ctx t). *)
    (*   { *)
    (*     constructor; eauto. *)
    (*     - econstructor; cbn; eauto. *)
    (*       apply (Forall_app (fun loc => Typing.ground (local_type loc)) &fn_locals [x]); eauto. *)
    (*       intros n loc Hnth. *)
    (*       eapply wt_fn_locals_sorted; eauto; cbn. *)
    (*       rewrite nth_error_app1; auto. *)
    (*       apply nth_error_Some; congruence. *)
    (*     - constructor; cbn; *)
    (*         inversion State_wt_env; subst; cbn in *; eauto. *)
    (*     - cbn; intros; eapply &State_wt_stack; eauto with datatypes. *)
    (*   } *)
    (*   specialize (IHfn_locals _ IHHwt_state). *)

    (*   intros ofst [Hrangele' Hrangelt']. *)
    (*   specialize (Z2Nat.inj_le 0 ofst (Z.le_refl 0)) as Hrangele. *)
    (*   specialize (Hrangele Hrangele') as [ Hrangele _ ]. *)
    (*   specialize (Hrangele Hrangele'). *)
    (*   cbn in Hrangele. *)
    (*   specialize (Z2Nat.inj_lt ofst (Z.of_nat (S (Datatypes.length &fn_locals) * store_memsize)) Hrangele' ltac:(eapply Nat2Z.is_nonneg; eauto)) as [ Hrangelt _ ]. *)
    (*   specialize (Hrangelt Hrangelt'). *)
    (*   rewrite Nat2Z.id in Hrangelt. *)

    (*   rewrite <- (Z2Nat.id ofst) > [ | assumption ]. *)
    (*   specialize (NatExt.interval_split *)
    (*                 (fun o => Memory.Mem.perm m sp (Z.of_nat o) Memtype.Cur Memtype.Freeable) *)
    (*                 0 (store_memsize * Datatypes.length &fn_locals) *)
    (*                 (store_memsize * (S (Datatypes.length &fn_locals))) *)
    (*              ) *)
    (*     as Hproof; *)
    (*     apply Hproof; (try (lia)); clear Hproof. *)
    (*   + intros n [ Hle Hlt ]. *)
    (*     apply (IHfn_locals (Z.of_nat n)); split; auto. *)
    (*     apply Nat2Z.is_nonneg. *)
    (*     apply Nat2Z.inj_lt. *)
    (*     now rewrite Nat.mul_comm. *)
    (*   + intros n [ Hle Hlt ]. *)

    (*     specialize (&State_wt_stack x ltac:(eapply in_elt; eauto)). *)
    (*     apply (&mem_perm_of_store _ _ _ _ &State_wt_stack). *)
    (*     constructor. *)
    (*     * apply Nat2Z.inj_le. *)
    (*       assert (HProof1: local_ofst x = Datatypes.length &fn_locals) by apply (&wt_fn_locals_sorted (Datatypes.length &fn_locals) x ltac:(eapply nth_error_last; eauto)). *)
    (*       lia. *)
    (*     * apply Nat2Z.inj_lt. *)
    (*       rewrite Nat.add_comm, mult_n_Sm. *)
    (*       assert (HProof1: local_ofst x = Datatypes.length &fn_locals) by apply (&wt_fn_locals_sorted (Datatypes.length &fn_locals) x ltac:(eapply nth_error_last; eauto)). *)
    (*       lia. *)
  Admitted.

  Lemma sp_free_success {St Hp prog f c k env locals sp s m inj}
    (WT: @Semantics.wt_state St Hp prog (Semantics.State f c k env locals sp s m inj))
    : exists m', Memory.Mem.free m sp 0%Z f.(fn_extra).(fn_stackspace) = Some m'.
  Proof.
    inversion WT; subst.
    eapply sp_free_success_State; now eauto.
  Qed.

End Free.

Section Preservation.

  Lemma prim_effect_wt_value {St Hp f c k env locals sp s m inj ctx t S2 ge v s' m' inj'}
    (Hwt_state: wt_State f c k env locals sp s m inj ctx t)
    (Hstep: step ge (State f c k env locals sp s m inj) Events.E0 S2)
    (BUILTIN: @builtin St Hp c ge env locals sp s m inj v s' m' inj')
    : Value.wt_value v t.
  Proof.
    inversion Hwt_state; subst.
    inversion State_wt_cmd as [ WTcmd ].
    inversion WTcmd; subst;
      inversion BUILTIN; subst;
      try (assumption);
      try (now constructor).
  Qed.

  Lemma mutate_store_wf_inj {St Hp s m inj nm v s' typ v_ptr_b_cc v_ptr_ofs_cc m'}
    (WF: @CCInj.wf St Hp s m inj)
    (MUT: Store.mutate (Primitives.store s) nm v = Some s')
    (CC: inhabited (Types.Sized typ) /\
           (exists v_cc (mc : AST.memory_chunk),
               Memory.Mem.store mc m v_ptr_b_cc v_ptr_ofs_cc v_cc = Some m' /\
                 type_mem_chunk typ = Some mc /\ CCInj.InjValue inj (Value.value_of_memval v) v_cc) \/
           (notT (Types.Sized typ) /\ m' = m))
        : CCInj.wf (Primitives.mkState s' (Primitives.heap s)) m' inj.
  Proof.
    constructor;
      try (now destruct WF); cbn.
    - intros b o v_hp SUBSTATE.
      destruct CC as [ (TSZ_mut & v_cc_mut & mc_mut & Estore_mut & TMC_mut & INJ_mut) | (NTSZ & Heq) ]; subst.
      + specialize (WF.(mem_contents_of_heap) SUBSTATE) as (b' & v' & mc & VMC & INJ & Hload); exists b', v', mc.
        split; [ assumption | ].
        split; [ assumption | ].
        intros o' LT.
        specialize (Hload o' LT) as [ PROOF1 PROOF2 ].
        admit.
      + specialize (WF.(mem_contents_of_heap) SUBSTATE) as (b' & v' & mc & VMC & INJ & Hload); exists b', v', mc.
        split; [ assumption | ].
        split; [ assumption | ].
        admit.
    - intros nm' v_st HBindsTo.
      admit.
    - intros f_id b HIn.
      destruct CC as [ (TSZ_mut & v_cc_mut & mc_mut & Estore_mut & TMC_mut & INJ_mut) | (NTSZ & Heq) ]; subst.
      + admit.
      + admit.
    - intros nm' b o freeable HIn.
      destruct CC as [ (TSZ_mut & v_cc_mut & mc_mut & Estore_mut & TMC_mut & INJ_mut) | (NTSZ & Heq) ]; subst.
      + intros ofs Hlelt.
        eapply Memory.Mem.perm_store_1; eauto.
        eapply (mem_perm_of_store WF _ _ _ _ HIn ofs Hlelt).
      + intros ofs Hlelt.
        eapply (mem_perm_of_store WF _ _ _ _ HIn ofs Hlelt).
  Admitted.

  Lemma builtin_wf_inject {St Hp c ge env locals sp s m inj v s' m' inj'}
    (Heffect: @builtin St Hp c ge env locals sp s m inj v s' m' inj')
    (Hwf_inj: CCInj.wf s m inj)
    : CCInj.wf s' m' inj'.
  Proof.
    inversion Heffect; subst; auto.
    all: admit.
  Admitted.

  Lemma pop_stack_wf_inject {St Hp sp f s m inj s' m' inj'}
    (Hwf_inj: CCInj.wf s m inj)
    (Hpop_stack: @pop_stack St Hp sp f.(fn_stackspace) s m inj = Some (s', m', inj'))
    : CCInj.wf s' m' inj'.
  Proof.
  Admitted.

  Lemma preservation_State_State_effect {St Hp f c k e locals sp s m inj ctx t ge f' c' k' e' locals' sp' s' m' inj' v target_id t'}
    (WT: @Semantics.wt_State St Hp f c k e locals sp s m inj ctx t)
    (Step: @Semantics.step St Hp ge (State f c k e locals sp s m inj) Events.E0 (State f' c' k' e' locals' sp' s' m' inj'))
    (Eff: @builtin St Hp c ge e locals sp s m inj v s' m' inj')
    (ST: seq_cont_target k target_id)
    : Semantics.wt_State f c' k' e' locals sp' s' m' inj' (Ctxt.set_pure target_id (t, true) ctx) t'.
  Proof.
    inversion WT; subst.
    inversion Step; subst;
      inversion Eff; subst.
  Abort.

  Lemma preservation_State_State {St Hp f c k e locals sp s m inj ctx t ge f' c' k' e' locals' sp' s' m' inj'}
    (Hwt_State: @Semantics.wt_State St Hp f c k e locals sp s m inj ctx t)
    (Hstep: @Semantics.step St Hp ge (State f c k e locals sp s m inj) Events.E0 (State f' c' k' e' locals' sp' s' m' inj'))
    : forall ctx' t'
             (Hstep_ctxt_effect: @step_ctxt_effect St (*Hp*) ctx c k ctx')
             (Hwt_cmd: Typing.wt_cmd ctx' c' t'),
      Semantics.wt_State f c' k' e' locals' sp' s' m' inj' ctx' t'.
  Proof.
  Admitted.

  (* Lemma preservation_Callstate_State {St Hp prog fd args k s m inj t f c k' e sp s' m' inj' ge} *)
  (*   (Hwt_Callstate: @Semantics.wt_state St Hp prog (Semantics.Callstate fd args k s m inj)) *)
  (*   (Hstep: @Semantics.step St Hp ge (Semantics.Callstate fd args k s m inj) t (Semantics.State f c k' e sp s' m' inj')) *)
  (*   : forall ctx t (Hwt_cmd: Cmd.wt_cmd ctx c t), Semantics.wt_State f c k' e sp s' m' inj' ctx t. *)
  (* Proof. *)
  (* Admitted. *)

  (* Lemma preservation_Returnstate_State {St Hp prog v k s m inj t f c k' e sp s' m' inj' ge} *)
  (*   (Hwt_Returnstate: @Semantics.wt_state St Hp prog (Semantics.Returnstate v k s m inj)) *)
  (*   (Hstep: @Semantics.step St Hp ge (Semantics.Returnstate v k s m inj) t (Semantics.State f c k' e sp s' m' inj')) *)
  (*   : forall ctx t (Hwt_cmd: Cmd.wt_cmd ctx c t), Semantics.wt_State f c k' e sp s' m' inj' ctx t. *)
  (* Proof. *)
  (* Admitted. *)

  (* Lemma preservation_State_Returnstate {St Hp prog f c k e sp s m inj ctx t ge v k' s' m' inj'} *)
  (*   (Hwt_State: @wt_State St Hp f c k e sp s m inj ctx t) *)
  (*   (Hstep: @step St Hp ge (State f c k e sp s m inj) Events.E0 (Semantics.Returnstate v k' s' m' inj')) *)
  (*   : @wt_state St Hp prog (Returnstate v k' s' m' inj'). *)
  (* Proof. *)
  (*   inversion Hstep; subst; *)
  (*     inversion Hwt_State; subst. *)
  (*   econstructor. *)
  (*   eapply prim_effect_wt_value; now eauto. *)
  (*   now eauto. *)
  (*   eapply pop_stack_wf_inject > [ eapply prim_effect_wf_inject; now eauto | now eauto ]. *)
  (* Qed. *)

  Lemma preservation {St Hp prog S1 t S2}
    (Hwt_state: @Semantics.wt_state St Hp prog S1)
    (Hstep: @Semantics.step St Hp (Globalenvs.Genv.globalenv prog) S1 t S2):
    Semantics.wt_state prog S2.
  Proof.
    inversion Hstep; subst;
      inversion Hwt_state; subst;
      try (inversion Hwt_fundef; subst; inversion Hwt_function; subst;
           econstructor; eapply preservation_Callstate_State; now eauto).
  Admitted.

End Preservation.

Section Progress.

  Context {St: Store}.
  Context {Hp: Imp.Heap.Heap}.

  Import ZArith.
  Local Open Scope Z_scope.

  Lemma step_progress {prog} S1 ge (Hwt_state: @wt_state St Hp prog S1):
    (exists t S2, Semantics.step ge S1 t S2) \/ (exists i, final_state S1 i).
  Proof.
  Abort.

End Progress.
