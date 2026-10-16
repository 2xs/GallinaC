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

From Stdlib Require Import ZArith Lia.

From HB Require Import structures.

From GallinaC.Utils Require PTreeExt.
From GallinaC.Utils Require Import ListExt Counter PosExt ProdExt.

From GallinaC.Imp Require Import Addr Heap Store Storable State.

From GallinaC.Compiler.Common Require Import Types Value Expr CCInj.
From GallinaC.Compiler.IR Require Import Semantics Prog Typing.

Local Open Scope separation_scope.

Section Pure.

  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).

  (* TODO should be moved to Common/Expr.v once Common/Env.v is defined *)
  Lemma eval_progress [ctx e t f env]
    (WTexpr: Expr.wt_expr ctx e t) (WTenv: @wt_env Sm f ctx env)
    : exists v, Value.wt_value v t /\ eval e env = Some v.
  Proof using Type.
    induction WTexpr; simpl;
      try (now (eexists; split; first [ now constructor | reflexivity ])).
    - specialize (WTenv.(wv_ty_env) var_id t true GET); cbn;
        intros ([ v [GETval WTval]] & IN).
      exists v; split; [ assumption | now rewrite GETval ].
    - destruct IHWTexpr as [ v (WTval & EVAL) ].
      apply Facts.type_of_value_complete in WTval.
      destruct v; try discriminate.
      exists (v_bool (negb b0)); split; [ now repeat constructor | now rewrite EVAL ].
    - destruct IHWTexpr1 as [ v1 (WTval1 & EVAL1) ].
      destruct IHWTexpr2 as [ v2 (WTval2 & EVAL2) ].
      apply Facts.type_of_value_complete in WTval1, WTval2.
      destruct v1, v2; try discriminate.
      now eexists; split; [ | rewrite EVAL1, EVAL2; reflexivity ]; constructor.
    - destruct IHWTexpr1 as [ v1 (WTval1 & EVAL1) ].
      destruct IHWTexpr2 as [ v2 (WTval2 & EVAL2) ].
      apply Facts.type_of_value_complete in WTval1, WTval2.
      destruct v1, v2; try discriminate.
      now eexists; split; [ | rewrite EVAL1, EVAL2; reflexivity ]; constructor.
    - destruct IHWTexpr1 as [ v1 (WTval1 & EVAL1) ].
      destruct IHWTexpr2 as [ v2 (WTval2 & EVAL2) ].
      apply Facts.type_of_value_complete in WTval1, WTval2.
      destruct v1, v2; try discriminate.
      now eexists; split; [ | rewrite EVAL1, EVAL2; reflexivity ]; constructor.
  Qed.

  (* TODO should be moved to Common/Expr.v once Common/Env.v is defined *)
  Lemma eval_t_unit [ctx e f env]
    (WTexpr: Expr.wt_expr ctx e Types.t_unit) (WTenv: @wt_env Sm f ctx env)
    : eval e env = Some Value.v_tt.
  Proof using Type.
    remember Types.t_unit as t.
    induction WTexpr; try discriminate; subst; cbn; try reflexivity.
    specialize (WTenv.(wv_ty_env) var_id Types.t_unit true GET); cbn;
      intros ( [ v [GETval WTval] ] & IN ).
    inversion WTval; subst.
    now rewrite GETval.
  Qed.

  (* TODO should be moved to Common/Expr.v once Common/Env.v is defined *)
  Lemma eval_v_tt
    [ctx e t f env]
    (WTexpr: Expr.wt_expr ctx e t)
    (WTenv: @wt_env Sm f ctx env)
    (EVAL: eval e env = Some Value.v_tt)
    : t = Types.t_unit.
  Proof using Type.
    induction WTexpr;
      auto;
      (try (simpl in EVAL; congruence)).
    - cbn in EVAL.
      destruct (Maps.PTree.get var_id env) as [ v | ] eqn:Eget_val_env; [ inversion EVAL; subst; clear EVAL | discriminate ].
      specialize (WTenv.(wv_ty_env) var_id t true GET) as ( [ v [GETval WTval] ] & INtemps).
      assert (v = Value.v_tt) by congruence; subst.
      now inversion WTval.
    - simpl in EVAL.
      destruct (eval _ _); (try (destruct v)); discriminate.
    - simpl in EVAL.
      destruct (eval _ _); try discriminate;
        destruct v; try discriminate;
        destruct (eval _ _); try discriminate;
        destruct v; discriminate.
    - simpl in EVAL;
        destruct (eval _ _); try discriminate;
        destruct v; try discriminate;
        destruct (eval _ _); try discriminate;
        destruct v; discriminate.
    - simpl in EVAL;
        destruct (eval _ _); try discriminate;
        destruct v; try discriminate;
        destruct (eval _ _); try discriminate;
        destruct v; discriminate.
  Qed.

End Pure.

Section Stack.

  Context {Sm: State.type}.
  Local Notation Nm := (@var_name Sm).

  Lemma pop_stack_base [base] [locals: list Nm] [fe: f_extra] [s s': Sm]
    (LAYERED: layered base locals (store s))
    (LOCALSSZ: List.length locals = Z.to_nat fe.(fn_stackspace))
    (POP: pop_stack fe.(fn_stackspace) s = Some s')
    : store s' = base.
  Proof using Type.
    unfold pop_stack in POP.
    destruct (proj1 State.state_pop_n_some POP) as ( ITER & _ ).
    destruct (layered_pop_n (List.length locals) locals (store s) LAYERED
                (Nat.le_refl _)) as ( st2 & ITER2 & LAYERED2 & _ ).
    assert (EN: N.of_nat (List.length locals) = Z.to_N fe.(fn_stackspace)).
    { rewrite LOCALSSZ; exact (Z_nat_N _). }
    rewrite EN, ITER in ITER2.
    injection ITER2 as EST; subst st2.
    exact (layered_nil_inv LAYERED2 (ListExt.removelast_n_app_length [] locals)).
  Qed.

  Lemma pop_stack_heap [n] [s s'': Sm] (POP: pop_stack n s = Some s'')
    : heap s'' = heap s.
  Proof using Type.
    unfold pop_stack in POP.
    now destruct (proj1 State.state_pop_n_some POP) as ( _ & _ & EH & _ ).
  Qed.

  Lemma stack_slot_bound [A: Type] [fe: f_extra] [locals: list A] [n nm]
    (WTE: wt_f_extra fe)
    (LOCALSSZ: List.length locals = Z.to_nat fe.(fn_stackspace))
    (DEREF: List.nth_error locals n = Some nm)
    : (0 <= CCInj.offset_to_offset (Z.of_nat n) <= Integers.Ptrofs.max_unsigned)%Z.
  Proof using Type.
    specialize memword_bytes_pos as MSPOS.
    assert (NLT: (n < List.length locals)%nat)
      by (apply List.nth_error_Some; rewrite DEREF; discriminate).
    rewrite LOCALSSZ in NLT.
    unfold wt_f_extra in WTE.
    rewrite (Intops.Unsigned.CompCert.Ptrofs.max_unsigned_eq (UInt := Uintptr.n_ofst_t) eq_refl) in WTE.
    assert (SSPOS: (0 <= fn_stackspace fe)%Z) by lia.
    assert (NZ: (Z.of_nat n < fn_stackspace fe)%Z)
      by (rewrite <- (Z2Nat.id _ SSPOS); apply Nat2Z.inj_lt; exact NLT).
    specialize (Z.mul_div_le Integers.Ptrofs.max_unsigned (Z.of_nat memword_bytes)
                  ltac:(lia)) as MDL.
    unfold CCInj.offset_to_offset.
    split; [ lia | nia ].
  Qed.

  Lemma pop_stack_length [A: Type] stackspace (s: Sm) (l: list A)
    (LEN: List.length l = Z.to_nat stackspace)
    : pop_stack stackspace s = state_pop_n (N.of_nat (List.length l)) s.
  Proof using Type.
    unfold pop_stack.
    now rewrite LEN, Znat.Z_nat_N.
  Qed.

End Stack.

Section Typing.

  Lemma derive_wt_ret_tt [ctx c t]
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

  Lemma call_cont_eq_inversion [Sm: State.type] [A: Type] [k a'] {a a0: A} (CONTcall: @is_call_cont Sm k):
    match k with
    | Semantics.Kbind b_id c k => (a' b_id c k)
    | _ => a
    end = a0 ->
    a = a0.
  Proof.
    now inversion CONTcall.
  Qed.

  Lemma cont_eq_inversion [Sm: State.type] [A: Type] [k: @cont Sm] [a'] [a a0: A]:
    match k with
    | Semantics.Kbind b_id c k => a' b_id c k
    | _ => a
    end = a0 ->
    (a = a0 \/ exists b_id c k', k = Semantics.Kbind b_id c k' /\ a' b_id c k' = a0).
  Proof.
    intros EQ.
    destruct k as [ | b_id c k' | | | ] eqn:Ek; try (now left).
    right.
    exists b_id, c, k'.
    split; auto.
  Qed.

  Lemma is_call_contb_spec [Sm: State.type] (k: @cont Sm):
    Bool.reflect (is_call_cont k) (is_call_contb k).
  Proof.
    destruct k; constructor; first [ constructor | inversion 1 ].
  Qed.

  Lemma cont_call_or_seq [Sm: State.type] (k: @cont Sm):
    is_call_cont k \/ is_seq_cont k.
  Proof.
    destruct k; [ left | right | right | right | left ]; constructor.
  Qed.

  Lemma cont_call_seq_exclusive [Sm: State.type] [k: @cont Sm]
    (CALL: is_call_cont k) (SEQ: is_seq_cont k): False.
  Proof.
    destruct k; inversion CALL; inversion SEQ.
  Qed.

  Lemma seq_cont_target_fun [Sm: State.type] [k target1 target2]
    (SEQtarget1: @seq_cont_target Sm k target1)
    (SEQtarget2: @seq_cont_target Sm k target2)
    : target2 = target1.
  Proof.
    now inversion SEQtarget1; subst; inversion SEQtarget2; subst.
  Qed.

  Lemma resolve_seq_cont_fun [Sm: State.type] [k v c_next1 c_next2 k'1 k'2]
    (CONTseq1: @resolve_seq_cont Sm k v c_next1 k'1)
    (CONTseq2: @resolve_seq_cont Sm k v c_next2 k'2)
    : c_next2 = c_next1 /\ k'2 = k'1.
  Proof.
    inversion CONTseq1; subst; inversion CONTseq2; subst;
      split; reflexivity.
  Qed.

End Rewriting.

Section Determinism.

  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).
  Lemma single_events (p: program): Smallstep.single_events (semantics (Sm := Sm) p).
  Proof using Type.
    unfold Smallstep.single_events; cbn;
      intros s t s' STEP.
    inversion STEP; subst; repeat constructor.
  Qed.

  Lemma receptive (p: program): Smallstep.receptive (semantics (Sm := Sm) p).
  Proof using Type.
    constructor.
    - intros s t1 s1 t2 STEP1 MATCH.
      inversion STEP1; subst; inversion MATCH; subst;
        eexists; eassumption.
    - apply single_events.
  Qed.

  Lemma strongly_receptive (p: program): Smallstep.strongly_receptive (semantics (Sm := Sm) p).
  Proof using Type.
    constructor.
    - intros s ev1 t1 s1 ev2 STEP MATCHTRACES.
      inversion STEP; subst; inversion X.
    - intros s t s' STEP.
      inversion STEP; now cbn.
  Qed.

  Lemma builtin_deterministic {c genv env locals s v s' v0 s'0}
    (BUILTIN : @builtin Sm c genv env locals s v s')
    (BUILTIN': @builtin Sm c genv env locals s v0 s'0):
    v0 = v /\ s'0 = s'.
  Proof using Type.
    destruct BUILTIN; inversion BUILTIN'; subst.
    -
      split; congruence.
    -
      assert (nm0 = nm) by congruence; subst.
      split; [ | reflexivity ].
      apply encode_inj; congruence.
    -
      assert (nm0 = nm) by congruence; subst.
      assert (v1 = v) by congruence; subst.
      assert (st'0 = st') by congruence; subst.
      split; [ reflexivity | ].
      apply state_ext; now autorewrite with seplog.
    -
      assert (v_size0 = v_size) by congruence; subst.
      assert (v_init0 = v_init) by congruence; subst.
      assert (hp'0 = hp') by congruence; subst.
      assert (alc'0 = alc') by congruence; subst.
      assert (ptr0 = ptr) by congruence; subst.
      split; [ reflexivity | ].
      apply state_ext; now autorewrite with seplog.
    -
      assert (v_ptr0 = v_ptr) by congruence; subst.
      split; [ | reflexivity ].
      apply encode_inj; congruence.
    -
      assert (v_ptr0 = v_ptr) by congruence; subst.
      assert (v_data0 = v_data) by congruence; subst.
      assert (hp'0 = hp') by congruence; subst.
      split; [ reflexivity | ].
      apply state_ext; now autorewrite with seplog.
    -
      assert (ptr0 = ptr) by congruence; subst.
      assert (hp'0 = hp') by congruence; subst.
      split; [ reflexivity | ].
      apply state_ext; now autorewrite with seplog.
    -
      assert (v_ptr0 = v_ptr) by congruence; subst.
      assert (v_shift0 = v_shift) by congruence; subst.
      assert (v_ptr'0 = v_ptr') by congruence; subst.
      now auto.
    -
      assert (v_ptr0 = v_ptr) by congruence; subst.
      assert (v_shift0 = v_shift) by congruence; subst.
      assert (v_ptr'0 = v_ptr') by congruence; subst.
      now auto.
    -
      assert (v_ptr_l0 = v_ptr_l) by congruence; subst.
      assert (v_ptr_r0 = v_ptr_r) by congruence; subst.
      assert (b0 = b) by congruence; subst.
      now auto.
    -
      split; congruence.
    -
      split; congruence.
  Qed.

  Lemma determinate (p: program) : Smallstep.determinate (semantics (Sm := Sm) p).
  Proof using Type.
    constructor; cbn.
    - intros s t1 s1 t2 s2 STEP1 STEP2.
      split; [ | intros -> ].
      + inversion STEP1; subst; inversion STEP2; subst; try (apply Events.match_traces_E0).
      + inversion STEP1; subst;
          inversion STEP2; subst;
          (try (now inversion BUILTIN));
          (try (destruct (builtin_deterministic BUILTIN BUILTIN0) as (-> & ->)));
          (try (specialize (seq_cont_target_fun SEQtarget SEQtarget0) as ->; subst));
          (try (specialize (resolve_seq_cont_fun SEQresolve SEQresolve0) as (-> & ->); subst));
          (try (replace b0 with b by congruence));
          (try (congruence));
          (try (now inversion CONTcall));
          (try (now inversion CONTseq));
          (try (now inversion CONTcall; subst; first [ inversion CONTseq | inversion SEQtarget ])).
    - eapply Smallstep.sr_traces.
      apply receptive.
    - intros s1 s2 INITIAL1 INITIAL2.
      inversion INITIAL1; subst; inversion INITIAL2; subst.
      congruence.
    - intros s r FINAL t s' STEP.
      inversion FINAL; subst.
      inversion STEP; subst.
    - intros s r1 r2 FINAL1 FINAL2.
      inversion FINAL1; subst; inversion FINAL2; subst.
      reflexivity.
  Qed.

End Determinism.

Section WT.

  Lemma xtype_of_type_sized [t] (SIZED: Types.Sized t): exists xt, type_to_xtype t = xt.
    destruct SIZED; now eexists.
  Qed.

  Lemma alloc_global_wt [Sm: State.type] [id gv] (s: Sm) [nm]
      (CGET: cget (scnt s) = Some nm)
      (WT: wt_globvar id gv)
    : exists s', alloc_global s (AST.Gvar gv) = Some s'
                 /\ scnt s' = cnext (scnt s).
  Proof.
    destruct gv as [var_info init readonly volatile]; cbn.
    destruct WT as [WTinit WTro WTvol]; cbn in WTinit, WTro, WTvol; subst.
    destruct (Prog.Facts.value_of_init_data_complete (Pt := @ptr_t Sm) _ _ WTinit) as [mv MV].
    unfold alloc_global.
    destruct var_info as [var_type]; cbn in MV |- *.
    rewrite MV.
    destruct (push_of_cget s mv nm CGET) as [st [sg [n PUSH]]].
    rewrite PUSH.
    rewrite (mk_state_opt_of_dominates st sg (heap s) (alc s)
               (dominates_push (store s) st (scnt s) sg mv n PUSH
                  (state_store_dominates s))
               (state_heap_dominates s)).
    eexists; split; [ reflexivity | ].
    rewrite scnt_mk_state.
    exact (push_cnt (store s) (scnt s) mv st sg n PUSH).
  Qed.

  Lemma alloc_global_state [Sm: State.type] [s: Sm] [g s'] [k]
    (CNT: scnt s = Owned (mk_cnt k None))
    (ALLOC: alloc_global s g = Some s'):
    heap s' = heap s /\ alc s' = alc s
    /\ exists k', scnt s' = Owned (mk_cnt k' None).
  Proof.
    destruct g as [ fd | [ [ var_type ] init [ | ] [ | ] ] ];
      cbn [alloc_global] in ALLOC;
      try discriminate ALLOC;
      [ injection ALLOC as <-; repeat apply conj;
        [ reflexivity | reflexivity | exists k; exact CNT ] | ].
    destruct (value_of_init_data var_type init) as [ init_v | ];
      [ | discriminate ALLOC ].
    destruct (push (store s) (scnt s) init_v)
      as [ [ [ st sg ] nm ] | ] eqn:PUSH; [ | discriminate ALLOC ].
    destruct (proj1 (mk_state_opt_some _ _ _ _ _) ALLOC) as ( _ & ESG & EHP & EALC ).
    repeat apply conj; [ exact EHP | exact EALC | ].
    exists (S k).
    rewrite ESG, (push_cnt _ _ _ _ _ _ PUSH), CNT, cnext_owned, cnext_mk_cnt.
    reflexivity.
  Qed.

  Lemma alloc_global_slot [Sm: State.type] [s: Sm] [g s']
    (ALLOC: alloc_global s g = Some s')
    : State.store s' = State.store s
      \/ exists (a: @m_ad Sm) (v: value (@ptr_t Sm)) gv,
           g = AST.Gvar gv
           /\ value_of_init_data gv.(AST.gvar_info).(var_type) gv.(AST.gvar_init) = Some v
           /\ one a v $+ State.store s = Some (State.store s').
  Proof.
    destruct g as [ fd | [ [ var_type ] init [ | ] [ | ] ] ];
      cbn [alloc_global] in ALLOC;
      try discriminate ALLOC;
      [ injection ALLOC as <-; left; reflexivity | ].
    destruct (value_of_init_data var_type init) as [ init_v | ] eqn:EVAL;
      [ | discriminate ALLOC ].
    destruct (push (State.store s) (State.scnt s) init_v)
      as [ [ [ st sg ] nm ] | ] eqn:PUSH; [ | discriminate ALLOC ].
    destruct (proj1 (mk_state_opt_some _ _ _ _ _) ALLOC) as ( EST & _ & _ & _ ).
    destruct (proj2 (push_some (State.store s) (State.scnt s) init_v)
                (ex_intro _ st (ex_intro _ sg (ex_intro _ nm PUSH))))
      as ( c & CGET & _ ).
    destruct (push_mem _ _ _ _ _ _ _ PUSH CGET) as ( REF & ALW & SUM ).
    right.
    do 3 eexists.
    split; [ reflexivity | ].
    cbn.
    split; [ exact EVAL | ].
    rewrite EST; exact SUM.
  Qed.

  Lemma alloc_globals_slots [Sm: State.type]:
    forall (defs: list (AST.ident * globdef)) (s s': Sm)
           (SBINDS: ListExt.SBinds defs)
           (ALLOC: alloc_globals s defs = Some s'),
    exists slots: list (@m_ad Sm * (AST.ident * value (@ptr_t Sm))),
      (forall a v, one a v $<= State.store s' ->
                   one a v $<= State.store s \/ exists id, In (a, (id, v)) slots)
      /\ (forall a id v, In (a, (id, v)) slots ->
                         exists gv, In (id, AST.Gvar gv) defs
                                    /\ value_of_init_data gv.(AST.gvar_info).(var_type) gv.(AST.gvar_init) = Some v)
      /\ (forall a id v, In (a, (id, v)) slots -> forall w, ~ (one a w $<= State.store s))
      /\ List.NoDup (List.map fst slots)
      /\ List.NoDup (List.map (fun x => fst (snd x)) slots).
  Proof.
    induction defs as [ | [ id g ] rest IH ]; intros s s' SBINDS ALLOC;
      cbn [alloc_globals] in ALLOC.
    - injection ALLOC as <-.
      exists []; repeat apply conj;
        [ intros a v SUB; left; exact SUB
        | intros a id v [] ..
        | constructor
        | constructor ].
    - destruct (alloc_global s g) as [ s1 | ] eqn:EALLOC1; [ | discriminate ALLOC ].
      inversion SBINDS as [ | ?a ?b ?l ABS SBrest ]; subst.
      destruct (IH _ _ SBrest ALLOC) as
        ( slots & FWD & INDEFS & FRESH & NDA & NDI ).
      destruct (alloc_global_slot EALLOC1) as
        [ ESTORE | ( a1 & v1 & gv1 & EGV & EVAL & SUM ) ].
      + exists slots; repeat apply conj.
        * intros a v SUB.
          destruct (FWD a v SUB) as [ SUB1 | INSL ];
            [ left; rewrite <- ESTORE; exact SUB1 | right; exact INSL ].
        * intros a id' v IN.
          destruct (INDEFS a id' v IN) as ( gv & INgv & EVAL ).
          exists gv; split; [ right; exact INgv | exact EVAL ].
        * intros a id' v IN w SUB.
          exact (FRESH a id' v IN w (eq_ind_r (fun t => one a w $<= t) SUB ESTORE)).
        * exact NDA.
        * exact NDI.
      + subst g.
        assert (SUBs1: forall a w, one a w $<= State.store s -> one a w $<= State.store s1)
          by (intros a w SUB;
              exact (substate_tran _ _ _ SUB (substate_of_partition_r SUM))).
        exists ((a1, (id, v1)) :: slots); repeat apply conj.
        * intros a v SUB.
          destruct (FWD a v SUB) as [ SUB1 | ( id' & INSL ) ];
            [ | right; exists id'; right; exact INSL ].
          destruct (one_discriminate SUM a v SUB1) as [ ( -> & -> ) | ( _ & SUB0 ) ];
            [ right; exists id; left; reflexivity | left; exact SUB0 ].
        * intros a id' v [ EQ | IN ].
          -- injection EQ as <- <- <-.
             exists gv1; split; [ left; reflexivity | exact EVAL ].
          -- destruct (INDEFS a id' v IN) as ( gv & INgv & EVALgv ).
             exists gv; split; [ right; exact INgv | exact EVALgv ].
        * intros a id' v [ EQ | IN ] w SUB.
          -- injection EQ as <- <- <-.
             exact (one_sum_not_sub SUM w SUB).
          -- exact (FRESH a id' v IN w (SUBs1 a w SUB)).
        * cbn; constructor; [ | exact NDA ].
          intros INa1.
          destruct (proj1 (in_map_iff fst slots a1) INa1) as ( [ a' [ id' v' ] ] & EA & IN ).
          cbn in EA; subst a'.
          exact (FRESH a1 id' v' IN v1 (substate_of_partition_l SUM)).
        * cbn; constructor; [ | exact NDI ].
          intros INid.
          destruct (proj1 (in_map_iff (fun x => fst (snd x)) slots id) INid)
            as ( [ a' [ id' v' ] ] & EI & IN ).
          cbn in EI; subst id'.
          destruct (INDEFS a' id v' IN) as ( gv & INgv & _ ).
          exact (proj1 (ListExt.AbsBind_iff_not_In_fst id rest) ABS
                   (in_map fst rest (id, AST.Gvar gv) INgv)).
  Qed.

  Lemma alloc_globals_state [Sm: State.type] [s: Sm] [gl s'] [k]
    (CNT: scnt s = Owned (mk_cnt k None))
    (ALLOC: alloc_globals s gl = Some s'):
    heap s' = heap s /\ alc s' = alc s
    /\ exists k', scnt s' = Owned (mk_cnt k' None).
  Proof.
    revert s k CNT ALLOC.
    induction gl as [ | [ id g ] gl IH ]; intros s k CNT ALLOC;
      cbn [alloc_globals] in ALLOC;
      [ injection ALLOC as <-; repeat apply conj;
        [ reflexivity | reflexivity | exists k; exact CNT ] | ].
    destruct (alloc_global s g) as [ s0 | ] eqn:E;
      [ | discriminate ALLOC ].
    destruct (alloc_global_state CNT E) as ( EHP0 & EALC0 & k0 & CNT0 ).
    destruct (IH _ _ CNT0 ALLOC) as ( EHP & EALC & k' & CNT' ).
    repeat apply conj;
      [ rewrite EHP, EHP0; reflexivity
      | rewrite EALC, EALC0; reflexivity
      | exists k'; exact CNT' ].
  Qed.

  Lemma init_state_wt [Sm: State.type]: forall p
      (WT: wt_program p),
      exists s0, init_state (Sm := Sm) p = Some s0.
  Proof.
    intros p WT.
    unfold init_state.
    pose proof (wt_prog_defs WT) as FL.
    assert (SHAPE: exists k, scnt (emp_state (Sm := Sm)) = Owned (mk_cnt k None)).
    { exists 0; unfold emp_state; exact (scnt_emp_with_alc _ _). }
    generalize dependent (emp_state (Sm := Sm)).
    induction FL as [ acc | acc x rest WTg FL IH ]; intros s SHAPE.
    - cbn; eauto.
    - destruct x as [id g]; cbn in WTg |- *.
      destruct WTg as [ ctx' id' f WTf | ctx' id' v WTv ].
      + cbn; apply IH; exact SHAPE.
      + destruct SHAPE as [k SCNT].
        assert (CGET: cget (scnt s) = Some k).
        { rewrite SCNT, cget_owned; exact (cget_mk_cnt_none k). }
        destruct (alloc_global_wt s CGET WTv) as [s' [ALLOC CNT]].
        cbn [alloc_globals]; rewrite ALLOC.
        apply IH.
        exists (S k).
        now rewrite CNT, SCNT, cnext_owned, cnext_mk_cnt.
  Qed.

  Lemma wt_initial_state [Sm: State.type] [prog S]
    (INITIAL: @initial_state Sm prog S)
    : wt_state prog S.
  Proof.
    destruct INITIAL as [ ge b fd s0 WTp INITgenv INITstate FINDmainb FINDmainf MAINsig ];
      subst ge.
    eapply wt_Callstate with (sig := mk_signature [] t_nat).
    - exact WTp.
    - exact (Typing.wt_glob_fundef WTp
               (Ctxt.Facts.get_global_find_funct_ptr (ctx := mk_glob_ctxt prog)
                  FINDmainb FINDmainf)).
    - exact (type_call_args_correct fd (mk_signature [] t_nat) []
               (type_funsig_complete fd _ MAINsig) eq_refl).
    - eapply (wt_cont_other
                (Ctxt.with_internal (Maps.PTree.empty _) (Ctxt.with_pure (Maps.PTree.empty _)
                   (Ctxt.with_stack [] (mk_glob_ctxt prog))))), wt_Kstop.
    - exact MAINsig.
    - reflexivity.
  Qed.

  Lemma initial_wt_program [Sm: State.type] [prog: program] [S]
    (INIT: @initial_state Sm prog S)
    : wt_program prog.
  Proof.
    now destruct INIT as [ ge b fd s0 WTp GE INITstate FINDsymbol FINDfp FUNSIG ].
  Qed.

  Lemma initial_wt_p_extra [Sm: State.type] [prog: program] [S]
    (INIT: @initial_state Sm prog S)
    : wt_p_extra prog.
  Proof.
    destruct INIT as [ ge b fd s0 WTp GE INITstate FINDsymbol FINDfp FUNSIG ];
      subst.
    now destruct WTp as [ _ _ _ _ WTPX ].
  Qed.

  Lemma wt_function_sbinds_vars [ctx] [fn: function]
    (WTFN: wt_function ctx fn)
    : ListExt.SBinds ((fn.(fn_params) ++ fn.(fn_temps)) ++ fn.(fn_internals)).
  Proof.
    apply (proj2 (ListExt.SBinds_app _ _)); split; [ | split ].
    - apply (proj2 (ListExt.SBinds_app _ _)); split; [ | split ].
      + exact (Prog.wt_fn_params_sbinds WTFN).
      + exact (Prog.wt_fn_temps_sbinds WTFN).
      + exact (Prog.wt_fn_params_temps_distinct WTFN).
    - exact (Prog.wt_fn_internals_sbinds WTFN).
    - exact (Prog.wt_fn_locals_internals_distinct WTFN).
  Qed.

  Lemma seq_target_In [Sm: State.type] [fn] [k: @cont Sm] [e: @env Sm]
    [ctx t target_id]
    (WTCONT: wt_cont ctx k t)
    (WTENV: wt_env fn ctx.(Ctxt.ctxt_pure) e)
    (FINT: function_internals ctx fn)
    (ST: seq_cont_target k target_id)
    : In (target_id, t) ((fn.(fn_params) ++ fn.(fn_temps)) ++ fn.(fn_internals)).
  Proof.
    inversion ST; subst;
      inversion WTCONT; subst;
      try (now inversion WTKCALL);
      apply in_or_app.
    - left; exact (proj2 (wv_ty_env WTENV _ _ _ BINDABLE)).
    - right; exact (FINT _ _ _ GETcond).
    - right; exact (FINT _ _ _ GETbody).
  Qed.

  Lemma seq_target_sfind [Sm: State.type] [fn] [k: @cont Sm] [e: @env Sm]
    [ctx t target_id]
    (WTCONT: wt_cont ctx k t)
    (WTFN: wt_function (Ctxt.to_glob_ctxt ctx) fn)
    (WTENV: wt_env fn ctx.(Ctxt.ctxt_pure) e)
    (FINT: function_internals ctx fn)
    (ST: seq_cont_target k target_id)
    : ListExt.sfind target_id
        ((fn.(fn_params) ++ fn.(fn_temps)) ++ fn.(fn_internals)) = Some t.
  Proof.
    assert (SB: ListExt.SBinds ((fn.(fn_params) ++ fn.(fn_temps)) ++ fn.(fn_internals)))
      by exact (wt_function_sbinds_vars WTFN).
    exact (proj1 (ListExt.sbinds_sfind SB _ _)
             (ListExt.SBinds_In SB (seq_target_In WTCONT WTENV FINT ST))).
  Qed.

  Lemma wt_State_seq_target_In [Sm: State.type] [fn c k e locals] [s: Sm]
    [ctx t target_id]
    (WT: wt_State fn c k e locals s ctx t)
    (ST: seq_cont_target k target_id)
    : In (target_id, t) ((fn.(fn_params) ++ fn.(fn_temps)) ++ fn.(fn_internals)).
  Proof.
    destruct WT as [ WTFN WTCMD WTCONT WTENV FINT ].
    exact (seq_target_In WTCONT WTENV FINT ST).
  Qed.

  Lemma wt_State_seq_target_sfind [Sm: State.type] [fn c k e locals] [s: Sm]
    [ctx t target_id]
    (WT: wt_State fn c k e locals s ctx t)
    (ST: seq_cont_target k target_id)
    : ListExt.sfind target_id
        ((fn.(fn_params) ++ fn.(fn_temps)) ++ fn.(fn_internals)) = Some t.
  Proof.
    destruct WT as [ WTFN WTCMD WTCONT WTENV FINT ].
    exact (seq_target_sfind WTCONT WTFN WTENV FINT ST).
  Qed.

End WT.

Section Weakening.

  Lemma wt_expr_set_true (ctx: Ctxt.ctxt (type * bool) (type * bool) unit fundef vardef) id ty b e t
    (GET: Ctxt.get_pure id ctx = Some (ty, b))
    (WT: wt_expr (Ctxt.ctxt_pure ctx) e t):
    wt_expr (Ctxt.ctxt_pure (Ctxt.set_pure id (ty, true) ctx)) e t.
  Proof.
    refine (Expr.Facts.wt_expr_true_incl _ WT).
    exact (PTreeExt.pure_set_true_incl _ _ _ _ GET).
  Qed.

  Lemma get_pure_set_true (ctx: Ctxt.ctxt (type * bool) (type * bool) unit fundef vardef) id ty b id' ty' b'
    (GET: Ctxt.get_pure id ctx = Some (ty, b))
    (GET': Ctxt.get_pure id' ctx = Some (ty', b')):
    exists b'', Ctxt.get_pure id' (Ctxt.set_pure id (ty, true) ctx) = Some (ty', b'').
  Proof.
    unfold Ctxt.get_pure, Ctxt.set_pure, Ctxt.with_pure in *; cbn in *.
    destruct (Coqlib.peq id' id) as [ -> | NE ].
    - rewrite GET in GET'; injection GET' as <- <-.
      exists true; apply Maps.PTree.gss.
    - exists b'; rewrite Maps.PTree.gso by assumption; exact GET'.
  Qed.

  Lemma wt_cmd_set_pure_true [ctx: Ctxt.ctxt (type * bool) (type * bool) unit fundef vardef] [c t] (WT: wt_cmd ctx c t):
    forall id ty b, Ctxt.get_pure id ctx = Some (ty, b) ->
                    wt_cmd (Ctxt.set_pure id (ty, true) ctx) c t.
  Proof.
    induction WT; intros id ty b0 GET.
    - exact (wt_ret (wt_expr_set_true _ _ _ _ _ _ GET WTexpr)).
    - destruct (Coqlib.peq id_b id) as [ -> | NE ].
      + rewrite GET in BINDABLE; injection BINDABLE as <- <-.
        apply (wt_bind (t_b := ty) (b_b := true)).
        * apply Ctxt.Facts.get_set_pure.
        * exact (IHWT1 _ _ _ GET).
        * rewrite Ctxt.Facts.set_pure_same; exact WT2.
      + destruct (get_pure_set_true _ _ _ _ _ _ _ GET BINDABLE) as ( b'' & GETb ).
        apply (wt_bind (t_b := t_b) (b_b := b'')).
        * exact GETb.
        * exact (IHWT1 _ _ _ GET).
        * rewrite Ctxt.Facts.set_pure_comm by congruence.
          refine (IHWT2 _ _ _ _).
          unfold Ctxt.get_pure, Ctxt.set_pure, Ctxt.with_pure in *; cbn in *.
          rewrite Maps.PTree.gso by congruence; exact GET.
    - exact (wt_if (wt_expr_set_true _ _ _ _ _ _ GET WTcond)
               (IHWT1 _ _ _ GET) (IHWT2 _ _ _ GET)).
    - exact (wt_while (eq_trans (Ctxt.Facts.get_internal_set_pure (ty, true)) BOUNDcond)
               (eq_trans (Ctxt.Facts.get_internal_set_pure (ty, true)) BOUNDbody)
               (IHWT1 _ _ _ GET) (IHWT2 _ _ _ GET)).
    - apply wt_read_var.
    - exact (wt_write_var (wt_expr_set_true _ _ _ _ _ _ GET WTval)).
    - apply (wt_alloc_ptr (b_p := b_p) (b_c := b_c) (b_i := b_i));
        [ exact MALLOC
        | exact (eq_trans (Ctxt.Facts.get_internal_set_pure (ty, true)) INTptr)
        | exact (eq_trans (Ctxt.Facts.get_internal_set_pure (ty, true)) INTcount)
        | exact (eq_trans (Ctxt.Facts.get_internal_set_pure (ty, true)) INTinit)
        | exact NEptrcount
        | exact NEptrinit
        | exact NEcountinit
        | exact (wt_expr_set_true _ _ _ _ _ _ GET WTcount)
        | exact (wt_expr_set_true _ _ _ _ _ _ GET WTinit) ].
    - exact (wt_read_ptr (wt_expr_set_true _ _ _ _ _ _ GET WTptr)).
    - exact (wt_write_ptr (wt_expr_set_true _ _ _ _ _ _ GET WTptr)
               (wt_expr_set_true _ _ _ _ _ _ GET WTval)).
    - apply wt_free_ptr;
        [ exact FREE | exact (wt_expr_set_true _ _ _ _ _ _ GET WTptr) ].
    - exact (wt_shift_fw_ptr (wt_expr_set_true _ _ _ _ _ _ GET WTptr)
               (wt_expr_set_true _ _ _ _ _ _ GET WTofst)).
    - exact (wt_shift_bw_ptr (wt_expr_set_true _ _ _ _ _ _ GET WTptr)
               (wt_expr_set_true _ _ _ _ _ _ GET WTofst)).
    - exact (wt_ptr_eq (wt_expr_set_true _ _ _ _ _ _ GET WTptr_l)
               (wt_expr_set_true _ _ _ _ _ _ GET WTptr_r)).
    - apply (wt_app (fn := fn));
        [ exact FINDfn
        | exact EQargs
        | exact (Forall2_impl _ (fun e0 t0 => wt_expr_set_true _ _ _ _ e0 t0 GET) WTargs) ].
    - apply (wt_app_exf (nm := nm) (sg := sg));
        [ exact FINDfn
        | exact SIG
        | exact (Forall2_impl _ (fun e0 t0 => wt_expr_set_true _ _ _ _ e0 t0 GET) WTargs) ].
    - exact (wt_div (wt_expr_set_true _ _ _ _ _ _ GET WTl)
               (wt_expr_set_true _ _ _ _ _ _ GET WTr)).
    - exact (wt_mod (wt_expr_set_true _ _ _ _ _ _ GET WTl)
               (wt_expr_set_true _ _ _ _ _ _ GET WTr)).
  Qed.

  Lemma wt_cont_set_pure_true [Sm: State.type] [ctx: Ctxt.ctxt (type * bool) (type * bool) unit fundef vardef] [k: @cont Sm] [t]
    (WT: wt_cont ctx k t):
    forall id ty b, Ctxt.get_pure id ctx = Some (ty, b) ->
                    wt_cont (Ctxt.set_pure id (ty, true) ctx) k t.
  Proof.
    induction WT; intros id0 ty b0 GET.
    - destruct (Coqlib.peq id id0) as [ -> | NE ].
      + rewrite GET in BINDABLE; injection BINDABLE as <- <-.
        eapply wt_cont_Kbind.
        * apply Ctxt.Facts.get_set_pure.
        * rewrite Ctxt.Facts.set_pure_same; exact WTCMD.
        * exact (IHWT _ _ _ GET).
      + destruct (get_pure_set_true _ _ _ _ _ _ _ GET BINDABLE) as ( b'' & GETb ).
        eapply wt_cont_Kbind.
        * exact GETb.
        * rewrite Ctxt.Facts.set_pure_comm by assumption.
          refine (wt_cmd_set_pure_true WTCMD _ _ _ _).
          unfold Ctxt.get_pure, Ctxt.set_pure, Ctxt.with_pure in *; cbn in *.
          rewrite Maps.PTree.gso by (now apply not_eq_sym); exact GET.
        * exact (IHWT _ _ _ GET).
    - exact (wt_cont_Kloop1 _ _ _ _ _ _ _ _
               (wt_cmd_set_pure_true WTCOND _ _ _ GET)
               (wt_cmd_set_pure_true WTBODY _ _ _ GET)
               (IHWT _ _ _ GET)
               (eq_trans (Ctxt.Facts.get_internal_set_pure (ty, true)) GETcond)
               (eq_trans (Ctxt.Facts.get_internal_set_pure (ty, true)) GETbody)).
    - exact (wt_cont_Kloop2 _ _ _ _ _ _ _ _
               (wt_cmd_set_pure_true WTCOND _ _ _ GET)
               (wt_cmd_set_pure_true WTBODY _ _ _ GET)
               (IHWT _ _ _ GET)
               (eq_trans (Ctxt.Facts.get_internal_set_pure (ty, true)) GETcond)
               (eq_trans (Ctxt.Facts.get_internal_set_pure (ty, true)) GETbody)).
    - apply wt_cont_other; exact WTKCALL.
  Qed.

  Scheme wt_cont_incl_global_ind := Minimality for Semantics.wt_cont Sort Prop
    with wt_cont_call_incl_global_ind := Minimality for Semantics.wt_cont_call Sort Prop.

  Section ContMono.

    Context {Sm: State.type}.

    Local Definition wt_cont_incl_global_Pcont (ctx: Ctxt.ctxt (type * bool) (type * bool) unit fundef vardef) (k: @cont Sm) (t: type): Prop :=
      forall ctx': Ctxt.ctxt (type * bool) (type * bool) unit fundef vardef,
        Ctxt.ctxt_pure ctx = Ctxt.ctxt_pure ctx' ->
        Ctxt.ctxt_internal ctx = Ctxt.ctxt_internal ctx' ->
        (forall id g, Ctxt.get_global id ctx = Some g ->
                      Ctxt.get_global id ctx' = Some g) ->
        wt_cont ctx' k t.

    Local Definition wt_cont_incl_global_Pcall (ctx: Ctxt.ctxt Empty_set Empty_set Empty_set fundef vardef)
      (k: @cont Sm) (t: type): Prop :=
      forall ctx': Ctxt.ctxt Empty_set Empty_set Empty_set fundef vardef,
        (forall id g, Ctxt.get_global id ctx = Some g ->
                      Ctxt.get_global id ctx' = Some g) ->
        wt_cont_call ctx' k t.

    Lemma get_internal_eq [ctx ctx': Ctxt.ctxt (type * bool) (type * bool) unit fundef vardef]
      (EQinternal: Ctxt.ctxt_internal ctx = Ctxt.ctxt_internal ctx')
      : forall id, Ctxt.get_internal id ctx = Ctxt.get_internal id ctx'.
    Proof using Type.
      intro id; unfold Ctxt.get_internal; now rewrite EQinternal.
    Qed.

    Lemma wt_cont_incl_global [ctx ctx': Ctxt.ctxt (type * bool) (type * bool) unit fundef vardef] [k: @cont Sm] [t]
      (EQpure: Ctxt.ctxt_pure ctx = Ctxt.ctxt_pure ctx')
      (EQinternal: Ctxt.ctxt_internal ctx = Ctxt.ctxt_internal ctx')
      (GLOB: forall id g, Ctxt.get_global id ctx = Some g ->
                          Ctxt.get_global id ctx' = Some g)
      (WT: wt_cont ctx k t)
      : wt_cont ctx' k t.
    Proof using Type.
      revert ctx' EQpure EQinternal GLOB.
      refine (wt_cont_incl_global_ind Sm wt_cont_incl_global_Pcont wt_cont_incl_global_Pcall _ _ _ _ _ _ _ _ _ WT);
        unfold wt_cont_incl_global_Pcall, wt_cont_incl_global_Pcont; clear WT ctx k t.
      - intros ctx id c k t_b t_c b GET WTcmd _ IHcont ctx' EQp EQi GLOB.
        apply (wt_cont_Kbind ctx' id c k t_b t_c b).
        + unfold Ctxt.get_pure in GET |- *; rewrite <- EQp; exact GET.
        + refine (Typing.wt_cmd_incl_global _ _ _ WTcmd).
          * unfold Ctxt.set_pure; cbn; now rewrite EQp.
          * unfold Ctxt.set_pure; cbn; exact EQi.
          * intros id' g; unfold Ctxt.get_global, Ctxt.set_pure; cbn; exact (GLOB id' g).
        + exact (IHcont _ EQp EQi GLOB).
      - intros ctx c_cond id_cond c_body id_body k b_cond b_unit
          WTcond WTbody _ IHcont GETcond GETbody ctx' EQp EQi GLOB.
        apply (wt_cont_Kloop1 ctx' c_cond id_cond c_body id_body k b_cond b_unit).
        + exact (Typing.wt_cmd_incl_global EQp EQi GLOB WTcond).
        + exact (Typing.wt_cmd_incl_global EQp EQi GLOB WTbody).
        + exact (IHcont _ EQp EQi GLOB).
        + now rewrite <- (get_internal_eq EQi).
        + now rewrite <- (get_internal_eq EQi).
      - intros ctx c_cond id_cond c_body id_body k b_cond b_unit
          WTcond WTbody _ IHcont GETcond GETbody ctx' EQp EQi GLOB.
        apply (wt_cont_Kloop2 ctx' c_cond id_cond c_body id_body k b_cond b_unit).
        + exact (Typing.wt_cmd_incl_global EQp EQi GLOB WTcond).
        + exact (Typing.wt_cmd_incl_global EQp EQi GLOB WTbody).
        + exact (IHcont _ EQp EQi GLOB).
        + now rewrite <- (get_internal_eq EQi).
        + now rewrite <- (get_internal_eq EQi).
      - intros ctx k tret _ IHcall ctx' _ _ GLOB.
        apply wt_cont_other, IHcall.
        intros id g; unfold Ctxt.get_global, Ctxt.with_pure, Ctxt.with_stack; cbn.
        exact (GLOB id g).
      - intros ctx ctx' _; exact (wt_Kstop ctx').
      - intros ctx f env locals k t ty_env int_env WTfn WTenv FINT _ IHcont ctx' GLOB.
        apply (wt_Kcall ctx' f env locals k t ty_env int_env).
        + exact (Prog.Facts.wt_function_incl_global
                   (fun c c' P I S G => @Typing.wt_cmd_incl_global_stack c c' P I S G) _ _ _ GLOB WTfn).
        + exact WTenv.
        + exact FINT.
        + refine (IHcont (Ctxt.with_internal int_env
                            (Ctxt.with_pure ty_env
                               (Ctxt.with_stack (List.map (fun _ => tt) locals) ctx')))
                    eq_refl eq_refl _).
          intros id g; unfold Ctxt.get_global, Ctxt.with_pure, Ctxt.with_stack; cbn.
          exact (GLOB id g).
    Qed.

    Lemma wt_cont_call_incl_global [ctx ctx': Ctxt.ctxt Empty_set Empty_set Empty_set fundef vardef]
      [k: @cont Sm] [t]
      (GLOB: forall id g, Ctxt.get_global id ctx = Some g ->
                          Ctxt.get_global id ctx' = Some g)
      (WT: wt_cont_call ctx k t)
      : wt_cont_call ctx' k t.
    Proof using Type.
      inversion WT; subst.
      - exact (wt_Kstop ctx').
      - eapply wt_Kcall.
        + exact (Prog.Facts.wt_function_incl_global
                   (fun c c' P I S G => @Typing.wt_cmd_incl_global_stack c c' P I S G) _ _ _ GLOB WTFN).
        + exact WTENV.
        + exact FINT.
        + refine (wt_cont_incl_global
                    (ctx := Ctxt.with_internal int_env
                              (Ctxt.with_pure ty_env
                                 (Ctxt.with_stack (List.map (fun _ => tt) locals) ctx)))
                    (ctx' := Ctxt.with_internal int_env
                               (Ctxt.with_pure ty_env
                                  (Ctxt.with_stack (List.map (fun _ => tt) locals) ctx')))
                    eq_refl eq_refl _ WTk).
          intros id g; unfold Ctxt.get_global, Ctxt.with_pure, Ctxt.with_stack; cbn.
          exact (GLOB id g).
    Qed.

    Lemma wt_function_ctxt_eq_global [ctx ctx': Ctxt.ctxt Empty_set Empty_set Empty_set fundef vardef]
      (EGLOB: Ctxt.ctxt_global ctx = Ctxt.ctxt_global ctx')
      [f: function] (WT: wt_function ctx f)
      : wt_function ctx' f.
    Proof using Type.
      refine (Prog.Facts.wt_function_incl_global
                (fun c c' P I S G => @Typing.wt_cmd_incl_global_stack c c' P I S G) _ _ _ _ WT).
      intros id g; unfold Ctxt.get_global; now rewrite EGLOB.
    Qed.

    Lemma wt_cont_call_cont_eq_global [ctx ctx': Ctxt.ctxt (type * bool) (type * bool) unit fundef vardef] [k: @cont Sm] [t]
      (CALL: is_call_cont k)
      (EGLOB: Ctxt.ctxt_global ctx = Ctxt.ctxt_global ctx')
      (WT: wt_cont ctx k t)
      : wt_cont ctx' k t.
    Proof using Type.
      inversion WT; subst; try (now inversion CALL).
      apply (wt_cont_other ctx' k t).
      refine (wt_cont_call_incl_global _ WTKCALL).
      intros id g; unfold Ctxt.get_global, Ctxt.with_pure, Ctxt.with_stack; cbn.
      now rewrite EGLOB.
    Qed.

  End ContMono.

  Lemma wt_env_set_absent [Sm: State.type]
    [f: function] [ty_env] [e: @env Sm] [id] [v: Value.value (@ptr_t Sm)] [t]
    (WTe: wt_env f ty_env e)
    (ABS: Maps.PTree.get id ty_env = None)
    (WTv: Value.wt_value v t)
    : wt_env f ty_env (Maps.PTree.set id v e).
  Proof.
    constructor.
    - intros var_id t0 IN.
      destruct (Coqlib.peq var_id id) as [ -> | NE ].
      + exists t; rewrite Maps.PTree.gss; left; exact WTv.
      + destruct (WTe.(wt_val_env) var_id t0 IN) as ( t1 & H ).
        exists t1; rewrite Maps.PTree.gso by assumption; exact H.
    - intros var_id t0 b GET.
      assert (NE: var_id <> id) by (intros ->; rewrite ABS in GET; discriminate GET).
      destruct (WTe.(wv_ty_env) var_id t0 b GET) as ( H & IN ).
      split; [ | exact IN ].
      destruct b.
      + destruct H as ( w & GETw & WTw ); exists w;
          rewrite Maps.PTree.gso by assumption; now split.
      + rewrite Maps.PTree.gso by assumption; exact H.
  Qed.

  Lemma function_internals_not_local
    [ctx: Ctxt.ctxt (type * bool) (type * bool) unit fundef vardef] [f: function]
    (WTFN: wt_function (Ctxt.to_glob_ctxt ctx) f)
    (FINT: function_internals ctx f)
    [id ty b] (GI: Ctxt.get_internal id ctx = Some (ty, b))
    : forall t', ~ In (id, t') (f.(fn_params) ++ f.(fn_temps)).
  Proof.
    intros t' INl.
    refine (proj1 (ListExt.DBinds_iff_disjoint_fst _ _)
              (Prog.wt_fn_locals_internals_distinct WTFN) id _ _).
    - exact (in_map fst _ _ INl).
    - exact (in_map fst _ _ (FINT id ty b GI)).
  Qed.

  Lemma pure_get_none_of_internal [Sm: State.type]
    [ctx: Ctxt.ctxt (type * bool) (type * bool) unit fundef vardef] [f: function] [e: @env Sm]
    (WTFN: wt_function (Ctxt.to_glob_ctxt ctx) f)
    (WTe: wt_env f (Ctxt.ctxt_pure ctx) e)
    (FINT: function_internals ctx f)
    [id ty b] (GI: Ctxt.get_internal id ctx = Some (ty, b))
    : Maps.PTree.get id (Ctxt.ctxt_pure ctx) = None.
  Proof.
    destruct (Maps.PTree.get id (Ctxt.ctxt_pure ctx)) as [ [ t' b' ] | ] eqn:GP;
      [ exfalso | reflexivity ].
    exact (function_internals_not_local WTFN FINT GI t'
             (proj2 (WTe.(wv_ty_env) _ _ _ GP))).
  Qed.

  Lemma kinternal_next_state_wt [Sm: State.type]
    [f: function] [ctx: Ctxt.ctxt (type * bool) (type * bool) unit fundef vardef] [id: AST.ident] [t_b t_c: type] [b: bool]
    [c_next: Cmd.cmd] [k: @cont Sm] [e: @env Sm] [locals: list (@var_name Sm)]
    [s: Sm] [v: Value.value (@ptr_t Sm)]
    (WTf: wt_function (Ctxt.to_glob_ctxt ctx) f)
    (GETint: Ctxt.get_internal id ctx = Some (t_b, b))
    (WTnext: wt_cmd ctx c_next t_c)
    (WTk: wt_cont ctx k t_c)
    (WTv: Value.wt_value v t_b)
    (WTe: wt_env f (Ctxt.ctxt_pure ctx) e)
    (FINT: function_internals ctx f)
    : wt_State f c_next k (Maps.PTree.set id v e) locals s
        (Ctxt.set_internal id (t_b, b) ctx) t_c.
  Proof.
    rewrite (Ctxt.Facts.set_internal_same GETint).
    constructor; try assumption.
    exact (wt_env_set_absent WTe (pure_get_none_of_internal WTf WTe FINT GETint) WTv).
  Qed.

  Lemma kbind_next_state_wt [Sm: State.type]
    [f: function] [ctx: Ctxt.ctxt (type * bool) (type * bool) unit fundef vardef] [id: AST.ident] [t_b t_c: type] [b: bool]
    [c_next: Cmd.cmd] [k: @cont Sm] [e: @env Sm] [locals: list (@var_name Sm)]
    [s: Sm] [v: Value.value (@ptr_t Sm)]
    (WTf: wt_function (Ctxt.to_glob_ctxt ctx) f)
    (GETpure: Ctxt.get_pure id ctx = Some (t_b, b))
    (WTnext: wt_cmd (Ctxt.set_pure id (t_b, true) ctx) c_next t_c)
    (WTk: wt_cont ctx k t_c)
    (WTv: Value.wt_value v t_b)
    (WTe: wt_env f (Ctxt.ctxt_pure ctx) e)
    (FINT: function_internals ctx f)
    : wt_State f c_next k (Maps.PTree.set id v e) locals s (Ctxt.set_pure id (t_b, true) ctx) t_c.
  Proof.
    constructor; try assumption.
    { exact (wt_cont_set_pure_true WTk _ _ _ GETpure). }
    constructor.
    - intros var_id t IN.
      destruct (WTe.(wt_val_env) var_id t IN) as ( t' & H ).
      destruct (Coqlib.peq var_id id) as [ -> | NE ].
      + exists t_b; rewrite Maps.PTree.gss; left; exact WTv.
      + exists t'; rewrite Maps.PTree.gso by assumption.
        destruct (Maps.PTree.get var_id e) as [ w | ].
        * destruct H as [ H | H ]; [ now left | right ].
          unfold Ctxt.set_pure, Ctxt.with_pure; cbn;
            rewrite Maps.PTree.gso by assumption; exact H.
        * unfold Ctxt.set_pure, Ctxt.with_pure; cbn;
            rewrite Maps.PTree.gso by assumption; exact H.
    - intros var_id t b' GET.
      unfold Ctxt.set_pure, Ctxt.with_pure in GET; cbn in GET.
      destruct (Coqlib.peq var_id id) as [ -> | NE ].
      + rewrite Maps.PTree.gss in GET.
        destruct (WTe.(wv_ty_env) id t_b b GETpure) as ( _ & IN ).
        inversion GET; subst.
        split;
          [ exists v; rewrite Maps.PTree.gss; split; [ reflexivity | assumption ]
          | assumption ].
      + rewrite Maps.PTree.gso in GET by assumption.
        destruct (WTe.(wv_ty_env) var_id t b' GET) as ( H & IN ).
        split; [ | exact IN ].
        destruct b'.
        * destruct H as ( w & GETw & WTw ); exists w;
            rewrite Maps.PTree.gso by assumption; now split.
        * rewrite Maps.PTree.gso by assumption; exact H.
  Qed.

  Lemma bind_next_state_wt [Sm: State.type]
    [fn: function] [id_b t_b c_b c_c t_c] [k: @cont Sm]
    [env locals] [s: Sm] [ctx]
    (WT: wt_State fn (Cmd.c_bind id_b t_b c_b c_c t_c) k env locals s ctx t_c)
    : wt_State fn c_b (Kbind id_b c_c k) env locals s ctx t_b.
  Proof.
    destruct WT as [ WTFN WTCMD WTCONT WTENV FINT ].
    inversion WTCMD; subst.
    constructor; try assumption.
    eapply wt_cont_Kbind; eassumption.
  Qed.

  Lemma if_next_state_wt [Sm: State.type]
    [fn: function] [e_i c_t c_e t] [k: @cont Sm]
    [env locals] [s: Sm] [ctx] (b: bool)
    (WT: wt_State fn (Cmd.c_if e_i c_t c_e t) k env locals s ctx t)
    : wt_State fn (if b then c_t else c_e) k env locals s ctx t.
  Proof.
    destruct WT as [ WTFN WTCMD WTCONT WTENV FINT ].
    inversion WTCMD; subst.
    constructor; try assumption.
    now destruct b.
  Qed.

  Lemma while_next_state_wt [Sm: State.type]
    [fn: function] [c_cond id_cond c_body id_body] [k: @cont Sm]
    [env locals] [s: Sm] [ctx t]
    (WT: wt_State fn (Cmd.c_while c_cond id_cond c_body id_body) k env locals s ctx t)
    : wt_State fn c_cond (Kloop1 c_cond id_cond c_body id_body k) env locals s ctx t_bool.
  Proof.
    destruct WT as [ WTFN WTCMD WTCONT WTENV FINT ].
    inversion WTCMD; subst.
    constructor; try assumption.
    eapply wt_cont_Kloop1; eassumption.
  Qed.

  Lemma kloop1_next_state_wt [Sm: State.type]
    [fn: function] [ctx] [c_cond id_cond c_body id_body] [k: @cont Sm]
    [e: @env Sm] [locals: list (@var_name Sm)] [s: Sm] [bb: bool]
    (WTCONT: wt_cont ctx (Kloop1 c_cond id_cond c_body id_body k) t_bool)
    (WTFN: wt_function (Ctxt.to_glob_ctxt ctx) fn)
    (WTENV: wt_env fn ctx.(Ctxt.ctxt_pure) e)
    (FINT: function_internals ctx fn)
    : wt_State fn
        (if bb then c_body else Cmd.c_ret Expr.e_tt t_unit)
        (if bb then Kloop2 c_cond id_cond c_body id_body k else k)
        (Maps.PTree.set id_cond (Value.v_bool bb) e) locals s ctx t_unit.
  Proof.
    inversion WTCONT; subst; [ | now inversion WTKCALL ].
    rewrite <- (Ctxt.Facts.set_internal_same GETcond).
    destruct bb.
    - exact (kinternal_next_state_wt WTFN GETcond WTBODY
               (wt_cont_Kloop2 _ _ _ _ _ _ _ _
                  WTCOND WTBODY WTk GETcond GETbody)
               (Value.wt_v_bool true) WTENV FINT).
    - exact (kinternal_next_state_wt WTFN GETcond
               (wt_ret Expr.wt_tt) WTk (Value.wt_v_bool false) WTENV FINT).
  Qed.

  Lemma kloop2_next_state_wt [Sm: State.type]
    [fn: function] [ctx] [c_cond id_cond c_body id_body] [k: @cont Sm]
    [e: @env Sm] [locals: list (@var_name Sm)] [s: Sm]
    (WTCONT: wt_cont ctx (Kloop2 c_cond id_cond c_body id_body k) t_unit)
    (WTFN: wt_function (Ctxt.to_glob_ctxt ctx) fn)
    (WTENV: wt_env fn ctx.(Ctxt.ctxt_pure) e)
    (FINT: function_internals ctx fn)
    : wt_State fn c_cond (Kloop1 c_cond id_cond c_body id_body k)
        (Maps.PTree.set id_body Value.v_tt e) locals s ctx t_bool.
  Proof.
    inversion WTCONT; subst; [ | now inversion WTKCALL ].
    rewrite <- (Ctxt.Facts.set_internal_same GETbody).
    exact (kinternal_next_state_wt WTFN GETbody WTCOND
             (wt_cont_Kloop1 _ _ _ _ _ _ _ _
                WTCOND WTBODY WTk GETcond GETbody)
             Value.wt_v_tt WTENV FINT).
  Qed.

  Lemma seq_cont_next_state_wt [Sm: State.type]
    [fn: function] [ctx] [k: @cont Sm] [t] [v: Value.value (@ptr_t Sm)]
    [target_id c_next] [k': @cont Sm]
    [e: @env Sm] [locals: list (@var_name Sm)] (s': Sm)
    (WTCONT: wt_cont ctx k t)
    (WTFN: wt_function (Ctxt.to_glob_ctxt ctx) fn)
    (WTENV: wt_env fn ctx.(Ctxt.ctxt_pure) e)
    (FINT: function_internals ctx fn)
    (WTv: Value.wt_value v t)
    (ST: seq_cont_target k target_id)
    (RES: resolve_seq_cont k v c_next k')
    : exists ctx' t',
        wt_State fn c_next k' (Maps.PTree.set target_id v e) locals s' ctx' t'
        /\ Ctxt.ctxt_global ctx' = Ctxt.ctxt_global ctx.
  Proof.
    inversion RES; subst; inversion ST; subst.
    - inversion WTCONT as [ ?ctx0 ?id0 ?c0 ?k0 ?tb ?tc ?b0
                             BINDABLE WTCMD WTk | | |
                             ?ctx0 ?k0 ?tr WTKCALL ];
        subst; [ | now inversion WTKCALL ].
      exists (Ctxt.set_pure target_id (t, true) ctx); eexists; split;
        [ exact (kbind_next_state_wt WTFN BINDABLE WTCMD WTk WTv WTENV FINT)
        | reflexivity ].
    - inversion WTv; subst.
      exists ctx, t_unit; split;
        [ exact (kloop1_next_state_wt WTCONT WTFN WTENV FINT) | reflexivity ].
    - inversion WTv; subst.
      exists ctx, t_bool; split;
        [ exact (kloop2_next_state_wt WTCONT WTFN WTENV FINT) | reflexivity ].
  Qed.

End Weakening.

Section Preservation.

  Lemma eval_args_wt [Sm: State.type] [ctx] [f: function] [env: @env Sm] [es ts v_args]
    (WTes: List.Forall2 (Expr.wt_expr ctx) es ts)
    (WTenv: @wt_env Sm f ctx env)
    (EVAL: ListExt.map_opt (fun e => eval e env) es = Some v_args)
    : List.Forall2 (@Value.wt_value (@m_ad Sm) (@ptr_t Sm)) v_args ts.
  Proof.
    revert v_args EVAL.
    induction WTes as [ | e t es ts WTe WTes IH ]; intros v_args EVAL.
    - injection EVAL as <-; constructor.
    - cbn in EVAL.
      destruct (eval e env) as [ v | ] eqn:EV; [ | discriminate EVAL ].
      destruct (ListExt.map_opt (fun e' => eval e' env) es) as [ vs | ] eqn:EVs;
        [ | discriminate EVAL ].
      injection EVAL as <-.
      destruct (eval_progress WTe WTenv) as ( v' & WTv' & EV' ).
      rewrite EV in EV'; injection EV' as <-.
      exact (List.Forall2_cons _ _ WTv' (IH vs eq_refl)).
  Qed.

  Lemma wt_app_call [Sm: State.type] [f: function] [ctx] [env: @env Sm]
    [f_id t_out args t fd v_args]
    (WTcmd: Typing.wt_cmd ctx (Cmd.c_app f_id t_out args) t)
    (WTenv: @wt_env Sm f (Ctxt.ctxt_pure ctx) env)
    (FINDfd: Ctxt.get_global f_id ctx = Some (AST.Gfun fd))
    (EVALargs: ListExt.map_opt (fun e => eval e env) (List.map fst args) = Some v_args)
    : exists sig, funsig fd sig
                  /\ sig.(sig_res) = t
                  /\ wt_fundef_call v_args fd.
  Proof.
    inversion WTcmd as [ | | | | | | | | | | | | | ?ctx0 ?f_id0 ?args0 fn0 FINDfn EQargs WTargs
                       | ?ctx0 ?f_id0 ?args0 ?t_out0 ?nm ?sg FINDfn SIG WTargs
                       | | ]; subst.
    - rewrite FINDfd in FINDfn; injection FINDfn as ->.
      exists (fn_signature fn0); split; [ apply funsig_Internal | split; [ reflexivity | ] ].
      constructor.
      rewrite EQargs.
      exact (eval_args_wt WTargs WTenv EVALargs).
    - rewrite FINDfd in FINDfn; injection FINDfn as ->.
      exists {| sig_args := List.map snd args; sig_res := t |}.
      split; [ exact (funsig_External _ _ SIG) | split; [ reflexivity | ] ].
      exact (wt_call_external _ _ _ _ _ SIG (eval_args_wt WTargs WTenv EVALargs)).
  Qed.

  Lemma wt_Callstate_app [Sm: State.type] [prog: program]
    [fn: function] [fd] [f_id t_out args] [k: @cont Sm] [env locals] [s: Sm]
    [ctx t v_args]
    (WTp: Typing.wt_program prog)
    (EGLOB: Ctxt.ctxt_global ctx = Ctxt.ctxt_global (mk_glob_ctxt prog))
    (WTstate: @wt_State Sm fn (Cmd.c_app f_id t_out args) k env locals s ctx t)
    (FINDfd: Ctxt.get_global f_id ctx = Some (AST.Gfun fd))
    (EVALargs: ListExt.map_opt (fun e => eval e env) (List.map fst args) = Some v_args)
    : wt_state prog (Callstate fd v_args (Kcall fn env locals k) s).
  Proof.
    destruct WTstate as [ WTfn WTcmd WTcont WTenv FINT ].
    destruct (wt_app_call WTcmd WTenv FINDfd EVALargs) as ( sig & SIG & ERES & WTargs ).
    refine (wt_Callstate prog fd v_args _ s sig ctx WTp _ WTargs _ SIG EGLOB).
    - refine (Typing.wt_glob_fundef WTp (id := f_id) _).
      unfold Ctxt.get_global in FINDfd |- *; rewrite <- EGLOB; exact FINDfd.
    - rewrite ERES.
      apply (wt_cont_other ctx (Kcall fn env locals k) t).
      apply (wt_Kcall _ fn env locals k t
               (Ctxt.ctxt_pure ctx) (Ctxt.ctxt_internal ctx) WTfn WTenv FINT).
      refine (wt_cont_incl_global _ _ _ WTcont); [ reflexivity | reflexivity | ].
      intros id g; unfold Ctxt.get_global; cbn; exact (fun G => G).
  Qed.

  Lemma wt_Callstate_tailapp [Sm: State.type] [prog: program]
    [fn: function] [fd] [f_id t_out args] [k: @cont Sm] [env locals] [s s': Sm]
    [ctx t v_args]
    (WTp: Typing.wt_program prog)
    (EGLOB: Ctxt.ctxt_global ctx = Ctxt.ctxt_global (mk_glob_ctxt prog))
    (WTstate: @wt_State Sm fn (Cmd.c_app f_id t_out args) k env locals s ctx t)
    (FINDfd: Ctxt.get_global f_id ctx = Some (AST.Gfun fd))
    (EVALargs: ListExt.map_opt (fun e => eval e env) (List.map fst args) = Some v_args)
    : wt_state prog (Callstate fd v_args k s').
  Proof.
    destruct WTstate as [ WTfn WTcmd WTcont WTenv FINT ].
    destruct (wt_app_call WTcmd WTenv FINDfd EVALargs) as ( sig & SIG & ERES & WTargs ).
    refine (wt_Callstate prog fd v_args k s' sig ctx WTp _ WTargs _ SIG EGLOB).
    - refine (Typing.wt_glob_fundef WTp (id := f_id) _).
      unfold Ctxt.get_global in FINDfd |- *; rewrite <- EGLOB; exact FINDfd.
    - rewrite ERES; exact WTcont.
  Qed.


  Lemma set_params_in_some_wt [Sm: State.type]:
    forall [params: list (AST.ident * type)] [args: list (Value.value (@ptr_t Sm))]
           (SBINDS: ListExt.SBinds params)
           (WTargs: List.Forall2 (@Value.wt_value (@m_ad Sm) (@ptr_t Sm)) args
                      (List.map snd params))
           [id t] (IN: In (id, t) params),
      exists v, Maps.PTree.get id (set_params params args) = Some v
                /\ Value.wt_value v t.
  Proof.
    induction params as [ | [ id1 t1 ] params IH ]; cbn; intros args SBINDS WTargs id t IN.
    - contradiction.
    - inversion WTargs as [ | v ?y args' ?l' WTv WTrest ]; subst.
      destruct IN as [ EQ | IN ].
      + inversion EQ; subst id1 t1.
        exists v; split; [ apply Maps.PTree.gss | exact WTv ].
      + assert (NE: id <> id1)
          by (eapply ListExt.SBinds_tl_neq with (a := id1) (b := t1) (a' := id) (b' := t);
              [ exact SBINDS | exact IN ]).
        assert (SB': ListExt.SBinds params) by (now inversion SBINDS).
        destruct (IH _ SB' WTrest _ _ IN) as ( v' & GET & WT ).
        exists v'; split; [ | exact WT ].
        rewrite Maps.PTree.gso by exact NE; exact GET.
  Qed.

  Lemma set_params_nth [Sm: State.type] {A: Type} {params vals ident val}
    (LOOKUP: Maps.PTree.get ident (@set_params Sm A params vals) = Some val)
    : exists n ty, nth_error params n = Some (ident, ty) /\ nth_error vals n = Some val.
  Proof using Type.
    revert ident vals val LOOKUP.
    induction params as [ | [ params_hd_id params_hd_ty ] params_tl ];
      cbn; intros;
      destruct vals; (try (rewrite Maps.PTree.gempty in LOOKUP; discriminate)).
    rewrite Maps.PTree.gsspec in LOOKUP.
    destruct (Coqlib.peq ident params_hd_id) as [ | NE ]; subst.
    * inversion LOOKUP; subst; clear LOOKUP.
      exists 0%nat, params_hd_ty.
      split; reflexivity.
    * destruct (IHparams_tl ident vals val LOOKUP) as ( n & ty & NTH1 & NTH2 ) .
      exists (S n), ty.
      split; auto.
  Qed.

  Lemma set_params_get_not_in [Sm: State.type]:
    forall [params: list (AST.ident * type)] [args: list (Value.value (@ptr_t Sm))] [id]
           (NI: ~ In id (List.map fst params)),
      Maps.PTree.get id (set_params params args) = None.
  Proof.
    induction params as [ | [ id1 t1 ] params IH ]; intros args id NI.
    - destruct args; cbn; apply Maps.PTree.gempty.
    - destruct args as [ | v args' ]; cbn; [ apply Maps.PTree.gempty | ].
      rewrite Maps.PTree.gso by (intros EQ; subst; apply NI; now left).
      apply IH; intros IN; apply NI; now right.
  Qed.

  Lemma wt_env_init [Sm: State.type]
    [ctx: Ctxt.ctxt Empty_set Empty_set Empty_set fundef vardef]
    [f: function] [args: list (Value.value (@ptr_t Sm))] [internals]
    (WTfn: Typing.wt_function ctx f)
    (WTargs: List.Forall2 (@Value.wt_value (@m_ad Sm) (@ptr_t Sm)) args
               (List.map snd f.(fn_params)))
    : @wt_env Sm f
        (Ctxt.ctxt_pure (mk_function_ctxt f.(fn_params) f.(fn_temps) internals ctx))
        (set_params f.(fn_params) args).
  Proof.
    pose proof (wt_fn_params_sbinds WTfn) as SBp.
    pose proof (wt_fn_temps_sbinds WTfn) as SBt.
    pose proof (wt_fn_params_temps_distinct WTfn) as DIST.
    assert (TNP: forall id t, In (id, t) f.(fn_temps) ->
                              ~ In id (List.map fst f.(fn_params))).
    { intros id t INt INpf.
      apply List.in_map_iff in INpf as ( [ ip tp ] & EF & INp ); cbn in EF; subst ip.
      exact (ListExt.AbsBind_In_False (ListExt.DBinds_In_AbsBind DIST INp) INt). }
    constructor.
    - intros id t IN.
      exists t.
      destruct (List.in_dec (ReflectExt.sumbool_of_reflect (@Algebra.eqb_spec (AST.ident * type)%type)) (id, t) f.(fn_params)) as [ INp | NINp ].
      + destruct (set_params_in_some_wt SBp WTargs INp) as ( v & GET & WTv ).
        rewrite GET; left; exact WTv.
      + assert (INt: In (id, t) f.(fn_temps))
          by (apply List.in_app_or in IN as [ | ]; [ contradiction | assumption ]).
        rewrite (set_params_get_not_in (TNP _ _ INt)).
        exact (Prog.Facts.mk_function_ctxt_pure_get_temp _ _ _ _ SBp SBt DIST _ _ INt).
    - intros id t b GET.
      destruct b.
      + assert (INp: In (id, t) f.(fn_params)).
        { destruct (Prog.Facts.mk_function_ctxt_pure_get_inv _ _ _ _ SBp SBt _ _ _ GET)
            as [ ( _ & INp ) | ( EB & _ ) ]; [ exact INp | discriminate EB ]. }
        split; [ | apply List.in_or_app; now left ].
        destruct (set_params_in_some_wt SBp WTargs INp) as ( v & GETv & WTv ).
        exists v; split; [ exact GETv | exact WTv ].
      + assert (INt: In (id, t) f.(fn_temps)).
        { destruct (Prog.Facts.mk_function_ctxt_pure_get_inv _ _ _ _ SBp SBt _ _ _ GET)
            as [ ( EB & _ ) | ( _ & INt ) ]; [ discriminate EB | exact INt ]. }
        split; [ | apply List.in_or_app; now right ].
        exact (set_params_get_not_in (TNP _ _ INt)).
  Qed.

  Lemma wt_State_call_internal [Sm: State.type] [prog: program]
    [fn: function] [args: list (Value.value (@ptr_t Sm))] [k: @cont Sm]
    [locals: list (@var_name Sm)] [s: Sm] [sig] [ctx]
    (WTfundef: Typing.wt_fundef (mk_glob_ctxt prog) (AST.Internal fn))
    (WTcall: Typing.wt_fundef_call args (AST.Internal fn))
    (SIG: funsig (AST.Internal fn) sig)
    (WTcont: wt_cont ctx k sig.(sig_res))
    (EGLOB: Ctxt.ctxt_global ctx = Ctxt.ctxt_global (mk_glob_ctxt prog))
    (CONTcall: is_call_cont k)
    : @wt_State Sm fn fn.(fn_body) k (set_params fn.(fn_params) args) locals s
        (mk_function_ctxt fn.(fn_params) fn.(fn_temps) fn.(fn_internals) (mk_glob_ctxt prog))
        fn.(fn_return).
  Proof.
    inversion WTfundef as [ ?ctx0 ?fn0 WTfn | | ]; subst.
    assert (ESIG: sig = fn_signature fn) by (now inversion SIG).
    subst sig.
    assert (WTargs: List.Forall2 (@Value.wt_value (@m_ad Sm) (@ptr_t Sm)) args
                      (List.map snd fn.(fn_params)))
      by (now inversion WTcall).
    constructor.
    - refine (wt_function_ctxt_eq_global _ WTfn); reflexivity.
    - exact (wt_fn_cmd WTfn).
    - refine (wt_cont_call_cont_eq_global CONTcall _ WTcont); exact EGLOB.
    - exact (wt_env_init WTfn WTargs).
    - intros id ty b GI.
      destruct (Prog.Facts.mk_typing_tree_get_inv fn.(fn_internals) _ id ty b GI) as [ IN | GE ];
        [ exact IN | rewrite Maps.PTree.gempty in GE; discriminate GE ].
  Qed.

  Lemma builtin_wt_value [Sm: State.type] [f c k env locals s ctx t ge v s']
    (WTstate: wt_State f c k env locals s ctx t)
    (BUILTIN: @builtin Sm c ge env locals s v s')
    : Value.wt_value v t.
  Proof.
    inversion WTstate; subst.
    inversion State_wt_cmd; subst;
      inversion BUILTIN; subst;
      try (assumption);
      try (now constructor).
  Qed.

  Lemma preservation_State_State_builtin [Sm: State.type]
    [f c k e locals s ctx t ge v c' k' target_id] [s': Sm]
    (WT: @Semantics.wt_State Sm f c k e locals s ctx t)
    (STEP: @Semantics.step Sm ge (State f c k e locals s) Events.E0
             (State f c' k' (Maps.PTree.set target_id v e) locals s'))
    (BUILTIN: @builtin Sm c ge e locals s v s')
    (SEQtarget: seq_cont_target k target_id)
    (SEQresolve: resolve_seq_cont k v c' k')
    : exists ctx' t',
        Semantics.wt_State f c' k' (Maps.PTree.set target_id v e) locals s' ctx' t'
        /\ Ctxt.ctxt_global ctx' = Ctxt.ctxt_global ctx.
  Proof.
    pose proof (builtin_wt_value WT BUILTIN) as WTv.
    destruct WT as [ WTFN WTCMD WTCONT WTENV FINT ].
    exact (seq_cont_next_state_wt s' WTCONT WTFN WTENV FINT WTv SEQtarget SEQresolve).
  Qed.

  Lemma preservation_bind [Sm: State.type] [prog]
    [f: function] [id_b t_b c_b c_c t_c] [k: @cont Sm] [e: @env Sm]
    [locals: list (@var_name Sm)] [s: Sm]
    (WTstate: wt_state prog (State f (Cmd.c_bind id_b t_b c_b c_c t_c) k e locals s))
    : wt_state prog (State f c_b (Kbind id_b c_c k) e locals s).
  Proof.
    inversion WTstate as [ f0 c0 k0 e0 l0 s0 ctx0 t0 WTp WT EG | | ]; subst.
    pose proof WT as WTc; destruct WTc as [ _ WTCMD _ _ _ ].
    inversion WTCMD; subst.
    exact (wt_State_intro _ _ _ _ _ _ _ _ _ WTp (bind_next_state_wt WT) EG).
  Qed.

  Lemma preservation_ifthenelse [Sm: State.type] [prog]
    [f: function] [e_i c_t c_e t] [k: @cont Sm] [e: @env Sm]
    [locals: list (@var_name Sm)] [s: Sm] (b: bool)
    (WTstate: wt_state prog (State f (Cmd.c_if e_i c_t c_e t) k e locals s))
    : wt_state prog (State f (if b then c_t else c_e) k e locals s).
  Proof.
    inversion WTstate as [ f0 c0 k0 e0 l0 s0 ctx0 t0 WTp WT EG | | ]; subst.
    pose proof WT as WTc; destruct WTc as [ _ WTCMD _ _ _ ].
    inversion WTCMD; subst.
    exact (wt_State_intro _ _ _ _ _ _ _ _ _ WTp (if_next_state_wt b WT) EG).
  Qed.

  Lemma preservation_while [Sm: State.type] [prog]
    [f: function] [c_cond id_cond c_body id_body] [k: @cont Sm] [e: @env Sm]
    [locals: list (@var_name Sm)] [s: Sm]
    (WTstate: wt_state prog
                (State f (Cmd.c_while c_cond id_cond c_body id_body) k e locals s))
    : wt_state prog
        (State f c_cond (Kloop1 c_cond id_cond c_body id_body k) e locals s).
  Proof.
    inversion WTstate as [ f0 c0 k0 e0 l0 s0 ctx0 t0 WTp WT EG | | ]; subst.
    exact (wt_State_intro _ _ _ _ _ _ _ _ _ WTp (while_next_state_wt WT) EG).
  Qed.

  Lemma preservation_builtin_seq_cont [Sm: State.type] [prog]
    [f: function] [c k e locals s ge v c' k' target_id] [s': Sm]
    (WTstate: wt_state prog (State f c k e locals s))
    (STEP: @Semantics.step Sm ge (State f c k e locals s) Events.E0
             (State f c' k' (Maps.PTree.set target_id v e) locals s'))
    (BUILTIN: @builtin Sm c ge e locals s v s')
    (SEQtarget: seq_cont_target k target_id)
    (SEQresolve: resolve_seq_cont k v c' k')
    : wt_state prog (State f c' k' (Maps.PTree.set target_id v e) locals s').
  Proof.
    inversion WTstate as [ f0 c0 k0 e0 l0 s0 ctx0 t0 WTp WT EG | | ]; subst.
    destruct (preservation_State_State_builtin WT STEP BUILTIN SEQtarget SEQresolve)
      as ( ctx' & t' & WT' & EG' ).
    exact (wt_State_intro _ _ _ _ _ _ _ _ _ WTp WT' (eq_trans EG' EG)).
  Qed.

  Lemma preservation_internal_function [Sm: State.type] [prog]
    [fn: function] [args] [k: @cont Sm] [s: Sm]
    [locals: list (@var_name Sm)] [s': Sm]
    (WTstate: wt_state prog (Callstate (AST.Internal fn) args k s))
    (CONTcall: is_call_cont k)
    : wt_state prog
        (State fn fn.(fn_body) k (set_params fn.(fn_params) args) locals s').
  Proof.
    inversion WTstate as [ | f0 args0 k0 s0 sig0 ctx0 WTp WTfd WTcall WTcont SIG EGLOB | ];
      subst.
    refine (wt_State_intro _ _ _ _ _ _ _ _ _ WTp
              (wt_State_call_internal WTfd WTcall SIG WTcont EGLOB CONTcall) _).
    reflexivity.
  Qed.

  Lemma preservation_return_call_seq [Sm: State.type] [prog]
    [v: Value.value (@ptr_t Sm)] [fn: function] [env: @env Sm]
    [locals: list (@var_name Sm)] [k: @cont Sm] [s: Sm]
    [c_next] [k': @cont Sm] [target_id]
    (WTstate: wt_state prog (Returnstate v (Kcall fn env locals k) s))
    (SEQtarget: seq_cont_target k target_id)
    (SEQresolve: resolve_seq_cont k v c_next k')
    : wt_state prog (State fn c_next k' (Maps.PTree.set target_id v env) locals s).
  Proof.
    inversion WTstate as [ | | v0 k0 s0 t0 ctx0 WTp WTres WTcont EGLOB ]; subst.
    inversion WTcont as [ | | | ctx1 k1 tr1 WTCC ]; subst.
    inversion WTCC as [ | ctx2 f2 env2 loc2 k2 t2 ty_env int_env
                         WTFN WTENV FINT WTk ]; subst.
    assert (WTFN': wt_function
                       (Ctxt.with_internal (Maps.PTree.empty _) (Ctxt.with_pure (Maps.PTree.empty _)
                          (Ctxt.with_stack []
                             (Ctxt.with_internal int_env
                                (Ctxt.with_pure ty_env
                                   (Ctxt.with_stack (List.map (fun _ => tt) locals)
                                      (Ctxt.with_pure (Maps.PTree.empty Empty_set)
                                         (Ctxt.with_stack (@nil Empty_set) ctx0))))))))
                       fn)
      by (refine (wt_function_ctxt_eq_global _ WTFN); reflexivity).
    destruct (seq_cont_next_state_wt (locals := locals) s WTk WTFN' WTENV
                FINT WTres SEQtarget SEQresolve)
      as ( ctx' & t' & WT & EG' ).
    exact (wt_State_intro _ _ _ _ _ _ _ _ _ WTp WT (eq_trans EG' EGLOB)).
  Qed.

  Lemma preservation [Sm: State.type] [prog S1 t S2]
    (WTstate: @Semantics.wt_state Sm prog S1)
    (STEP: @Semantics.step Sm (Globalenvs.Genv.globalenv prog) S1 t S2):
    Semantics.wt_state prog S2.
  Proof.
    inversion STEP; subst.
    - exact (preservation_bind WTstate).
    - inversion WTstate as [ f0 c0 k0 e0 l0 s0 ctx0 t0 WTp WT EG | | ]; subst.
      pose proof (builtin_wt_value WT BUILTIN) as WTv.
      pose proof WT as W; destruct W as [ _ _ WTCONT _ _ ].
      exact (wt_Returnstate prog _ _ _ _ ctx0 WTp WTv WTCONT EG).
    - exact (preservation_builtin_seq_cont WTstate STEP BUILTIN SEQtarget SEQresolve).
    - inversion WTstate as [ f0 c0 k0 e0 l0 s0 ctx0 t0 WTp WT EG | | ]; subst.
      assert (FSY: Globalenvs.Genv.find_symbol (Ctxt.ctxt_global ctx0) id = Some b)
        by (rewrite EG; exact FINDsymb).
      assert (FFP: Globalenvs.Genv.find_funct_ptr (Ctxt.ctxt_global ctx0) b = Some fd)
        by (rewrite EG; exact FINDfunct).
      exact (wt_Callstate_app WTp EG WT
               (Ctxt.Facts.get_global_find_funct_ptr FSY FFP) EVALargs).
    - inversion WTstate as [ f0 c0 k0 e0 l0 s0 ctx0 t0 WTp WT EG | | ]; subst.
      assert (FSY: Globalenvs.Genv.find_symbol (Ctxt.ctxt_global ctx0) f_id = Some b)
        by (rewrite EG; exact FINDsymb).
      assert (FFP: Globalenvs.Genv.find_funct_ptr (Ctxt.ctxt_global ctx0) b = Some fd)
        by (rewrite EG; exact FINDfunct).
      exact (wt_Callstate_tailapp WTp EG WT
               (Ctxt.Facts.get_global_find_funct_ptr FSY FFP) EVALargs).
    - exact (preservation_ifthenelse b WTstate).
    - exact (preservation_while WTstate).
    - exact (preservation_internal_function WTstate CONTcall).
    - exact (preservation_return_call_seq WTstate SEQtarget SEQresolve).
  Qed.

End Preservation.
