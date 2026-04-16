From Stdlib Require ZArith.

From GallinaC.Utils Require Import NatExt ListExt.

From GallinaC.Imp Require Heap Memval.
From GallinaC.Imp Require Import Store.

From GallinaC.Compiler.Common Require Import Types Value Expr.
From GallinaC.Compiler.Deep Require Import OpSem Prog Typing.

Section Determinism.

  Import Value.Facts.
  Import Expr.Facts.
  Import OpSem.Facts.

  Context {St: Store}.
  Context {Hp: Heap.Heap}.

  Lemma single_events (p: program): Smallstep.single_events (@semantics St Hp p).
  Proof using St Hp.
    unfold Smallstep.single_events; cbn;
      intros s t s' Hstep.
    inversion Hstep; subst; repeat constructor.
  Qed.

  Lemma receptive (p: program): Smallstep.receptive (@semantics St Hp p).
  Proof using St Hp.
    constructor.
    - intros s t1 s1 t2 Hstep1 Hmatch.
      inversion Hstep1; subst; inversion Hmatch; subst;
        eexists; now eauto.
    - apply single_events.
  Qed.

  Lemma strongly_receptive (p: program): Smallstep.strongly_receptive (@semantics St Hp p).
  Proof using St Hp.
    constructor.
    - intros s ev1 t1 s1 ev2 Hstep Hmatch_traces.
      inversion Hstep; subst.
    - intros s t s' Hstep.
      inversion Hstep; now cbn.
  Qed.

  Lemma builtin_deterministic {c genv env locals s v s' v0 s'0}
    (Hbuiltin : @builtin St Hp c genv env locals s v s')
    (Hbuiltin': @builtin St Hp c genv env locals s v0 s'0):
    v0 = v /\ s'0 = s'.
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
      reflexivity.
    - assert (v_size0 = v_size) by congruence; subst; clear EVAL_SIZE0.
      assert (v_init0 = v_init) by congruence; subst; clear EVAL_INIT0.
      assert (hp'0 = hp') by congruence; subst;
        assert (ptr0 = ptr) by congruence; subst;
        clear ALLOC0.
      now auto.
    - assert (v_ptr0 = v_ptr) by congruence; subst; clear EVAL0.
      assert (v0 = v_read) by (destruct v0, v_read; cbn in *; congruence); subst; clear LOOKUP0.
      now auto.
    - assert (v_ptr0 = v_ptr) by congruence; subst; clear EVAL_ptr0.
      assert (v_data0 = v_data) by congruence; subst; clear EVAL_data0.
      assert (hp'0 = hp') by congruence; subst; clear MUTATE0.
      now auto.
    - assert (v_ptr0 = v_ptr) by congruence; subst;
        clear EVAL0.
      assert (hp'0 = hp') by congruence; subst; clear FREE0.
      now auto.
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
          (try (destruct (builtin_deterministic BUILTIN BUILTIN0) as (eqv & eqs');
                subst));
          (try (specialize (resolve_seq_cont_fun RESOLVE RESOLVE0) as (eq1 & eq2 & eq3); subst));
          (try (replace b0 with b by congruence));
          (try (replace sp0 with sp by congruence));
          (try (congruence));
          (try (now inversion CALLK));
          (try (now inversion CALLK; subst; first [ inversion RESOLVE | inversion SEQK ])).
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
