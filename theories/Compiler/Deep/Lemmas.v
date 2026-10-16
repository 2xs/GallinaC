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

From Corelib Require Import ssreflect ssrfun ssrbool.
From Stdlib Require ZArith.

From HB Require Import structures.

From GallinaC.Utils Require Import NatExt ListExt.

From GallinaC.Imp Require Import Heap.
From GallinaC.Imp Require Import Addr Store Storable State.

From GallinaC.Compiler.Common Require Import Types Value Expr.
From GallinaC.Compiler.Deep Require Import OpSem Prog Typing.

Local Open Scope separation_scope.

Section Determinism.

  Import Value.Facts.
  Import Expr.Facts.
  Import OpSem.Facts.

  Context {Sm: State.type}.
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).

  Lemma pop_stack_n_O (s: Sm): pop_stack_n 0 s = Some s.
  Proof using Type. exact (state_pop_n_0 s). Qed.

  Lemma single_events (p: program): Smallstep.single_events (semantics (Sm := Sm) p).
  Proof using Type.
    unfold Smallstep.single_events; cbn;
      intros s t s' STEP.
    now inversion STEP; subst; auto; constructor.
  Qed.

  Lemma receptive (p: program): Smallstep.receptive (semantics (Sm := Sm) p).
  Proof using Type.
    constructor.
    - intros s t1 s1 t2 STEP1 MATCH.
      inversion STEP1; subst; inversion MATCH; subst;
        eexists; try now eauto.
    - apply single_events.
  Qed.

  Lemma strongly_receptive (p: program): Smallstep.strongly_receptive (semantics (Sm := Sm) p).
  Proof using Type.
    constructor.
    - intros s ev1 t1 s1 ev2 STEP MATCHTRACES.
      inversion STEP; subst.
    - intros s t s' STEP.
      inversion STEP; now cbn.
  Qed.

  Lemma builtin_deterministic {c genv env locals s v s' v0 s'0}
    (BUILTIN : @builtin Sm c genv env locals s v s')
    (BUILTIN': @builtin Sm c genv env locals s v0 s'0):
    v0 = v /\ s'0 = s'.
  Proof using Type.
    destruct BUILTIN; inversion BUILTIN'; subst.
    - repeat split; congruence.
    - repeat split; congruence.
    - split; [ reflexivity | ].
      assert (nm0 = nm) by congruence; subst; clear DEREF0.
      assert (v1 = v) by congruence; subst; clear EVAL0.
      assert (st'0 = st') by congruence; subst.
      apply state_ext; now autorewrite with seplog.
    - assert (v_size0 = v_size) by congruence; subst; clear EVAL_SIZE0.
      assert (v_init0 = v_init) by congruence; subst; clear EVAL_INIT0.
      assert (hp'0 = hp') by congruence; subst.
      assert (alc'0 = alc') by congruence; subst.
      assert (ptr0 = ptr) by congruence; subst.
      split; [ reflexivity | ].
      apply state_ext; now autorewrite with seplog.
    - assert (v_ptr0 = v_ptr) by congruence; subst; clear EVAL0.
      assert (v0 = v_read) by congruence; subst; clear LOOKUP0.
      now auto.
    - assert (v_ptr0 = v_ptr) by congruence; subst; clear EVAL_ptr0.
      assert (v_data0 = v_data) by congruence; subst; clear EVAL_data0.
      assert (hp'0 = hp') by congruence; subst.
      split; [ reflexivity | ].
      apply state_ext; now autorewrite with seplog.
    - assert (v_ptr0 = v_ptr) by congruence; subst; clear EVAL0.
      assert (hp'0 = hp') by congruence; subst.
      split; [ reflexivity | ].
      apply state_ext; now autorewrite with seplog.
    - assert (v_ptr0 = v_ptr) by congruence; subst.
      assert (v_shift0 = v_shift) by congruence; subst.
      assert (v_ptr'0 = v_ptr') by congruence; subst.
      now auto.
    - assert (v_ptr0 = v_ptr) by congruence; subst.
      assert (v_shift0 = v_shift) by congruence; subst.
      assert (v_ptr'0 = v_ptr') by congruence; subst.
      now auto.
    - assert (v_ptr_l0 = v_ptr_l) by congruence; subst; clear EVAL_l0.
      assert (v_ptr_r0 = v_ptr_r) by congruence; subst; clear EVAL_r0.
      assert (b0 = b) by congruence; subst.
      now auto.
    - repeat split; congruence.
    - repeat split; congruence.
  Qed.

  Lemma determinate (p: program) : Smallstep.determinate (semantics (Sm := Sm) p).
  Proof using Type.
    constructor; cbn.
    - intros s t1 s1 t2 s2 STEP1 STEP2.
      split; [ | intros EQ; subst ].
      + inversion STEP1; subst; inversion STEP2; subst; try (apply Events.match_traces_E0).
      + inversion STEP1; subst;
          inversion STEP2; subst;
          (try (now inversion BUILTIN));
          (try (destruct (builtin_deterministic BUILTIN BUILTIN0) as (eqv & eqs');
                subst));
          (try (specialize (resolve_seq_cont_fun RESOLVE RESOLVE0) as (eq1 & eq2 & eq3 & eq4); subst));
          (try (specialize (resolve_call_cont_fun CALLK CALLK0) as eq0; subst));
          (try (replace b0 with b by congruence));
          (try (replace sp0 with sp by congruence));
          (try (congruence));
          (try (now inversion CALLK; subst;
                match goal with H: is_call_cont _ |- _ => inversion H end));
          (try (now inversion CALLK; subst;
                match goal with H: is_call_cont _ |- _ => inversion H end;
                subst; first [ inversion RESOLVE | inversion SEQK ]));
          (try (now exfalso;
                first [ exact (resolve_call_cont_not_resolve_seq CALLK RESOLVE)
                      | exact (resolve_call_cont_not_resolve_seq CALLK0 RESOLVE0) ]));
          (try (now assert (v0 = v) by congruence; subst;
                assert (nm0 = nm) by congruence; subst;
                assert (st'0 = st') by congruence; subst;
                assert (sg'0 = sg') by congruence; subst;
                f_equal; apply state_ext; autorewrite with seplog; reflexivity)).
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
