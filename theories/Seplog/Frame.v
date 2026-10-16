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
From HB Require Import structures.

From Stdlib Require Import Arith NArith Lia.

From GallinaC.Utils Require Import ListExt.
From GallinaC.Imp Require Import Storable Store PrimitivesProp.
From GallinaC.Seplog Require Import Hoare.
From GallinaC.Seplog.Indep Require Import Indep.

Import (coercions) Intops.IntCarrier Intops.Unsigned.

Local Open Scope separation_scope.
Local Open Scope mem_scope.
Local Open Scope program_scope.

HB.mixin Record isFraming (S: Type) (conn: Pred S -> Pred S -> Pred S) :=
  {
    #[canonical=no] frame_side: forall (A: Type), Pred S -> (A -> Pred S) -> Pred S -> (A -> Pred S) -> program S A -> Prop;
    frame_law: forall (total: bool) (A: Type) (P: Pred S) (Q: A -> Pred S) (R: Pred S) (R': A -> Pred S) (c: program S A),
      frame_side A P Q R R' c -> hoare total P c Q -> hoare total (conn P R) c (fun v => conn (Q v) (R' v));
  }.
HB.structure Definition Framing (S: Type) := { conn of isFraming S conn }.

Lemma frame_rule_gen [S: Type] [F: Framing.type S] [total: bool] [A: Type]
  [P: Pred S] [Q: A -> Pred S] [R: Pred S] [R': A -> Pred S] [c: program S A]
  (SIDE: frame_side (s:=F) A P Q R R' c) (TRIPLE: hoare total P c Q)
  : hoare total (F P R) c (fun v => F (Q v) (R' v)).
Proof.
  exact: frame_law SIDE TRIPLE.
Qed.

Lemma frame_rule [S: Type] [F: Framing.type S] [total: bool] [A: Type]
  [P: Pred S] [Q: A -> Pred S] [R: Pred S] [c: program S A]
  (SIDE: frame_side (s:=F) A P Q R (fun _ => R) c) (TRIPLE: hoare total P c Q)
  : hoare total (F P R) c (fun v => F (Q v) R).
Proof.
  exact: frame_rule_gen SIDE TRIPLE.
Qed.

Section MemoryHelpers.

  (* Shared shape of the three framing lemmas below: an operation turns [m1] into
     [m1'] while only touching addresses that the frame [f] does not hold, and
     [m2'] holds exactly the singletons of [m1'] and of [f]. *)
  #[local] Lemma frame_sum [Ad Vl] [Mm: Memory.type Ad Vl] (m1 f m2 m1' m2': Mm)
    (EQm2: m1 $+ f = Some m2)
    (SPLIT: forall a v, (a |-> v) $<= m1' ->
                        (a |-> v) $<= m1 \/ (forall w, ~ ((a |-> w) $<= f)))
    (CHAR: forall a v, (a |-> v) $<= m2' <-> ((a |-> v) $<= m1' \/ (a |-> v) $<= f))
    : m1' $+ f = Some m2'.
  Proof.
    have SEPf: m1 $/= f by exists m2.
    apply: sum_eq_char _ _ _ _ CHAR.
    apply: mem_sep => a1 a2 v1 v2 SUB1 SUB2.
    case: (SPLIT a1 v1 SUB1) => [SUBm1|ABS].
    - exact: (proj2 (mem_sep_iff m1 f) SEPf a1 a2 v1 v2 SUBm1 SUB2).
    - by apply/one_ne_addr => EQa1; apply: (ABS v2); rewrite EQa1.
  Qed.

  #[local] Lemma mutate_frame [Ad Vl] [Nm: Ref.type Ad] [RW: RWMemory.type Ad Nm Vl]
    (m1 f m2 m1': RW) (r: Nm) (v: Vl)
    (EQm2: m1 $+ f = Some m2)
    (MUT: mutate m1 r v = Some m1')
    : exists m2', mutate m2 r v = Some m2' /\ m1' $+ f = Some m2'.
  Proof.
    have SEPf: m1 $/= f by exists m2.
    case: (proj2 (mutate_some_iff m1 r v) (ex_intro _ m1' MUT))
      => a [v0 [REF [ALW SUB0] ] ].
    have SUB0': (a |-> v0) $<= m2
      := substate_tran _ _ _ SUB0 (substate_of_partition_l EQm2).
    case: (proj1 (mutate_some_iff m2 r v)
             (ex_intro _ a (ex_intro _ v0 (conj REF (conj ALW SUB0')))))
      => m2' MUT2.
    have ANF := absent_of_separate m1 f a v0 SEPf SUB0.
    have M1 := mutate_mem_iff m1 r v m1' a REF MUT.
    have M2 := mutate_mem_iff m2 r v m2' a REF MUT2.
    have SPL := sub_sum_split_iff m1 f m2 EQm2.
    exists m2'; split; [exact: MUT2 | ].
    apply: (frame_sum m1 f m2 m1' m2' EQm2).
    - move=> b w /(M1 b w) [ [-> _]|[_ SUBm1] ]; [by right | by left].
    - move=> b w; split.
      + move/(M2 b w) => [ [-> ->]|[NE /(SPL b w) [SUBm1|SUBf] ] ].
        * by left; apply/(M1 a v); left.
        * by left; apply/(M1 b w); right.
        * by right.
      + case=> [/(M1 b w) [ [-> ->]|[NE SUBm1] ]|SUBf].
        * by apply/(M2 a v); left.
        * by apply/(M2 b w); right; split; [ | apply/(SPL b w); left].
        * apply/(M2 b w); right; split; last by apply/(SPL b w); right.
          by move=> EQa; apply: (ANF w); rewrite -EQa.
  Qed.

  #[local] Lemma alloc_frame [Ad: Addr.type] [Pt: Ptr.type Ad] [Vl: Type] [Hp: Heap.type Ad Pt Vl]
    (h1 f h2 h1': Hp) (c c1': excl (@heap_alc Ad Pt Vl Hp)) (sz: N.t) (v: Vl) (p: Pt)
    (EQh2: h1 $+ f = Some h2)
    (DOM: dominates h2 c)
    (AL: alloc h1 c sz v = Some (h1', c1', p))
    : exists h2', alloc h2 c sz v = Some (h2', c1', p) /\ h1' $+ f = Some h2'.
  Proof.
    case: (proj2 (alloc_some h1 c sz v)
             (ex_intro _ h1' (ex_intro _ c1' (ex_intro _ p AL))))
      => bid [GET [SZ _] ].
    have FRESH2: forall o w, ~ ((((mkAddr bid o): Ad) |-> w) $<= h2).
    { move=> o w SUB.
      by have := DOM (mkAddr bid o) w bid SUB GET; rewrite mkAddr_block; lia. }
    case: (proj1 (alloc_some h2 c sz v)
             (ex_intro _ bid (conj GET (conj SZ FRESH2))))
      => h2' [c2' [p2 AL2] ].
    have EQp2: p2 = p := alloc_det h2 h1 c sz v v h2' h1' c2' c1' p2 p AL2 AL.
    move: EQp2 AL2 => -> AL2.
    have EQc2': c2' = c1'.
    { rewrite (alloc_alc h2 c sz v h2' c2' p AL2).
      by symmetry; exact: (alloc_alc h1 c sz v h1' c1' p AL). }
    move: EQc2' AL2 => -> AL2.
    have R0: Reaches p ((mkAddr bid 0%N): Ad)
      by apply/(alloc_reaches h1 c sz v h1' c1' p bid AL GET 0%N); exact: N.le_0_l.
    have NOTF: forall (a: Ad) w, Reaches p a -> ~ ((a |-> w) $<= f).
    { move=> a w RA SUBf.
      have SUBh2: (a |-> w) $<= h2
        := substate_tran _ _ _ SUBf (substate_of_partition_r EQh2).
      have := DOM a w bid SUBh2 GET.
      by rewrite (reaches_block p a (mkAddr bid 0%N) RA R0) mkAddr_block; lia. }
    have A1 := alloc_mem h1 c sz v h1' c1' p AL.
    have A2 := alloc_mem h2 c sz v h2' c1' p AL2.
    have SPL := sub_sum_split_iff h1 f h2 EQh2.
    exists h2'; split; [exact: AL2 | ].
    apply: (frame_sum h1 f h2 h1' h2' EQh2).
    - move=> a w /(A1 a w) [ [R1 _]|[_ SUBh1] ]; last by left.
      by right => x; exact: (NOTF a x R1).
    - move=> a w.
      case REACH: ((reaches p a && reaches p (shift_fw a 1%N))%bool); last first.
      { have NSTR: ~ (Reaches p a /\ Reaches p (shift_fw a 1%N))
          by move=> [R1 R2]; move: REACH; rewrite R1 R2.
        split.
        - move/(A2 a w) => [ [R1 [R2 _] ]|[_ SUBh2] ]; first by case: (NSTR (conj R1 R2)).
          case: (proj1 (SPL a w) SUBh2) => [SUBh1|SUBf]; last by right.
          by left; apply/(A1 a w); right.
        - case=> [/(A1 a w) [ [R1 [R2 _] ]|[_ SUBh1] ]|SUBf].
          + by case: (NSTR (conj R1 R2)).
          + by apply/(A2 a w); right; split; [ | apply/(SPL a w); left].
          + by apply/(A2 a w); right; split; [ | apply/(SPL a w); right]. }
      move: REACH => /andP [R1 R2].
      split.
      + move/(A2 a w) => [ [_ [_ ->] ]|[NR _] ]; last by case: (NR (conj R1 R2)).
        by left; apply/(A1 a v); left.
      + case=> [/(A1 a w) [ [_ [_ ->] ]|[NR _] ]|SUBf].
        * by apply/(A2 a v); left.
        * by case: (NR (conj R1 R2)).
        * by case: (NOTF a w R1 SUBf).
  Qed.

  #[local] Lemma free_frame [Ad: Addr.type] [Pt: Ptr.type Ad] [Vl: Type] [Hp: Heap.type Ad Pt Vl]
    (h1 f h2 h1': Hp) (p: Pt)
    (EQh2: h1 $+ f = Some h2)
    (FR: free h1 p = Some h1')
    : exists h2', free h2 p = Some h2' /\ h1' $+ f = Some h2'.
  Proof.
    have SEPf: h1 $/= f by exists h2.
    case: (proj2 (free_some h1 p) (ex_intro _ h1' FR)) => ALW OWN.
    have OWN2: forall a, Reaches p a -> Reaches p (shift_fw a 1%N) ->
                         exists w, (a |-> w) $<= h2.
    { move=> a R1 R2; case: (OWN a R1 R2) => w SUB.
      by exists w; exact: (substate_tran _ _ _ SUB (substate_of_partition_l EQh2)). }
    case: (proj1 (free_some h2 p) (conj ALW OWN2)) => h2' FR2.
    have F1 := free_mem h1 p h1' FR.
    have F2 := free_mem h2 p h2' FR2.
    have SPL := sub_sum_split_iff h1 f h2 EQh2.
    exists h2'; split; [exact: FR2 | ].
    apply: (frame_sum h1 f h2 h1' h2' EQh2).
    - move=> a w SUB; left.
      case: (F1 a) => [ [_ NB]|[_ IFF] ]; last exact: (proj2 (IFF w) SUB).
      by exfalso; apply: NB; exists w.
    - move=> a w.
      case: (F1 a) => [ [STR1 NB1]|[NSTR1 IFF1] ]; case: (F2 a) => [ [STR2 NB2]|[NSTR2 IFF2] ].
      + split.
        * by move=> SUB; exfalso; apply: NB2; exists w.
        * case=> [SUB|SUBf]; first by exfalso; apply: NB1; exists w.
          case: (OWN a (proj1 STR1) (proj2 STR1)) => u SUBu.
          by case: (absent_of_separate h1 f a u SEPf SUBu w SUBf).
      + by case: (NSTR2 STR1).
      + by case: (NSTR1 STR2).
      + split.
        * move=> SUB.
          case: (proj1 (SPL a w) (proj2 (IFF2 w) SUB)) => [SUBh1|SUBf]; last by right.
          by left; exact: (proj1 (IFF1 w) SUBh1).
        * case=> [SUB|SUBf]; apply/(IFF2 w); apply/(SPL a w);
            [ left; exact: (proj2 (IFF1 w) SUB) | by right ].
  Qed.

End MemoryHelpers.

Section Frame.

  Context [Sm: State.type].
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).

  Definition action_local {A} (c: program Sm A): Prop :=
    forall s1 s2 f,
      s1 $+ f = Some s2 ->
      match c s1 with
      | Some (Success (v, s1')) =>
          exists s2',
          s1' $+ f = Some s2'
          /\ c s2 = Some (Success (v, s2'))
      | Some Failure => True
      | None => c s2 = None
      end.

  Definition stack_discipline {A} (c: program Sm A): Prop :=
    forall s v s', c s = Some (Success (v, s')) -> domain_equal (store s) (store s').

  Lemma stack_discipline_of_eq {A} (c: program Sm A)
    (EQst': forall s v s', c s = Some (Success (v, s')) -> store s' = store s)
    : stack_discipline c.
  Proof using Type.
    by move=> s v s' EQc; rewrite (EQst' s v s' EQc).
  Qed.

  Definition action_local_strong {A} (c: program Sm A): Prop :=
    action_local c /\ stack_discipline c.

  Lemma action_local_of_strong {A} (c: program Sm A) (LOCAL: action_local_strong c)
    : action_local c.
  Proof using Type. exact: (proj1 LOCAL). Qed.

  Lemma stack_discipline_of_action_local_strong {A} (c: program Sm A)
    (LOCAL: action_local_strong c)
    : stack_discipline c.
  Proof using Type. exact: (proj2 LOCAL). Qed.

  Lemma action_local_strong_ret {A} (x: A): action_local_strong (ret x).
  Proof using Type.
    split.
    { by move=> s1 s2 f EQs2 /=; exists s2; split. }
    by apply: stack_discipline_of_eq => s v s' [] _ <-.
  Qed.

  Lemma action_local_strong_fail {A}: action_local_strong (fail (S:=Sm) (A:=A)).
  Proof using Type.
    split.
    { by move=> s1 s2 f EQs2. }
    by move=> s v s' EQc; discriminate EQc.
  Qed.

  Lemma action_local_strong_loop {A}: action_local_strong (loop (S:=Sm) (A:=A)).
  Proof using Type.
    split.
    { by move=> s1 s2 f EQs2. }
    by move=> s v s' EQc; discriminate EQc.
  Qed.

  Lemma action_local_strong_bind {A B} (c: program Sm A) (g: A -> program Sm B)
    (LOCALc: action_local_strong c) (LOCALg: forall x, action_local_strong (g x))
    : action_local_strong (bind c g).
  Proof using Type.
    split.
    { move=> s1 s2 f EQs2; rewrite /bind.
      move: (proj1 LOCALc s1 s2 f EQs2).
      case: (c s1) => [ [ [x s1']| ]| ] //=; last by move=> ->.
      move=> [s2' [EQs2' ->] ] /=.
      by move: (proj1 (LOCALg x) s1' s2' f EQs2'); case: (g x s1'). }
    move=> s v s'; rewrite /bind.
    case EQc: (c s) => [ [ [x s1]| ]| ] // EQg.
    exact: (domain_equal_tran _ _ _ (proj2 LOCALc s x s1 EQc) (proj2 (LOCALg x) s1 v s' EQg)).
  Qed.

  Lemma action_local_strong_If {A} (c_if: program Sm bool) (c_then c_else: program Sm A)
    (LOCALif: action_local_strong c_if) (LOCALthen: action_local_strong c_then)
    (LOCALelse: action_local_strong c_else)
    : action_local_strong (If c_if then c_then else c_else).
  Proof using Type.
    by apply: action_local_strong_bind; [exact: LOCALif | case].
  Qed.

  Lemma action_local_strong_while_fuel (fuel: nat)
    (cond: program Sm bool) (body: program Sm unit)
    (LOCALcond: action_local_strong cond) (LOCALbody: action_local_strong body)
    : action_local_strong (while_fuel fuel cond body).
  Proof using Type.
    elim: fuel => [ |fuel IH]; first exact: action_local_strong_loop.
    rewrite while_fuel_fixpoint.
    apply: action_local_strong_If; [exact: LOCALcond | | exact: action_local_strong_ret].
    apply: action_local_strong_bind; [exact: LOCALbody | move=> _; exact: IH].
  Qed.

  Lemma action_local_strong_While (cond: program Sm bool) (body: program Sm unit)
    (LOCALcond: action_local_strong cond) (LOCALbody: action_local_strong body)
    : action_local_strong (while cond body).
  Proof using Type.
    have FUEL: forall fuel, action_local_strong (while_fuel fuel cond body)
      := fun fuel => action_local_strong_while_fuel fuel cond body LOCALcond LOCALbody.
    split.
    { move=> s1 s2 f EQs2.
      case EQw: (while cond body s1) => [ [ [ [] s1']| ]| ] //.
      - case: (proj1 (while_fuel_while_some cond body s1 (Success (tt, s1'))) EQw)
          => fuel EQfuel.
        move: (proj1 (FUEL fuel) s1 s2 f EQs2); rewrite EQfuel /= => -[s2' [EQs2' EQfuel'] ].
        exists s2'; split; [exact: EQs2' | ].
        by apply/while_fuel_while_some; exists fuel.
      - apply: while_fuel_None_while => fuel.
        move: (proj1 (FUEL fuel) s1 s2 f EQs2).
        by rewrite (while_None_while_fuel cond body s1 EQw fuel) /=. }
    move=> s v s' EQw.
    case: (proj1 (while_fuel_while_some cond body s (Success (v, s'))) EQw) => fuel EQfuel.
    exact: (proj2 (FUEL fuel) s v s' EQfuel).
  Qed.

  Local Notation SCnt := (excl (@store_cnt _ Nm Vl St)).

  (* Simplifies a [with_var] term into a proof amenable form *)
  #[local] Lemma with_var_eval {A} {So: Storable.type Vl} (e: So)
    (p: Nm -> program Sm A) (s: Sm)
    : with_var e p s
      = match push (store s) (scnt s) (encode e) with
        | Some (st, sg, n) =>
            match mk_state_opt st sg (heap s) (alc s) with
            | Some s1 =>
                match p n s1 with
                | Some (Success (v, s')) =>
                    match pop (store s') with
                    | Some st' =>
                        match mk_state_opt st' (scnt s') (heap s') (alc s') with
                        | Some s'' => Some (Success (v, s''))
                        | None => Some Failure
                        end
                    | None => Some Failure
                    end
                | Some Failure => Some Failure
                | None => None
                end
            | None => Some Failure
            end
        | None => Some Failure
        end.
  Proof using Type.
    rewrite /with_var /bind /get /put /ret /fail.
    case: (push (store s) (scnt s) (encode e)) => [ [ [st sg] n]| ] //.
    case: (mk_state_opt st sg (heap s) (alc s)) => [s1| ] //.
    case: (p n s1) => [ [ [v s']| ]| ] //.
    case: (pop (store s')) => [st'| ] //.
    by case: (mk_state_opt st' (scnt s') (heap s') (alc s')) => [s''| ].
  Qed.

  (* Further simplifies a [with_var] *)
  Lemma with_var_eval_push {A} {So: Storable.type Vl} (e: So)
    (p: Nm -> program Sm A) (s: Sm)
    (st: St) (sg: SCnt) (n: Nm) (s1: Sm)
    (PUSH: push (store s) (scnt s) (encode e) = Some (st, sg, n))
    (E1: store s1 = st) (E2: scnt s1 = sg)
    (E3: heap s1 = heap s) (E4: alc s1 = alc s)
    : with_var e p s
      = match p n s1 with
        | Some (Success (v, s')) =>
            match pop (store s') with
            | Some st' =>
                match mk_state_opt st' (scnt s') (heap s') (alc s') with
                | Some s'' => Some (Success (v, s''))
                | None => Some Failure
                end
            | None => Some Failure
            end
        | Some Failure => Some Failure
        | None => None
        end.
  Proof using Type.
    rewrite (with_var_eval e p s) PUSH.
    have MK: mk_state_opt st sg (heap s) (alc s) = Some s1
      by apply/mk_state_opt_some; rewrite E1 E2 E3 E4.
    by rewrite MK.
  Qed.

  (* Core properties about [with_var], similar to mixin laws like [push_mem] *)
  Lemma with_var_core {A} {So: Storable.type Vl} (e: So)
    (p: Nm -> program Sm A)
    (s: Sm) (st1: St) (sg1: SCnt) (n: Nm) (nm: nat)
    (GET: cget (scnt s) = Some nm)
    (PUSH: push (store s) (scnt s) (encode e) = Some (st1, sg1, n))
    (D1: dominates st1 sg1)
    (v: A) (s'': Sm)
    (CONT: p n (mk_state st1 sg1 (heap s) (alc s) D1 (state_heap_dominates s))
           = Some (Success (v, s'')))
    (PRES: stack_discipline (p n))
    : exists t bl bi,
        pop (store s'') = Some t
        /\ t $+ bl = Some (store s'')
        /\ (exists a w, (a |-> w) $<= bl)
        /\ (forall a w, (a |-> w) $<= bl -> block a = bi)
        /\ (forall a w, (a |-> w) $<= t -> (block a < bi)%nat)
        /\ (nm <= bi)%nat.
  Proof using Type.
    case: (push_mem (store s) (scnt s) (encode e) st1 sg1 n nm PUSH GET)
      => REF [ALW SUM1].
    have SUBa0: (((mkAddr nm 0%N: Ad) |-> (encode e)): St) $<= st1
      := substate_of_partition_l SUM1.
    have SUBa1: (((mkAddr nm 0%N: Ad) |-> (encode e)): St)
                $<= store (mk_state st1 sg1 (heap s) (alc s) D1 (state_heap_dominates s))
      by rewrite store_mk_state; exact: SUBa0.
    have [w' SUBw'] := domain_equal_fw _ _ (PRES _ v s'' CONT) (mkAddr nm 0%N) (encode e) SUBa1.
    have NEMP: store s'' <> $0 := sub_one_neq_emp _ _ _ SUBw'.
    case: (pop_some (store s'') NEMP) => t POP.
    case: (pop_mem (store s'') t POP) => bl [bi [SUM2 [NE [BLK LT] ] ] ].
    exists t, bl, bi.
    do 5 (split; [ by [] | ]).
    case: (proj1 (sub_sum_split_iff t bl (store s'') SUM2 (mkAddr nm 0%N) w') SUBw')
      => [SUBt|SUBbl].
    - have := LT _ _ SUBt; rewrite mkAddr_block; lia.
    - have := BLK _ _ SUBbl; rewrite mkAddr_block; lia.
  Qed.

  Lemma action_local_strong_with_var {A} {So: Storable.type Vl} (e: So)
    (p: Nm -> program Sm A)
    (LOCAL: forall nm, action_local_strong (p nm))
    : action_local_strong (with_var e p).
  Proof using Type.
    split.
    {
      move=> s sf f EQsf.
      case/state_sum_spec: EQsf => EQstf [ EQsgf [ EQhpf EQalcf ] ].
      case PUSH1: (push (store s) (scnt s) (encode e)) => [ [ [st1 sg1] n]| ]; last first.
      { by rewrite (with_var_eval e p s) PUSH1. }
      case: (proj2 (push_some (store s) (scnt s) (encode e))
               (ex_intro _ st1 (ex_intro _ sg1 (ex_intro _ n PUSH1))))
        => nm [GET FRESH].
      have D1: dominates st1 sg1
        := dominates_push _ _ _ _ _ _ PUSH1 (state_store_dominates s).
      pose s1 := mk_state st1 sg1 (heap s) (alc s) D1 (state_heap_dominates s).
      have EVAL1 := with_var_eval_push e p s st1 sg1 n s1 PUSH1
                      (store_mk_state _ _ _ _ _ _) (scnt_mk_state _ _ _ _ _ _)
                      (heap_mk_state _ _ _ _ _ _) (alc_mk_state _ _ _ _ _ _).
      have EQsgfr: scnt f = ($0: SCnt).
      { case: (excl_sum_excl _ (scnt s) (scnt f) (scnt sf) EQsgf) => [EQsg|EQsgfr] //.
        by exfalso; move: GET; rewrite EQsg cget_emp. }
      have EQsgf': scnt sf = scnt s.
      { have EQsg: scnt s $+ scnt f = Some (scnt s) by rewrite EQsgfr; exact: op_id_r.
        congruence. }
      have GET2: cget (scnt sf) = Some nm by rewrite EQsgf'.
      have FRESH2: forall (o: N.t) (v': Vl),
          ~ (((((mkAddr nm o): Ad) |-> v'): St) $<= store sf).
      { move=> o v' SUB.
        have := state_store_dominates sf (mkAddr nm o) v' nm SUB GET2.
        rewrite mkAddr_block; lia. }
      case: (proj1 (push_some (store sf) (scnt sf) (encode e))
               (ex_intro _ nm (conj GET2 FRESH2)))
        => st2 [sg2 [n2 PUSH2] ].
      have PUSH2': push (store sf) (scnt s) (encode e) = Some (st2, sg2, n2)
        by rewrite -EQsgf'.
      have EQn2: n2 = n
        := push_det (store sf) (store s) (scnt s) (encode e) (encode e)
             st2 st1 sg2 sg1 n2 n PUSH2' PUSH1.
      move: EQn2 PUSH2 PUSH2' => -> PUSH2 PUSH2'.
      have EQsg2: sg2 = sg1.
      { have G2 := push_cnt _ _ _ _ _ _ PUSH2'.
        have G1 := push_cnt _ _ _ _ _ _ PUSH1.
        congruence. }
      move: EQsg2 PUSH2 => -> PUSH2.
      case: (push_mem (store s) (scnt s) (encode e) st1 sg1 n nm PUSH1 GET)
        => REF1 [ALW1 SUM1].
      case: (push_mem (store sf) (scnt sf) (encode e) st2 sg1 n nm PUSH2 GET2)
        => REF2 [ALW2 SUM2].
      have EQstf1: st1 $+ store f = Some st2.
      { have ASSC := op_assc ((((mkAddr nm 0%N): Ad) |-> (encode e)): St) (store s) (store f).
        rewrite SUM1 EQstf /Basics.flip /= in ASSC.
        by rewrite ASSC SUM2. }
      have D2: dominates st2 sg1
        := dominates_push _ _ _ _ _ _ PUSH2 (state_store_dominates sf).
      pose sf1 := mk_state st2 sg1 (heap sf) (alc sf) D2 (state_heap_dominates sf).
      have EVAL2 := with_var_eval_push e p sf st2 sg1 n sf1 PUSH2
                      (store_mk_state _ _ _ _ _ _) (scnt_mk_state _ _ _ _ _ _)
                      (heap_mk_state _ _ _ _ _ _) (alc_mk_state _ _ _ _ _ _).
      have EQsf1: s1 $+ f = Some sf1.
      { apply/state_sum_spec.
        rewrite /s1 /sf1 ?store_mk_state ?scnt_mk_state ?heap_mk_state ?alc_mk_state.
        split; [exact: EQstf1 | split; [ | split; [exact: EQhpf | exact: EQalcf] ] ].
        by rewrite EQsgfr; exact: op_id_r. }
      have ACT := proj1 (LOCAL n) s1 sf1 f EQsf1.
      have PRES := proj2 (LOCAL n).
      rewrite EVAL1.
      case CONT1: (p n s1) => [ [ [v s2]| ]| ]; rewrite CONT1 in ACT.
      - case: ACT => sf2 [EQsf2 CONT2].
        case: (with_var_core e p s st1 sg1 n nm GET PUSH1 D1 v s2 CONT1 PRES)
          => t [bl [bi [POP1 [SUMt [NE [BLK [LT LEnm] ] ] ] ] ] ].
        case/state_sum_spec: EQsf2 => EQstf2 [ EQsgf2 [ EQhpf2 EQalcf2 ] ].
        have [u [EQtf SUMu] ] :=
          op_swap t bl (store f) (store s2) (store sf2) SUMt EQstf2.
        have LTf: forall (a: Ad) (w: Vl),
            (((a |-> w): St) $<= store f) -> (block a < bi)%nat.
        { move=> a w SUBa.
          have SUBsf: ((a |-> w): St) $<= store sf
            := substate_tran _ _ _ SUBa (substate_of_partition_r EQstf).
          have := state_store_dominates sf a w nm SUBsf GET2; lia. }
        have POP2: pop (store sf2) = Some u.
        { apply: (pop_char (store sf2) u bl bi SUMu NE BLK).
          move=> a w SUBa.
          case: (proj1 (sub_sum_split_iff t (store f) u EQtf a w) SUBa) => [SUBt|SUBf].
          - exact: (LT _ _ SUBt).
          - exact: (LTf _ _ SUBf). }
        have Dt: dominates t (scnt s2)
          := dominates_pop (store s2) t (scnt s2) POP1 (state_store_dominates s2).
        have Du: dominates u (scnt sf2)
          := dominates_pop (store sf2) u (scnt sf2) POP2 (state_store_dominates sf2).
        pose s3 := mk_state t (scnt s2) (heap s2) (alc s2) Dt
                   (state_heap_dominates s2).
        pose sf3 := mk_state u (scnt sf2) (heap sf2) (alc sf2) Du
                    (state_heap_dominates sf2).
        have MK1: mk_state_opt t (scnt s2) (heap s2) (alc s2) = Some s3
          by apply/mk_state_opt_some;
             rewrite /s3 store_mk_state scnt_mk_state heap_mk_state alc_mk_state.
        have MK2: mk_state_opt u (scnt sf2) (heap sf2) (alc sf2) = Some sf3
          by apply/mk_state_opt_some;
             rewrite /sf3 store_mk_state scnt_mk_state heap_mk_state alc_mk_state.
        rewrite POP1 MK1.
        exists sf3; split.
        + apply/state_sum_spec.
          rewrite /s3 /sf3 ?store_mk_state ?scnt_mk_state ?heap_mk_state ?alc_mk_state.
          by split; [exact: EQtf | split; [exact: EQsgf2 | split] ].
        + by rewrite EVAL2 CONT2 POP2 MK2.
      - by [].
      - by rewrite EVAL2 ACT.
    }
    move=> s v s'.
    case PUSH: (push (store s) (scnt s) (encode e)) => [ [ [st1 sg1] n]| ].
    2: { by rewrite (with_var_eval e p s) PUSH => -[]. }
    case: (proj2 (push_some (store s) (scnt s) (encode e))
             (ex_intro _ st1 (ex_intro _ sg1 (ex_intro _ n PUSH))))
      => nm [GET FRESH].
    have D1: dominates st1 sg1
      := dominates_push _ _ _ _ _ _ PUSH (state_store_dominates s).
    pose s1 := mk_state st1 sg1 (heap s) (alc s) D1 (state_heap_dominates s).
    rewrite (with_var_eval_push e p s st1 sg1 n s1 PUSH
               (store_mk_state _ _ _ _ _ _) (scnt_mk_state _ _ _ _ _ _)
               (heap_mk_state _ _ _ _ _ _) (alc_mk_state _ _ _ _ _ _)).
    case CONT: (p n s1) => [ [ [v0 s2]| ]| ].
    2: { by move=> EQc; discriminate EQc. }
    2: { by move=> EQc; discriminate EQc. }
    case: (with_var_core e p s st1 sg1 n nm GET PUSH D1 v0 s2 CONT (proj2 (LOCAL n)))
      => t [bl [bi [POP1 [SUMt [NE [BLK [LT LEnm] ] ] ] ] ] ].
    have Dt: dominates t (scnt s2)
      := dominates_pop (store s2) t (scnt s2) POP1 (state_store_dominates s2).
    pose s3 := mk_state t (scnt s2) (heap s2) (alc s2) Dt (state_heap_dominates s2).
    have MK: mk_state_opt t (scnt s2) (heap s2) (alc s2) = Some s3
      by apply/mk_state_opt_some;
         rewrite /s3 store_mk_state scnt_mk_state heap_mk_state alc_mk_state.
    rewrite POP1 MK => -[] _ <-.
    case: (push_mem (store s) (scnt s) (encode e) st1 sg1 n nm PUSH GET)
      => REF [ALW SUM1].
    have PRESn := proj2 (LOCAL n) s1 v0 s2 CONT.
    have EQbi: bi = nm.
    { case: NE => a1 [w1 SUBbl1].
      have SUBs2: ((a1 |-> w1): St) $<= store s2
        := substate_tran _ _ _ SUBbl1 (substate_of_partition_r SUMt).
      case: (domain_equal_bw _ _ PRESn a1 w1 SUBs2) => w1' SUBw1'.
      rewrite /s1 store_mk_state in SUBw1'.
      case: (proj1 (one_discriminate_iff SUM1 a1 w1') SUBw1') => [ [EQa1 _] | [_ SUBs0] ].
      - by rewrite -(BLK _ _ SUBbl1) EQa1 mkAddr_block.
      - have B1 := state_store_dominates s a1 w1' nm SUBs0 GET.
        have B2 := BLK _ _ SUBbl1.
        lia. }
    move=> a; split.
    { move=> [w SUBa].
      have SUBst1: (((a |-> w): St) $<= st1)
        := substate_tran _ _ _ SUBa (substate_of_partition_r SUM1).
      have SUBs1: (((a |-> w): St) $<= store s1)
        by rewrite /s1 store_mk_state; exact: SUBst1.
      case: (domain_equal_fw _ _ PRESn a w SUBs1) => w' SUBw'.
      case: (proj1 (sub_sum_split_iff t bl (store s2) SUMt a w') SUBw') => [SUBt|SUBbl].
      - by rewrite /s3 store_mk_state; exists w'.
      - exfalso.
        have B1 := BLK _ _ SUBbl.
        have B2 := state_store_dominates s a w nm SUBa GET.
        lia. }
    move=> [w SUBt].
    rewrite /s3 store_mk_state in SUBt.
    have SUBs2: ((a |-> w): St) $<= store s2
      := substate_tran _ _ _ SUBt (substate_of_partition_l SUMt).
    case: (domain_equal_bw _ _ PRESn a w SUBs2) => w' SUBw'.
    rewrite /s1 store_mk_state in SUBw'.
    case: (proj1 (one_discriminate_iff SUM1 a w') SUBw') => [ [EQa _] | [_ SUBs0] ].
    - exfalso.
      have B1 := LT _ _ SUBt.
      rewrite EQa mkAddr_block EQbi in B1.
      lia.
    - by exists w'.
  Qed.

  Lemma action_local_with_var_of_strong {A} {So: Storable.type Vl} (e: So)
    (p: Nm -> program Sm A)
    (LOCAL: forall nm, action_local_strong (p nm))
    : action_local (with_var e p).
  Proof using Type. exact: (proj1 (action_local_strong_with_var e p LOCAL)). Qed.

  Lemma action_local_strong_read_var {So: Storable.type Vl} (varname: Nm):
    action_local_strong (read_var (So:=So) varname).
  Proof using Type.
    split.
    { move=> s1 s2 f EQs2.
      have EQst2 := state_hp_ext_store s1 s2 f EQs2.
      rewrite /read_var /bind /get.
      case LK1: (lookup (store s1) varname) => [mv| ] //=.
      case DEC: (decode mv) => [val| ] //=.
      have LK2: lookup (store s2) varname = Some mv.
      { apply/lookup_iff.
        case: (proj2 (lookup_iff (store s1) varname mv) LK1) => a [REF [ALW SUB] ].
        exists a; split; [exact: REF | split; [exact: ALW | ] ].
        exact: (substate_tran _ _ _ SUB (substate_of_partition_l EQst2)). }
      by rewrite LK2 /= DEC; exists s2. }
    apply: stack_discipline_of_eq => s v s' EQc.
    by rewrite (read_var_eq_state varname s v s' EQc).
  Qed.

  Lemma action_local_strong_write_var {So: Storable.type Vl} (varname: Nm) (val: So):
    action_local_strong (write_var varname val).
  Proof using Type.
    split.
    { move=> s1 s2 f EQs2.
      have EQst2 := state_hp_ext_store s1 s2 f EQs2.
      have EQsg2 := state_hp_ext_scnt s1 s2 f EQs2.
      have EQhp2 := state_hp_ext_heap s1 s2 f EQs2.
      have EQalc2 := state_hp_ext_alc s1 s2 f EQs2.
      case MUT1: (mutate (store s1) varname (encode val)) => [st1'| ];
        last by rewrite (write_var_none varname val s1 MUT1).
      case: (mutate_frame (store s1) (store f) (store s2) st1' varname (encode val) EQst2 MUT1)
        => st2' [MUT2 EQst'].
      have D1: dominates st1' (scnt s1)
        := dominates_mutate (store s1) st1' varname (encode val) (scnt s1) MUT1
             (state_store_dominates s1).
      have D2: dominates st2' (scnt s2)
        := dominates_mutate (store s2) st2' varname (encode val) (scnt s2) MUT2
             (state_store_dominates s2).
      rewrite (write_var_some varname val s1
                 (mk_state st1' (scnt s1) (heap s1) (alc s1) D1 (state_heap_dominates s1))
                 st1' MUT1 (store_mk_state _ _ _ _ _ _) (scnt_mk_state _ _ _ _ _ _)
                 (heap_mk_state _ _ _ _ _ _) (alc_mk_state _ _ _ _ _ _)).
      exists (mk_state st2' (scnt s2) (heap s2) (alc s2) D2 (state_heap_dominates s2)).
      split; first by apply: state_hp_ext_intro; autorewrite with seplog.
      exact: (write_var_some varname val s2
                (mk_state st2' (scnt s2) (heap s2) (alc s2) D2 (state_heap_dominates s2))
                st2' MUT2 (store_mk_state _ _ _ _ _ _) (scnt_mk_state _ _ _ _ _ _)
                (heap_mk_state _ _ _ _ _ _) (alc_mk_state _ _ _ _ _ _)). }
    move=> s v s'.
    rewrite /write_var /bind /get.
    case MUT: (mutate (store s) varname (encode val)) => [st| ]; last by move=> [].
    case MK: (mk_state_opt st (scnt s) (heap s) (alc s)) => [s1| ]; last by move=> [].
    rewrite /put => -[] _ <-.
    rewrite (proj1 (proj1 (mk_state_opt_some st (scnt s) (heap s) (alc s) s1) MK)).
    exact: (mutate_dom_eq (store s) st varname (encode val) MUT).
  Qed.

  Lemma action_local_strong_read_ptr {So: Storable.type Vl} (p: Pt):
    action_local_strong (read_ptr (So:=So) p).
  Proof using Type.
    split.
    { move=> s1 s2 f EQs2.
      have EQhp2 := state_hp_ext_heap s1 s2 f EQs2.
      rewrite /read_ptr /bind /get.
      case LK1: (lookup (heap s1) p) => [mv| ] //=.
      case DEC: (decode mv) => [val| ] //=.
      have LK2: lookup (heap s2) p = Some mv.
      { apply/lookup_iff.
        case: (proj2 (lookup_iff (heap s1) p mv) LK1) => a [REF [ALW SUB] ].
        exists a; split; [exact: REF | split; [exact: ALW | ] ].
        exact: (substate_tran _ _ _ SUB (substate_of_partition_l EQhp2)). }
      by rewrite LK2 /= DEC; exists s2. }
    apply: stack_discipline_of_eq => s v s' EQc.
    by rewrite (read_ptr_eq_state p s v s' EQc).
  Qed.

  Lemma action_local_strong_write_ptr {So: Storable.type Vl} (p: Pt) (val: So):
    action_local_strong (write_ptr p val).
  Proof using Type.
    split.
    { move=> s1 s2 f EQs2.
      have EQst2 := state_hp_ext_store s1 s2 f EQs2.
      have EQsg2 := state_hp_ext_scnt s1 s2 f EQs2.
      have EQhp2 := state_hp_ext_heap s1 s2 f EQs2.
      have EQalc2 := state_hp_ext_alc s1 s2 f EQs2.
      case MUT1: (mutate (heap s1) p (encode val)) => [h1'| ];
        last by rewrite (write_ptr_none p val s1 MUT1).
      case: (mutate_frame (heap s1) (heap f) (heap s2) h1' p (encode val) EQhp2 MUT1)
        => h2' [MUT2 EQhp'].
      have D1: dominates h1' (alc s1)
        := dominates_mutate (heap s1) h1' p (encode val) (alc s1) MUT1
             (state_heap_dominates s1).
      have D2: dominates h2' (alc s2)
        := dominates_mutate (heap s2) h2' p (encode val) (alc s2) MUT2
             (state_heap_dominates s2).
      rewrite (write_ptr_some p val s1
                 (mk_state (store s1) (scnt s1) h1' (alc s1) (state_store_dominates s1) D1)
                 h1' MUT1 (store_mk_state _ _ _ _ _ _) (scnt_mk_state _ _ _ _ _ _)
                 (heap_mk_state _ _ _ _ _ _) (alc_mk_state _ _ _ _ _ _)).
      exists (mk_state (store s2) (scnt s2) h2' (alc s2) (state_store_dominates s2) D2).
      split; first by apply: state_hp_ext_intro; autorewrite with seplog.
      exact: (write_ptr_some p val s2
                (mk_state (store s2) (scnt s2) h2' (alc s2) (state_store_dominates s2) D2)
                h2' MUT2 (store_mk_state _ _ _ _ _ _) (scnt_mk_state _ _ _ _ _ _)
                (heap_mk_state _ _ _ _ _ _) (alc_mk_state _ _ _ _ _ _)). }
    apply: stack_discipline_of_eq => s v s'.
    rewrite /write_ptr /bind /get.
    case MUT: (mutate (heap s) p (encode val)) => [h| ]; last by move=> [].
    case MK: (mk_state_opt (store s) (scnt s) h (alc s)) => [s1| ]; last by move=> [].
    rewrite /put => -[] _ <-.
    exact: (proj1 (proj1 (mk_state_opt_some (store s) (scnt s) h (alc s) s1) MK)).
  Qed.

  Lemma action_local_strong_alloc_ptr {So: Storable.type Vl} (sz: N.t) (val: So):
    action_local_strong (alloc_ptr (So:=So) sz val).
  Proof using Type.
    split.
    { move=> s1 s2 f EQs2.
      have EQhp2 := state_hp_ext_heap s1 s2 f EQs2.
      have EQalc2 := state_hp_ext_alc s1 s2 f EQs2.
      case: (N.le_gt_cases sz alloc_max_size) => [BNDle | BND];
        last by rewrite (alloc_ptr_overflow_fail sz val s1 BND).
      case AL1: (alloc (heap s1) (alc s1) sz (encode val)) => [ [ [h1' c1'] p1]| ];
        last by rewrite (alloc_ptr_none sz val s1 AL1).
      have EQalcf: alc f = $0.
      { case: (proj2 (alloc_some (heap s1) (alc s1) sz (encode val))
                 (ex_intro _ h1' (ex_intro _ c1' (ex_intro _ p1 AL1))))
          => bid [GET _].
        case: (excl_sum_excl _ (alc s1) (alc f) (alc s2) EQalc2) => [EQalc1|EQalcf] //.
        by exfalso; move: GET; rewrite EQalc1 cget_emp. }
      have EQalc2': alc s2 = alc s1.
      { have EQalc1: alc s1 $+ alc f = Some (alc s1) by rewrite EQalcf; exact: op_id_r.
        congruence. }
      have DOM2: dominates (heap s2) (alc s1)
        by rewrite -EQalc2'; exact: (state_heap_dominates s2).
      case: (alloc_frame (heap s1) (heap f) (heap s2) h1' (alc s1) c1'
               sz (encode val) p1 EQhp2 DOM2 AL1)
        => h2' [AL2 EQhp'].
      have AL2': alloc (heap s2) (alc s2) sz (encode val) = Some (h2', c1', p1)
        by rewrite EQalc2'.
      have D1: dominates h1' c1'
        := dominates_alloc (heap s1) h1' (alc s1) c1' sz (encode val) p1 AL1
             (state_heap_dominates s1).
      have D2: dominates h2' c1'
        := dominates_alloc (heap s2) h2' (alc s1) c1' sz (encode val) p1 AL2 DOM2.
      have EQalc': c1' $+ alc f = Some c1' by rewrite EQalcf; exact: op_id_r.
      rewrite (alloc_ptr_some sz val s1
                 (mk_state (store s1) (scnt s1) h1' c1' (state_store_dominates s1) D1)
                 h1' c1' p1 BNDle AL1 (store_mk_state _ _ _ _ _ _) (scnt_mk_state _ _ _ _ _ _)
                 (heap_mk_state _ _ _ _ _ _) (alc_mk_state _ _ _ _ _ _)).
      exists (mk_state (store s2) (scnt s2) h2' c1' (state_store_dominates s2) D2).
      split; first by apply: state_hp_ext_intro; autorewrite with seplog;
        [exact: state_hp_ext_store | exact: state_hp_ext_scnt | | ].
      exact: (alloc_ptr_some sz val s2
                (mk_state (store s2) (scnt s2) h2' c1' (state_store_dominates s2) D2)
                h2' c1' p1 BNDle AL2' (store_mk_state _ _ _ _ _ _) (scnt_mk_state _ _ _ _ _ _)
                (heap_mk_state _ _ _ _ _ _) (alc_mk_state _ _ _ _ _ _)). }
    apply: stack_discipline_of_eq => s v s'.
    rewrite /alloc_ptr.
    case: (N.leb sz alloc_max_size); last by move=> [].
    rewrite /bind /get.
    case AL: (alloc (heap s) (alc s) sz (encode val)) => [ [ [h c] q]| ]; last by move=> [].
    case MK: (mk_state_opt (store s) (scnt s) h c) => [s1| ]; last by move=> [].
    rewrite /put /ret /bind => -[] _ <-.
    exact: (proj1 (proj1 (mk_state_opt_some (store s) (scnt s) h c s1) MK)).
  Qed.

  Lemma action_local_strong_free_ptr (p: Pt): action_local_strong (free_ptr p).
  Proof using Type.
    split.
    { move=> s1 s2 f EQs2.
      have EQhp2 := state_hp_ext_heap s1 s2 f EQs2.
      case FR1: (free (heap s1) p) => [h1'| ];
        last by rewrite (free_ptr_none p s1 FR1).
      case: (free_frame (heap s1) (heap f) (heap s2) h1' p EQhp2 FR1) => h2' [FR2 EQhp'].
      have D1: dominates h1' (alc s1)
        := dominates_free (heap s1) h1' p (alc s1) FR1 (state_heap_dominates s1).
      have D2: dominates h2' (alc s2)
        := dominates_free (heap s2) h2' p (alc s2) FR2 (state_heap_dominates s2).
      rewrite (free_ptr_some p s1
                 (mk_state (store s1) (scnt s1) h1' (alc s1) (state_store_dominates s1) D1)
                 h1' FR1 (store_mk_state _ _ _ _ _ _) (scnt_mk_state _ _ _ _ _ _)
                 (heap_mk_state _ _ _ _ _ _) (alc_mk_state _ _ _ _ _ _)).
      exists (mk_state (store s2) (scnt s2) h2' (alc s2) (state_store_dominates s2) D2).
      split; first by apply: state_hp_ext_intro; autorewrite with seplog;
        [exact: state_hp_ext_store | exact: state_hp_ext_scnt | | exact: state_hp_ext_alc].
      exact: (free_ptr_some p s2
                (mk_state (store s2) (scnt s2) h2' (alc s2) (state_store_dominates s2) D2)
                h2' FR2 (store_mk_state _ _ _ _ _ _) (scnt_mk_state _ _ _ _ _ _)
                (heap_mk_state _ _ _ _ _ _) (alc_mk_state _ _ _ _ _ _)). }
    apply: stack_discipline_of_eq => s v s'.
    rewrite /free_ptr /bind /get.
    case FR: (free (heap s) p) => [h| ]; last by move=> [].
    case MK: (mk_state_opt (store s) (scnt s) h (alc s)) => [s1| ]; last by move=> [].
    rewrite /put => -[] _ <-.
    exact: (proj1 (proj1 (mk_state_opt_some (store s) (scnt s) h (alc s) s1) MK)).
  Qed.

  Lemma action_local_strong_shift_fw_ptr (ptr: Pt) (sh: N.t):
    action_local_strong (shift_fw_ptr ptr sh).
  Proof using Type.
    split.
    { move=> s1 s2 f EQs2.
      have EQhp2 := state_hp_ext_heap s1 s2 f EQs2.
      have SUB12: heap s1 $<= heap s2 := substate_of_partition_l EQhp2.
      rewrite /shift_fw_ptr /bind /get.
      case WV1: (weakly_valid (heap s1) ptr) => //=.
      rewrite (weakly_valid_mono _ _ _ SUB12 WV1).
      case: (ptr_shift_fw ptr sh) => [q| ] //=.
      case WV2: (weakly_valid (heap s1) q) => //=.
      by rewrite (weakly_valid_mono _ _ _ SUB12 WV2); exists s2. }
    apply: stack_discipline_of_eq => s v s'.
    rewrite /shift_fw_ptr /bind /get.
    case: (weakly_valid (heap s) ptr); case: (ptr_shift_fw ptr sh) => [q| ];
      try (by move=> EQc; discriminate EQc).
    case: (weakly_valid (heap s) q); [ by move=> [] _ <- | by move=> [] ].
  Qed.

  Lemma action_local_strong_shift_bw_ptr (ptr: Pt) (sh: N.t):
    action_local_strong (shift_bw_ptr ptr sh).
  Proof using Type.
    split.
    { move=> s1 s2 f EQs2.
      have EQhp2 := state_hp_ext_heap s1 s2 f EQs2.
      have SUB12: heap s1 $<= heap s2 := substate_of_partition_l EQhp2.
      rewrite /shift_bw_ptr /bind /get.
      case WV1: (weakly_valid (heap s1) ptr) => //=.
      rewrite (weakly_valid_mono _ _ _ SUB12 WV1).
      case: (ptr_shift_bw ptr sh) => [q| ] //=.
      case WV2: (weakly_valid (heap s1) q) => //=.
      by rewrite (weakly_valid_mono _ _ _ SUB12 WV2); exists s2. }
    apply: stack_discipline_of_eq => s v s'.
    rewrite /shift_bw_ptr /bind /get.
    case: (weakly_valid (heap s) ptr); case: (ptr_shift_bw ptr sh) => [q| ];
      try (by move=> EQc; discriminate EQc).
    case: (weakly_valid (heap s) q); [ by move=> [] _ <- | by move=> [] ].
  Qed.

  Lemma action_local_strong_eq_ptr (pl pr: Pt): action_local_strong (eq_ptr pl pr).
  Proof using Type.
    split.
    { move=> s1 s2 f EQs2.
      have EQhp2 := state_hp_ext_heap s1 s2 f EQs2.
      have SUB12: heap s1 $<= heap s2 := substate_of_partition_l EQhp2.
      rewrite /eq_ptr /bind /get.
      case CV: (cmp_valid (heap s1) pl pr) => //=.
      rewrite (cmp_valid_mono _ _ _ _ SUB12 CV).
      case: (cmp pl pr) => [b| ] //=.
      by exists s2. }
    apply: stack_discipline_of_eq => s v s'.
    rewrite /eq_ptr /bind /get.
    case: (cmp_valid (heap s) pl pr); last by move=> EQc; discriminate EQc.
    case: (cmp pl pr) => [b| ]; last by move=> EQc; discriminate EQc.
    by move=> [] _ <-.
  Qed.

  Lemma action_local_strong_div [UInt: Unsigned.Unsigned] (l r: UInt):
    action_local_strong (Unsigned.div (S:=Sm) l r).
  Proof using Type.
    rewrite /Unsigned.div.
    case: ifP => _; [exact: action_local_strong_fail | exact: action_local_strong_ret].
  Qed.

  Lemma action_local_strong_mdl [UInt: Unsigned.Unsigned] (l r: UInt):
    action_local_strong (Unsigned.mdl (S:=Sm) l r).
  Proof using Type.
    rewrite /Unsigned.mdl.
    case: ifP => _; [exact: action_local_strong_fail | exact: action_local_strong_ret].
  Qed.

  (* Executing c does not change a part of the store *)
  Definition indep_cmd_partial_store {A} (c: program Sm A) nms :=
    forall s v s', c s = Some (Success (v, s')) -> store_partial_equal (store s) (store s') nms.

  Lemma indep_cmd_partial_store_nil {A} (c: program Sm A):
    indep_cmd_partial_store c [].
  Proof using Type.
    by move=> s v s' EQc m w [].
  Qed.

  Lemma indep_cmd_partial_store_of_store_eq {A} (c: program Sm A) (nms: list Nm)
    (EQst': forall s v s', c s = Some (Success (v, s')) -> store s' = store s)
    : indep_cmd_partial_store c nms.
  Proof using Type.
    move=> s v s' EQc m w INm.
    by rewrite (EQst' s v s' EQc); exact: iff_refl.
  Qed.

  Lemma indep_cmd_partial_store_bind {A B}
    (c: program Sm A) (g: A -> program Sm B) (nms: list Nm)
    (INDEPc: indep_cmd_partial_store c nms)
    (INDEPg: forall x, indep_cmd_partial_store (g x) nms)
    : indep_cmd_partial_store (bind c g) nms.
  Proof using Type.
    move=> s v s' EQcg m w INm.
    rewrite /bind in EQcg.
    move: EQcg; case EQc: (c s) => [ [ [ x s1 ] | ] | ] // EQg.
    exact: (iff_trans (INDEPc s x s1 EQc m w INm) (INDEPg x s1 v s' EQg m w INm)).
  Qed.

  Lemma indep_cmd_partial_store_with_var {A} {So: Storable.type Vl} (e: So)
    (p: Nm -> program Sm A) (nms: list Nm)
    (PRES: forall n, stack_discipline (p n))
    (INDEP: forall n, indep_cmd_partial_store (p n) nms)
    : indep_cmd_partial_store (with_var e p) nms.
  Proof using Type.
    move=> s v s'.
    case PUSH: (push (store s) (scnt s) (encode e)) => [ [ [st1 sg1] n ] | ].
    2: { by rewrite /with_var /bind /get /ret /fail PUSH => -[]. }
    case: (proj2 (push_some (store s) (scnt s) (encode e))
             (ex_intro _ st1 (ex_intro _ sg1 (ex_intro _ n PUSH))))
      => bid [GET FRESH].
    have D1: dominates st1 sg1
      := dominates_push _ _ _ _ _ _ PUSH (state_store_dominates s).
    pose s1 := mk_state st1 sg1 (heap s) (alc s) D1 (state_heap_dominates s).
    have EQst1: store s1 = st1 := store_mk_state _ _ _ _ _ _.
    rewrite (with_var_eval_push e p s st1 sg1 n s1 PUSH
               (store_mk_state _ _ _ _ _ _) (scnt_mk_state _ _ _ _ _ _)
               (heap_mk_state _ _ _ _ _ _) (alc_mk_state _ _ _ _ _ _)).
    case CONT: (p n s1) => [ [ [v0 s2] | ] | ].
    2: { by move=> EQc; discriminate EQc. }
    2: { by move=> EQc; discriminate EQc. }
    case: (with_var_core e p s st1 sg1 n bid GET PUSH D1 v0 s2 CONT (PRES n))
      => t [bl [bi [POP1 [SUMt [NE [BLK [LT LEnm] ] ] ] ] ] ].
    have Dt: dominates t (scnt s2)
      := dominates_pop (store s2) t (scnt s2) POP1 (state_store_dominates s2).
    pose s3 := mk_state t (scnt s2) (heap s2) (alc s2) Dt (state_heap_dominates s2).
    have MK: mk_state_opt t (scnt s2) (heap s2) (alc s2) = Some s3
      by apply/mk_state_opt_some;
         rewrite /s3 store_mk_state scnt_mk_state heap_mk_state alc_mk_state.
    rewrite POP1 MK => -[] _ <-.
    rewrite /s3 store_mk_state.
    case: (push_mem (store s) (scnt s) (encode e) st1 sg1 n bid PUSH GET)
      => REF [ALW SUM1].
    have EQbid: bid = bi.
    { case: NE => a1 [w1 SUBbl1].
      have SUBs2: ((a1 |-> w1): St) $<= store s2
        := substate_tran _ _ _ SUBbl1 (substate_of_partition_r SUMt).
      case: (domain_equal_bw _ _ (PRES n s1 v0 s2 CONT) a1 w1 SUBs2) => w1' SUBw1'.
      move: EQst1 SUBw1' => -> SUBw1'.
      case: (proj1 (one_discriminate_iff SUM1 a1 w1') SUBw1') => [ [EQa1 _] | [_ SUBs0] ].
      - by rewrite -(BLK _ _ SUBbl1) EQa1 mkAddr_block.
      - have B1 := state_store_dominates s a1 w1' bid SUBs0 GET.
        have B2 := BLK _ _ SUBbl1.
        move: B2 B1 => -> B1.
        by case: (Nat.lt_irrefl bi (Nat.lt_le_trans _ _ _ B1 LEnm)). }
    move=> m w INm.
    have IND := INDEP n s1 v0 s2 CONT m w INm.
    move: EQst1 IND => -> IND.
    split.
    - move=> [a [REFa SUBa] ].
      have SUBst1: ((a |-> w): St) $<= st1
        := substate_tran _ _ _ SUBa (substate_of_partition_r SUM1).
      case: (proj1 IND (ex_intro _ a (conj REFa SUBst1))) => a' [REFa' SUBa'].
      have EQa': a' = a by congruence.
      move: EQa' SUBa' => -> SUBa'.
      case: (proj1 (sub_sum_split_iff t bl (store s2) SUMt a w) SUBa') => [SUBt | SUBbl].
      + by exists a.
      + have B1 := BLK _ _ SUBbl.
        have B2 := state_store_dominates s a w bid SUBa GET.
        move: B1 B2 => -> B2.
        by case: (Nat.lt_irrefl bi (Nat.lt_le_trans _ _ _ B2 LEnm)).
    - move=> [a [REFa SUBa] ].
      have SUBs2: ((a |-> w): St) $<= store s2
        := substate_tran _ _ _ SUBa (substate_of_partition_l SUMt).
      case: (proj2 IND (ex_intro _ a (conj REFa SUBs2))) => a' [REFa' SUBa'].
      have EQa': a' = a by congruence.
      move: EQa' SUBa' => -> SUBa'.
      case: (proj1 (one_discriminate_iff SUM1 a w) SUBa') => [ [EQa _] | [_ SUBs0] ].
      + have B1 := LT _ _ SUBa.
        rewrite EQa mkAddr_block EQbid in B1.
        by case: (Nat.lt_irrefl bi B1).
      + by exists a.
  Qed.

  Lemma indep_cmd_partial_store_write_var {So: Storable.type Vl}
    (n: Nm) (val: So) (nms: list Nm)
    (SEP: forall (m: Nm) (a b: Ad), List.In m nms ->
                                      References n a -> References m b -> b <> a)
    : indep_cmd_partial_store (write_var n val: program Sm unit) nms.
  Proof using Type.
    move=> s u s' EQc m w INm.
    case MUT: (mutate (store s) n (encode val)) => [ st' | ];
      last by rewrite (write_var_none n val s MUT) in EQc.
    have DOM: dominates st' (scnt s)
      := dominates_mutate (store s) st' n (encode val) (scnt s) MUT
           (state_store_dominates s).
    rewrite (write_var_some n val s
               (mk_state st' (scnt s) (heap s) (alc s) DOM (state_heap_dominates s)) st'
               MUT (store_mk_state _ _ _ _ _ _) (scnt_mk_state _ _ _ _ _ _)
               (heap_mk_state _ _ _ _ _ _) (alc_mk_state _ _ _ _ _ _)) in EQc.
    move: EQc => [_ <-].
    case: (proj2 (mutate_some_iff (store s) n (encode val)) (ex_intro _ st' MUT))
      => a [v0 [REF [ALW SUB0] ] ].
    rewrite store_mk_state.
    split.
    - move=> [b [REFb SUBb] ].
      exists b; split; first exact: REFb.
      apply/(mutate_mem_iff (store s) n (encode val) st' a REF MUT b w).
      by right; split; [ exact: (SEP m a b INm REF REFb) | exact: SUBb ].
    - move=> [b [REFb SUBb] ].
      exists b; split; first exact: REFb.
      case/(mutate_mem_iff (store s) n (encode val) st' a REF MUT b w): SUBb
        => [ [EQb EQw] | [NE SUB] ]; last exact: SUB.
      by case: (SEP m a b INm REF REFb EQb).
  Qed.

  (* Executing a command c does not change the store in a way that it invalidates the predicate P *)
  Definition indep_no_cnt {A} (P: Pred Sm) (c: program Sm A) :=
    forall s1 v s1' s, c s1 = Some (Success (v, s1')) ->
                       P (set_store_no_cnt s s1) ->
                       P (set_store_no_cnt s s1').

  Lemma indep_no_cnt_of_store_eq {A} (P: Pred Sm) (c: program Sm A)
    (EQst': forall s v s', c s = Some (Success (v, s')) -> store s' = store s)
    : indep_no_cnt P c.
  Proof using Type.
    move=> s1 v s1' s EQc Ps1.
    have EQs1': set_store_no_cnt s s1' = set_store_no_cnt s s1.
    { by apply: state_ext; autorewrite with seplog; first exact: (EQst' s1 v s1' EQc). }
    by rewrite EQs1'.
  Qed.

  (* Now we have indep_no_cnt if we have both of these properties *)
  Lemma indep_no_cnt_of_replace {A} (P: Pred Sm) (c: program Sm A) (nms: list Nm)
    (INDEPP: indep_store_replace P nms) (INDEPc: indep_cmd_partial_store c nms)
    : indep_no_cnt P c.
  Proof using Type.
    move=> s1 v s1' s EQc Ps1.
    apply: (INDEPP (set_store_no_cnt s s1) (set_store_no_cnt s s1') Ps1);
      autorewrite with seplog => //.
    by move=> nm w INnm; exact: (INDEPc s1 v s1' EQc nm w INnm).
  Qed.

  Lemma indep_no_cnt_ret {A} (P: Pred Sm) (x: A): indep_no_cnt P (ret x).
  Proof using Type.
    by apply: indep_no_cnt_of_store_eq; move=> s v s'; rewrite /ret => -[_ ->].
  Qed.

  Lemma indep_no_cnt_fail {A} (P: Pred Sm): indep_no_cnt P (fail (A:=A)).
  Proof using Type.
    by move=> s1 v s1' s; rewrite /fail.
  Qed.

  Lemma indep_no_cnt_loop {A} (P: Pred Sm): indep_no_cnt P (loop (A:=A)).
  Proof using Type.
    by move=> s1 v s1' s; rewrite /loop.
  Qed.

  Lemma indep_no_cnt_bind {A B} (P: Pred Sm) (c: program Sm A) (g: A -> program Sm B)
    (INDEPc: indep_no_cnt P c) (INDEPg: forall x, indep_no_cnt P (g x))
    : indep_no_cnt P (bind c g).
  Proof using Type.
    move=> s1 v s1' s EQcg Ps1.
    rewrite /bind in EQcg.
    move: EQcg; case EQc: (c s1) => [ [ [ x s2 ] | ] | ] // EQg.
    exact: (INDEPg x s2 v s1' s EQg (INDEPc s1 x s2 s EQc Ps1)).
  Qed.

  Lemma indep_no_cnt_If {A} (P: Pred Sm)
    (c_if: program Sm bool) (c_then c_else: program Sm A)
    (INDEPif: indep_no_cnt P c_if)
    (INDEPthen: indep_no_cnt P c_then)
    (INDEPelse: indep_no_cnt P c_else)
    : indep_no_cnt P (If c_if then c_then else c_else).
  Proof using Type.
    apply: indep_no_cnt_bind; first exact: INDEPif.
    by case.
  Qed.

  Lemma indep_no_cnt_while_fuel (P: Pred Sm) (fuel: nat)
    (cond: program Sm bool) (body: program Sm unit)
    (INDEPcond: indep_no_cnt P cond) (INDEPbody: indep_no_cnt P body)
    : indep_no_cnt P (while_fuel fuel cond body).
  Proof using Type.
    elim: fuel => [ | n IHn]; first exact: indep_no_cnt_loop.
    rewrite while_fuel_fixpoint.
    apply: indep_no_cnt_If.
    - exact: INDEPcond.
    - apply: indep_no_cnt_bind; [ exact: INDEPbody | by move=> x ].
    - exact: indep_no_cnt_ret.
  Qed.

  Lemma indep_no_cnt_While (P: Pred Sm)
    (cond: program Sm bool) (body: program Sm unit)
    (INDEPcond: indep_no_cnt P cond) (INDEPbody: indep_no_cnt P body)
    : indep_no_cnt P (while cond body).
  Proof using Type.
    move=> s1 v s1' s EQw Ps1.
    case/while_fuel_while_some: EQw => fuel EQfuel.
    exact: (indep_no_cnt_while_fuel P fuel cond body INDEPcond INDEPbody
             s1 v s1' s EQfuel Ps1).
  Qed.

  Lemma indep_no_cnt_with_var {A} {So: Storable.type Vl} (P: Pred Sm) (e: So)
    (p: Nm -> program Sm A) (nms: list Nm)
    (INDEPP: indep_store_replace P nms)
    (PRES: forall n, stack_discipline (p n))
    (INDEP: forall n, indep_cmd_partial_store (p n) nms)
    : indep_no_cnt P (with_var e p).
  Proof using Type.
    apply: (indep_no_cnt_of_replace P (with_var e p) nms INDEPP).
    exact: (indep_cmd_partial_store_with_var e p nms PRES INDEP).
  Qed.

  Lemma indep_no_cnt_read_var {So: Storable.type Vl} (P: Pred Sm) (n: Nm):
    indep_no_cnt P (read_var (So:=So) n).
  Proof using Type.
    apply: indep_no_cnt_of_store_eq => s v s'.
    rewrite /read_var /bind /get /ret /fail.
    case: (lookup (store s) n) => [ mv | ] //.
    case: (decode mv) => [ x | ] //.
    by move=> -[_ ->].
  Qed.

  Lemma indep_no_cnt_read_ptr {So: Storable.type Vl} (P: Pred Sm) (p: Pt):
    indep_no_cnt P (read_ptr (So:=So) p).
  Proof using Type.
    apply: indep_no_cnt_of_store_eq => s v s'.
    rewrite /read_ptr /bind /get /ret /fail.
    case: (lookup (heap s) p) => [ mv | ] //.
    case: (decode mv) => [ x | ] //.
    by move=> -[_ ->].
  Qed.

  Lemma indep_no_cnt_write_ptr {So: Storable.type Vl} (P: Pred Sm) (p: Pt) (val: So):
    indep_no_cnt P (write_ptr p val).
  Proof using Type.
    apply: indep_no_cnt_of_store_eq => s v s' EQc.
    case MUT: (mutate (heap s) p (encode val)) => [ h | ].
    - have DOM: dominates h (alc s)
        := dominates_mutate (heap s) h p (encode val) (alc s) MUT (state_heap_dominates s).
      rewrite (write_ptr_some p val s
                 (mk_state (store s) (scnt s) h (alc s)
                    (state_store_dominates s) DOM) h
                 MUT (store_mk_state _ _ _ _ _ _) (scnt_mk_state _ _ _ _ _ _)
                 (heap_mk_state _ _ _ _ _ _) (alc_mk_state _ _ _ _ _ _)) in EQc.
      move: EQc => [_ <-].
      exact: (store_mk_state _ _ _ _ _ _).
    - by rewrite (write_ptr_none p val s MUT) in EQc.
  Qed.

  Lemma indep_no_cnt_alloc_ptr {So: Storable.type Vl} (P: Pred Sm) (n: N.t) (val: So):
    indep_no_cnt P (alloc_ptr n val).
  Proof using Type.
    apply: indep_no_cnt_of_store_eq => s v s' EQc; move: EQc.
    rewrite /alloc_ptr.
    case: (N.leb n alloc_max_size) => //.
    rewrite /bind /get /put /ret /fail.
    case: (alloc (heap s) (alc s) n (encode val)) => [ [ [ hp c ] q ] | ] //.
    case MK: (mk_state_opt (store s) (scnt s) hp c) => [ s1 | ] //.
    case: (proj1 (mk_state_opt_some (store s) (scnt s) hp c s1) MK) => EQst1 _.
    by move=> [] _ <-.
  Qed.

  Lemma indep_no_cnt_free_ptr (P: Pred Sm) (p: Pt): indep_no_cnt P (free_ptr p).
  Proof using Type.
    apply: indep_no_cnt_of_store_eq => s v s' EQc; move: EQc.
    rewrite /free_ptr /bind /get /put /ret /fail.
    case: (free (heap s) p) => [ h | ] //.
    case MK: (mk_state_opt (store s) (scnt s) h (alc s)) => [ s1 | ] //.
    case: (proj1 (mk_state_opt_some (store s) (scnt s) h (alc s) s1) MK) => EQst1 _.
    by move=> [] _ <-.
  Qed.

  Lemma indep_no_cnt_shift_fw_ptr (P: Pred Sm) (p: Pt) (sh: N.t):
    indep_no_cnt P (shift_fw_ptr p sh).
  Proof using Type.
    apply: indep_no_cnt_of_store_eq => s v s'.
    rewrite /shift_fw_ptr /bind /get /ret /fail.
    case: (weakly_valid (heap s) p) => //.
    case: (ptr_shift_fw p sh) => [ q | ] //.
    case: (weakly_valid (heap s) q) => //.
    by move=> -[_ ->].
  Qed.

  Lemma indep_no_cnt_shift_bw_ptr (P: Pred Sm) (p: Pt) (sh: N.t):
    indep_no_cnt P (shift_bw_ptr p sh).
  Proof using Type.
    apply: indep_no_cnt_of_store_eq => s v s'.
    rewrite /shift_bw_ptr /bind /get /ret /fail.
    case: (weakly_valid (heap s) p) => //.
    case: (ptr_shift_bw p sh) => [ q | ] //.
    case: (weakly_valid (heap s) q) => //.
    by move=> -[_ ->].
  Qed.

  Lemma indep_no_cnt_eq_ptr (P: Pred Sm) (p_l p_r: Pt):
    indep_no_cnt P (eq_ptr p_l p_r).
  Proof using Type.
    apply: indep_no_cnt_of_store_eq => s v s'.
    rewrite /eq_ptr /bind /get /ret /fail.
    case: (cmp_valid (heap s) p_l p_r) => //.
    case: (cmp p_l p_r) => [b| ] //.
    by move=> -[_ ->].
  Qed.

  Lemma indep_no_cnt_div [UInt: Unsigned.Unsigned] (P: Pred Sm) (l r: UInt):
    indep_no_cnt P (Unsigned.div (S:=Sm) l r).
  Proof using Type.
    rewrite /Unsigned.div.
    case: ifP => _; [ exact: indep_no_cnt_fail | exact: indep_no_cnt_ret ].
  Qed.

  Lemma indep_no_cnt_mdl [UInt: Unsigned.Unsigned] (P: Pred Sm) (l r: UInt):
    indep_no_cnt P (Unsigned.mdl (S:=Sm) l r).
  Proof using Type.
    rewrite /Unsigned.mdl.
    case: ifP => _; [ exact: indep_no_cnt_fail | exact: indep_no_cnt_ret ].
  Qed.

End Frame.

Arguments action_local_strong_fail {Sm} {A}.
Arguments action_local_strong_loop {Sm} {A}.

(** Automatically infers [action_local_strong] and related properties for GallinaC primitives *)
#[global] Hint Resolve action_local_of_strong stack_discipline_of_action_local_strong
  action_local_strong_ret action_local_strong_fail action_local_strong_loop
  action_local_strong_If action_local_strong_While action_local_strong_while_fuel
  action_local_strong_with_var action_local_strong_read_var action_local_strong_write_var
  action_local_strong_read_ptr action_local_strong_write_ptr action_local_strong_alloc_ptr
  action_local_strong_free_ptr action_local_strong_shift_fw_ptr action_local_strong_shift_bw_ptr
  action_local_strong_eq_ptr action_local_strong_bind
  action_local_strong_div action_local_strong_mdl : seplog_search.

(* The lemmas are registered in a secondary Hint database. It's called internally whenever the goal is of the correct shape *)
#[global] Hint Extern 1 (action_local _) => seplog_search_auto : seplog.
#[global] Hint Extern 1 (action_local_strong _) => seplog_search_auto : seplog.
#[global] Hint Extern 1 (stack_discipline _) => seplog_search_auto : seplog.

#[global] Hint Resolve indep_cmd_partial_store_nil indep_cmd_partial_store_of_store_eq
  indep_cmd_partial_store_write_var : seplog_search.
#[global] Hint Resolve indep_cmd_partial_store_bind indep_cmd_partial_store_with_var : seplog_search.

#[global] Hint Resolve indep_no_cnt_ret indep_no_cnt_fail indep_no_cnt_loop indep_no_cnt_If
  indep_no_cnt_while_fuel indep_no_cnt_While indep_no_cnt_read_var indep_no_cnt_read_ptr
  indep_no_cnt_write_ptr indep_no_cnt_alloc_ptr indep_no_cnt_free_ptr
  indep_no_cnt_shift_fw_ptr indep_no_cnt_shift_bw_ptr indep_no_cnt_eq_ptr
  indep_no_cnt_bind indep_no_cnt_with_var
  : seplog_search.
#[global] Hint Resolve indep_no_cnt_of_replace | 5 : seplog_search.

#[global] Hint Extern 1 (indep_no_cnt _ _) => seplog_search_auto : seplog.
#[global] Hint Resolve indep_no_cnt_div indep_no_cnt_mdl : seplog_search.

Section Preserves.

  Context [S: Type].

  Definition preserves [A: Type] (R: Pred S) (c: program S A): Prop :=
    forall s v s', R s -> c s = Some (Success (v, s')) -> R s'.

  Lemma preserves_of_state_eq [A: Type] (R: Pred S) (c: program S A)
    (EQs': forall s v s', c s = Some (Success (v, s')) -> s' = s)
    : preserves R c.
  Proof using Type.
    by move=> s v s' Rs EQc; rewrite (EQs' s v s' EQc).
  Qed.

  Lemma preserves_ret [A: Type] (R: Pred S) (x: A): preserves R (ret x).
  Proof using Type.
    by move=> s v s' Rs; rewrite /ret => -[_ <-].
  Qed.

  Lemma preserves_fail [A: Type] (R: Pred S): preserves R (@fail S A).
  Proof using Type.
    by move=> s v s' _; rewrite /fail.
  Qed.

  Lemma preserves_loop [A: Type] (R: Pred S): preserves R (@loop S A).
  Proof using Type.
    by move=> s v s' _; rewrite /loop.
  Qed.

  Lemma preserves_bind [A B: Type] (R: Pred S) (c: program S A) (g: A -> program S B)
    (PRESc: preserves R c) (PRESg: forall x, preserves R (g x))
    : preserves R (bind c g).
  Proof using Type.
    move=> s v s' Rs EQcg.
    rewrite /bind in EQcg.
    move: EQcg; case EQc: (c s) => [ [ [ x s1 ] | ] | ] // EQg.
    exact: (PRESg x s1 v s' (PRESc s x s1 Rs EQc) EQg).
  Qed.

  Lemma preserves_If [A: Type] (R: Pred S)
    (c_if: program S bool) (c_then c_else: program S A)
    (PRESif: preserves R c_if) (PRESthen: preserves R c_then) (PRESelse: preserves R c_else)
    : preserves R (If c_if then c_then else c_else).
  Proof using Type.
    apply: preserves_bind; first exact: PRESif.
    by case.
  Qed.

  Lemma preserves_while_fuel (R: Pred S) (fuel: nat)
    (cond: program S bool) (body: program S unit)
    (PREScond: preserves R cond) (PRESbody: preserves R body)
    : preserves R (while_fuel fuel cond body).
  Proof using Type.
    elim: fuel => [ | n IHn]; first exact: preserves_loop.
    rewrite while_fuel_fixpoint.
    apply: preserves_If.
    - exact: PREScond.
    - apply: preserves_bind; [ exact: PRESbody | by move=> x ].
    - exact: preserves_ret.
  Qed.

  Lemma preserves_While (R: Pred S)
    (cond: program S bool) (body: program S unit)
    (PREScond: preserves R cond) (PRESbody: preserves R body)
    : preserves R (while cond body).
  Proof using Type.
    move=> s v s' Rs EQw.
    case/while_fuel_while_some: EQw => fuel EQfuel.
    exact: (preserves_while_fuel R fuel cond body PREScond PRESbody s v s' Rs EQfuel).
  Qed.

End Preserves.

#[global] Hint Resolve preserves_ret preserves_fail preserves_loop preserves_bind
  preserves_If preserves_while_fuel preserves_While : seplog_search.
#[global] Hint Extern 1 (preserves _ _) => seplog_search_auto : seplog.

Section PreservesState.

  Context [Sm: State.type].
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).

  Lemma with_var_push_replace (R: Pred Sm) (nms: list Nm)
    (INDEP: indep_store_replace R nms)
    (CNTN: forall s t, R s -> store t = store s -> scnt t = cnext (scnt s) ->
                       heap t = heap s -> alc t = alc s -> R t)
    (FRESH: forall s nm bid, R s -> List.In nm nms -> cget (scnt s) = Some bid ->
                             ~ References nm (mkAddr bid 0%N))
    (s: Sm) (v: Vl) (st1: St) (sg1: SCnt Sm) (n: Nm)
    (Rs: R s) (PUSH: push (store s) (scnt s) v = Some (st1, sg1, n))
    (D1: dominates st1 sg1)
    : R (mk_state st1 sg1 (heap s) (alc s) D1 (state_heap_dominates s)).
  Proof using Type.
    case: (proj2 (push_some (store s) (scnt s) v)
             (ex_intro _ st1 (ex_intro _ sg1 (ex_intro _ n PUSH))))
      => bid [GET _].
    case: (push_mem (store s) (scnt s) v st1 sg1 n bid PUSH GET) => REF [ALW SUM1].
    have Dt: dominates (store s) sg1
      := dominates_sub_mem st1 (store s) sg1 (substate_of_partition_r SUM1) D1.
    pose s' := mk_state (store s) sg1 (heap s) (alc s) Dt (state_heap_dominates s).
    have EQst': store s' = store s := store_mk_state _ _ _ _ _ _.
    have EQsg': scnt s' = sg1 := scnt_mk_state _ _ _ _ _ _.
    have EQhp': heap s' = heap s := heap_mk_state _ _ _ _ _ _.
    have EQalc': alc s' = alc s := alc_mk_state _ _ _ _ _ _.
    have Rs': R s'.
    { apply: (CNTN s s' Rs EQst' _ EQhp' EQalc').
      by rewrite EQsg'; exact: (push_cnt _ _ _ _ _ _ PUSH). }
    apply: (INDEP s' _ Rs').
    - rewrite EQst' store_mk_state => nm w INnm; split.
      + move=> [a [REFa SUBa] ]; exists a; split; first exact: REFa.
        exact: (substate_tran _ _ _ SUBa (substate_of_partition_r SUM1)).
      + move=> [a [REFa SUBa] ].
        case: (proj1 (one_discriminate_iff SUM1 a w) SUBa) => [ [EQa _] | [_ SUBs] ].
        * by case: (FRESH s nm bid Rs INnm GET); rewrite -EQa.
        * by exists a.
    - by rewrite scnt_mk_state EQsg'.
    - by rewrite heap_mk_state EQhp'.
    - by rewrite alc_mk_state EQalc'.
  Qed.

  Lemma preserves_with_var_replace_core [A: Type] {So: Storable.type Vl}
    (R: Pred Sm) (e: So) (p: Nm -> program Sm A) (nms: list Nm)
    (INDEP: indep_store_replace R nms)
    (CNTN: forall s t, R s -> store t = store s -> scnt t = cnext (scnt s) ->
                       heap t = heap s -> alc t = alc s -> R t)
    (FRESH: forall s nm bid, R s -> List.In nm nms -> cget (scnt s) = Some bid ->
                             ~ References nm (mkAddr bid 0%N))
    (STACK: forall n, stack_discipline (p n))
    (PRES: forall n, preserves R (p n))
    : preserves R (with_var e p).
  Proof using Type.
    move=> s v s' Rs.
    case PUSH: (push (store s) (scnt s) (encode e)) => [ [ [st1 sg1] n ] | ].
    2: { by rewrite /with_var /bind /get /ret /fail PUSH => -[]. }
    case: (proj2 (push_some (store s) (scnt s) (encode e))
             (ex_intro _ st1 (ex_intro _ sg1 (ex_intro _ n PUSH))))
      => bid [GET _].
    case: (push_mem (store s) (scnt s) (encode e) st1 sg1 n bid PUSH GET)
      => REF [ALW SUM1].
    have D1: dominates st1 sg1
      := dominates_push _ _ _ _ _ _ PUSH (state_store_dominates s).
    pose s1 := mk_state st1 sg1 (heap s) (alc s) D1 (state_heap_dominates s).
    have EQst1: store s1 = st1 := store_mk_state _ _ _ _ _ _.
    have EQsg1: scnt s1 = sg1 := scnt_mk_state _ _ _ _ _ _.
    have EQhp1: heap s1 = heap s := heap_mk_state _ _ _ _ _ _.
    have EQalc1: alc s1 = alc s := alc_mk_state _ _ _ _ _ _.
    have Rs1: R s1
      := with_var_push_replace R nms INDEP CNTN FRESH s (encode e) st1 sg1 n Rs PUSH D1.
    rewrite (with_var_eval_push e p s st1 sg1 n s1 PUSH EQst1 EQsg1 EQhp1 EQalc1).
    case CONT: (p n s1) => [ [ [v0 s2] | ] | ].
    2: { by move=> EQc; discriminate EQc. }
    2: { by move=> EQc; discriminate EQc. }
    have Rs2: R s2 := PRES n s1 v0 s2 Rs1 CONT.
    case: (with_var_core e p s st1 sg1 n bid GET PUSH D1 v0 s2 CONT (STACK n))
      => st' [bl [bi [POP1 [SUMt [NE [BLK [LT LEnm] ] ] ] ] ] ].
    rewrite POP1.
    case MK: (mk_state_opt st' (scnt s2) (heap s2) (alc s2)) => [ s3 | ]; last by [].
    move=> -[] _ <-.
    case: (proj1 (mk_state_opt_some st' (scnt s2) (heap s2) (alc s2) s3) MK)
      => EQst3 [EQsg3 [EQhp3 EQalc3] ].
    apply: (INDEP s2 s3 Rs2 _ EQsg3 EQhp3 EQalc3).
    rewrite EQst3 => nm w INnm; split.
    - move=> [a [REFa SUBa] ].
      case: (proj1 (sub_sum_split_iff st' bl (store s2) SUMt a w) SUBa) => [SUBst' | SUBbl].
      + by exists a.
      + exfalso.
        have Ba := BLK _ _ SUBbl.
        case: (domain_equal_bw _ _ (STACK n s1 v0 s2 CONT) a w SUBa) => w' SUBw'.
        move: EQst1 SUBw' => -> SUBw'.
        case: (proj1 (one_discriminate_iff SUM1 a w') SUBw') => [ [EQa _] | [_ SUBs] ].
        * by apply: (FRESH s nm bid Rs INnm GET); rewrite -EQa.
        * have := state_store_dominates s a w' bid SUBs GET.
          lia.
    - move=> [a [REFa SUBa] ]; exists a; split; first exact: REFa.
      exact: (substate_tran _ _ _ SUBa (substate_of_partition_l SUMt)).
  Qed.

  Lemma preserves_with_var_replace [A: Type] {So: Storable.type Vl}
    (R: Pred Sm) (e: So) (p: Nm -> program Sm A) (nms: list Nm)
    (INDEP: indep_store_replace R nms) (CNT: indep_cnt R)
    (ALLOC: forall s, R s -> forall nm, List.In nm nms -> exists w, nm |~> w @ store s)
    (STACK: forall n, stack_discipline (p n))
    (PRES: forall n, preserves R (p n))
    : preserves R (with_var e p).
  Proof using Type.
    apply: (preserves_with_var_replace_core R e p nms INDEP _ _ STACK PRES).
    - move=> s s' Rs EQst' _ EQhp' EQalc'.
      exact: (CNT s s' (eq_sym EQst') (eq_sym EQhp') (eq_sym EQalc') Rs).
    - move=> s nm bid Rs INnm GET REFnm.
      case: (ALLOC s Rs nm INnm) => w [a' [REFa' SUBa'] ].
      have EQa': a' = mkAddr bid 0%N by congruence.
      move: EQa' SUBa' => -> SUBa'.
      have := state_store_dominates s _ w bid SUBa' GET.
      rewrite mkAddr_block; lia.
  Qed.

  Lemma preserves_with_var [A: Type] {So: Storable.type Vl}
    (R: Pred Sm) (e: So) (p: Nm -> program Sm A)
    (INDEP: indep_store R) (PRES: forall n, preserves R (p n))
    : preserves R (with_var e p).
  Proof using Type.
    move=> s v s' Rs.
    case PUSH: (push (store s) (scnt s) (encode e)) => [ [ [st1 sg1] n ] | ].
    2: { by rewrite /with_var /bind /get /ret /fail PUSH => -[]. }
    have D1: dominates st1 sg1
      := dominates_push _ _ _ _ _ _ PUSH (state_store_dominates s).
    pose s1 := mk_state st1 sg1 (heap s) (alc s) D1 (state_heap_dominates s).
    have EQst1: store s1 = st1 := store_mk_state _ _ _ _ _ _.
    have EQsg1: scnt s1 = sg1 := scnt_mk_state _ _ _ _ _ _.
    have EQhp1: heap s1 = heap s := heap_mk_state _ _ _ _ _ _.
    have EQalc1: alc s1 = alc s := alc_mk_state _ _ _ _ _ _.
    have Rs1: R s1 := INDEP s s1 (eq_sym EQhp1) (eq_sym EQalc1) Rs.
    rewrite (with_var_eval_push e p s st1 sg1 n s1 PUSH EQst1 EQsg1 EQhp1 EQalc1).
    case CONT: (p n s1) => [ [ [v0 s2] | ] | ].
    2: { by move=> EQc; discriminate EQc. }
    2: { by move=> EQc; discriminate EQc. }
    have Rs2: R s2 := PRES n s1 v0 s2 Rs1 CONT.
    case: (pop (store s2)) => [ st' | ]; last by [].
    case MK: (mk_state_opt st' (scnt s2) (heap s2) (alc s2)) => [ s3 | ]; last by [].
    move=> -[] _ <-.
    case: (proj1 (mk_state_opt_some st' (scnt s2) (heap s2) (alc s2) s3) MK)
      => _ [_ [EQhp3 EQalc3] ].
    exact: (INDEP s2 s3 (eq_sym EQhp3) (eq_sym EQalc3) Rs2).
  Qed.

  Lemma preserves_read_var {So: Storable.type Vl} (R: Pred Sm) (n: Nm):
    preserves R (read_var (So:=So) n).
  Proof using Type.
    apply: preserves_of_state_eq => s v s'.
    rewrite /read_var /bind /get /ret /fail.
    case: (lookup (store s) n) => [ mv | ] //.
    case: (decode mv) => [ x | ] //.
    by move=> -[_ ->].
  Qed.

  Lemma preserves_write_var_replace {So: Storable.type Vl} (R: Pred Sm) (n: Nm) (val: So)
    (nms: list Nm) (INDEP: indep_store_replace R nms)
    (SEP: forall (m: Nm) (a b: Ad), List.In m nms -> References n a -> References m b -> b <> a)
    : preserves R (write_var n val).
  Proof using Type.
    move=> s u s' Rs EQc.
    have SPE := indep_cmd_partial_store_write_var n val nms SEP s u s' EQc.
    have [EQsg' [EQhp' EQalc'] ]: scnt s' = scnt s /\ heap s' = heap s /\ alc s' = alc s.
    { move: EQc; rewrite /write_var /bind /get /put /fail.
      case: (mutate (store s) n (encode val)) => [ st | ] //.
      case MK: (mk_state_opt st (scnt s) (heap s) (alc s)) => [ s1 | ] //.
      move=> -[_ <-].
      by case: (proj1 (mk_state_opt_some st (scnt s) (heap s) (alc s) s1) MK) => _. }
    exact: (INDEP s s' Rs SPE EQsg' EQhp' EQalc').
  Qed.

  Lemma preserves_write_var {So: Storable.type Vl} (R: Pred Sm) (n: Nm) (val: So)
    (INDEP: indep_store R)
    : preserves R (write_var n val).
  Proof using Type.
    apply: (preserves_write_var_replace R n val [] (indep_store_replace_of_indep_store R INDEP)).
    by move=> m a b [].
  Qed.

  Lemma preserves_read_ptr {So: Storable.type Vl} (R: Pred Sm) (p: Pt):
    preserves R (read_ptr (So:=So) p).
  Proof using Type.
    apply: preserves_of_state_eq => s v s'.
    rewrite /read_ptr /bind /get /ret /fail.
    case: (lookup (heap s) p) => [ mv | ] //.
    case: (decode mv) => [ x | ] //.
    by move=> -[_ ->].
  Qed.

  Lemma preserves_write_ptr {So: Storable.type Vl} (R: Pred Sm) (p: Pt) (val: So)
    (INDEP: indep_heap R)
    : preserves R (write_ptr p val).
  Proof using Type.
    move=> s u s' Rs EQc.
    have [EQst' EQsg']: store s' = store s /\ scnt s' = scnt s.
    { move: EQc; rewrite /write_ptr /bind /get /put /fail.
      case: (mutate (heap s) p (encode val)) => [ h | ] //.
      case MK: (mk_state_opt (store s) (scnt s) h (alc s)) => [ s1 | ] //.
      move=> -[_ <-].
      by case: (proj1 (mk_state_opt_some (store s) (scnt s) h (alc s) s1) MK) => EQst1 [EQsg1 _]. }
    exact: (INDEP s s' (eq_sym EQst') (eq_sym EQsg') Rs).
  Qed.

  Lemma preserves_alloc_ptr {So: Storable.type Vl} (R: Pred Sm) (n: N.t) (val: So)
    (INDEP: indep_heap R)
    : preserves R (alloc_ptr n val).
  Proof using Type.
    move=> s q s' Rs EQc.
    have [EQst' EQsg']: store s' = store s /\ scnt s' = scnt s.
    { move: EQc; rewrite /alloc_ptr.
      case: (N.leb n alloc_max_size) => //.
      rewrite /bind /get /put /ret /fail.
      case: (alloc (heap s) (alc s) n (encode val)) => [ [ [ hp c ] q' ] | ] //.
      case MK: (mk_state_opt (store s) (scnt s) hp c) => [ s1 | ] //.
      move=> -[_ <-].
      by case: (proj1 (mk_state_opt_some (store s) (scnt s) hp c s1) MK) => EQst1 [EQsg1 _]. }
    exact: (INDEP s s' (eq_sym EQst') (eq_sym EQsg') Rs).
  Qed.

  Lemma preserves_free_ptr (R: Pred Sm) (p: Pt) (INDEP: indep_heap R):
    preserves R (free_ptr p).
  Proof using Type.
    move=> s u s' Rs EQc.
    have [EQst' EQsg']: store s' = store s /\ scnt s' = scnt s.
    { move: EQc; rewrite /free_ptr /bind /get /put /fail.
      case: (free (heap s) p) => [ h | ] //.
      case MK: (mk_state_opt (store s) (scnt s) h (alc s)) => [ s1 | ] //.
      move=> -[_ <-].
      by case: (proj1 (mk_state_opt_some (store s) (scnt s) h (alc s) s1) MK) => EQst1 [EQsg1 _]. }
    exact: (INDEP s s' (eq_sym EQst') (eq_sym EQsg') Rs).
  Qed.

  Lemma preserves_shift_fw_ptr (R: Pred Sm) (p: Pt) (sh: N.t):
    preserves R (shift_fw_ptr p sh).
  Proof using Type.
    apply: preserves_of_state_eq => s v s'.
    rewrite /shift_fw_ptr /bind /get /ret /fail.
    case: (weakly_valid (heap s) p) => //.
    case: (ptr_shift_fw p sh) => [ q | ] //.
    case: (weakly_valid (heap s) q) => //.
    by move=> -[_ ->].
  Qed.

  Lemma preserves_shift_bw_ptr (R: Pred Sm) (p: Pt) (sh: N.t):
    preserves R (shift_bw_ptr p sh).
  Proof using Type.
    apply: preserves_of_state_eq => s v s'.
    rewrite /shift_bw_ptr /bind /get /ret /fail.
    case: (weakly_valid (heap s) p) => //.
    case: (ptr_shift_bw p sh) => [ q | ] //.
    case: (weakly_valid (heap s) q) => //.
    by move=> -[_ ->].
  Qed.

  Lemma preserves_eq_ptr (R: Pred Sm) (p_l p_r: Pt):
    preserves R (eq_ptr p_l p_r).
  Proof using Type.
    apply: preserves_of_state_eq => s v s'.
    rewrite /eq_ptr /bind /get /ret /fail.
    case: (cmp_valid (heap s) p_l p_r) => //.
    case: (cmp p_l p_r) => [b| ] //.
    by move=> -[_ ->].
  Qed.

End PreservesState.

#[global] Hint Resolve preserves_read_var preserves_read_ptr preserves_shift_fw_ptr
  preserves_shift_bw_ptr preserves_eq_ptr preserves_write_var preserves_write_ptr
  preserves_alloc_ptr preserves_free_ptr preserves_with_var : seplog_search.

Section PreservesArith.

  Context [S: Type].

  Lemma preserves_div [UInt: Unsigned.Unsigned] (R: Pred S) (l r: UInt):
    preserves R (Unsigned.div (S:=S) l r).
  Proof using Type.
    rewrite /Unsigned.div.
    case: ifP => _; [ exact: preserves_fail | exact: preserves_ret ].
  Qed.

  Lemma preserves_mdl [UInt: Unsigned.Unsigned] (R: Pred S) (l r: UInt):
    preserves R (Unsigned.mdl (S:=S) l r).
  Proof using Type.
    rewrite /Unsigned.mdl.
    case: ifP => _; [ exact: preserves_fail | exact: preserves_ret ].
  Qed.

End PreservesArith.

#[global] Hint Resolve preserves_div preserves_mdl : seplog_search.

Ltac frame_side_parts :=
  lazymatch goal with
  | |- _ /\ _ => split; frame_side_parts
  | |- _ => first [ solve [ auto with seplog ] | solve [ intros; reflexivity ] | idtac ]
  end.

Ltac frame_with close_triple :=
  first [ apply: frame_rule | apply: frame_rule_gen ];
  [ rewrite /frame_side /=; frame_side_parts | close_triple ].

Tactic Notation "frame" := frame_with ltac:(try eassumption).
Tactic Notation "frame" uconstr(H) := frame_with ltac:(exact H).
