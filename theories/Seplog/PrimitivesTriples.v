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

From Stdlib Require Import ZArith Lia.

From GallinaC.Utils Require Import ListExt.
From GallinaC.Imp Require Import Storable PrimitivesProp Store.
From GallinaC.Seplog.Inter Require Import Inter.
From GallinaC.Seplog.Exists Require Import Exists.
From GallinaC.Seplog.Forall Require Import Forall.
From GallinaC.Seplog Require Import Hoare.
From GallinaC.Seplog.Emp Require Import Emp.
From GallinaC.Seplog.Lift Require Import Lift.
From GallinaC.Seplog.Star Require Import Star Facts.
From GallinaC.Seplog.Upclose Require Import Upclose.
From GallinaC.Seplog.Wand Require Import Wand Facts.
From GallinaC.Seplog.IterStar Require Import IterStar.
From GallinaC.Seplog.State Require Import Atoms.
From GallinaC.Seplog Require Import Frame.
From GallinaC.Seplog.Inter Require Import Frame.
From GallinaC.Seplog.Star Require Import Frame.

Import Intops.IntCarrier Intops.Unsigned.

Local Open Scope program_scope.
Local Open Scope separation_scope.
Local Open Scope mem_scope.

Lemma ret_fw [S: Separation.type] [A: Type] [total: bool] [a: A] [P: Pred S]:
  hoare total P (ret a) (fun r => [| r = a |] ** P).
Proof.
  move=> s Ps.
  exists $0%sep, s.
  split; first exact: op_id_l.
  by split.
Qed.

Lemma ret_bw [S A: Type] [total: bool] [a: A] [P: A -> Pred S]:
  hoare total (P a) (ret a) P.
Proof.
  by move=> s PRE.
Qed.
#[global] Hint Resolve ret_bw: seplog.

Lemma bind_rule [S A B: Type] [total: bool] [m: program S A] [f: A -> program S B]
  [P: Pred S] [Q: A -> Pred S] [R: B -> Pred S]:
  (forall a, hoare total (Q a) (f a) R) -> hoare total P m Q ->
  hoare total P (do x <- m; f x) R.
Proof.
  move=> TRIPLEf TRIPLEm s PRE.
  rewrite /bind.
  case EQm: (m s) => [ [ [ a s1 ] | ] | ].
  - case EQf: (f a s1) => [ [ [ b s2 ] | ] | ];
      move: (TRIPLEm _ PRE);
      rewrite EQm => Qas1;
      move: (TRIPLEf _ _ Qas1);
      by rewrite EQf.
  - move: (TRIPLEm _ PRE).
    by rewrite EQm.
  - move: (TRIPLEm _ PRE).
    by rewrite EQm.
Qed.

Lemma seq_rule [S A B: Type] [total: bool] [m1: program S A] [m2: program S B]
  [P Q: Pred S] [R: B -> Pred S]:
  hoare total Q m2 R -> hoare total P m1 (fun _ => Q) -> hoare total P (m1;; m2) R.
Proof.
  move=> TRIPLE2 TRIPLE1.
  exact: (bind_rule (fun _ => TRIPLE2) TRIPLE1).
Qed.

Lemma if_rule [S A: Type] [total: bool] [cond: program S bool] [m1 m2: program S A]
  [P: Pred S] [Q: bool -> Pred S] [R: A -> Pred S]:
  hoare total P cond Q -> hoare total (Q true) m1 R -> hoare total (Q false) m2 R ->
  hoare total P (If cond then m1 else m2) R.
Proof.
  move=> TRIPLEc TRIPLE1 TRIPLE2.
  apply: bind_rule.
  - case.
    + exact: TRIPLE1.
    + exact: TRIPLE2.
  - exact: TRIPLEc.
Qed.
#[global] Hint Resolve if_rule: seplog.

Lemma while_fuel_rule [S: Type]
  [cond: program S bool] [body: program S unit]
  [E: Pred S] [I: bool -> Pred S]
  (COND: {{ E }} cond {{ I }})
  (BODY: {{ I true }} body {{ fun=> E }})
  : forall fuel, {{ E }} while_fuel fuel cond body {{ fun=> I false }}.
Proof.
  elim=> [ | fuel IH ];
    first by move=> s PRE.
  rewrite while_fuel_fixpoint.
  apply: if_rule.
  - exact: COND.
  - apply: seq_rule; [ exact: IH | exact: BODY ].
  - exact: ret_bw.
Qed.

Lemma while_fuel_bridge [S: Type]
  [cond: program S bool] [body: program S unit]
  [P: Pred S] [Q: unit -> Pred S]
  (n: nat)
  : [[ P ]] while_fuel n cond body [[ Q ]] -> [[ P ]] while cond body [[ Q ]].
Proof.
  move=> TRIPLE s PRE; move: (TRIPLE s PRE).
  case EQfuel: (while_fuel n cond body s) => [x| ] // POST.
  have ->: while cond body s = Some x by apply/while_fuel_while_some; exists n.
  exact: POST.
Qed.

Lemma while_fuel_indexed [S: Type]
  [cond: program S bool] [body: program S unit]
  [E: nat -> Pred S] [I: nat -> bool -> Pred S]
  (COND: forall k, [[ E k ]] cond [[ I k ]])
  (BODY: forall k, [[ I (Datatypes.S k) true ]] body [[ fun=> E k ]])
  (ZERO: forall s, ~ I 0 true s)
  : forall n, [[ E n ]] while_fuel (Datatypes.S n) cond body
                [[ fun=> Exists k, I k false ]].
Proof.
  elim=> [ |n IH] s PRE; rewrite while_fuel_fixpoint /bind.
  - move: (COND 0 s PRE).
    case: (cond s) => [ [ [b s1]| ]| ] //.
    case: b => Is1; [case: (ZERO s1 Is1) | by exists 0].
  - move: (COND (Datatypes.S n) s PRE).
    case: (cond s) => [ [ [b s1]| ]| ] //.
    case: b => Is1.
    + move: (BODY n s1 Is1).
      case: (body s1) => [ [ [ [] s2]| ]| ] // Ens2.
      exact: (IH s2 Ens2).
    + by exists (Datatypes.S n).
Qed.

Lemma while_rule [S: Type] [cond: program S bool] [body: program S unit]
  [E: Pred S] [I: bool -> Pred S]
  (COND: {{ E }} cond {{ I }})
  (BODY: {{ I true }} body {{ fun=> E }})
  : {{ E }} while cond body {{ fun=> I false }}.
Proof.
  move=> s PRE.
  case EQw: (while cond body s) => [ x | ] //.
  case/while_fuel_while_some: EQw => fuel EQfuel.
  move: (while_fuel_rule COND BODY fuel s PRE).
  by rewrite EQfuel.
Qed.

Lemma while_measure [S: Type]
  [cond: program S bool] [body: program S unit]
  [M: Type] [LT: M -> M -> Prop] [E: M -> Pred S] [I: M -> bool -> Pred S]
  (WF: well_founded LT)
  (COND: forall m, [[ E m ]] cond [[ I m ]])
  (BODY: forall m, [[ I m true ]] body [[ fun=> Exists m', Basics.const (LT m' m) && E m' ]])
  : [[ Exists m, E m ]] while cond body [[ fun=> Exists m, I m false ]].
Proof.
  move=> s [m PRE]; move: s PRE.
  elim/(well_founded_induction WF): m => m IH s PRE.
  rewrite while_fixpoint /bind.
  move: (COND m s PRE).
  case: (cond s) => [ [ [b s1]| ]| ] //.
  case: b => Ims1.
  - move: (BODY m s1 Ims1).
    case: (body s1) => [ [ [ [] s2]| ]| ] //.
    move=> [m' [LTm'm Em's2] ].
    exact: (IH m' LTm'm s2 Em's2).
  - by exists m.
Qed.

Section WhileTriples.

  Context [Sm: State.type].

  Lemma while_fuel_rule_bw [cond: program Sm bool] [body: program Sm unit]
    [E: Pred Sm] [I: bool -> Pred Sm] [Q: unit -> Pred Sm]
    (LOCALc: action_local_strong cond) (LOCALb: action_local_strong body)
    (COND: {{ E }} cond {{ I }})
    (BODY: {{ I true }} body {{ fun=> E }})
    : forall fuel, {{ E ** (I false -* Q tt) }} while_fuel fuel cond body {{ Q }}.
  Proof using Type.
    move=> fuel.
    have FR: {{ E ** (I false -* Q tt) }} while_fuel fuel cond body
               {{ fun=> I false ** (I false -* Q tt) }}.
    { frame (while_fuel_rule COND BODY fuel). }
    apply: (consequence _ FR); first by [].
    move=> [ ] s POST.
    exact: (star_wand_mp (I false) (Q tt) s POST).
  Qed.

  Lemma while_fuel_indexed_bw [cond: program Sm bool] [body: program Sm unit]
    [E: nat -> Pred Sm] [I: nat -> bool -> Pred Sm] [Q: unit -> Pred Sm]
    (LOCALc: action_local_strong cond) (LOCALb: action_local_strong body)
    (COND: forall k, [[ E k ]] cond [[ I k ]])
    (BODY: forall k, [[ I (Datatypes.S k) true ]] body [[ fun=> E k ]])
    (ZERO: forall s, ~ I 0 true s)
    : forall n, [[ E n ** ((Exists k, I k false) -* Q tt) ]] while_fuel (Datatypes.S n) cond body
                  [[ Q ]].
  Proof using Type.
    move=> n.
    have FR: [[ E n ** ((Exists k, I k false) -* Q tt) ]] while_fuel (Datatypes.S n) cond body
               [[ fun=> (Exists k, I k false) ** ((Exists k, I k false) -* Q tt) ]].
    { frame (while_fuel_indexed COND BODY ZERO n). }
    apply: (consequence _ FR); first by [].
    move=> [ ] s POST.
    exact: (star_wand_mp (Exists k, I k false) (Q tt) s POST).
  Qed.

  Lemma while_rule_bw [cond: program Sm bool] [body: program Sm unit]
    [E: Pred Sm] [I: bool -> Pred Sm] [Q: unit -> Pred Sm]
    (LOCALc: action_local_strong cond) (LOCALb: action_local_strong body)
    (COND: {{ E }} cond {{ I }})
    (BODY: {{ I true }} body {{ fun=> E }})
    : {{ E ** (I false -* Q tt) }} while cond body {{ Q }}.
  Proof using Type.
    have FR: {{ E ** (I false -* Q tt) }} while cond body
               {{ fun=> I false ** (I false -* Q tt) }}.
    { frame (while_rule COND BODY). }
    apply: (consequence _ FR); first by [].
    move=> [ ] s POST.
    exact: (star_wand_mp (I false) (Q tt) s POST).
  Qed.

  Lemma while_measure_bw [cond: program Sm bool] [body: program Sm unit]
    [M: Type] [LT: M -> M -> Prop] [E: M -> Pred Sm] [I: M -> bool -> Pred Sm] [Q: unit -> Pred Sm]
    (LOCALc: action_local_strong cond) (LOCALb: action_local_strong body)
    (WF: well_founded LT)
    (COND: forall m, [[ E m ]] cond [[ I m ]])
    (BODY: forall m, [[ I m true ]] body [[ fun=> Exists m', Basics.const (LT m' m) && E m' ]])
    : [[ (Exists m, E m) ** ((Exists m, I m false) -* Q tt) ]] while cond body [[ Q ]].
  Proof using Type.
    have FR: [[ (Exists m, E m) ** ((Exists m, I m false) -* Q tt) ]] while cond body
               [[ fun=> (Exists m, I m false) ** ((Exists m, I m false) -* Q tt) ]].
    { frame (while_measure WF COND BODY). }
    apply: (consequence _ FR); first by [].
    move=> [ ] s POST.
    exact: (star_wand_mp (Exists m, I m false) (Q tt) s POST).
  Qed.

End WhileTriples.

Section StoreTriples.

  Context [Sm: State.type].
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation St := (@m_st Sm).
  Local Notation Hp := (@m_hp Sm).

  #[local] Lemma with_var_pop [A: Type] (Q: A -> Pred Sm) (n: Nm) (bid: nat) (r: A) (s2: Sm)
    (REF: References n (mkAddr bid 0%N))
    (POST: (Q r ** (Exists w, var_pt n w)) s2)
    (LOW: forall (a: Ad) (v: Vl), (((a |-> v): St) $<= store s2) ->
                                  a <> mkAddr bid 0%N -> (block a < bid)%nat)
    : exists q, pop (store s2) = Some (store q)
                /\ mk_state_opt (store q) (scnt s2) (heap s2) (alc s2) = Some q
                /\ Q r q.
  Proof using Type.
    case: POST => sq [ vv [ EQs2 [ Qrsq [ w [ [ a [ REFa + ] ] [ EQsgvv [ EQhpvv EQalcvv ] ] ] ] ] ] ].
    have -> : a = mkAddr bid 0%N by congruence.
    move=> {REFa a} EQstvv.
    case/state_sum_spec: EQs2 => EQst2 [ EQsg2 [ EQhp2 EQalc2 ] ].
    move: EQstvv EQst2 => -> EQst2.
    move: EQsgvv EQsg2 => -> EQsg2.
    move: EQhpvv EQhp2 => -> EQhp2.
    move: EQalcvv EQalc2 => -> EQalc2.
    move/partition_emp_r: EQsg2 => EQsg2.
    move/partition_emp_r: EQhp2 => EQhp2.
    move/partition_emp_r: EQalc2 => EQalc2.
    exists sq; split; [ | split; [ | exact: Qrsq ] ].
    - apply: (pop_char (store s2) (store sq) ((mkAddr bid 0%N) |-> w) bid EQst2).
      + by exists (mkAddr bid 0%N), w; exact: substate_refl.
      + move=> a v SUB.
        case/sub_one_iff: SUB => -> _.
        exact: mkAddr_block.
      + move=> a v SUB.
        apply: (LOW a v (substate_tran _ _ _ SUB (substate_of_partition_l EQst2))).
        move: SUB => /[swap] -> SUB.
        exact: (absent_of_separate (store sq) ((mkAddr bid 0%N) |-> w) (mkAddr bid 0%N) v
                  (ex_intro _ (store s2) EQst2) SUB w (substate_refl _)).
    - rewrite -EQsg2 -EQhp2 -EQalc2.
      exact: mk_state_opt_self.
  Qed.

  Lemma with_var_fw_core [A: Type] {So: Storable.type Vl} [total: bool] [e: So]
    [p: Nm -> program Sm A] [c: SCnt Sm] [P: Pred Sm] [Q: A -> Pred Sm]
    (BUDGET: CBudget c 1)
    (LOWER: forall n bid s1 r s2, cget c = Some bid -> References n (mkAddr bid 0%N) ->
       (P ** var_pt n (encode e) ** own_scnt (cnext c)) s1 ->
       (forall (a: Ad) (v: Vl), (((a |-> v): St) $<= store s1) ->
                                a <> mkAddr bid 0%N -> (block a < bid)%nat) ->
       p n s1 = Some (Success (r, s2)) ->
       (Q r ** (Exists w, var_pt n w)) s2 ->
       forall (a: Ad) (v: Vl), (((a |-> v): St) $<= store s2) ->
                               a <> mkAddr bid 0%N -> (block a < bid)%nat)
    (BODY: forall n, Allows n Operation.Write ->
       hoare total (P ** var_pt n (encode e) ** own_scnt (cnext c)) (p n)
                   (fun r => Q r ** (Exists w, var_pt n w)))
    : hoare total (P ** own_scnt c) (with_var e p) Q.
  Proof using Type.
    move=> s [ sp [ sq [ EQs [ Psp [ EQstq [ EQsgq [ EQhpq EQalcq ] ] ] ] ] ] ].
    case: (cbudget_some c 0 BUDGET) => bid CGET.
    case/state_sum_spec: EQs => EQst [ EQsg [ EQhp EQalc ] ].
    move: EQstq EQst => -> EQst.
    move: EQsgq EQsg => -> EQsg.
    move: EQhpq EQhp => -> EQhp.
    move: EQalcq EQalc => -> EQalc.
    move/partition_emp_r: EQst => EQst.
    move/partition_emp_r: EQhp => EQhp.
    move/partition_emp_r: EQalc => EQalc.
    have EQsgp: scnt sp = $0.
    { case: (excl_sum_excl _ (scnt sp) c (scnt s) EQsg) => [ EQsgp | EQc ] //.
      by move: CGET; rewrite EQc cget_unowned. }
    have EQsg': scnt s = c.
    { move: EQsgp EQsg => -> EQsg.
      exact: (eq_sym (partition_emp_l EQsg)). }
    have CGETs: cget (scnt s) = Some bid by rewrite EQsg'.
    case: (push_of_cget s (encode e) bid CGETs) => st1 [ sg1 [ n PUSH ] ].
    case: (push_mem (store s) (scnt s) (encode e) st1 sg1 n bid PUSH CGETs) => REF [ ALW SUM1 ].
    have EQsg1': sg1 = cnext c by rewrite (push_cnt _ _ _ _ _ _ PUSH) EQsg'.
    have D1: dominates st1 sg1 := dominates_push _ _ _ _ _ _ PUSH (state_store_dominates s).
    pose s1 := mk_state st1 sg1 (heap s) (alc s) D1 (state_heap_dominates s).
    have EQst1: store s1 = st1 := store_mk_state _ _ _ _ _ _.
    have EQsg1: scnt s1 = sg1 := scnt_mk_state _ _ _ _ _ _.
    have EQhp1: heap s1 = heap s := heap_mk_state _ _ _ _ _ _.
    have EQalc1: alc s1 = alc s := alc_mk_state _ _ _ _ _ _.
    rewrite (with_var_eval_push e p s st1 sg1 n s1 PUSH EQst1 EQsg1 EQhp1 EQalc1).
    have PRE1: (P ** var_pt n (encode e) ** own_scnt (cnext c)) s1.
    { exists (mk_state st1 $0 (heap s) (alc s) (dominates_emp_cnt st1) (state_heap_dominates s)),
        (emp_with_alc (cnext c) $0).
      split.
      { apply: state_hp_ext_intro.
        - rewrite store_mk_state store_emp_with_alc EQst1.
          exact: op_id_r.
        - rewrite scnt_mk_state scnt_emp_with_alc EQsg1 EQsg1'.
          exact: op_id_l.
        - rewrite heap_mk_state heap_emp_with_alc EQhp1.
          exact: op_id_r.
        - rewrite alc_mk_state alc_emp_with_alc EQalc1.
          exact: op_id_r. }
      split; last first.
      { by rewrite /own_scnt store_emp_with_alc scnt_emp_with_alc heap_emp_with_alc
             alc_emp_with_alc. }
      exists sp, (mk_state ((mkAddr bid 0%N) |-> (encode e)) $0 $0 $0
                    (dominates_emp_cnt _) (dominates_emp _)).
      split.
      { apply: state_hp_ext_intro.
        - rewrite !store_mk_state EQst.
          exact: (partition_comm SUM1).
        - rewrite !scnt_mk_state EQsgp.
          exact: op_id_l.
        - rewrite !heap_mk_state EQhp.
          exact: op_id_r.
        - rewrite !alc_mk_state EQalc.
          exact: op_id_r. }
      split; first exact: Psp.
      split; first by exists (mkAddr bid 0%N); split; [ exact: REF | exact: store_mk_state ].
      by rewrite scnt_mk_state heap_mk_state alc_mk_state. }
    have LOW1: forall (a: Ad) (v: Vl), (((a |-> v): St) $<= store s1) ->
                                       a <> mkAddr bid 0%N -> (block a < bid)%nat.
    { move=> a v SUB NE.
      move: EQst1 SUB => -> SUB.
      case: (proj1 (one_discriminate_iff SUM1 a v) SUB) => [ [ EQa _ ] | [ _ SUBs ] ].
      - by case: (NE EQa).
      - exact: (state_store_dominates s a v bid SUBs CGETs). }
    move: (BODY n ALW s1 PRE1).
    case CONT: (p n s1) => [ [ [ r s2 ] | ] | ] //.
    move=> POST.
    have LOW := LOWER n bid s1 r s2 CGET REF PRE1 LOW1 CONT POST.
    case: (with_var_pop Q n bid r s2 REF POST LOW) => s3 [ POP [ MK Qrs3 ] ].
    by rewrite POP MK.
  Qed.

  Lemma with_var_fw_gen [A: Type] {So: Storable.type Vl} [total: bool] [e: So]
    [p: Nm -> program Sm A] [c: SCnt Sm] [P: Pred Sm] [Q: A -> Pred Sm]
    (BUDGET: CBudget c 1)
    (STACK: forall n, stack_discipline (p n))
    (BODY: forall n, Allows n Operation.Write ->
       hoare total (P ** var_pt n (encode e) ** own_scnt (cnext c)) (p n)
                   (fun r => Q r ** (Exists w, var_pt n w)))
    : hoare total (P ** own_scnt c) (with_var e p) Q.
  Proof using Type.
    apply: (with_var_fw_core BUDGET _ BODY).
    move=> n bid s1 r s2 _ _ _ LOW1 CONT _ a v2 SUB2 NE.
    case: (domain_equal_bw _ _ (STACK n s1 r s2 CONT) a v2 SUB2) => v1 SUB1.
    exact: (LOW1 a v1 SUB1 NE).
  Qed.

  Lemma with_var_fw [A: Type] {So: Storable.type Vl} [total: bool] [e: So] [p: Nm -> program Sm A]
    [c c': SCnt Sm] [P: Pred Sm] [Q: A -> Pred Sm]
    (BUDGET: CBudget c 1)
    (STACK: forall n, stack_discipline (p n))
    (BODY: forall n, Allows n Operation.Write ->
           hoare total (P ** var_pt n (encode e) ** own_scnt (cnext c)) (p n)
                       (fun r => Q r ** (Exists w, var_pt n w) ** own_scnt c'))
    : hoare total (P ** own_scnt c) (with_var e p) (fun r => Q r ** own_scnt c').
  Proof using Type.
    apply: (with_var_fw_gen BUDGET STACK).
    move=> n ALW.
    apply: (consequence _ (BODY n ALW)); first by [].
    move=> r s POST.
    rewrite star_assoc (star_comm (Exists w, var_pt n w)) -star_assoc in POST.
    exact: POST.
  Qed.

  Lemma with_var_bw [A: Type] {So: Storable.type Vl} [total: bool] [e: So] [p: Nm -> program Sm A]
    [c c': SCnt Sm] [P: Pred Sm] [Q R: A -> Pred Sm]
    (BUDGET: CBudget c 1)
    (LOCAL: forall n, action_local_strong (p n))
    (BODY: forall n, Allows n Operation.Write ->
           hoare total (P ** var_pt n (encode e) ** own_scnt (cnext c)) (p n)
                       (fun r => Q r ** (Exists w, var_pt n w) ** own_scnt c'))
    : hoare total ((P ** own_scnt c) ** (Forall r, (Q r ** own_scnt c') -* R r)) (with_var e p) R.
  Proof using Type.
    have FR: hoare total ((P ** own_scnt c) ** (Forall r, (Q r ** own_scnt c') -* R r)) (with_var e p)
               (fun r => (Q r ** own_scnt c') ** (Forall r, (Q r ** own_scnt c') -* R r)).
    { frame (with_var_fw BUDGET
               (fun n => stack_discipline_of_action_local_strong (p n) (LOCAL n)) BODY). }
    apply: (consequence _ FR); first by [].
    move=> r s [ s1 [ sw [ EQs [ POSTs1 WAND ] ] ] ].
    apply: (star_wand_mp (Q r ** own_scnt c') (R r)).
    exists s1, sw.
    split; first exact: EQs.
    split; first exact: POSTs1.
    exact: (WAND r).
  Qed.

  Lemma read_var_fw {So: Storable.type Vl} [n: Nm] [x: So] (ALW: Allows n Operation.Read):
    [[ var_pt n (encode x) ]] read_var n [[ fun r => [| r = x |] ** var_pt n (encode x) ]].
  Proof using Type.
    move=> s PRE.
    case: (PRE) => [ [ a [ REF EQst ] ] _ ].
    have LK: lookup (store s) n = Some (encode x).
    { apply/lookup_iff.
      exists a; split; first exact: REF.
      split; first exact: ALW.
      rewrite EQst.
      exact: substate_refl. }
    rewrite /read_var /bind /get.
    rewrite LK /=.
    rewrite encode_decode.
    exists $0%sep, s.
    split; first exact: op_id_l.
    by split.
  Qed.

  Lemma read_var_bw {So: Storable.type Vl} [n: Nm] [Q: So -> Pred Sm] (x: So)
    (ALW: Allows n Operation.Read):
    [[ var_pt n (encode x) ** (var_pt n (encode x) -* Q x) ]] read_var n [[ Q ]].
  Proof using Type.
    have FR: [[ var_pt n (encode x) ** (var_pt n (encode x) -* Q x) ]] read_var n
               [[ fun r => ([| r = x |] ** var_pt n (encode x)) ** (var_pt n (encode x) -* Q x) ]].
    { frame (read_var_fw ALW). }
    apply: (consequence _ FR); first by [].
    move=> r s [ s1 [ sw [ EQs [ [ ? [ s2 [ EQs1 [ [ -> EMP ] VAR ] ] ] ] WAND ] ] ] ].
    move: EMP EQs1 => -> EQs1.
    move/partition_emp_l: EQs1 VAR => -> VAR.
    apply: (star_wand_mp (var_pt n (encode x)) (Q x)).
    exists s1, sw.
    by split; [ exact: EQs | split ].
  Qed.

  Lemma read_var_lookup [total: bool] {So: Storable.type Vl} [n: Nm] [P: So -> Pred Sm]
    (ALW: Allows n Operation.Read):
    hoare total (Exists x, upclose (var_pt n (encode x)) && P x) (read_var n) P.
  Proof using Type.
    apply: exists_pre => x.
    have FW: hoare total (var_pt n (encode x)) (read_var n) (fun r => [| r = x |] ** var_pt n (encode x)).
    { case: total; [ exact: read_var_fw | exact: total_partial (read_var_fw ALW) ]. }
    have FR: hoare total ((var_pt n (encode x) ** top) && P x) (read_var n)
               (fun r => (([| r = x |] ** var_pt n (encode x)) ** top) && P x).
    { frame.
      frame FW. }
    apply: (consequence _ FR); first by [].
    move=> r s [ [ s1 [ s2 [ _ [ [ s3 [ s4 [ _ [ [ EQr _ ] _ ] ] ] ] _ ] ] ] ] Pxs ].
    by rewrite EQr.
  Qed.

  Lemma write_var_fw {So: Storable.type Vl} [n: Nm] [w: Vl] [x: So]
    (ALW: Allows n Operation.Write):
    [[ var_pt n w ]] write_var n x [[ fun=> var_pt n (encode x) ]].
  Proof using Type.
    move=> s [ [ a [ REF EQst ] ] [ EQsg [ EQhp EQalc ] ] ].
    have MUT: mutate (store s) n (encode x) = Some (one a (encode x)).
    { rewrite EQst.
      exact: (mutate_one REF ALW w (encode x)). }
    rewrite (write_var_some n x s (state_mutate_store s MUT) _ MUT
               (store_state_mutate_store s _ _ _ MUT) (scnt_state_mutate_store s _ _ _ MUT)
               (heap_state_mutate_store s _ _ _ MUT) (alc_state_mutate_store s _ _ _ MUT)).
    split; first by exists a; split; [ exact: REF | exact: store_state_mutate_store ].
    rewrite scnt_state_mutate_store heap_state_mutate_store alc_state_mutate_store.
    by split; [ | split ].
  Qed.

  Lemma write_var_bw {So: Storable.type Vl} [n: Nm] [x: So] [Q: unit -> Pred Sm] (w: Vl)
    (ALW: Allows n Operation.Write):
    [[ var_pt n w ** (var_pt n (encode x) -* Q tt) ]] write_var n x [[ Q ]].
  Proof using Type.
    have FR: [[ var_pt n w ** (var_pt n (encode x) -* Q tt) ]] write_var n x
               [[ fun=> var_pt n (encode x) ** (var_pt n (encode x) -* Q tt) ]].
    { frame (write_var_fw ALW). }
    apply: (consequence _ FR); first by [].
    move=> [ ] s POST.
    exact: (star_wand_mp (var_pt n (encode x)) (Q tt) s POST).
  Qed.

End StoreTriples.

Section HeapTriples.

  Context [Sm: State.type].
  Local Notation Ad := (@m_ad Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).

  Lemma read_ptr_fw {So: Storable.type Vl} [p: Pt] [a: Ad] [x: So]
    (REF: References p a) (ALW: Allows p Operation.Read):
    [[ a ||~> encode x ]] read_ptr p [[ fun r => [| r = x |] ** a ||~> encode x ]].
  Proof using Type.
    move=> s PRE.
    case: (PRE) => [ _ [ _ [ EQhp _ ] ] ].
    have LK: lookup (heap s) p = Some (encode x).
    { apply/lookup_iff.
      exists a; split; first exact: REF.
      split; first exact: ALW.
      rewrite EQhp.
      exact: substate_refl. }
    rewrite /read_ptr /bind /get.
    rewrite LK /=.
    rewrite encode_decode.
    exists $0%sep, s.
    split; first exact: op_id_l.
    by split.
  Qed.

  Lemma read_ptr_bw {So: Storable.type Vl} [p: Pt] [a: Ad] [Q: So -> Pred Sm] (x: So)
    (REF: References p a) (ALW: Allows p Operation.Read):
    [[ a ||~> encode x ** (a ||~> encode x -* Q x) ]] read_ptr p [[ Q ]].
  Proof using Type.
    have FR: [[ a ||~> encode x ** (a ||~> encode x -* Q x) ]] read_ptr p
               [[ fun r => ([| r = x |] ** a ||~> encode x) ** (a ||~> encode x -* Q x) ]].
    { frame (read_ptr_fw REF ALW). }
    apply: (consequence _ FR); first by [].
    move=> r s [ s1 [ sw [ EQs [ [ ? [ s2 [ EQs1 [ [ -> EMP ] CELL ] ] ] ] WAND ] ] ] ].
    move: EMP EQs1 => -> EQs1.
    move/partition_emp_l: EQs1 CELL => -> CELL.
    apply: (star_wand_mp (a ||~> encode x) (Q x)).
    exists s1, sw.
    by split; [ exact: EQs | split ].
  Qed.

  Lemma read_ptr_lookup [total: bool] {So: Storable.type Vl} [p: Pt] [a: Ad] [P: So -> Pred Sm]
    (REF: References p a) (ALW: Allows p Operation.Read):
    hoare total (Exists x, upclose (a ||~> encode x) && P x) (read_ptr p) P.
  Proof using Type.
    apply: exists_pre => x.
    have FW: hoare total (a ||~> encode x) (read_ptr p) (fun r => [| r = x |] ** a ||~> encode x).
    { case: total; [ exact: read_ptr_fw | exact: total_partial (read_ptr_fw REF ALW) ]. }
    have FR: hoare total ((a ||~> encode x ** top) && P x) (read_ptr p)
               (fun r => (([| r = x |] ** a ||~> encode x) ** top) && P x).
    { frame.
      frame FW. }
    apply: (consequence _ FR); first by [].
    move=> r s [ [ s1 [ s2 [ _ [ [ s3 [ s4 [ _ [ [ EQr _ ] _ ] ] ] ] _ ] ] ] ] Pxs ].
    by rewrite EQr.
  Qed.

  Lemma write_ptr_fw {So: Storable.type Vl} [p: Pt] [a: Ad] [w: Vl] [x: So]
    (REF: References p a) (ALW: Allows p Operation.Write):
    [[ a ||~> w ]] write_ptr p x [[ fun=> a ||~> encode x ]].
  Proof using Type.
    move=> s [ EQst [ EQsg [ EQhp EQalc ] ] ].
    have MUT: mutate (heap s) p (encode x) = Some (a |-> (encode x)).
    { rewrite EQhp.
      exact: (mutate_one REF ALW w (encode x)). }
    rewrite (write_ptr_some p x s (state_mutate_heap s MUT) _ MUT
               (store_state_mutate_heap s _ _ _ MUT) (scnt_state_mutate_heap s _ _ _ MUT)
               (heap_state_mutate_heap s _ _ _ MUT) (alc_state_mutate_heap s _ _ _ MUT)).
    rewrite /own_heap store_state_mutate_heap scnt_state_mutate_heap heap_state_mutate_heap
      alc_state_mutate_heap.
    by split; [ | split; [ | split ] ].
  Qed.

  Lemma write_ptr_bw {So: Storable.type Vl} [p: Pt] [a: Ad] [x: So] [Q: unit -> Pred Sm] (w: Vl)
    (REF: References p a) (ALW: Allows p Operation.Write):
    [[ a ||~> w ** (a ||~> encode x -* Q tt) ]] write_ptr p x [[ Q ]].
  Proof using Type.
    have FR: [[ a ||~> w ** (a ||~> encode x -* Q tt) ]] write_ptr p x
               [[ fun=> a ||~> encode x ** (a ||~> encode x -* Q tt) ]].
    { frame (write_ptr_fw REF ALW). }
    apply: (consequence _ FR); first by [].
    move=> [ ] s POST.
    exact: (star_wand_mp (a ||~> encode x) (Q tt) s POST).
  Qed.

  Lemma alloc_ptr_fw {So: Storable.type Vl} [sz: N] [x: So] [c: Alc Sm] [b: nat]
    (CGET: cget c = Some b) (POS: (0 < sz)%N) (MAX: (sz <= alloc_max_size)%N):
    [[ own_alc c ]] alloc_ptr sz x
    [[ fun p => [| References p (mkAddr b 0) /\ Allows p Operation.Free /\ Extent p b sz |]
                ** (Iter o in seq 0 (N.to_nat sz), mkAddr b (N.of_nat o) ||~> encode x)
                ** own_alc (cnext c) ]].
  Proof using Type.
    move=> s [ EQst [ EQsg [ EQhp EQalc ] ] ].
    have CGETs: cget (alc s) = Some b by rewrite EQalc.
    have FRESH: forall o v', ~ (((mkAddr b o) |-> v': @m_hp Sm) $<= heap s).
    { move=> o v'.
      rewrite EQhp.
      exact: emp_no_sub. }
    case: (proj1 (alloc_some (heap s) (alc s) sz (encode x))
             (ex_intro _ b (conj CGETs (conj POS FRESH)))) => h' [ alc' [ p ALLOC ] ].
    rewrite (alloc_ptr_some sz x s (state_alloc s ALLOC) h' alc' p MAX ALLOC
               (store_state_alloc s _ _ _ _ _ ALLOC) (scnt_state_alloc s _ _ _ _ _ ALLOC)
               (heap_state_alloc s _ _ _ _ _ ALLOC) (alc_state_alloc s _ _ _ _ _ ALLOC)).
    have EQalc': alc' = cnext c by rewrite (alloc_alc _ _ _ _ _ _ _ ALLOC) EQalc.
    have EXT: Extent p b sz := alloc_Extent _ _ _ _ _ _ _ _ ALLOC CGETs.
    have CHAR: forall (a: Ad) (w: Vl), (((a |-> w): @m_hp Sm) $<= h') <->
                 (block a = b /\ (N.of_nat 0 <= offset a < N.of_nat (0 + N.to_nat sz))%N) /\ w = encode x.
    { move=> a w.
      split.
      - move=> SUB.
        case: (proj1 (alloc_mem _ _ _ _ _ _ _ ALLOC a w) SUB) => [ [ R [ R1 EQw ] ] | [ _ SUB0 ] ].
        + case: (proj1 (Extent_cell p b sz EXT a) (conj R R1)) => EQb LT.
          split; last exact: EQw.
          split; first exact: EQb.
          lia.
        + move: EQhp SUB0 => -> SUB0.
          by case: (emp_no_sub a w SUB0).
      - move=> [ [ EQb RNG ] EQw ].
        have LT: (offset a < sz)%N by lia.
        case: (proj2 (Extent_cell p b sz EXT a) (conj EQb LT)) => R R1.
        apply: (proj2 (alloc_mem _ _ _ _ _ _ _ ALLOC a w)).
        left.
        by split; [ | split ]. }
    exists (mk_state $0 $0 h' $0 (dominates_emp_cnt _) (dominates_emp_cnt _)), (emp_with_alc $0 (cnext c)).
    split.
    { apply: state_hp_ext_intro.
      - rewrite store_mk_state store_emp_with_alc store_state_alloc EQst.
        exact: op_id_l.
      - rewrite scnt_mk_state scnt_emp_with_alc scnt_state_alloc EQsg.
        exact: op_id_l.
      - rewrite heap_mk_state heap_emp_with_alc heap_state_alloc.
        exact: op_id_r.
      - rewrite alc_mk_state alc_emp_with_alc alc_state_alloc EQalc'.
        exact: op_id_l. }
    split; last first.
    { by rewrite /own_alc store_emp_with_alc scnt_emp_with_alc heap_emp_with_alc alc_emp_with_alc. }
    exists $0%sep, (mk_state $0 $0 h' $0 (dominates_emp_cnt _) (dominates_emp_cnt _)).
    split; first exact: op_id_l.
    split.
    { split; last by [].
      split; first exact: (alloc_references _ _ _ _ _ _ _ _ ALLOC CGETs).
      split; first exact: (alloc_allows _ _ _ _ _ _ _ _ ALLOC CGETs).
      exact: EXT. }
    apply: iter_star_own_heap_intro.
    - exact: store_mk_state.
    - exact: scnt_mk_state.
    - exact: alc_mk_state.
    - move=> a w.
      rewrite heap_mk_state.
      exact: CHAR.
  Qed.

  Lemma alloc_ptr_bw {So: Storable.type Vl} [sz: N] [x: So] [c: Alc Sm] [b: nat] [Q: Pt -> Pred Sm]
    (CGET: cget c = Some b) (POS: (0 < sz)%N) (MAX: (sz <= alloc_max_size)%N):
    [[ own_alc c
       ** (Forall p, ([| References p (mkAddr b 0) /\ Allows p Operation.Free /\ Extent p b sz |]
                      ** (Iter o in seq 0 (N.to_nat sz), mkAddr b (N.of_nat o) ||~> encode x)
                      ** own_alc (cnext c)) -* Q p) ]]
      alloc_ptr sz x [[ Q ]].
  Proof using Type.
    pose POST (p: Pt) := [| References p (mkAddr b 0) /\ Allows p Operation.Free /\ Extent p b sz |]
                         ** (Iter o in seq 0 (N.to_nat sz), mkAddr b (N.of_nat o) ||~> encode x)
                         ** own_alc (cnext c).
    have FR: [[ own_alc c ** (Forall p, POST p -* Q p) ]] alloc_ptr sz x
               [[ fun p => POST p ** (Forall p, POST p -* Q p) ]].
    { frame (alloc_ptr_fw CGET POS MAX). }
    apply: (consequence _ FR); first by [].
    move=> p s [ s1 [ sw [ EQs [ POSTs1 WAND ] ] ] ].
    apply: (star_wand_mp (POST p) (Q p)).
    exists s1, sw.
    split; first exact: EQs.
    split; first exact: POSTs1.
    exact: (WAND p).
  Qed.

  Lemma free_ptr_fw [p: Pt] [b: nat] [sz: N]
    (ALW: Allows p Operation.Free) (EXT: Extent p b sz):
    [[ Iter o in seq 0 (N.to_nat sz), Exists v, mkAddr b (N.of_nat o) ||~> v ]]
      free_ptr p [[ fun=> $$0 ]].
  Proof using Type.
    move=> s CELLS.
    case: (iter_star_own_heap_elim b 0 (N.to_nat sz) s CELLS) => EQst [ EQsg [ EQalc CHAR ] ].
    have COV: forall a, Reaches p a -> Reaches p (shift_fw a 1%N) ->
                        exists v, ((a |-> v): @m_hp Sm) $<= heap s.
    { move=> a R R1.
      case: (proj1 (Extent_cell p b sz EXT a) (conj R R1)) => EQb LT.
      apply/CHAR.
      split; first exact: EQb.
      lia. }
    case: (proj1 (free_some (heap s) p) (conj ALW COV)) => h' FREE.
    have EQh': h' = $0.
    { apply: mem_ext => a w.
      split => SUB; last by case: (emp_no_sub a w SUB).
      case: (free_mem _ _ _ FREE a) => [ [ _ NEX ] | [ NR IFF ] ].
      - by case: NEX; exists w.
      - case: NR.
        apply/(Extent_cell p b sz EXT a).
        case: (proj1 (CHAR a) (ex_intro _ w (proj2 (IFF w) SUB))) => EQb RNG.
        split; first exact: EQb.
        lia. }
    rewrite (free_ptr_some p s (state_free s FREE) h' FREE (store_state_free s _ _ FREE)
               (scnt_state_free s _ _ FREE) (heap_state_free s _ _ FREE) (alc_state_free s _ _ FREE)).
    rewrite /Emp.
    apply: state_ext.
    - by rewrite store_state_free store_emp.
    - by rewrite scnt_state_free scnt_emp.
    - by rewrite heap_state_free heap_emp.
    - by rewrite alc_state_free alc_emp.
  Qed.

  Lemma free_ptr_bw [p: Pt] [b: nat] [sz: N] [Q: unit -> Pred Sm]
    (ALW: Allows p Operation.Free) (EXT: Extent p b sz):
    [[ (Iter o in seq 0 (N.to_nat sz), Exists v, mkAddr b (N.of_nat o) ||~> v) ** ($$0 -* Q tt) ]]
      free_ptr p [[ Q ]].
  Proof using Type.
    have FR: [[ (Iter o in seq 0 (N.to_nat sz), Exists v, mkAddr b (N.of_nat o) ||~> v) ** ($$0 -* Q tt) ]]
               free_ptr p [[ fun=> $$0 ** ($$0 -* Q tt) ]].
    { frame (free_ptr_fw ALW EXT). }
    apply: (consequence _ FR); first by [].
    move=> [ ] s POST.
    exact: (star_wand_mp $$0 (Q tt) s POST).
  Qed.

End HeapTriples.

Section PointerTriples.

  Context [Sm: State.type].
  Local Notation Ad := (@m_ad Sm).
  Local Notation Nm := (@var_name Sm).
  Local Notation Pt := (@ptr_t Sm).
  Local Notation Vl := (value (@ptr_t Sm)).
  Local Notation Hp := (@m_hp Sm).

  Lemma shift_fw_ptr_fw [p: Pt] [sh: N] [a: Ad] [h: Hp]
    (REF: References p a) (RCH: Reaches p a) (RCHs: Reaches p (shift_fw a sh))
    (WV: WValid h p) (WVs: forall p', References p' (shift_fw a sh) -> WValid h p'):
    [[ own_heap h ]] shift_fw_ptr p sh
    [[ fun r => [| ptr_shift_fw p sh = Some r /\ References r (shift_fw a sh) /\ (forall a', Reaches r a' <-> Reaches p a') |]
                ** own_heap h ]].
  Proof using Type.
    move=> s PRE.
    case: (PRE) => [ _ [ _ [ EQhp _ ] ] ].
    case: (proj1 (ptr_shift_fw_some p sh) (ex_intro _ a (conj REF (conj RCH RCHs)))) => p' EQp'.
    have REF' := ptr_shift_fw_references p sh p' EQp' a REF.
    have WVb: weakly_valid h p = true.
    { case: (weakly_valid_spec h p) => [ // | NW ].
      case: (NW WV). }
    have WVb': weakly_valid h p' = true.
    { case: (weakly_valid_spec h p') => [ // | NW ].
      case: (NW (WVs p' REF')). }
    rewrite /shift_fw_ptr /bind /get.
    rewrite EQhp WVb EQp' WVb' /=.
    exists $0%sep, s.
    split; first exact: op_id_l.
    split; last exact: PRE.
    split; last by [].
    split; first by [].
    split; [ exact: REF' | exact: (ptr_shift_fw_reaches p sh p' EQp') ].
  Qed.

  Lemma shift_fw_ptr_bw [p: Pt] [sh: N] [a: Ad] [h: Hp] [Q: Pt -> Pred Sm]
    (REF: References p a) (RCH: Reaches p a) (RCHs: Reaches p (shift_fw a sh))
    (WV: WValid h p) (WVs: forall p', References p' (shift_fw a sh) -> WValid h p'):
    [[ own_heap h
       ** (Forall r, ([| ptr_shift_fw p sh = Some r /\ References r (shift_fw a sh) /\ (forall a', Reaches r a' <-> Reaches p a') |]
                      ** own_heap h) -* Q r) ]]
      shift_fw_ptr p sh [[ Q ]].
  Proof using Type.
    pose POST (r: Pt) := [| ptr_shift_fw p sh = Some r /\ References r (shift_fw a sh) /\ (forall a', Reaches r a' <-> Reaches p a') |]
                         ** own_heap h.
    have FR: [[ own_heap h ** (Forall r, POST r -* Q r) ]] shift_fw_ptr p sh
               [[ fun r => POST r ** (Forall r, POST r -* Q r) ]].
    { frame (shift_fw_ptr_fw REF RCH RCHs WV WVs). }
    apply: (consequence _ FR); first by [].
    move=> r s [ s1 [ sw [ EQs [ POSTs1 WAND ] ] ] ].
    apply: (star_wand_mp (POST r) (Q r)).
    exists s1, sw.
    split; first exact: EQs.
    split; first exact: POSTs1.
    exact: (WAND r).
  Qed.

  Lemma shift_bw_ptr_fw [p: Pt] [sh: N] [a a': Ad] [h: Hp]
    (REF: References p a) (RCH: Reaches p a) (SH: shift_bw a sh = Some a') (RCHs: Reaches p a')
    (WV: WValid h p) (WVs: forall p', References p' a' -> WValid h p'):
    [[ own_heap h ]] shift_bw_ptr p sh
    [[ fun r => [| ptr_shift_bw p sh = Some r /\ References r a' /\ (forall a'', Reaches r a'' <-> Reaches p a'') |]
                ** own_heap h ]].
  Proof using Type.
    move=> s PRE.
    case: (PRE) => [ _ [ _ [ EQhp _ ] ] ].
    case: (proj1 (ptr_shift_bw_some p sh)
             (ex_intro _ a (ex_intro _ a' (conj REF (conj RCH (conj SH RCHs)))))) => p' EQp'.
    move: (ptr_shift_bw_references p sh p' EQp' a REF).
    rewrite SH => - [ _ [ [ <- ] REF' ] ].
    have WVb: weakly_valid h p = true.
    { case: (weakly_valid_spec h p) => [ // | NW ].
      case: (NW WV). }
    have WVb': weakly_valid h p' = true.
    { case: (weakly_valid_spec h p') => [ // | NW ].
      case: (NW (WVs p' REF')). }
    rewrite /shift_bw_ptr /bind /get.
    rewrite EQhp WVb EQp' WVb' /=.
    exists $0%sep, s.
    split; first exact: op_id_l.
    split; last exact: PRE.
    split; last by [].
    split; first by [].
    split; [ exact: REF' | exact: (ptr_shift_bw_reaches p sh p' EQp') ].
  Qed.

  Lemma shift_bw_ptr_bw [p: Pt] [sh: N] [a a': Ad] [h: Hp] [Q: Pt -> Pred Sm]
    (REF: References p a) (RCH: Reaches p a) (SH: shift_bw a sh = Some a') (RCHs: Reaches p a')
    (WV: WValid h p) (WVs: forall p', References p' a' -> WValid h p'):
    [[ own_heap h
       ** (Forall r, ([| ptr_shift_bw p sh = Some r /\ References r a' /\ (forall a'', Reaches r a'' <-> Reaches p a'') |]
                      ** own_heap h) -* Q r) ]]
      shift_bw_ptr p sh [[ Q ]].
  Proof using Type.
    pose POST (r: Pt) := [| ptr_shift_bw p sh = Some r /\ References r a' /\ (forall a'', Reaches r a'' <-> Reaches p a'') |]
                         ** own_heap h.
    have FR: [[ own_heap h ** (Forall r, POST r -* Q r) ]] shift_bw_ptr p sh
               [[ fun r => POST r ** (Forall r, POST r -* Q r) ]].
    { frame (shift_bw_ptr_fw REF RCH SH RCHs WV WVs). }
    apply: (consequence _ FR); first by [].
    move=> r s [ s1 [ sw [ EQs [ POSTs1 WAND ] ] ] ].
    apply: (star_wand_mp (POST r) (Q r)).
    exists s1, sw.
    split; first exact: EQs.
    split; first exact: POSTs1.
    exact: (WAND r).
  Qed.

  Lemma eq_ptr_fw [l r: Pt] [h: Hp]
    (CV: CmpValid h l r) (ALWl: Allows l Operation.Cmp) (ALWr: Allows r Operation.Cmp):
    [[ own_heap h ]] eq_ptr l r [[ fun c => [| c = ptr_addr_eqb l r |] ** own_heap h ]].
  Proof using Type.
    move=> s PRE.
    case: (PRE) => [ _ [ _ [ EQhp _ ] ] ].
    have CVb: cmp_valid h l r = true.
    { case: (cmp_valid_spec h l r) => [ // | NC ].
      case: (NC CV). }
    rewrite /eq_ptr /bind /get.
    rewrite EQhp CVb (proj1 (cmp_spec l r) (conj ALWl ALWr)) /=.
    exists $0%sep, s.
    split; first exact: op_id_l.
    by split.
  Qed.

  Lemma eq_ptr_bw [l r: Pt] [h: Hp] [Q: bool -> Pred Sm]
    (CV: CmpValid h l r) (ALWl: Allows l Operation.Cmp) (ALWr: Allows r Operation.Cmp):
    [[ own_heap h ** (own_heap h -* Q (ptr_addr_eqb l r)) ]] eq_ptr l r [[ Q ]].
  Proof using Type.
    have FR: [[ own_heap h ** (own_heap h -* Q (ptr_addr_eqb l r)) ]] eq_ptr l r
               [[ fun c => ([| c = ptr_addr_eqb l r |] ** own_heap h) ** (own_heap h -* Q (ptr_addr_eqb l r)) ]].
    { frame (eq_ptr_fw CV ALWl ALWr). }
    apply: (consequence _ FR); first by [].
    move=> c s [ s1 [ sw [ EQs [ [ ? [ s2 [ EQs1 [ [ -> EMP ] HEAP ] ] ] ] WAND ] ] ] ].
    move: EMP EQs1 => -> EQs1.
    move/partition_emp_l: EQs1 HEAP => -> HEAP.
    apply: (star_wand_mp (own_heap h) (Q (ptr_addr_eqb l r))).
    exists s1, sw.
    by split; [ exact: EQs | split ].
  Qed.

End PointerTriples.

Lemma div_fw [S: Type] [UInt: Unsigned.Unsigned] [l r: UInt] [P: Pred S] (NZ: to_Z r <> 0%Z):
  [[ P ]] Unsigned.div l r [[ fun v s => v = of_Z ((to_Z l / to_Z r) mod modulus UInt)%Z /\ P s ]].
Proof.
  move=> s Ps.
  rewrite /Unsigned.div.
  case: (Z.eqb_spec (to_Z r) 0%Z) => [ EQr | _ ]; first by case: (NZ EQr).
  by split.
Qed.

Lemma div_bw [S: Type] [UInt: Unsigned.Unsigned] [l r: UInt] [P: UInt -> Pred S]:
  [[ fun s => to_Z r <> 0%Z /\ P (of_Z ((to_Z l / to_Z r) mod modulus UInt)%Z) s ]] Unsigned.div l r [[ P ]].
Proof.
  apply: pure_pre => NZ.
  apply: (consequence _ (div_fw (P:=P (of_Z ((to_Z l / to_Z r) mod modulus UInt)%Z)) NZ)).
  - by [].
  - by move=> v s [ -> Ps ].
Qed.

Lemma mdl_fw [S: Type] [UInt: Unsigned.Unsigned] [l r: UInt] [P: Pred S] (NZ: to_Z r <> 0%Z):
  [[ P ]] Unsigned.mdl l r [[ fun v s => v = of_Z ((to_Z l mod to_Z r) mod modulus UInt)%Z /\ P s ]].
Proof.
  move=> s Ps.
  rewrite /Unsigned.mdl.
  case: (Z.eqb_spec (to_Z r) 0%Z) => [ EQr | _ ]; first by case: (NZ EQr).
  by split.
Qed.

Lemma mdl_bw [S: Type] [UInt: Unsigned.Unsigned] [l r: UInt] [P: UInt -> Pred S]:
  [[ fun s => to_Z r <> 0%Z /\ P (of_Z ((to_Z l mod to_Z r) mod modulus UInt)%Z) s ]] Unsigned.mdl l r [[ P ]].
Proof.
  apply: pure_pre => NZ.
  apply: (consequence _ (mdl_fw (P:=P (of_Z ((to_Z l mod to_Z r) mod modulus UInt)%Z)) NZ)).
  - by [].
  - by move=> v s [ -> Ps ].
Qed.
