From Stdlib Require Import Arith NArith.
From GallinaC.Utils Require Import Algebra.
From GallinaC.Imp Require Import Store Heap.
Import Store.Facts Heap.Facts.
From GallinaC.Imp Require Import Monad Primitives.
From GallinaC.Seplog Require Import Hoare Pred GenAssertion.

Local Open Scope separation_scope.
Local Open Scope state_scope.
Local Open Scope program_scope.
Local Open Scope heap_scope.

Definition state_hp_ext {St Hp} (s1 s2: State St Hp) hp: Prop :=
  Primitives.store s1 = Primitives.store s2 /\
    Primitives.heap s1 $+ hp = Some (Primitives.heap s2).

Definition action_local {A St Hp} (c: program (State St Hp) A): Prop :=
  forall s1 s2 hp,
    state_hp_ext s1 s2 hp ->
    match c s1 with
    | Some (Success (v, s1')) =>
        exists s2',
        state_hp_ext s1' s2' hp
        /\ c s2 = Some (Success (v, s2'))
    | Some Failure => True
    | None => c s2 = None
    end.

(* Executing a command c does not change the store in a way that it invalidates the predicate P *)
(* Note: Why is the heap hp and not (heap s1) ? *)
Definition indep_cmd_store {A St Hp} (P: Pred (State St Hp)) (c: program (State St Hp) A) :=
  forall s1 v s1' hp, c s1 = Some (Success (v, s1')) -> P (mkState (store s1) hp) -> P (mkState (store s1') hp).

(* A stronger/stricter version of indep_cmd_store *)
(* It is closer to how it is in the litterature *)

(* Only the variables in nms is guaranteed equal in stores st1 and st2 *)
Definition store_partial_equal {St: Store.Store} (st1 st2: Store.store St) nms: Prop :=
  forall nm v, List.In nm nms -> (BindsTo nm v st1 <-> BindsTo nm v st2).
(* If P is true for a state, then replacing the store by a partially equal one doesn't invalidate P *)
Definition indep_partial_store {St Hp} (P: Pred (State St Hp)) (nms: list (@name St)) :=
  forall s1 st2, P s1 -> store_partial_equal (store s1) st2 nms -> P (mkState st2 (heap s1)).
(* Executing P does not change a part of the store *)
Definition indep_cmd_partial_store {A St Hp} (c: program (State St Hp) A) nms :=
  forall s v s', c s = Some (Success (v, s')) -> store_partial_equal (store s) (store s') nms.
(* Now we have indep_cmd_store if we have both of these properties *)
Lemma indep_cmd_store_select_impl {A St Hp} (P: Pred (State St Hp)) (c: program (State St Hp) A) nms:
  indep_partial_store P nms -> indep_cmd_partial_store c nms -> indep_cmd_store P c.
Proof.
  intros HindepP Hindepc.
  unfold indep_cmd_store.
  intros s v s' hp Hcs HP.
  specialize (Hindepc s v s' Hcs).
  specialize (HindepP (mkState (store s) hp) (store s') HP Hindepc).
  assumption.
Qed.

Lemma frame {St Hp} (P R: (State St Hp) -> Prop) (Q: memval -> (State St Hp) -> Prop) c: indep_cmd_store R c -> action_local c -> {{ P }} c {{ Q }} -> {{ P ** R }} c {{ fun v s => ((Q v) ** R) s }}.
Proof.
  intros Hindep_store Haction_local HPQ s HPR.
  destruct HPR as ( s1 & s2 & Hst1 & Hst2 & HPartition & HP & HR ).
  specialize (HPQ s1 HP).
  specialize (Haction_local s1 s (heap s2) ltac:(constructor; [ congruence | apply HPartition ])).
  destruct (c s1) as [ [ [ v s1' ] | ] | ] eqn:Ecs1.
  - destruct Haction_local as ( s2' & ( Hst' & HPartition') & Ecs ).
    rewrite Ecs.
    exists {| store := store s1'; heap := (heap s1') |},
      {| store := store s1' ; heap := heap s2 |};
      cbn.
    split; [ congruence | ].
    split; [ congruence | ].
    split; [ assumption | ].
    split; [ now destruct s1' | ].
    specialize (Hindep_store s1 v s1' (heap s2) Ecs1).
    apply Hindep_store.
    destruct s1 as [ st1 hp1 ], s2 as [ st2 hp2 ]; now rewrite <- Hst1, Hst2.
  - contradiction.
  - now rewrite Haction_local.
Qed.

Lemma action_local_ret {St Hp A} (val: A): @action_local A St Hp (ret val).
Proof.
  intros s1 s2 hp (Hst & HPartition); cbn.
  exists s2.
  repeat split; eauto with mem.
Qed.
Hint Resolve action_local_ret: seplog.

Lemma action_local_fail {St Hp A}: @action_local A St Hp fail.
Proof.
  now intros s1 s2 h (Hst & HPartition).
Qed.
Hint Resolve action_local_fail: seplog.

Lemma action_local_loop {St Hp A}: @action_local A St Hp loop.
Proof.
  now intros s1 s2 h (Hst & HPartition).
Qed.
Hint Resolve action_local_loop: seplog.

Lemma action_local_bind {St Hp A B} (c: program (State St Hp) A) (f: A -> program _ B):
  action_local c -> (forall v, action_local (f v)) -> action_local (bind c f).
Proof.
  intros Haction_localc Haction_localf s1 s2 hp (Hst & HPartition).
  unfold bind.
  specialize (Haction_localc s1 s2 hp (conj Hst HPartition)).
  destruct (c s1) as [ [ [ x s1' ] | ] | ] eqn:Ecs1;
    [  | trivial | now rewrite Haction_localc ].
  destruct Haction_localc as ( s2' & (Hst' & HPartition') & Hcs2 ).
  rewrite Hcs2.
  specialize (Haction_localf x s1' s2' hp (conj Hst' HPartition')).
  destruct (f x s1') as [ [ [ y s1'' ] | ] | ] eqn:Efxs1';
    assumption.
Qed.
Hint Resolve action_local_bind: seplog.

Lemma action_local_If {St Hp A}
  (c_if: program (State St Hp) bool)
  (c_then c_else: program (State St Hp) A)
  (Haction_local_if: action_local c_if)
  (Haction_local_then: action_local c_then)
  (Haction_local_else: action_local c_else):
  action_local (If c_if then c_then else c_else).
Proof.
  intros s1 s2 hp (Hst & HPartition).
  apply action_local_bind; [ | destruct v | constructor]; assumption.
Qed.
Hint Resolve action_local_If: seplog.

Lemma action_local_while_fuel {St Hp}
  fuel
  (cond: program (State St Hp) bool)
  (body: program (State St Hp) unit)
  (Haction_local_cond: action_local cond)
  (Haction_local_body: action_local body):
  action_local ( while_fuel fuel cond body ).
Proof.
  induction fuel.
  apply action_local_loop.
  rewrite while_fuel_fixpoint.
  eauto with seplog.
Qed.

Lemma action_local_While {St Hp}
  (cond: program (State St Hp) bool)
  (body: program (State St Hp) unit)
  (Haction_local_cond: action_local cond)
  (Haction_local_body: action_local body):
  action_local ( while cond body ).
Proof.
  intros s1 s2 hp HpExt.
  destruct (while cond body s1) as [ [[[ ] s1'''] | ] | ] eqn:Ewhile; [ | auto | ].
  - apply while_fuel_while_some in Ewhile as (fuel & Ewhile).
    revert s1 s2 hp HpExt s1''' Ewhile.
    induction fuel; intros; [ discriminate | ].
    rewrite while_fuel_fixpoint in Ewhile.
    rewrite while_fixpoint.
    unfold bind in *.
    specialize (Haction_local_cond s1 s2 hp HpExt).
    destruct (cond s1) as [ [ [ b s1' ] | ] | ]; [ destruct Haction_local_cond as (s2' & HpExt' & EQcond) | discriminate | discriminate ].
    destruct b; [ | now inversion Ewhile; subst s1'''; exists s2'; split; auto; rewrite EQcond ].
    rewrite EQcond.
    specialize (Haction_local_body s1' s2' hp HpExt').
    destruct (body s1') as [ [ [ [] s1'' ] | ] | ]; [ destruct Haction_local_body as (s2'' & HpExt'' & EQbody) | discriminate | discriminate ].
    rewrite EQbody.
    eapply IHfuel.
    apply HpExt''.
    apply Ewhile.
  - apply while_fuel_None_while.
    intros fuel.
    revert s1 s2 HpExt Ewhile.
    induction fuel; intros; auto.
    rewrite while_fixpoint in Ewhile.
    rewrite while_fuel_fixpoint.
    unfold bind in *.
    specialize (Haction_local_cond s1 s2 hp HpExt).
    destruct (cond s1) as [ [ [ [ | ] s1' ] | ] | ]; [  | discriminate | discriminate | now rewrite Haction_local_cond ].
    destruct Haction_local_cond as (s2' & HpExt' & EQcond).
    rewrite EQcond.
    specialize (Haction_local_body s1' s2' hp HpExt').
    destruct (body s1') as [ [ [ [ ] s1'' ] | ] | ]; [ | discriminate | now rewrite Haction_local_body ].
    destruct Haction_local_body as (s2'' & HpExt'' & EQbody).
    rewrite EQbody.
    eapply IHfuel.
    apply HpExt''.
    apply Ewhile.
Qed.

Lemma action_local_with_var {A St Hp MS}
  {e_var: (obj MS)}
  {p_cont: @name St -> program (State St Hp) A}
  (ACTLOC_cont: forall nm, action_local (p_cont nm))
  : action_local (with_var e_var p_cont).
Proof.
  intros s1 s2 hp HpExt.
  unfold with_var.
  cbn.
  unfold bind.
  destruct (push (store s1) (encode e_var)) as [ st' nm ] eqn:Epush; cbn.
  specialize (ACTLOC_cont nm).
Admitted.

Lemma action_local_read_var {St Hp MS} varname: action_local (@read_var St Hp MS varname).
Proof.
  intros s1 s2 hp (Hst & HPartition); cbn.
  destruct (Store.lookup (store s1) varname) as [ mem_val | ] eqn:Elookup; [ cbn | now cbn ].
  destruct (decode mem_val) as [ val | ] eqn:Edecode; [ cbn | now cbn ].
  exists s2.
  split; [ split; assumption | ].
  apply Store.lookup_spec in Elookup.
  rewrite <- Hst.
  rewrite (Store.Facts.lookup_spec_l Elookup).
  rewrite Edecode.
  reflexivity.
Qed.

Lemma action_local_write_var {St Hp MS} varname val: action_local (@write_var St Hp MS varname val).
Proof.
  intros s1 s2 h (Hst & HPartition); cbn.
  destruct (Store.mutate (store s1) varname (encode val)) as [ st' | ] eqn:Emutate; [ cbn | reflexivity ].
  exists (mkState st' (heap s2)).
  split; [ split; [ reflexivity | assumption ] | ].
  rewrite <- Hst, Emutate; reflexivity.
Qed.

Lemma action_local_read_ptr {St Hp MS} ptr: action_local (@read_ptr St Hp MS ptr).
Proof.
  intros s1 s2 h (Hst & HPartition); cbn.
  destruct (Heap.lookup (heap s1) ptr) as [ mem_val | ] eqn:Elookup; [ cbn | reflexivity ].
  destruct (decode mem_val) as [ val | ] eqn:Edecode; [ cbn | reflexivity ].
  exists s2.
  split; [ split; assumption | ].
  rewrite (proj1 (lookup_some (heap s2) ptr mem_val)), Edecode.
  reflexivity.
  apply lookup_some in Elookup.
  destruct Elookup as (addr & REF & ALLOWS & SUB).
  exists addr.
  split; auto.
  split; auto.
  etransitivity.
  apply SUB.
  now exists h.
Qed.

Lemma action_local_write_ptr {St Hp MS} ptr val: action_local (@write_ptr St Hp MS ptr val).
Proof.
  intros s1 s2 hp HpExt; cbn.
  destruct (Heap.mutate (heap s1) ptr (encode val)) as [ hp' | ] eqn:Emutate; [ cbn | easy ].
  (* mutate does not alter heap disjointness, hence it should follow immediately *)
Admitted.

Lemma action_local_alloc_ptr {St: Store} {Hp: Heap} {MS} (sz: N) val: action_local (@alloc_ptr St Hp MS sz val).
Proof.
  intros s1 s2 hp HpExt; cbn.
  destruct (Heap.alloc (heap s1) sz (encode val)) as [ [ hp' ptr ] | ] eqn:Ealloc; [ cbn | easy ].
  (* ditto *)
Admitted.

Lemma action_local_free_ptr {St: Store} {Hp: Heap} (ptr: Pointer.t): action_local (@free_ptr St Hp ptr).
Proof.
  intros s1 s2 hp HpExt; cbn.
  destruct (Heap.free (heap s1) ptr) as [ hp' | ] eqn:Ealloc; [ cbn | easy ].
  (* ditto *)
Admitted.

Lemma action_local_shift_fw_ptr {St: Store} {Hp: Heap} (ptr: Pointer.t) (shift: N.t): action_local (@shift_fw_ptr St Hp ptr shift).
Proof.
Admitted.

Lemma action_local_shift_bw_ptr {St: Store} {Hp: Heap} (ptr: Pointer.t) (shift: N.t): action_local (@shift_bw_ptr St Hp ptr shift).
Proof.
Admitted.

Lemma action_local_eq_ptr {St: Store} {Hp: Heap} (ptr_l ptr_r: Pointer.t): action_local (@eq_ptr St Hp ptr_l ptr_r).
Proof.
Admitted.
