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

From Stdlib Require Import NArith Arith Lia.

From GallinaC.Utils Require NExt.
From GallinaC.Utils Require Import ListExt Algebra Counter OptionExt ProdExt.
From GallinaC.Imp Require Import Monad Storable Heap Store While.
From GallinaC.Imp Require Export Value.

Local Open Scope separation_scope.
Local Open Scope program_scope.

HB.mixin Record isState T of Separation T :=
  {
    m_ad: Addr.type;
    var_name: Ref.type m_ad;
    ptr_t: Ptr.type m_ad;
    m_st: Store.type m_ad var_name (value ptr_t);
    m_hp: Heap.type m_ad ptr_t (value ptr_t);

    store: T -> m_st;
    scnt: T -> excl (@store_cnt m_ad var_name (value ptr_t) m_st);
    heap: T -> m_hp;
    alc: T -> excl (@heap_alc m_ad ptr_t (value ptr_t) m_hp);

    mk_state: forall (st: m_st) (sc: excl (@store_cnt m_ad var_name (value ptr_t) m_st))
                     (h: m_hp) (c: excl (@heap_alc m_ad ptr_t (value ptr_t) m_hp))
                     (DOMs: dominates st sc) (DOMh: dominates h c), T;

    mk_state_opt: m_st -> excl (@store_cnt m_ad var_name (value ptr_t) m_st) ->
                  m_hp -> excl (@heap_alc m_ad ptr_t (value ptr_t) m_hp) -> option T;

    state_store_dominates: forall s1: T, dominates (store s1) (scnt s1);
    state_heap_dominates: forall s1: T, dominates (heap s1) (alc s1);

    state_ext: forall s1 s2: T,
        store s1 = store s2 -> scnt s1 = scnt s2 ->
        heap s1 = heap s2 -> alc s1 = alc s2 -> s1 = s2;

    store_mk_state: forall st sc h c DOMs DOMh,
        store (mk_state st sc h c DOMs DOMh) = st;
    scnt_mk_state: forall st sc h c DOMs DOMh,
        scnt (mk_state st sc h c DOMs DOMh) = sc;
    heap_mk_state: forall st sc h c DOMs DOMh,
        heap (mk_state st sc h c DOMs DOMh) = h;
    alc_mk_state: forall st sc h c DOMs DOMh,
        alc (mk_state st sc h c DOMs DOMh) = c;

    mk_state_opt_some: forall st sc h c (s1: T),
        mk_state_opt st sc h c = Some s1
        <-> (store s1 = st /\ scnt s1 = sc /\ heap s1 = h /\ alc s1 = c);

    state_sum_spec: forall s1 s2 s3: T,
        s1 $+ s2 = Some s3
        <-> (store s1 $+ store s2 = Some (store s3) /\
               scnt s1 $+ scnt s2 = Some (scnt s3) /\
               heap s1 $+ heap s2 = Some (heap s3) /\
               alc s1 $+ alc s2 = Some (alc s3));

    state_emp: ($0: T)
               = mk_state $0 $0 $0 $0
                   (dominates_emp ($0: excl (@store_cnt m_ad var_name (value ptr_t) m_st)))
                   (dominates_emp ($0: excl (@heap_alc m_ad ptr_t (value ptr_t) m_hp)));
  }.

HB.structure Definition State := { T of Separation T & isState T }.

Notation SCnt Sm := (excl (@store_cnt (@m_ad Sm) (@var_name Sm) (value (@ptr_t Sm)) (@m_st Sm))).
Notation Alc Sm := (excl (@heap_alc (@m_ad Sm) (@ptr_t Sm) (value (@ptr_t Sm)) (@m_hp Sm))).

Section StateOps.

  Context {Sm: State.type}.

  Definition emp_with_alc (sc: SCnt Sm) (a: Alc Sm): Sm :=
    mk_state $0 sc $0 a (dominates_emp sc) (dominates_emp a).

  (* Apply [s'] store onto [s] *)
  Definition emp_state: Sm :=
    emp_with_alc (Owned (mk_cnt 0 None)) (Owned (mk_cnt 0 None)).

  Definition set_store (s s': Sm): Sm :=
    mk_state (store s') (scnt s') (heap s) (alc s)
      (state_store_dominates s') (state_heap_dominates s).

  Lemma store_set_store (s s': Sm): store (set_store s s') = store s'.
  Proof using Type. exact: store_mk_state. Qed.

  Lemma scnt_set_store (s s': Sm): scnt (set_store s s') = scnt s'.
  Proof using Type. exact: scnt_mk_state. Qed.

  Lemma heap_set_store (s s': Sm): heap (set_store s s') = heap s.
  Proof using Type. exact: heap_mk_state. Qed.

  Lemma alc_set_store (s s': Sm): alc (set_store s s') = alc s.
  Proof using Type. exact: alc_mk_state. Qed.

  Lemma set_store_self (s: Sm): set_store s s = s.
  Proof using Type.
    by apply: state_ext;
      [ rewrite store_set_store
      | rewrite scnt_set_store
      | rewrite heap_set_store
      | rewrite alc_set_store ].
  Qed.

  (* Apply [s'] store onto [s], with an empty counter *)
  Definition set_store_no_cnt (s s': Sm): Sm :=
    mk_state (store s') $0 (heap s) (alc s)
      (dominates_emp_cnt (store s')) (state_heap_dominates s).

  Lemma store_set_store_no_cnt (s s': Sm): store (set_store_no_cnt s s') = store s'.
  Proof using Type. exact: store_mk_state. Qed.

  Lemma scnt_set_store_no_cnt (s s': Sm): scnt (set_store_no_cnt s s') = $0.
  Proof using Type. exact: scnt_mk_state. Qed.

  Lemma heap_set_store_no_cnt (s s': Sm): heap (set_store_no_cnt s s') = heap s.
  Proof using Type. exact: heap_mk_state. Qed.

  Lemma alc_set_store_no_cnt (s s': Sm): alc (set_store_no_cnt s s') = alc s.
  Proof using Type. exact: alc_mk_state. Qed.

  Definition state_push (s: Sm) [v: value (@ptr_t Sm)] [st': @m_st Sm] [sg': SCnt Sm]
    [nm: @var_name Sm] (PUSH: push (store s) (scnt s) v = Some (st', sg', nm)): Sm :=
    mk_state st' sg' (heap s) (alc s)
      (dominates_push (store s) st' (scnt s) sg' v nm PUSH (state_store_dominates s))
      (state_heap_dominates s).

  Lemma store_state_push (s: Sm) v st' sg' nm
    (PUSH: push (store s) (scnt s) v = Some (st', sg', nm)):
    store (state_push s PUSH) = st'.
  Proof using Type. exact: store_mk_state. Qed.

  Lemma scnt_state_push (s: Sm) v st' sg' nm
    (PUSH: push (store s) (scnt s) v = Some (st', sg', nm)):
    scnt (state_push s PUSH) = sg'.
  Proof using Type. exact: scnt_mk_state. Qed.

  Lemma heap_state_push (s: Sm) v st' sg' nm
    (PUSH: push (store s) (scnt s) v = Some (st', sg', nm)):
    heap (state_push s PUSH) = heap s.
  Proof using Type. exact: heap_mk_state. Qed.

  Lemma alc_state_push (s: Sm) v st' sg' nm
    (PUSH: push (store s) (scnt s) v = Some (st', sg', nm)):
    alc (state_push s PUSH) = alc s.
  Proof using Type. exact: alc_mk_state. Qed.

  Definition state_pop (s: Sm) [st': @m_st Sm] (POP: pop (store s) = Some st'): Sm :=
    mk_state st' (scnt s) (heap s) (alc s)
      (dominates_pop (store s) st' (scnt s) POP (state_store_dominates s))
      (state_heap_dominates s).

  Lemma store_state_pop (s: Sm) st' (POP: pop (store s) = Some st'):
    store (state_pop s POP) = st'.
  Proof using Type. exact: store_mk_state. Qed.

  Lemma scnt_state_pop (s: Sm) st' (POP: pop (store s) = Some st'):
    scnt (state_pop s POP) = scnt s.
  Proof using Type. exact: scnt_mk_state. Qed.

  Lemma heap_state_pop (s: Sm) st' (POP: pop (store s) = Some st'):
    heap (state_pop s POP) = heap s.
  Proof using Type. exact: heap_mk_state. Qed.

  Lemma alc_state_pop (s: Sm) st' (POP: pop (store s) = Some st'):
    alc (state_pop s POP) = alc s.
  Proof using Type. exact: alc_mk_state. Qed.

  Definition state_pop_n (n: N) (s: Sm): option Sm :=
    match NExt.iter_opt (fun st => pop st) n (store s) with
    | Some st' => mk_state_opt st' (scnt s) (heap s) (alc s)
    | None => None
    end.

  Definition state_mutate_store (s: Sm) [nm: @var_name Sm] [v: value (@ptr_t Sm)]
    [st': @m_st Sm] (MUTATE: mutate (store s) nm v = Some st'): Sm :=
    mk_state st' (scnt s) (heap s) (alc s)
      (dominates_mutate (store s) st' nm v (scnt s) MUTATE (state_store_dominates s))
      (state_heap_dominates s).

  Lemma store_state_mutate_store (s: Sm) nm v st' (MUTATE: mutate (store s) nm v = Some st'):
    store (state_mutate_store s MUTATE) = st'.
  Proof using Type. exact: store_mk_state. Qed.

  Lemma scnt_state_mutate_store (s: Sm) nm v st' (MUTATE: mutate (store s) nm v = Some st'):
    scnt (state_mutate_store s MUTATE) = scnt s.
  Proof using Type. exact: scnt_mk_state. Qed.

  Lemma heap_state_mutate_store (s: Sm) nm v st' (MUTATE: mutate (store s) nm v = Some st'):
    heap (state_mutate_store s MUTATE) = heap s.
  Proof using Type. exact: heap_mk_state. Qed.

  Lemma alc_state_mutate_store (s: Sm) nm v st' (MUTATE: mutate (store s) nm v = Some st'):
    alc (state_mutate_store s MUTATE) = alc s.
  Proof using Type. exact: alc_mk_state. Qed.

  Definition state_mutate_heap (s: Sm) [p: @ptr_t Sm] [v: value (@ptr_t Sm)]
    [hp': @m_hp Sm] (MUTATE: mutate (heap s) p v = Some hp'): Sm :=
    mk_state (store s) (scnt s) hp' (alc s)
      (state_store_dominates s)
      (dominates_mutate (heap s) hp' p v (alc s) MUTATE (state_heap_dominates s)).

  Lemma store_state_mutate_heap (s: Sm) p v hp' (MUTATE: mutate (heap s) p v = Some hp'):
    store (state_mutate_heap s MUTATE) = store s.
  Proof using Type. exact: store_mk_state. Qed.

  Lemma scnt_state_mutate_heap (s: Sm) p v hp' (MUTATE: mutate (heap s) p v = Some hp'):
    scnt (state_mutate_heap s MUTATE) = scnt s.
  Proof using Type. exact: scnt_mk_state. Qed.

  Lemma heap_state_mutate_heap (s: Sm) p v hp' (MUTATE: mutate (heap s) p v = Some hp'):
    heap (state_mutate_heap s MUTATE) = hp'.
  Proof using Type. exact: heap_mk_state. Qed.

  Lemma alc_state_mutate_heap (s: Sm) p v hp' (MUTATE: mutate (heap s) p v = Some hp'):
    alc (state_mutate_heap s MUTATE) = alc s.
  Proof using Type. exact: alc_mk_state. Qed.

  Definition state_alloc (s: Sm) [sz: N.t] [v: value (@ptr_t Sm)] [hp': @m_hp Sm]
    [alc': Alc Sm] [p: @ptr_t Sm]
    (ALLOC: alloc (heap s) (alc s) sz v = Some (hp', alc', p)): Sm :=
    mk_state (store s) (scnt s) hp' alc'
      (state_store_dominates s)
      (dominates_alloc (heap s) hp' (alc s) alc' sz v p ALLOC (state_heap_dominates s)).

  Lemma store_state_alloc (s: Sm) sz v hp' alc' p
    (ALLOC: alloc (heap s) (alc s) sz v = Some (hp', alc', p)):
    store (state_alloc s ALLOC) = store s.
  Proof using Type. exact: store_mk_state. Qed.

  Lemma scnt_state_alloc (s: Sm) sz v hp' alc' p
    (ALLOC: alloc (heap s) (alc s) sz v = Some (hp', alc', p)):
    scnt (state_alloc s ALLOC) = scnt s.
  Proof using Type. exact: scnt_mk_state. Qed.

  Lemma heap_state_alloc (s: Sm) sz v hp' alc' p
    (ALLOC: alloc (heap s) (alc s) sz v = Some (hp', alc', p)):
    heap (state_alloc s ALLOC) = hp'.
  Proof using Type. exact: heap_mk_state. Qed.

  Lemma alc_state_alloc (s: Sm) sz v hp' alc' p
    (ALLOC: alloc (heap s) (alc s) sz v = Some (hp', alc', p)):
    alc (state_alloc s ALLOC) = alc'.
  Proof using Type. exact: alc_mk_state. Qed.

  Definition state_free (s: Sm) [p: @ptr_t Sm] [hp': @m_hp Sm]
    (FREE: free (heap s) p = Some hp'): Sm :=
    mk_state (store s) (scnt s) hp' (alc s)
      (state_store_dominates s)
      (dominates_free (heap s) hp' p (alc s) FREE (state_heap_dominates s)).

  Lemma store_state_free (s: Sm) p hp' (FREE: free (heap s) p = Some hp'):
    store (state_free s FREE) = store s.
  Proof using Type. exact: store_mk_state. Qed.

  Lemma scnt_state_free (s: Sm) p hp' (FREE: free (heap s) p = Some hp'):
    scnt (state_free s FREE) = scnt s.
  Proof using Type. exact: scnt_mk_state. Qed.

  Lemma heap_state_free (s: Sm) p hp' (FREE: free (heap s) p = Some hp'):
    heap (state_free s FREE) = hp'.
  Proof using Type. exact: heap_mk_state. Qed.

  Lemma alc_state_free (s: Sm) p hp' (FREE: free (heap s) p = Some hp'):
    alc (state_free s FREE) = alc s.
  Proof using Type. exact: alc_mk_state. Qed.

  Lemma store_emp_with_alc (sc: SCnt Sm) (a: Alc Sm):
    store (emp_with_alc sc a) = $0.
  Proof using Type. exact: store_mk_state. Qed.

  Lemma scnt_emp_with_alc (sc: SCnt Sm) (a: Alc Sm):
    scnt (emp_with_alc sc a) = sc.
  Proof using Type. exact: scnt_mk_state. Qed.

  Lemma heap_emp_with_alc (sc: SCnt Sm) (a: Alc Sm):
    heap (emp_with_alc sc a) = $0.
  Proof using Type. exact: heap_mk_state. Qed.

  Lemma alc_emp_with_alc (sc: SCnt Sm) (a: Alc Sm):
    alc (emp_with_alc sc a) = a.
  Proof using Type. exact: alc_mk_state. Qed.

  Lemma store_emp: store ($0: Sm) = $0.
  Proof using Type. by rewrite state_emp store_mk_state. Qed.

  Lemma scnt_emp: scnt ($0: Sm) = $0.
  Proof using Type. by rewrite state_emp scnt_mk_state. Qed.

  Lemma heap_emp: heap ($0: Sm) = $0.
  Proof using Type. by rewrite state_emp heap_mk_state. Qed.

  Lemma alc_emp: alc ($0: Sm) = $0.
  Proof using Type. by rewrite state_emp alc_mk_state. Qed.

  Lemma emp_proj:
    store ($0: Sm) = $0 /\ scnt ($0: Sm) = $0
    /\ heap ($0: Sm) = $0 /\ alc ($0: Sm) = $0.
  Proof.
    repeat split;
      [ exact: store_emp | exact: scnt_emp | exact: heap_emp | exact: alc_emp ].
  Qed.

  Definition state_store_only (s: Sm): Sm :=
    mk_state (store s) $0 $0 $0
      (dominates_emp_cnt (store s)) (dominates_emp _).

  Lemma state_store_only_proj (s: Sm):
    store (state_store_only s) = store s
    /\ scnt (state_store_only s) = $0
    /\ heap (state_store_only s) = $0
    /\ alc (state_store_only s) = $0.
  Proof using Type.
    repeat split;
      [ exact: (store_mk_state _ _ _ _ _ _)
      | exact: (scnt_mk_state _ _ _ _ _ _)
      | exact: (heap_mk_state _ _ _ _ _ _)
      | exact: (alc_mk_state _ _ _ _ _ _) ].
  Qed.

  Definition state_store_free (s: Sm): Sm :=
    mk_state $0 (scnt s) (heap s) (alc s)
      (dominates_emp _) (state_heap_dominates s).

  Lemma state_store_free_proj (s: Sm):
    store (state_store_free s) = $0
    /\ scnt (state_store_free s) = scnt s
    /\ heap (state_store_free s) = heap s
    /\ alc (state_store_free s) = alc s.
  Proof using Type.
    repeat split;
      [ exact: (store_mk_state _ _ _ _ _ _)
      | exact: (scnt_mk_state _ _ _ _ _ _)
      | exact: (heap_mk_state _ _ _ _ _ _)
      | exact: (alc_mk_state _ _ _ _ _ _) ].
  Qed.

  (* Componentwise projections of a state partition *)

  Lemma state_hp_ext_store (s1 s2 f: Sm) (EXT: s1 $+ f = Some s2)
    : store s1 $+ store f = Some (store s2).
  Proof using Type. exact: (proj1 (proj1 (state_sum_spec s1 f s2) EXT)). Qed.

  Lemma state_hp_ext_scnt (s1 s2 f: Sm) (EXT: s1 $+ f = Some s2)
    : scnt s1 $+ scnt f = Some (scnt s2).
  Proof using Type. exact: (proj1 (proj2 (proj1 (state_sum_spec s1 f s2) EXT))). Qed.

  Lemma state_hp_ext_heap (s1 s2 f: Sm) (EXT: s1 $+ f = Some s2)
    : heap s1 $+ heap f = Some (heap s2).
  Proof using Type. exact: (proj1 (proj2 (proj2 (proj1 (state_sum_spec s1 f s2) EXT)))). Qed.

  Lemma state_hp_ext_alc (s1 s2 f: Sm) (EXT: s1 $+ f = Some s2)
    : alc s1 $+ alc f = Some (alc s2).
  Proof using Type. exact: (proj2 (proj2 (proj2 (proj1 (state_sum_spec s1 f s2) EXT)))). Qed.

  Lemma state_hp_ext_intro (s1 s2 f: Sm)
    (EQst: store s1 $+ store f = Some (store s2))
    (EQsg: scnt s1 $+ scnt f = Some (scnt s2))
    (EQhp: heap s1 $+ heap f = Some (heap s2))
    (EQalc: alc s1 $+ alc f = Some (alc s2))
    : s1 $+ f = Some s2.
  Proof using Type.
    exact: (proj2 (state_sum_spec s1 f s2)
              (conj EQst (conj EQsg (conj EQhp EQalc)))).
  Qed.

  (* Discarding the store *)

  Lemma mk_state_opt_self (s: Sm):
    mk_state_opt (store s) (scnt s) (heap s) (alc s) = Some s.
  Proof using Type.
    apply (proj2 (mk_state_opt_some (store s) (scnt s) (heap s) (alc s) s)).
    repeat split.
  Qed.

  Lemma mk_state_opt_of_dominates
    (st: @m_st Sm) (sg: SCnt Sm) (h: @m_hp Sm) (c: Alc Sm)
    (DOMs: dominates st sg) (DOMh: dominates h c)
    : mk_state_opt st sg h c = Some (mk_state st sg h c DOMs DOMh).
  Proof using Type.
    apply (proj2 (mk_state_opt_some st sg h c (mk_state st sg h c DOMs DOMh))).
    repeat split;
      [ apply store_mk_state | apply scnt_mk_state
      | apply heap_mk_state | apply alc_mk_state ].
  Qed.

  Lemma state_pop_n_some {n} {s s': Sm}:
    state_pop_n n s = Some s'
    <-> NExt.iter_opt (fun st => pop st) n (store s) = Some (store s')
        /\ scnt s' = scnt s /\ heap s' = heap s /\ alc s' = alc s.
  Proof using Type.
    unfold state_pop_n.
    destruct (NExt.iter_opt (fun st => pop st) n (store s)) as [ st | ] eqn:E.
    - split.
      + intros MK.
        destruct (proj1 (mk_state_opt_some st (scnt s) (heap s) (alc s) s') MK)
          as ( EST & ESG & EHP & EALC ).
        exact (conj (f_equal Some (eq_sym EST)) (conj ESG (conj EHP EALC))).
      + intros ( EST & ESG & EHP & EALC ).
        injection EST as EST.
        exact (proj2 (mk_state_opt_some st (scnt s) (heap s) (alc s) s')
                 (conj (eq_sym EST) (conj ESG (conj EHP EALC)))).
    - split; [ discriminate | intros ( EST & _ ); discriminate EST ].
  Qed.

  Lemma state_pop_n_of_dominates [n] [s: Sm] [st']
    (DOM: dominates st' (scnt s))
    (POP: NExt.iter_opt (fun st => pop st) n (store s) = Some st'):
    state_pop_n n s
    = Some (mk_state st' (scnt s) (heap s) (alc s) DOM (state_heap_dominates s)).
  Proof using Type.
    unfold state_pop_n.
    rewrite POP.
    exact (mk_state_opt_of_dominates _ _ _ _ DOM (state_heap_dominates s)).
  Qed.

  Lemma state_pop_n_0 (s: Sm): state_pop_n 0 s = Some s.
  Proof using Type.
    unfold state_pop_n.
    rewrite NExt.iter_opt_0.
    exact (mk_state_opt_self s).
  Qed.

  Lemma state_pop_n_succ_r [n] [s: Sm] [st'] (POP: pop (store s) = Some st'):
    state_pop_n (N.succ n) s = state_pop_n n (state_pop s POP).
  Proof using Type.
    unfold state_pop_n.
    rewrite NExt.iter_opt_succ_r POP store_state_pop scnt_state_pop heap_state_pop alc_state_pop.
    reflexivity.
  Qed.

  Lemma state_pop_n_succ_r_None [n] [s: Sm] (POP: pop (store s) = None):
    state_pop_n (N.succ n) s = None.
  Proof using Type.
    unfold state_pop_n.
    rewrite NExt.iter_opt_succ_r POP.
    reflexivity.
  Qed.

  Lemma push_of_cget (s: Sm) (v: value (@ptr_t Sm)) nm
    (CGET: cget (scnt s) = Some nm)
    : exists st sg n, push (store s) (scnt s) v = Some (st, sg, n).
  Proof using Type.
    apply (proj1 (push_some (store s) (scnt s) v)).
    exists nm; split; [ exact CGET | ].
    intros o v' SUB.
    pose proof (state_store_dominates s _ _ _ SUB CGET) as LT.
    rewrite mkAddr_block in LT.
    lia.
  Qed.

  Definition discard_store (s: Sm): Sm :=
    mk_state $0 $0 (heap s) (alc s) (dominates_emp _) (state_heap_dominates s).

  Lemma discard_store_proj (s: Sm):
    store (discard_store s) = $0
    /\ scnt (discard_store s) = $0
    /\ heap (discard_store s) = heap s
    /\ alc (discard_store s) = alc s.
  Proof using Type.
    repeat split;
      [ exact: (store_mk_state _ _ _ _ _ _)
      | exact: (scnt_mk_state _ _ _ _ _ _)
      | exact: (heap_mk_state _ _ _ _ _ _)
      | exact: (alc_mk_state _ _ _ _ _ _) ].
  Qed.

End StateOps.

Arguments set_store {Sm} _ _.
Arguments set_store_no_cnt {Sm} _ _.
Arguments emp_with_alc {Sm} sc a.

#[global] Hint Resolve state_heap_dominates : seplog.
#[global] Hint Resolve state_store_dominates : seplog.
#[global] Hint Resolve state_ext | 20 : seplog.
#[global] Hint Resolve <- mk_state_opt_some : seplog.

#[global] Hint Rewrite @store_mk_state @scnt_mk_state @heap_mk_state @alc_mk_state
  : seplog.
#[global] Hint Rewrite @store_set_store @scnt_set_store @heap_set_store @alc_set_store
  : seplog.
#[global] Hint Rewrite @store_set_store_no_cnt @scnt_set_store_no_cnt
  @heap_set_store_no_cnt @alc_set_store_no_cnt : seplog.
#[global] Hint Rewrite @store_state_push @scnt_state_push @heap_state_push @alc_state_push
  : seplog.
#[global] Hint Rewrite @store_state_pop @scnt_state_pop @heap_state_pop @alc_state_pop
  : seplog.
#[global] Hint Rewrite @store_state_mutate_store @scnt_state_mutate_store
  @heap_state_mutate_store @alc_state_mutate_store : seplog.
#[global] Hint Rewrite @store_state_mutate_heap @scnt_state_mutate_heap
  @heap_state_mutate_heap @alc_state_mutate_heap : seplog.
#[global] Hint Rewrite @store_state_alloc @scnt_state_alloc @heap_state_alloc
  @alc_state_alloc : seplog.
#[global] Hint Rewrite @store_state_free @scnt_state_free @heap_state_free @alc_state_free
  : seplog.
#[global] Hint Rewrite @store_emp @scnt_emp @heap_emp @alc_emp : seplog.
#[global] Hint Rewrite @store_emp_with_alc @scnt_emp_with_alc
  @heap_emp_with_alc @alc_emp_with_alc : seplog.
