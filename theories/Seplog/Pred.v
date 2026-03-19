From GallinaC.Corec Require Export Sets.
From GallinaC.Utils Require Import Algebra.

Require Export Setoid.
Require Export Relation_Definitions.

Declare Scope state_scope.
Local Open Scope state_scope.

Definition Pred (A:Type) := Setof A.

(* Conjunction *)

Definition inter {A:Type} (P Q : Pred A) : Pred A:=
  fun a => P a /\ Q a.
Hint Unfold inter: seplog.

Infix "&&" := inter (at level 40, left associativity): state_scope.

Lemma inter_pair {A s} (P Q: Pred A): P s -> Q s -> (P && Q) s.
Proof.
  intros; now constructor.
Qed.
Hint Resolve inter_pair: seplog.

Lemma inter_split [A s] (P: Pred A): (P && P) s -> P s.
Proof.
  now intros (HP & _).
Qed.
Hint Extern 4 => apply inter_split : seplog.

Lemma inter_split_l [A s] (P Q: Pred A): (P && Q) s -> P s.
Proof.
  now intros (HP & _).
Qed.
Hint Extern 4 => apply inter_split_l : seplog.

Lemma inter_split_r [A s] (P Q: Pred A): (P && Q) s -> Q s.
Proof.
  now intros (_ & HQ).
Qed.
Hint Extern 4 => apply inter_split_r : seplog.

Lemma inter_sym {A s} (P Q: Pred A): (P && Q) s -> (Q && P) s.
Proof.
  intros [ HP HQ ]; eauto with seplog.
Qed.
Hint Resolve inter_sym: seplog.

Lemma inter_trans {A s} (P Q R: Pred A): (P && Q) s -> (Q && R) s -> (P && R) s.
Proof.
  intros [ HP HQ ] [ _ HR ]; eauto with seplog.
Qed.
Hint Resolve inter_trans: seplog.

Add Parametric Relation A s : (Pred A) (fun P Q => @inter A P Q s)
  symmetry proved by inter_sym
  transitivity proved by inter_trans
  as inter_rel.

(* Implication *)

Definition impl {A:Type} (P Q : Pred A) : Pred A :=
  fun s => P s -> Q s.

Infix "===>" := impl (at level 70, right associativity): state_scope.

Lemma impl_impl_1 {A s} (P Q: Pred A): (P s -> Q s) -> (P ===> Q) s.
Proof.
  now unfold impl.
Qed.
Hint Resolve impl_impl_1: seplog.

Lemma impl_impl_2 {A s} (P Q: Pred A): (P ===> Q) s -> P s -> Q s.
Proof.
  now unfold impl.
Qed.
Hint Extern 4 => apply impl_impl_2: seplog.

Lemma impl_refl {A s} (P: Pred A): (P ===> P) s.
Proof.
  now auto.
Qed.
Hint Resolve impl_refl: seplog.

Lemma impl_trans {A s} (P Q R: Pred A): (P ===> Q) s -> (Q ===> R) s -> (P ===> R) s.
Proof.
  unfold impl; intros; eauto.
Qed.
Hint Resolve impl_trans: seplog.

Add Parametric Relation A s : (Pred A) (fun P Q => @impl A P Q s)
    reflexivity proved by impl_refl
    transitivity proved by impl_trans
    as impl_rel.

(* Equivalence *)

Definition equiv {A: Type} (P Q: Pred A): Pred A :=
  fun s => P s <-> Q s.

Infix "<==>" := equiv (at level 75): state_scope.

Lemma equiv_impl_l {A s} (P Q: Pred A): (P <==> Q) s -> (P ===> Q) s.
Proof.
  now intros [ HPQ _ ].
Qed.
Hint Resolve equiv_impl_l: seplog.

Lemma equiv_impl_r {A s} (P Q: Pred A): (P <==> Q) s -> (Q ===> P) s.
Proof.
  now intros [ _ HQP ].
Qed.
Hint Resolve equiv_impl_r: seplog.

Lemma equiv_refl {A s} (P: Pred A): (P <==> P) s.
Proof.
  now auto.
Qed.
Hint Resolve equiv_refl: seplog.

Lemma equiv_sym {A s} (P Q: Pred A): (P <==> Q) s -> (Q <==> P) s.
Proof.
  intros HPQ.
  constructor; [ intros HQ | intros HP ].
  now eapply HPQ.
  now eapply HPQ.
Qed.
Hint Resolve equiv_sym: seplog.

Lemma equiv_trans {A s} (P Q R: Pred A): (P <==> Q) s -> (Q <==> R) s -> (P <==> R) s.
Proof.
  intros HPQ HQR.
  constructor; [ intros HP | intros HR ].
  now eapply HQR, HPQ.
  now eapply HPQ, HQR.
Qed.
Hint Resolve equiv_trans: seplog.

Add Parametric Relation A s : (Pred A) (fun P Q => @equiv A P Q s)
    reflexivity proved by equiv_refl
    symmetry proved by equiv_sym
    transitivity proved by equiv_trans
    as equiv_rel.

(* Tautology *)

Definition taut {A:Type} (P: Pred A) : Prop :=
  forall s, P s.

Notation "|- P" := (taut P) (at level 80): state_scope.

(* Existential quantification *)

Definition Exis {A B : Type} (P : A -> Pred B) : Pred B :=
  fun s => exists x, P x s.

Notation "'Exists' x .. y , p" :=
  (Exis (fun x => .. (Exis (fun y => p)) ..))
    (at level 200, x closed binder, y closed binder, right associativity).

(* Morphisms *)

Add Parametric Morphism A s : (@inter A)
    with signature (fun P Q => @impl A P Q s ) ==> (fun P Q => @impl A P Q s) ==> (fun P Q => @impl A P Q s) as inter_impl_mor.
Proof.
  unfold impl.
  intros P P' HimplP Q Q' HimplQ [ HP HQ ].
  eauto with seplog.
Qed.

Add Parametric Morphism A s : (@inter A)
    with signature (fun P Q => @equiv A P Q s) ==> (fun P Q => @equiv A P Q s) ==> (fun P Q => @impl A P Q s) as inter_equiv_mor.
Proof.
  intros P P' [ HPP' HP'P ] Q Q' [ HQQ' HQ'Q ] [ HP HQ ].
  constructor; eauto.
Qed.

Add Parametric Morphism A s : (@impl A)
    with signature (fun P Q => @impl A Q P s) ==> (fun P Q => @impl A P Q s) ==> (fun P Q => @impl A P Q s) as impl_impl_mor.
Proof.
  intros P P' HP'P Q Q' HQQ' HPQ HP'; eauto.
Qed.

Add Parametric Morphism A s : (@impl A)
    with signature (fun P Q => @equiv A P Q s) ==> (fun P Q => @equiv A P Q s) ==> (fun P Q => @equiv A P Q s) as impl_equiv_mor.
Proof.
  intros P P' [ HPP' HP'P ] Q Q' [ HQQ' HQ'Q ].
  constructor; [ intros HPQ HP' | intros HQP HQ' ]; eauto.
Qed.

Add Parametric Morphism A s : (@equiv A)
    with signature (fun P Q => @equiv A P Q s) ==> (fun P Q => @equiv A P Q s) ==> (fun P Q => @impl A P Q s) as equiv_impl_mor.
Proof.
  intros P P' [ HPP' HP'P ] Q Q' [ HQQ' HQ'Q ] [ HPQ HQP ].
  constructor; [ intros HP' | intros HQ' ]; eauto.
Qed.

Add Parametric Morphism A s : (@equiv A)
    with signature (fun P Q => @equiv A P Q s) ==> (fun P Q => @equiv A P Q s) ==> (fun P Q => @equiv A P Q s) as equiv_equiv_mor.
Proof.
  intros P P' [ HPP' HP'P ] Q Q' [ HQQ' HQ'Q ].
  constructor; [ intros [ HPQ HQP ] | intros [ HP'Q' HQ'P' ] ];
    constructor; eauto.
Qed.

Add Parametric Morphism A B b : (@Exis A B)
    with signature (fun P Q => forall a, @impl B (P a) (Q a) b) ==> (fun P Q => @impl B P Q b)
      as exists_impl_mor.
Proof.
  unfold impl, Exis.
  intros P P' Himpl [ x HP ].
  exists x.
  eauto.
Qed.

Add Parametric Morphism A B b : (@Exis A B)
    with signature (fun P Q => forall a, @equiv B (P a) (Q a) b) ==> (fun P Q => @equiv B P Q b)
      as exists_equiv_mor.
Proof.
  unfold equiv, Exis.
  intros P P' Hequiv.
  constructor; [ intros [ x HP ] | intros [ x HP' ] ];
    exists x;
    now apply Hequiv.
Qed.

Add Parametric Morphism A: (@taut A)
    with signature (fun P Q => forall s, @equiv A P Q s) ==> iff
      as  taut_equiv_mor.
Proof.
  intros P Q Hequiv.
  split; [ intros H | intros H ]; intros s;
    specialize (Hequiv s);
    specialize (H s);
    destruct Hequiv as [ HPQ HQP ];
    eauto.
Qed.

(* Multi-constructor lemmas *)

Lemma impl_refl_eq {A:Type} (p q : Pred A):
  p = q ->
      |- p ===> q.
Proof.
  intro Heq; now subst.
Qed.
Hint Resolve impl_refl_eq: seplog.

Lemma impl_refl_taut {A: Type} (P: Pred A):
      |- P ===> P.
Proof.
  eauto with seplog.
Qed.
Hint Resolve impl_refl_taut: seplog.

Lemma impl_trans_taut {A:Type} (p q r: Pred A) :
      |- p ===> q -> |- q ===> r -> |- p ===> r.
Proof.
  intros Ht Ht' s Hs.
  now apply Ht', Ht.
Qed.
Hint Resolve impl_trans_taut: seplog.

Lemma impl_antisym {A: Type} s (p q: Pred A):
  (p ===> q) s -> (q ===> p) s -> (p <==> q) s.
Proof.
  intros Ht Ht'.
  constructor;
    eauto with seplog.
Qed.
Hint Resolve impl_antisym: seplog.

Lemma impl_antisym_taut {A:Type} (p q: Pred A) :
      |- p ===> q -> |- q ===> p -> |- p <==> q.
Proof.
  intros Ht Ht'.
  constructor; [ apply Ht | apply Ht' ].
Qed.
Hint Resolve impl_antisym_taut: seplog.

Lemma equiv_refl_eq {A: Type} (p q: Pred A):
  p = q -> |- p <==> q.
Proof.
  intros Heq; now subst.
Qed.
Hint Resolve equiv_refl_eq: seplog.

Lemma equiv_refl_taut {A: Type} (P: Pred A):
      |- P <==> P.
Proof.
  eauto with seplog.
Qed.
Hint Resolve equiv_refl_taut: seplog.

Lemma equiv_sym_taut {A: Type} (P Q: Pred A):
  (|- P <==> Q) -> (|- Q <==> P).
Proof.
  intros H s.
  specialize (H s).
  eauto with seplog.
Qed.
Hint Resolve equiv_sym_taut: seplog.

Lemma equiv_trans_taut {A: Type} (P Q R: Pred A):
  (|- P <==> Q) -> (|- Q <==> R) -> (|- P <==> R).
Proof.
  intros HEPQ HEQR s.
  specialize (HEPQ s) as [ HPQ HQP ].
  specialize (HEQR s) as [ HQR HRQ ].
  constructor; auto.
Qed.
Hint Resolve equiv_trans_taut: seplog.

Lemma Exists_impl {A B: Type} s: forall (p: Pred A) (q: B -> Pred A),
    (Exists x, p ===> q x) s  -> (p ===> Exists x, q x) s.
Proof.
  intros p q Himp Hs.
  unfold impl, Exis,taut in *.
  destruct (Himp) as (x & Himp').
  exists x; eauto with seplog.
Qed.
Hint Resolve Exists_impl: seplog.

Lemma Exists_impl_taut {A B: Type}: forall (p: Pred A) (q: B -> Pred A),
    (|- Exists x, p ===> q x)  -> |- (p ===> Exists x, q x).
Proof.
  intros p q Himp s Hs.
  unfold impl, Exis,taut in *.
  destruct (Himp s) as (x & Himp').
  exists x; eauto.
Qed.
Hint Resolve Exists_impl_taut: seplog.

Lemma skolem_left {A B: Type} s: forall (p: B ->Pred A) (q: Pred A),
    (forall x, (p x ===> q) s) -> ((Exists x, p x) ===> q) s.
Proof.
  intros p q Ha Hm.
  destruct Hm as (x & Hp).
  now apply (Ha x).
Qed.
Hint Resolve skolem_left: seplog.

Lemma skolem_left_taut{A B: Type}: forall (p: B ->Pred A)
                                     (q: Pred A),
    (forall x, |- p x ===> q) -> |- (Exists x, p x) ===> q.
Proof.
  intros p q Ha s Hm.
  destruct Hm as (x & Hp).
  now apply (Ha x).
Qed.
Hint Resolve skolem_left_taut: seplog.

Lemma inst_Exists {A B: Type} s:
  forall (P: B -> Pred A),
  forall x, (P x s) -> (Exists x, P x) s.
Proof.
  intros p x HP.
  now exists x.
Qed.
Hint Resolve inst_Exists: seplog.

Lemma inst_Exists_taut {A B: Type}:
  forall (P: B -> Pred A),
  forall x, |- P x -> |- Exists x, P x.
Proof.
  intros p x HP s.
  now exists x.
Qed.
Hint Resolve inst_Exists_taut: seplog.

Lemma swap_Exists {A B:Type} (p: B -> B -> Pred A):
  |- (Exists x y, p x y) <==> Exists y x, p x y .
Proof.
  apply impl_antisym_taut; intros s Hm; unfold Exis in *;
    destruct Hm as (x & x0 & H); eauto.
Qed.
Hint Resolve swap_Exists: seplog.

Lemma impl_cnj_right {A: Type} s :
  forall (p q r: Pred A),
    (p  ===> q) s -> (p ===> r) s  -> (p ===> q && r) s.
Proof.
  intros p q r Hi1 Hi2 Hs; split;
    [now apply Hi1| now apply Hi2].
Qed.
Hint Resolve impl_cnj_right: seplog.

Lemma impl_cnj_right_taut {A: Type} :
  forall (p q r: Pred A),
    |-  p  ===> q -> |- p ===>  r  -> |- p ===> q && r.
Proof.
  intros p q r Hi1 Hi2 s Hs; split;
    [now apply Hi1| now apply Hi2].
Qed.
Hint Resolve impl_cnj_right_taut: seplog.
