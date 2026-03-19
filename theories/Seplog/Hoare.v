From GallinaC.Imp Require Export Monad While.

Create HintDb seplog.

Local Open Scope program_scope.

Definition partial_exception_hoare
  {S A : Type} (P : S -> Prop) (m : program S A)
  (Q : A -> S -> Prop) : Prop :=
  forall s,
    P s -> match m s with
           | Some (Success (a, s')) => Q a s'
           | Some Failure => False
           | None =>  True
           end.

Notation "{{ P }} m {{ Q }}" :=
  (partial_exception_hoare P m Q)
    (at level 90,
      format "'[' '[' {{  P  }}  ']' '/  ' '[' m ']' '['  {{  Q  }} ']' ']'"
    ).

Lemma weaken
  {S A : Type} (m : program S A) (P Q : S -> Prop) (R : A -> S -> Prop) :
  {{ Q }} m {{ R }} -> (forall s, P s -> Q s) -> {{ P }} m {{ R }}.
Proof.
  intros Hm Himpl s Hp.
  destruct (m s) as [ [(a & s') | ] | ] eqn:Hms;
    specialize (Hm _ (Himpl _ Hp)) as Hm';
    now rewrite Hms in Hm'.
Qed.

Lemma strengthen
  {S A : Type} (m : program S A) (P : S -> Prop) (Q R : A -> S -> Prop) :
  {{ P }} m {{ Q }} -> (forall a s, Q a s -> R a s) -> {{ P }} m {{ R }}.
Proof.
  intros Hm Himpl s Hp.
  destruct (m s) as [ [(a & s') | ] | ] eqn:Hms;
    specialize (Hm _ Hp) as Hm';
    rewrite Hms in Hm'; auto.
Qed.

Lemma bind_rule
  {S A B : Type} (m : program S A) (f : A -> program S B)
  (P : S -> Prop) (Q : A -> S -> Prop) (R : B -> S ->  Prop) :
  (forall a, {{ Q a }} f a {{ R }}) -> {{ P }} m {{ Q }} ->
  {{ P }} do x <- m; f x {{ R }}.
Proof.
  intros Hf Hm s Hp.
  unfold bind.
  destruct  (m s) as [ [(a & s') | ] | ] eqn:Hms; auto.
  - destruct  (f a s') as [ [(a' & s'') | ] | ] eqn:Hfas; auto;
      specialize (Hm _ Hp);
      rewrite Hms in Hm;
      specialize (Hf _ _ Hm);
      now rewrite Hfas in Hf.
  - specialize (Hm _ Hp).
    now rewrite Hms in Hm.
Qed.

Lemma seq_rule
  {S A B : Type} (m1 : program S A) (m2 : program S B)
  (P : S -> Prop) (Q : S -> Prop) (R : B -> S ->  Prop) :
  {{ Q }} m2 {{ R }} -> {{ P }} m1 {{ fun _ s => Q s }} ->
  {{ P }} m1;; m2 {{ R }}.
Proof.
  intros Hm2 Hm1.
  exact (bind_rule m1 (fun _ => m2) P (fun _ s => Q s) R (fun _ => Hm2) Hm1).
Qed.

Lemma ret_triple {S A : Type} (a : A) (P : A -> S -> Prop) :
  {{ fun s => P a s }} ret a {{ P }}.
Proof.
  now intros s Hp.
Qed.
Hint Resolve ret_triple: seplog.

Lemma get_triple {S : Type} (P : S -> S -> Prop) :
  {{ fun s => P s s }} get {{ P }}.
Proof.
  now intros s Hp.
Qed.
Hint Resolve get_triple: seplog.

Lemma put_triple {S : Type} (s : S) (P : unit -> S -> Prop) :
  {{ fun _ => P tt s }} put s {{ P }}.
Proof.
  now intros s' Hp.
Qed.
Hint Resolve put_triple: seplog.

Lemma modify_triple {S : Type} (f : S -> S) (P : unit -> S ->  Prop) :
  {{ fun s => P tt (f s) }} modify f {{ P }}.
Proof.
  unfold modify.
  eapply bind_rule.
  - intro s.
    apply put_triple.
  - eapply weaken; eauto with seplog.
Qed.
Hint Resolve modify_triple: seplog.

Lemma fail_triple{S A: Type}(P: A -> S -> Prop):
  {{ fun _ => False}} fail {{P}}.
Proof.
  now intros x Hf.
Qed.
Hint Resolve fail_triple: seplog.

Lemma if_rule
  {S A : Type} (cond : program S bool) (m1 m2 : program S A)
  (P : S -> Prop) (Q : bool -> S -> Prop) (R : A -> S -> Prop) :
  {{ P }} cond {{ Q }} -> {{ Q true}} m1 {{ R }} -> {{ Q false}} m2 {{ R }} ->
  {{ P }} If cond then m1 else m2 {{ R }}.
Proof.
  intros Hcond Hm1 Hm2.
  eapply bind_rule.
  - intros [ | ].
    + exact Hm1.
    + exact Hm2.
  - exact Hcond.
Qed.
Hint Resolve if_rule: seplog.

Lemma while_fuel_rule
  (fuel : nat) {S : Type} {cond : program S bool} {body : program S unit}
  {I : bool -> S -> Prop}
  (COND: {{ fun s => exists b, I b s }} cond {{ I }})
  (BODY: {{ I true }} body {{ fun _ s' => exists b, I b s' }})
  : {{ fun s => exists b, I b s }} while_fuel fuel cond body {{ fun _ s' => I false s' }}.
Proof.
  induction fuel as [ | fuel IH];
    [now intros s (b & Hi) |].
  rewrite while_fuel_fixpoint.
  eapply if_rule.
  - exact COND.
  - eapply seq_rule; eassumption.
  - eapply weaken; auto with seplog.
Qed.

Lemma while_rule
  {S : Type} {cond : program S bool} {body : program S unit}
  {I : bool -> S -> Prop}
  (COND: {{ fun s => exists b, I b s }} cond{{ I }})
  (BODY: {{ I true }} body {{ fun _ s' => exists b, I b s' }})
  : {{ fun s => exists b, I b s }}
      while cond body
      {{ fun _ s' => I false s' }}.
Proof.
  intros s Hex.
  remember (while cond body) as w.
  destruct (w s) eqn:Hws; auto.
  subst.
  rewrite while_fuel_while_some in Hws.
  destruct Hws as (fuel & Hfuel).
  destruct o; [destruct p|].
  - specialize
      (while_fuel_rule fuel COND BODY s Hex) as Hf.
    now rewrite Hfuel in Hf.
  - eapply while_fuel_rule  with (fuel := fuel) in COND;
      eauto with seplog.
    specialize (COND s Hex).
    now rewrite Hfuel in COND.
Qed.
