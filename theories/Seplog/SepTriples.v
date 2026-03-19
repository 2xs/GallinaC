From Stdlib Require Import FunctionalExtensionality PropExtensionality Nat Lia.
From GallinaC.Seplog Require Export PrimitivesTriples StateAssertion.
Local Open Scope state_scope.


Lemma sep_weaken : forall (S A : Type) (m : program S A)
         (P Q : Pred S) (R : A -> Pred S),
       {{ Q }} m {{ R }} ->
       (|- P ===> Q) -> {{ P }} m {{ R }}.
Proof.
intros.
eapply weaken; eauto.
Qed.


Lemma sep_strengthen
  {S A : Type} (m : program S A) (P : Pred S) (Q R : A -> Pred S) :
{{ P }} m {{ Q }} -> (forall a, |- Q a ===> R a ) -> {{ P }} m {{ R }}.
Proof.
intros.
eapply strengthen; eauto.
Qed.


Local Open Scope program_scope.

Lemma  sep_bind_rule
  {S A B : Type} (m : program S A) (f : A -> program S B)
  (P : S -> Prop) (Q : A -> Pred S) (R : B -> Pred S) :
(forall a, {{ Q a }} f a {{ R }}) -> {{ P }} m {{ Q }} ->
{{ P }} do x <- m; f x {{ R }}.
Proof.
eapply bind_rule; eauto.
Qed.



Lemma sep_seq_rule
  {S A B : Type} (m1 : program S A) (m2 : program S B)
  (P : Pred S) (Q : Pred S) (R : B -> Pred S) :
{{ Q }} m2 {{ R }} -> {{ P }} m1 {{ fun _ s => Q s }} ->
{{ P }} m1;; m2 {{ R }}.
Proof.
eapply seq_rule; eauto.
Qed.


Lemma sep_ret_triple {S A : Type} (a : A) (P : A -> Pred S) :
{{ P a }} ret a {{ P }}.
Proof.
apply ret_triple.
Qed.

Lemma sep_fail_triple{S A: Type}(P: A -> Pred S):
{{ fun _ => False}} fail {{P}}.
Proof.
apply fail_triple.
Qed.

Lemma sep_if_rule
  {S A : Type} (cond : program S bool) (m1 m2 : program S A)
  (P : Pred S) (Q : bool -> Pred S) (R : A -> Pred S) :
{{ P }} cond {{ Q }} -> {{ Q true}} m1 {{ R }} -> {{ Q false}} m2 {{ R }} ->
{{ P }} If cond then m1 else m2 {{ R }}.
Proof.
eapply if_rule; eauto.
Qed.


Local Open Scope state_scope.

Lemma sep_while_rule {S}
   (cond : program S bool) (body : program S unit)
  (I : bool -> Pred S) :
{{ Exists b, I b }}
 cond
{{ I }} ->
{{ I true }}
  body
{{ fun _ => Exists b, I b }} ->
{{ Exists b, I b }}
  while cond body
{{ fun _ => I false }}.
Proof.
eapply while_rule; eauto.
Qed.

(* Lemma sep_read_reg1_triple {S} (P : nat -> Pred S) : *)
(* {{Exists r, (reg1= r) ** (P r)}} read_reg1 {{ P }}. *)
(* Proof. *)
(* rewrite pre_read_reg1_eq. *)
(* apply read_reg1_triple. *)
(* Qed. *)


(* Lemma sep_read_reg2_triple (P : nat -> Pred State) : *)
(* {{ Exists r, (reg2= r) ** (P r)}} read_reg2 {{ P }}. *)
(* Proof. *)
(* rewrite pre_read_reg2_eq. *)
(* apply read_reg2_triple. *)
(* Qed. *)


(* Lemma sep_write_reg1_triple(r:nat) *)
(* (Q: unit -> Pred State): *)
(* {{ *)
(* [reg1=r]-* (Q tt) *)
(* }} *)
(* write_reg1 r *)
(* {{ *)
(*  Q *)
(* }}. *)
(* Proof. *)
(* apply write_reg1_triple. *)
(* Qed. *)


(* Lemma sep_write_reg2_triple(r:nat) *)
(* (Q: unit -> Pred State): *)
(* {{ *)
(* [reg2=r]-* (Q tt) *)
(* }} *)
(* write_reg2 r *)
(* {{ *)
(*  Q *)
(* }}. *)
(* Proof. *)
(* apply write_reg2_triple. *)
(* Qed. *)

(**
Lemma fw_write_reg2_triple(r:nat)
(P: Pred State):
{{
P
}}
write_reg2 r
{{
fun _ => (reg2= r) ** P
}}.
Proof.
 eapply  sep_weaken;  [apply sep_write_reg2_triple| ].
cbn.
Admitted.
*)

(* Lemma sep_read_addr_triple (addr : nat) (P : nat -> Pred S) : *)
(*   {{ *)
(*     Exists a, (addr ---> a) && (P a) *)
(*      }} *)
(*    read_addr addr *)
(*    {{ P }}. *)
(* Proof. *)
(* rewrite pre_read_addr_eq. *)
(* apply read_addr_triple. *)
(* Qed. *)


(* Lemma sep_write_addr_triple (a:addr) (v : nat) (P : unit -> Pred State) : *)
(* {{ *)
(* (Exists x, (a |~> x))**((a |~> v) -* (P tt)) *)
(* }} *)
(* write_addr a v *)
(* {{ P }}. *)
(* Proof. *)
(* rewrite  write_addr_wp_eq. *)
(* apply write_addr_triple. *)
(* Qed. *)


(* Lemma sep_deref_succ_reg1_triple (P : nat -> Pred State) : *)
(* {{ (Exists (a r:nat), (reg1= r) ** *)
(*                         ((r + 1) ---> a && P a)) }} *)
(*   deref_succ_reg1 *)
(* {{ P }}. *)
(* Proof. *)
(* unfold deref_succ_reg1. *)
(* eapply bind_rule. *)
(* - intro x. *)
(*   apply sep_read_addr_triple. *)
(* - eapply sep_weaken; [apply read_reg1_triple | ]. *)
(*   rewrite <-  wp_deref_succ_reg1_eq. *)
(*   now intros s Hm. *)
(* Qed. *)
