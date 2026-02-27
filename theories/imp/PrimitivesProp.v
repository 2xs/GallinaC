From Imp Require Export Primitives Monad.
From Imp Require Import Store Heap.

Section Props.
  Context {St: Store}.
  Context {Hp: Heap}.

  Lemma read_var_eq_state {MS}: forall nm s v s', @read_var St Hp MS nm s = Some (Success (v, s')) -> s' = s.
  Proof using St Hp.
    intros nm s v s' Hread_var.
    unfold read_var in Hread_var.
    cbn in Hread_var.
    destruct (Store.lookup (Primitives.store s) nm) eqn:Hlookup; [ | discriminate ].
    now destruct (decode m); inversion Hread_var.
  Qed.

  Lemma read_ptr_eq_state {MS}: forall ptr s v s', @read_ptr St Hp MS ptr s = Some (Success (v, s')) -> s' = s.
  Proof using St Hp.
    intros ptr s v s' Hread_ptr.
    unfold read_ptr in Hread_ptr.
    cbn in Hread_ptr.
    destruct (Heap.lookup (Primitives.heap s) ptr) eqn:Hlookup; [ | discriminate ].
    now destruct (decode m); inversion Hread_ptr.
  Qed.

End Props.
