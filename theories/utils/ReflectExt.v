From Stdlib Require Export Bool.

Definition eqb_of_eq_dec {A: Type} (eq_dec: forall (x y: A), { x = y } + { x <> y }) (x y: A): bool :=
  if eq_dec x y then true else false.

Lemma reflect_of_eq_dec {A: Type} (eq_dec: forall (x y: A), { x = y } + { x <> y }) (x y: A):
  Bool.reflect (x = y) (eqb_of_eq_dec eq_dec x y).
Proof.
  unfold eqb_of_eq_dec.
  destruct (eq_dec x y);
    now constructor.
Qed.
Hint Resolve reflect_of_eq_dec: bool.

Definition eq_dec_of_reflect {A: Type} {eqb: A -> A -> bool} (Hreflect: forall (x y: A), Bool.reflect (x = y) (eqb x y)) (x y: A): { x = y } + { x <> y }.
Proof.
  destruct (Hreflect x y) as [ Heq | Hneq ]; now constructor.
Qed.
Hint Resolve eq_dec_of_reflect: bool.

Definition reflect_refl {A: Type} {eqb: A -> A -> bool} (Hreflect: forall (x y: A), Bool.reflect (x = y) (eqb x y)) (x: A): eqb x x = true.
Proof.
  destruct (Hreflect x x); congruence.
Qed.
Hint Resolve reflect_refl: bool.

Lemma pair_eq_dec {A B: Type}: (forall x y: A, { x = y } + { x <> y }) -> (forall x y: B, { x = y } + { x <> y }) -> forall x y: (A * B), { x = y } + { x <> y }.
Proof.
  intros eq_dec_A eq_dec_B x y.
  destruct x as [ a1 b1 ], y as [ a2 b2 ].
  destruct (eq_dec_A a1 a2); [ subst | constructor; congruence ].
  destruct (eq_dec_B b1 b2); constructor; congruence.
Qed.
Hint Resolve pair_eq_dec: bool.

Definition pair_eqb {A B: Type} (eqbA: A -> A -> bool) (eqbB: B -> B -> bool) (p1 p2: A * B): bool :=
  match p1, p2 with
  | (a1, b1), (a2, b2) =>
      eqbA a1 a2 && eqbB b1 b2
  end.

Lemma pair_eqb_spec {A B: Type} {eqbA eqbB} (eqbA_spec: forall x y, Bool.reflect (x = y) (eqbA x y)) (eqbB_spec: forall x y, Bool.reflect (x = y) (eqbB x y)): forall x y: A * B, Bool.reflect (x = y) (pair_eqb eqbA eqbB x y).
Proof.
  intros [xa xb] [ya yb].
  cbn.
  destruct (eqbA_spec xa ya); [ subst | right; congruence].
  destruct (eqbB_spec xb yb); subst; constructor; congruence.
Qed.
Hint Resolve pair_eqb_spec: bool.

Lemma pair_eqb_refl {A B: Type} {eqbA eqbB} (eqbA_refl: forall x, eqbA x x = true) (eqbB_refl: forall x, eqbB x x = true): forall x: A * B, pair_eqb eqbA eqbB x x = true.
Proof.
  intros [a b]; cbn.
  now rewrite eqbA_refl, eqbB_refl.
Qed.
Hint Resolve pair_eqb_refl: bool.

Lemma eq_dec_refl_if {A: Type} (eq_dec: forall (x y: A), { x = y } + { x <> y }): forall (x: A), (if eq_dec x x then true else false) = true.
  intros x. destruct (eq_dec x x); subst; congruence.
Qed.
Hint Resolve eq_dec_refl_if: bool.

Lemma reflect_sym {A: Type} {eqb: A -> A -> bool} (Hreflect: forall (x y: A), reflect (x = y) (eqb x y)) x y: eqb x y = eqb y x.
Proof.
  destruct (Hreflect x y) as [ Heq1 | Hneq1 ];
    destruct (Hreflect y x) as [ Heq2 | Hneq2 ];
    congruence.
Qed.

Lemma reflect_trans {A: Type} {eqb: A -> A -> bool} (Hreflect: forall (x y: A), reflect (x = y) (eqb x y)) {x y z} (Heqbxy: eqb x y = true) (Heqbyz: eqb y z = true): eqb x z = true.
Proof.
  destruct (Hreflect x y) as [ Heqxy | Hneqxy ];
    destruct (Hreflect y z) as [ Heqyz | Hneqyz ];
    destruct (Hreflect x z) as [ Heqxz | Hneqxz ];
    congruence.
Qed.
