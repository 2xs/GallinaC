From Stdlib Require Import Arith Psatz.
From Stdlib Require Export List SetoidList.
Export ListNotations.

From compcert.lib Require Coqlib.

Lemma cons_self_neq [A] [l] [a: A] (EQ: a::l = l): False.
  revert a EQ.
  induction l; cbn; intros.
  discriminate.
  inversion EQ.
  eapply IHl, H1.
Qed.

Lemma In_neq_hd [A] [l: list A] [a a'] (IN: In a (a'::l)) (NE: a <> a'): In a l.
Proof.
  destruct IN; congruence.
Qed.

Lemma InA_In [A: Type] (a: A) l: InA eq a l <-> In a l.
Proof.
  induction l as [ | a' l];
    split; intros H; inversion H; subst;
    first [ now left | now right; apply IHl ].
Qed.

Lemma map_In_inj {A B: Type} {f: A -> B} {l: list A} {a}
  (f_inj: forall a1 a2, f a1 = f a2 -> a1 = a2)
  (HIn: In (f a) (map f l))
  : In a l.
Proof.
  induction l; [ contradiction | ].
  cbn in HIn.
  destruct HIn as [ Heq | HIn ]; constructor; now auto.
Qed.

Fixpoint replaceA {A B: Type} {eqA: A -> A -> Prop} {eqA_equiv: Equivalence eqA} {eqA_dec: forall x y, {eqA x y} + {~eqA x y}} (k: A) (v: B) (l: list (A*B)): list (A*B) :=
  match l with
  | [] => []
  | (x,y)::l => (if eqA_dec x k then (x,v) else (x,y))::(@replaceA A B eqA eqA_equiv eqA_dec k v l)
  end.

Fixpoint replace {A B: Type} {eq_dec: forall x y, {x = y} + {x <> y}} (k: A) (v: B) (l: list (A*B)) :=
  match l with
  | [] => []
  | (x, y)::l => if eq_dec x k then (x, v)::l else ((x,y)::(@replace A B eq_dec k v l))
  end.

Fixpoint replace_insert {A B: Type} {eq_dec: forall x y, {x = y} + {x <> y}} (k: A) (v: B) (l: list (A*B)) :=
  match l with
  | [] => [(k,v)]
  | (x, y)::l => if eq_dec x k then (x, v)::l else ((x,y)::(@replace_insert A B eq_dec k v l))
  end.

Fixpoint replace_nth [A: Type] (n: nat) (a: A) (l: list A) {struct n}: list A :=
  match n, l with
  | 0, _::l => a::l
  | S n, x::l => x::(replace_nth n a l)
  | _, [] => []
  end.

Fixpoint remove_bind {A B: Type} {eqA: A -> A -> Prop} (eqA_dec: forall x y, {eqA x y} + {~eqA x y}) (k: A) (l: list (A*B)): list (A*B) :=
  match l with
  | [] => []
  | (x,y)::l =>
      if eqA_dec x k then
        @remove_bind A B eqA eqA_dec k l
      else
        (x,y)::(@remove_bind A B eqA eqA_dec k l)
  end.

(* Tricky variants of In* since the terminal case must be strict equality, but the recursive case requires inequality only on the first term *)
Inductive AbsIn {A: Type}: A -> list A -> Prop :=
| AbsIn_nil: forall a, AbsIn a []
| AbsIn_cons: forall a a' l, a <> a' -> AbsIn a l -> AbsIn a (a'::l)
.
Inductive SIn {A: Type}: A -> list A -> Prop :=
| SIn_hd: forall a l, AbsIn a l -> SIn a (a::l)
| SIn_cons: forall a a' l, a <> a' ->  SIn a l -> SIn a (a'::l)
.

Inductive SIns {A: Type}: list A -> Prop :=
| SIns_nil: SIns []
| SIns_cons: forall a l, AbsIn a l -> SIns l -> SIns (a::l)
.

Inductive AbsBind {A B: Type}: A -> list (A*B) -> Prop :=
| AbsBind_nil: forall x, AbsBind x []
| AbsBind_cons: forall x x' y' l, x <> x' -> AbsBind x l -> AbsBind x ((x',y')::l)
.
Inductive BindIn {A B: Type}: A -> B -> list (A*B) -> Prop :=
| BindIn_hd: forall x y l, BindIn x y ((x,y)::l)
| BindIn_tl: forall x y l x' y', x <> x' -> BindIn x y l -> BindIn x y ((x', y')::l)
.
Inductive SBindIn {A B: Type}: A -> B -> list (A*B) -> Prop :=
| SBindIn_hd: forall x y l, AbsBind x l -> SBindIn x y ((x,y)::l)
| SBindIn_tl: forall x y l x' y', x <> x' -> SBindIn x y l -> SBindIn x y ((x', y')::l)
.

Inductive SBinds {A B: Type}: list (A*B) -> Prop :=
| SBinds_nil: SBinds []
| SBinds_cons: forall a b l, AbsBind a l -> SBinds l -> SBinds ((a,b)::l)
.

Inductive AbsBind2 {A B: Type}: A -> B -> list (A*B) -> Prop :=
| AbsBind2_nil: forall a b, AbsBind2 a b []
| AbsBind2_cons: forall a a' b b' l, a <> a' -> b <> b' -> AbsBind2 a b l -> AbsBind2 a b ((a',b')::l)
.

Inductive SBinds2 {A B: Type}: list (A*B) -> Prop :=
| SBinds2_nil: SBinds2 []
| SBinds2_cons: forall a b l, AbsBind2 a b l -> SBinds2 l -> SBinds2 ((a,b)::l)
.

Lemma AbsIn_In_contra {A: Type} {l: list A} {a} (HAbsIn: AbsIn a l) (HIn: In a l): False.
Proof.
  induction HAbsIn; [ contradiction | ].
  inversion HIn; subst; now auto.
Qed.

Lemma AbsIn_not_In {A: Type} (l: list A): forall a, AbsIn a l <-> ~In a l.
Proof.
  induction l; [ now intros; split; intros H; auto; constructor  | intros; split; intros H ].
  - intros contra.
    inversion H; subst.
    eapply IHl; [ eauto | destruct contra; [ congruence | assumption ] ].
  - constructor; [ | apply IHl ];
      intros contra; subst;
      now apply H; now constructor.
Qed.

Lemma SIns_tl_neq {A: Type}: forall (l: list A) a a', SIns (a::l) -> In a' l -> a' <> a.
Proof.
  induction l as [ | a l ]; [ cbn; intros; contradiction | ].
  cbn.
  intros a0 a' HSIns [ Heq | HIn ].
  - subst.
    inversion HSIns; subst.
    intros contra; subst.
    now inversion H1; subst.
  - inversion HSIns; subst.
    inversion H1; subst.
    inversion H2; subst.
    eapply IHl; [ constructor; eauto | eauto ].
Qed.

Lemma SIns_In {A: Type} {l: list A} {a} (HSIns: SIns l) (HIn: In a l): SIn a l.
Proof.
  induction l; [ contradiction | ].
  inversion HSIns; subst.
  inversion HIn; subst.
  - now left.
  - right; auto.
    intros eq; subst.
    eapply SIns_tl_neq; [ apply HSIns | eauto | eauto ].
Qed.

Lemma SBinds_tl_neq {A B: Type}: forall (l: list (A*B)) a b a' b', SBinds ((a,b)::l) -> In (a',b') l -> a' <> a.
Proof.
  induction l as [ | [ a b ] l ]; [ cbn; intros; contradiction | ].
  cbn.
  intros a0 b0 a' b' HSBinds [ Heq | HIn ].
  - inversion Heq; subst; clear Heq.
    inversion HSBinds as [ | ?a ?b ?l ?HAbsBind ?HSBinds' ]; subst.
    inversion HAbsBind as [ | ?a ?a ?b ?l ?Hneq ?HAbsBind' ]; subst.
    now symmetry.
  - inversion HSBinds as [ | ?a ?b ?l HAbsBind ?HSBinds' ]; subst.
    inversion HAbsBind as [ | ?a ?a ?b ?l ?Hneq ?HAbsBind' ]; subst.
    inversion HSBinds' as [ | ?a ?b ?l ?HAbsBind'' ?HSBinds'' ]; subst.
    eapply IHl with (b := b0).
    econstructor; auto.
    apply HIn.
Qed.

Lemma AbsBind_In_False
  {A B: Type} {a b} {l: list (A*B)}
  (HAbsBind: AbsBind a l)
  (HIn: In (a,b) l)
  : False.
Proof.
  induction l as [ | [ a' b' ] l ]; [ contradiction | ].
  inversion HAbsBind as [ | ?x ?x' ?y' ?l Hneq HAbsBind']; subst.
  destruct HIn as [ Heq | ]; [ inversion Heq; subst; contradiction | auto ].
Qed.

Lemma NoDup_map_fst_AbsBind [A B: Type] [l: list (A*B)] [a b] (NODUP: NoDup (map fst ((a,b)::l))): AbsBind a l.
Proof.
  induction l as [ | [ a' b' ] l ]; [ constructor | right ].
  - inversion NODUP; subst.
    intros contra; subst a'; apply H1.
    now left.
  - apply IHl.
    cbn in *.
    constructor.
    + intros contra.
      inversion NODUP; subst.
      apply H1.
      now right.
    + inversion NODUP; subst.
      now inversion H2; subst.
Qed.

Lemma SBinds_same_In_eq
  {A B: Type} {a b1 b2} {l: list (A*B)}
  (HSBinds: SBinds l)
  (HIn1: In (a, b1) l) (HIn2: In (a, b2) l)
  : b2 = b1.
Proof.
  induction l as [ | [ a' b' ] l ]; [ contradiction | ].
  inversion HSBinds as [ | ?a ?b ?l ?HAbsBind ?HSBinds' ]; subst.
  cbn in HIn1, HIn2.
  specialize (IHl HSBinds').
  destruct HIn1 as [ Heq | HIn1 ]; [ inversion Heq; subst; clear Heq | specialize (IHl HIn1) ].
  - destruct HIn2 as [ Heq | HIn2 ]; [ inversion Heq; subst; clear Heq | ].
    auto.
    exfalso; eapply AbsBind_In_False; now eauto.
  - destruct HIn2 as [ Heq | HIn2 ]; [ inversion Heq; subst; clear Heq | ].
    exfalso; eapply AbsBind_In_False; now eauto.
    auto.
Qed.

Lemma SBinds_In {A B: Type} {a b} {l: list (A*B)}: SBinds l -> In (a,b) l -> SBindIn a b l.
Proof.
  revert a b.
  induction l as [ | [ a b ] l IHl ]; [ cbn; intros; contradiction | ].
  cbn.
  intros a' b' HSBinds HIn.
  inversion HSBinds as [ | ?a ?b ?l HAbsBind HSBinds' ]; subst.
  destruct HIn as [ Heq | HIn ].
  - inversion Heq; subst; clear Heq.
    now constructor.
  - right; [ | now eapply IHl ].
    eapply SBinds_tl_neq; [ apply HSBinds | apply HIn ].
Qed.
Hint Resolve SBinds_In: datatypes.

Lemma SBinds_In_tl [A B: Type] [l: list (A * B)] [a b b'] (SBINDS: SBinds ((a,b)::l)) (IN: In (a, b') ((a, b)::l)): b' = b.
Proof.
  inversion SBINDS; subst; inversion IN; subst.
  congruence.
  exfalso; eapply AbsBind_In_False; eauto.
Qed.

Lemma NoDup_SBinds [A B: Type] [l: list (A * B)] (NODUP: NoDup (map fst l)): SBinds l.
Proof.
  induction l as [ | [ a b ] l ]; constructor.
  - eapply NoDup_map_fst_AbsBind; apply NODUP.
  - inversion NODUP; subst.
    now apply IHl.
Qed.

Lemma SIns_NoDupA {A: Type} {l: list A}: SIns l <-> SetoidList.NoDupA Logic.eq l.
Proof.
  induction l as [ | a l ]; [ split; intros; constructor | ].
  split; intros H; inversion H; subst.
  all: constructor; [ | now apply IHl ].
  now intros contra; eapply AbsIn_In_contra; [ eauto | apply InA_In; eauto ].
  now apply AbsIn_not_In;
    intros contra; apply H2, InA_In.
Qed.

Lemma AbsBind_AbsIn {A B: Type} {l: list (A*B)} {a b} (Abs: AbsBind a l): AbsIn (a,b) l.
Proof.
  induction Abs; constructor; auto.
  congruence.
Qed.

Lemma SBinds_SIns {A B: Type} {l: list (A*B)} (HSBinds: SBinds l): SIns l.
Proof.
  induction HSBinds; constructor.
  now apply AbsBind_AbsIn.
  auto.
Qed.

Lemma SBinds_NoDupA_fst {A B: Type} {l: list (A*B)}
  (eq_dec: forall (x y: A), {x = y} + {x <> y})
  (HSBinds: SBinds l):
  SetoidList.NoDupA (fun p p' => (fst p) = (fst p')) l.
Proof.
  induction HSBinds as [ | a b l HAbsBind HSBinds ]; constructor; auto.
  intros contra.
  revert a b HAbsBind contra.
  induction l as [ | [ a' b' ] l ]; intros.
  now inversion contra.
  inversion HAbsBind; subst.
  inversion contra as [ [ ?a' ?b' ] ?l ?Heq | [ ?a' ?b' ] ?l ?HInA' ]; subst.
  now cbn in Heq.
  eapply IHl; eauto.
  now inversion HSBinds.
  now inversion IHHSBinds.
Qed.

Lemma SBindIn_BindIn {A B: Type} {a b} {l: list (A*B)}: SBindIn a b l -> BindIn a b l.
Proof.
  revert a b.
  induction l as [ | [ a' b' ] l IHl ]; [ intros a b HIn; now inversion HIn | ].
  intros a b HSBindIn.
  inversion HSBindIn as [ ?a ?b ?l ?HAbsBind | ?a ?b ?l ?a' ?b' ?Hneq ?HSBindIn ];
    subst;
    constructor; now eauto.
Qed.
Hint Resolve SBindIn_BindIn: datatypes.

Lemma BindIn_In {A B: Type} {a b} {l: list (A*B)}: BindIn a b l -> In (a,b) l.
Proof.
  revert a b.
  induction l as [ | [ a' b' ] l IHl ]; [ intros a b HIn; now inversion HIn | ].
  intros a b HBindIn.
  inversion HBindIn as [ ?a ?b ?l | ?a ?b ?l ?a' ?b' ?Hneq ?HBindIn ];
    subst;
    constructor; now eauto.
Qed.
Hint Resolve BindIn_In: datatypes.

Lemma BindIn_fun: forall {A B: Type} (a: A) (b b': B) l, BindIn a b l -> BindIn a b' l -> b' = b.
Proof.
  intros A B a b b' l HBindIn.
  revert b'.
  induction HBindIn.
  - intros b' HBindIn'.
    inversion HBindIn'; congruence.
  - intros b' HBindIn'.
    inversion HBindIn'; subst; try (congruence).
    now apply IHHBindIn.
Qed.
Hint Resolve BindIn_fun: datatypes.

Lemma BindIn_findA_reflect_eq
  {A B: Type} {a: A} {b: B} {l} {eqb}
         (reflect: forall x y, Bool.reflect (x = y) (eqb x y))
         (HBindIn: BindIn a b l):
    findA (eqb a) l = Some b.
Proof.
  induction HBindIn; cbn.
  - now destruct (reflect x x).
  - now destruct (reflect x x').
Qed.

Lemma AbsBind_map_fst_AbsIn {A B: Type} {l: list (A * B)} {a} (HAbsBind: AbsBind a l): AbsIn a (map fst l).
Proof.
  induction HAbsBind; [ constructor | cbn ].
  now constructor.
Qed.

Lemma AbsIn_map_inj {A B: Type} {l: list A} {a} (f: A -> B) (Abs: AbsIn a l) (inj: forall x y, f x = f y -> x = y): AbsIn (f a) (map f l).
Proof.
  induction Abs; cbn; constructor; auto.
Qed.

Lemma SIns_map_inj {A B: Type} {l: list A} (f: A -> B) (HSIns: SIns l) (inj: forall x y, f x = f y -> x = y): SIns (map f l).
Proof.
  induction HSIns; cbn; constructor; auto using AbsIn_map_inj.
Qed.

Lemma AbsBind_map_inj_fst_snd {A B C: Type} {l: list (A * B)} {a} (f: B -> C) (Abs: AbsBind a l) (inj: forall x y, f x = f y -> x = y): AbsBind a (map (fun ab => (fst ab, f (snd ab))) l).
Proof.
  now induction Abs; cbn; constructor.
Qed.

Lemma SBinds_map_inj_fst_snd {A B C: Type} {l: list (A * B)} (f: B -> C) (Binds: SBinds l) (inj: forall x y, f x = f y -> x = y): SBinds (map (fun ab => (fst ab, f (snd ab))) l).
Proof.
  induction Binds; cbn; constructor; auto using AbsBind_map_inj_fst_snd.
Qed.

Lemma SBinds_map_fst_SIns {A B: Type} {l: list (A * B)} (HSBinds: SBinds l): SIns (map fst l).
  induction HSBinds; [ constructor | ].
  cbn.
  constructor; [ eapply AbsBind_map_fst_AbsIn; now eauto | auto ].
Qed.

Lemma SIn_map_fst_SBindIn {A B: Type} {l: list (A * B)} {a} (HSBinds: SBinds l) (HSIn: SIn a (map fst l)): exists b, SBindIn a b l.
Proof.
  induction HSBinds; [ now inversion HSIn | ].
  cbn in HSIn; inversion HSIn; subst.
  exists b; constructor; auto.
  specialize (IHHSBinds H4) as ( b0 & IH ).
  exists b0.
  right; auto.
Qed.

Lemma AbsBind_map {A B C: Type} {l: list (A * B)} {f: B -> C} {a} (HAbsBind: AbsBind a l)
  : AbsBind a (map (fun ab => (fst ab, f (snd ab))) l).
Proof.
  induction HAbsBind; [ now constructor | cbn ].
  constructor; auto.
Qed.

Lemma SBinds_map {A B C: Type} {l: list (A * B)} {f: B -> C} (HSBinds: SBinds l)
  : SBinds (map (fun ab => (fst ab, f (snd ab))) l).
Proof.
  induction HSBinds; [ now constructor | cbn ].
  constructor; [ now apply AbsBind_map | assumption ].
Qed.

Lemma SBindIn_map {A B C: Type} {l: list (A * B)} {f: B -> C} {a b} (HSBindIn: SBindIn a b l)
  : SBindIn a (f b) (map (fun ab => (fst ab, f (snd ab))) l).
Proof.
  induction HSBindIn; cbn.
  now constructor; eapply AbsBind_map.
  now right.
Qed.

Fixpoint sfind {A B: Type} (eqA_dec: forall x y: A, { x = y } + { x <> y }) (a: A) (l: list (A * B)): option B :=
  match l with
  | [] => None
  | (a',b)::l =>
      if eqA_dec a' a then
        Some b
      else
        sfind eqA_dec a l
  end.

Lemma sbinds_sfind {A B: Type} {l: list (A*B)}
  (eqA_dec: forall x y: A, { x = y } + { x <> y })
  (HSBinds: SBinds l)
  : forall a b, SBindIn a b l <-> sfind eqA_dec a l = Some b.
Proof.
  intros a b; split.
  - intros HBind.
    induction HBind.
    cbn.
    destruct (eqA_dec x x); [ auto | contradiction ].
    cbn.
    destruct (eqA_dec x' x); [ congruence | cbn ].
    apply IHHBind.
    now inversion HSBinds.
  - intros Esfind.
    induction HSBinds.
    discriminate.
    cbn in Esfind.
    destruct (eqA_dec a0 a); subst.
    now inversion Esfind; subst; constructor.
    right. congruence. eauto.
Qed.

Lemma sfind_None_In {A B: Type} {a} {l: list (A*B)} (eqA_dec: forall x y: A, { x = y } + { x <> y })
  (Esfind: sfind eqA_dec a l = None)
  : forall b, ~In (a,b) l.
Proof.
  induction l as [ | [ a' b' ] ]; cbn; eauto.
  intros b [ Heq | HIn ].
  inversion Heq; subst; clear Heq.
  - cbn in Esfind.
    destruct (eqA_dec a a) as [ _ | Hneq ]; [ discriminate | contradiction ].
  - cbn in Esfind.
    destruct (eqA_dec a' a) as [ _ | Hneq ]; [ discriminate | ].
    eapply IHl; eauto.
Qed.

Definition pair_l_eqA {A B: Type} (eqA: A -> A -> Prop) (x y: (A*B)) := eqA (fst x) (fst y).

Lemma pair_l_eqA_dec {A B: Type} {eqA: A -> A -> Prop} (eqA_dec: forall x y, {eqA x y} + {~eqA x y}): forall (x y: (A*B)), { pair_l_eqA eqA x y } + { ~ pair_l_eqA eqA x y }.
Proof.
  destruct x as [ xa xb ], y as [ ya yb ].
  destruct (eqA_dec xa ya) as [ Heq | Hneq ];
    now constructor.
Qed.

Fixpoint mapi' [A B: Type] (f: A -> nat -> B) (l: list A) (n: nat) {struct l}: list B :=
  match l with
  | [] => []
  | x::xs =>
      (f x n)::(mapi' f xs (S n))
  end.

Definition mapi [A B: Type] (f: A -> nat -> B) (l: list A): list B := mapi' f l 0.

Fixpoint map_opt [A B: Type] (f: A -> option B) (l: list A) : option (list B) :=
  match l with
  | [] => Some []
  | a::l =>
      match f a, map_opt f l with
      | Some b, Some bs => Some (b :: bs)
      | _, _ => None
      end
  end.

Lemma Forall_forall_l [A: Type] [P: A -> Prop] [l: list A] (HForall: Forall P l): forall x, In x l -> P x.
Proof.
  now apply Forall_forall.
Qed.

Inductive ForallT [A: Type] (P: A -> Type): list A -> Prop :=
| ForallT_nil : ForallT P []
| ForallT_cons: forall (x: A) (l: list A), P x -> ForallT P l -> ForallT P (x::l)
.

Lemma Forall2_dec: forall [A B: Type] (P: A -> B -> Prop),
    (forall x y, { P x y } + { ~P x y}) ->
    forall l l', { Forall2 P l l' } + { ~Forall2 P l l'}.
Proof.
  intros A B P P_dec.
  induction l.
  - destruct l'.
    left; constructor.
    right; intros contra; inversion contra.
  - destruct l'.
    right; intros contra; inversion contra.
    destruct (P_dec a b).
    + destruct (IHl l').
      left.
      now constructor.
      right.
      intros contra; now inversion contra.
    + right; intros contra; now inversion contra.
Qed.

Fixpoint forall2 {A B: Type} (f: A -> B -> bool) (l: list A) (l': list B): bool :=
  match l, l' with
  | [], [] => true
  | x::xs, y::ys =>
      if f x y then
        forall2 f xs ys
      else
        false
  | _,_ => false
  end.

Inductive Forall2T {A B: Type} R: list A -> list B -> Type :=
| Forall2T_nil: Forall2T R [] []
| Forall2T_cons: forall x y l l', R x y -> Forall2T R l l' -> Forall2T R (x::l) (y::l')
.

Lemma Forall2T_dec: forall {A B: Type} (R: A -> B -> Type) (R_dec: (forall a b, (R a b) + (R a b -> Empty_set))) la lb, (Forall2T R la lb) + ((Forall2T R la lb) -> Empty_set).
Proof.
  intros A B R R_dec la.
  induction la.
  - destruct lb.
    repeat constructor.
    right; intros contra; now inversion contra.
  - destruct lb.
    right; intros contra; now inversion contra.
    destruct (IHla lb) as [ HForall | HNForall ].
    destruct (R_dec a b).
    now repeat constructor.
    right; intros contra; now inversion contra.
    right; intros contra; now inversion contra.
Qed.

Definition list_eqb {A: Type} (eqb: A -> A -> bool) (l: list A) (l': list A): bool := forall2 eqb l l'.

Lemma list_eqb_refl {A: Type} (eqb: A -> A -> bool) (eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y)): forall l, list_eqb eqb l l = true.
Proof.
  induction l; [ reflexivity | ].
  cbn.
  destruct (eqb_spec a a) as [ _ | ]; [ now cbn | contradiction ].
Qed.
Hint Resolve list_eqb_refl: datatypes.

Lemma list_eqb_spec {A: Type} (eqb: A -> A -> bool): forall l l' (eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y)), Bool.reflect (l = l') (list_eqb eqb l l').
Proof.
  fix IH 1.
  destruct l as [ | x l ], l' as [ | y l' ];
    (try (constructor; congruence)).
  intros eqb_spec.
  cbn.
  destruct (eqb_spec x y); [ subst y; cbn | right; congruence ].
  fold (@list_eqb A eqb l l').
  destruct (IH l l' eqb_spec); [ subst l' | ].
  now constructor.
  right.
  congruence.
Qed.
Hint Resolve list_eqb_spec: datatypes.

Fixpoint filter_map [A B: Type] (f: A -> option B) (l: list A): list B :=
  match l with
  | [] => []
  | a::t =>
      match f a with
      | Some b => b :: filter_map f t
      | None => filter_map f t
      end
  end.

Lemma nth_error_last [A: Type] l a:
  @nth_error A ( l ++ [a] ) (length l) = Some a.
Proof.
  revert a.
  induction l; [ reflexivity | ].
  now apply IHl.
Qed.

Lemma findA_app {A B: Type} (f: A -> bool) (l1 l2: list (A*B)) b:
  findA f (l1 ++ l2) = Some b <->
    findA f l1 = Some b \/ (findA f l1 = None /\ findA f l2 = Some b).
Proof.
  induction l1 as [ | [ a' b' ] l1 ]; cbn.
  - split.
    + intros Hfind; now repeat constructor.
    + now intros [ contra | ( _ & Hfind ) ].
  - destruct (f a') eqn:Efa'.
    + split.
      * intros Heq; inversion Heq; subst; clear Heq; now constructor.
      * intros [ Heq | ( contra & _ ) ]; congruence.
    + assumption.
Qed.

(* Fixpoint lookup {A B : Type} (eqb : A -> A -> bool) (l : list (A*B)) (x : A) : *)
(*   option B := *)
(*   match l with *)
(*   | [] => None *)
(*   | (x', y) :: l' => if eqb x x' then Some y else lookup eqb l' x *)
(*   end. *)

(* Lemma lookup_app *)
(*   {A B : Type} (eqb : A -> A -> bool) (l1 l2 : list (A*B)) (x : A) (y : B) : *)
(*   lookup eqb (l1 ++ l2) x = Some y <-> *)
(*     lookup eqb l1 x = Some y \/ lookup eqb l1 x = None /\ lookup eqb l2 x = Some y. *)
(* Proof. *)
(*   induction l1 as [ | [x' y'] l1 IH]. *)
(*   - cbn. *)
(*     split; [tauto | ]. *)
(*     intros [[=] | [_ Heq]]. *)
(*     exact Heq. *)
(*   - cbn. *)
(*     destruct (eqb x x'); [ | exact IH]. *)
(*     split; [tauto | ]. *)
(*     intros [ |[Heq _]]; [assumption | discriminate Heq]. *)
(* Qed. *)

(* Lemma lookup_in *)
(*   {A B : Type} (eqb : A -> A -> bool) *)
(*   (Heqb : forall x y, eqb x y = true -> x = y) *)
(*   (l : list (A*B)) (x : A) (y : B) : *)
(*   lookup eqb l x = Some y -> In (x, y) l. *)
(* Proof. *)
(*   induction l as [ | [x' y'] l IH]; [intros [=] | ]. *)
(*   cbn. *)
(*   destruct (eqb x x') eqn: Heq. *)
(*   - intros [= Hy]. *)
(*     left. *)
(*     f_equal; [ | exact Hy]. *)
(*     symmetry. *)
(*     apply Heqb, Heq. *)
(*   - intro Hy. *)
(*     right. *)
(*     apply IH, Hy. *)
(* Qed. *)

(* Lemma nth_error_nil {A : Type} (n : nat) : nth_error (@nil A) n = None. *)
(* Proof. *)
(*   destruct n; reflexivity. *)
(* Qed. *)

(* Lemma length_neq_neq {A: Type}: forall (l l': list A), length l <> length l' -> l <> l'. *)
(* Proof. *)
(*   induction l. *)
(*   - destruct l'; [ contradiction | discriminate ]. *)
(*   - destruct l'; [ discriminate | intros Hneqlength ]. *)
(*     intros contra. *)
(*     inversion contra; subst; clear contra. *)
(*     contradiction. *)
(* Qed. *)

Fixpoint set_nth {A: Type} (l: list A) (n: nat) (a: A): list A :=
  match l, n with
  | _::xs, 0 => a::xs
  | x::xs, S n => x::(set_nth xs n a)
  | [], _ => []
  end.

Lemma set_nth_correct: forall A (l: list A) n a, n < List.length l -> forall m, ((n <> m /\ List.nth_error l m = List.nth_error (set_nth l n a) m) \/ (n = m /\ List.nth_error (set_nth l n a) n = Some a)).
Proof.
  intros A l n a Hlt m.
  revert A l n a Hlt.
  induction m.
  - intros.
    destruct (Nat.eq_dec n 0); [ subst; right; split; auto | left; split; auto ].
    + cbn. destruct l as [ | x xs ]; [ cbn in Hlt; lia | cbn in Hlt; reflexivity ].
    + destruct l as [ | x xs ]; [ reflexivity | cbn ].
      destruct n; [ contradiction | reflexivity ].
  - intros.
    destruct (Nat.eq_dec n (S m)); [ subst; right; split; auto | left; split; auto ].
    + cbn. destruct l as [ | x xs ]; [ cbn in Hlt; lia | ].
      cbn.
      destruct (IHm A xs m a) as [ [ Hneq Hnth ] | [ _ Hnth ] ];
        [ cbn in Hlt; lia | contradiction | assumption ].
    + cbn. destruct l as [ | x xs ]; [ cbn in Hlt; lia | ].
      cbn.
      destruct n; [ reflexivity | ].
      destruct (IHm A xs n a) as [ [ Hneq Hnth ] | [ Heq Hnth ] ]; [ cbn in Hlt; lia | auto | subst; contradiction ].
Qed.

Fixpoint fold_left_opt [A B: Type] (f: A -> B -> option A) (l: list B) (acc: A): option A :=
  match l with
  | [] => Some acc
  | x::xs =>
      match f acc x with
      | Some acc => fold_left_opt f xs acc
      | None => None
      end
  end.

(* Fixpoint nat_fold_opt [A: Type] (f: A -> option A) (n: nat) (acc: A): option A := *)
(*   match n with *)
(*   | 0 => Some acc *)
(*   | S n => *)
(*       match f acc with *)
(*       | Some acc => nat_fold_opt f n acc *)
(*       | None => None *)
(*       end *)
(*   end. *)

(* Inductive eqlistAB {A B: Type} (eqAB: A -> B -> Prop): list A -> list B -> Prop := *)
(* | eqlistAB_nil: eqlistAB eqAB [] [] *)
(* | eqlistAB_cons: forall a b la lb, eqAB a b -> eqlistAB eqAB la lb -> eqlistAB eqAB (a::la) (b::lb) *)
(* . *)

Lemma split_map [A B: Type] (l: list (A * B)): exists l_l l_r, split l = (l_l, l_r) /\ combine l_l l_r = l /\ map fst l = l_l /\ map snd l = l_r.
Proof.
  induction l as [ | ( hd_l & hd_r ) tl ] ; [ now repeat econstructor | ].
  destruct IHtl as ( l_l & l_r & Hsplit & Hcombine & Hfst & Hsnd ).
  exists (hd_l::map fst tl), (hd_r::map snd tl).
  split; [ cbn; rewrite Hsplit; congruence | ].
  split; [ cbn; now rewrite Hfst, Hsnd, Hcombine | ].
  now split.
Qed.

Lemma NoDupA_NoDup [A: Type] (l: list A): NoDupA eq l <-> NoDup l.
Proof.
  induction l; [ repeat constructor | ].
  split; intros H;
    inversion H; subst;
    (constructor; [ | now apply IHl ]).
  now rewrite InA_In in H2.
  now rewrite <- InA_In in H2.
Qed.

Lemma list_no_repet_NoDup [A: Type] (l: list A): Coqlib.list_norepet l <-> NoDup l.
Proof.
  induction l.
  - split; constructor.
  - split; intros H;
      inversion H; subst;
      (constructor; [ assumption | now apply IHl ]).
Qed.

Lemma rev_list_rect [A: Type] : forall P:list A-> Type,
    P [] ->
    (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
    forall l:list A, P (rev l).
Proof.
  intros P ? ? l; induction l; auto.
Qed.

Lemma rev_rect [A: Type] (P: list A -> Type) (Pnil: P []) (Pcons: forall (x: A) (l: list A), P l -> P (l ++ [x])) l: P l.
Proof.
  rewrite <- (rev_involutive l).
  apply (rev_list_rect P); cbn; auto.
Qed.
