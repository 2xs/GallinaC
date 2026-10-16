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

From Stdlib Require Import Arith PArith Psatz.
From Stdlib Require Export List SetoidList Sorting.Sorted.
Export ListNotations.

From HB Require Import structures.

From compcert.lib Require Coqlib.

From GallinaC.Utils Require Import Algebra.

(* Facts about cons *)
Section Cons.

  Lemma cons_self_neq [A] [l] [a: A]: a::l <> l.
    revert a.
    induction l as [ | a' l ]; intros a EQ;
      [ discriminate | inversion EQ; eapply IHl; eassumption ].
  Qed.

End Cons.

(* Facts about In *)
Section In.

  Lemma In_neq_hd [A] [l: list A] [a a'] (IN: In a (a'::l)) (NE: a <> a'): In a l.
  Proof.
    destruct IN; congruence.
  Qed.

  Lemma InA_In [A] (a: A) l: InA eq a l <-> In a l.
  Proof.
    induction l as [ | a' l];
      split; intros H; inversion H; subst;
      first [ now left | now right; apply IHl ].
  Qed.

  Lemma In_rev_append [A] (l d: list A) (x: A):
    In x (rev_append l d) <-> In x l \/ In x d.
  Proof.
    rewrite rev_append_rev.
    split.
    - intros IN.
      destruct (proj1 (in_app_iff _ _ _) IN) as [ INR | IND ];
        [ left; exact (proj2 (in_rev _ _) INR) | right; exact IND ].
    - intros [ INL | IND ]; apply (proj2 (in_app_iff _ _ _));
        [ left; exact (proj1 (in_rev _ _) INL) | right; exact IND ].
  Qed.

End In.

(* Facts about map *)
Section Map.

  Lemma map_In_inj [A B] [f: A -> B] [l: list A] [a]
    (f_inj: forall a1 a2, f a1 = f a2 -> a1 = a2)
    (IN: In (f a) (map f l))
    : In a l.
  Proof.
    induction l; [ contradiction | ].
    cbn in IN.
    now destruct IN as [ EQ | IN ]; constructor; auto.
  Qed.

End Map.

(* Facts about [nth_error] *)
Section NthError.

  Lemma nth_error_last [A] l a:
    @nth_error A ( l ++ [a] ) (length l) = Some a.
  Proof.
    revert a.
    induction l; [ reflexivity | ].
    now apply IHl.
  Qed.

  Lemma nth_error_snoc_mono [A] [l: list A] [x n y]
    (NTH: nth_error l n = Some y):
    nth_error (l ++ [x]) n = Some y.
  Proof.
    revert n NTH; induction l as [ | z l IH ]; intros [ | n ] NTH;
      cbn in NTH |- *; try discriminate.
    - exact NTH.
    - exact (IH n NTH).
  Qed.

  Lemma nth_error_snoc_inv [A]:
    forall [l: list A] [x n y]
    (NTH: nth_error (l ++ [x]) n = Some y),
      nth_error l n = Some y \/ (n = length l /\ y = x).
  Proof.
    induction l.
    - now intros until n;
        destruct n as [ | [ | n ] ]; cbn;
        intros y;
        first [ injection 1 as <-; constructor | discriminate ].
    - intros until n;
        destruct n; cbn;
        intros y.
      now injection 1 as <-; constructor.
      intros EQ.
      now apply IHl in EQ as [ EQ | [ EQ1 EQ2 ] ]; subst; constructor.
  Qed.

End NthError.

(* Replacing values in a list *)
Section Replace.

  Fixpoint replaceA [A B: Type] [eqA: A -> A -> Prop] [eqA_equiv: Equivalence eqA] [eqA_dec: forall x y, {eqA x y} + {~eqA x y}] (k: A) (v: B) (l: list (A*B)): list (A*B) :=
    match l with
    | [] => []
    | (x,y)::l => (if eqA_dec x k then (x,v) else (x,y))::(@replaceA A B eqA eqA_equiv eqA_dec k v l)
    end.

  Fixpoint replace [A B: Type] [eq_dec: forall x y, {x = y} + {x <> y}] (k: A) (v: B) (l: list (A*B)) :=
    match l with
    | [] => []
    | (x, y)::l => if eq_dec x k then (x, v)::l else ((x,y)::(@replace A B eq_dec k v l))
    end.

  Fixpoint replace_insert [A B: Type] [eq_dec: forall x y, {x = y} + {x <> y}] (k: A) (v: B) (l: list (A*B)) :=
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

End Replace.

(* Tricky variants of In* that are more relevant when manipulating bindings *)
(* Meaning of naming fragments:
 * - [In]: Such inductives relate to the [In] predicate
 * - [Bind]: Such inductives relate to variable bindings, hence they operate on lists of pairs ([fst] for the key, [snd] for the value)
 * - [Abs]: Such inductives encode the _absence_ of elements
 * - [S]: Such inductives are _strict_, when something exists in a list, it doesn't exist later in the list
 * - [s]: Such inductives state that a list respects the given property for all bindings
 * *)
Section Bindings.

  Section Inductives.

    (* [AbsIn a l] states that [a] does not exist in [l] *)
    Inductive AbsIn [A: Type]: A -> list A -> Prop :=
    | AbsIn_nil: forall a, AbsIn a []
    | AbsIn_cons: forall a a' l, a <> a' -> AbsIn a l -> AbsIn a (a'::l)
    .
    (* [SIn a l] states that [a] exists in [l], but only at one position *)
    Inductive SIn [A: Type]: A -> list A -> Prop :=
    | SIn_hd: forall a l, AbsIn a l -> SIn a (a::l)
    | SIn_cons: forall a a' l, a <> a' ->  SIn a l -> SIn a (a'::l)
    .

    (* [SIns l] states that [l] respects the [SIn] property in all points *)
    Inductive SIns {A: Type}: list A -> Prop :=
    | SIns_nil: SIns []
    | SIns_cons: forall a l, AbsIn a l -> SIns l -> SIns (a::l)
    .

    (* [AbsBind a l] states that there is no [(a, b)] (for any [b]) in [l] *)
    Inductive AbsBind [A B: Type]: A -> list (A*B) -> Prop :=
    | AbsBind_nil: forall x, AbsBind x []
    | AbsBind_cons: forall x x' y' l, x <> x' -> AbsBind x l -> AbsBind x ((x',y')::l)
    .
    (* [BindIn a b l] states that there is a [(a, b)] in [l], no such binding might exists before the witnessed position *)
    Inductive BindIn [A B: Type]: A -> B -> list (A*B) -> Prop :=
    | BindIn_hd: forall x y l, BindIn x y ((x,y)::l)
    | BindIn_tl: forall x y l x' y', x <> x' -> BindIn x y l -> BindIn x y ((x', y')::l)
    .
    (* [SBindIn a b l] states that there is a [(a, b)] in [l], but there is no other binding of [a] at any other position *)
    Inductive SBindIn [A B: Type]: A -> B -> list (A*B) -> Prop :=
    | SBindIn_hd: forall x y l, AbsBind x l -> SBindIn x y ((x,y)::l)
    | SBindIn_tl: forall x y l x' y', x <> x' -> SBindIn x y l -> SBindIn x y ((x', y')::l)
    .

    (* [SBinds l] states that [l] respects the [SBindIn] property in all points *)
    Inductive SBinds {A B: Type}: list (A*B) -> Prop :=
    | SBinds_nil: SBinds []
    | SBinds_cons: forall a b l, AbsBind a l -> SBinds l -> SBinds ((a,b)::l)
    .

    Inductive AbsBind2 [A B: Type]: A -> B -> list (A*B) -> Prop :=
    | AbsBind2_nil: forall a b, AbsBind2 a b []
    | AbsBind2_cons: forall a a' b b' l, a <> a' -> b <> b' -> AbsBind2 a b l -> AbsBind2 a b ((a',b')::l)
    .

    Inductive SBinds2 {A B: Type}: list (A*B) -> Prop :=
    | SBinds2_nil: SBinds2 []
    | SBinds2_cons: forall a b l, AbsBind2 a b l -> SBinds2 l -> SBinds2 ((a,b)::l)
    .

    Inductive AbsBMap [A B C: Type]: A -> B -> list (A*(B*C)) -> Prop :=
    | AbsBMap_nil: forall a b, AbsBMap a b []
    | AbsBMap_cons: forall a b a' b' c' l,
        a <> a' -> b <> b' -> AbsBMap a b l -> AbsBMap a b ((a',(b',c'))::l)
    .

    (* [BMap l] states that [l] is a bidirectional map
     * Values of both type `A` and `B` can be used to index it *)
    Inductive BMap {A B C: Type}: list (A*(B*C)) -> Prop :=
    | BMap_nil: BMap []
    | BMap_cons: forall a b c l, AbsBMap a b l -> BMap l -> BMap ((a,(b,c))::l)
    .

    (* [DBinds l m]: every key bound in [l] is absent from [m]
       (the two binding lists have disjoint keys). *)
    Inductive DBinds [A B: Type]: list (A*B) -> list (A*B) -> Prop :=
    | DBinds_nil: forall m, DBinds [] m
    | DBinds_cons: forall a b l m, AbsBind a m -> DBinds l m -> DBinds ((a,b)::l) m
    .

  End Inductives.

  Section Reflections.

    Fixpoint abs_bind [A B: Type] (eqbA: A -> A -> bool) (a: A) (l: list (A*B)) : bool :=
      match l with
      | [] => true
      | (a', _) :: rest => negb (eqbA a a') && abs_bind eqbA a rest
      end.

    Fixpoint sbinds [A B: Type] (eqbA: A -> A -> bool) (l: list (A*B)) : bool :=
      match l with
      | [] => true
      | (a, _) :: rest => abs_bind eqbA a rest && sbinds eqbA rest
      end.

    Fixpoint dbinds [A B: Type] (eqbA: A -> A -> bool) (l m: list (A*B)) : bool :=
      match l with
      | [] => true
      | (a, _) :: rest => abs_bind eqbA a m && dbinds eqbA rest m
      end.

    Lemma abs_bind_spec [A B: Type] (eqbA: A -> A -> bool)
      (eqb_spec: forall x y, Bool.reflect (x = y) (eqbA x y))
      : forall (a: A) (l: list (A*B)),
        Bool.reflect (AbsBind a l) (abs_bind eqbA a l).
    Proof.
      intros a l.
      induction l as [ | [a' b'] rest IH ]; cbn.
      - apply ReflectT. constructor.
      - destruct (eqb_spec a a') as [Heq | Hneq]; cbn.
        + subst. apply ReflectF. intros H. inversion H; subst. contradiction.
        + destruct IH as [HAbs | HnotAbs].
          * apply ReflectT. constructor; assumption.
          * apply ReflectF. intros H. inversion H; subst. contradiction.
    Qed.

    Lemma sbinds_spec [A B: Type] (eqbA: A -> A -> bool)
      (eqb_spec: forall x y, Bool.reflect (x = y) (eqbA x y))
      : forall (l: list (A*B)),
        Bool.reflect (SBinds l) (sbinds eqbA l).
    Proof.
      intros l.
      induction l as [ | [a b] rest IH ]; cbn.
      - apply ReflectT. constructor.
      - destruct (abs_bind_spec eqbA eqb_spec a rest) as [HAbs | HnotAbs]; cbn.
        + destruct IH as [HSB | HnotSB].
          * apply ReflectT. now constructor.
          * apply ReflectF. intros H. inversion H; subst. contradiction.
        + apply ReflectF. intros H. inversion H; subst. contradiction.
    Qed.

    Lemma dbinds_spec [A B: Type] (eqbA: A -> A -> bool)
      (eqb_spec: forall x y, Bool.reflect (x = y) (eqbA x y))
      : forall (l m: list (A*B)),
        Bool.reflect (DBinds l m) (dbinds eqbA l m).
    Proof.
      intros l m.
      induction l as [ | [a b] rest IH ]; cbn.
      - apply ReflectT. constructor.
      - destruct (abs_bind_spec eqbA eqb_spec a m) as [HAbs | HnotAbs]; cbn.
        + destruct IH as [HDB | HnotDB].
          * apply ReflectT. now constructor.
          * apply ReflectF. intros H. inversion H; subst. contradiction.
        + apply ReflectF. intros H. inversion H; subst. contradiction.
    Qed.

    Lemma sbinds_true_SBinds [A B: Type] (eqbA: A -> A -> bool)
      (eqb_spec: forall x y, Bool.reflect (x = y) (eqbA x y))
      [l: list (A*B)] (SB: sbinds eqbA l = true):
      SBinds l.
    Proof.
      destruct (sbinds_spec eqbA eqb_spec l) as [ HSB | _ ];
        [ exact HSB | discriminate SB ].
    Qed.

  End Reflections.

  (* Facts about AbsIn *)
  Section AbsIn.

    Lemma AbsIn_In_contra [A: Type] [l: list A] [a] (HAbsIn: AbsIn a l) (HIn: In a l): False.
    Proof.
      induction HAbsIn; [ contradiction | ].
      inversion HIn; subst; now auto.
    Qed.

    Lemma AbsIn_not_In [A: Type] (l: list A): forall a, AbsIn a l <-> ~In a l.
    Proof.
      induction l; [ now intros; split; intros H; auto; constructor  | intros; split; intros H ].
      - intros contra.
        inversion H; subst.
        eapply IHl; [ eauto | destruct contra; [ congruence | assumption ] ].
      - constructor; [ | apply IHl ];
          intros contra; subst;
          now apply H; now constructor.
    Qed.

    Lemma AbsIn_map_inj [A B: Type] [l: list A] [a] (f: A -> B) (Abs: AbsIn a l) (inj: forall x y, f x = f y -> x = y): AbsIn (f a) (map f l).
    Proof.
      induction Abs; cbn; constructor; auto.
    Qed.

  End AbsIn.

  Section SIn.

    Lemma SIn_map_fst_SBindIn [A B: Type] [l: list (A * B)] [a] (HSBinds: SBinds l) (HSIn: SIn a (map fst l)): exists b, SBindIn a b l.
    Proof.
      induction HSBinds; [ now inversion HSIn | ].
      cbn in HSIn; inversion HSIn; subst.
      exists b; constructor; auto.
      specialize (IHHSBinds H4) as ( b0 & IH ).
      exists b0.
      right; auto.
    Qed.

  End SIn.

  (* Facts about SIns *)
  Section SIns.

    Lemma SIns_tl_neq [A: Type]: forall (l: list A) a a', SIns (a::l) -> In a' l -> a' <> a.
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

    Lemma SIns_In [A: Type] [l: list A] [a] (HSIns: SIns l) (HIn: In a l): SIn a l.
    Proof.
      induction l; [ contradiction | ].
      inversion HSIns; subst.
      inversion HIn; subst.
      - now left.
      - right; auto.
        intros eq; subst.
        eapply SIns_tl_neq; [ apply HSIns | eauto | eauto ].
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

    Lemma SIns_map_inj [A B: Type] [l: list A] (f: A -> B) (HSIns: SIns l) (inj: forall x y, f x = f y -> x = y): SIns (map f l).
    Proof.
      induction HSIns; cbn; constructor; auto using AbsIn_map_inj.
    Qed.

    Lemma SIns_list_norepet {A: Type} {l: list A} (HSIns: SIns l): Coqlib.list_norepet l.
    Proof using Type.
      induction HSIns as [ | a l HAbsIn HSIns ].
      constructor.
      constructor; eauto using AbsIn_In_contra.
    Qed.

  End SIns.

  (* Facts about AbsBind *)
  Section AbsBind.

    Lemma AbsBind_In_False
      [A B: Type] [a b] [l: list (A*B)]
      (HAbsBind: AbsBind a l)
      (HIn: In (a,b) l)
      : False.
    Proof.
      induction l as [ | [ a' b' ] l ]; [ contradiction | ].
      inversion HAbsBind as [ | ?x ?x' ?y' ?l Hneq HAbsBind']; subst.
      destruct HIn as [ Heq | ]; [ inversion Heq; subst; contradiction | auto ].
    Qed.

    Lemma DBinds_In_AbsBind
      [A B: Type] [l m: list (A*B)] [a b]
      (HD: DBinds l m) (HIn: In (a,b) l)
      : AbsBind a m.
    Proof.
      induction HD as [ | a' b' l m Hab HD IH ]; [ contradiction | ].
      destruct HIn as [ Heq | HIn ]; [ inversion Heq; subst; exact Hab | exact (IH HIn) ].
    Qed.

    Lemma DBinds_In_AbsBind_rev
      [A B: Type] [l m: list (A*B)] [a b]
      (HD: DBinds l m) (HIn: In (a, b) m)
      : AbsBind a l.
    Proof.
      induction l as [ | [k v] rest IH ]; [ constructor | ].
      inversion HD as [ | ? ? ? ? Habs HD' ]; subst.
      constructor.
      - intros ->; exact (AbsBind_In_False Habs HIn).
      - apply IH; exact HD'.
    Qed.

    Lemma DBinds_Forall
      [A B: Type] [l m: list (A*B)] (HD: DBinds l m)
      : List.Forall (fun idt => ~ exists idt', In idt' m /\ fst idt' = fst idt) l.
    Proof.
      induction HD as [ | a b l m Hab HD IH ]; constructor; [ | exact IH ].
      intros (idt' & HIn & Hfst).
      destruct idt' as [ a' b' ]; cbn in Hfst; subst a'.
      exact (AbsBind_In_False Hab HIn).
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

    Lemma AbsBind_AbsIn [A B: Type] [l: list (A*B)] [a b] (Abs: AbsBind a l): AbsIn (a,b) l.
    Proof.
      induction Abs; constructor; auto.
      congruence.
    Qed.

    Lemma AbsBind_map_fst_AbsIn [A B: Type] [l: list (A * B)] [a] (HAbsBind: AbsBind a l): AbsIn a (map fst l).
    Proof.
      induction HAbsBind; [ constructor | cbn ].
      now constructor.
    Qed.

    Lemma AbsBind_map_inj_fst_snd [A B C: Type] [l: list (A * B)] [a] (f: B -> C) (Abs: AbsBind a l) (inj: forall x y, f x = f y -> x = y): AbsBind a (map (fun ab => (fst ab, f (snd ab))) l).
    Proof.
      now induction Abs; cbn; constructor.
    Qed.

    Lemma AbsBind_map [A B C: Type] [l: list (A * B)] [f: B -> C] [a] (HAbsBind: AbsBind a l)
      : AbsBind a (map (fun ab => (fst ab, f (snd ab))) l).
    Proof.
      induction HAbsBind; [ now constructor | cbn ].
      constructor; auto.
    Qed.

    Lemma AbsBind_iff_not_In_fst [A B: Type] (x: A) (l: list (A*B)):
      AbsBind x l <-> ~ In x (map fst l).
    Proof.
      split.
      - intros ABS IN.
        apply in_map_iff in IN as ( [ a b ] & EQ & INL ).
        cbn [fst] in EQ; subst a.
        exact (AbsBind_In_False ABS INL).
      - induction l as [ | [ a b ] l IH ]; intros NIN; [ constructor | ].
        constructor.
        + intros EQ; exact (NIN (or_introl (eq_sym EQ))).
        + exact (IH (fun IN => NIN (or_intror IN))).
    Qed.

    Lemma AbsBind_rev_append [A B: Type] (t d: list (A*B)) (x: A):
      AbsBind x (rev_append t d) <-> AbsBind x t /\ AbsBind x d.
    Proof.
      revert d.
      induction t as [ | [ a b ] t IH ]; intros d; cbn [rev_append].
      - split;
          [ intros ABS; split; [ constructor | exact ABS ]
          | intros ( _ & ABS ); exact ABS ].
      - split.
        + intros ABS.
          destruct (proj1 (IH _) ABS) as ( ABSt & ABSad ).
          inversion ABSad as [ | ?y ?y' ?z ?m NE ABSd ]; subst.
          split; [ constructor; [ exact NE | exact ABSt ] | exact ABSd ].
        + intros ( ABSat & ABSd ).
          inversion ABSat as [ | ?y ?y' ?z ?m NE ABSt ]; subst.
          apply (proj2 (IH _)).
          split; [ exact ABSt | constructor; [ exact NE | exact ABSd ] ].
    Qed.

  End AbsBind.

  (* Facts about DBinds *)
  Section DBinds.

    Lemma DBinds_iff_disjoint_fst [A B: Type] (l m: list (A*B)):
      DBinds l m <-> (forall a, In a (map fst l) -> In a (map fst m) -> False).
    Proof.
      induction l as [ | [ a b ] l IH ].
      - split;
          [ intros _ x INL INM; cbn in INL; exact INL | intros _; constructor ].
      - split.
        + intros DB x INL INM.
          inversion DB as [ | ?y ?y' ?l0 ?m0 ABS DBl ]; subst.
          destruct INL as [ EQ | INL ];
            [ subst x; exact (proj1 (AbsBind_iff_not_In_fst _ _) ABS INM)
            | exact (proj1 IH DBl x INL INM) ].
        + intros DSJ.
          constructor.
          * apply (proj2 (AbsBind_iff_not_In_fst _ _)).
            intros INM; exact (DSJ a (or_introl eq_refl) INM).
          * apply (proj2 IH).
            intros x INL INM; exact (DSJ x (or_intror INL) INM).
    Qed.

    Lemma DBinds_rev_append [A B: Type] (l t d: list (A*B)):
      DBinds l (rev_append t d) <-> DBinds l t /\ DBinds l d.
    Proof.
      induction l as [ | [ a b ] l IH ].
      - split; [ intros _; split; constructor | intros _; constructor ].
      - split.
        + intros DB.
          inversion DB as [ | ?y ?y' ?l0 ?m0 ABS DBl ]; subst.
          destruct (proj1 IH DBl) as ( DBt & DBd ).
          destruct (proj1 (AbsBind_rev_append _ _ _) ABS) as ( ABSt & ABSd ).
          split; constructor; assumption.
        + intros ( DBt & DBd ).
          inversion DBt as [ | ?y ?y' ?l0 ?m0 ABSt DBlt ]; subst.
          inversion DBd as [ | ?z ?z' ?l1 ?m1 ABSd DBld ]; subst.
          constructor;
            [ exact (proj2 (AbsBind_rev_append _ _ _) (conj ABSt ABSd))
            | exact (proj2 IH (conj DBlt DBld)) ].
    Qed.

    Lemma DBinds_list_disjoint_fst [A B: Type] (l m: list (A*B)):
      DBinds l m <-> (Coqlib.list_disjoint (map fst l) (map fst m)).
    Proof.
      split; unfold Coqlib.list_disjoint.
      - intros DBINDS x y INl INm EQ; subst.
        now eapply DBinds_iff_disjoint_fst; eauto.
      - intros NE.
        apply DBinds_iff_disjoint_fst.
        intros a INl INm.
        now eapply NE; eauto.
    Qed.

    Lemma DBinds_nil_r [A B: Type] (l: list (A * B))
      : DBinds l [].
    Proof.
      induction l as [ | [a b] l ]; [ constructor | ].
      now repeat constructor.
    Qed.

    Lemma DBinds_cons_r [A B: Type] [l m: list (A*B)] [a b]
      (DBINDS: DBinds l m) (ABSl: AbsBind a l) (ABSm: AbsBind a m)
      : DBinds l ((a, b)::m).
    Proof.
      induction DBINDS as [ | a' b' l m ABSm' DBINDS ]; [ now constructor | ].
      constructor.
      - constructor; [ | assumption ].
        intros contra; subst.
        now inversion ABSl.
      - eapply IHDBINDS; [ inversion ABSl | ]; assumption.
    Qed.

  End DBinds.

  (* Facts about SBinds *)
  Section SBinds.

    Lemma SBinds_tl_neq [A B: Type]: forall (l: list (A*B)) a b a' b', SBinds ((a,b)::l) -> In (a',b') l -> a' <> a.
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

    Lemma SBinds_same_In_eq
      [A B: Type] [a b1 b2] [l: list (A*B)]
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

    Lemma SBinds_In [A B: Type] [a b] [l: list (A*B)]: SBinds l -> In (a,b) l -> SBindIn a b l.
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

    Lemma SBinds_SIns [A B: Type] [l: list (A*B)] (HSBinds: SBinds l): SIns l.
    Proof.
      induction HSBinds; constructor.
      now apply AbsBind_AbsIn.
      auto.
    Qed.

    Lemma SBinds_list_norepet [A B: Type] (l: list (A*B)):
      SBinds l <-> Coqlib.list_norepet (List.map fst l).
    Proof.
      induction l as [ | [ a b ] l ]; cbn.
      - now repeat constructor.
      - split; intros H; constructor.
        * now inversion H; subst; apply AbsBind_iff_not_In_fst.
        * now apply IHl; inversion H.
        * inversion H as [ | ?hd ?tl ?NIn _]; subst.
          now apply AbsBind_iff_not_In_fst.
        * apply IHl.
          now inversion H.
    Qed.

    Lemma SBinds_NoDupA_fst [A B: Type] [l: list (A*B)]
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

    Lemma SBinds_map_inj_fst_snd [A B C: Type] [l: list (A * B)] (f: B -> C) (Binds: SBinds l) (inj: forall x y, f x = f y -> x = y): SBinds (map (fun ab => (fst ab, f (snd ab))) l).
    Proof.
      induction Binds; cbn; constructor; auto using AbsBind_map_inj_fst_snd.
    Qed.

    Lemma SBinds_map_fst_SIns [A B: Type] [l: list (A * B)] (HSBinds: SBinds l): SIns (map fst l).
      induction HSBinds; [ constructor | ].
      cbn.
      constructor; [ eapply AbsBind_map_fst_AbsIn; now eauto | auto ].
    Qed.

    Lemma SBinds_map [A B C: Type] [l: list (A * B)] [f: B -> C] (HSBinds: SBinds l)
      : SBinds (map (fun ab => (fst ab, f (snd ab))) l).
    Proof.
      induction HSBinds; [ now constructor | cbn ].
      constructor; [ now apply AbsBind_map | assumption ].
    Qed.

    Lemma SBinds_app [A B: Type] (l1 l2: list (A*B)):
      SBinds (l1 ++ l2) <->
      SBinds l1 /\ SBinds l2
      /\ DBinds l1 l2.
    Proof.
      split.
      - intros SB.
        pose proof (proj1 (SBinds_list_norepet _) SB) as NR.
        rewrite map_app in NR.
        destruct (proj1 (Coqlib.list_norepet_app _ _) NR) as ( NR1 & NR2 & DSJ );
          repeat first
            [ split
            | now eapply SBinds_list_norepet
            | now eapply DBinds_list_disjoint_fst ].
      - intros ( SB1 & SB2 & DSJ ).
        apply SBinds_list_norepet; rewrite map_app.
        apply Coqlib.list_norepet_app; split; [ | split ].
        + now apply SBinds_list_norepet.
        + now apply SBinds_list_norepet.
        + now eapply DBinds_list_disjoint_fst.
    Qed.

    Lemma DBinds_by_range [T: Type] [A B: list (positive * T)] [mid: positive]
      (RA: forall id ty, In (id, ty) A -> (mid <= id)%positive)
      (RB: forall id ty, In (id, ty) B -> (id < mid)%positive):
      DBinds A B.
    Proof.
      apply (proj2 (DBinds_iff_disjoint_fst _ _)).
      intros x INx INy.
      apply in_map_iff in INx as ( [ idx tyx ] & EQx & INx ).
      apply in_map_iff in INy as ( [ idy tyy ] & EQy & INy ).
      cbn [fst] in EQx, EQy; subst x; subst idy.
      specialize (RA _ _ INx); specialize (RB _ _ INy); lia.
    Qed.

    Lemma SBinds_app_by_range [T: Type] [A B: list (positive * T)] [mid: positive]
      (SA: SBinds A) (SB: SBinds B)
      (RA: forall id ty, In (id, ty) A -> (mid <= id)%positive)
      (RB: forall id ty, In (id, ty) B -> (id < mid)%positive):
      SBinds (A ++ B).
    Proof.
      apply (proj2 (SBinds_app _ _)).
      split; [ exact SA | split; [ exact SB | exact (DBinds_by_range RA RB) ] ].
    Qed.

    Lemma SBinds_rev_append_intro [A B: Type] (l d: list (A*B))
      (SL: SBinds l) (SD: SBinds d)
      (DBINDS: DBinds l d):
      SBinds (rev_append l d).
    Proof.
      revert d SD DBINDS.
      induction SL as [ | ?a ?b ?l ?ABS ?SL]; cbn; intros d SD DBINDS; [ exact SD  | ].
      apply IHSL.
      - constructor; [ | exact SD ].
        now inversion DBINDS; subst.
      - inversion DBINDS; subst.
        now apply DBinds_cons_r.
    Qed.

  End SBinds.

  Section SBindIn.

    Lemma SBindIn_BindIn [A B: Type] [a b] [l: list (A*B)]: SBindIn a b l -> BindIn a b l.
    Proof.
      revert a b.
      induction l as [ | [ a' b' ] l IHl ]; [ intros a b HIn; now inversion HIn | ].
      intros a b HSBindIn.
      inversion HSBindIn as [ ?a ?b ?l ?HAbsBind | ?a ?b ?l ?a' ?b' ?Hneq ?HSBindIn ];
        subst;
        constructor; now eauto.
    Qed.

    Lemma BindIn_In [A B: Type] [a b] [l: list (A*B)]: BindIn a b l -> In (a,b) l.
    Proof.
      revert a b.
      induction l as [ | [ a' b' ] l IHl ]; [ intros a b HIn; now inversion HIn | ].
      intros a b HBindIn.
      inversion HBindIn as [ ?a ?b ?l | ?a ?b ?l ?a' ?b' ?Hneq ?HBindIn ];
        subst;
        constructor; now eauto.
    Qed.

    Lemma SBindIn_map [A B C: Type] [l: list (A * B)] [f: B -> C] [a b] (HSBindIn: SBindIn a b l)
      : SBindIn a (f b) (map (fun ab => (fst ab, f (snd ab))) l).
    Proof.
      induction HSBindIn; cbn.
      now constructor; eapply AbsBind_map.
      now right.
    Qed.

  End SBindIn.

  Section BindIn.

    Lemma BindIn_fun: forall [A B: Type] (a: A) (b b': B) l, BindIn a b l -> BindIn a b' l -> b' = b.
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

    Lemma BindIn_cons_inv [A B: Type] [x x0: A] [y y0: B] [l: list (A*B)]
      (NE: x <> x0) (BI: BindIn x y ((x0, y0) :: l))
      : BindIn x y l.
    Proof using Type.
      inversion BI; subst; [ congruence | assumption ].
    Qed.

    Lemma BindIn_findA_reflect_eq
      [A B: Type] [a: A] [b: B] [l] [eqb]
      (reflect: forall x y, Bool.reflect (x = y) (eqb x y))
      (HBindIn: BindIn a b l):
      findA (eqb a) l = Some b.
    Proof.
      induction HBindIn; cbn.
      - now destruct (reflect x x).
      - now destruct (reflect x x').
    Qed.

    Fixpoint remove_bind [A B: Type] [eqA: A -> A -> Prop] (eqA_dec: forall x y, {eqA x y} + {~eqA x y}) (k: A) (l: list (A*B)): list (A*B) :=
      match l with
      | [] => []
      | (x,y)::l =>
          if eqA_dec x k then
            @remove_bind A B eqA eqA_dec k l
          else
            (x,y)::(@remove_bind A B eqA eqA_dec k l)
      end.

  End BindIn.

  Section AbsBind2.

    Lemma AbsBind2_In_l [A B: Type] [a: A] [b: B] [l] (AB: AbsBind2 a b l):
      forall y, ~ In (a, y) l.
    Proof using Type.
      induction AB as [ a0 b0 | a1 a2 b1 b2 l1 NE1 NE2 AB1 IH1 ]; intros y IN;
        [ contradiction | ].
      destruct IN as [ EQ | IN ]; [ inversion EQ; congruence | exact (IH1 y IN) ].
    Qed.

    Lemma SBinds2_fun [A B: Type] [l: list (A*B)] (SB: SBinds2 l):
      forall a x y, In (a, x) l -> In (a, y) l -> x = y.
    Proof using Type.
      induction SB as [ | a0 b0 l0 AB2 SB0 IH ]; intros a x y IN1 IN2; [ contradiction | ].
      destruct IN1 as [ E1 | IN1 ]; destruct IN2 as [ E2 | IN2 ].
      - inversion E1; inversion E2; congruence.
      - inversion E1; subst; now specialize (AbsBind2_In_l AB2 y IN2).
      - inversion E2; subst; now specialize (AbsBind2_In_l AB2 x IN1).
      - exact (IH a x y IN1 IN2).
    Qed.

    Lemma AbsBind2_filter [A B: Type] (g: A * B -> bool) [a: A] [b: B] [l]
      (AB: AbsBind2 a b l)
      : AbsBind2 a b (List.filter g l).
    Proof using Type.
      induction AB as [ a0 b0 | a1 a2 b1 b2 l1 NE1 NE2 AB IH ]; [ constructor | ].
      cbn [List.filter]; destruct (g (a2, b2));
        [ exact (AbsBind2_cons a1 a2 b1 b2 _ NE1 NE2 IH) | exact IH ].
    Qed.

    Lemma SBinds2_filter [A B: Type] (g: A * B -> bool) [l: list (A * B)]
      (SB: SBinds2 l)
      : SBinds2 (List.filter g l).
    Proof using Type.
      induction SB as [ | a b l AB SB IH ]; [ constructor | ].
      cbn [List.filter]; destruct (g (a, b));
        [ exact (SBinds2_cons a b _ (AbsBind2_filter g AB) IH) | exact IH ].
    Qed.

    Lemma AbsBind2_of_notin [A B: Type] [a: A] [b: B] [l]
      (D: forall a' b', In (a', b') l -> a <> a' /\ b <> b')
      : AbsBind2 a b l.
    Proof using Type.
      induction l as [ | [ a' b' ] l IH ]; [ constructor | ].
      destruct (D a' b' (or_introl eq_refl)) as ( NA & NB ).
      exact (AbsBind2_cons a a' b b' l NA NB
               (IH (fun x y INxy => D x y (or_intror INxy)))).
    Qed.

    Lemma AbsBind2_app [A B: Type] [a: A] [b: B] [l1 l2]
      (AB: AbsBind2 a b l1)
      (D: forall a' b', In (a', b') l2 -> a <> a' /\ b <> b')
      : AbsBind2 a b (l1 ++ l2).
    Proof using Type.
      induction AB as [ a0 b0 | a1 a2 b1 b2 l NE1 NE2 AB IH ];
        [ exact (AbsBind2_of_notin D) | ].
      cbn [List.app]; exact (AbsBind2_cons a1 a2 b1 b2 _ NE1 NE2 (IH D)).
    Qed.

    Lemma SBinds2_app_intro [A B: Type] [l1 l2: list (A * B)]
      (S1: SBinds2 l1) (S2: SBinds2 l2)
      (D: forall a x a' y, In (a, x) l1 -> In (a', y) l2 -> a <> a' /\ x <> y)
      : SBinds2 (l1 ++ l2).
    Proof using Type.
      induction S1 as [ | a b l AB S1 IH ]; [ exact S2 | ].
      cbn [List.app].
      refine (SBinds2_cons a b (l ++ l2) (AbsBind2_app AB _) (IH _)).
      - intros a' b' INab; exact (D a b a' b' (or_introl eq_refl) INab).
      - intros a0 x a' y IN1 IN2; exact (D a0 x a' y (or_intror IN1) IN2).
    Qed.

  End AbsBind2.

  Section BMap.

    Lemma AbsBMap_In [A B C: Type] [a: A] [b: B] [l: list (A*(B*C))]
      (AB: AbsBMap a b l) [a' b' c'] (IN: In (a',(b',c')) l)
      : a <> a' /\ b <> b'.
    Proof.
      induction AB as [ | ?a ?b a0 b0 c0 l NEa NEb AB IH ];
        [ now inversion IN | ].
      destruct IN as [ EQ | IN ]; [ injection EQ as <- <- <- | ];
        now auto.
    Qed.

    Lemma AbsBMap_intro [A B C: Type] [a: A] [b: B] [l: list (A*(B*C))]
      (NE: forall a' b' c', In (a',(b',c')) l -> a <> a' /\ b <> b')
      : AbsBMap a b l.
    Proof.
      induction l as [ | ( a0 & b0 & c0 ) l IH ]; [ now constructor | ].
      destruct (NE a0 b0 c0 (or_introl eq_refl)) as ( NEa & NEb ).
      constructor; [ exact NEa | exact NEb | ].
      apply IH; intros a' b' c' IN; exact (NE a' b' c' (or_intror IN)).
    Qed.

    Lemma AbsBMap_AbsBind2 [A B C: Type] [a: A] [b: B] [c: C] [l: list (A*(B*C))]
      (AB: AbsBMap a b l): AbsBind2 a (b,c) l.
    Proof.
      induction AB as [ | ?a ?b a0 b0 c0 l NEa NEb AB IH ]; constructor;
        [ exact NEa | | exact IH ].
      now injection 1 as EQ.
    Qed.

    Lemma BMap_SBinds2 [A B C: Type] [l: list (A*(B*C))] (BM: BMap l): SBinds2 l.
    Proof.
      induction BM as [ | a b c l AB BM IH ]; constructor;
        [ exact (AbsBMap_AbsBind2 AB) | exact IH ].
    Qed.

    Lemma BMap_b_fun [A B C: Type] [l: list (A*(B*C))] (BM: BMap l)
      [a1 a2 b c1 c2] (IN1: In (a1,(b,c1)) l) (IN2: In (a2,(b,c2)) l)
      : a1 = a2 /\ c1 = c2.
    Proof.
      induction BM as [ | a b0 c0 l AB BM IH ]; [ now inversion IN1 | ].
      destruct IN1 as [ EQ1 | IN1 ]; destruct IN2 as [ EQ2 | IN2 ].
      - injection EQ1 as Ea1 Eb1 Ec1; injection EQ2 as Ea2 Eb2 Ec2.
        split; congruence.
      - injection EQ1 as Ea1 Eb1 Ec1; subst.
        destruct (AbsBMap_In AB IN2) as ( _ & NE ); now contradiction NE.
      - injection EQ2 as Ea2 Eb2 Ec2; subst.
        destruct (AbsBMap_In AB IN1) as ( _ & NE ); now contradiction NE.
      - exact (IH IN1 IN2).
    Qed.

    Lemma BMap_In_BindIn [A B C: Type] [l: list (A*(B*C))] (BM: BMap l)
      [a b c] (IN: In (a,(b,c)) l): BindIn a (b,c) l.
    Proof.
      induction BM as [ | a0 b0 c0 l AB BM IH ]; [ now inversion IN | ].
      destruct IN as [ EQ | IN ];
        [ injection EQ as Ea Eb Ec; subst; now constructor | ].
      destruct (AbsBMap_In AB IN) as ( NEa & _ ).
      now constructor; auto.
    Qed.

    Fixpoint bmap_update_a [A B C: Type] (eqbA: A -> A -> bool) (a: A) (f: C -> C)
      (l: list (A*(B*C))): list (A*(B*C)) :=
      match l with
      | [] => []
      | (a',(b',c'))::r =>
          if eqbA a a' then (a',(b', f c'))::r
          else (a',(b',c'))::bmap_update_a eqbA a f r
      end.

    Lemma AbsBMap_bmap_update_a [A B C: Type] [eqbA] [a0: A] [f: C -> C]
      [a b] [l: list (A*(B*C))] (AB: AbsBMap a b l)
      : AbsBMap a b (bmap_update_a (B := B) eqbA a0 f l).
    Proof.
      induction AB as [ | ?a ?b a' b' c' l NEa NEb AB IH ]; [ now constructor | ].
      cbn [bmap_update_a]; destruct (eqbA a0 a'); now constructor.
    Qed.

    Lemma bmap_update_a_BMap [A B C: Type] [eqbA] [a0: A] [f: C -> C]
      [l: list (A*(B*C))] (BM: BMap l)
      : BMap (bmap_update_a (B := B) eqbA a0 f l).
    Proof.
      induction BM as [ | a b c l AB BM IH ]; [ now constructor | ].
      cbn [bmap_update_a]; destruct (eqbA a0 a);
        constructor;
        solve [ exact AB | exact (AbsBMap_bmap_update_a AB) | exact BM | exact IH ].
    Qed.

    Lemma bmap_update_a_BindIn_eq [A B C: Type] [eqbA] [a: A] [f: C -> C]
      [b c] [l: list (A*(B*C))]
      (RFL: forall x y, Bool.reflect (x = y) (eqbA x y))
      (IN: BindIn a (b,c) l)
      : BindIn a (b, f c) (bmap_update_a eqbA a f l).
    Proof.
      induction l as [ | ( a' & b' & c' ) l IH ]; [ now inversion IN | ].
      cbn [bmap_update_a]; destruct (RFL a a') as [ EQ | NE ].
      - subst a'; inversion IN as [ | ?x ?y ?l ?x' ?y' NE ]; subst;
          [ now constructor | now contradiction NE ].
      - constructor; [ exact NE | apply IH ].
        inversion IN as [ ?x ?y ?l | ?x ?y ?l ?x' ?y' ?NE IN' ]; subst;
          [ now contradiction NE | exact IN' ].
    Qed.

    Lemma bmap_update_a_BindIn_neq [A B C: Type] [eqbA] [a0 a: A] [f: C -> C]
      [b c] [l: list (A*(B*C))]
      (RFL: forall x y, Bool.reflect (x = y) (eqbA x y))
      (NE: a <> a0) (IN: BindIn a (b,c) l)
      : BindIn a (b, c) (bmap_update_a eqbA a0 f l).
    Proof.
      induction l as [ | ( a' & b' & c' ) l IH ]; [ now inversion IN | ].
      cbn [bmap_update_a]; destruct (RFL a0 a') as [ EQ | NE' ].
      - subst a'; inversion IN as [ | ?x ?y ?l ?x' ?y' ?NE IN' ]; subst;
          [ now contradiction NE | now constructor ].
      - inversion IN as [ ?x ?y ?l | ?x ?y ?l ?x' ?y' ?NE0 IN' ]; subst;
          [ now constructor | now constructor; auto ].
    Qed.

    Lemma bmap_update_a_BindIn_inv [A B C: Type] [eqbA] [a0 a: A] [f: C -> C]
      [b c'] [l: list (A*(B*C))]
      (RFL: forall x y, Bool.reflect (x = y) (eqbA x y))
      (IN: BindIn a (b,c') (bmap_update_a eqbA a0 f l))
      : exists c, BindIn a (b,c) l
                  /\ ((a <> a0 /\ c' = c) \/ (a = a0 /\ c' = f c)).
    Proof.
      induction l as [ | ( a1 & b1 & c1 ) l IH ]; [ now inversion IN | ].
      cbn [bmap_update_a] in IN; destruct (RFL a0 a1) as [ EQ | NE1 ].
      - subst a1.
        inversion IN as [ ?x ?y ?l | ?x ?y ?l ?x' ?y' NE IN' ]; subst.
        + eexists; split; [ now constructor | now right ].
        + exists c'; split;
            [ constructor; [ exact NE | exact IN' ] | now left ].
      - inversion IN as [ ?x ?y ?l | ?x ?y ?l ?x' ?y' NE IN' ]; subst.
        + eexists; split;
            [ now constructor | left; split; [ exact (not_eq_sym NE1) | reflexivity ] ].
        + destruct (IH IN') as ( c & IN0 & DSJ ).
          exists c; split; [ now constructor | exact DSJ ].
    Qed.

    Lemma bmap_update_a_In_inv [A B C: Type] [eqbA] [a0 a: A] [f: C -> C]
      [b c'] [l: list (A*(B*C))]
      (IN: In (a,(b,c')) (bmap_update_a eqbA a0 f l))
      : exists c, In (a,(b,c)) l.
    Proof.
      induction l as [ | ( a1 & b1 & c1 ) l IH ]; [ now inversion IN | ].
      cbn [bmap_update_a] in IN; destruct (eqbA a0 a1).
      - destruct IN as [ EQ | IN ].
        + injection EQ as Ea Eb Ec; subst a; subst b; exists c1; now left.
        + exists c'; now right.
      - destruct IN as [ EQ | IN ].
        + injection EQ as Ea Eb Ec; subst a; subst b; exists c1; now left.
        + destruct (IH IN) as ( c & IN0 ); exists c; now right.
    Qed.

  End BMap.

End Bindings.

Arguments BMap [A B C] _.

#[global] Hint Resolve SBinds_In: datatypes.
#[global] Hint Resolve SBindIn_BindIn: datatypes.
#[global] Hint Resolve BindIn_In: datatypes.
#[global] Hint Resolve BindIn_fun: datatypes.

(* find variant which uses decidable equality *)
Section SFind.

  Fixpoint sfind [A: EqDec.type] [B: Type] (a: A) (l: list (A * B)): option B :=
    match l with
    | [] => None
    | (a',b)::l =>
        if eqb a' a then
          Some b
        else
          sfind a l
    end.

  Fixpoint sfind_r [A B: Type] (eqb_b: B -> B -> bool) (b: B) (l: list (A * B)): option A :=
    match l with
    | [] => None
    | (a, b')::l =>
        if eqb_b b' b then
          Some a
        else
          sfind_r eqb_b b l
    end.

  Lemma sbinds_sfind [A: EqDec.type] [B: Type] [l: list (A*B)]
    (HSBinds: SBinds l)
    : forall a b, SBindIn a b l <-> sfind a l = Some b.
  Proof.
    intros a b; split.
    - intros HBind.
      induction HBind.
      cbn.
      destruct (eqb_spec x x); [ auto | contradiction ].
      cbn.
      destruct (eqb_spec x' x); [ congruence | cbn ].
      apply IHHBind.
      now inversion HSBinds.
    - intros Esfind.
      induction HSBinds.
      discriminate.
      cbn in Esfind.
      destruct (eqb_spec a0 a); subst.
      now inversion Esfind; subst; constructor.
      right. congruence. eauto.
  Qed.

  Lemma sfind_None_In [A: EqDec.type] [B: Type] [a] [l: list (A*B)]
    (Esfind: sfind a l = None)
    : forall b, ~In (a,b) l.
  Proof.
    induction l as [ | [ a' b' ] ]; cbn; eauto.
    intros b [ Heq | HIn ].
    inversion Heq; subst; clear Heq.
    - cbn in Esfind.
      destruct (eqb_spec a a) as [ _ | Hneq ]; [ discriminate | contradiction ].
    - cbn in Esfind.
      destruct (eqb_spec a' a) as [ _ | Hneq ]; [ discriminate | ].
      eapply IHl; eauto.
  Qed.

  Lemma sfind_r_In [A B: Type] [eqb_b: B -> B -> bool] [b: B] [l: list (A*B)] [a]
    (EQB: forall x y, Bool.reflect (x = y) (eqb_b x y))
    (EQ: sfind_r eqb_b b l = Some a)
    : In (a, b) l.
  Proof.
    induction l as [ | [ a' b' ] l IH ]; cbn in EQ; [ discriminate | ].
    destruct (EQB b' b) as [ Heq | Hneq ].
    - subst b'; inversion EQ; subst; now left.
    - now right; apply IH.
  Qed.

  Lemma sfind_r_None_not_In [A B: Type] [eqb_b: B -> B -> bool] [b: B] [l: list (A*B)]
    (EQB: forall x y, Bool.reflect (x = y) (eqb_b x y))
    (EQ: sfind_r eqb_b b l = None)
    : forall a, ~In (a, b) l.
  Proof.
    induction l as [ | [ a' b' ] l IH ]; cbn in EQ; [ now cbn | ].
    destruct (EQB b' b) as [ Heq | Hneq ]; [ discriminate | ].
    intros a [ Heq | HIn ]; [ inversion Heq; congruence | ].
    eapply IH; eassumption.
  Qed.

End SFind.

(* Facts about lists of pairs *)
Section Pair.
  Definition pair_l_eqA [A B: Type] (eqA: A -> A -> Prop) (x y: (A*B)) := eqA (fst x) (fst y).

  Lemma pair_l_eqA_dec [A B: Type] [eqA: A -> A -> Prop] (eqA_dec: forall x y, {eqA x y} + {~eqA x y}): forall (x y: (A*B)), { pair_l_eqA eqA x y } + { ~ pair_l_eqA eqA x y }.
  Proof.
    destruct x as [ xa xb ], y as [ ya yb ].
    destruct (eqA_dec xa ya) as [ Heq | Hneq ];
      now constructor.
  Qed.

End Pair.

(* Counting map *)
Section Mapi.

  Fixpoint mapi' [A B: Type] (f: A -> nat -> B) (l: list A) (n: nat) {struct l}: list B :=
    match l with
    | [] => []
    | x::xs =>
        (f x n)::(mapi' f xs (S n))
    end.

  Definition mapi [A B: Type] (f: A -> nat -> B) (l: list A): list B := mapi' f l 0.

  Lemma concat_mapi'_inv [A B: Type] (g: A -> nat -> list B) (l: list A):
    forall k b, In b (List.concat (mapi' g l k)) ->
    exists i x, List.nth_error l i = Some x /\ In b (g x (k + i)%nat).
  Proof using Type.
    induction l as [ | x l IH ]; intros k b IN; [ contradiction | ].
    cbn [mapi' List.concat] in IN.
    destruct (in_app_or _ _ _ IN) as [ INh | INt ].
    - exists 0%nat, x; split; [ reflexivity | rewrite Nat.add_0_r; exact INh ].
    - destruct (IH (S k) b INt) as ( i & y & NTH & INg ).
      exists (S i), y; split; [ exact NTH | ].
      assert (EK: (k + S i)%nat = (S k + i)%nat) by lia.
      rewrite EK; exact INg.
  Qed.

  Lemma concat_mapi'_fwd [A B: Type] (g: A -> nat -> list B) (l: list A):
    forall k i x b, List.nth_error l i = Some x -> In b (g x (k + i)%nat) ->
                    In b (List.concat (mapi' g l k)).
  Proof using Type.
    induction l as [ | y l IH ]; intros k i x b NTH INg;
      [ destruct i; discriminate NTH | ].
    cbn [mapi' List.concat]; apply in_or_app.
    destruct i as [ | i ]; cbn [List.nth_error] in NTH.
    - injection NTH as <-; left; rewrite Nat.add_0_r in INg; exact INg.
    - right; refine (IH (S k) i x b NTH _).
      assert (EK: (S k + i)%nat = (k + S i)%nat) by lia.
      rewrite EK; exact INg.
  Qed.

End Mapi.

(* Fallible map, either all maps succeed, or none *)
Section MapOpt.

  Fixpoint map_opt [A B: Type] (f: A -> option B) (l: list A) : option (list B) :=
    match l with
    | [] => Some []
    | a::l =>
        match f a, map_opt f l with
        | Some b, Some bs => Some (b :: bs)
        | _, _ => None
        end
    end.

  Lemma map_opt_length [A B: Type] [f: A -> option B] [l: list A] [l': list B]
    (MAP: map_opt f l = Some l'):
    length l' = length l.
  Proof.
    revert l' MAP.
    induction l as [ | a l IH ]; intros l' MAP; cbn in MAP.
    - injection MAP as <-; reflexivity.
    - destruct (f a) as [ b | ]; [ | discriminate ].
      destruct (map_opt f l) as [ bs | ]; [ | discriminate ].
      injection MAP as <-; cbn; f_equal; exact (IH _ eq_refl).
  Qed.

End MapOpt.

(* Facts about 2 list Forall predicate *)
Section Forall2.

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

  Fixpoint forall2b [A B: Type] (f: A -> B -> bool) (l: list A) (l': list B): bool :=
    match l, l' with
    | [], [] => true
    | x::xs, y::ys =>
        if f x y then
          forall2b f xs ys
        else
          false
    | _,_ => false
    end.

  (* [forall2b] decides the [Forall2] of its pointwise boolean check. *)
  Lemma forall2b_Forall2 [A B: Type] (f: A -> B -> bool) (l: list A) (l': list B):
    forall2b f l l' = true <-> Forall2 (fun a b => f a b = true) l l'.
  Proof.
    split.
    - revert l'; induction l as [|x xs IH]; intros [|y ys] EQ;
        cbn in EQ; try discriminate EQ.
      + constructor.
      + destruct (f x y) eqn:E; [ | discriminate EQ ].
        constructor; [ exact E | exact (IH ys EQ) ].
    - induction 1 as [ | x y xs ys Hxy _ IH ]; cbn.
      + reflexivity.
      + rewrite Hxy; exact IH.
  Qed.

  (* [forall2b_opt eqb f l l'] returns true iff for each element of [a] of [l],
     [f a = Some b] and [b] is in [l'] at the same index as [a]. Both lists must have the same length.*)
  Fixpoint forall2b_opt [A B: Type] (eqb: B -> B -> bool) (f: A -> option B)
                       (l: list A) (l': list B): bool :=
    match l, l' with
    | [], [] => true
    | x::xs, y::ys =>
        match f x with
        | Some fx => eqb fx y && forall2b_opt eqb f xs ys
        | None => false
        end
    | _,_ => false
    end.

    Lemma map_opt_Forall2 [A B: Type] [f: A -> option B] [R: A -> B -> Prop]
      (SOUND: forall a b, R a b -> f a = Some b)
      [l l'] (FORALL2: Forall2 R l l'):
      map_opt f l = Some l'.
    Proof.
      induction FORALL2 as [| a b l l' Hr _ IH]; cbn.
      - reflexivity.
      - rewrite (SOUND _ _ Hr), IH; reflexivity.
    Qed.

    Lemma map_opt_Forall2_inv [A B: Type] [f: A -> option B] [R: A -> B -> Prop]
      (COMPLETE: forall a b, f a = Some b -> R a b)
      [l l'] (EQ: map_opt f l = Some l'):
      Forall2 R l l'.
    Proof.
      revert l' EQ; induction l as [| a l IH]; intros l' EQ; cbn in EQ.
      - inversion EQ; subst; constructor.
      - destruct (f a) eqn:EQfa; [| discriminate].
        destruct (map_opt f l) eqn:EQmap; [| discriminate].
        inversion EQ; subst.
        constructor.
        + apply COMPLETE, EQfa.
        + now refine (IH _ _).
    Qed.

    Lemma forall2b_opt_map_opt [A B: Type] (eqb: B -> B -> bool) (f: A -> option B)
      (l: list A) (ts l': list B):
      map_opt f l = Some ts -> forall2b_opt eqb f l l' = forall2b eqb ts l'.
    Proof.
      revert ts l'; induction l as [| a l IH]; intros ts l' H; cbn in H.
      - inversion H; subst; destruct l'; reflexivity.
      - destruct (f a) as [b|] eqn:Ea; [| discriminate].
        destruct (map_opt f l) as [bs|] eqn:Eargs; [| discriminate].
        inversion H; subst; clear H.
        destruct l' as [| y ys]; cbn; [reflexivity |].
        rewrite Ea, (IH bs ys eq_refl).
        destruct (eqb b y); reflexivity.
    Qed.

End Forall2.

(* Equality between lists *)
Section Eqb.

  Definition list_eqb [A: Type] (eqb: A -> A -> bool) (l: list A) (l': list A): bool := forall2b eqb l l'.

  Lemma list_eqb_refl [A: Type] (eqb: A -> A -> bool) (eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y)): forall l, list_eqb eqb l l = true.
  Proof.
    induction l; [ reflexivity | ].
    cbn.
    destruct (eqb_spec a a) as [ _ | ]; [ now cbn | contradiction ].
  Qed.

  Lemma list_eqb_spec [A: Type] (eqb: A -> A -> bool): forall l l' (eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y)), Bool.reflect (l = l') (list_eqb eqb l l').
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

End Eqb.

HB.instance Definition _ (A: EqDec.type) :=
  hasEqDec.Build (list A) (list_eqb (@eqb A))
    (fun l l' => list_eqb_spec (@eqb A) l l' (@eqb_spec A)).

#[global] Hint Resolve list_eqb_refl: datatypes.
#[global] Hint Resolve list_eqb_spec: datatypes.

(* Joined filter and map like in OCaml *)
Section FilterMap.

  Fixpoint filter_map [A B: Type] (f: A -> option B) (l: list A): list B :=
    match l with
    | [] => []
    | a::t =>
        match f a with
        | Some b => b :: filter_map f t
        | None => filter_map f t
        end
    end.

End FilterMap.

(* Facts about findA *)
Section findA.

  Lemma findA_app [A B: Type] (f: A -> bool) (l1 l2: list (A*B)) b:
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

End findA.

Section FoldLeft.

  Inductive FoldLeft [A B: Type] (P: B -> A -> Prop) (f: B -> A -> B): B -> list A -> Prop :=
  | FoldLeft_nil: forall acc, FoldLeft P f acc []
  | FoldLeft_cons: forall acc x rest,
      P acc x ->
      FoldLeft P f (f acc x) rest ->
      FoldLeft P f acc (x :: rest)
  .

  Fixpoint fold_left_b [A B: Type] (P_b: B -> A -> bool) (f: B -> A -> B)
                       (acc: B) (l: list A) : bool :=
    match l with
    | [] => true
    | x :: rest => P_b acc x && fold_left_b P_b f (f acc x) rest
    end.

  Lemma fold_left_b_spec [A B: Type] (P: B -> A -> Prop) (P_b: B -> A -> bool)
    (P_spec: forall acc x, Bool.reflect (P acc x) (P_b acc x))
    (f: B -> A -> B):
    forall acc l, Bool.reflect (FoldLeft P f acc l) (fold_left_b P_b f acc l).
  Proof.
    intros acc l; revert acc.
    induction l as [| x rest IH]; intros acc; cbn.
    - apply ReflectT; constructor.
    - destruct (P_spec acc x) as [HP | HnP]; cbn.
      + destruct (IH (f acc x)) as [HF | HnF].
        * apply ReflectT; now constructor.
        * apply ReflectF; intros H; inversion H; contradiction.
      + apply ReflectF; intros H; inversion H; contradiction.
  Qed.

End FoldLeft.

Section SortedDec.

  Fixpoint sorted_strict_b [A: Type] (ltb: A -> A -> bool) (l: list A) : bool :=
    match l with
    | [] => true
    | x :: t =>
        match t with
        | [] => true
        | y :: _ => ltb x y && sorted_strict_b ltb t
        end
    end.

  Lemma sorted_strict_b_spec [A: Type] (lt: A -> A -> Prop) (ltb: A -> A -> bool)
    (ltb_spec: forall x y, Bool.reflect (lt x y) (ltb x y)):
    forall l, Bool.reflect (Sorted lt l) (sorted_strict_b ltb l).
  Proof.
    induction l as [| x t IH].
    - apply ReflectT; constructor.
    - destruct t as [| y rest].
      + apply ReflectT; repeat constructor.
      + cbn [sorted_strict_b].
        apply Bool.iff_reflect.
        rewrite Bool.andb_true_iff.
        rewrite <- (Bool.reflect_iff _ _ (ltb_spec x y)).
        rewrite <- (Bool.reflect_iff _ _ IH).
        split.
        * intros HS; inversion HS as [| ? ? Hsub Hhd]; subst.
          inversion Hhd; subst; split; assumption.
        * intros [Hlt HSt].
          constructor; [exact HSt | constructor; exact Hlt].
  Qed.

End SortedDec.

(* fold_left for fallible operations *)
Section FoldLeftOpt.

  Fixpoint fold_left_opt [A B: Type] (f: A -> B -> option A) (l: list B) (acc: A): option A :=
    match l with
    | [] => Some acc
    | x::xs =>
        match f acc x with
        | Some acc => fold_left_opt f xs acc
        | None => None
        end
    end.

  Lemma fold_left_opt_cons [A B: Type] (f: A -> B -> option A) l acc x:
    fold_left_opt f (x::l) acc =
      match f acc x with
      | Some acc' =>  fold_left_opt f l acc'
      | None => None
      end.
  Proof.
    now cbn; destruct (f acc x).
  Qed.

  Lemma fold_left_opt_nil [A B: Type] (f: A -> B -> option _) acc:
    fold_left_opt f [] acc = Some acc.
  Proof.
    reflexivity.
  Qed.

End FoldLeftOpt.

(* Facts about split and combine *)
Section SplitCombine.

  Lemma split_map [A B: Type] (l: list (A * B)): exists l_l l_r, split l = (l_l, l_r) /\ combine l_l l_r = l /\ map fst l = l_l /\ map snd l = l_r.
  Proof.
    induction l as [ | ( hd_l & hd_r ) tl ] ; [ now repeat econstructor | ].
    destruct IHtl as ( l_l & l_r & Hsplit & Hcombine & Hfst & Hsnd ).
    exists (hd_l::map fst tl), (hd_r::map snd tl).
    split; [ cbn; rewrite Hsplit; congruence | ].
    split; [ cbn; now rewrite Hfst, Hsnd, Hcombine | ].
    now split.
  Qed.

  Lemma map_fst_combine [A B: Type] (l: list A) (l': list B)
    (LEN: length l' = length l):
    map fst (combine l l') = l.
  Proof.
    destruct (split_map (combine l l')) as ( l_l & l_r & SPL & _ & EFST & _ ).
    rewrite (combine_split l l' (eq_sym LEN)) in SPL.
    exact (eq_trans EFST (eq_sym (f_equal fst SPL))).
  Qed.

  Lemma map_snd_combine [A B: Type] (l: list A) (l': list B)
    (LEN: length l' = length l):
    map snd (combine l l') = l'.
  Proof.
    destruct (split_map (combine l l')) as ( l_l & l_r & SPL & _ & _ & ESND ).
    rewrite (combine_split l l' (eq_sym LEN)) in SPL.
    exact (eq_trans ESND (eq_sym (f_equal snd SPL))).
  Qed.

End SplitCombine.

(* Facts about NoDup and NoDupA *)
Section NoDup.

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

End NoDup.

(* Facts about rev *)
Section Rev.

  (* Recursion schemes for rev *)
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

End Rev.

(* [removelast_n n l] perform [n] times [removelast l] *)
Section RemoveLastN.

  Fixpoint removelast_n [A: Type] (n: nat) (l: list A) : list A :=
    match n with
    | O => l
    | S n' => removelast_n n' (removelast l)
    end.

  Lemma length_removelast [A: Type] (l: list A) : length (removelast l) = length l - 1.
  Proof.
    rewrite removelast_firstn_len, length_firstn. lia.
  Qed.

  Lemma length_removelast_n [A: Type] (n: nat) (l: list A) :
    length (removelast_n n l) = length l - n.
  Proof.
    revert l; induction n as [|n IH]; intro l; cbn [removelast_n].
    - lia.
    - rewrite IH, length_removelast. lia.
  Qed.

  Lemma removelast_n_app_length [A: Type] (l1 l2: list A) :
    removelast_n (length l2) (l1 ++ l2) = l1.
  Proof.
    induction l2 as [|x l2 IH] using rev_rect.
    - cbn [removelast_n]. rewrite app_nil_r. reflexivity.
    - rewrite length_app, Nat.add_1_r, app_assoc.
      cbn [removelast_n]. rewrite removelast_last. exact IH.
  Qed.

  Lemma map_removelast [A B: Type] (f: A -> B) (l: list A) :
    removelast (map f l) = map f (removelast l).
  Proof.
    induction l as [|a l _] using rev_rect.
    - reflexivity.
    - rewrite map_app; cbn [map]; rewrite removelast_last, removelast_last. reflexivity.
  Qed.

  Lemma map_removelast_n [A B: Type] (f: A -> B) (n: nat) (l: list A) :
    removelast_n n (map f l) = map f (removelast_n n l).
  Proof.
    revert l; induction n as [|n IH]; intro l; cbn [removelast_n].
    - reflexivity.
    - rewrite map_removelast. apply IH.
  Qed.

  Lemma removelast_n_snoc [A: Type] (n: nat) (l: list A) (x: A):
    removelast_n (S n) (l ++ [x]) = removelast_n n l.
  Proof.
    cbn [removelast_n]; rewrite removelast_last; reflexivity.
  Qed.

  Lemma removelast_n_split [A: Type] (n: nat):
    forall (l: list A) (LE: (n <= length l)%nat),
    exists suf, l = removelast_n n l ++ suf.
  Proof.
    induction n as [ | n IH ]; intros l LE.
    - exists []; cbn [removelast_n]; rewrite app_nil_r; reflexivity.
    - assert (NENIL: l <> []) by (intros ENIL; subst l; cbn in LE;lia).
      destruct (exists_last NENIL) as ( l' & ( x & ESNOC ) ).
      assert (LE': (n <= length l')%nat)
        by (subst l; rewrite length_app in LE; cbn in LE; lia).
      destruct (IH l' LE') as ( suf & ESPLIT ).
      exists (suf ++ [x]).
      rewrite ESNOC, removelast_n_snoc, app_assoc, <- ESPLIT; reflexivity.
  Qed.

  Lemma nth_error_removelast_n [A: Type] (n: nat) (l: list A) (k: nat)
    (LT: (k < length l - n)%nat):
    nth_error (removelast_n n l) k = nth_error l k.
  Proof.
    assert (LE: (n <= length l)%nat) by lia.
    destruct (removelast_n_split n l LE) as ( suf & ESPLIT ).
    replace (nth_error l k) with (nth_error (removelast_n n l ++ suf) k)
      by (rewrite <- ESPLIT; reflexivity).
    symmetry; apply nth_error_app1.
    rewrite length_removelast_n; lia.
  Qed.

End RemoveLastN.
