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

From Stdlib Require Import FunctionalExtensionality PropExtensionality Classical
  IndefiniteDescription.
From GallinaC.Corec Require Export Oracle.

Definition Setof (X: Type): Type := X -> Prop.

Definition member {X} (S: Setof X) (x: X): Prop := S x.

Definition subset {X: Type} (S S': Setof X): Prop :=
  forall x, member S x -> member S' x.

Lemma subset_refl {X: Type}: forall (S: Setof X), subset S S.
Proof.
  intros S x Hm; exact Hm.
Qed.

Lemma subset_trans {X: Type}: forall (S S' S'': Setof X),
    subset S S' -> subset S' S'' -> subset S S''.
Proof.
  intros S S' S'' Hs1 Hs2 x Hm.
  apply Hs2, Hs1, Hm.
Qed.

Lemma subset_antisym {X: Type}: forall (S S': Setof X),
    subset S S' -> subset S' S -> S = S'.
Proof.
  intros S S' Hs Hs'.
  extensionality x.
  apply propositional_extensionality; split; intro HS.
  - apply Hs, HS.
  - apply Hs', HS.
Qed.

Lemma set_equal {X: Type}: forall (S S': Setof X),
    S = S' <-> forall x, member S x <-> member S' x.
Proof.
  split.
  - intro Heq; subst; split; auto.
  - intros Hm.
    extensionality x.
    apply propositional_extensionality.
    split; intro Hx; now apply Hm.
Qed.

Definition empty{X: Type}: Setof X := fun _ => False.

Lemma empty_subset{X: Type}: forall (S: Setof X), subset empty S.
Proof.
  intros S x Habs; inversion Habs.
Qed.

Lemma subset_empty{X: Type}: forall (S: Setof X),
    subset S empty <-> S = empty.
Proof.
  intro S; split; intro Hs; try (now subst).
  apply set_equal.
  intros x; split; intro Hm; auto.
  inversion Hm.
Qed.

Definition single{X: Type}(x: X): Setof X :=
  fun y => y = x.

Lemma member_subset{X: Type}:
  forall (x:X) S S', member S x -> subset S S' -> member S' x.
Proof.
  intros x S S' Hm Hs.
  apply Hs, Hm.
Qed.

Lemma member_single{X: Type}: forall (x: X),
    member (single x) x.
Proof.
  intro x.
  reflexivity.
Qed.

Lemma member_single_iff{X: Type}: forall (x y: X),
    member (single x) y <-> y = x.
Proof.
  split.
  - intro Hm.
    exact Hm.
  - intro Heq; subst.
    apply member_single.
Qed.

Definition is_empty {X: Type} (S: Setof X) := S = empty.

Lemma is_empty_no_member{X: Type}: forall (S: Setof X),
    is_empty S <-> forall x, ~member S x.
Proof.
  split.
  - intros He x Hm.
    rewrite He in Hm.
    inversion Hm.
  - intros Hnm.
    unfold is_empty.
    extensionality x.
    specialize (Hnm x).
    unfold member,not in Hnm.
    apply propositional_extensionality.
    split; auto.
    intro Habs; inversion Habs.
Qed.

Lemma not_empty_member{X:Type} :
  forall(S: Setof X), ~is_empty S <-> exists x, member S x.
Proof.
  split.
  - intro Hne.
    rewrite is_empty_no_member in Hne.
    now apply not_all_not_ex in Hne.
  - intros He Hne.
    rewrite is_empty_no_member in Hne.
    destruct He as (x & Hm).
    now apply (Hne x).
Qed.

Lemma single_not_empty {X:Type}: forall (x:X), ~is_empty (single x).
Proof.
  intros x He.
  rewrite is_empty_no_member in He.
  apply (He x),member_single.
Qed.

Lemma not_empty_not_single_2dif{X: Type}:
  forall (S: Setof X) (x: X),
    ~ is_empty S -> S <> single x -> exists y, member S y /\ y <> x.
Proof.
  intros S x Hne Hs.
  rewrite not_empty_member in Hne.
  destruct Hne as (y & Hm).
  apply not_all_not_ex.
  intro Hall.
  apply Hs; clear Hs.
  assert (Hall': forall z, member S z -> z = x).
  {
    intros z Hmz.
    specialize (Hall z).
    apply not_and_or in Hall.
    destruct Hall as [Hmn | Hnn]; [exfalso ; now apply Hmn |].
    now apply NNPP.
  }
  clear Hall.
  apply set_equal; intro z ; split; intro Hmz.
  - now apply member_single_iff, Hall'.
  - rewrite member_single_iff in Hmz; subst.
    now rewrite <- (Hall' y).
Qed.

Lemma not_empty_not_single_2dif_alt{X: Type}:
  forall (S: Setof X),
    ~ is_empty S -> (forall x, S <> single x) ->
    exists x y, member S x /\ member S y /\ y <> x.
Proof.
  intros S Hne Ha.
  specialize Hne as Hne'.
  rewrite not_empty_member in Hne'.
  destruct Hne' as (x & Hmx).
  specialize (Ha x).
  apply not_empty_not_single_2dif with (x := x) in Hne;
    auto.
  destruct Hne as (y & Hmy & Hd).
  firstorder.
Qed.

Lemma ordered_pair_reorder{X: Type} :
  forall (x y: X),
    (fun z => z = x \/ z = y) =
      (fun z => z = y \/ z = x).
Proof.
  intros x y.
  apply set_equal; intro w; split; intro Hm;
    unfold member in *; cbn in * ; tauto.
Qed.

Lemma single_subset_member{X: Type}: forall (S: Setof X) (x:X),
    subset (single x) S <->member S x.
Proof.
  split.
  - intros Hs.
    apply Hs,member_single.
  - intros Hm y Hm'.
    rewrite member_single_iff in Hm'.
    now subst.
Qed.

Definition remove{X: Type}(S: Setof X) (x: X) :=
  fun y => S y /\ y <> x.

Lemma not_member_remove_eq{X: Type}: forall (S: Setof X) (x: X),
    ~ member S x -> remove S x = S.
Proof.
  intros S x Hh.
  apply set_equal; intro y; split; intro Hm; firstorder.
  intro Heq; subst; now apply Hh.
Qed.

Lemma subset_remove{X:Type}: forall (S S': Setof X) (x: X),
    subset S S' -> subset (remove S x) (remove S' x).
  intros S S' x Hs y Hm.
  unfold remove, member in *.
  destruct Hm as (Hm & Hneq).
  split; auto.
  now apply Hs.
Qed.

Definition add{X: Type}(S: Setof X) (x: X) :=
  fun y => S y \/ y = x.

Lemma remove_add{X: Type}: forall (S: Setof X)(x: X),
    subset (remove (add S x) x) S.
Proof.
  intros S x y Hm.
  firstorder.
Qed.

Lemma remove_add_eq{X: Type}: forall (S: Setof X)(x: X),
    ~member S x ->  remove (add S x) x = S.
Proof.
  intros S x Hm.
  apply set_equal ; intro y; split; intro Hm'; firstorder.
  intro Hne; subst; now apply Hm.
Qed.

Lemma add_remove{X: Type}: forall (S: Setof X)(x: X),
    subset S (add (remove S x) x).
Proof.
  intros S x y Hm.
  unfold member,add,remove in *.
  destruct (oracle (y =x)); now constructor.
Qed.

Lemma remove_add_same{X:Type}:
  forall (S: Setof X)(x:X),
    member S x -> S = add (remove (remove S x) x) x.
Proof.
  intros S x Hm.
  apply set_equal ; intro y ; split; intro Hm'.
  - destruct (oracle (x = y)) ; subst; now repeat constructor.
  - destruct (oracle (x = y)) ; subst;auto.
    destruct Hm' as [Hm' | Hm'].
    + now destruct Hm',H.
    + now subst.
Qed.

Lemma add_remove_eq{X: Type}: forall (S: Setof X)(x: X),
    member S x -> add (remove S x) x = S.
Proof.
  intros S x Hm.
  apply set_equal ; intro y; split; intro Hm'.
  - now firstorder; subst.
  - unfold member,add,remove in *.
    destruct (oracle (y =x)).
    + now right.
    + now left.
Qed.

Lemma member_add{X:Type}: forall (S: Setof X)(x:X),
    member S x <-> S = add S x.
Proof.
  split;intros Hm.
  - apply set_equal.
    + intro z ; split; intro Hm'.
      * now left.
      * destruct (oracle (x = z)); try now subst.
        firstorder.
        exfalso.
        now apply n.
  - now rewrite Hm; right.
Qed.

Lemma subset_add{X:Type}: forall (S S': Setof X)(x:X),
    subset S' (add S x) -> {subset S' S} + {member S' x}.
  intros S S' x Hsub.
  destruct (oracle (member S' x)).
  - now right.
  - left.
    intros y Hm.
    unfold subset, add, member in *.
    destruct (Hsub y) as [Hl | Hr]; subst; auto.
    exfalso ; now apply n.
Qed.

Lemma remove_subset {X:Type}: forall (S: Setof X)(x:X),
    subset (remove S x) S.
Proof.
  intros S x y Hm.
  now destruct Hm as (Hm & _).
Qed.

Lemma remove_is_single {X: Type} :
  forall (S: Setof X) (x a: X),
    remove S x = single a -> S = (fun y => y = a \/ y = x)
                             \/ S = fun y => y = a.
Proof.
  intros S x a Heq.
  destruct (oracle (member S x)).
  - left.
    apply set_equal; intro y; split ; intro Hm.
    + unfold member; cbn.
      destruct (oracle (y = x)); [ now right |].
      assert (Hm': (member (remove S x)) y) by (split;auto).
      rewrite Heq in Hm'.
      rewrite member_single_iff in Hm'.
      now left.
    + unfold member in Hm ; cbn in Hm.
      destruct Hm ; subst; auto.
      assert (Hm': (member (remove S x)) a)
        by (rewrite Heq;apply member_single).
      now destruct Hm'.
  - right.
    rewrite not_member_remove_eq in Heq; auto.
Qed.

Definition union {X: Type} (SS: Setof (Setof X)): Setof X :=
  fun (x:X) => exists S, member SS S /\ member S x.

Lemma member_union {X:Type} :
  forall (SS: Setof (Setof X)) (S: Setof X) (x: X),
    member S x -> member SS S -> member (union SS) x.
Proof.
  intros SS S x Hmx HmS.
  now exists S.
Qed.

Lemma member_union_member_one {X:Type}:
  forall (SS: Setof (Setof X)) (x: X),
    member (union SS) x -> exists S, member SS S /\ member S x.
Proof.
  intros SS x (S,(Hm1 & Hm2)).
  now exists S.
Qed.

Lemma member_union_subset {X:Type} :
  forall (SS: Setof (Setof X)) (S: Setof X),
    member SS S -> subset S (union SS).
Proof.
  intros SS S HmS y Hmy.
  eapply member_union; eauto.
Qed.

Lemma union_lub {X:Type}: forall (SS: Setof (Setof X))(Y: Setof X),
    (forall S, member SS S -> subset S Y ) ->
    subset (union SS) Y.
Proof.
  intros SS Y Hall x Hm.
  destruct Hm as (Z & HmZ & Hmx).
  now apply (Hall _ HmZ).
Qed.


Definition fmap{X Y: Type} (S: Setof X) (f: X -> Y): Setof Y :=
  fun y => exists x, S x /\ y = f x.

Lemma is_empty_fmap{X Y: Type}: forall (S: Setof X) (f: X -> Y),
    is_empty S <-> is_empty (fmap S f).
Proof.
  split ; do 2 rewrite is_empty_no_member; intros Hnm z Hnm'.
  -
    destruct Hnm' as (x & Hx & Heq).
    now apply (Hnm x).
  -
    apply (Hnm (f z)).
    now exists z.
Qed.

Lemma member_fmap{X Y: Type}: forall (S: Setof X) (f: X -> Y) (x:X),
    member S x -> member (fmap S f) (f x).
Proof.
  intros S f x Hm.
  now exists x.
Qed.

Lemma fmap_eq{X Y: Type}: forall (S: Setof X) (f g: X -> Y),
    (forall x, member S x -> f x = g x) -> fmap S f = fmap S g.
Proof.
  intros S f g Hae.
  apply set_equal ; intro x; split; intro Hm.
  -
    destruct Hm as (y & Hmy & Heq); subst.
    exists y; split; auto.
  -
    destruct Hm as (y & Hmy & Heq); subst.
    exists y; split; auto.
    now rewrite Hae.
Qed.

Lemma not_empty_fmap{X Y: Type} (S: Setof X)
  (f: X -> Y): ~ is_empty S -> ~ is_empty (fmap S f).
Proof.
  intros Hne He.
  apply Hne.
  now rewrite <- is_empty_fmap in He.
Qed.

Lemma fmap_single{X Y: Type}:
  forall (x: X) (f: X -> Y), fmap (single x) f = single (f x).
Proof.
  intros x f.
  apply set_equal; intro w; split; intro Hm.
  -
    destruct Hm as (u & Hmu & Heq); subst.
    change (single x u) with (member (single x) u) in Hmu.
    rewrite member_single_iff in Hmu; subst.
    apply member_single.
  -
    rewrite member_single_iff in Hm; subst.
    exists x; split; auto.
    unfold single; cbn; reflexivity.
Qed.


Lemma fmap_const_single{A B:Type}:
  forall (S: Setof A), ~is_empty S -> forall (b:B),
      fmap S (fun _: A => b) = single b.
Proof.
  intros S Hne b.
  apply set_equal; intro x ; split; intro Hmx.
  -
    destruct Hmx as (y & Hmy & Heq); subst.
    apply member_single.
  -
    rewrite member_single_iff in Hmx; subst.
    rewrite not_empty_member in Hne.
    destruct Hne as (a & Hm).
    now exists a.
Qed.

Definition comp{X Y Z: Type} (f: Y ->Z) (g: X -> Y): X -> Z := fun x => f (g x).
Infix "°" := (@comp _ _ _) (at level 70, no associativity).


Definition id{X:Type}: X -> X := fun x => x.

Lemma comp_id_right{X Y: Type}: forall (f: X -> Y), f ° id = f.
Proof.
  intro f.
  now extensionality x.
Qed.



Lemma comp_id_left{X Y: Type}: forall (f: X -> Y), id° f = f.
Proof.
  intro f.
  now extensionality x.
Qed.

Definition is_injective{X Y: Type} (f: X ->Y) :=
  forall x y, f x = f y -> x = y.

Definition is_surjective{X Y: Type} (f: X -> Y) :=
  forall y, exists x, y = f x.

Definition is_bijective{X Y: Type} (f: X -> Y) :=
  is_injective f /\ is_surjective f.

Lemma id_is_bijective{X: Type}: is_bijective id(X := X).
Proof.
  split.
  -
    now intros x y Heq.
  -
    intro x; now exists x.
Qed.

Lemma comp_is_bijective{X Y Z: Type}: forall (f: Y -> Z) (g: X -> Y),
    is_bijective f -> is_bijective g -> is_bijective (f° g).
Proof.
  intros f g (Hi1 & Hs1) (Hi2 & Hs2); split.
  -
    intros x y Heq.
    unfold comp in Heq.
    now apply Hi1,Hi2 in Heq.
  -
    intro z.
    destruct (Hs1 z) as (y & Hy).
    destruct (Hs2 y) as (x & Hx); subst.
    now exists x.
Qed.


Lemma is_bijective_inverse {X Y: Type} (f: X -> Y) :
  is_bijective f -> {f': Y -> X | f ° f' = id /\ f' ° f = id}.
  intros (Hi & Hs).
  unshelve eexists.
  -
    exact (fun y => proj1_sig (constructive_indefinite_description _ (Hs y))).
  -
    split.
    +
      extensionality y.
      unfold id,comp; cbn.
      destruct (constructive_indefinite_description _ (Hs y)); cbn.
      now subst.
    +
      extensionality x.
      unfold id,comp; cbn.
      destruct (constructive_indefinite_description _ (Hs (f x))); cbn.
      now apply Hi.
Qed.



Lemma inj_member_fmap{X Y: Type}: forall (S: Setof X) (f: X -> Y) (x: X),
    is_injective f ->  member (fmap S f) (f x) -> member S x.
Proof.
  intros S f x Hi Hm.
  destruct Hm as (u & Hu & Heq).
  apply Hi in Heq; now subst.
Qed.

Lemma inj_fmap_single{X Y: Type} :
  forall (S: Setof X) (f: X -> Y) (x: X),
    (fmap S f) = single (f x) -> is_injective f ->
    S = single x.
Proof.
  intros S f x Hm Hi.
  apply set_equal; intro y ; split; intro Hmy.
  -
    rewrite member_single_iff.
    apply member_fmap with (f := f) in Hmy.
    rewrite Hm in Hmy.
    rewrite member_single_iff in Hmy.
    now apply Hi.
  -

    rewrite member_single_iff in Hmy; subst.
    apply inj_member_fmap with (f := f); auto.
    rewrite Hm.
    apply member_single.
Qed.



Lemma inv_member_fmap{X Y: Type}: forall (S: Setof X) (f: X -> Y) (y: Y),
    member (fmap S f) y -> exists x, y = f x /\ member S x.
Proof.
  intros S f y Hm.
  destruct Hm as (u & Hu & Heq); subst.
  now exists u.
Qed.




Record BIJECTION (X Y: Type): Type :=
  {
    to: X -> Y;
    from: Y -> X;
    to_from: forall x, to (from x) = x;
    from_to: forall y, from (to y) = y;
  }.



Arguments to {_ _} _ _.
Arguments from {_ _} _ _.
Arguments to_from {_ _} _ _.
Arguments from_to {_ _} _ _.


Lemma fmap_id{X: Type}: forall (S: Setof X),
    fmap S id = S.
Proof.
  intros S.
  apply set_equal; split; intro Hm.
  apply inv_member_fmap in Hm.
  -
    now destruct Hm as (y & Heq & Hm); subst.
  -
    now exists x.
Qed.



Lemma fmap_comp{X Y Z: Type}: forall (f: Y -> Z) (g: X -> Y) (S: Setof X),
    fmap S (f ° g) = fmap (fmap S g) f.
Proof.
  intros f g S.
  apply set_equal; intros z ; split; intro Hm.
  -
    apply inv_member_fmap in Hm.
    destruct Hm as (x & Heq & Hm).
    rewrite Heq.
    unfold comp.
    now do 2 apply member_fmap.
  -
    apply inv_member_fmap in Hm.
    destruct Hm as (y & Heq & Hm); subst.
    apply inv_member_fmap in Hm.
    destruct Hm as (x & Heq & Hm); subst.
    now exists x.
Qed.

Lemma to_surjective{X Y: Type}: forall (b: BIJECTION X Y),
    is_surjective (to b).
Proof.
  intros b y.
  destruct b.
  cbn in *.
  now exists (from0 y).
Qed.



Lemma from_surjective{X Y: Type}: forall (b: BIJECTION X Y),
    is_surjective (from b).
Proof.
  intros b y.
  destruct b.
  cbn in *.
  now exists (to0 y).
Qed.

Lemma to_injective{X Y: Type}: forall (b: BIJECTION X Y),
    is_injective (to b).
Proof.
  intros b x x' Heq.
  destruct (from_surjective b x ).
  destruct (from_surjective b x' ).
  subst.
  f_equal.
  now do 2 rewrite (to_from b) in Heq.
Qed.



Lemma from_injective{X Y: Type}: forall (b: BIJECTION X Y),
    is_injective (from b).
Proof.
  intros b y y' Heq.
  destruct (to_surjective b y ).
  destruct (to_surjective b y' ).
  subst.
  f_equal.
  now do 2 rewrite (from_to b) in Heq.
Qed.


Definition BIJECTION_refl (X: Type): BIJECTION X X.
  unshelve econstructor.
  -
    exact id.
  -
    exact id.
  -
    now intro x.
  -
    now intro x.
Defined.

Definition BIJECTION_sym (X Y: Type) (b: BIJECTION X Y): BIJECTION Y X.
  unshelve econstructor.
  -
    exact (from b).
  -
    exact (to b).
  -
    intro x.
    now rewrite from_to.
  -
    intro y.
    now rewrite to_from.
Defined.

Definition BIJECTION_trans (X Y Z: Type)
  (b1: BIJECTION X Y) (b2: BIJECTION Y Z): BIJECTION X Z.
  unshelve econstructor.
  -
    exact ((to b2) ° (to b1)).
  -
    exact ((from b1) ° (from b2)).
  -
    intros x; unfold comp ; cbn.
    now do 2 rewrite to_from.
  -
    intros y; unfold comp ; cbn.
    now do 2 rewrite from_to.
Defined.

Lemma bijection_from_to{X Y: Type}: forall (b: BIJECTION X Y),
    (from b) ° (to b) = id.
Proof.
  intro b.
  extensionality x.
  apply from_to.
Qed.


Lemma bijection_to_from{X Y: Type}: forall (b: BIJECTION X Y),
    (to b) ° (from b) = id.
Proof.
  intro b.
  extensionality x.
  apply to_from.
Qed.
