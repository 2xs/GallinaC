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

From Stdlib Require Import FunctionalExtensionality PropExtensionality
 IndefiniteDescription Classical List Lia.
From GallinaC.Corec Require Export Completion Finite.
Import ListNotations.


Definition EXP (D C: Type) : Type := D -> C.

Definition EXP_Poset (D: Type) (C: Poset):  Poset :=
  {|
    poset_carrier := EXP D C;
    poset_le := fun f f' => forall d, @poset_le C (f d) (f' d);
    poset_refl := ltac:(cbn;intros; apply poset_refl);
    poset_trans := ltac:(cbn;intros; eapply poset_trans; eauto);
    poset_antisym :=
      ltac:(cbn;intros;extensionality w ;apply poset_antisym; auto)
  |}.

Definition EXP_PPO (D: Type) (C: PPO):  PPO :=
{|
  ppo_poset := EXP_Poset D C;
  ppo_bot := fun _ => ppo_bot;
  ppo_bot_least := ltac:(cbn;intros; apply ppo_bot_least);
|}.


Definition proj{D : Type} {C : PPO} (S : Setof (EXP_PPO D C))(d : D) :=
 (fun c => exists f, member S f /\ c = f d).

(* this lemma and the following = Lemma 5 in paper *)
Lemma directed_proj{D: Type} {C: PPO} :
  forall  (S: Setof (EXP_PPO D C)) (d:D),
    is_directed S -> is_directed (proj S d).
Proof.
intros S d (Hne & Hd).
split.
-
  apply not_empty_member.
  apply not_empty_member in Hne.
  destruct Hne as (f & Hm).
  now exists (f d), f.
-
  intros x y Hm1 Hm2.
  destruct Hm1 as (f1 & Hm1 & Heq1).
  destruct Hm2 as (f2 & Hm2 & Heq2).
  destruct (Hd _ _ Hm1 Hm2) as (f & Hm & Hle1 & Hle2).
  subst.
  exists (f d); split; auto.
  now exists f.
Qed.


Lemma lub_proj{D : Type}{C : CPO}: forall S,
is_directed S ->
is_lub S
  (fun d : D =>
   cpo_lub (c:= C) (proj S d)).
Proof.
intros  S Hd.
split.
-
  intros f Hm d.
  cbn in *.
  specialize (cpo_lub_prop  _ (directed_proj S d Hd)) as (Hu & _).
  apply (Hu (f d)).
  now  exists f.
-
  intros g Hu d.
  specialize (cpo_lub_prop  _ (directed_proj S d Hd)) as (_ &Hmm).
  apply Hmm; clear Hmm.
  intros x Hmx.
  destruct Hmx as (f & Hf & Heq).
  subst.
  specialize (Hu _ Hf).
  cbn in Hu.
  apply Hu.
Qed.


Definition EXP_CPO (D: Type) (C: CPO):  CPO :=
{|
  cpo_ppo := EXP_PPO D C;
  cpo_lub := fun  S =>
  (fun d =>  cpo_lub (proj S d));
  cpo_lub_prop := lub_proj
|}.


Definition support{A:Type}{B:PPO}(f: A -> B) : Setof A :=
  fun a => f a <> ppo_bot.

Lemma finite_support_with_compact_values_is_compact{A:Type}{B:CPO}:
forall (f : A -> B), is_finite (support f) ->
(forall a, is_compact  (f a))  ->
is_compact (P := EXP_CPO A B) f.
Proof.
intros f Hf Hac.
rewrite is_compact_alt.
intros F Hd Hcl Hle.
assert(Hfunc:
  forall (a:A), exists (b : B), member (proj F a) b /\ f a <= b).
{
  intros a.
  assert (Hds : is_directed (proj F a))
    by now apply directed_proj.
  now specialize (Hac a _ Hds (Hle a)).
}
apply functional_choice in Hfunc.
destruct Hfunc as (g & Hag).
assert (Hma: forall a, member (support f) a -> member (proj F a)
(g a) /\
f a <= g a) by (intros a _ ; now destruct (Hag a)).
clear Hag.
apply is_finite_iff in Hf.
destruct Hf as (l & _ & Himp).
assert (Hma' : forall a : A,
   In a l ->
     member (proj F a) (g a) /\ f a <= g a)
 by (intros a Hin; apply Hma;now rewrite Himp ).
clear Hma Hle.
assert (Hma : forall a, In a l -> exists h, member F h /\ f a <= h a).
{
  intros a Hin.
  destruct (Hma' _ Hin) as (Hm & Hle).
  destruct Hm as (h & Hmh & Heq).
  rewrite Heq in Hle.
  now exists h.
}
clear Hma'.
assert (Hma' : forall (a: {a: A | In a l}), exists h,
  member F h /\ f (proj1_sig a) <= h (proj1_sig a)) by
  (intros (a & Hin); now apply Hma).
clear Hma.
apply functional_choice in Hma'.
assert (Hnsig : exists ff: A -> EXP_CPO A B,
  forall a, In a l -> member F (ff a) /\ f a <= ff a a).
{
  destruct Hma' as (fsig & Hasig).
  exists (fun x =>
    match (oracle (In x l)) with
     | left Hl => fsig (exist _ x Hl)
     | right _ => ppo_bot
    end
  ).
 intros a Hin.
 destruct (oracle (In a l)); [| now contradict n].
 apply Hasig.
}
clear Hma'.
destruct Hnsig as (ff & Haff).
assert (Haff1 : forall a : A,
In a l ->
member F (ff a)) by (intros a Hin;  now destruct (Haff _ Hin)).
assert (Haff2 : forall a : A,
In a l -> f a <= ff a a) by (intros a Hin;  now destruct (Haff _ Hin)).
clear Haff.
specialize (list_directed_has_upper_alt _ Hd (map ff l)) as Hex.
assert (HH : forall x : EXP_CPO A B,
In x (map ff l) -> member F x).
{
  intros x Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as (a & Heq & Hin).
  rewrite <- Heq.
  now apply Haff1.
}
specialize  (Hex HH).
destruct Hex as (q & Hmq & Ha).
clear HH.
exists (fun a =>
    match (oracle (In a l)) with
     | left Hl => ff a a
     | right _ => ppo_bot
    end
  ).
 split.
 -
   apply Hcl with (x := q); auto.
   intro a.
   destruct (oracle (In a l)); [| apply ppo_bot_least].
   assert (Hin : In (ff a) (map ff l)) by
   (rewrite  in_map_iff; now exists a).
   specialize (Ha _ Hin).
   cbn in Ha.
   apply Ha.
 -
   intro a.
   destruct (oracle (In a l)).
   +
    now apply Haff2.
   +
    assert (Hnm : ~member (support f) a)  by (now rewrite Himp).
    unfold member, support in Hnm.
    unfold not in Hnm.
    apply NNPP in Hnm.
    rewrite Hnm.
    apply poset_refl.
Qed.


Definition cp_func{D : Type}{C : CPO}
(S : D -> Setof C)   (Hall : forall j : D, is_directed (S j))
  (f1 f2 : EXP D C)
  (Hmf1 : forall d : D, S d (f1 d))
  (Hmf2 : forall d : D, S d (f2 d)) : forall (d:D), C.
  intro d.
  specialize (Hmf1 d).
  specialize (Hmf2 d).
  specialize (Hall d ) as (_ & Hall').
  specialize (Hall' _ _ Hmf1 Hmf2).
  remember (constructive_indefinite_description _ Hall') as Hall''.
  destruct Hall'' as (z & Hmz & Hle1 & Hle2).
  exact z.
Defined.


Lemma  cp_func_prop_1{D : Type}{C : CPO} :
 forall  (S : D -> Setof C)
  (Hall : forall j : D, is_directed (S j))
  (f1 f2 : EXP D C)
  (Hmf1 : forall d : D, S d (f1 d))
  (Hmf2 : forall d : D, S d (f2 d)) (d : D),
   S d
     (cp_func S Hall f1 f2 Hmf1
        Hmf2 d).
intros.
unfold cp_func.
destruct (Hall d).
remember (constructive_indefinite_description _
          (e (f1 d) (f2 d) (Hmf1 d) (Hmf2 d))) as ci.
clear Heqci.
now destruct ci as (x & Hmx & Hle1 & Hle2).
Qed.

Lemma  cp_func_prop_2{D : Type}{C : CPO} :
 forall  (S : D -> Setof C)
  (Hall : forall j : D, is_directed (S j))
  (f1 f2 : EXP D C)
  (Hmf1 : forall d : D, S d (f1 d))
  (Hmf2 : forall d : D, S d (f2 d)) (d : D),
 f1 d <=
 cp_func S Hall f1 f2 Hmf1 Hmf2 d.
Proof.
intros.
unfold cp_func.
destruct (Hall d).
remember (constructive_indefinite_description _
          (e (f1 d) (f2 d) (Hmf1 d) (Hmf2 d))) as ci.
now destruct ci as (x & Hmx & Hle1 & Hle2).
Qed.

Lemma  cp_func_prop_3{D : Type}{C : CPO} :
 forall  (S : D -> Setof C)
  (Hall : forall j : D, is_directed (S j))
  (f1 f2 : EXP D C)
  (Hmf1 : forall d : D, S d (f1 d))
  (Hmf2 : forall d : D, S d (f2 d)) (d : D),
 f2 d <=
 cp_func S Hall f1 f2 Hmf1 Hmf2 d.
Proof.
intros.
unfold cp_func.
destruct (Hall  d); cbn.
remember ( constructive_indefinite_description _
       (e (f1 d) (f2 d) (Hmf1 d) (Hmf2 d))) as ci.
now  destruct ci as (x & Hmx & Hle1 & Hle2).
Qed.



Definition choose{C : PPO} (S : Setof C): is_directed S ->  C.
intro Hd.
destruct Hd as (Hne & _).
apply not_empty_member in Hne.
remember (constructive_indefinite_description _  Hne) as x.
clear Heqx.
destruct x as (x & Hm).
exact x.
Defined.

Lemma choose_chooses{C : PPO} : forall (S : Setof C)Hd, member S  (choose  S Hd).
Proof.
intros S (Hne & Hx).
unfold choose.
remember (constructive_indefinite_description
         (member S)
         (match not_empty_member S with
          | conj H _ => H
          end Hne)) as ci.
now destruct ci as (x & Hm).
Qed.

Lemma cartesian_product_is_directed{D : Type}{C : CPO}
  (S : D -> Setof C)
  (Hall: forall j, is_directed (S j)):
  is_directed (P := EXP_CPO D C)
    (fun f =>  forall  d,  member (S d) (f d)).
Proof.
cbn.
split.
-
  apply not_empty_member.
  exists (fun d => choose (S d) (Hall d)).
  unfold member; cbn.
  intro d.
  apply choose_chooses.
-
  cbn.
  intros f1 f2 Hmf1 Hmf2.
  unfold member in *.
  exists (cp_func S Hall f1 f2 Hmf1 Hmf2).
  repeat split.
  *
    apply  cp_func_prop_1.
  *
    apply cp_func_prop_2.
  *
    apply cp_func_prop_3.
Qed.


Lemma lub_of_cartesian_product{D : Type}{C : CPO}
  (S : D -> Setof C)
  (Hall: forall j, is_directed (S j)):
    cpo_lub  (c := EXP_CPO D C)
     (fun f =>  forall  d,  member (S d) (f d))=
    fun d => cpo_lub (S d).
Proof.
extensionality d.
cbn.
set (F :=  (fun f : EXP D C =>
        forall d : D,
          member (S d) (f d))).
specialize (cpo_lub_prop _  (directed_proj F d (cartesian_product_is_directed S Hall)) ) as Hl.
remember (cpo_lub (proj F d)) as c.
specialize (cpo_lub_prop _  (Hall d) ) as Hl'.
remember  (cpo_lub (S d)) as c'.
clear Heqc Heqc'.
replace  (proj F d) with
            (S d) in *; [eapply is_lub_unique; eauto|].
apply set_equal.
intro x; split; intro Hm.
-
  exists (fun j =>
              match (oracle (j = d)) with
                left  => x
               | right  => choose (S j) (Hall j)
              end).
  unfold member; cbn.
  split.
  +
    intros d'.
    remember  (oracle (d' = d) ) as o.
    destruct o; try (now subst).
    apply choose_chooses.
  +
    remember (oracle (d = d)) as o.
    destruct o; auto.
    clear Heqo.
    now contradict n.
-
  destruct Hm as (f & Hf & Heq); subst.
  apply Hf.
Qed.


Lemma compacts_have_compact_values{D: Type}:
forall {A:ALGEBRAIC} f,
    is_compact (P:= (EXP_CPO D A)) f ->
      forall d, is_compact (f d).
Proof.
intros  A f Hc d.
rewrite is_compact_alt.
intros Sd Hd Hcl  Hle.
remember (fun d => (compacts_le (f d))) as F.
assert (Hall : forall d, is_directed (F d)) by
  (intros;   subst; apply algebraic_dir).
specialize (lub_of_cartesian_product  _ Hall) as Hlem.
subst.
specialize (Hc  _ (cartesian_product_is_directed
              (fun d : D =>
               compacts_le (f d))
              Hall) ).
cbn [compacts_le] in Hc.
rewrite Hlem in Hc.
assert (Hlef :
 f <= (fun d : D => cpo_lub (compacts_le (f d)))).
{
  intro d'.
  rewrite (algebraic_lub (f d')) at 1.
  apply poset_refl.
}
specialize (Hc Hlef).
clear Hlef.
destruct Hc as (f'& Hm & Hlef).
unfold member in Hm; cbn in Hm.
exists (f' d); split; auto.
specialize (Hm d) as Hmd.
unfold compacts_le in Hmd.
destruct Hmd as (Hc' & Hle').
assert (Hlef' : f' d <= cpo_lub Sd)
  by (eapply poset_trans; eauto).
unfold is_compact in Hc'.
specialize (Hc' _ Hd Hlef').
destruct Hc' as (c & Hmc & Hlec).
now apply  (Hcl _ Hmc).
Qed.

Definition is_restriction{A:Type}{B: PPO} (f g : A -> B) : Prop :=
subset (support f) (support g) /\
    forall a, member (support f) a -> f a = g a.


Definition is_mixture{A:Type}{B: PPO} (f g h : A -> B):= forall x,
h x = f x \/ h x = g x.



Lemma mixture_finite_is_finite {A:Type}{B: PPO} (f g h : A -> B):
is_mixture f g h ->  is_finite (support f) -> is_finite (support g) ->
is_finite (support h).
intros Hm Hff Hfg.
destruct Hff as (lf & Hf).
destruct Hfg as (lg & Hg).
exists (lf ++ lg).
intros x Hmx.
apply in_or_app.
destruct (Hm x) as [Hl | Hr].
-
 left.
 apply Hf.
 unfold member, support in *.
 now rewrite <- Hl.
-
 right.
 apply Hg.
 unfold member, support in *.
 now rewrite <- Hr.
Qed.


Definition finite_restrictions{A:Type}{B: PPO}(g: A -> B):Setof(EXP A B):=
fun f => is_restriction f g /\ is_finite (support f).

Lemma finite_restriction_directed{A:Type}{B: PPO}(g: A -> B) :
  is_directed (P := EXP_Poset A B)(finite_restrictions g).
Proof.
split.
-
 apply not_empty_member.
 exists (fun _ => ppo_bot).
 repeat split.
+
  now intro x.
+
  intros x Hm.
  now contradict Hm.
+
  exists [].
  intros x Hm.
  now contradict Hm.
-
  intros f' g' Hmf' Hmg'.
  exists (fun a =>
    match (oracle (f' a = ppo_bot)), (oracle (g' a = ppo_bot)) with
    |right _, right _  => f' a
    |left _, right _ => g' a
    |right _, left _ => f' a
    |left _, left _ => ppo_bot
    end).
  repeat split.
  +
   intros x Hmx Heq.
   apply Hmx; clear Hmx.
   destruct (oracle (f' x = ppo_bot));
     destruct (oracle (g' x = ppo_bot)); auto.
   *
    exfalso; apply n.
    destruct Hmg' as ((Hs & Heq') & _).
    rewrite Heq'; auto.
   *
   exfalso; apply n.
   destruct Hmf' as ((Hs & Heq') & _).
   rewrite Heq'; auto.
   *
   exfalso; apply n.
   destruct Hmf' as ((Hs & Heq') & _).
   rewrite Heq'; auto.
 +
  intros x Hmx.
  unfold member, support in Hmx.
  destruct (oracle (f' x = ppo_bot));
     destruct (oracle (g' x = ppo_bot)).
  *
   now contradict Hmx.
  *
  destruct Hmg' as ((Hs & Heq') & _).
  rewrite Heq'; auto.
  *
  destruct Hmf' as ((Hs & Heq') & _).
  rewrite Heq'; auto.
  *
  destruct Hmf' as ((Hs & Heq') & _).
  rewrite Heq'; auto.
 +
   apply mixture_finite_is_finite with (f := f') (g := g').
   *
   intros x.
   destruct (oracle (f' x = ppo_bot));
      destruct (oracle (g' x = ppo_bot)); auto.
   *
    now destruct Hmf'.
   *
    now destruct Hmg'.
  +
    intros x.
    destruct (oracle (f' x = ppo_bot));
      destruct (oracle (g' x = ppo_bot)); try (rewrite e) ;
      try (rewrite e0); try (apply poset_refl).
    apply ppo_bot_least.
+
  intros x.
  destruct (oracle (f' x = ppo_bot));
   destruct (oracle (g' x = ppo_bot)); try (rewrite e) ;
   try (rewrite e0); try (apply poset_refl); try (apply ppo_bot_least).
  destruct Hmg' as ((_ & Heq') & _).
  destruct Hmf' as ((_ & Heq'') & _).
  rewrite Heq',Heq''; auto.
  apply poset_refl.
Qed.


Lemma single_support_finite_restriction{A:Type}{B: PPO}:
forall (f: A -> B) a,
member(finite_restrictions f)
(fun x : A => if oracle (x = a) then f a else ppo_bot).
Proof.
intros f a.
repeat split.
 -
   intros x Hmx.
   unfold member, support in Hmx.
   destruct (oracle (x = a)); subst; auto.
   now contradict Hmx.
-
  intros x Hmx.
  unfold member, support in Hmx.
  destruct (oracle (x = a)); subst; auto.
  now contradict Hmx.
-
 exists [a].
 intros x Hmx.
 unfold member, support in Hmx.
 destruct (oracle (x = a)); subst; try constructor; auto.
 now contradict Hmx.
Qed.


Lemma function_is_lub_of_finite_restrictions{A:Type}{B: PPO}:
forall (f: A -> B),
 is_lub (P := EXP_Poset A B)(finite_restrictions f) f.
Proof.
intros f.
split.
-
  intros g Hmg a.
  destruct Hmg as ((Hq & Heq') & _).
  destruct (oracle (g a = ppo_bot)); [rewrite e; apply ppo_bot_least |].
  rewrite Heq'; auto.
  apply poset_refl.
-
 intros g Hug a.
 unfold is_upper in Hug.
 specialize (Hug _ (single_support_finite_restriction f a) a).
 cbn in Hug.
 destruct (oracle (a = a)); auto.
 now contradict n.
 Qed.


Lemma function_le_lub_of_finite_restrictions{A:Type}{B: CPO}:
forall (f: A -> B),
poset_le (p := EXP_Poset A B )f
(cpo_lub (c := EXP_CPO A B)(finite_restrictions f)).
Proof.
intro f.
specialize (function_is_lub_of_finite_restrictions f) as Hlf.
specialize (finite_restriction_directed f) as Hdf.
specialize (@is_lub_cpo_lub_eq  (EXP_CPO A B) _ _ Hlf Hdf) as Hf.
replace (finite_restriction_directed f) with Hdf by
 (now apply proof_irrelevance).
rewrite <- Hf.
apply poset_refl.
Qed.



Lemma compacts_have_finite_support{D: Type} {A:ALGEBRAIC} : forall f,
     is_compact (P:= (EXP_CPO D A)) f -> is_finite (support f).
Proof.
intros f Hc.
specialize (function_le_lub_of_finite_restrictions f) as Hle.
specialize (finite_restriction_directed f) as Hdf.
specialize (Hc _ Hdf Hle); clear Hle.
destruct Hc as (h & (Hr & Hf) & Hle).
destruct Hf as (l & Hin).
exists l.
intros x Hm.
apply Hin.
cbn in Hle.
intro Heq; apply Hm.
specialize (Hle x).
rewrite Heq in Hle.
now apply  le_bot_eq.
Qed.

Lemma compacts_are_functions_with_finite_support_and_compact_values
{A: Type}{B:ALGEBRAIC} : forall f,
    is_compact (P:= (EXP_CPO A B)) f <->
    (is_finite (support f) /\  forall a, is_compact (f a)).
Proof.
split.
-
  intro Hc.
  split.
  +
   now apply compacts_have_finite_support.
  +
   now apply compacts_have_compact_values.
-
 intros (Hf & Ha).
 now apply finite_support_with_compact_values_is_compact.
Qed.


Lemma my_algebraic_dir{A:Type}{B:ALGEBRAIC}:
forall (f : A -> B), is_directed (compacts_le (P := EXP_CPO A B)f).
Proof.
intros f.
split.
-
 apply not_empty_member.
 exists (fun _ => ppo_bot).
 split; [| intro x; apply ppo_bot_least].
 rewrite compacts_are_functions_with_finite_support_and_compact_values.
 split.
 + exists [].
   intros x Hm.
   now contradict Hm.
 +
  intros _.
  apply bot_is_compact.
-
  intros u v (Hcu & Hleu) (Hcv & Hlev).
  rewrite compacts_are_functions_with_finite_support_and_compact_values
    in Hcu, Hcv.
  destruct Hcu as (Hfu & Hau).
  destruct Hcv as (Hfv & Hav).
  cbn in Hleu, Hlev.
  assert (Hkey : forall d,
    exists w, u d <= w /\ w <= f d/\ v d <= w  /\ is_compact w
     /\ (~member (support u) d /\ ~member (support v) d -> w = ppo_bot)).
  {
     intro a.
     specialize (Hau a).
     specialize (Hav a).
     specialize (Hleu a).
     specialize (Hlev a).
     specialize (algebraic_lub (f a)) as Heq.
     rewrite Heq in Hleu,Hlev.
     (*specialize (compacts_le_directed (f a)) as Hd.*)
     assert (Hd : is_directed (compacts_le (f a))) by
        apply algebraic_dir.
     specialize (Hau _ Hd Hleu).
     specialize (Hav _ Hd Hlev).
     clear Hleu Hlev.
     destruct Hau as (wu & Hcwu & Hleu).
     destruct Hav as (wv & Hcwv & Hlev).
     destruct Hd as (_ & Hd).
     specialize (Hd _ _ Hcwu Hcwv).
     destruct Hd as (z & (Hcz & Hmz) & Hleuz & Hlevz).
     destruct (oracle (member (support u) a));
       destruct (oracle (member (support v) a)).
    -
     exists z; repeat split; auto.
     +
     eapply poset_trans; eauto.
     +
     eapply poset_trans; eauto.
     +
      intros (Hnmu & Hnmv).
      now contradict Hnmu.
   -
    exists z; repeat split; auto.
    +
    eapply poset_trans; eauto.
    +
    eapply poset_trans; eauto.
    +
    intros (Hnmu & Hnmv).
    now contradict Hnmu.
  -
    exists z; repeat split; auto.
    +
    eapply poset_trans; eauto.
    +
    eapply poset_trans; eauto.
    +
    intros (Hnmu & Hnmv).
    now contradict Hnmv.
 -
  exists ppo_bot; repeat split; auto.
  +
   apply NNPP in n.
   rewrite n.
   apply poset_refl.
  +
    apply ppo_bot_least.
  +
  apply NNPP in n0.
  rewrite n0.
  apply poset_refl.
  +
   apply bot_is_compact.
  }
  apply functional_choice in Hkey.
  destruct Hkey as (g & Hag).
  exists g; repeat split.
  +
   rewrite compacts_are_functions_with_finite_support_and_compact_values.
   split.
   *
     destruct Hfu as (lu & Hlu).
     destruct Hfv as (lv & Hlv).
     exists (lu ++ lv).
     intros x Hmx.
     destruct (Hag x) as (_ &_ & _ & _ & Himp).
     unfold member, support in *.
     assert (u x <> ppo_bot \/ v x <> ppo_bot); try tauto.
     clear Himp.
     apply in_or_app.
     destruct H as [Hl | Hr];
      [left; now apply Hlu| right; now apply Hlv].
   *
      intro a.
      now destruct (Hag a) as (_& _ & _ & Hc & _).
  +
    intros a.
    now destruct (Hag a) as (_& Hle & _ & _ & _).
  +
    intros a.
    now destruct (Hag a) as (Hle & _ & _ & _ & _).
  +
    intros a.
    now destruct (Hag a) as (_ & _ & Hle & _ & _).
Qed.


Lemma my_algebraic_lub{A:Type}{B:ALGEBRAIC}:
forall (f : A -> B),
f = cpo_lub (compacts_le (P:= EXP_CPO A B)f).
Proof.
intro f.
remember  (my_algebraic_dir f) as Hd.
extensionality a.
rewrite (algebraic_lub  (f a)).
apply poset_antisym.
-
 apply forallex_lelub;  auto.
 +
   apply algebraic_dir.
 + now apply directed_proj.
 +

 intros b (Hcb & Hleb).
 exists b; split; try apply poset_refl.
 exists
  (fun x =>
    match (oracle (x = a) ) with
    left _ => b
    |right _ => ppo_bot
    end).
 repeat split.
  *
  rewrite compacts_are_functions_with_finite_support_and_compact_values.
  split.
  --
     exists[a].
     intros x Hmx.
     unfold member, support in Hmx.
     destruct (oracle (x =a)); subst; try constructor; auto.
     now contradict Hmx.
  --
   intro x.
   destruct (oracle (x =a)); subst; auto.
   apply bot_is_compact.
  *
   intro x.
   destruct (oracle (x =a)); subst; auto.
   apply ppo_bot_least.
 *
  destruct (oracle (a  =a)); subst; auto.
  now contradict n.
 -
  apply forallex_lelub.

  + now apply directed_proj.
  + apply algebraic_dir.
  + intros b (g & (Hcg & Hleg) & Heqb).
  exists b.
  rewrite compacts_are_functions_with_finite_support_and_compact_values
   in Hcg.
  destruct Hcg as (Hf & Hac).
  repeat split; try apply poset_refl.
  *
    rewrite Heqb.
    apply Hac.
  *
   rewrite Heqb.
   apply (Hleg a).
Qed.

Definition EXP_ALGEBRAIC (A: Type) (B: ALGEBRAIC): ALGEBRAIC :=
{|
  algebraic_cpo := EXP_CPO A B;
  algebraic_dir := my_algebraic_dir;
  algebraic_lub := my_algebraic_lub
|}.



Record BELOW (N:nat) : Type :=
{
nval :> nat ;
is_below : (nval < N)%nat
}.




Lemma BELOW_equal{N: nat}:
forall (i j : nat)(Hi : i < N)(Hj : j < N),
i = j ->
{| nval := i; is_below := Hi|} =   {| nval := j; is_below := Hj|}.
Proof.
intros.
subst.
f_equal.
apply proof_irrelevance.
Qed.

Program Definition bshift{T: Type}(N :nat) (e: EXP (BELOW (S (S N))) T) :
EXP (BELOW (S N)) T :=
fun (x: BELOW (S N))  => e {| nval :=  _  ; is_below := _ |} .

Next Obligation.
intros.
destruct x.
exact (S nval0).
Defined.

Next Obligation.
intros.
unfold bshift_obligation_1.
destruct x.
lia.
Qed.


Program Fixpoint bEXP2list{T:Type}(N: nat) (e :EXP (BELOW (S N)) T) :
list T :=
match N as N' return (N' = N -> list T) with
|0 => fun Heq => [e {| nval := 0; is_below :=
 PeanoNat.Nat.lt_0_succ _ |}]
| S M =>  fun Heq => (e  {| nval := 0; is_below :=
 PeanoNat.Nat.lt_0_succ _|}) ::
    (bEXP2list M  (bshift M  e ))
end eq_refl.

Next Obligation.
intros.
f_equal.
exact Heq.
Defined.


Lemma blength_EXP2list{T:Type}: forall N (e: EXP (BELOW (S N)) T),
 length (bEXP2list N e) = S N.
Proof.
induction N; intro e; auto.
cbn.
f_equal.
now rewrite IHN.
Qed.

Lemma bnth_EXP2list{T:Type}(d:T):
forall N (e: EXP (BELOW (S N)) T) (i: nat) (Hi : (i <  S N)%nat),
  nth i (bEXP2list N e) d = e {| nval := i; is_below := Hi |}.
Proof.
induction N; intros e i Hi.
-
 destruct i; [cbn;f_equal|lia].
 f_equal.
 apply proof_irrelevance.
-
  destruct i; cbn; [repeat f_equal;apply proof_irrelevance |].
  remember (bshift N
  (fun
     x :
      BELOW
        (S (S N))
   => e x)) as e'.

  rewrite  IHN with (Hi := le_S_n _ _ Hi).
  rewrite Heqe'.
  unfold bshift.
  cbn.
  do 2 f_equal.
  apply proof_irrelevance.
Qed.


Lemma BELOW_finite_type : forall N, is_finite_type (BELOW N).
Proof.
destruct N as [ | M ].
-
  exists [].
  intros x; destruct x; lia.
-
   exists (bEXP2list (T := (BELOW (S M) )) M id).
   intros (n, Hnb).
   specialize (nth_In (A := BELOW (S M)) (n := n) (bEXP2list M id)
   {| nval := n ; is_below := Hnb |}) as Hni.
   rewrite blength_EXP2list  in Hni.
   erewrite bnth_EXP2list with (Hi := Hnb) in Hni.
   now apply Hni.
Qed.



Definition EXP_BELOW_ALGEBRAIC (N:nat) (A: ALGEBRAIC):  ALGEBRAIC :=
  EXP_ALGEBRAIC (BELOW N) A.



Program Definition exp_below_completion (N:nat) (P: PPO) (m : COMPLETION P) :
 COMPLETION  (EXP_PPO (BELOW N) P) :=
{|
 alg := EXP_BELOW_ALGEBRAIC N m;
 inject := fun f x => inject (f x);
 rev_inj := fun a  d =>
  match (oracle (is_compact a)) with
    left _ => rev_inj (a d)
    |right _ => ppo_bot
  end
|}.


Next Obligation.
cbn in *.
intros.
extensionality x.
apply inject_bot.
Qed.

Next Obligation.
cbn.
intros.
split ; intros Hall d.
-
 apply inject_bimono.
 apply Hall.
-
 rewrite inject_bimono.
 apply Hall.
Qed.


Next Obligation.
cbn.
intros N  P m p.
rewrite compacts_are_functions_with_finite_support_and_compact_values.
split.
-
  apply finite_type_all_sets_finite.
  apply BELOW_finite_type.
-
  intro a.
  apply inject_compact.
Qed.

Next Obligation.
cbn.
intros N P m fc  p Hc.
destruct (oracle (is_compact  (P:= EXP_CPO (BELOW N) _) fc));
[| exfalso; now apply n].
split ; intro F.
-
 extensionality d.
 rewrite <- F.
 rewrite <- rev_inj_iff; auto.
 rewrite compacts_are_functions_with_finite_support_and_compact_values in Hc.
 now destruct Hc.
-
 extensionality d.
 rewrite rev_inj_iff.
 now rewrite <- F.
 rewrite compacts_are_functions_with_finite_support_and_compact_values in Hc.
 now destruct Hc.
Qed.
