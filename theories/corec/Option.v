From Coq Require Import Classical IndefiniteDescription.
From Corec Require Export Completion.

Inductive option_le{A:Type} : option A  -> option A -> Prop :=
| None_le : forall o, option_le None o
| Some_le : forall o, option_le (Some o) (Some o).


Lemma option_le_refl{A:Type} : forall (o: option A), option_le o o.
Proof.
intro o;destruct o; constructor.
Qed.

Lemma option_le_trans{A:Type} : forall (o o' o'': option A),
    option_le o o' -> option_le o' o'' -> option_le o o''.
Proof.
intros x y z Hle1 Hle2; inversion Hle1; subst; inversion Hle2; subst;  constructor.
Qed.

Lemma option_le_antisym{A:Type} :  forall (o o': option A),
option_le o o' -> option_le o' o -> o = o'.
Proof.
intros x y Hle1 Hle2; inversion Hle1; subst; inversion Hle2; subst; try constructor.
Qed.


Definition option_Poset (A:Type) : Poset :=
{|
  poset_carrier := option A;
  poset_le := option_le;
  poset_refl := option_le_refl;
  poset_trans := option_le_trans;
  poset_antisym := option_le_antisym
|}.


Definition option_PPO (A:Type) : PPO :=
{|
  ppo_poset := option_Poset A;
  ppo_bot := None;
  ppo_bot_least := None_le
|}.
    

Lemma option_directed{A:Type} : forall (T:Setof (option A)),
 is_directed (P := option_Poset A) T <-> (exists a, T = single a) \/
 (exists a, T = (fun x => x = None \/ x = a)).
Proof.
intros T; split; intro Hs.
-
  destruct Hs as (Hne & Hd).
  destruct (oracle (exists a, T = single a)); [now left | right].
  
  specialize (not_ex_all_not _ _ n) as Ha.
  apply not_empty_not_single_2dif_alt in Hne; auto.
  clear n Ha.
  destruct Hne as (x & y & Hmx & Hmy & Hne).
  cbn in x,y.
  destruct (Hd _ _ Hmx Hmy) as (z & Hmz & Hlexz & Hleyz).
  inversion Hlexz; inversion Hleyz ; subst.
  + exfalso; now apply Hne.
  +
    exists (Some o0).
    apply set_equal; intro u; split; intro Hmu.
    *   
      destruct u; unfold member; auto.
      destruct (Hd _ _ Hmz Hmu) as (w & Hmw & Hlezw & Hleuw).
      inversion Hleuw; inversion Hlezw ; subst.
      now right.
    *
     destruct Hmu; subst; auto.
  +  
    exists (Some o).
    apply set_equal; intro u; split; intro Hmu.
    *   
      destruct u; unfold member; auto.
      destruct (Hd _ _ Hmz Hmu) as (w & Hmw & Hlezw & Hleuw).
      inversion Hleuw; inversion Hlezw ; subst.
      now right.
    *
     destruct Hmu; subst; auto.
  +   
    exfalso; now apply Hne.
-
  destruct Hs as [(a & Hs)  | (a & Hs)]. 
  +
   subst.
   apply @single_is_directed.
  +
    rewrite Hs.
    apply  @ordered_pair_is_directed.
    apply None_le.
 Qed.     
   

Lemma option_lub{A:Type} : forall (T: Setof (option A)),
is_directed (P :=(option_Poset A)) T -> 
 {x : option A | is_lub (P :=(option_Poset A)) T x}.
Proof.
intros T Hd.
rewrite  option_directed in Hd; subst.
apply constructive_indefinite_description.
destruct Hd as [(a & Hd) | (a & Hd)].
- 
  exists a.
  subst.
  apply @is_lub_single.
-
 exists a.
 subst.
 apply @ordered_pair_has_lub, None_le.  
Qed.

(*
fun S => match (oracle (is_directed S))
    with
      left Hd =>  proj1_sig (is_directed_lub  _ S Hd)
    | right _ => sum_bot (fun x : J => T x)
    end;
*)

Program
Definition option_CPO (A:Type) :=
{|
  cpo_ppo := option_PPO A;
  cpo_lub := 
  fun S => match (oracle (is_directed S))
  with
    left Hd =>  proj1_sig (option_lub S Hd)
  | right _ => None
  end;
  cpo_lub_prop :=  _ 
|}.

Next Obligation.
cbn.
intros.
destruct
     (oracle
       (is_directed  (P := option_Poset A) S)) ; [| contradiction].
exact  (proj2_sig (option_lub S i)).
Qed.
(*
Definition option_CPO (A:Type) :=
{|
  cpo_ppo := option_PPO A;
  cpo_lub := fun T Hd => proj1_sig (option_lub T Hd);
  cpo_lub_prop := fun T Hd => proj2_sig (option_lub T Hd)  
|}.
*)

Lemma option_compact{A:Type}: forall (c:option A), 
is_compact (P:= option_CPO A) c.
Proof.
intros [a |].
-
  intros T Hd Hle.
  specialize Hd as Hd'.
  rewrite (option_directed  T) in Hd'.
  destruct Hd' as [(a' & Heq ) | (a' & Heq)]; subst.
  +
    rewrite @cpo_lub_single in Hle.
    inversion Hle; subst.
    exists (Some a); split.
    *
     apply member_single.
    * apply @poset_refl.
  +
   exists a'; split; [now right |].
   replace  (cpo_lub  (c:= option_CPO A)
    (fun x : option A => x = None \/ x = a'))
    with (a': option A) in Hle; auto.
   rewrite (is_lub_cpo_lub_eq (C :=  option_CPO A) 
    (fun x : option_PPO A => x = None \/ x = a')).
   *
      symmetry.
      erewrite (@is_lub_cpo_lub_eq (option_CPO A) ); eauto.
      apply @ordered_pair_has_lub, @ppo_bot_least.
  *
    apply cpo_lub_prop.
    apply (@ordered_pair_is_directed (option_Poset A)).
    constructor.
  *   
    apply (@ordered_pair_is_directed (option_Poset A)).
    constructor.
 -  
  apply @bot_is_compact.   
Qed.
    
Lemma some_lub_member{A:Type}:
forall (T : Setof (option A))(a:A),
is_directed (P := option_Poset A) T -> 
is_lub (P := option_Poset A) T (Some a) -> member T (Some a).
Proof.
intros T a Hd Hl.
assert (Hle : 
option_le (Some a) (cpo_lub (c := option_CPO A) T)) by
 (
  rewrite (@is_lub_cpo_lub_eq (option_CPO A) _ _  Hl Hd);
  apply option_le_refl
 ).
 destruct (option_compact (Some a) _ Hd Hle) as (x & Hmx & Hlex).
 inversion Hlex; now subst.
 Qed.


Lemma member_lub_some{A:Type}:
forall (T : Setof (option A))(a:A),
is_directed (P := option_Poset A) T -> 
member T (Some a) -> is_lub (P := option_Poset A) T (Some a).
Proof.
intros T a Hm.
split.
- 
 intros [n |] Hmx; [| constructor].
 destruct Hm as (_ & Hd).
 destruct (Hd _ _ H Hmx) as (z & Hmz & Hle1 & Hle2).
 inversion Hle1; subst.
 inversion Hle2; now subst.
-
 intros y Huy.
 now apply Huy.
Qed.  


 Lemma cont_of_lub_some{C: CPO}{A:Type} : 
 forall (T: Setof C) (Hd: is_directed T)
 (f: C -> option A) ( a: A),
 is_continuous (P1 := C) (P2 := option_CPO A) f ->
 f (cpo_lub T) = Some a -> exists t, member T t /\ f t = Some a.
 Proof.
intros T Hd f a Hc Heqa.
destruct (Hc _ Hd) as (Hd' & Heqc).
rewrite Heqc in Heqa.
specialize (cpo_lub_prop _ Hd') as Hl.
rewrite Heqa in Hl.
specialize Hd' as Hd''.
apply some_lub_member with (a := a) in Hd''; auto.
destruct Hd'' as (z & Hmz & Heq); subst.
now exists z.
Qed.


Lemma option_compacts_le{A:Type} : 
forall (c : option A),
 compacts_le (P := option_CPO A) c = fun x => x <= c.
Proof.
intros c.
apply set_equal ; intro x ; split; intro Hmx.
-
 now destruct Hmx.
-
 split; auto.
 apply option_compact.
Qed.


Lemma my_algebraic_dir{A:Type} :
 forall c : option_CPO A, is_directed (compacts_le c).
Proof.
intro c.
rewrite option_compacts_le.
rewrite (option_directed (fun x : option_CPO A => x <= c)).
destruct c.
-
  right.
  exists (Some a).    
  apply set_equal ; intro x ; split; intro Hmx.
  +
    inversion Hmx; subst; [now left | now right].
  +
   destruct Hmx as [Heq | Heq]; subst.
   * 
    apply @ppo_bot_least.
   *
    apply poset_refl.    
    -
    left.
    exists None.
    apply set_equal ; intro x ; split; intro Hmx.
    +
      apply @le_bot_iff_eq in Hmx; subst.
      apply member_single.
    +
     rewrite member_single_iff in Hmx; subst.
     apply poset_refl.    
Qed.

Lemma option_is_lub{A:Type}: 
forall (a: option A), is_lub (compacts_le (P := option_CPO A) a) a.
Proof.
intro a.  
rewrite option_compacts_le.
destruct a.
- 
 split.
 +
   intros x Hmx.
   inversion Hmx; subst; [apply @ppo_bot_least  | apply poset_refl].
 +
 intros y Hu.
 apply Hu, poset_refl.
 -
  replace  (fun x : option_CPO A => x <= None)
   with (single (@ppo_bot (option_PPO A))); [apply is_lub_single |].
  apply set_equal ; intro x ; split; intro Hmx.
  +
  rewrite member_single_iff in Hmx; subst.
  apply poset_refl.
  +
  apply @le_bot_iff_eq in Hmx; subst.
  apply member_single.
Qed.    
    

Lemma my_algebraic_lub{A:Type}: forall (c : option_CPO A),
 c = cpo_lub (compacts_le c) .
Proof.
intro c.
apply is_lub_cpo_lub_eq.
 - apply option_is_lub.
 - apply my_algebraic_dir.
Qed.  


Definition option_ALGEBRAIC (A:Type) : ALGEBRAIC :=
{|
  algebraic_cpo := option_CPO A;
  algebraic_dir := my_algebraic_dir;
  algebraic_lub := my_algebraic_lub
|}.


Program Definition option_completion (A:Type) : COMPLETION (option_PPO A) :=
{|
  alg := option_ALGEBRAIC A;
  inject := id;
  rev_inj := id
|}.


Next Obligation.
reflexivity.
Qed.

Next Obligation.
intros p p'; split; auto.
Qed.

Next Obligation.
intros  A p;
  apply option_compact.
Qed.

Next Obligation.
cbn.
intros;split;auto.
Qed.
