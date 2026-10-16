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


From Stdlib Require Import Psatz Arith NArith ZArith Bool Eqdep_dec.

From HB Require Import structures.

From GallinaC.Utils Require Import ListExt OptionExt UnitExt PTreeExt ReflectExt CompCertExt.
From GallinaC.Imp Require Export Monad Primitives Intops Uint32 Uintptr.
From GallinaC.Imp Require Import Addr Heap Store Storable State.
Import Unsigned.Notations.
From GallinaC.Compiler.Common Require Export Types Ctxt Expr CCInj Value.
From GallinaC.Compiler.Deep Require Import Cmd Prog OpSem(state, step, cont) Typing.
Import OpSem.Typing(type_state).

Local Open Scope program_scope.

Local Obligation Tactic := idtac.

Section Denotation.

Context {Sm: State.type}.

Section Elements.

  Definition denote_type (t: type) : Type :=
    match t with
    | t_unit => unit
    | t_bool => bool
    | t_nat => nat
    | t_ofst => N.t
    | t_ptr => @ptr_t Sm
    end.

  Definition denote_binding (tb: type * bool): option Type :=
    match tb with
    | (t_unit, true) => Some (unit: Type)
    | (t_bool, true) => Some (bool: Type)
    | (t_nat, true) => Some (nat: Type)
    | (t_ofst, true) => Some (N.t: Type)
    | (t_ptr, true) => Some (@ptr_t Sm: Type)
    | (_, false) => None
    end.

  Definition denote_type_memval (t: type): Storable.type (value (@ptr_t Sm)) :=
    match t with
    | t_unit => unit : Storable.type (value (@ptr_t Sm))
    | t_bool => bool : Storable.type (value (@ptr_t Sm))
    | t_nat => nat : Storable.type (value (@ptr_t Sm))
    | t_ofst => N : Storable.type (value (@ptr_t Sm))
    | t_ptr => @ptr_t Sm : Storable.type (value (@ptr_t Sm))
    end.

  Definition denote_value (v: value (@ptr_t Sm)) : denote_type (type_of_value v) :=
    match v with
    | v_tt => tt
    | v_bool b => b
    | v_nat n => n
    | v_ofst o => o
    | v_ptr p => p
    end.

  Definition denote_value_eq {v t} (EQ: type_of_value v = t) : denote_type t :=
    convert_eq (f_equal denote_type EQ) (denote_value v).

  Definition denote_local (_:unit): option Type :=
    Some (@var_name Sm: Type).

  Definition denote_id [A] (_: A): option Type := Some A.

  Fixpoint denote_sig' (tl: list type) (tout: type): Type :=
    match tl with
    | [] => Monad.program Sm (denote_type tout)
    | t::tl => (denote_type t) -> (denote_sig' tl tout)
    end.

  Definition denote_globdef (g: globdef): option Type :=
    match g with
    | AST.Gfun (AST.Internal fn) => Some (denote_sig' (fn_signature fn).(sig_args) (fn_signature fn).(sig_res))
    | AST.Gfun (AST.External ef) =>
        match Facts.ef_sig_dec ef with
        | Some sig => Some (denote_sig' sig.(sig_args) sig.(sig_res))
        | None => Some (unit: Type)
        end
    | AST.Gvar {| AST.gvar_info := t; |} => Some (denote_type t.(var_type))
    end.

  Lemma denote_types_agree: forall (t: type), denote_type t = denote_type_memval t.
  Proof.
    destruct t; reflexivity.
  Defined.

  Lemma denote_binding_eq: forall t, denote_binding (t, true) = Some (denote_type t).
  Proof.
    destruct t; reflexivity.
  Defined.

  Lemma denote_binding_false_eq: forall t, denote_binding (t, false) = None.
  Proof.
    destruct t; reflexivity.
  Defined.

  Lemma encode_denote_value v t (TY: type_of_value v = t):
    encode (s := denote_type_memval t)
      (convert_eq (denote_types_agree t) (denote_value_eq TY))
    = v.
  Proof using Type.
    unfold denote_value_eq, convert_eq.
    destruct TY; destruct v; reflexivity.
  Qed.

  Lemma decode_value_memval v t mv
    (TY: type_of_value v = t) (VMV: decode mv = Some v):
    decode (s := denote_type_memval t) mv
    = Some (convert_eq (denote_types_agree t) (denote_value_eq TY)).
  Proof using Type.
    cbn in VMV. injection VMV as EQmv. subst mv.
    unfold denote_value_eq, convert_eq.
    destruct TY; destruct v; reflexivity.
  Qed.

End Elements.

Local Notation denote_sig sig := (denote_sig' sig.(sig_args) sig.(sig_res)).

Local Notation denote_fn_sig fn := (denote_sig (fn_signature fn)).

Section Tree.

  Fixpoint denote_tree' [A: Type] (denote: A -> option Type) (ctx: Maps.PTree.tree' A): Type :=
    match ctx with
    | Maps.PTree.Node001 r => denote_tree' denote r
    | Maps.PTree.Node010 a =>
        match denote a with
        | Some d => d
        | None => unit
        end
    | Maps.PTree.Node011 a r =>
        match denote a with
        | Some d => d * (denote_tree' denote r)
        | None => denote_tree' denote r
        end
    | Maps.PTree.Node100 l => denote_tree' denote l
    | Maps.PTree.Node101 l r => denote_tree' denote l * denote_tree' denote r
    | Maps.PTree.Node110 l a =>
        match denote a with
        | Some d => denote_tree' denote l * d
        | None => denote_tree' denote l
        end
    | Maps.PTree.Node111 l a r =>
        match denote a with
        | Some d =>
            denote_tree' denote l * d * denote_tree' denote r
        | None =>
            denote_tree' denote l * denote_tree' denote r
        end
    end.

  Definition denote_tree [A: Type] (denote: A -> option Type) (ctx: Maps.PTree.t A): Type :=
    match ctx with
    | Maps.PTree.Empty => unit
    | Maps.PTree.Nodes ctx => denote_tree' denote ctx
    end.

  Definition cast_bind: forall [A] [a a0: A] [a_d] [denote: A -> option Type] (EQ: Some a = Some a0) (DENOTE: denote a0 = Some a_d) (m_d: match denote a with Some d => d | None => unit end), a_d.
  Proof.
    intros A a a0 a_d denote EQ DENOTE m_d.
    refine (eq_rect (denote a)
              (fun o => match o with Some d => d | None => unit end)
              m_d (Some a_d) _).
    refine (eq_trans _ DENOTE).
    exact (f_equal denote
             (f_equal (fun o => match o with Some x => x | None => a end) EQ)).
  Defined.

  Fixpoint denote_tree_lookup' [A: Type] [denote]
    [m: Maps.PTree.tree' A]
    {struct m}
    : forall k [a a_d]
             (GET: Maps.PTree.get' k m = Some a)
             (DENOTE: denote a = Some a_d)
             (m_d: denote_tree' denote m),
      a_d.
  Proof.
    destruct m as [ r | a | a r | l | l r | l a | l a r ];
      intros k aq a_d GET DENOTE m_d.
    - destruct k as [ q | q | ]; try discriminate GET.
      exact (denote_tree_lookup' A denote r q aq a_d GET DENOTE m_d).
    - destruct k as [ q | q | ]; try discriminate GET.
      exact (cast_bind GET DENOTE m_d).
    - destruct k as [ q | q | ]; try discriminate GET.
      + refine (denote_tree_lookup' A denote r q aq a_d GET DENOTE _).
        exact (match denote a as o return
                     (match o with
                      | Some d => d * denote_tree' denote r
                      | None   => denote_tree' denote r
                      end) -> denote_tree' denote r
               with
               | Some _ => fun m => snd m
               | None   => fun m => m
               end m_d).
      + refine (cast_bind GET DENOTE _).
        exact (match denote a as o return
                     (match o with
                      | Some d => d * denote_tree' denote r
                      | None   => denote_tree' denote r
                      end) -> (match o with Some d => d | None => unit end)
               with
               | Some _ => fun m => fst m
               | None   => fun _ => tt
               end m_d).
    - destruct k as [ q | q | ]; try discriminate GET.
      exact (denote_tree_lookup' A denote l q aq a_d GET DENOTE m_d).
    - destruct k as [ q | q | ]; try discriminate GET; cbn in m_d.
      + exact (denote_tree_lookup' A denote r q aq a_d GET DENOTE (snd m_d)).
      + exact (denote_tree_lookup' A denote l q aq a_d GET DENOTE (fst m_d)).
    - destruct k as [ q | q | ]; try discriminate GET.
      + refine (denote_tree_lookup' A denote l q aq a_d GET DENOTE _).
        exact (match denote a as o return
                     (match o with
                      | Some d => denote_tree' denote l * d
                      | None   => denote_tree' denote l
                      end) -> denote_tree' denote l
               with
               | Some _ => fun m => fst m
               | None   => fun m => m
               end m_d).
      + refine (cast_bind GET DENOTE _).
        exact (match denote a as o return
                     (match o with
                      | Some d => denote_tree' denote l * d
                      | None   => denote_tree' denote l
                      end) -> (match o with Some d => d | None => unit end)
               with
               | Some _ => fun m => snd m
               | None   => fun _ => tt
               end m_d).
    - destruct k as [ q | q | ].
      + refine (denote_tree_lookup' A denote r q aq a_d GET DENOTE _).
        exact (match denote a as o return
                     (match o with
                      | Some d => denote_tree' denote l * d * denote_tree' denote r
                      | None   => denote_tree' denote l * denote_tree' denote r
                      end) -> denote_tree' denote r
               with
               | Some _ => fun m => snd m
               | None   => fun m => snd m
               end m_d).
      + refine (denote_tree_lookup' A denote l q aq a_d GET DENOTE _).
        exact (match denote a as o return
                     (match o with
                      | Some d => denote_tree' denote l * d * denote_tree' denote r
                      | None   => denote_tree' denote l * denote_tree' denote r
                      end) -> denote_tree' denote l
               with
               | Some _ => fun m => fst (fst m)
               | None   => fun m => fst m
               end m_d).
      + refine (cast_bind GET DENOTE _).
        exact (match denote a as o return
                     (match o with
                      | Some d => denote_tree' denote l * d * denote_tree' denote r
                      | None   => denote_tree' denote l * denote_tree' denote r
                      end) -> (match o with Some d => d | None => unit end)
               with
               | Some _ => fun m => snd (fst m)
               | None   => fun _ => tt
               end m_d).
  Defined.

  Program Definition denote_tree_lookup [A: Type] [denote: A -> option Type] [m: Maps.PTree.t A]
    [k: positive] [a: A] [a_d: Type]
    (GET: Maps.PTree.get k m = Some a) (DENOTE: denote a = Some a_d) (m_d: denote_tree denote m):
    a_d.
  Proof.
    destruct m; [ discriminate |  ].
    exact (denote_tree_lookup' _ GET DENOTE m_d).
  Defined.

  Fixpoint denote_tree_set0 [A] [denote: A -> option Type] [a] [a_d]
    (p: positive) (DENOTE: denote a = Some a_d) (d: a_d)
    {struct p}
    : denote_tree' denote (Maps.PTree.set0 p a).
  Proof.
    destruct p as [q | q | ]; cbn.
    - exact (@denote_tree_set0 A denote a a_d q DENOTE d).
    - exact (@denote_tree_set0 A denote a a_d q DENOTE d).
    - exact (eq_rect (Some a_d)
               (fun o => match o with Some d' => d' | None => unit end)
               d (denote a) (eq_sym DENOTE)).
  Defined.

  Fixpoint denote_tree_unset0 [A] [denote: A -> option Type] [a]
    (p: positive) (DENOTE: denote a = None)
    {struct p}
    : denote_tree' denote (Maps.PTree.set0 p a).
  Proof.
    destruct p as [q | q | ]; cbn.
    - exact (@denote_tree_unset0 A denote a q DENOTE).
    - exact (@denote_tree_unset0 A denote a q DENOTE).
    - exact (eq_rect None
               (fun o => match o with Some d' => d' | None => unit end)
               tt (denote a) (eq_sym DENOTE)).
  Defined.

  Fixpoint denote_tree_set' [A: Type] [denote] [m: Maps.PTree.tree' A]
    {struct m}
    : forall (p: positive) [a] [a_d]
             (DENOTE: denote a = Some a_d)
             (d: a_d)
             (m_d: denote_tree' denote m),
      denote_tree' denote (Maps.PTree.set' p a m).
  Proof.
    destruct m as [r | a' | a' r | l | l r | l a' | l a' r];
      intros p a a_d DENOTE d m_d;
      destruct p as [q | q | ]; cbn in *.
    - exact (denote_tree_set' _ _ _ q _ _ DENOTE d m_d).
    - exact (@denote_tree_set0 A denote a a_d q DENOTE d, m_d).
    - exact (eq_rect (Some a_d)
               (fun o => match o with Some d' => (d' * denote_tree' denote r)%type | None => denote_tree' denote r end)
               (d, m_d) (denote a) (eq_sym DENOTE)).
    - refine (match denote a' as o return
                    match o with Some d' => d' | None => unit end
                    -> match o with Some d' => d' * denote_tree' denote (Maps.PTree.set0 q a) | None => denote_tree' denote (Maps.PTree.set0 q a) end
              with
              | Some _ => fun v => (v, @denote_tree_set0 A denote a a_d q DENOTE d)
              | None   => fun _ => @denote_tree_set0 A denote a a_d q DENOTE d
              end m_d).
    - refine (match denote a' as o return
                    match o with Some d' => d' | None => unit end
                    -> match o with Some d' => denote_tree' denote (Maps.PTree.set0 q a) * d' | None => denote_tree' denote (Maps.PTree.set0 q a) end
              with
              | Some _ => fun v => (@denote_tree_set0 A denote a a_d q DENOTE d, v)
              | None   => fun _ => @denote_tree_set0 A denote a a_d q DENOTE d
              end m_d).
    - exact (eq_rect (Some a_d)
               (fun o => match o with Some d' => d' | None => unit end)
               d (denote a) (eq_sym DENOTE)).
    - refine (match denote a' as o return
                    match o with Some d' => d' * denote_tree' denote r | None => denote_tree' denote r end
                    -> match o with Some d' => d' * denote_tree' denote (Maps.PTree.set' q a r) | None => denote_tree' denote (Maps.PTree.set' q a r) end
              with
              | Some _ => fun mm => (fst mm, denote_tree_set' _ _ _ q _ _ DENOTE d (snd mm))
              | None   => fun mm => denote_tree_set' _ _ _ q _ _ DENOTE d mm
              end m_d).
    - refine (match denote a' as o return
                    match o with Some d' => d' * denote_tree' denote r | None => denote_tree' denote r end
                    -> match o with Some d' => denote_tree' denote (Maps.PTree.set0 q a) * d' * denote_tree' denote r | None => denote_tree' denote (Maps.PTree.set0 q a) * denote_tree' denote r end
              with
              | Some _ => fun mm => (@denote_tree_set0 A denote a a_d q DENOTE d, fst mm, snd mm)
              | None   => fun mm => (@denote_tree_set0 A denote a a_d q DENOTE d, mm)
              end m_d).
    - exact (eq_rect (Some a_d)
               (fun o => match o with Some d' => (d' * denote_tree' denote r)%type | None => denote_tree' denote r end)
               (d, (match denote a' as o return
                          match o with Some d' => d' * denote_tree' denote r | None => denote_tree' denote r end
                          -> denote_tree' denote r
                    with
                    | Some _ => fun mm => snd mm
                    | None   => fun mm => mm
                    end m_d)) (denote a) (eq_sym DENOTE)).
    - exact (m_d, @denote_tree_set0 A denote a a_d q DENOTE d).
    - exact (denote_tree_set' _ _ _ q _ _ DENOTE d m_d).
    - exact (eq_rect (Some a_d)
               (fun o => match o with Some d' => (denote_tree' denote l * d')%type | None => denote_tree' denote l end)
               (m_d, d) (denote a) (eq_sym DENOTE)).
    - exact (fst m_d, denote_tree_set' _ _ _ q _ _ DENOTE d (snd m_d)).
    - exact (denote_tree_set' _ _ _ q _ _ DENOTE d (fst m_d), snd m_d).
    - exact (eq_rect (Some a_d)
               (fun o => match o with Some d' => (denote_tree' denote l * d' * denote_tree' denote r)%type | None => (denote_tree' denote l * denote_tree' denote r)%type end)
               (fst m_d, d, snd m_d) (denote a) (eq_sym DENOTE)).
    - refine (match denote a' as o return
                    match o with Some d' => denote_tree' denote l * d' | None => denote_tree' denote l end
                    -> match o with Some d' => denote_tree' denote l * d' * denote_tree' denote (Maps.PTree.set0 q a) | None => denote_tree' denote l * denote_tree' denote (Maps.PTree.set0 q a) end
              with
              | Some _ => fun mm => (fst mm, snd mm, @denote_tree_set0 A denote a a_d q DENOTE d)
              | None   => fun mm => (mm, @denote_tree_set0 A denote a a_d q DENOTE d)
              end m_d).
    - refine (match denote a' as o return
                    match o with Some d' => denote_tree' denote l * d' | None => denote_tree' denote l end
                    -> match o with Some d' => denote_tree' denote (Maps.PTree.set' q a l) * d' | None => denote_tree' denote (Maps.PTree.set' q a l) end
              with
              | Some _ => fun mm => (denote_tree_set' _ _ _ q _ _ DENOTE d (fst mm), snd mm)
              | None   => fun mm => denote_tree_set' _ _ _ q _ _ DENOTE d mm
              end m_d).
    - exact (eq_rect (Some a_d)
               (fun o => match o with Some d' => (denote_tree' denote l * d')%type | None => denote_tree' denote l end)
               ((match denote a' as o return
                       match o with Some d' => denote_tree' denote l * d' | None => denote_tree' denote l end
                       -> denote_tree' denote l
                 with
                 | Some _ => fun mm => fst mm
                 | None   => fun mm => mm
                 end m_d), d) (denote a) (eq_sym DENOTE)).
    - refine (match denote a' as o return
                    match o with Some d' => denote_tree' denote l * d' * denote_tree' denote r | None => denote_tree' denote l * denote_tree' denote r end
                    -> match o with Some d' => denote_tree' denote l * d' * denote_tree' denote (Maps.PTree.set' q a r) | None => denote_tree' denote l * denote_tree' denote (Maps.PTree.set' q a r) end
              with
              | Some _ => fun mm => (fst (fst mm), snd (fst mm), denote_tree_set' _ _ _ q _ _ DENOTE d (snd mm))
              | None   => fun mm => (fst mm, denote_tree_set' _ _ _ q _ _ DENOTE d (snd mm))
              end m_d).
    - refine (match denote a' as o return
                    match o with Some d' => denote_tree' denote l * d' * denote_tree' denote r | None => denote_tree' denote l * denote_tree' denote r end
                    -> match o with Some d' => denote_tree' denote (Maps.PTree.set' q a l) * d' * denote_tree' denote r | None => denote_tree' denote (Maps.PTree.set' q a l) * denote_tree' denote r end
              with
              | Some _ => fun mm => (denote_tree_set' _ _ _ q _ _ DENOTE d (fst (fst mm)), snd (fst mm), snd mm)
              | None   => fun mm => (denote_tree_set' _ _ _ q _ _ DENOTE d (fst mm), snd mm)
              end m_d).
    - exact (eq_rect (Some a_d)
               (fun o => match o with Some d' => (denote_tree' denote l * d' * denote_tree' denote r)%type | None => (denote_tree' denote l * denote_tree' denote r)%type end)
               ((match denote a' as o return
                       match o with Some d' => denote_tree' denote l * d' * denote_tree' denote r | None => denote_tree' denote l * denote_tree' denote r end
                       -> denote_tree' denote l
                 with
                 | Some _ => fun mm => fst (fst mm)
                 | None   => fun mm => fst mm
                 end m_d), d,
                 (match denote a' as o return
                        match o with Some d' => denote_tree' denote l * d' * denote_tree' denote r | None => denote_tree' denote l * denote_tree' denote r end
                        -> denote_tree' denote r
                  with
                  | Some _ => fun mm => snd mm
                  | None   => fun mm => snd mm
                  end m_d)) (denote a) (eq_sym DENOTE)).
  Defined.

  Definition denote_tree_set [A] [denote: A -> option Type] [a] [a_d] [m: Maps.PTree.t A]
    (k: positive) (DENOTE: denote a = Some a_d) (d: a_d)
    (m_d: denote_tree denote m)
    : denote_tree denote (Maps.PTree.set k a m).
  Proof.
    destruct m as [|m']; cbn in *.
    - exact (denote_tree_set0 k DENOTE d).
    - exact (denote_tree_set' k DENOTE d m_d).
  Defined.

  Fixpoint denote_tree_unset' [A: Type] [denote] [m: Maps.PTree.tree' A]
    {struct m}
    : forall (p: positive) [a]
             (DENOTE: denote a = None)
             (m_d: denote_tree' denote m),
      denote_tree' denote (Maps.PTree.set' p a m).
  Proof.
    destruct m as [r | a' | a' r | l | l r | l a' | l a' r];
      intros p a DENOTE m_d;
      destruct p as [q | q | ]; cbn in *.
    - exact (denote_tree_unset' _ _ _ q _ DENOTE m_d).
    - exact (@denote_tree_unset0 A denote a q DENOTE, m_d).
    - exact (eq_rect None
               (fun o => match o with Some d' => (d' * denote_tree' denote r)%type | None => denote_tree' denote r end)
               m_d (denote a) (eq_sym DENOTE)).
    - refine (match denote a' as o return
                    match o with Some d' => d' | None => unit end
                    -> match o with Some d' => d' * denote_tree' denote (Maps.PTree.set0 q a) | None => denote_tree' denote (Maps.PTree.set0 q a) end
              with
              | Some _ => fun v => (v, @denote_tree_unset0 A denote a q DENOTE)
              | None   => fun _ => @denote_tree_unset0 A denote a q DENOTE
              end m_d).
    - refine (match denote a' as o return
                    match o with Some d' => d' | None => unit end
                    -> match o with Some d' => denote_tree' denote (Maps.PTree.set0 q a) * d' | None => denote_tree' denote (Maps.PTree.set0 q a) end
              with
              | Some _ => fun v => (@denote_tree_unset0 A denote a q DENOTE, v)
              | None   => fun _ => @denote_tree_unset0 A denote a q DENOTE
              end m_d).
    - exact (eq_rect None
               (fun o => match o with Some d' => d' | None => unit end)
               tt (denote a) (eq_sym DENOTE)).
    - refine (match denote a' as o return
                    match o with Some d' => d' * denote_tree' denote r | None => denote_tree' denote r end
                    -> match o with Some d' => d' * denote_tree' denote (Maps.PTree.set' q a r) | None => denote_tree' denote (Maps.PTree.set' q a r) end
              with
              | Some _ => fun mm => (fst mm, denote_tree_unset' _ _ _ q _ DENOTE (snd mm))
              | None   => fun mm => denote_tree_unset' _ _ _ q _ DENOTE mm
              end m_d).
    - refine (match denote a' as o return
                    match o with Some d' => d' * denote_tree' denote r | None => denote_tree' denote r end
                    -> match o with Some d' => denote_tree' denote (Maps.PTree.set0 q a) * d' * denote_tree' denote r | None => denote_tree' denote (Maps.PTree.set0 q a) * denote_tree' denote r end
              with
              | Some _ => fun mm => (@denote_tree_unset0 A denote a q DENOTE, fst mm, snd mm)
              | None   => fun mm => (@denote_tree_unset0 A denote a q DENOTE, mm)
              end m_d).
    - exact (eq_rect None
               (fun o => match o with Some d' => (d' * denote_tree' denote r)%type | None => denote_tree' denote r end)
               (match denote a' as o return
                      match o with Some d' => d' * denote_tree' denote r | None => denote_tree' denote r end
                      -> denote_tree' denote r
                with
                | Some _ => fun mm => snd mm
                | None   => fun mm => mm
                end m_d) (denote a) (eq_sym DENOTE)).
    - exact (m_d, @denote_tree_unset0 A denote a q DENOTE).
    - exact (denote_tree_unset' _ _ _ q _ DENOTE m_d).
    - exact (eq_rect None
               (fun o => match o with Some d' => (denote_tree' denote l * d')%type | None => denote_tree' denote l end)
               m_d (denote a) (eq_sym DENOTE)).
    - exact (fst m_d, denote_tree_unset' _ _ _ q _ DENOTE (snd m_d)).
    - exact (denote_tree_unset' _ _ _ q _ DENOTE (fst m_d), snd m_d).
    - exact (eq_rect None
               (fun o => match o with Some d' => (denote_tree' denote l * d' * denote_tree' denote r)%type | None => (denote_tree' denote l * denote_tree' denote r)%type end)
               (fst m_d, snd m_d) (denote a) (eq_sym DENOTE)).
    - refine (match denote a' as o return
                    match o with Some d' => denote_tree' denote l * d' | None => denote_tree' denote l end
                    -> match o with Some d' => denote_tree' denote l * d' * denote_tree' denote (Maps.PTree.set0 q a) | None => denote_tree' denote l * denote_tree' denote (Maps.PTree.set0 q a) end
              with
              | Some _ => fun mm => (fst mm, snd mm, @denote_tree_unset0 A denote a q DENOTE)
              | None   => fun mm => (mm, @denote_tree_unset0 A denote a q DENOTE)
              end m_d).
    - refine (match denote a' as o return
                    match o with Some d' => denote_tree' denote l * d' | None => denote_tree' denote l end
                    -> match o with Some d' => denote_tree' denote (Maps.PTree.set' q a l) * d' | None => denote_tree' denote (Maps.PTree.set' q a l) end
              with
              | Some _ => fun mm => (denote_tree_unset' _ _ _ q _ DENOTE (fst mm), snd mm)
              | None   => fun mm => denote_tree_unset' _ _ _ q _ DENOTE mm
              end m_d).
    - exact (eq_rect None
               (fun o => match o with Some d' => (denote_tree' denote l * d')%type | None => denote_tree' denote l end)
               (match denote a' as o return
                      match o with Some d' => denote_tree' denote l * d' | None => denote_tree' denote l end
                      -> denote_tree' denote l
                with
                | Some _ => fun mm => fst mm
                | None   => fun mm => mm
                end m_d) (denote a) (eq_sym DENOTE)).
    - refine (match denote a' as o return
                    match o with Some d' => denote_tree' denote l * d' * denote_tree' denote r | None => denote_tree' denote l * denote_tree' denote r end
                    -> match o with Some d' => denote_tree' denote l * d' * denote_tree' denote (Maps.PTree.set' q a r) | None => denote_tree' denote l * denote_tree' denote (Maps.PTree.set' q a r) end
              with
              | Some _ => fun mm => (fst (fst mm), snd (fst mm), denote_tree_unset' _ _ _ q _ DENOTE (snd mm))
              | None   => fun mm => (fst mm, denote_tree_unset' _ _ _ q _ DENOTE (snd mm))
              end m_d).
    - refine (match denote a' as o return
                    match o with Some d' => denote_tree' denote l * d' * denote_tree' denote r | None => denote_tree' denote l * denote_tree' denote r end
                    -> match o with Some d' => denote_tree' denote (Maps.PTree.set' q a l) * d' * denote_tree' denote r | None => denote_tree' denote (Maps.PTree.set' q a l) * denote_tree' denote r end
              with
              | Some _ => fun mm => (denote_tree_unset' _ _ _ q _ DENOTE (fst (fst mm)), snd (fst mm), snd mm)
              | None   => fun mm => (denote_tree_unset' _ _ _ q _ DENOTE (fst mm), snd mm)
              end m_d).
    - exact (eq_rect None
               (fun o => match o with Some d' => (denote_tree' denote l * d' * denote_tree' denote r)%type | None => (denote_tree' denote l * denote_tree' denote r)%type end)
               ((match denote a' as o return
                       match o with Some d' => denote_tree' denote l * d' * denote_tree' denote r | None => denote_tree' denote l * denote_tree' denote r end
                       -> denote_tree' denote l
                 with
                 | Some _ => fun mm => fst (fst mm)
                 | None   => fun mm => fst mm
                 end m_d),
                 (match denote a' as o return
                        match o with Some d' => denote_tree' denote l * d' * denote_tree' denote r | None => denote_tree' denote l * denote_tree' denote r end
                        -> denote_tree' denote r
                  with
                  | Some _ => fun mm => snd mm
                  | None   => fun mm => snd mm
                  end m_d)) (denote a) (eq_sym DENOTE)).
  Defined.

  Definition denote_tree_unset [A] [denote: A -> option Type] [a] [m: Maps.PTree.t A]
    (k: positive) (DENOTE: denote a = None)
    (m_d: denote_tree denote m)
    : denote_tree denote (Maps.PTree.set k a m).
  Proof.
    destruct m as [|m']; cbn in *.
    - exact (denote_tree_unset0 k DENOTE).
    - exact (denote_tree_unset' k DENOTE m_d).
  Defined.

End Tree.

Section Stack.

  Fixpoint denote_stack [A] (denote: A -> option Type) (ctx: list A): Type :=
    match ctx with
    | [] => unit
    | a::ctx =>
        match denote a with
        | Some d => (denote_stack denote ctx * d)%type
        | None => denote_stack denote ctx
        end
    end.

  Fixpoint denote_stack_lookup
    [A] [denote] [n] [a] [a_d] [ctx: list A]
    (GET: List.nth_error ctx n = Some a)
    (DENOTE: denote a = Some a_d)
    (env: denote_stack denote ctx)
    {struct n}
    : a_d.
  Proof.
    destruct n as [|n], ctx as [|a' cs]; try discriminate GET.
    - refine (cast_bind GET DENOTE _).
      exact (match denote a' as o return
                   match o with Some d => denote_stack denote cs * d | None => denote_stack denote cs end
                   -> match o with Some d => d | None => unit end
             with
             | Some _ => fun e => snd e
             | None   => fun _ => tt
             end env).
    - refine (denote_stack_lookup _ _ n _ _ _ GET DENOTE _).
      exact (match denote a' as o return
                   match o with Some d => denote_stack denote cs * d | None => denote_stack denote cs end
                   -> denote_stack denote cs
             with
             | Some _ => fun e => fst e
             | None   => fun e => e
             end env).
  Defined.

  Fixpoint denote_stack_push
    [A] [denote] [ctx: list A]
    (env: denote_stack denote ctx)
    [a: A] [a_d] (DENOTE: denote a = Some a_d) (d: a_d)
    {struct ctx}
    : denote_stack denote (ctx ++ [a]).
  Proof.
    destruct ctx as [|c cs].
    - exact (eq_rect (Some a_d)
               (fun o => match o with Some d' => (unit * d')%type | None => unit end)
               (tt, d) (denote a) (eq_sym DENOTE)).
    - exact (match denote c as o
                   return match o with Some dc => denote_stack denote cs * dc | None => denote_stack denote cs end
                          -> match o with Some dc => denote_stack denote (cs ++ [a]) * dc | None => denote_stack denote (cs ++ [a]) end
             with
             | Some _ => fun e => (denote_stack_push _ _ _ (fst e) _ _ DENOTE d, snd e)
             | None   => fun e => denote_stack_push _ _ _ e _ _ DENOTE d
             end env).
  Defined.

  Fixpoint denote_stack_removelast_fuel
    [A] (denote: A -> option Type) (n: nat) {struct n}
    : forall (ctx: list A), length ctx <= n -> denote_stack denote ctx -> denote_stack denote (removelast ctx).
  Proof.
    destruct n as [|n'].
    - intros ctx LEN.
      destruct ctx as [|a cs].
      + exact (fun _ => tt).
      + exfalso; cbn in LEN; lia.
    - intros ctx LEN.
      destruct ctx as [|a cs].
      + exact (fun _ => tt).
      + destruct cs as [|c cs'].
        * exact (fun _ => tt).
        * assert (LEN': length (c :: cs') <= n') by (cbn in LEN |- *; lia).
          exact (match denote a as o
                       return match o with Some d => denote_stack denote (c::cs') * d | None => denote_stack denote (c::cs') end
                              -> match o with Some d => denote_stack denote (removelast (c::cs')) * d | None => denote_stack denote (removelast (c::cs')) end
                 with
                 | Some _ => fun e => (@denote_stack_removelast_fuel A denote n' (c::cs') LEN' (fst e), snd e)
                 | None   => fun e => @denote_stack_removelast_fuel A denote n' (c::cs') LEN' e
                 end).
  Defined.

  Definition denote_stack_removelast
    [A] (denote: A -> option Type) (ctx: list A)
    : denote_stack denote ctx -> denote_stack denote (removelast ctx) :=
    denote_stack_removelast_fuel denote (length ctx) ctx (le_n _).

End Stack.

Section Env.

  Fixpoint build_tree' [A] [denote: A -> option Type]
    (m: Maps.PTree.tree' A)
    (lookup: forall p a, Maps.PTree.get' p m = Some a ->
                         match denote a with Some d => d | None => unit end)
    {struct m}
    : denote_tree' denote m.
  Proof.
    destruct m as [r | a | a r | l | l r | l a | l a r]; cbn.
    - exact (build_tree' _ _ r (fun p a' GET => lookup (xI p) a' GET)).
    - exact (lookup xH a eq_refl).
    - refine (
          match denote a as o return
                (match o with Some d => d | None => unit end) ->
                (match o with Some d => d * denote_tree' denote r | None => denote_tree' denote r end)
          with
          | Some _ => fun v_a => (v_a, _)
          | None => fun _ => _
          end (lookup xH a eq_refl));
        exact (build_tree' _ _ r (fun p a' GET => lookup (xI p) a' GET)).
    - exact (build_tree' _ _ l (fun p a' GET => lookup (xO p) a' GET)).
    - exact (build_tree' _ _ l (fun p a' GET => lookup (xO p) a' GET),
              build_tree' _ _ r (fun p a' GET => lookup (xI p) a' GET)).
    - refine (
          match denote a as o return
                (match o with Some d => d | None => unit end) ->
                (match o with Some d => denote_tree' denote l * d | None => denote_tree' denote l end)
          with
          | Some _ => fun v_a => (_, v_a)
          | None => fun _ => _
          end (lookup xH a eq_refl));
        exact (build_tree' _ _ l (fun p a' GET => lookup (xO p) a' GET)).
    - refine (
          match denote a as o return
                (match o with Some d => d | None => unit end) ->
                (match o with
                 | Some d => denote_tree' denote l * d * denote_tree' denote r
                 | None => denote_tree' denote l * denote_tree' denote r
                 end)
          with
          | Some _ => fun v_a => (_, v_a, _)
          | None => fun _ => (_, _)
          end (lookup xH a eq_refl));
        first
          [ exact (build_tree' _ _ l (fun p a' GET => lookup (xO p) a' GET))
          | exact (build_tree' _ _ r (fun p a' GET => lookup (xI p) a' GET)) ].
  Defined.

  Definition denote_tree_uninit [A] [denote: A -> option Type] (m: Maps.PTree.t A)
    (H: forall p a, Maps.PTree.get p m = Some a -> denote a = None)
    : denote_tree denote m.
  Proof.
    destruct m as [|m']; [exact tt | ].
    apply build_tree'. intros p a GET.
    generalize (H p a GET).
    destruct (denote a) as [d|]; [ discriminate | intros _; exact tt ].
  Defined.

  Fixpoint denote_locals (locals: list (@var_name Sm))
    : denote_stack denote_local (List.map (fun _ => tt) locals) :=
    match locals with
    | [] => tt
    | n :: ls => (denote_locals ls, n)
    end.

  Lemma eq_rect_stack_cons (l1 l2 : list unit) (E : l1 = l2)
    (rest : denote_stack denote_local l1) (nm : @var_name Sm) :
    eq_rect (tt :: l1) (denote_stack denote_local) (rest, nm) (tt :: l2)
      (f_equal (cons tt) E)
    = (eq_rect l1 (denote_stack denote_local) rest l2 E, nm).
  Proof using Type. destruct E. reflexivity. Qed.

  Lemma denote_stack_removelast_fuel_irrel :
    forall (locals : list (@var_name Sm)) n m
      (LEn : length (List.map (fun _ => tt) locals) <= n)
      (LEm : length (List.map (fun _ => tt) locals) <= m)
      (env : denote_stack denote_local (List.map (fun _ => tt) locals)),
      denote_stack_removelast_fuel denote_local n (List.map (fun _ => tt) locals) LEn env
      = denote_stack_removelast_fuel denote_local m (List.map (fun _ => tt) locals) LEm env.
  Proof using Type.
    induction locals as [|n0 ls IH]; intros n m LEn LEm env.
    - destruct n, m; reflexivity.
    - destruct ls as [|n1 ls'].
      + destruct n as [|n]; [cbn in LEn; lia|]. destruct m as [|m]; [cbn in LEm; lia|].
        reflexivity.
      + destruct n as [|n]; [cbn in LEn; lia|]. destruct m as [|m]; [cbn in LEm; lia|].
        change (List.map (fun _ => tt) (n0 :: n1 :: ls'))
          with (tt :: tt :: List.map (fun _ => tt) ls') in env |- *.
        cbn [denote_stack_removelast_fuel denote_local].
        f_equal. apply IH.
  Qed.

  Lemma denote_locals_removelast_step (n0 n1 : @var_name Sm)
    (ls' : list (@var_name Sm)) n
    (LEn : length (List.map (fun _ => tt) (n0 :: n1 :: ls')) <= S n)
    (LEn' : length (List.map (fun _ => tt) (n1 :: ls')) <= n) :
    denote_stack_removelast_fuel denote_local (S n)
      (List.map (fun _ => tt) (n0 :: n1 :: ls')) LEn (denote_locals (n0 :: n1 :: ls'))
    = (denote_stack_removelast_fuel denote_local n
         (List.map (fun _ => tt) (n1 :: ls')) LEn' (denote_locals (n1 :: ls')), n0).
  Proof using Type.
    change (List.map (fun _ => tt) (n0 :: n1 :: ls'))
      with (tt :: tt :: List.map (fun _ => tt) ls').
    change (denote_locals (n0 :: n1 :: ls')) with (denote_locals (n1 :: ls'), n0).
    cbn [denote_stack_removelast_fuel denote_local fst snd].
    f_equal.
    change (tt :: List.map (fun _ => tt) ls') with (List.map (fun _ => tt) (n1 :: ls')).
    apply denote_stack_removelast_fuel_irrel.
  Qed.

  Lemma denote_locals_removelast_fuel (locals : list (@var_name Sm)) :
    forall nfuel (H : length (List.map (fun _ => tt) locals) <= nfuel),
      eq_rect (removelast (List.map (fun _ => tt) locals)) (denote_stack denote_local)
        (denote_stack_removelast_fuel denote_local nfuel
           (List.map (fun _ => tt) locals) H (denote_locals locals))
        (List.map (fun _ => tt) (removelast locals)) (map_removelast (fun _ => tt) locals)
      = denote_locals (removelast locals).
  Proof using Type.
    induction locals as [|n0 ls IH]; intros nfuel H.
    - cbn [List.map removelast denote_locals].
      rewrite (UIP_dec (ReflectExt.sumbool_of_reflect Algebra.eqb_spec) (map_removelast (fun _ => tt) []) eq_refl).
      destruct nfuel; reflexivity.
    - destruct ls as [|n1 ls'].
      + cbn [List.map removelast denote_locals].
        rewrite (UIP_dec (ReflectExt.sumbool_of_reflect Algebra.eqb_spec) (map_removelast (fun _ => tt) [n0]) eq_refl).
        destruct nfuel as [|nf]; [ cbn in H; lia | ]. reflexivity.
      + destruct nfuel as [|nf]; [ cbn in H; lia | ].
        assert (LEN' : length (List.map (fun _ => tt) (n1 :: ls')) <= nf)
          by (cbn in H |- *; lia).
        rewrite (denote_locals_removelast_step n0 n1 ls' nf H LEN').
        change (removelast (List.map (fun _ => tt) (n0 :: n1 :: ls')))
          with (tt :: removelast (List.map (fun _ => tt) (n1 :: ls'))).
        change (List.map (fun _ => tt) (removelast (n0 :: n1 :: ls')))
          with (tt :: List.map (fun _ => tt) (removelast (n1 :: ls'))).
        change (denote_locals (removelast (n0 :: n1 :: ls')))
          with (denote_locals (removelast (n1 :: ls')), n0).
        rewrite (UIP_dec (ReflectExt.sumbool_of_reflect Algebra.eqb_spec) (map_removelast (fun _ => tt) (n0 :: n1 :: ls'))
                   (f_equal (cons tt) (map_removelast (fun _ => tt) (n1 :: ls')))).
        rewrite eq_rect_stack_cons.
        rewrite (IH nf LEN'). reflexivity.
  Qed.

  Corollary denote_locals_removelast (locals : list (@var_name Sm)) :
    eq_rect (removelast (List.map (fun _ => tt) locals)) (denote_stack denote_local)
      (denote_stack_removelast denote_local (List.map (fun _ => tt) locals)
         (denote_locals locals))
      (List.map (fun _ => tt) (removelast locals)) (map_removelast (fun _ => tt) locals)
    = denote_locals (removelast locals).
  Proof using Type. apply denote_locals_removelast_fuel. Qed.

  Lemma denote_locals_push_step (n0 : @var_name Sm) (ls : list (@var_name Sm))
    (nm : @var_name Sm) :
    denote_stack_push (denote_locals (n0 :: ls))
      (eq_refl : denote_local tt = Some (@var_name Sm: Type)) nm
    = (denote_stack_push (denote_locals ls)
         (eq_refl : denote_local tt = Some (@var_name Sm: Type)) nm, n0).
  Proof using Type.
    change (denote_locals (n0 :: ls)) with (denote_locals ls, n0). reflexivity.
  Qed.

  Lemma denote_locals_push (locals : list (@var_name Sm)) (nm : @var_name Sm) :
    eq_rect (List.map (fun _ => tt) (locals ++ [nm])) (denote_stack denote_local)
      (denote_locals (locals ++ [nm]))
      (List.map (fun _ => tt) locals ++ [tt]) (map_app (fun _ => tt) locals [nm])
    = denote_stack_push (denote_locals locals)
        (eq_refl : denote_local tt = Some (@var_name Sm: Type)) nm.
  Proof using Type.
    induction locals as [|n0 ls IH].
    - match goal with |- context[eq_rect _ _ _ _ ?p] =>
        rewrite (UIP_dec (ReflectExt.sumbool_of_reflect Algebra.eqb_spec) p eq_refl) end.
      reflexivity.
    - change ((n0 :: ls) ++ [nm]) with (n0 :: (ls ++ [nm])).
      change (denote_locals (n0 :: (ls ++ [nm]))) with (denote_locals (ls ++ [nm]), n0).
      rewrite denote_locals_push_step.
      change (List.map (fun _ => tt) (n0 :: (ls ++ [nm])))
        with (tt :: List.map (fun _ => tt) (ls ++ [nm])).
      change (List.map (fun _ => tt) (n0 :: ls) ++ [tt])
        with (tt :: (List.map (fun _ => tt) ls ++ [tt])).
      match goal with |- context[eq_rect _ _ _ _ ?p] =>
        rewrite (UIP_dec (ReflectExt.sumbool_of_reflect Algebra.eqb_spec) p
                   (f_equal (cons tt) (map_app (fun _ => tt) ls [nm]))) end.
      rewrite eq_rect_stack_cons.
      f_equal. exact IH.
  Qed.

  Lemma eq_rect_eq_trans [A] (P : A -> Type) (a b c : A) (E1 : a = b) (E2 : b = c)
    (x : P a) :
    eq_rect a P x c (eq_trans E1 E2) = eq_rect b P (eq_rect a P x b E1) c E2.
  Proof using Type. destruct E2, E1. reflexivity. Qed.

  Lemma denote_locals_eq_rect_map (l l' : list (@var_name Sm)) (H : l = l') :
    eq_rect (List.map (fun _ => tt) l) (denote_stack denote_local) (denote_locals l)
      (List.map (fun _ => tt) l') (f_equal (List.map (fun _ => tt)) H)
    = denote_locals l'.
  Proof using Type. destruct H. reflexivity. Qed.

  Lemma denote_stack_removelast_locals_snoc (locals : list (@var_name Sm))
    (nm : @var_name Sm) :
    eq_rect (removelast (List.map (fun _ => tt) (locals ++ [nm]))) (denote_stack denote_local)
      (denote_stack_removelast denote_local (List.map (fun _ => tt) (locals ++ [nm]))
         (denote_locals (locals ++ [nm])))
      (List.map (fun _ => tt) locals)
      (eq_trans (map_removelast (fun _ => tt) (locals ++ [nm]))
                (f_equal (List.map (fun _ => tt)) (removelast_last locals nm)))
    = denote_locals locals.
  Proof using Type.
    rewrite eq_rect_eq_trans.
    rewrite denote_locals_removelast.
    apply (denote_locals_eq_rect_map (removelast (locals ++ [nm])) locals
             (removelast_last locals nm)).
  Qed.

  Definition denote_env [f] [ty_env: Maps.PTree.t (type * bool)]
    [e: Maps.PTree.t (value (@ptr_t Sm))]
    (EQ: OpSem.Typing.type_env f e = Some ty_env)
    : denote_tree denote_binding ty_env.
  Proof.
    destruct ty_env as [|m]; [exact tt | ].
    apply build_tree'. intros p [t b] GET.
    destruct b.
    - destruct (OpSem.Typing.type_env_get_value EQ GET) as [v _ TYv].
      destruct t; first [ exact tt | exact (denote_value_eq TYv) | idtac].
    - destruct t; exact tt.
  Defined.

  Definition exf_env : Type :=
    forall (nm: String.string) (sig: signature), option (denote_sig sig).

  Definition empty_exfs : exf_env := fun _ _ => None.

End Env.

Lemma cast_bind_eq_rect {A: EqDec.type} {denote: A->option Type}
  {a a_d} (GET: Some a = Some a) (DENOTE: denote a = Some a_d)
  (x: match denote a with Some d => d | None => unit end) :
  cast_bind GET DENOTE x
  = eq_rect (denote a) (fun o => match o with Some d => d | None => unit end) x (Some a_d) DENOTE.
Proof using Type.
  assert (GET = eq_refl) as -> by (apply (UIP_dec (ReflectExt.sumbool_of_reflect Algebra.eqb_spec))).
  unfold cast_bind. cbn [f_equal]. rewrite eq_trans_refl_l. reflexivity.
Qed.

Lemma denote_stack_lookup_locals:
  forall (locals: list (@var_name Sm)) n nm
    (GET: List.nth_error (List.map (fun _ => tt) locals) n = Some tt)
    (DEREF: List.nth_error locals n = Some nm),
    denote_stack_lookup (denote := denote_local) GET eq_refl (denote_locals locals) = nm.
Proof using Type.
  induction locals as [|a ls IH]; intros [|n] nm GET DEREF; cbn in *; try discriminate.
  - cbn [denote_stack_lookup].
    rewrite cast_bind_eq_rect.
    cbn. injection DEREF as <-. reflexivity.
  - cbn [denote_stack_lookup]. apply IH. exact DEREF.
Qed.

Lemma denote_tree_lookup'_build_tree' {A: EqDec.type}
  {denote: A -> option Type} :
  forall (m: Maps.PTree.tree' A)
         (lk: forall p a, Maps.PTree.get' p m = Some a ->
                          match denote a with Some d => d | None => unit end)
         k v v_d (GET: Maps.PTree.get' k m = Some v) (DENOTE: denote v = Some v_d),
    denote_tree_lookup' k GET DENOTE (build_tree' m lk)
    = eq_rect (denote v) (fun o => match o with Some d => d | None => unit end)
        (lk k v GET) (Some v_d) DENOTE.
Proof using Type.
  intro m;
  induction m as [r IHr | a | a r IHr | l IHl | l IHl r IHr | l IHl a | l IHl a r IHr];
    intros lk k v v_d GET DENOTE;
    cbn [build_tree' denote_tree_lookup'];
    revert GET; destruct k as [q|q|]; intro GET; try discriminate GET.
  - apply IHr.
  - pose proof GET as GETv; cbn in GETv;
    match goal with [ GETv : Some ?nv = Some ?vv |- _ ] => assert (nv = vv) as -> by congruence end;
    clear GETv.
    assert (GET = eq_refl) as -> by (apply (UIP_dec (ReflectExt.sumbool_of_reflect Algebra.eqb_spec))).
    rewrite cast_bind_eq_rect; try reflexivity; f_equal;
    match goal with [ |- context [ lk ?p v ?e ] ] => generalize (lk p v e) end;
    destruct (denote v) as [d|] eqn:DEN;
      first [ (intros y; cbn [fst snd]; reflexivity) | discriminate DENOTE ].
  - match goal with [ |- context [ lk ?p a ?e ] ] => generalize (lk p a e) end;
    destruct (denote a) as [d|]; cbn [fst snd]; intro; apply IHr.
  - pose proof GET as GETv; cbn in GETv;
    match goal with [ GETv : Some ?nv = Some ?vv |- _ ] => assert (nv = vv) as -> by congruence end;
    clear GETv.
    assert (GET = eq_refl) as -> by (apply (UIP_dec (ReflectExt.sumbool_of_reflect Algebra.eqb_spec))).
    rewrite cast_bind_eq_rect.
    f_equal.
    match goal with [ |- context [ lk ?p v ?e ] ] => generalize (lk p v e) end.
    destruct (denote v) as [d|] eqn:DEN.
    + intros y; cbn [fst snd]; reflexivity.
    + discriminate DENOTE.
  - apply IHl.
  - cbn [fst snd]; apply IHr.
  - cbn [fst snd]; apply IHl.
  - match goal with [ |- context [ lk ?p a ?e ] ] => generalize (lk p a e) end;
    destruct (denote a) as [d|]; cbn [fst snd]; intro; apply IHl.
  - pose proof GET as GETv; cbn in GETv;
    match goal with [ GETv : Some ?nv = Some ?vv |- _ ] => assert (nv = vv) as -> by congruence end;
    clear GETv.
    assert (GET = eq_refl) as -> by (apply (UIP_dec (ReflectExt.sumbool_of_reflect Algebra.eqb_spec))).
    rewrite cast_bind_eq_rect; try reflexivity; f_equal;
    match goal with [ |- context [ lk ?p v ?e ] ] => generalize (lk p v e) end;
    destruct (denote v) as [d|] eqn:DEN;
      first [ (intros y; cbn [fst snd]; reflexivity) | discriminate DENOTE ].
  - match goal with [ |- context [ lk ?p a ?e ] ] => generalize (lk p a e) end;
    destruct (denote a) as [d|]; cbn [fst snd]; intro; apply IHr.
  - match goal with [ |- context [ lk ?p a ?e ] ] => generalize (lk p a e) end;
    destruct (denote a) as [d|]; cbn [fst snd]; intro; apply IHl.
  - pose proof GET as GETv; cbn in GETv;
    match goal with [ GETv : Some ?nv = Some ?vv |- _ ] => assert (nv = vv) as -> by congruence end;
    clear GETv.
    assert (GET = eq_refl) as -> by (apply (UIP_dec (ReflectExt.sumbool_of_reflect Algebra.eqb_spec))).
    rewrite cast_bind_eq_rect; try reflexivity; f_equal;
    match goal with [ |- context [ lk ?p v ?e ] ] => generalize (lk p v e) end;
    destruct (denote v) as [d|] eqn:DEN;
      first [ (intros y; cbn [fst snd]; reflexivity) | discriminate DENOTE ].
Qed.

Definition cast_node {A} {a a0: A} {denote: A -> option Type} (EQ: Some a = Some a0)
  (m_d: match denote a with Some d => d | None => unit end)
  : match denote a0 with Some d => d | None => unit end :=
  eq_rect (denote a) (fun o => match o with Some d => d | None => unit end)
    m_d (denote a0)
    (f_equal denote (f_equal (fun o => match o with Some x => x | None => a end) EQ)).

Fixpoint denote_tree_lookup'_tot [A: Type] [denote]
  [m: Maps.PTree.tree' A]
  {struct m}
  : forall k [a]
           (GET: Maps.PTree.get' k m = Some a)
           (m_d: denote_tree' denote m),
    match denote a with Some d => d | None => unit end.
Proof.
  destruct m as [ r | a | a r | l | l r | l a | l a r ];
    intros k aq GET m_d.
  - destruct k as [ q | q | ]; try discriminate GET.
    exact (denote_tree_lookup'_tot A denote r q aq GET m_d).
  - destruct k as [ q | q | ]; try discriminate GET.
    exact (cast_node GET m_d).
  - destruct k as [ q | q | ]; try discriminate GET.
    + refine (denote_tree_lookup'_tot A denote r q aq GET _).
      exact (match denote a as o return
                   (match o with
                    | Some d => d * denote_tree' denote r
                    | None   => denote_tree' denote r
                    end) -> denote_tree' denote r
             with
             | Some _ => fun m => snd m
             | None   => fun m => m
             end m_d).
    + refine (cast_node GET _).
      exact (match denote a as o return
                   (match o with
                    | Some d => d * denote_tree' denote r
                    | None   => denote_tree' denote r
                    end) -> (match o with Some d => d | None => unit end)
             with
             | Some _ => fun m => fst m
             | None   => fun _ => tt
             end m_d).
  - destruct k as [ q | q | ]; try discriminate GET.
    exact (denote_tree_lookup'_tot A denote l q aq GET m_d).
  - destruct k as [ q | q | ]; try discriminate GET; cbn in m_d.
    + exact (denote_tree_lookup'_tot A denote r q aq GET (snd m_d)).
    + exact (denote_tree_lookup'_tot A denote l q aq GET (fst m_d)).
  - destruct k as [ q | q | ]; try discriminate GET.
    + refine (denote_tree_lookup'_tot A denote l q aq GET _).
      exact (match denote a as o return
                   (match o with
                    | Some d => denote_tree' denote l * d
                    | None   => denote_tree' denote l
                    end) -> denote_tree' denote l
             with
             | Some _ => fun m => fst m
             | None   => fun m => m
             end m_d).
    + refine (cast_node GET _).
      exact (match denote a as o return
                   (match o with
                    | Some d => denote_tree' denote l * d
                    | None   => denote_tree' denote l
                    end) -> (match o with Some d => d | None => unit end)
             with
             | Some _ => fun m => snd m
             | None   => fun _ => tt
             end m_d).
  - destruct k as [ q | q | ].
    + refine (denote_tree_lookup'_tot A denote r q aq GET _).
      exact (match denote a as o return
                   (match o with
                    | Some d => denote_tree' denote l * d * denote_tree' denote r
                    | None   => denote_tree' denote l * denote_tree' denote r
                    end) -> denote_tree' denote r
             with
             | Some _ => fun m => snd m
             | None   => fun m => snd m
             end m_d).
    + refine (denote_tree_lookup'_tot A denote l q aq GET _).
      exact (match denote a as o return
                   (match o with
                    | Some d => denote_tree' denote l * d * denote_tree' denote r
                    | None   => denote_tree' denote l * denote_tree' denote r
                    end) -> denote_tree' denote l
             with
             | Some _ => fun m => fst (fst m)
             | None   => fun m => fst m
             end m_d).
    + refine (cast_node GET _).
      exact (match denote a as o return
                   (match o with
                    | Some d => denote_tree' denote l * d * denote_tree' denote r
                    | None   => denote_tree' denote l * denote_tree' denote r
                    end) -> (match o with Some d => d | None => unit end)
             with
             | Some _ => fun m => snd (fst m)
             | None   => fun _ => tt
             end m_d).
Defined.

Lemma eq_rect_inj {U} (P: U -> Type) {a b} (e: a = b) {x y: P a} :
  eq_rect a P x b e = eq_rect a P y b e -> x = y.
Proof using Type. destruct e. exact (fun h => h). Qed.

Lemma build_tree'_ext_lk {A} {denote: A -> option Type} (m: Maps.PTree.tree' A) :
  forall (lk1 lk2: forall p a, Maps.PTree.get' p m = Some a ->
                               match denote a with Some d => d | None => unit end),
    (forall p a (G: Maps.PTree.get' p m = Some a), lk1 p a G = lk2 p a G) ->
    build_tree' m lk1 = build_tree' m lk2.
Proof using Type.
  induction m as [r IHr | a | a r IHr | l IHl | l IHl r IHr | l IHl a | l IHl a r IHr];
    intros lk1 lk2 H; cbn [build_tree'].
  - apply IHr; intros; apply H.
  - apply H.
  - rewrite (H xH a eq_refl).
    rewrite (IHr (fun p a' G => lk1 (xI p) a' G) (fun p a' G => lk2 (xI p) a' G)
                 (fun p a' G => H (xI p) a' G)).
    reflexivity.
  - apply IHl; intros; apply H.
  - rewrite (IHl (fun p a' G => lk1 (xO p) a' G) (fun p a' G => lk2 (xO p) a' G)
                 (fun p a' G => H (xO p) a' G)).
    rewrite (IHr (fun p a' G => lk1 (xI p) a' G) (fun p a' G => lk2 (xI p) a' G)
                 (fun p a' G => H (xI p) a' G)).
    reflexivity.
  - rewrite (H xH a eq_refl).
    rewrite (IHl (fun p a' G => lk1 (xO p) a' G) (fun p a' G => lk2 (xO p) a' G)
                 (fun p a' G => H (xO p) a' G)).
    reflexivity.
  - rewrite (H xH a eq_refl).
    rewrite (IHl (fun p a' G => lk1 (xO p) a' G) (fun p a' G => lk2 (xO p) a' G)
                 (fun p a' G => H (xO p) a' G)).
    rewrite (IHr (fun p a' G => lk1 (xI p) a' G) (fun p a' G => lk2 (xI p) a' G)
                 (fun p a' G => H (xI p) a' G)).
    reflexivity.
Qed.

Lemma cast_node_refl {A} {a: A} {denote: A -> option Type}
  (m_d: match denote a with Some d => d | None => unit end) :
  cast_node (eq_refl: Some a = Some a) m_d = m_d.
Proof using Type. reflexivity. Qed.

Definition optR_leaf (R: Type) (o: option Type)
  : match o with Some d => (d * R)%type | None => R end -> match o with Some d => d | None => unit end
  := match o with Some _ => fun m => fst m | None => fun _ => tt end.
Definition optR_rest (R: Type) (o: option Type)
  : match o with Some d => (d * R)%type | None => R end -> R
  := match o with Some _ => fun m => snd m | None => fun m => m end.
Definition optL_leaf (L: Type) (o: option Type)
  : match o with Some d => (L * d)%type | None => L end -> match o with Some d => d | None => unit end
  := match o with Some _ => fun m => snd m | None => fun _ => tt end.
Definition optL_rest (L: Type) (o: option Type)
  : match o with Some d => (L * d)%type | None => L end -> L
  := match o with Some _ => fun m => fst m | None => fun m => m end.
Definition optLR_leaf (L R: Type) (o: option Type)
  : match o with Some d => (L * d * R)%type | None => (L * R)%type end -> match o with Some d => d | None => unit end
  := match o with Some _ => fun m => snd (fst m) | None => fun _ => tt end.
Definition optLR_restl (L R: Type) (o: option Type)
  : match o with Some d => (L * d * R)%type | None => (L * R)%type end -> L
  := match o with Some _ => fun m => fst (fst m) | None => fun m => fst m end.
Definition optLR_restr (L R: Type) (o: option Type)
  : match o with Some d => (L * d * R)%type | None => (L * R)%type end -> R
  := match o with Some _ => fun m => snd m | None => fun m => snd m end.

Lemma build_tree'_eta {A} {denote: A -> option Type} (m: Maps.PTree.tree' A) :
  forall (m_d: denote_tree' denote m),
    m_d = build_tree' m (fun p a (G: Maps.PTree.get' p m = Some a) =>
                           denote_tree_lookup'_tot p G m_d).
Proof using Type.
  induction m as [r IHr | a | a r IHr | l IHl | l IHl r IHr | l IHl a | l IHl a r IHr];
    intros m_d; cbn [denote_tree' build_tree'].
  - transitivity (build_tree' r
                    (fun p a (G: Maps.PTree.get' p r = Some a) =>
                       denote_tree_lookup'_tot p G m_d));
      [ exact (IHr m_d)
      | apply build_tree'_ext_lk; intros ? ? ?; reflexivity ].
  - reflexivity.
  - refine (match denote a as o return
              forall md: match o with Some d => (d * denote_tree' denote r)%type | None => denote_tree' denote r end,
                md = match o as o0 return
                       (match o0 with Some d => d | None => unit end ->
                        match o0 with Some d => (d * denote_tree' denote r)%type | None => denote_tree' denote r end)
                     with
                     | Some _ => fun v => (v, build_tree' r (fun p a0 (G: Maps.PTree.get' p r = Some a0) =>
                                     denote_tree_lookup'_tot p G (optR_rest (denote_tree' denote r) o md)))
                     | None => fun _ => build_tree' r (fun p a0 (G: Maps.PTree.get' p r = Some a0) =>
                                     denote_tree_lookup'_tot p G (optR_rest (denote_tree' denote r) o md))
                     end (optR_leaf (denote_tree' denote r) o md)
            with Some d => fun md => _ | None => fun md => _ end m_d).
    + destruct md as [v rd]; cbn [optR_leaf optR_rest fst snd].
      rewrite <- (IHr rd). reflexivity.
    + cbn [optR_leaf optR_rest]. exact (IHr md).
  - transitivity (build_tree' l
                    (fun p a (G: Maps.PTree.get' p l = Some a) =>
                       denote_tree_lookup'_tot p G m_d));
      [ exact (IHl m_d)
      | apply build_tree'_ext_lk; intros ? ? ?; reflexivity ].
  - destruct m_d as [ml mr]. f_equal.
    + transitivity (build_tree' l
                      (fun p a (G: Maps.PTree.get' p l = Some a) =>
                         denote_tree_lookup'_tot p G ml));
        [ apply (IHl ml)
        | apply build_tree'_ext_lk; intros ? ? ?; reflexivity ].
    + transitivity (build_tree' r
                      (fun p a (G: Maps.PTree.get' p r = Some a) =>
                         denote_tree_lookup'_tot p G mr));
        [ apply (IHr mr)
        | apply build_tree'_ext_lk; intros ? ? ?; reflexivity ].
  - refine (match denote a as o return
              forall md: match o with Some d => (denote_tree' denote l * d)%type | None => denote_tree' denote l end,
                md = match o as o0 return
                       (match o0 with Some d => d | None => unit end ->
                        match o0 with Some d => (denote_tree' denote l * d)%type | None => denote_tree' denote l end)
                     with
                     | Some _ => fun v => (build_tree' l (fun p a0 (G: Maps.PTree.get' p l = Some a0) =>
                                     denote_tree_lookup'_tot p G (optL_rest (denote_tree' denote l) o md)), v)
                     | None => fun _ => build_tree' l (fun p a0 (G: Maps.PTree.get' p l = Some a0) =>
                                     denote_tree_lookup'_tot p G (optL_rest (denote_tree' denote l) o md))
                     end (optL_leaf (denote_tree' denote l) o md)
            with Some d => fun md => _ | None => fun md => _ end m_d).
    + destruct md as [ml v]; cbn [optL_leaf optL_rest fst snd].
      rewrite <- (IHl ml). reflexivity.
    + cbn [optL_leaf optL_rest]. exact (IHl md).
  - refine (match denote a as o return
              forall md: match o with Some d => (denote_tree' denote l * d * denote_tree' denote r)%type
                                    | None => (denote_tree' denote l * denote_tree' denote r)%type end,
                md = match o as o0 return
                       (match o0 with Some d => d | None => unit end ->
                        match o0 with Some d => (denote_tree' denote l * d * denote_tree' denote r)%type
                                   | None => (denote_tree' denote l * denote_tree' denote r)%type end)
                     with
                     | Some _ => fun v => (build_tree' l (fun p a0 (G: Maps.PTree.get' p l = Some a0) =>
                                     denote_tree_lookup'_tot p G (optLR_restl (denote_tree' denote l) (denote_tree' denote r) o md)),
                                   v,
                                   build_tree' r (fun p a0 (G: Maps.PTree.get' p r = Some a0) =>
                                     denote_tree_lookup'_tot p G (optLR_restr (denote_tree' denote l) (denote_tree' denote r) o md)))
                     | None => fun _ => (build_tree' l (fun p a0 (G: Maps.PTree.get' p l = Some a0) =>
                                     denote_tree_lookup'_tot p G (optLR_restl (denote_tree' denote l) (denote_tree' denote r) o md)),
                                   build_tree' r (fun p a0 (G: Maps.PTree.get' p r = Some a0) =>
                                     denote_tree_lookup'_tot p G (optLR_restr (denote_tree' denote l) (denote_tree' denote r) o md)))
                     end (optLR_leaf (denote_tree' denote l) (denote_tree' denote r) o md)
            with Some d => fun md => _ | None => fun md => _ end m_d).
    + destruct md as [[ml v] rd]; cbn [optLR_leaf optLR_restl optLR_restr fst snd].
      rewrite <- (IHl ml), <- (IHr rd). reflexivity.
    + destruct md as [ml rd]; cbn [optLR_leaf optLR_restl optLR_restr fst snd].
      rewrite <- (IHl ml), <- (IHr rd). reflexivity.
Qed.

Lemma denote_tree_lookup'_tot_eq {A: EqDec.type}
  {denote: A -> option Type} (m: Maps.PTree.tree' A)
  k a a_d (GET: Maps.PTree.get' k m = Some a) (DEN: denote a = Some a_d)
  (m_d: denote_tree' denote m) :
  denote_tree_lookup' k GET DEN m_d
  = eq_rect (denote a) (fun o => match o with Some d => d | None => unit end)
      (denote_tree_lookup'_tot k GET m_d) (Some a_d) DEN.
Proof using Type.
  rewrite (build_tree'_eta m m_d) at 1.
  exact (denote_tree_lookup'_build_tree' m _ k a a_d GET DEN).
Qed.

Lemma denote_tree_lookup_indep_DEN {A: EqDec.type}
  {denote: A -> option Type} {m: Maps.PTree.t A} {k a a_d a_d0}
  (GET: Maps.PTree.get k m = Some a)
  (DEN: denote a = Some a_d) (DEN0: denote a = Some a_d0)
  (x y: denote_tree denote m) :
  denote_tree_lookup GET DEN0 x = denote_tree_lookup GET DEN0 y ->
  denote_tree_lookup GET DEN x = denote_tree_lookup GET DEN y.
Proof using Type.
  destruct m as [|m']; [discriminate GET|].
  cbn [denote_tree_lookup]. intro H.
  rewrite !denote_tree_lookup'_tot_eq in H |- *.
  apply (eq_rect_inj (fun o : option Type => match o with Some d => d | None => unit end) DEN0) in H.
  rewrite H. reflexivity.
Qed.

Lemma opt_val_ext (o: option Type)
  (u v: match o with Some d => d | None => unit end)
  (H: forall a_d (E: o = Some a_d),
        eq_rect o (fun o0 => match o0 with Some d => d | None => unit end) u (Some a_d) E
      = eq_rect o (fun o0 => match o0 with Some d => d | None => unit end) v (Some a_d) E) :
  u = v.
Proof using Type.
  destruct o as [a_d|].
  - exact (H a_d eq_refl).
  - destruct u, v; reflexivity.
Qed.

Lemma opt_leaf_eq_rect {R: Type} (o: option Type) {a_d: Type}
  (E: Some a_d = o) (d: a_d) (X: R) :
  match o as o0 return
        (match o0 with Some D => D * R | None => R end
         -> match o0 with Some D => D | None => unit end)
  with
  | Some _ => fun m => fst m
  | None   => fun _ => tt
  end
    (eq_rect (Some a_d)
       (fun o0 => match o0 with Some D => (D * R)%type | None => R end)
       (d, X) o E)
  = eq_rect (Some a_d) (fun o0 => match o0 with Some D => D | None => unit end) d o E.
Proof using Type. destruct E. reflexivity. Qed.

Lemma opt_leaf_eq_rect_L {L: Type} (o: option Type) {a_d: Type}
  (E: Some a_d = o) (d: a_d) (X: L) :
  match o as o0 return
        (match o0 with Some D => L * D | None => L end
         -> match o0 with Some D => D | None => unit end)
  with
  | Some _ => fun m => snd m
  | None   => fun _ => tt
  end
    (eq_rect (Some a_d)
       (fun o0 => match o0 with Some D => (L * D)%type | None => L end)
       (X, d) o E)
  = eq_rect (Some a_d) (fun o0 => match o0 with Some D => D | None => unit end) d o E.
Proof using Type. destruct E. reflexivity. Qed.

Lemma opt_leaf_eq_rect_LR {L R: Type} (o: option Type) {a_d: Type}
  (E: Some a_d = o) (d: a_d) (XL: L) (XR: R) :
  match o as o0 return
        (match o0 with Some D => L * D * R | None => L * R end
         -> match o0 with Some D => D | None => unit end)
  with
  | Some _ => fun m => snd (fst m)
  | None   => fun _ => tt
  end
    (eq_rect (Some a_d)
       (fun o0 => match o0 with Some D => (L * D * R)%type | None => (L * R)%type end)
       (XL, d, XR) o E)
  = eq_rect (Some a_d) (fun o0 => match o0 with Some D => D | None => unit end) d o E.
Proof using Type. destruct E. reflexivity. Qed.

Lemma denote_tree'_ext {A: EqDec.type}
  {denote: A -> option Type} (m: Maps.PTree.tree' A) (x y: denote_tree' denote m)
  (H: forall k a a_d (GET: Maps.PTree.get' k m = Some a) (DEN: denote a = Some a_d),
        denote_tree_lookup' k GET DEN x = denote_tree_lookup' k GET DEN y) :
  x = y.
Proof using Type.
  rewrite (build_tree'_eta m x), (build_tree'_eta m y).
  apply build_tree'_ext_lk; intros p a G.
  apply opt_val_ext; intros a_d DEN.
  rewrite <- (denote_tree_lookup'_tot_eq m p a a_d G DEN x),
          <- (denote_tree_lookup'_tot_eq m p a a_d G DEN y).
  apply (H p a a_d G DEN).
Qed.

Lemma denote_tree_ext {A: EqDec.type}
  {denote: A -> option Type} (m: Maps.PTree.t A) (x y: denote_tree denote m)
  (H: forall k a a_d (GET: Maps.PTree.get k m = Some a) (DEN: denote a = Some a_d),
        denote_tree_lookup GET DEN x = denote_tree_lookup GET DEN y) :
  x = y.
Proof using Type.
  destruct m as [|m'].
  - destruct x, y; reflexivity.
  - apply denote_tree'_ext; intros k a a_d GET DEN.
    exact (H k a a_d GET DEN).
Qed.

Lemma cast_node_same {A: EqDec.type} {a: A}
  {denote: A -> option Type} (GET: Some a = Some a)
  (m_d: match denote a with Some d => d | None => unit end) :
  cast_node GET m_d = m_d.
Proof using Type. rewrite (UIP_dec (ReflectExt.sumbool_of_reflect Algebra.eqb_spec) GET eq_refl). apply cast_node_refl. Qed.

Lemma denote_tree_lookup'_tot_set0 {A: EqDec.type}
  {denote: A -> option Type} {a a_d} (DEN: denote a = Some a_d) (d: a_d) :
  forall (k: positive) (GET: Maps.PTree.get' k (Maps.PTree.set0 k a) = Some a),
  denote_tree_lookup'_tot k GET (denote_tree_set0 k DEN d)
  = eq_rect (Some a_d) (fun o => match o with Some x => x | None => unit end)
      d (denote a) (eq_sym DEN).
Proof using Type.
  induction k as [q IH | q IH | ]; intro GET;
    cbn [denote_tree_set0 denote_tree_lookup'_tot].
  - apply IH.
  - apply IH.
  - apply cast_node_same.
Qed.

Lemma denote_tree_lookup'_tot_set' {A: EqDec.type}
  {denote: A -> option Type} {a a_d} (DEN: denote a = Some a_d) (d: a_d) :
  forall (m: Maps.PTree.tree' A) (k: positive) (m_d: denote_tree' denote m)
         (GET: Maps.PTree.get' k (Maps.PTree.set' k a m) = Some a),
  denote_tree_lookup'_tot k GET (denote_tree_set' k DEN d m_d)
  = eq_rect (Some a_d) (fun o => match o with Some x => x | None => unit end)
      d (denote a) (eq_sym DEN).
Proof using Type.
  induction m as [r IHr | a' | a' r IHr | l IHl | l IHl r IHr | l IHl a' | l IHl a' r IHr];
    intros k m_d GET; destruct k as [q | q | ];
    cbn [denote_tree_set' denote_tree_lookup'_tot Maps.PTree.set' Maps.PTree.set0].
  - apply IHr.
  - apply denote_tree_lookup'_tot_set0.
  - rewrite opt_leaf_eq_rect; apply cast_node_same.
  - cbn [denote_tree'] in m_d; revert m_d; destruct (denote a') as [d'|]; intro m_d;
      cbn [denote_tree_set' denote_tree_lookup'_tot];
      apply denote_tree_lookup'_tot_set0.
  - cbn [denote_tree'] in m_d; revert m_d; destruct (denote a') as [d'|]; intro m_d;
      cbn [denote_tree_set' denote_tree_lookup'_tot];
      apply denote_tree_lookup'_tot_set0.
  - apply cast_node_same.
  - cbn [denote_tree'] in m_d; revert m_d; destruct (denote a') as [d'|]; intro m_d;
      cbn [denote_tree_set' denote_tree_lookup'_tot];
      apply IHr.
  - cbn [denote_tree'] in m_d; revert m_d; destruct (denote a') as [d'|]; intro m_d;
      cbn [denote_tree_set' denote_tree_lookup'_tot];
      apply denote_tree_lookup'_tot_set0.
  - rewrite opt_leaf_eq_rect; apply cast_node_same.
  - apply denote_tree_lookup'_tot_set0.
  - apply IHl.
  - rewrite opt_leaf_eq_rect_L; apply cast_node_same.
  - apply IHr.
  - apply IHl.
  - rewrite opt_leaf_eq_rect_LR; apply cast_node_same.
  - cbn [denote_tree'] in m_d; revert m_d; destruct (denote a') as [d'|]; intro m_d;
      cbn [denote_tree_set' denote_tree_lookup'_tot];
      apply denote_tree_lookup'_tot_set0.
  - cbn [denote_tree'] in m_d; revert m_d; destruct (denote a') as [d'|]; intro m_d;
      cbn [denote_tree_set' denote_tree_lookup'_tot];
      apply IHl.
  - rewrite opt_leaf_eq_rect_L; apply cast_node_same.
  - cbn [denote_tree'] in m_d; revert m_d; destruct (denote a') as [d'|]; intro m_d;
      cbn [denote_tree_set' denote_tree_lookup'_tot];
      apply IHr.
  - cbn [denote_tree'] in m_d; revert m_d; destruct (denote a') as [d'|]; intro m_d;
      cbn [denote_tree_set' denote_tree_lookup'_tot];
      apply IHl.
  - rewrite opt_leaf_eq_rect_LR; apply cast_node_same.
Qed.

Lemma eq_rect_cancel' {X} (P: X -> Type) {x y: X} (e: x = y) (v: P y) :
  eq_rect x P (eq_rect y P v x (eq_sym e)) y e = v.
Proof using Type. destruct e. reflexivity. Qed.

Lemma denote_tree_lookup_set_same {A: EqDec.type}
  {denote: A -> option Type} {a a_d} (DEN: denote a = Some a_d) (d: a_d) :
  forall (m: Maps.PTree.t A) (k: positive) (m_d: denote_tree denote m)
         (G: Maps.PTree.get k (Maps.PTree.set k a m) = Some a),
  denote_tree_lookup G DEN (denote_tree_set k DEN d m_d) = d.
Proof using Type.
  intros m k m_d G.
  destruct m as [|m'];
    cbn [denote_tree_set] in *; unfold denote_tree_lookup.
  - change (Maps.PTree.set k a Maps.PTree.Empty)
      with (Maps.PTree.Nodes (Maps.PTree.set0 k a)) in *.
    cbn beta iota.
    rewrite denote_tree_lookup'_tot_eq, denote_tree_lookup'_tot_set0.
    exact (eq_rect_cancel' _ DEN d).
  - change (Maps.PTree.set k a (Maps.PTree.Nodes m'))
      with (Maps.PTree.Nodes (Maps.PTree.set' k a m')) in *.
    cbn beta iota.
    rewrite denote_tree_lookup'_tot_eq, denote_tree_lookup'_tot_set'.
    exact (eq_rect_cancel' _ DEN d).
Qed.

Lemma denote_tree_lookup_set_D {A: EqDec.type}
  {denote: A -> option Type} {a a_d} (DEN D: denote a = Some a_d) (d: a_d) :
  forall (m: Maps.PTree.t A) (k: positive) (m_d: denote_tree denote m)
         (G: Maps.PTree.get k (Maps.PTree.set k a m) = Some a),
  denote_tree_lookup G D (denote_tree_set k DEN d m_d)
  = eq_rect (denote a) (fun o => match o with Some x => x | None => unit end)
      (eq_rect (Some a_d) (fun o => match o with Some x => x | None => unit end)
         d (denote a) (eq_sym DEN))
      (Some a_d) D.
Proof using Type.
  intros m k m_d G.
  destruct m as [|m'];
    cbn [denote_tree_set] in *; unfold denote_tree_lookup.
  - change (Maps.PTree.set k a Maps.PTree.Empty)
      with (Maps.PTree.Nodes (Maps.PTree.set0 k a)) in *.
    cbn beta iota.
    rewrite denote_tree_lookup'_tot_eq, denote_tree_lookup'_tot_set0.
    reflexivity.
  - change (Maps.PTree.set k a (Maps.PTree.Nodes m'))
      with (Maps.PTree.Nodes (Maps.PTree.set' k a m')) in *.
    cbn beta iota.
    rewrite denote_tree_lookup'_tot_eq, denote_tree_lookup'_tot_set'.
    reflexivity.
Qed.

Lemma denote_tree_lookup'_tot_pirr {A: EqDec.type}
  {denote: A -> option Type} {m: Maps.PTree.tree' A} (k: positive) {a}
  (G G': Maps.PTree.get' k m = Some a) (m_d: denote_tree' denote m) :
  denote_tree_lookup'_tot k G m_d = denote_tree_lookup'_tot k G' m_d.
Proof using Type. rewrite (UIP_dec (ReflectExt.sumbool_of_reflect Algebra.eqb_spec) G G'). reflexivity. Qed.

Lemma proj_snd_eq_rect {R} (o: option Type) {D} (E: Some D = o) (xd: D) (xr: R) :
  match o as o0 return (match o0 with Some d => (d*R)%type | None => R end -> R) with
  | Some _ => fun m => snd m | None => fun m => m end
    (eq_rect (Some D) (fun o0 => match o0 with Some d => (d*R)%type | None => R end)
       (xd, xr) o E) = xr.
Proof using Type. destruct E; reflexivity. Qed.

Lemma proj_fst_eq_rect {L} (o: option Type) {D} (E: Some D = o) (xl: L) (xd: D) :
  match o as o0 return (match o0 with Some d => (L*d)%type | None => L end -> L) with
  | Some _ => fun m => fst m | None => fun m => m end
    (eq_rect (Some D) (fun o0 => match o0 with Some d => (L*d)%type | None => L end)
       (xl, xd) o E) = xl.
Proof using Type. destruct E; reflexivity. Qed.

Lemma proj_LR_left {L R} (o: option Type) {D} (E: Some D = o) (xl: L) (xd: D) (xr: R) :
  match o as o0 return (match o0 with Some d => (L*d*R)%type | None => (L*R)%type end -> L) with
  | Some _ => fun m => fst (fst m) | None => fun m => fst m end
    (eq_rect (Some D) (fun o0 => match o0 with Some d => (L*d*R)%type | None => (L*R)%type end)
       (xl, xd, xr) o E) = xl.
Proof using Type. destruct E; reflexivity. Qed.

Lemma proj_LR_right {L R} (o: option Type) {D} (E: Some D = o) (xl: L) (xd: D) (xr: R) :
  match o as o0 return (match o0 with Some d => (L*d*R)%type | None => (L*R)%type end -> R) with
  | Some _ => fun m => snd m | None => fun m => snd m end
    (eq_rect (Some D) (fun o0 => match o0 with Some d => (L*d*R)%type | None => (L*R)%type end)
       (xl, xd, xr) o E) = xr.
Proof using Type. destruct E; reflexivity. Qed.

Lemma cast_node_pirr {A: EqDec.type}
  {denote: A -> option Type} {a a0:A} (E E': Some a = Some a0)
  (x y: match denote a with Some d => d | None => unit end) (EQxy: x = y) :
  cast_node (denote:=denote) E x = cast_node (denote:=denote) E' y.
Proof using Type. subst y. rewrite (UIP_dec (ReflectExt.sumbool_of_reflect Algebra.eqb_spec) E E'). reflexivity. Qed.

Lemma denote_tree_lookup'_tot_set'_other {A: EqDec.type}
  {denote: A -> option Type} {a a_d} (DEN: denote a = Some a_d) (d: a_d) :
  forall (m: Maps.PTree.tree' A) (k1 k2: positive) (NEQ: k1 <> k2)
         (m_d: denote_tree' denote m) {a2}
         (G : Maps.PTree.get' k2 (Maps.PTree.set' k1 a m) = Some a2)
         (G': Maps.PTree.get' k2 m = Some a2),
  denote_tree_lookup'_tot k2 G  (denote_tree_set' k1 DEN d m_d)
  = denote_tree_lookup'_tot k2 G' m_d.
Proof using Type.
  induction m as [r IHr | a' | a' r IHr | l IHl | l IHl r IHr | l IHl a' | l IHl a' r IHr];
    intros k1 k2 NEQ m_d a2 G G';
    destruct k1 as [q1|q1|]; destruct k2 as [q2|q2|];
    cbn [denote_tree_set' denote_tree_lookup'_tot Maps.PTree.set' Maps.PTree.set0 Maps.PTree.get'] in *;
    try discriminate G; try discriminate G'; try (exfalso; congruence).
  all: try (apply IHr; congruence).
  all: try (apply IHl; congruence).
  all: try (cbn [snd fst]; erewrite denote_tree_lookup'_tot_pirr; reflexivity).
  all: try (exfalso; rewrite Maps.PTree.gso0 in G  by congruence; discriminate).
  all: try (exfalso; rewrite Maps.PTree.gso0 in G' by congruence; discriminate).
  all: try (rewrite proj_snd_eq_rect; erewrite denote_tree_lookup'_tot_pirr; reflexivity).
  all: try (rewrite proj_fst_eq_rect; erewrite denote_tree_lookup'_tot_pirr; reflexivity).
  all: try (rewrite proj_LR_left;  erewrite denote_tree_lookup'_tot_pirr; reflexivity).
  all: try (rewrite proj_LR_right; erewrite denote_tree_lookup'_tot_pirr; reflexivity).
  all: try (apply cast_node_pirr).
  all: cbn [denote_tree'] in m_d.
  all: revert m_d; destruct (denote a') as [d'|]; intros m_d.
  all: cbn [denote_tree_set' denote_tree_lookup'_tot fst snd] in *.
  all: first
    [ reflexivity
    | (destruct m_d; reflexivity)
    | erewrite denote_tree_lookup'_tot_pirr; reflexivity
    | apply denote_tree_lookup'_tot_set0
    | solve [exfalso; (discriminate G || discriminate G'
             || (rewrite Maps.PTree.gso0 in G by congruence; discriminate)
             || (rewrite Maps.PTree.gso0 in G' by congruence; discriminate))]
    | multimatch goal with H : forall k1 k2 : positive, _ |- _ => apply H; congruence end ].
Qed.

Lemma denote_tree_lookup_set_other {A: EqDec.type}
  {denote: A -> option Type} {a a_d} (DEN: denote a = Some a_d) (d: a_d) :
  forall (m: Maps.PTree.t A) (k1 k2: positive) (NEQ: k1 <> k2)
         (m_d: denote_tree denote m) {a2 a2_d} (DEN2: denote a2 = Some a2_d)
         (G : Maps.PTree.get k2 (Maps.PTree.set k1 a m) = Some a2)
         (G': Maps.PTree.get k2 m = Some a2),
  denote_tree_lookup G DEN2 (denote_tree_set k1 DEN d m_d)
  = denote_tree_lookup G' DEN2 m_d.
Proof using Type.
  intros m k1 k2 NEQ m_d a2 a2_d DEN2 G G'.
  destruct m as [|m'].
  - discriminate G'.
  - change (Maps.PTree.set k1 a (Maps.PTree.Nodes m'))
      with (Maps.PTree.Nodes (Maps.PTree.set' k1 a m')) in *.
    cbn [denote_tree_set]; unfold denote_tree_lookup; cbn beta iota.
    rewrite denote_tree_lookup'_tot_eq, denote_tree_lookup'_tot_eq.
    f_equal.
    exact (denote_tree_lookup'_tot_set'_other DEN d m' k1 k2 NEQ m_d G G').
Qed.

Lemma proj_snd_eq_rect_none {R} (o: option Type) (E: None = o) (xr: R) :
  match o as o0 return (match o0 with Some d => (d*R)%type | None => R end -> R) with
  | Some _ => fun m => snd m | None => fun m => m end
    (eq_rect None (fun o0 => match o0 with Some d => (d*R)%type | None => R end)
       xr o E) = xr.
Proof using Type. destruct E; reflexivity. Qed.

Lemma proj_fst_eq_rect_none {L} (o: option Type) (E: None = o) (xl: L) :
  match o as o0 return (match o0 with Some d => (L*d)%type | None => L end -> L) with
  | Some _ => fun m => fst m | None => fun m => m end
    (eq_rect None (fun o0 => match o0 with Some d => (L*d)%type | None => L end)
       xl o E) = xl.
Proof using Type. destruct E; reflexivity. Qed.

Lemma proj_LR_left_none {L R} (o: option Type) (E: None = o) (xl: L) (xr: R) :
  match o as o0 return (match o0 with Some d => L*d*R | None => L*R end -> L) with
  | Some _ => fun m => fst (fst m) | None => fun m => fst m end
    (eq_rect None (fun o0 => match o0 with Some d => (L*d*R)%type | None => (L*R)%type end)
       (xl, xr) o E) = xl.
Proof using Type. destruct E; reflexivity. Qed.

Lemma proj_LR_right_none {L R} (o: option Type) (E: None = o) (xl: L) (xr: R) :
  match o as o0 return (match o0 with Some d => L*d*R | None => L*R end -> R) with
  | Some _ => fun m => snd m | None => fun m => snd m end
    (eq_rect None (fun o0 => match o0 with Some d => (L*d*R)%type | None => (L*R)%type end)
       (xl, xr) o E) = xr.
Proof using Type. destruct E; reflexivity. Qed.

Lemma denote_tree_lookup'_tot_unset0 {A: EqDec.type}
  {denote: A -> option Type} {a} (DEN: denote a = None) :
  forall (k: positive) (GET: Maps.PTree.get' k (Maps.PTree.set0 k a) = Some a),
  denote_tree_lookup'_tot k GET (denote_tree_unset0 k DEN)
  = eq_rect None (fun o => match o with Some x => x | None => unit end)
      tt (denote a) (eq_sym DEN).
Proof using Type.
  induction k as [q IH | q IH | ]; intro GET;
    cbn [denote_tree_unset0 denote_tree_lookup'_tot].
  - apply IH.
  - apply IH.
  - apply cast_node_same.
Qed.

Lemma denote_tree_lookup'_tot_unset'_other {A: EqDec.type}
  {denote: A -> option Type} {a} (DEN: denote a = None) :
  forall (m: Maps.PTree.tree' A) (k1 k2: positive) (NEQ: k1 <> k2)
         (m_d: denote_tree' denote m) {a2}
         (G : Maps.PTree.get' k2 (Maps.PTree.set' k1 a m) = Some a2)
         (G': Maps.PTree.get' k2 m = Some a2),
  denote_tree_lookup'_tot k2 G  (denote_tree_unset' k1 DEN m_d)
  = denote_tree_lookup'_tot k2 G' m_d.
Proof using Type.
  induction m as [r IHr | a' | a' r IHr | l IHl | l IHl r IHr | l IHl a' | l IHl a' r IHr];
    intros k1 k2 NEQ m_d a2 G G';
    destruct k1 as [q1|q1|]; destruct k2 as [q2|q2|];
    cbn [denote_tree_unset' denote_tree_lookup'_tot Maps.PTree.set' Maps.PTree.set0 Maps.PTree.get'] in *;
    try discriminate G; try discriminate G'; try (exfalso; congruence).
  all: try (apply IHr; congruence).
  all: try (apply IHl; congruence).
  all: try (cbn [snd fst]; erewrite denote_tree_lookup'_tot_pirr; reflexivity).
  all: try (exfalso; rewrite Maps.PTree.gso0 in G  by congruence; discriminate).
  all: try (exfalso; rewrite Maps.PTree.gso0 in G' by congruence; discriminate).
  all: try (rewrite proj_snd_eq_rect_none; erewrite denote_tree_lookup'_tot_pirr; reflexivity).
  all: try (rewrite proj_fst_eq_rect_none; erewrite denote_tree_lookup'_tot_pirr; reflexivity).
  all: try (rewrite proj_LR_left_none;  erewrite denote_tree_lookup'_tot_pirr; reflexivity).
  all: try (rewrite proj_LR_right_none; erewrite denote_tree_lookup'_tot_pirr; reflexivity).
  all: try (apply cast_node_pirr).
  all: cbn [denote_tree'] in m_d.
  all: revert m_d; destruct (denote a') as [d'|]; intros m_d.
  all: cbn [denote_tree_unset' denote_tree_lookup'_tot fst snd] in *.
  all: first
    [ reflexivity
    | (destruct m_d; reflexivity)
    | erewrite denote_tree_lookup'_tot_pirr; reflexivity
    | apply denote_tree_lookup'_tot_unset0
    | solve [exfalso; (discriminate G || discriminate G'
             || (rewrite Maps.PTree.gso0 in G by congruence; discriminate)
             || (rewrite Maps.PTree.gso0 in G' by congruence; discriminate))]
    | multimatch goal with H : forall k1 k2 : positive, _ |- _ => apply H; congruence end ].
Qed.

Lemma denote_tree_lookup_unset_other {A: EqDec.type}
  {denote: A -> option Type} {a} (DEN: denote a = None) :
  forall (m: Maps.PTree.t A) (k1 k2: positive) (NEQ: k1 <> k2)
         (m_d: denote_tree denote m) {a2 a2_d} (DEN2: denote a2 = Some a2_d)
         (G : Maps.PTree.get k2 (Maps.PTree.set k1 a m) = Some a2)
         (G': Maps.PTree.get k2 m = Some a2),
  denote_tree_lookup G DEN2 (denote_tree_unset k1 DEN m_d)
  = denote_tree_lookup G' DEN2 m_d.
Proof using Type.
  intros m k1 k2 NEQ m_d a2 a2_d DEN2 G G'.
  destruct m as [|m'].
  - discriminate G'.
  - change (Maps.PTree.set k1 a (Maps.PTree.Nodes m'))
      with (Maps.PTree.Nodes (Maps.PTree.set' k1 a m')) in *.
    cbn [denote_tree_unset]; unfold denote_tree_lookup; cbn beta iota.
    rewrite denote_tree_lookup'_tot_eq, denote_tree_lookup'_tot_eq.
    f_equal.
    exact (denote_tree_lookup'_tot_unset'_other DEN m' k1 k2 NEQ m_d G G').
Qed.

Local Notation denote_pure_ctxt ctx := (denote_tree denote_binding ctx.(ctxt_pure)).

Local Notation denote_stack_ctxt ctx := (denote_stack denote_local ctx.(ctxt_stack)).

Local Notation denote_glob_ctxt ctx := (denote_tree denote_globdef ctx.(ctxt_global).(Globalenvs.Genv.genv_defs)).

Section Ctxt.

  Definition denote_ctxt (ctx: ctxt (type * bool) (type * bool) unit fundef vardef): Type :=
    (denote_pure_ctxt ctx * denote_stack_ctxt ctx * denote_glob_ctxt ctx)%type.

End Ctxt.

Section Cmd.

  Fixpoint denote_expr
    [ctx: Maps.PTree.t (type * bool)] [e: expr] [t: type]
    (WT: type_expr ctx e = Some t)
    (env: denote_tree denote_binding ctx)
    {struct e}: denote_type t.
  Proof.
    destruct e as [var_id | | b | n | ofst | | e1 | e1 e2 | e1 e2 | e1 e2].
    - cbn in WT.
      destruct (Maps.PTree.get var_id ctx) as [[t' [|]]|] eqn:GET;
        try destruct t'; try discriminate;
        injection WT as <-;
        exact (denote_tree_lookup GET (denote_binding_eq _) env).
    - destruct t; first [ exact tt | discriminate ].
    - destruct t; first [ exact b | discriminate ].
    - cbn in WT.
      destruct (Z.of_nat n <=? _)%Z; [ destruct t | ]; first [ exact n | discriminate ].
    - cbn in WT.
      destruct (_ <=? _)%Z; [ destruct t | ]; first [ exact ofst | discriminate ].
    - destruct t; first [ exact (null: @ptr_t Sm) | discriminate ].
    - cbn in WT.
      destruct (type_expr ctx e1) as [t_e|] eqn:TYPe; try discriminate WT.
      destruct t_e; try discriminate WT.
      injection WT as <-.
      exact (negb (denote_expr ctx _ _ TYPe env)).
    - cbn in WT.
      destruct (type_expr ctx e1) as [t_l|] eqn:TYPl; try discriminate WT.
      destruct t_l; try discriminate WT.
      destruct (type_expr ctx e2) as [t_r|] eqn:TYPr; try discriminate WT.
      destruct t_r; try discriminate WT.
      injection WT as <-.
      exact (denote_expr _ _ _ TYPl env + denote_expr _ _ _ TYPr env)%int.
    - cbn in WT.
      destruct (type_expr ctx e1) as [t_l|] eqn:TYPl; try discriminate WT.
      destruct t_l; try discriminate WT.
      destruct (type_expr ctx e2) as [t_r|] eqn:TYPr; try discriminate WT.
      destruct t_r; try discriminate WT.
      injection WT as <-.
      exact (denote_expr _ _ _ TYPl env * denote_expr _ _ _ TYPr env)%int.
    - cbn in WT.
      destruct (type_expr ctx e1) as [t_l|] eqn:TYPl; try discriminate WT.
      destruct t_l; try discriminate WT.
      destruct (type_expr ctx e2) as [t_r|] eqn:TYPr; try discriminate WT.
      destruct t_r; try discriminate WT.
      injection WT as <-.
      exact (denote_expr _ _ _ TYPl env =? denote_expr _ _ _ TYPr env)%int.
  Defined.

  Fixpoint denote_app
    {ctxt: ctxt (type * bool) (type * bool) unit fundef vardef}
    {params: list type} {ret: type} {args: list expr}
    (d_fn: denote_sig' params ret)
    (env: denote_pure_ctxt ctxt)
    (WTargs: ListExt.forall2b_opt eqb (type_expr ctxt.(ctxt_pure)) args params = true)
    {struct args}
    : Monad.program Sm (denote_type ret).
  Proof.
    destruct args as [| a args'].
    - destruct params as [| t params']; [ exact d_fn | discriminate WTargs ].
    - destruct params as [| t params']; [ discriminate WTargs | cbn in WTargs ].
      destruct (type_expr ctxt.(ctxt_pure) a) as [t'|] eqn:TYPa; [ | discriminate WTargs ].
      destruct (type_eqb t' t) eqn:EQ; [ | discriminate WTargs ].
      refine (denote_app ctxt params' ret args' (d_fn (denote_expr (e := a) (t := t) _ env)) env WTargs).
      destruct t', t; first [ discriminate EQ | exact TYPa ].
  Defined.

  Definition denote_app_exf
    {ctx: ctxt (type * bool) (type * bool) unit fundef vardef}
    {f_id} {args: list expr} {ef} {sig}
    (FINDfn: get_global f_id ctx = Some (AST.Gfun (AST.External ef)))
    (SIG: Facts.ef_sig_dec ef = Some sig)
    (WTargs: ListExt.forall2b_opt eqb (type_expr ctx.(ctxt_pure)) args sig.(sig_args) = true)
    (env: denote_ctxt ctx)
    : Monad.program Sm (denote_type sig.(sig_res)).
    refine (denote_app _ (fst (fst env)) WTargs).
    refine (match Globalenvs.Genv.find_symbol ctx.(ctxt_global) f_id as symb
                  return (match symb with
                          | Some b => Globalenvs.Genv.find_def ctx.(ctxt_global) b
                          | None => None
                          end = Some (AST.Gfun (AST.External ef))) ->
                         denote_sig sig
            with
            | Some _ => _
            | None => ltac:(discriminate)
            end FINDfn).
    intros GET'.
    refine (denote_tree_lookup GET' _ (snd env)).
    refine (eq_rect _
             (fun o => match o with
                       | Some s => Some (denote_sig s)
                       | None => Some (unit: Type)
                       end = Some (denote_sig sig))
             _ _ (eq_sym SIG)).
    reflexivity.
  Defined.

  Fixpoint denote_cmd
    [ctxt] [c : cmd] [t : type]
    (WT : type_cmd ctxt c = Some t)
    (env: denote_ctxt ctxt)
    {struct c}:
    Monad.program Sm (denote_type t).
  Proof.
    destruct c as
      [ e
      | id_b t_b c_b c_c
      | e_if c_then c_else
      | c_cond c_body
      | t_v e_v c_c
      | o_v t_v
      | o_v t_v e_v
      | e_size t_init e_init
      | e_ptr t_val
      | e_ptr t_val e_val
      | e_ptr
      | e_ptr e_ofst
      | e_ptr e_ofst
      | e_ptr_l e_ptr_r
      | f_id args
      | e_l e_r
      | e_l e_r
      ].
    - exact (ret (denote_expr WT (fst (fst env)))).
    - cbn [type_cmd] in WT.
      destruct (get_pure id_b ctxt) as [ [ t' [ | ] ] | ] eqn:GET; [ discriminate WT | | discriminate WT ].
      destruct (eqb t_b t') eqn:EQ1; [ | discriminate WT ].
      destruct (type_cmd ctxt c_b) as [t0|] eqn:WTc1; [ | discriminate WT ].
      destruct (eqb t_b t0) eqn:EQ2; [ | discriminate WT ].
      destruct (type_cmd (set_pure id_b (t_b, true) ctxt) c_c) as [t1|] eqn:WTc2; [ | discriminate WT ].
      injection WT as <-.
      refine (do v <- denote_cmd ctxt c_b t0 WTc1 env;
              denote_cmd (set_pure id_b (t_b, true) ctxt) c_c t1 WTc2
                (denote_tree_set id_b (denote_binding_eq t_b) _ (fst (fst env)), snd (fst env), snd env)).
      destruct t_b, t0; first [ discriminate EQ2 | exact v ].
    - cbn [type_cmd] in WT.
      destruct (type_expr ctxt.(ctxt_pure) e_if) as [ [ | | | | ] | ] eqn:TYPcond; try discriminate WT.
      destruct (type_cmd ctxt c_then) as [t_t|] eqn:WTthen; [ | discriminate WT ].
      destruct (type_cmd ctxt c_else) as [t_e|] eqn:WTelse; [ | discriminate WT ].
      destruct (eqb t_t t_e) eqn:EQ; [ | discriminate WT ].
      injection WT as <-.
      refine (if denote_expr TYPcond (fst (fst env))
              then denote_cmd ctxt c_then t_t WTthen env
              else _).
      destruct t_t, t_e; first [ discriminate EQ | exact (denote_cmd ctxt c_else _ WTelse env) ].
    - cbn [type_cmd] in WT.
      destruct (type_cmd ctxt c_cond) as [ [ | | | | ] | ] eqn:WTcond; try discriminate WT.
      destruct (type_cmd ctxt c_body) as [ [ | | | | ] | ] eqn:WTbody; try discriminate WT.
      injection WT as <-.
      exact (while (denote_cmd ctxt c_cond t_bool WTcond env)
                   (denote_cmd ctxt c_body t_unit WTbody env)).
    - cbn [type_cmd] in WT.
      destruct (type_expr ctxt.(ctxt_pure) e_v) as [t_v'|] eqn:TYPinit; [ | discriminate WT ].
      destruct (type_cmd (push_stack tt ctxt) c_c) as [t_c|] eqn:WTc; [ | discriminate WT ].
      destruct (eqb t_v t_v') eqn:EQ; [ | discriminate WT ].
      injection WT as <-.
      refine (with_var (So := denote_type_memval t_v)
                (convert_eq (denote_types_agree t_v)
                   (denote_expr (e := e_v) (t := t_v) _ (fst (fst env))))
                (fun x => denote_cmd (push_stack tt ctxt) c_c t_c WTc
                            (fst (fst env), denote_stack_push (snd (fst env)) eq_refl x, snd env))).
      destruct t_v, t_v'; first [ discriminate EQ | exact TYPinit ].
    - cbn [type_cmd] in WT.
      destruct (get_stack o_v ctxt) as [ [] | ] eqn:NTH; [ | discriminate WT ].
      injection WT as <-.
      exact (convert_eq
               (eq_sym (f_equal (Monad.program Sm) (denote_types_agree t_v)))
               (read_var (So := denote_type_memval t_v)
                  (denote_stack_lookup NTH eq_refl (snd (fst env))))).
    - cbn [type_cmd] in WT.
      destruct (type_expr ctxt.(ctxt_pure) e_v) as [t'|] eqn:TYPval; [ | discriminate WT ].
      destruct (get_stack o_v ctxt) as [ [] | ] eqn:NTH; [ | discriminate WT ].
      destruct (eqb t_v t') eqn:EQ; [ | discriminate WT ].
      injection WT as <-.
      refine (write_var (So := denote_type_memval t_v)
                (denote_stack_lookup NTH eq_refl (snd (fst env)))
                (convert_eq (denote_types_agree t_v)
                   (denote_expr (e := e_v) (t := t_v) _ (fst (fst env))))).
      destruct t_v, t'; first [ discriminate EQ | exact TYPval ].
    - cbn [type_cmd] in WT.
      destruct (find_exf_genv AST.EF_malloc ctxt) as [ id_m | ] eqn:SRCH;
        [ | discriminate WT ].
      destruct (type_expr ctxt.(ctxt_pure) e_size) as [ [ | | | | ] | ] eqn:TYPsize; try discriminate WT.
      destruct (type_expr ctxt.(ctxt_pure) e_init) as [t'|] eqn:TYPinit; [ | discriminate WT ].
      destruct (eqb t_init t') eqn:EQ; [ | discriminate WT ].
      injection WT as <-.
      refine (alloc_ptr (So := denote_type_memval t_init)
                (denote_expr TYPsize (fst (fst env)))
                (convert_eq (denote_types_agree t_init)
                   (denote_expr (e := e_init) (t := t_init) _ (fst (fst env))))).
      destruct t_init, t'; first [ discriminate EQ | exact TYPinit ].
    - cbn [type_cmd] in WT.
      destruct (type_expr ctxt.(ctxt_pure) e_ptr) as [ [ | | | | ] | ] eqn:TYPptr; try discriminate WT.
      injection WT as <-.
      exact (convert_eq
               (eq_sym (f_equal (Monad.program Sm) (denote_types_agree t_val)))
               (read_ptr (So := denote_type_memval t_val) (denote_expr TYPptr (fst (fst env))))).
    - cbn [type_cmd] in WT.
      destruct (type_expr ctxt.(ctxt_pure) e_ptr) as [ [ | | | | ] | ] eqn:TYPptr; try discriminate WT.
      destruct (type_expr ctxt.(ctxt_pure) e_val) as [t'|] eqn:TYPval; [ | discriminate WT ].
      destruct (eqb t_val t') eqn:EQ; [ | discriminate WT ].
      injection WT as <-.
      refine (write_ptr (So := denote_type_memval t_val)
                (denote_expr TYPptr (fst (fst env)))
                (convert_eq (denote_types_agree t_val)
                   (denote_expr (e := e_val) (t := t_val) _ (fst (fst env))))).
      destruct t_val, t'; first [ discriminate EQ | exact TYPval ].
    - cbn [type_cmd] in WT.
      destruct (find_exf_genv AST.EF_free ctxt) as [ id_f | ] eqn:SRCH;
        [ | discriminate WT ].
      destruct (type_expr ctxt.(ctxt_pure) e_ptr) as [ [ | | | | ] | ] eqn:TYPptr; try discriminate WT.
      injection WT as <-.
      exact (free_ptr (denote_expr TYPptr (fst (fst env)))).
    - cbn [type_cmd] in WT.
      destruct (type_expr ctxt.(ctxt_pure) e_ptr) as [ [ | | | | ] | ] eqn:TYPptr; try discriminate WT.
      destruct (type_expr ctxt.(ctxt_pure) e_ofst) as [ [ | | | | ] | ] eqn:TYPofst; try discriminate WT.
      injection WT as <-.
      exact (shift_fw_ptr (denote_expr TYPptr (fst (fst env))) (denote_expr TYPofst (fst (fst env)))).
    - cbn [type_cmd] in WT.
      destruct (type_expr ctxt.(ctxt_pure) e_ptr) as [ [ | | | | ] | ] eqn:TYPptr; try discriminate WT.
      destruct (type_expr ctxt.(ctxt_pure) e_ofst) as [ [ | | | | ] | ] eqn:TYPofst; try discriminate WT.
      injection WT as <-.
      exact (shift_bw_ptr (denote_expr TYPptr (fst (fst env))) (denote_expr TYPofst (fst (fst env)))).
    - cbn [type_cmd] in WT.
      destruct (type_expr ctxt.(ctxt_pure) e_ptr_l) as [ [ | | | | ] | ] eqn:TYPl; try discriminate WT.
      destruct (type_expr ctxt.(ctxt_pure) e_ptr_r) as [ [ | | | | ] | ] eqn:TYPr; try discriminate WT.
      injection WT as <-.
      exact (eq_ptr (denote_expr TYPl (fst (fst env))) (denote_expr TYPr (fst (fst env)))).
    - cbn [type_cmd] in WT.
      destruct (get_global f_id ctxt) as [ [ [ fn | ef ] | gv ] | ] eqn:FIND;
        [ | | discriminate WT | discriminate WT ].
      + destruct (ListExt.map_opt (type_expr ctxt.(ctxt_pure)) args) as [t_args|] eqn:MAP; [ | discriminate WT ].
        destruct (ListExt.forall2b eqb t_args (List.map snd fn.(fn_params))) eqn:F2; [ | discriminate WT ].
        injection WT as <-.
        exact (denote_app
                 (match Globalenvs.Genv.find_symbol (ctxt_global ctxt) f_id as fs
                         return (match fs with
                                 | Some b => Globalenvs.Genv.find_def (ctxt_global ctxt) b
                                 | None => None
                                 end = Some (AST.Gfun (AST.Internal fn))) ->
                                (denote_fn_sig fn)
                   with
                   | Some _ => fun GET' => denote_tree_lookup GET' eq_refl (snd env)
                   | None => fun GET' =>
                               False_rect _
                                 (eq_rect None
                                    (fun o => match o with Some _ => False | None => True end)
                                    I
                                    (Some (AST.Gfun (AST.Internal fn)))
                                    GET')
                   end FIND)
                 (fst (fst env))
                 (eq_trans (ListExt.forall2b_opt_map_opt _ _ _ _ _ MAP) F2)).
      + destruct ef as [ nm sg | | | | | | | | | | | ]; try discriminate WT.
        destruct (ListExt.map_opt (type_expr ctxt.(ctxt_pure)) args) as [t_args|] eqn:MAP; [ | discriminate WT ].
        destruct (Facts.ef_sig_dec (AST.EF_external nm sg)) as [sig|] eqn:DEC; [ | discriminate WT ].
        destruct (ListExt.forall2b eqb t_args sig.(sig_args)) eqn:F2; [ | discriminate WT ].
        injection WT as <-.
        exact (denote_app_exf FIND DEC
                 (eq_trans (ListExt.forall2b_opt_map_opt _ _ _ _ _ MAP) F2) env).
    - cbn [type_cmd] in WT.
      destruct (type_expr ctxt.(ctxt_pure) e_l) as [t_l|] eqn:TYPl; [ | discriminate WT ].
      destruct t_l; try discriminate WT.
      destruct (type_expr ctxt.(ctxt_pure) e_r) as [t_r|] eqn:TYPr; [ | discriminate WT ].
      destruct t_r; try discriminate WT.
      injection WT as <-.
      exact (Unsigned.div (denote_expr TYPl (fst (fst env)))
               (denote_expr TYPr (fst (fst env)))).
    - cbn [type_cmd] in WT.
      destruct (type_expr ctxt.(ctxt_pure) e_l) as [t_l|] eqn:TYPl; [ | discriminate WT ].
      destruct t_l; try discriminate WT.
      destruct (type_expr ctxt.(ctxt_pure) e_r) as [t_r|] eqn:TYPr; [ | discriminate WT ].
      destruct t_r; try discriminate WT.
      injection WT as <-.
      exact (Unsigned.mdl (denote_expr TYPl (fst (fst env)))
               (denote_expr TYPr (fst (fst env)))).
  Defined.

End Cmd.

Section OpSem.

  Context (exfs: exf_env).

  Fixpoint denote_cont
    [ctx] [k: @cont Sm] [t]
    (WT: OpSem.Typing.type_cont ctx k = Some t)
    (env: denote_pure_ctxt ctx)
    (stack: denote_stack_ctxt ctx)
    (glob: denote_glob_ctxt ctx)
    (v: denote_type t)
    {struct k}
    : Monad.program Sm nat
  with denote_cont_call
         [ctx] [k: @cont Sm] [t]
         (WT: OpSem.Typing.type_cont_call ctx k = Some t)
         (glob: denote_glob_ctxt ctx)
         (v: denote_type t)
         {struct k}
    : Monad.program Sm nat.
  Proof.
    - destruct k as [ | id c k' | c_cond c_body k' | c_cond c_body k' | f e locals k' | sx k' ];
        cbn [OpSem.Typing.type_cont] in WT.
      + destruct (ctxt_stack ctx) as [|s0 sl0] eqn:STK0; [ | discriminate WT ].
        injection WT as <-. exact (ret v).
      + destruct (get_pure id ctx) as [ [ t_b [ | ] ] | ] eqn:GETP; [ discriminate WT | | discriminate WT ].
        destruct (type_cmd (set_pure id (t_b, true) ctx) c) as [t_c|] eqn:WTc; [ | discriminate WT ].
        destruct (OpSem.Typing.type_cont ctx k') as [t_c'|] eqn:WTk; [ | discriminate WT ].
        destruct (type_eqb t_c t_c') eqn:EQ; [ | discriminate WT ].
        injection WT as <-.
        refine (do v' <- denote_cmd WTc
                           (denote_tree_set id (denote_binding_eq t_b) v env, stack, glob);
                   denote_cont _ _ _ WTk env stack glob _).
        destruct t_c, t_c'; first [ discriminate EQ | exact v' ].
      + destruct (type_cmd ctx c_cond) as [ [ | | | | ] | ] eqn:WTcond; try discriminate WT.
        destruct (type_cmd ctx c_body) as [ [ | | | | ] | ] eqn:WTbody; try discriminate WT.
        destruct (OpSem.Typing.type_cont ctx k') as [ [ | | | | ] | ] eqn:WTk; try discriminate WT.
        injection WT as <-.
        exact
          (if v
           then
             do _ <- denote_cmd WTbody (env, stack, glob);
                do _ <- while
                          (denote_cmd WTcond (env, stack, glob))
                          (denote_cmd WTbody (env, stack, glob));
                   denote_cont _ _ _ WTk env stack glob tt
           else denote_cont _ _ _ WTk env stack glob tt).
      + destruct (type_cmd ctx c_cond) as [ [ | | | | ] | ] eqn:WTcond; try discriminate WT.
        destruct (type_cmd ctx c_body) as [ [ | | | | ] | ] eqn:WTbody; try discriminate WT.
        destruct (OpSem.Typing.type_cont ctx k') as [ [ | | | | ] | ] eqn:WTk; try discriminate WT.
        injection WT as <-.
        exact
          (do _ <- while
                     (denote_cmd WTcond (env, stack, glob))
                     (denote_cmd WTbody (env, stack, glob));
              denote_cont _ _ _ WTk env stack glob tt).
      + destruct (ctxt_stack ctx) as [|s0 sl0] eqn:STK0; [ | discriminate WT ].
        destruct (type_function (to_glob_ctxt ctx) f) eqn:TF;
          [ | discriminate WT ].
        destruct (OpSem.Typing.type_env f e) as [ty_env|] eqn:TE; [ | discriminate WT ].
        exact (denote_cont _ _ _ WT
                 (denote_env TE)
                 (denote_locals locals) glob v).
      + destruct sx as [id | ].
        * destruct (get_pure id ctx) as [ [ t_b [ | ] ] | ] eqn:GETP; [ | discriminate WT | discriminate WT ].
          exact (denote_cont _ _ _ WT
                   (denote_tree_unset id (denote_binding_false_eq t_b) env) stack glob v).
        * destruct (ctxt_stack ctx) as [|s0 sl0] eqn:STK; [ discriminate WT | ].
          exact (do s <- get;
                 match pop (store s) with
                 | Some st =>
                     match mk_state_opt st (scnt s) (heap s) (alc s) with
                     | Some s' =>
                         put s';;
                         denote_cont _ _ _ WT env (denote_stack_removelast _ _ stack) glob v
                     | None => fail
                     end
                 | None => fail
                 end).
    - destruct k as [ | id c k' | c_cond c_body k' | c_cond c_body k' | f e locals k' | sx k' ];
        cbn [OpSem.Typing.type_cont_call'] in WT; try discriminate WT.
      + injection WT as <-. exact (ret v).
      + destruct (type_function ctx f) eqn:TF; [ | discriminate WT ].
        destruct (OpSem.Typing.type_env f e) as [ty_env|] eqn:TE; [ | discriminate WT ].
        exact (denote_cont _ _ _ WT
                 (denote_env TE)
                 (denote_locals locals) glob v).
  Defined.

  Fixpoint denote_stub (tl: list type) [tout: type] (r: Monad.program Sm (denote_type tout))
    : denote_sig' tl tout :=
    match tl with
    | [] => r
    | _ :: tl' => fun _ => denote_stub tl' r
    end.

  Definition denote_exf_body (ef: AST.external_function) (sig: signature)
    : denote_sig sig :=
    match ef with
    | AST.EF_external nm _ =>
        match exfs nm sig with
        | Some body => body
        | None => denote_stub sig.(sig_args) fail
        end
    | _ => denote_stub sig.(sig_args) fail
    end.

  Definition denote_external_function
    (ef: AST.external_function)
    (EQ: type_external_function ef = true)
    : match Facts.ef_sig_dec ef with
      | Some sig => denote_sig sig
      | None => Empty_set
      end :=
    match Facts.ef_sig_dec ef as o
          return (match o with Some _ => true | None => false end = true ->
                  match o with Some sig => denote_sig sig | None => Empty_set end)
    with
    | Some sig => fun _ => denote_exf_body ef sig
    | None => fun NONE => False_rect _ (Bool.diff_false_true NONE)
    end EQ.

  Definition denote_init_data_value
    (init: list AST.init_data) (t: type)
    (EQ: type_init_data init t = true) : denote_type t.
  Proof.
    destruct t.
    - exact tt.
    - destruct init as [|i1 init1]; [discriminate|].
      destruct i1; try discriminate.
      destruct init1 as [|i2 init2]; [discriminate|].
      destruct i2; try discriminate.
      destruct init2; [|discriminate].
      exact (Z.eqb (Integers.Int.unsigned i) 1%Z).
    - destruct init as [|i1 init1]; [discriminate|].
      destruct i1; try discriminate.
      destruct init1 as [|i2 init2]; [discriminate|].
      destruct i2; try discriminate.
      destruct init2; [|discriminate].
      exact (Z.to_nat (Integers.Int.unsigned i)).
    - discriminate.
    - destruct init as [|i1 init1]; [discriminate|].
      destruct i1; try discriminate;
        destruct init1; [exact (null: @ptr_t Sm) | discriminate |
                          exact (null: @ptr_t Sm) | discriminate].
  Defined.

  Fixpoint denote_function_curried
    [ctx: ctxt Empty_set Empty_set Empty_set fundef vardef]
    (internal: Maps.PTree.t (type * bool))
    (params_todo: list (AST.ident * type))
    (done_tree: Maps.PTree.t (type * bool))
    (body: cmd) (tout: type)
    (env: denote_tree denote_binding done_tree)
    (WTbody: type_cmd
               (with_internal internal
                  (with_pure (mk_typing_tree true params_todo done_tree)
                     (with_stack [] ctx)))
               body = Some tout)
    (glob: denote_glob_ctxt ctx)
    {struct params_todo}
    : denote_sig' (List.map snd params_todo) tout.
  Proof.
    destruct params_todo as [| [id t] rest].
    - exact (denote_cmd WTbody (env, tt, glob)).
    - intro x.
      exact (denote_function_curried ctx internal rest
               (Maps.PTree.set id (t, true) done_tree)
               body tout
               (denote_tree_set id (denote_binding_eq t) x env)
               WTbody
               glob).
  Defined.

  Definition denote_function
    [ctx: ctxt Empty_set Empty_set Empty_set fundef vardef] [fn: function]
    (WT: type_function ctx fn = true)
    (glob: denote_glob_ctxt ctx)
    : denote_fn_sig fn.
  Proof.
    unfold type_function, Prog.type_function in WT.
    destruct (type_cmd (mk_function_ctxt fn.(fn_params) fn.(fn_temps) fn.(fn_internals) ctx) fn.(fn_body))
      as [t'|] eqn:ETC; [ | discriminate WT ].
    destruct (type_eqb t' fn.(fn_return)) eqn:ERET; [ | discriminate WT ].
    refine (denote_function_curried (mk_typing_tree false fn.(fn_internals) Maps.PTree.Empty)
              fn.(fn_params)
              (mk_typing_tree false (fn.(fn_params) ++ fn.(fn_temps)) Maps.PTree.Empty)
              fn.(fn_body) fn.(fn_return)
              (denote_tree_uninit _ _)
              _
              glob).
    - intros p a GET. destruct a as [t b]. destruct b.
      + exfalso.
        refine (Facts.mk_typing_tree_false_not_true
                  (fn.(fn_params) ++ fn.(fn_temps)) Maps.PTree.Empty _ p t GET).
        intros id v TYv. rewrite Maps.PTree.gempty in TYv. discriminate.
      + destruct t; reflexivity.
    - destruct t', fn.(fn_return); first [ discriminate ERET | exact ETC | idtac ].
  Defined.

  Definition denote_globdef_value
    [ctx: ctxt Empty_set Empty_set Empty_set fundef vardef]
    [id: AST.ident] [gd: globdef]
    (H: type_globdef ctx id gd = true)
    (glob: denote_glob_ctxt ctx)
    : match denote_globdef gd with Some d => d | None => Empty_set end.
  Proof.
    destruct gd as [f | v]; cbn [denote_globdef].
    - destruct f as [fn | ef].
      + cbn in H.
        exact (denote_function H glob).
      + cbn in H.
        destruct (ExtFun.is_runtime ef) eqn:RT.
        * rewrite (Facts.is_runtime_ef_sig_dec_none ef RT).
          exact tt.
        * cbn [orb] in H.
          generalize (@denote_external_function ef H).
          destruct (Facts.ef_sig_dec ef); cbn; intros Dv; [ exact Dv | exact tt ].
    - cbn in H.
      destruct v as [[t] vinit vread vvol].
      unfold type_globvar, Prog.type_globvar in H.
      cbn in H.
      destruct (type_init_data vinit t) eqn:E; [ | discriminate ].
      refine (denote_init_data_value vinit t E).
  Defined.

  Definition genv_defs_add_global F V (ge: Globalenvs.Genv.t F V) idg:
    Globalenvs.Genv.genv_defs (Globalenvs.Genv.add_global ge idg) =
      Maps.PTree.set (Globalenvs.Genv.genv_next ge) (snd idg)
        (Globalenvs.Genv.genv_defs ge) := eq_refl.

  Definition denote_glob_ctxt_extend
    [ctx: ctxt Empty_set Empty_set Empty_set fundef vardef]
    [id: AST.ident] [gd: globdef]
    (H: type_globdef ctx id gd = true)
    (d_gd: match denote_globdef gd with Some d => d | None => Empty_set end)
    (glob: denote_tree denote_globdef
             (Globalenvs.Genv.genv_defs (ctxt_global ctx)))
    : denote_tree denote_globdef
        (Globalenvs.Genv.genv_defs (ctxt_global (add_global ctx (id, gd)))).
  Proof.
    unfold add_global; cbn [ctxt_global with_global].
    rewrite (genv_defs_add_global _ _ (ctxt_global ctx) (id, gd)); cbn [snd].
    destruct gd as [f | v].
    - destruct f as [fn | ef].
      + cbn in d_gd.
        exact (@denote_tree_set _ denote_globdef
                 (AST.Gfun (AST.Internal fn))
                 (denote_fn_sig fn)
                 (Globalenvs.Genv.genv_defs (ctxt_global ctx))
                 (Globalenvs.Genv.genv_next (ctxt_global ctx))
                 eq_refl d_gd glob).
      + cbn in H.
        unfold type_external_function in H.
        destruct (Facts.ef_sig_dec ef) as [sig|] eqn:E.
        * cbn in d_gd. rewrite E in d_gd. cbn in d_gd.
          refine (@denote_tree_set _ denote_globdef
                    (AST.Gfun (AST.External ef))
                    (denote_sig sig)
                    (Globalenvs.Genv.genv_defs (ctxt_global ctx))
                    (Globalenvs.Genv.genv_next (ctxt_global ctx))
                    _ d_gd glob).
          cbn. rewrite E. reflexivity.
        * refine (@denote_tree_set _ denote_globdef
                    (AST.Gfun (AST.External ef))
                    unit
                    (Globalenvs.Genv.genv_defs (ctxt_global ctx))
                    (Globalenvs.Genv.genv_next (ctxt_global ctx))
                    _ tt glob).
          cbn. rewrite E. reflexivity.
    - destruct v as [vinfo vinit vread vvol].
      destruct vinfo as [t]; cbn in *.
      exact (@denote_tree_set _ denote_globdef
               (AST.Gvar {| AST.gvar_info := {| var_type := t |};
                           AST.gvar_init := vinit;
                           AST.gvar_readonly := vread;
                           AST.gvar_volatile := vvol |})
               (denote_type t)
               (Globalenvs.Genv.genv_defs (ctxt_global ctx))
               (Globalenvs.Genv.genv_next (ctxt_global ctx))
               eq_refl d_gd glob).
  Defined.

  Fixpoint denote_prog_defs_fold
    (defs: list (AST.ident * globdef))
    (ctx: ctxt Empty_set Empty_set Empty_set fundef vardef)
    (H: type_prog_defs ctx defs = true)
    (glob: denote_tree denote_globdef
             (Globalenvs.Genv.genv_defs (ctxt_global ctx)))
    {struct defs}
    : denote_tree denote_globdef
        (Globalenvs.Genv.genv_defs
           (List.fold_left
              (@Globalenvs.Genv.add_global fundef vardef)
              defs (ctxt_global ctx))).
  Proof.
    destruct defs as [|[id gd] rest]; cbn.
    - exact glob.
    - unfold type_prog_defs, Prog.type_prog_defs in H; cbn in H.
      destruct (Prog.type_globdef _ _ ctx id gd) eqn:WTGD; [ | discriminate H ].
      cbn in H.
      pose (d_gd := denote_globdef_value WTGD glob).
      pose (glob1 := denote_glob_ctxt_extend WTGD d_gd glob).
      exact (denote_prog_defs_fold rest (add_global ctx (id, gd)) H glob1).
  Defined.

  Fixpoint denote_app_values
    (ts: list type) (to: type)
    (d_fn: denote_sig' ts to)
    (args: list (value (@ptr_t Sm))) {struct ts}
    : Monad.program Sm (denote_type to) :=
    match ts return denote_sig' ts to
                    -> Monad.program Sm (denote_type to) with
    | [] => fun d => match args with [] => d | _ => fail end
    | t :: ts' => fun d =>
                    match args with
                    | [] => fail
                    | a :: args' =>
                        match ReflectExt.sumbool_of_reflect type_eqb_spec (type_of_value a) t with
                        | left EQ =>
                            denote_app_values ts' to
                              (d (eq_rect _ denote_type (denote_value a) t EQ)) args'
                        | right _ => fail
                        end
                    end
    end d_fn.

  Definition denote_glob_ctxt_of_program
    (p: Prog.program) (WTp: type_program p = true)
    : denote_tree denote_globdef
        (Globalenvs.Genv.genv_defs (Globalenvs.Genv.globalenv p)).
  Proof.
    unfold type_program, Prog.type_program in WTp.
    destruct (Prog.type_prog_defs _ _ _ _) eqn:E1; [ | discriminate WTp ].
    exact (denote_prog_defs_fold p.(prog_defs)
                                 (ctxt_emp _ _ _ _ _ p.(prog_public)) E1 tt).
  Defined.

  Definition denote_fundef_call
    [gctx: ctxt Empty_set Empty_set Empty_set fundef vardef] [f: fundef] [sig: signature]
    (WTFD: type_fundef gctx f = true) (SIG: type_funsig f = Some sig)
    (glob: denote_glob_ctxt gctx) (args: list (value (@ptr_t Sm)))
    : Monad.program Sm (denote_type sig.(sig_res)).
  Proof.
    destruct f as [fn | ef]; cbn [type_funsig] in SIG.
    - injection SIG as <-.
      exact (denote_app_values (List.map snd fn.(fn_params)) fn.(fn_return)
               (denote_function WTFD glob) args).
    - assert (H: type_external_function ef = true)
        by (unfold type_external_function; rewrite SIG; reflexivity).
      refine (denote_app_values sig.(sig_args) sig.(sig_res) _ args).
      exact (eq_rect (Facts.ef_sig_dec ef)
               (fun o => match o with
                         | Some s0 => denote_sig s0
                         | None => Empty_set
                         end)
               (denote_external_function ef H) (Some sig) SIG).
  Defined.

  Definition denote_state
    [p: Prog.program] [s: @state Sm] [t: type]
    (WTp: type_program p = true) (WT: type_state p s = Some t)
    : Monad.program Sm nat.
  Proof.
    destruct s as [ f c k e locals s' | f args k s' | v k s' ];
      cbn [type_state] in WT.
    - destruct (type_function (mk_glob_ctxt p) f) eqn:WTFN; [| discriminate WT].
      destruct (OpSem.Typing.type_env f e) as [ty_env|] eqn:TENV; [| discriminate WT].
      set (ctx := OpSem.Typing.state_ctxt p f ty_env locals) in *.
      destruct (type_cmd ctx c) as [t_c|] eqn:WTCMD; [| discriminate WT].
      destruct (OpSem.Typing.type_cont ctx k) as [t_k|] eqn:WTCONT; [| discriminate WT].
      destruct (type_eqb t_c t_k) eqn:EQ; [| discriminate WT].
      pose (env_pure := denote_env TENV).
      pose (stack_d := denote_locals locals : denote_stack_ctxt ctx).
      pose (glob := denote_glob_ctxt_of_program p WTp : denote_glob_ctxt ctx).
      refine (do v <- denote_cmd WTCMD (env_pure, stack_d, glob);
                 denote_cont WTCONT env_pure stack_d glob _).
      refine (convert_eq (f_equal _ _)  v).
      refine (reflect_eq_of_true eqb_spec EQ).
    - destruct (type_funsig f) as [sig|] eqn:SIG; [| discriminate WT].
      destruct (type_fundef (mk_glob_ctxt p) f) eqn:WTFD; [| discriminate WT].
      destruct (type_call_args args sig.(sig_args)) eqn:WTARGS; [| discriminate WT].
      destruct (OpSem.Typing.type_cont_call (mk_glob_ctxt p) k) as [t_k|] eqn:WTCONT;
        [| discriminate WT].
      destruct (type_eqb t_k sig.(sig_res)) eqn:EQ; [| discriminate WT].
      pose (glob := denote_glob_ctxt_of_program p WTp
                    : denote_glob_ctxt (mk_glob_ctxt p)).
      refine (do v <- denote_fundef_call WTFD SIG glob args;
                denote_cont_call WTCONT glob _).
      exact (convert_eq (f_equal denote_type (eq_sym (reflect_eq_of_true eqb_spec EQ))) v).
    - destruct (OpSem.Typing.type_cont_call (mk_glob_ctxt p) k) as [t_k|] eqn:WTCONT;
        [| discriminate WT].
      destruct (type_eqb (type_of_value v) t_k) eqn:EQ; [| discriminate WT].
      pose (glob := denote_glob_ctxt_of_program p WTp
                    : denote_glob_ctxt (mk_glob_ctxt p)).
      exact (denote_cont_call WTCONT glob (denote_value_eq (reflect_eq_of_true eqb_spec EQ))).
  Defined.

End OpSem.

End Denotation.

Notation denote_sig Sm sig := (@denote_sig' Sm sig.(sig_args) sig.(sig_res)).

Notation denote_fn_sig Sm fn := (denote_sig Sm (fn_signature fn)).

Notation denote_pure_ctxt Sm ctx := (denote_tree (@denote_binding Sm) ctx.(ctxt_pure)).

Notation denote_stack_ctxt Sm ctx := (denote_stack (@denote_local Sm) ctx.(ctxt_stack)).

Notation denote_glob_ctxt Sm ctx :=
  (denote_tree (@denote_globdef Sm) ctx.(ctxt_global).(Globalenvs.Genv.genv_defs)).
