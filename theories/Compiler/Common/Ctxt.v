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

From compcert.common Require AST.
From compcert.common Require Import Globalenvs.
From compcert.lib Require Import Maps.

From GallinaC.Utils Require Import ListExt.
From GallinaC.Imp Require Store.
From GallinaC.Compiler.Common Require Import Types.

(* The context determines how variables are accessed
 * "pure" (i.e. those from bind/do) by name
 * "internal" (introduced to handle lower compilation stages) by name
 * global by name
 * stack variables (those from (read/write)_var inside a function are referenced by their offset in the stack: List.nth_error ctxt_stack n = Some a <-> the variable with offset n has value a in the context
 * Recall that offsets are in "memory words"
 * A typical convention is to have the type instantiated with [(_ * bool)]. Here, the boolean tracks whether the variable is already initialised or not
 *)
Record ctxt (P I S GF GV: Type): Type :=
  {
    ctxt_pure: Maps.PTree.t P;
    ctxt_internal: Maps.PTree.t I;
    ctxt_stack: list S;
    ctxt_global: Globalenvs.Genv.t GF GV;
  }.
Arguments ctxt_pure [P I S GF GV] c.
Arguments ctxt_internal [P I S GF GV] c.
Arguments ctxt_stack [P I S GF GV] c.
Arguments ctxt_global [P I S GF GV] c.

Definition ctxt_emp (P I S GF GV: Type) prog: ctxt P I S GF GV :=
  {|
    ctxt_pure := PTree.empty _;
    ctxt_internal := PTree.empty _;
    ctxt_stack := [];
    ctxt_global := Globalenvs.Genv.empty_genv _ _ prog;
  |}.
Definition with_pure [P I S GF GV P'] (pure: Maps.PTree.t P') (ctxt: ctxt P I S GF GV) :=
  {|
    ctxt_pure := pure;
    ctxt_internal := ctxt_internal ctxt;
    ctxt_global := ctxt_global ctxt;
    ctxt_stack := ctxt_stack ctxt;
  |}.
Definition with_internal [P I S GF GV I'] (internal: Maps.PTree.t I') (ctxt: ctxt P I S GF GV) :=
  {|
    ctxt_pure := ctxt_pure ctxt;
    ctxt_internal := internal;
    ctxt_global := ctxt_global ctxt;
    ctxt_stack := ctxt_stack ctxt;
  |}.
Definition with_global [P I S GF GV GF' GV'] (global: Globalenvs.Genv.t GF' GV') (ctxt: ctxt P I S GF GV) :=
  {|
    ctxt_pure := ctxt_pure ctxt;
    ctxt_internal := ctxt_internal ctxt;
    ctxt_global := global;
    ctxt_stack := ctxt_stack ctxt;
  |}.
Definition with_stack [P I S GF GV S'] (st: list S') (ctxt: ctxt P I S GF GV) :=
  {|
    ctxt_pure := ctxt_pure ctxt;
    ctxt_internal := ctxt_internal ctxt;
    ctxt_global := ctxt_global ctxt;
    ctxt_stack := st;
  |}.
Definition to_glob_ctxt [P I S GF GV] (c: ctxt P I S GF GV): ctxt Empty_set Empty_set Empty_set GF GV :=
  with_internal (PTree.empty _) (with_pure (PTree.empty _) (with_stack [] c)).
Definition from_pure [P I S GF GV: Type] (pure: Maps.PTree.t P): ctxt P I S GF GV := with_pure pure (ctxt_emp P I S GF GV []).
Definition get_pure [P I S GF GV] x (c: ctxt P I S GF GV): option P := PTree.get x (ctxt_pure c).
Definition set_pure [P I S GF GV] x y (c: ctxt P I S GF GV) :=
  {|
    ctxt_pure := PTree.set x y (ctxt_pure c);
    ctxt_internal := ctxt_internal c;
    ctxt_global := ctxt_global c;
    ctxt_stack := ctxt_stack c;
  |}.

Definition get_internal [P I S GF GV] x (c: ctxt P I S GF GV): option I :=
  PTree.get x (ctxt_internal c).
Definition set_internal [P I S GF GV] x y (c: ctxt P I S GF GV) :=
  {|
    ctxt_pure := ctxt_pure c;
    ctxt_internal := PTree.set x y (ctxt_internal c);
    ctxt_global := ctxt_global c;
    ctxt_stack := ctxt_stack c;
  |}.
Definition get_global [P I S GF GV] x (c: ctxt P I S GF GV): option _ :=
  match Globalenvs.Genv.find_symbol (ctxt_global c) x with
  | Some b => Globalenvs.Genv.find_def (ctxt_global c) b
  | None => None
  end.

Definition add_global [P I S GF GV]
  (ctx: ctxt P I S GF GV)
  (idg: AST.ident * AST.globdef GF GV)
  : ctxt P I S GF GV :=
  with_global (Globalenvs.Genv.add_global (ctxt_global ctx) idg) ctx.

Definition get_stack [P I S GF GV] n (c: ctxt P I S GF GV): option S := List.nth_error (ctxt_stack c) n.
Definition set_stack [P I S GF GV] n y (c: ctxt P I S GF GV) := with_stack (ListExt.replace_nth n (ctxt_stack c) y) c.
Definition push_stack [P I S GF GV] y (c: ctxt P I S GF GV) := with_stack ((ctxt_stack c)++[y]) c.

Module Facts.

  Lemma get_set_pure {P I S GF GV: Type} {ctx id_pure} {v_pure: P}: @get_pure P I S GF GV id_pure (set_pure id_pure v_pure ctx) = Some v_pure.
  Proof.
    unfold get_pure, set_pure.
    cbn.
    apply PTree.gss.
  Qed.

  Lemma set_pure_same [P I S GF GV: Type] (ctx: ctxt P I S GF GV) id (v w: P):
    set_pure id v (set_pure id w ctx) = set_pure id v ctx.
  Proof.
    unfold set_pure, with_pure; cbn.
    now rewrite Maps.PTree.set2.
  Qed.

  Lemma set_pure_comm [P I S GF GV: Type] (ctx: ctxt P I S GF GV) id1 id2 (v1 v2: P) (NE: id1 <> id2):
    set_pure id1 v1 (set_pure id2 v2 ctx)
    = set_pure id2 v2 (set_pure id1 v1 ctx).
  Proof.
    unfold set_pure, with_pure; cbn; f_equal.
    apply Maps.PTree.extensionality; intro j.
    rewrite ! Maps.PTree.gsspec.
    destruct (Coqlib.peq j id1); destruct (Coqlib.peq j id2); subst; congruence.
  Qed.

  Lemma with_pure_with_pure {P P1 P2 I S GF GV: Type} {ctx: ctxt P I S GF GV} {p1: Maps.PTree.t P1} {p2: Maps.PTree.t P2}: with_pure p2 (with_pure p1 ctx) = with_pure p2 ctx.
  Proof.
    reflexivity.
  Qed.

  Lemma set_internal_same [P I S GF GV: Type] [ctx: ctxt P I S GF GV] [id v]
    (GI: get_internal id ctx = Some v): set_internal id v ctx = ctx.
  Proof.
    unfold get_internal in GI.
    unfold set_internal; destruct ctx as [ pure internal stack global ]; cbn in GI |- *.
    now rewrite (PTree.gsident _ _ GI).
  Qed.

  Lemma get_set_internal {P I S GF GV: Type} {ctx: ctxt P I S GF GV} {id_int v_int}:
    get_internal id_int (set_internal id_int v_int ctx) = Some v_int.
  Proof.
    unfold get_internal, set_internal; cbn.
    now rewrite PTree.gss.
  Qed.

  Lemma get_internal_set_pure [P I S GF GV: Type] [ctx: ctxt P I S GF GV] [id id_p] (v_p: P):
    get_internal id (set_pure id_p v_p ctx) = get_internal id ctx.
  Proof.
    reflexivity.
  Qed.

  Lemma get_pure_set_internal {P I S GF GV: Type} {ctx: ctxt P I S GF GV} {id id_i v_i}:
    get_pure id (set_internal id_i v_i ctx) = get_pure id ctx.
  Proof.
    reflexivity.
  Qed.

  Lemma ctxt_internal_set_pure [P I S GF GV: Type] (ctx: ctxt P I S GF GV) id (v: P):
    ctxt_internal (set_pure id v ctx) = ctxt_internal ctx.
  Proof.
    reflexivity.
  Qed.

  Lemma ctxt_internal_with_stack [P I S S' GF GV: Type] (st: list S') (ctx: ctxt P I S GF GV):
    ctxt_internal (with_stack st ctx) = ctxt_internal ctx.
  Proof.
    reflexivity.
  Qed.

  Lemma get_global_with_pure [P P' I S GF GV: Type] (pure: Maps.PTree.t P') (ctx: ctxt P I S GF GV) id:
    get_global id (with_pure pure ctx) = get_global id ctx.
  Proof.
    reflexivity.
  Qed.

  Lemma get_global_with_stack [P I S S' GF GV: Type] (st: list S') (ctx: ctxt P I S GF GV) id:
    get_global id (with_stack st ctx) = get_global id ctx.
  Proof.
    reflexivity.
  Qed.

  Lemma get_global_set_pure [P I S GF GV: Type] (ctx: ctxt P I S GF GV) x (v: P) id:
    get_global id (set_pure x v ctx) = get_global id ctx.
  Proof.
    reflexivity.
  Qed.

  Lemma get_global_set_internal [P I S GF GV: Type] (ctx: ctxt P I S GF GV) x v id:
    get_global id (set_internal x v ctx) = get_global id ctx.
  Proof.
    reflexivity.
  Qed.

  Lemma get_global_with_internal [P I I' S GF GV: Type] (internal: Maps.PTree.t I') (ctx: ctxt P I S GF GV) id:
    get_global id (with_internal internal ctx) = get_global id ctx.
  Proof.
    reflexivity.
  Qed.

  Lemma get_global_add_global_neq [P I S GF GV] (ctx: ctxt P I S GF GV) idg id
    (NE: fst idg <> id):
    get_global id (add_global ctx idg) = get_global id ctx.
  Proof.
    destruct idg as [id' g]; cbn in NE.
    unfold get_global, add_global, with_global; cbn.
    unfold Globalenvs.Genv.find_symbol, Globalenvs.Genv.find_def, Globalenvs.Genv.add_global; cbn.
    rewrite PTree.gso by (intros ?; subst; congruence).
    destruct (PTree.get id (Globalenvs.Genv.genv_symb (ctxt_global ctx))) as [b|] eqn:SYMB;
      [| reflexivity ].
    rewrite PTree.gso; [ reflexivity |].
    apply Coqlib.Plt_ne.
    eapply (Globalenvs.Genv.genv_symb_range (ctxt_global ctx)); eassumption.
  Qed.

  Lemma get_global_add_global_eq [P I S GF GV] (ctx: ctxt P I S GF GV) id g:
    get_global id (add_global ctx (id, g)) = Some g.
  Proof.
    unfold get_global, add_global, with_global; cbn.
    unfold Globalenvs.Genv.find_symbol, Globalenvs.Genv.find_def, Globalenvs.Genv.add_global; cbn.
    rewrite PTree.gss, PTree.gss.
    reflexivity.
  Qed.

  Lemma ctxt_ext [P I S GF GV] (c1 c2: ctxt P I S GF GV):
    ctxt_pure c1 = ctxt_pure c2 ->
    ctxt_internal c1 = ctxt_internal c2 ->
    ctxt_stack c1 = ctxt_stack c2 ->
    ctxt_global c1 = ctxt_global c2 ->
    c1 = c2.
  Proof.
    now destruct c1, c2; cbn; intros -> -> -> ->.
  Qed.

  Lemma get_global_find_funct_ptr [P I S GF GV] [ctx: ctxt P I S GF GV] [id b f]
    (FIND_SYMB: Globalenvs.Genv.find_symbol (ctxt_global ctx) id = Some b)
    (FIND_FUNC: Globalenvs.Genv.find_funct_ptr (ctxt_global ctx) b = Some f):
    get_global id ctx = Some (AST.Gfun f).
  Proof.
    unfold get_global.
    rewrite FIND_SYMB.
    unfold Globalenvs.Genv.find_funct_ptr in FIND_FUNC.
    destruct (Globalenvs.Genv.find_def (ctxt_global ctx) b) as [ [ f' | v' ] | ];
      try discriminate FIND_FUNC.
    now injection FIND_FUNC as <-.
  Qed.

  Lemma get_global_find_funct_ptr_inv [P I S GF GV] [ctx: ctxt P I S GF GV]
    [ge: Globalenvs.Genv.t GF GV] [id b fd g]
    (EGLOB: ctxt_global ctx = ge)
    (FINDfn: get_global id ctx = Some (AST.Gfun g))
    (FINDsymb: Globalenvs.Genv.find_symbol ge id = Some b)
    (FINDfunct: Globalenvs.Genv.find_funct_ptr ge b = Some fd)
    : fd = g.
  Proof.
    unfold get_global in FINDfn.
    rewrite EGLOB, FINDsymb in FINDfn.
    apply Globalenvs.Genv.find_funct_ptr_iff in FINDfunct.
    rewrite FINDfunct in FINDfn.
    now injection FINDfn.
  Qed.

  Lemma get_global_ctxt_global_eq [P I S GF GV P' I' S']
    [c1: ctxt P I S GF GV] [c2: ctxt P' I' S' GF GV]
    (EQ: ctxt_global c1 = ctxt_global c2) id:
    get_global id c1 = get_global id c2.
  Proof.
    now unfold get_global; rewrite EQ.
  Qed.

  Lemma get_global_ctxt_emp (P I S GF GV: Type) pub id:
    get_global id (ctxt_emp P I S GF GV pub) = None.
  Proof.
    unfold get_global, ctxt_emp; cbn.
    unfold Globalenvs.Genv.find_symbol; cbn.
    now rewrite Maps.PTree.gempty.
  Qed.

End Facts.
