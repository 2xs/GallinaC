From compcert.common Require AST.
From compcert.common Require Import Globalenvs.
From compcert.lib Require Import Maps.

From GallinaC.Utils Require Import ListExt.
From GallinaC.Imp Require Store.
From GallinaC.Compiler.Common Require Import Types.

Definition map_ctxt := PTree.t.

(* The context determines how variables are accessed
 * "pure" (i.e. those from bind/do) and global are referenced by their name
 * stack variables (those from (read/write)_var inside a function are referenced by their offset in the stack: List.nth_error ctxt_stack n = Some a <-> the variable with offset n has value a in the context
 * Recall that offsets are in "memory words"
 * Since pure and stack variables may be initially unassigned, the boolean says if their assigned (true) or not (false)
 *)
Record ctxt (P S GF GV: Type): Type :=
  {
    ctxt_pure: map_ctxt P;
    ctxt_stack: list S;
    ctxt_global: Globalenvs.Genv.t GF GV;
  }.
Arguments ctxt_pure {P S GF GV} c.
Arguments ctxt_stack {P S GF GV} c.
Arguments ctxt_global {P S GF GV} c.

Definition ctxt_emp (P S GF GV: Type) prog: ctxt P S GF GV :=
  {|
    ctxt_pure := PTree.empty _;
    ctxt_stack := [];
    ctxt_global := Globalenvs.Genv.empty_genv _ _ prog;
  |}.
Definition with_pure {P S GF GV P'} (pure: map_ctxt P') (ctxt: ctxt P S GF GV) :=
  {|
    ctxt_pure := pure;
    ctxt_global := ctxt_global ctxt;
    ctxt_stack := ctxt_stack ctxt;
  |}.
Definition with_global {P S GF GV GF' GV'} (global: Globalenvs.Genv.t GF' GV') (ctxt: ctxt P S GF GV) :=
  {|
    ctxt_pure := ctxt_pure ctxt;
    ctxt_global := global;
    ctxt_stack := ctxt_stack ctxt;
  |}.
Definition with_stack {P S GF GV S'} (st: list S') (ctxt: ctxt P S GF GV) :=
  {|
    ctxt_pure := ctxt_pure ctxt;
    ctxt_global := ctxt_global ctxt;
    ctxt_stack := st;
  |}.
Definition from_pure {P S GF GV: Type} (pure: map_ctxt P): ctxt P S GF GV := with_pure pure (ctxt_emp P S GF GV []).
Definition get_pure {P S GF GV} x (c: ctxt P S GF GV): option P := PTree.get x (ctxt_pure c).
Definition set_pure {P S GF GV} x y (c: ctxt P S GF GV) := with_pure (PTree.set x y (ctxt_pure c)) c.
Definition get_global {P S GF GV} x (c: ctxt P S GF GV): option _ :=
  match Globalenvs.Genv.find_symbol (ctxt_global c) x with
  | Some b => Globalenvs.Genv.find_def (ctxt_global c) b
  | None => None
  end.

Definition add_global [P S GF GV]
  (ctx: ctxt P S GF GV)
  (idg: AST.ident * AST.globdef GF GV)
  : ctxt P S GF GV :=
  with_global (Globalenvs.Genv.add_global (ctxt_global ctx) idg) ctx.

(* Definition set_global {P S GF GV} x y (c: ctxt P S GF GV) := with_global (PTree.set x y (ctxt_global c)) c. *)
Definition get_stack {P S GF GV} n (c: ctxt P S GF GV): option S := List.nth_error (ctxt_stack c) n.
Definition set_stack {P S GF GV} n y (c: ctxt P S GF GV) := with_stack (ListExt.set_nth (ctxt_stack c) n y) c.
Definition push_stack {P S GF GV} y (c: ctxt P S GF GV) := with_stack ((ctxt_stack c)++[y]) c.

Coercion ctxt_pure: ctxt >-> map_ctxt.

Module Facts.

  Lemma get_set_pure {P S GF GV: Type} {ctx id_pure} {v_pure: P}: @get_pure P S GF GV id_pure (set_pure id_pure v_pure ctx) = Some v_pure.
  Proof.
    unfold get_pure, set_pure, with_pure.
    cbn.
    apply PTree.gss.
  Qed.

  Lemma with_pure_with_pure {P P1 P2 S GF GV: Type} {ctx: ctxt P S GF GV} {p1: map_ctxt P1} {p2: map_ctxt P2}: with_pure p2 (with_pure p1 ctx) = with_pure p2 ctx.
  Proof.
    reflexivity.
  Qed.

  Lemma get_global_with_pure {P P' S GF GV: Type} (pure: map_ctxt P') (ctx: ctxt P S GF GV) id:
    get_global id (with_pure pure ctx) = get_global id ctx.
  Proof.
    reflexivity.
  Qed.

  Lemma get_global_with_stack {P S S' GF GV: Type} (st: list S') (ctx: ctxt P S GF GV) id:
    get_global id (with_stack st ctx) = get_global id ctx.
  Proof.
    reflexivity.
  Qed.

  Lemma get_global_add_global_neq [P S GF GV] (ctx: ctxt P S GF GV) idg id
    (Hneq: fst idg <> id):
    get_global id (add_global ctx idg) = get_global id ctx.
  Proof.
    destruct idg as [id' g]; cbn in Hneq.
    unfold get_global, add_global, with_global; cbn.
    unfold Globalenvs.Genv.find_symbol, Globalenvs.Genv.find_def, Globalenvs.Genv.add_global; cbn.
    rewrite PTree.gso by (intros ?; subst; congruence).
    destruct (PTree.get id (Globalenvs.Genv.genv_symb (ctxt_global ctx))) as [b|] eqn:Hsym;
      [| reflexivity ].
    rewrite PTree.gso; [ reflexivity |].
    apply Coqlib.Plt_ne.
    eapply (Globalenvs.Genv.genv_symb_range (ctxt_global ctx)); eassumption.
  Qed.

  Lemma get_global_add_global_eq [P S GF GV] (ctx: ctxt P S GF GV) id g:
    get_global id (add_global ctx (id, g)) = Some g.
  Proof.
    unfold get_global, add_global, with_global; cbn.
    unfold Globalenvs.Genv.find_symbol, Globalenvs.Genv.find_def, Globalenvs.Genv.add_global; cbn.
    rewrite PTree.gss, PTree.gss.
    reflexivity.
  Qed.

End Facts.
