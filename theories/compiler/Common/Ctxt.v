From compcert.common Require AST.
From compcert.common Require Import Globalenvs.
From compcert.lib Require Import Maps.

From Utils Require Import ListExt.
From Imp Require Store.
From Compiler.Common Require Import Types.

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
(* Definition set_global {P S GF GV} x y (c: ctxt P S GF GV) := with_global (PTree.set x y (ctxt_global c)) c. *)
Definition get_stack {P S GF GV} n (c: ctxt P S GF GV): option S := List.nth_error (ctxt_stack c) n.
Definition set_stack {P S GF GV} n y (c: ctxt P S GF GV) := with_stack (ListExt.set_nth (ctxt_stack c) n y) c.

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

End Facts.
