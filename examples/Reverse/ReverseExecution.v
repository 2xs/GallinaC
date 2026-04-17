From GallinaC Require Import Programming.

From GallinaC.Examples.Reverse Require Import Reverse.
Import List ListNotations.

Definition init_state: Primitives.State ListStore list_heap_heap := Primitives.mkState Store.emp (Heap.emp_with_alc (mkOptAlloc (Some 0%nat))).

Definition post_prelude_state: Primitives.State ListStore list_heap_heap :=
  Primitives.mkState
    {| ls_bindings := nil; ls_next_var := 0 |}
    {| list_heap :=
        [
          [ Some (VInt 3); Some (VPtr Pointer.NULL) ];
          [ Some (VInt 2); Some (VPtr (Some (Addr.mkAddr 0 0, Provenance.Allocation 0 0 2 0 2 Permission.Free))) ];
          [ Some (VInt 1); Some (VPtr (Some (Addr.mkAddr 1 0, Provenance.Allocation 1 0 2 0 2 Permission.Free))) ]
        ];
      alloc := true |}.

Definition post_reverse_state: Primitives.State ListStore list_heap_heap :=
  Primitives.mkState
    {| ls_bindings := nil; ls_next_var := 2 |}
    {| list_heap :=
        [
          [ Some (VInt 3); Some  (VPtr (Some (Addr.mkAddr 1 0, Provenance.Allocation 1 0 2 0 2 Permission.Free)))];
          [ Some (VInt 2); Some (VPtr (Some (Addr.mkAddr 2 0, Provenance.Allocation 2 0 2 0 2 Permission.Free))) ];
          [ Some (VInt 1); Some (VPtr Pointer.NULL) ]
        ];
      alloc := true |}.

(* Programs without while can be reduced using the classical tactics without issue *)
Example prelude_execution:
  prelude init_state = Some (Success (Some (Addr.mkAddr 2 0, Provenance.Allocation 2 0 2 0 2 Permission.Free), post_prelude_state)).
Proof.
  reflexivity.
Qed.

(* When `while` is involved, reduction is blocked when we encounter `while`.
 * Hence, reflexivity cannot validate the execution of `reverse`
 * Let's first define a tactic to reduce programs until we encounter a `while` *)
Ltac reduce := match goal with
               | |- (do x <- ret _; _) _ = _ => unfold ret at 1; cbn; simpl
               | |- (do x <- (do y <- _; _); _) _ = _ => rewrite bind_assoc; cbn; simpl
               | |- (do x <- (do var v <- _ ; _); _) _ = _ => unfold with_var at 1; (try rewrite bind_assoc); cbn; simpl
               | |- (do x <- read_var _; _) _ = _ => unfold read_var at 1; cbn; simpl
               | |- (do x <- write_var _ _; _) _ = _ => unfold read_var at 1; cbn; simpl
               | |- (do x <- read_ptr _; _) _ = _ => unfold read_ptr at 1; cbn; simpl
               | |- (do x <- write_ptr _ _; _) _ = _ => unfold write_ptr at 1; cbn; simpl
               | |- (do x <- alloc_ptr _ _; _) _ = _ => unfold alloc_ptr at 1; cbn; simpl
               | |- (do x <- free_ptr _; _) _ = _ => unfold free_ptr at 1; cbn; simpl
               | |- (do x <- _ ~+> _; _) _ = _ => unfold shift_fw_ptr at 1; cbn; simpl
               | |- (do x <- _ ~-> _; _) _ = _ => unfold shift_bw_ptr at 1; cbn; simpl
               | |- (do x <- eq_ptr _ _; _) _ = _ => unfold eq_ptr at 1; cbn; simpl
               | |- (do x <- put _; _) _ = _ => unfold put at 1; cbn; simpl
               | _ => fail
               end.

(* Then, we can progress as usual, except that we must unroll iterations of the
 * while loop one-by-one *)
Example reverse_execution:
  main init_state = Some (Success (0, post_reverse_state)).
Proof.
  cbv delta [main prelude reverse postlude].
  repeat reduce.
  (* We are stuck at a while, unroll the loop once, the continue evaluation *)
  rewrite while_fixpoint; repeat reduce.
  (* If we know that the loop terminates, we can also just repeat this as necessary *)
  repeat (rewrite while_fixpoint; repeat reduce).
  (* Program terminated successfully, finish the proof by reflexivity *)
  reflexivity.
Qed.
