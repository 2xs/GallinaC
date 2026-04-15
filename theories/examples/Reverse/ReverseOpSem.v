From Examples.Reverse Require Import ReverseReify ReverseExecution.

From Utils Require Import ListExt OptionExt.
From Imp Require Import Canonical.
From Compiler.Common Require Import Prog.
From Compiler.Deep Require Import OpSem.

Definition fundef_main: (Prog.fundef Cmd.cmd) :=
  Eval compute in
    match deep_reverse_prog.(Prog.prog_defs) with
    | (_, AST.Gfun fd)::_ => fd
    | _ => AST.External (AST.EF_external String.EmptyString AST.signature_main)
    end.

(* Adaptation of the initial state from ReverseExecution *)
Definition init_state := Callstate fundef_main [] (@Kstop _) ReverseExecution.init_state.

Definition final_state := Returnstate (Value.v_nat 0) (@Kstop _) ReverseExecution.post_reverse_state.

Ltac builtin_step :=
  first
    [ eapply builtin_alloc_ptr; [ reflexivity | reflexivity | now constructor | reflexivity ]
    | eapply builtin_write_ptr; now constructor
    ].

Ltac one_step :=
  first
    [ apply Smallstep.star_refl
    | eapply Smallstep.star_step with (t1 := Events.E0) (t2 := Events.E0);
      [ first
          [ eapply step_internal_function; [ now repeat constructor | reflexivity | now constructor ]
          | apply step_bind
          | eapply step_app ; [ reflexivity | reflexivity | reflexivity | constructor ]
          | eapply step_builtin_seq_cont; [ now constructor | builtin_step ]
          ]
        | auto
        | reflexivity]
    ];
  cbn -[Globalenvs.Genv.globalenv].

Example reverse_execution:
  Smallstep.star (@OpSem.step _ _) (Globalenvs.Genv.globalenv deep_reverse_prog) init_state Events.E0 final_state.
Proof.
  repeat one_step.
  eapply Smallstep.star_step with (t1 := Events.E0) (t2 := Events.E0); [ | | reflexivity ].
  eapply step_builtin_seq_cont; [ now constructor | ].
  eapply builtin_shift_fw_ptr; [ reflexivity | reflexivity | now constructor| | ].
  left.
  Eval compute in Algebra.carrier (Heap.mem (Heap.heap list_heap_heap)).
  match goal with
  | |- Heap.Facts.Valid ?hp (Some ({| Pointer.Addr.block := ?b; Pointer.Addr.offset := ?o |}, ?prov)) => eexists {| Pointer.Addr.block := b; Pointer.Addr.offset := o |}, (default Memval.VUnit (List.nth (BinNat.N.to_nat o) (List.nth b (list_heap hp) []) None)); split; [ constructor | ]
  end.
  cbn -[Heap.one].
  match goal with
    | |- Algebra.Substate (Heap.one ?addr ?v) {| list_heap := ?hp; alloc := ?b_alloc |} =>
        auto
  end.
  Check set_nth [[None; None]; [None; None]] 1.
