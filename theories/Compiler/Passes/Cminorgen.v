From Stdlib Require Import String ZArith ssrfun.

From GallinaC.Utils Require Import ListExt.

From GallinaC.Imp Require Import Heap Store.

From GallinaC.Compiler.Common Require Import CCInj Types Expr.
From GallinaC.Compiler.IR Require Import Cmd Prog.

From compcert.common Require Import Errors.
From compcert.backend Require Cminor.
From compcert.lib Require Maps.
From compcert.lib Require Import Integers.

Local Open Scope error_monad_scope.

(* Local Notation "'do' 'assertion' A ; B" := (if A then B else assertion_failed) *)
(*                                              (at level 200, A at level 100, B at level 200) *)
(*     : error_monad_scope. *)

Local Notation "'do' 'assert' A 'with' fail_msg ; B" := (if A then B else Error (msg fail_msg))
                                                          (at level 200, A at level 100, B at level 200)
    : error_monad_scope.

(* Return in IR and in Cminor are very different.
 * In IR, return simply terminates a command and produces a pure value
 * In Cminor, return terminates a function and has it return the provided pure value
 * Thus, when compiling a function, we must keep track of a stack of bindings.
 * Each time, we recurse on bind, we push the bound identifier to the stack.
 * When we encounter a ret,
 * - If the stack is empty, we are at the top of the function, and can actually call a Cminor return
 * - Otherwise, we must assign to the bound variable (which is a temporary actually)
 *)
Record compilenv :=
  mkcompilenv
    {
      temps: list (AST.ident * type);
      id_malloc: option AST.ident;
      id_free: option AST.ident;
    }.

Definition make_int (n: nat): Cminor.expr :=
  Cminor.Econst (Cminor.Ointconst (Int.repr (Z.of_nat n))).

(* Booleans are long lost at that point in C, must hard-code to 1 or 0 resp. *)
Definition make_bool (b: bool): Cminor.expr :=
  Cminor.Econst (Cminor.Ointconst (if b then Int.one else Int.zero)).

Definition make_nullptr: Cminor.expr :=
  if Archi.ptr64 then
    Cminor.Econst (Cminor.Olongconst Int64.zero)
  else
    Cminor.Econst (Cminor.Ointconst Int.zero).

Definition make_size_t (n: N.t): Cminor.expr :=
  if Archi.ptr64 then
    Cminor.Econst (Cminor.Olongconst (Int64.repr (Z.of_N n)))
  else
    Cminor.Econst (Cminor.Ointconst (Int.repr (Z.of_N n))).

(* Since we don't have booleans anymore, we instead compare that the boolean is equal to "false" *)
Definition make_bool_not (e: Cminor.expr): Cminor.expr :=
  Cminor.Ebinop (Cminor.Ocmpu Ceq) e (make_bool false).

Definition make_nat_add (l r: Cminor.expr): Cminor.expr :=
  Cminor.Ebinop Cminor.Oadd l r.

Definition make_nat_eq (l r: Cminor.expr): Cminor.expr :=
  Cminor.Ebinop (Cminor.Ocmpu Ceq) l r.

Definition make_nat_lt (l r: Cminor.expr): Cminor.expr :=
  Cminor.Ebinop (Cminor.Ocmpu Clt) l r.

Definition make_ofst_lt (l r: Cminor.expr): Cminor.expr :=
  Cminor.Ebinop (Cminor.Ocmplu Clt) l r.

Definition ofst_add_op: Cminor.binary_operation :=
  if Archi.ptr64 then
    Cminor.Oaddl
  else
    Cminor.Oadd.

Definition ofst_sub_op: Cminor.binary_operation :=
  if Archi.ptr64 then
    Cminor.Osubl
  else
    Cminor.Osub.

Definition make_ofst_add (l r: Cminor.expr): Cminor.expr :=
  Cminor.Ebinop ofst_add_op l r.

(* GallinaC counts offsets in "memory words" *)
(* Compilation preserves values at this size *)
(* Before each operation, we adjust them to be the correct value *)
Definition adjust_offset (n: Cminor.expr): Cminor.expr :=
  if Archi.ptr64 then
    Cminor.Ebinop Cminor.Omull n (make_size_t (N.of_nat memval_memsize))
  else
    Cminor.Ebinop Cminor.Omul n (make_size_t (N.of_nat memval_memsize)).

Definition make_array_ofst := adjust_offset.

Definition make_size_from_count := adjust_offset.

Definition ptr_shift_fw_op: Cminor.binary_operation := ofst_add_op.

Definition ptr_shift_bw_op: Cminor.binary_operation := ofst_sub_op.

Definition make_ptr_shift_fw (p n: Cminor.expr): Cminor.expr :=
  Cminor.Ebinop ptr_shift_fw_op p (adjust_offset n).

Definition make_ptr_shift_bw (p n: Cminor.expr): Cminor.expr :=
  Cminor.Ebinop ptr_shift_bw_op p (adjust_offset n).

Definition make_ptr_eq (p1 p2: Cminor.expr): Cminor.expr :=
  if Archi.ptr64 then
    Cminor.Ebinop (Cminor.Ocmplu Ceq) p1 p2
  else
    Cminor.Ebinop (Cminor.Ocmpu Ceq) p1 p2.


(* Translates an expression *)
(* Assumes the expression is well-typed *)
(* Unsized-values are a failure case *)
Fixpoint transl_expr_maybe_sized cenv e t {struct e}: res (option (Cminor.expr * AST.memory_chunk)) :=
  match e, t with
  | e_var id, t =>
      match SetoidList.findA (Pos.eqb id) cenv.(temps) with
      | Some t' =>
          if type_eqb t' t
          then
            match type_mem_chunk t with
            | Some mc => OK (Some (Cminor.Evar id, mc))
            | None => OK None
            end
          else
            Error [ MSG "Identifier type mismatch" ]
      | None => Error [ MSG "Unbound identifier"; POS id ]
      end
  | e_tt, t_unit => OK None
  | e_bool b, t_bool => OK (Some (make_bool b, AST.Mbool))
  | e_nat n, t_nat => OK (Some (make_int n, AST.Mint32))
  | e_ofst n, t_ofst => OK (Some (make_size_t n, AST.Mptr))
  | e_nullptr, t_ptr => OK (Some (make_nullptr, AST.Mptr))
  | e_neg e, t_bool =>
      do e' <- transl_expr_maybe_sized cenv e t_bool;
      match e' with
      | Some (e', AST.Mbool) => OK (Some (make_bool_not e', AST.Mbool))
      | Some (_, _) => Error [ MSG "Negation of non-bool sized expression" ]
      | None => Error [ MSG "Negation of zero-sized" ]
      end
  | e_plus l r, t_nat =>
      do l' <- transl_expr_maybe_sized cenv l t_nat;
      do r' <- transl_expr_maybe_sized cenv r t_nat;
      match l', r' with
      | Some (l', AST.Mint32), Some (r', AST.Mint32) => OK (Some (make_nat_add l' r', AST.Mint32))
      | Some (_, _), Some(_, _) => Error [ MSG "Integer sum of non-integer shaped expression" ]
      | None, _ | _, None => Error [ MSG "Integer sum of zero-sized expression" ]
      end
  | e_nat_eq l r, t_bool =>
      do l' <- transl_expr_maybe_sized cenv l t_nat;
      do r' <- transl_expr_maybe_sized cenv r t_nat;
      match l', r' with
      | Some (l', AST.Mint32), Some (r', AST.Mint32) => OK (Some (make_nat_eq l' r', AST.Mbool))
      | Some (_, _), Some(_, _) => Error [ MSG "Integer comparison of non-integer shaped expressions" ]
      | None, _ | _, None => Error [ MSG "Integer comparison of zero-sized expression" ]
      end
  | e_tt, (t_bool | t_nat | t_ofst | t_ptr | t_fun _ _)
  | e_bool _, (t_unit | t_nat | t_ofst | t_ptr | t_fun _ _)
  | e_nat _, (t_unit | t_bool | t_ofst | t_ptr | t_fun _ _)
  | e_ofst _, (t_unit | t_bool | t_nat | t_ptr | t_fun _ _)
  | e_nullptr, (t_unit | t_bool | t_nat | t_ofst | t_fun _ _)
  | e_neg _, (t_unit | t_nat | t_ofst | t_ptr | t_fun _ _)
  | e_plus _ _, (t_unit | t_bool | t_ofst | t_ptr | t_fun _ _)
  | e_nat_eq _ _, (t_unit | t_nat | t_ofst | t_ptr | t_fun _ _)
    =>
      Error [ MSG "transl_expr_maybe_sized type mismatch" ]
  end.

Definition transl_expr_sized cenv (e: expr) (t: type): res (Cminor.expr * AST.memory_chunk) :=
  do e' <- transl_expr_maybe_sized cenv e t;
  match e' with
  | Some x => OK x
  | None => Error [ MSG "transl_expr_sized expression is zero-sized" ]
  end.

(* Helper function that returns or assigns a zero-sized value *)
Definition return_or_assign_unsized (target: option AST.ident): Cminor.stmt :=
  match target with
  | None => Cminor.Sreturn None
  | Some _ => Cminor.Sskip
  end.

(* Helper function that either returns a value whether we're inside a bind or not *)
Definition return_or_assign_sized target e: Cminor.stmt :=
  match target with
  | None => Cminor.Sreturn (Some e)
  | Some target => Cminor.Sassign target e
  end.

Definition perform_then_ret_unsized target s: Cminor.stmt :=
  Cminor.Sseq s (return_or_assign_unsized target).

(* Perform a GallinaC-style "return" *)
(* With a "target", we assign the result of evaluating e to it *)
(* Without, we exit the function with the result of evaluating e *)
Definition ret_expr (cenv: compilenv) (target: option AST.ident) (e: expr) (t: type): res Cminor.stmt :=
  do emc <- transl_expr_maybe_sized cenv e t;
  OK (Option.apply
        (return_or_assign_sized target)
        (return_or_assign_unsized target)
        (option_map fst emc)).

Definition load_ptr_expr e_ptr mc: Cminor.expr := Cminor.Eload mc e_ptr.

(* Loads from the provided address and perform a GallinaC-style return *)
Definition ret_load_ptr target e_ptr (t: type): res Cminor.stmt :=
  let e := Option.map (load_ptr_expr e_ptr) (type_mem_chunk t) in
  OK (Option.apply
        (return_or_assign_sized target)
        (return_or_assign_unsized target)
        e).

Definition store_ptr_stmt e_ptr emc_data := Cminor.Sstore (snd emc_data) e_ptr (fst emc_data).

Definition ret_store_ptr cenv target (e_ptr: Cminor.expr) (e_data: expr) (t: type): res Cminor.stmt :=
  do emc_data <- transl_expr_maybe_sized cenv e_data t;
  let s_store :=
    ssrfun.Option.apply
      (store_ptr_stmt e_ptr)
      Cminor.Sskip
      emc_data
  in
  OK (perform_then_ret_unsized target s_store).

(* Offset is in "memory words" (i.e. max(sizeof(t_nat), sizeof(t_ptr))) *)
Definition stack_ptr (ofst: nat): Cminor.expr :=
  Cminor.Econst (Cminor.Oaddrstack (Ptrofs.repr (Z.of_nat (ofst * memval_memsize)))).

Definition global_ptr (id: AST.ident): Cminor.expr :=
  Cminor.Econst (Cminor.Oaddrsymbol id Ptrofs.zero).

Definition make_call target f args sig: Cminor.stmt :=
  match target with
  | None => Cminor.Stailcall sig (global_ptr f) args
  | Some target =>
      Cminor.Scall
        (match sig.(AST.sig_res) with
         | AST.Xvoid => None
         | _ => Some target
         end)
        sig (global_ptr f)
        args
  end.

Definition make_for_ofst (i: AST.ident) (start: Cminor.expr) (step: Cminor.expr) (stop: Cminor.expr) (body: Cminor.expr -> Cminor.stmt): Cminor.stmt :=
  Cminor.Sblock
    (Cminor.Sseq
       (Cminor.Sassign i start)
       (Cminor.Sloop
          (Cminor.Sifthenelse
             (make_ofst_lt (Cminor.Evar i) stop)
             (Cminor.Sseq
                (body (Cminor.Evar i))
                (Cminor.Sassign i (make_ofst_add (Cminor.Evar i) step)))
             (Cminor.Sexit 0))))
.

Fixpoint transl_cmd (cenv: compilenv) (target: option AST.ident) (c: cmd) {struct c}: res Cminor.stmt :=
  match c with
  | c_ret e t =>
      ret_expr cenv target e t
  | c_bind i' t_b c_b c_c t_c =>
      do c_b' <- transl_cmd cenv (Some i') c_b;
      do c_c' <- transl_cmd cenv target c_c;
      OK (Cminor.Sseq c_b' c_c')
  | c_if e_if c_then c_else t_te =>
      do (e_if', mc_if) <- transl_expr_sized cenv e_if t_bool;
      do assert (AST.chunk_eq mc_if AST.Mbool) with "If condition is not a bool";
      do c_then' <- transl_cmd cenv target c_then;
      do c_else' <- transl_cmd cenv target c_else;
      OK (Cminor.Sifthenelse e_if' c_then' c_else')
  | c_while c_cond id_cond c_body id_body =>
      do c_cond' <- transl_cmd cenv (Some id_cond) c_cond;
      do c_body' <- transl_cmd cenv (Some id_body) c_body;
      (* We don't know the context in which the while is executing
       * To be sure, we explicitly "return" after exciting the loop
       * Because the termination checker is annoying, we must manually specify a sub-function call
       *)
      OK
        (perform_then_ret_unsized
           target
           (Cminor.Sblock
              (Cminor.Sloop
                 (Cminor.Sseq
                    c_cond'
                    (Cminor.Sifthenelse
                       (Cminor.Evar id_cond)
                       c_body'
                       (Cminor.Sexit 0)))))
        )
  | c_read_var n t =>
      ret_load_ptr target (stack_ptr n) t
  | c_write_var n t e_data =>
      ret_store_ptr cenv target (stack_ptr n) e_data t
  | c_alloc_ptr e_count t e_init id_ptr id_init =>
      match cenv.(id_malloc) with
      | Some id_malloc =>
          do (e_count', mc_count) <- transl_expr_sized cenv e_count t_ofst;
          do assert (AST.chunk_eq mc_count AST.Mptr) with "Chunk of allocation size is not AST.Mptr";
          let e_size' := make_size_from_count e_count' in
          do emc_init' <- transl_expr_maybe_sized cenv e_init t;
          OK
            (ssrfun.Option.apply
               (fun (emc_init': Cminor.expr * AST.memory_chunk) =>
                  let (e_init', mc) := emc_init' in
                  Cminor.Sseq
                    (* Alloc & Initialize memory *)
                    (Cminor.Sseq
                       (* Alloc *)
                       (make_call (Some id_ptr) id_malloc [ e_size' ] (AST.ef_sig AST.EF_malloc))
                       (* Initialize *)
                       (make_for_ofst id_init (make_size_t 0) (make_size_t 1) e_count'
                          (fun id => store_ptr_stmt
                                       (* offset adjustemnt done by make_ptr_shift_fw *)
                                       (make_ptr_shift_fw
                                          (Cminor.Evar id_ptr)
                                          id)
                                       emc_init')))
                    (return_or_assign_sized target (Cminor.Evar id_ptr))
               )
               (return_or_assign_unsized target)
               emc_init')
      | None =>
          Error [ MSG "No access to malloc" ]
      end
  | c_read_ptr e_ptr t =>
      do (e_ptr', mc_ptr) <- transl_expr_sized cenv e_ptr t_ptr;
      ret_load_ptr target e_ptr' t
  | c_write_ptr e_ptr t e_data =>
      do (e_ptr', mc_ptr) <- transl_expr_sized cenv e_ptr t_ptr;
      ret_store_ptr cenv target e_ptr' e_data t
  | c_free_ptr e_ptr =>
      match cenv.(id_free) with
      | Some id_free =>
          do (e_ptr', mc_ptr) <- transl_expr_sized cenv e_ptr t_ptr;
          do assert (AST.chunk_eq mc_ptr AST.Mptr) with "free pointer is not a pointer";
          OK
            (make_call target id_free [ e_ptr' ] (AST.ef_sig AST.EF_free))
      | None =>
          Error [ MSG "No access to free" ]
      end
  | c_shift_fw_ptr e_ptr e_shift =>
      do (e_ptr', mc_ptr) <- transl_expr_sized cenv e_ptr t_ptr;
      do assert (AST.chunk_eq mc_ptr AST.Mptr) with "shift_fw pointer is not a pointer";
      do (e_shift', mc_shift) <- transl_expr_sized cenv e_shift t_ofst;
      do assert (AST.chunk_eq mc_shift AST.Mptr) with "shift_fw offset is not an offset";
      OK (return_or_assign_sized target (make_ptr_shift_fw e_ptr' e_shift'))
  | c_shift_bw_ptr e_ptr e_shift =>
      do (e_ptr', mc_ptr) <- transl_expr_sized cenv e_ptr t_ptr;
      do assert (AST.chunk_eq mc_ptr AST.Mptr) with "shift_bw pointer is not a pointer";
      do (e_shift', mc_shift) <- transl_expr_sized cenv e_shift t_ofst;
      do assert (AST.chunk_eq mc_shift AST.Mint32) with "shift_bw offset is not an offset";
      OK (return_or_assign_sized target (make_ptr_shift_fw e_ptr' e_shift'))
  | c_ptr_eq e_ptr_l e_ptr_r =>
      do (e_ptr_l', mc_ptr_l) <- transl_expr_sized cenv e_ptr_l t_ptr;
      do assert (AST.chunk_eq mc_ptr_l AST.Mptr) with "ptr_eq left pointer is not a pointer";
      do (e_ptr_r', mc_ptr_r) <- transl_expr_sized cenv e_ptr_r t_ptr;
      do assert (AST.chunk_eq mc_ptr_r AST.Mptr) with "ptr_eq right pointer is not a pointer";
      OK (return_or_assign_sized target (make_ptr_eq e_ptr_l' e_ptr_r'))
  | c_app f t_out args =>
      let sig := mk_signature (List.map snd args) t_out in
      do args' <- Errors.mmap (uncurry (transl_expr_maybe_sized cenv)) args;
      let args' := ListExt.filter_map id args' in
      let args' := List.map fst args' in
      OK (make_call target f args' (mk_signature (List.map snd args) t_out))
  end.

Definition params_of_function (f: function): list AST.ident :=
  ListExt.filter_map (fun idt => match idt with (_, t_unit) => None | (id, (t_bool|t_nat|t_ofst|t_ptr|t_fun _ _)) => Some id end) f.(fn_params).

Definition vars_of_function (f: function): list AST.ident :=
  List.map fst f.(fn_temps).

Definition transl_funbody id_malloc id_free (f: function): res Cminor.function :=
  do tbody <- transl_cmd (mkcompilenv (f.(fn_params)++f.(fn_temps)) id_malloc id_free) None f.(fn_body);
  OK (Cminor.mkfunction
        (* fn_sig *)
        (Prog.signature_of_signature (Prog.fn_signature f))
        (* fn_params *)
        (params_of_function f)
        (* fn_vars /!\ Those are temporaries, not local variables *)
        (vars_of_function f)
        (* fn_stackspace /!\ Stackspace holds local variables, but not temporaries *)
        (offset_to_offset f.(fn_extra).(fn_stackspace))
        tbody)
.

Definition transl_function id_malloc id_free (f: function): res Cminor.function :=
  transl_funbody id_malloc id_free f.

Definition transl_fundef id_malloc id_free (id: AST.ident) (f: fundef): res Cminor.fundef :=
  AST.transf_partial_fundef (transl_function id_malloc id_free) f.

Definition transl_globvar (id: AST.ident) (ty: vardef) := OK tt.

Definition transl_program (p: program) : res Cminor.program :=
  AST.transform_partial_program2 (transl_fundef p.(prog_extra).(prog_malloc) p.(prog_extra).(prog_free)) transl_globvar (Prog.program_of_program p).
