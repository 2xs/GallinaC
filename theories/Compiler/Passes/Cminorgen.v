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

From Stdlib Require Import String ZArith ssrfun.

From GallinaC.Utils Require Import ListExt.

From GallinaC.Imp Require Import Heap Store Value.

From GallinaC.Compiler.Common Require Import CCInj Types Expr.
From GallinaC.Compiler.IR Require Typing.
From GallinaC.Compiler.IR Require Import Cmd Prog.

From compcert.common Require Import Errors.
From compcert.backend Require Cminor.
From compcert.lib Require Maps.
From compcert.lib Require Import Integers.

Local Open Scope error_monad_scope.

(* Return in IR and in Cminor are very different.
 * In IR, return simply terminates a command and produces a pure value
 * In Cminor, return terminates a function and has it return the provided pure value
 * Thus, when compiling a function, we must keep track of a stack of bindings.
 * Each time, we recurse on bind, we push the bound identifier to the stack.
 * When we encounter a ret,
 * - If the stack is empty, we are at the top of the function, and can actually call a Cminor return
 * - Otherwise, we must assign to the bound variable (which is a temporary actually)
 *)

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

Definition make_ofst (n: N.t): Cminor.expr :=
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

Definition make_nat_mul (l r: Cminor.expr): Cminor.expr :=
  Cminor.Ebinop Cminor.Omul l r.

Definition make_nat_div (l r: Cminor.expr): Cminor.expr :=
  Cminor.Ebinop Cminor.Odivu l r.

Definition make_nat_mod (l r: Cminor.expr): Cminor.expr :=
  Cminor.Ebinop Cminor.Omodu l r.

Definition make_nat_lt (l r: Cminor.expr): Cminor.expr :=
  Cminor.Ebinop (Cminor.Ocmpu Clt) l r.

Definition make_ofst_lt (l r: Cminor.expr): Cminor.expr :=
  if Archi.ptr64 then
    Cminor.Ebinop (Cminor.Ocmplu Clt) l r
  else
    Cminor.Ebinop (Cminor.Ocmpu Clt) l r.

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
    Cminor.Ebinop Cminor.Omull n (make_ofst (N.of_nat memword_bytes))
  else
    Cminor.Ebinop Cminor.Omul n (make_ofst (N.of_nat memword_bytes)).

Definition make_array_ofst := adjust_offset.

Definition make_ofst_from_count := adjust_offset.

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
Fixpoint transl_expr (e: expr): Cminor.expr :=
  match e with
  | e_var id => Cminor.Evar id
  | e_tt => make_int 0
  | e_bool b => make_bool b
  | e_nat n => make_int n
  | e_ofst n => make_ofst n
  | e_nullptr => make_nullptr
  | e_neg e => make_bool_not (transl_expr e)
  | e_add l r => make_nat_add (transl_expr l) (transl_expr r)
  | e_eqb l r => make_nat_eq (transl_expr l) (transl_expr r)
  | e_mul l r => make_nat_mul (transl_expr l) (transl_expr r)
  end.

Definition transl_expr_sized (e: expr) (t: type): option (Cminor.expr * AST.memory_chunk) :=
  match type_mem_chunk t with
  | Some mc => Some (transl_expr e, mc)
  | None => None
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

Definition load_ptr_expr e_ptr mc: Cminor.expr := Cminor.Eload mc e_ptr.

Definition store_ptr_stmt e_ptr emc_data := Cminor.Sstore (snd emc_data) e_ptr (fst emc_data).

(* Perform a GallinaC-style "return" *)
(* With a "target", we assign the result of evaluating e to it *)
(* Without, we exit the function with the result of evaluating e *)
Definition ret_expr (target: option AST.ident) (e: expr) (t: type): Cminor.stmt :=
  match type_mem_chunk t with
  | Some _ => return_or_assign_sized target (transl_expr e)
  | None => return_or_assign_unsized target
  end.

(* Loads from the provided address and perform a GallinaC-style return *)
Definition ret_load_ptr (target: option AST.ident) (e_ptr: Cminor.expr) (t: type): Cminor.stmt :=
  match type_mem_chunk t with
  | Some mc => return_or_assign_sized target (load_ptr_expr e_ptr mc)
  | None => return_or_assign_unsized target
  end.

Definition ret_store_ptr (target: option AST.ident) (e_ptr: Cminor.expr) (e_data: expr) (t: type): Cminor.stmt :=
  perform_then_ret_unsized
    target
    (match type_mem_chunk t with
     | Some mc => Cminor.Sstore mc e_ptr (transl_expr e_data)
     | None => Cminor.Sskip
     end).

(* Offset is in "memory words" (i.e. max(sizeof(t_nat), sizeof(t_ptr))) *)
Definition stack_ptr (ofst: nat): Cminor.expr :=
  Cminor.Econst (Cminor.Oaddrstack (Ptrofs.repr (offset_to_offset (Z.of_nat ofst)))).

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

Definition arg_is_sized (et: expr * type): bool :=
  match type_mem_chunk (snd et) with
  | Some _ => true
  | None => false
  end.

Definition transl_args (args: list (expr * type)): list Cminor.expr :=
  List.map (fun et => transl_expr (fst et)) (List.filter arg_is_sized args).

Fixpoint transl_cmd (id_malloc id_free: AST.ident) (target: option AST.ident) (c: cmd) {struct c}: Cminor.stmt :=
  match c with
  | c_ret e t =>
      ret_expr target e t
  | c_bind i' t_b c_b c_c t_c =>
      Cminor.Sseq
        (transl_cmd id_malloc id_free (Some i') c_b)
        (transl_cmd id_malloc id_free target c_c)
  | c_if e_if c_then c_else t_te =>
      Cminor.Sifthenelse
        (transl_expr e_if)
        (transl_cmd id_malloc id_free target c_then)
        (transl_cmd id_malloc id_free target c_else)
  | c_while c_cond id_cond c_body id_body =>
      (* We don't know the context in which the while is executing
       * To be sure, we explicitly "return" after exciting the loop
       *)
      perform_then_ret_unsized
        target
        (Cminor.Sblock
           (Cminor.Sloop
              (Cminor.Sseq
                 (transl_cmd id_malloc id_free (Some id_cond) c_cond)
                 (Cminor.Sifthenelse
                    (Cminor.Evar id_cond)
                    (transl_cmd id_malloc id_free (Some id_body) c_body)
                    (Cminor.Sexit 0)))))
  | c_read_var n t =>
      ret_load_ptr target (stack_ptr n) t
  | c_write_var n t e_data =>
      ret_store_ptr target (stack_ptr n) e_data t
  | c_alloc_ptr e_count t e_init id_ptr id_count id_init =>
      Cminor.Sseq
        (ret_expr (Some id_init) e_init t)
        (Cminor.Sseq
           (* Alloc & Initialize memory *)
           (Cminor.Sseq
              (* Alloc *)
              (make_call (Some id_ptr) id_malloc [ make_ofst_from_count (transl_expr e_count) ] (AST.ef_sig AST.EF_malloc))
              (* Initialize *)
              (match type_mem_chunk t with
               | Some mc =>
                   make_for_ofst id_count (make_ofst 0) (make_ofst 1) (transl_expr e_count)
                     (fun id => store_ptr_stmt
                                  (* offset adjustemnt done by make_ptr_shift_fw *)
                                  (make_ptr_shift_fw
                                     (Cminor.Evar id_ptr)
                                     id)
                                  (Cminor.Evar id_init, mc))
               | None => Cminor.Sskip
               end))
           (return_or_assign_sized target (Cminor.Evar id_ptr)))
  | c_read_ptr e_ptr t =>
      ret_load_ptr target (transl_expr e_ptr) t
  | c_write_ptr e_ptr t e_data =>
      ret_store_ptr target (transl_expr e_ptr) e_data t
  | c_free_ptr e_ptr =>
      make_call target id_free [ transl_expr e_ptr ] (AST.ef_sig AST.EF_free)
  | c_shift_fw_ptr e_ptr e_shift =>
      return_or_assign_sized target (make_ptr_shift_fw (transl_expr e_ptr) (transl_expr e_shift))
  | c_shift_bw_ptr e_ptr e_shift =>
      return_or_assign_sized target (make_ptr_shift_bw (transl_expr e_ptr) (transl_expr e_shift))
  | c_ptr_eq e_ptr_l e_ptr_r =>
      return_or_assign_sized target (make_ptr_eq (transl_expr e_ptr_l) (transl_expr e_ptr_r))
  | c_app f t_out args =>
      make_call target f (transl_args args) (mk_signature (List.map snd args) t_out)
  | c_div e_l e_r =>
      return_or_assign_sized target (make_nat_div (transl_expr e_l) (transl_expr e_r))
  | c_mod e_l e_r =>
      return_or_assign_sized target (make_nat_mod (transl_expr e_l) (transl_expr e_r))
  end.

Definition params_of_function (f: function): list AST.ident :=
  ListExt.filter_map (fun idt => match idt with (_, t_unit) => None | (id, (t_bool|t_nat|t_ofst|t_ptr)) => Some id end) f.(fn_params).

Definition vars_of_function (f: function): list AST.ident :=
  List.map fst f.(fn_temps) ++ List.map fst f.(fn_internals).

Definition transl_funbody (id_malloc id_free: AST.ident) (f: function): Cminor.function :=
  Cminor.mkfunction
        (* fn_sig *)
        (Prog.signature_of_signature (Prog.fn_signature f))
        (* fn_params *)
        (params_of_function f)
        (* fn_vars /!\ Those are temporaries, not local variables *)
        (vars_of_function f)
        (* fn_stackspace /!\ Stackspace holds local variables, but not temporaries *)
        (offset_to_offset f.(fn_extra).(fn_stackspace))
        (transl_cmd id_malloc id_free None f.(fn_body))
.

Definition transl_function (id_malloc id_free: AST.ident) (f: function): Cminor.function :=
  transl_funbody id_malloc id_free f.

Definition transl_fundef (id_malloc id_free: AST.ident) (f: fundef): Cminor.fundef :=
  AST.transf_fundef (transl_function id_malloc id_free) f.

Definition transl_globvar (v: AST.globvar vardef): AST.globvar unit :=
  AST.mkglobvar tt v.(AST.gvar_init) v.(AST.gvar_readonly) v.(AST.gvar_volatile).

Definition transl_globdef (id_malloc id_free: AST.ident) (idg: AST.ident * AST.globdef fundef vardef): AST.ident * AST.globdef Cminor.fundef unit :=
  match idg with
  | (id, AST.Gfun f) => (id, AST.Gfun (transl_fundef id_malloc id_free f))
  | (id, AST.Gvar v) => (id, AST.Gvar (transl_globvar v))
  end.

Definition lookup_exf (dm: Maps.PTree.t globdef) (ef: AST.external_function) (name: string)
  : res AST.ident :=
  match find_exf_defmap dm ef with
  | Some id => OK id
  | None => Error (MSG name :: MSG ": missing declaration" :: nil)
  end.

Definition transl_program (p: program) : res Cminor.program :=
  let dm := AST.prog_defmap p in
  do idm <- lookup_exf dm AST.EF_malloc "malloc"%string;
  do idf <- lookup_exf dm AST.EF_free "free"%string;
  OK (AST.mkprogram
        (List.map (transl_globdef idm idf) (Prog.prog_defs p))
        (Prog.prog_public p)
        (Prog.prog_main p)).
