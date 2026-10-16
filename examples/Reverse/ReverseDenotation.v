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

From Stdlib Require Import String PArith Bool.

From compcert.backend Require Import SplitLong(sig_f_l, sig_l_f, sig_l_s, sig_ll_l, sig_li_l).

From GallinaC.Examples.Reverse Require Import ReverseReify ReverseExecution ReverseOpSem Reverse.
Import Reverse.

From GallinaC.Utils Require Import ListExt OptionExt PosExt StringExt.
From GallinaC.Imp Require Import Monad.
From GallinaC.Models Require Import GCModel.
From GallinaC.Compiler.Common Require Import Ctxt.
From GallinaC.Compiler.Deep Require Import Denotation Cmd Prog Typing Agree.

Local Open Scope string_scope.

Definition dummy_function : function :=
  {| fn_return := t_unit; fn_params := []; fn_temps := []; fn_internals := [];
                                           fn_body := c_ret e_tt; fn_extra := tt |}.

Definition fn_allocate : function :=
  Eval compute in
    match ListExt.sfind "allocate" deep_reverse_prog_symbols with
    | Some id =>
        match ListExt.sfind id deep_reverse_prog.(prog_defs) with
        | Some (AST.Gfun (AST.Internal fn)) => fn
        | _ => dummy_function
        end
    | None => dummy_function
    end.

Definition fn_reverse : function :=
  Eval compute in
    match ListExt.sfind "reverse" deep_reverse_prog_symbols with
    | Some id =>
        match ListExt.sfind id deep_reverse_prog.(prog_defs) with
        | Some (AST.Gfun (AST.Internal fn)) => fn
        | _ => dummy_function
        end
    | None => dummy_function
    end.

Definition fn_main : function :=
  Eval compute in
    match ListExt.sfind "main" deep_reverse_prog_symbols with
    | Some id =>
        match ListExt.sfind id deep_reverse_prog.(prog_defs) with
        | Some (AST.Gfun (AST.Internal fn)) => fn
        | _ => dummy_function
        end
    | None => dummy_function
    end.

Definition print_ll_ef : AST.external_function :=
  Eval compute in
    match ListExt.sfind "print_ll" deep_reverse_prog_symbols with
    | Some id =>
        match ListExt.sfind id deep_reverse_prog.(prog_defs) with
        | Some (AST.Gfun (AST.External ef)) => ef
        | _ => AST.EF_free
        end
    | None => AST.EF_free
    end.

Definition ctx0 : Ctxt.ctxt Empty_set Empty_set Empty_set fundef vardef :=
  ctxt_emp Empty_set Empty_set Empty_set fundef vardef deep_reverse_prog.(prog_public).
Definition glob0 : @denote_glob_ctxt GCModel ctx0 := tt.

Definition reverse_exfs : @exf_env GCModel :=
  fun nm sig =>
    if String.eqb nm "print_ll" then
      match sig as s return option (denote_sig GCModel s) with
      | {| sig_args := [t_ptr]; sig_res := t_unit |} => Some print_ll
      | _ => None
      end
    else None.

(* malloc *)
Definition d_malloc :=
  @denote_external_function GCModel reverse_exfs AST.EF_malloc eq_refl.
Definition ctx1 : Ctxt.ctxt Empty_set Empty_set Empty_set fundef vardef :=
  add_global ctx0 (1%positive, AST.Gfun (AST.External AST.EF_malloc)).
Definition glob1 : @denote_glob_ctxt GCModel ctx1 :=
  @denote_glob_ctxt_extend GCModel ctx0
    1%positive (AST.Gfun (AST.External AST.EF_malloc))
    eq_refl d_malloc glob0.

(* free *)
Definition d_free :=
  @denote_external_function GCModel reverse_exfs AST.EF_free eq_refl.
Definition ctx2 : Ctxt.ctxt Empty_set Empty_set Empty_set fundef vardef :=
  add_global ctx1 (2%positive, AST.Gfun (AST.External AST.EF_free)).
Definition glob2 : @denote_glob_ctxt GCModel ctx2 :=
  @denote_glob_ctxt_extend GCModel ctx1
    2%positive (AST.Gfun (AST.External AST.EF_free))
    eq_refl d_free glob1.

Definition runtime_helpers : list (AST.ident * string * AST.signature) :=
  [ (3%positive, "__compcert_i64_dtos", sig_f_l);
    (4%positive, "__compcert_i64_dtou", sig_f_l);
    (5%positive, "__compcert_i64_stod", sig_l_f);
    (6%positive, "__compcert_i64_utod", sig_l_f);
    (7%positive, "__compcert_i64_stof", sig_l_s);
    (8%positive, "__compcert_i64_utof", sig_l_s);
    (9%positive, "__compcert_i64_sdiv", sig_ll_l);
    (10%positive, "__compcert_i64_udiv", sig_ll_l);
    (11%positive, "__compcert_i64_smod", sig_ll_l);
    (12%positive, "__compcert_i64_umod", sig_ll_l);
    (13%positive, "__compcert_i64_shl", sig_li_l);
    (14%positive, "__compcert_i64_shr", sig_li_l);
    (15%positive, "__compcert_i64_sar", sig_li_l);
    (16%positive, "__compcert_i64_umulh", sig_ll_l);
    (17%positive, "__compcert_i64_smulh", sig_ll_l) ].

Fixpoint denote_runtime_chain (helpers: list (AST.ident * string * AST.signature))
  (ctx: Ctxt.ctxt Empty_set Empty_set Empty_set fundef vardef)
  (glob: @denote_glob_ctxt GCModel ctx)
  : { ctx': Ctxt.ctxt Empty_set Empty_set Empty_set fundef vardef & @denote_glob_ctxt GCModel ctx' } :=
  match helpers with
  | [] => existT _ ctx glob
  | (id, name, sig)::helpers =>
      denote_runtime_chain helpers
        (add_global ctx (id, AST.Gfun (AST.External (AST.EF_runtime name sig))))
        (@denote_glob_ctxt_extend GCModel ctx
           id (AST.Gfun (AST.External (AST.EF_runtime name sig)))
           eq_refl tt glob)
  end.

Definition packed_runtime := denote_runtime_chain runtime_helpers ctx2 glob2.
Definition ctx2' : Ctxt.ctxt Empty_set Empty_set Empty_set fundef vardef :=
  projT1 packed_runtime.
Definition glob2' : @denote_glob_ctxt GCModel ctx2' :=
  projT2 packed_runtime.

(* allocate *)
Definition d_allocate :=
  @denote_function GCModel ctx2' fn_allocate eq_refl glob2'.
Definition ctx3 : Ctxt.ctxt Empty_set Empty_set Empty_set fundef vardef :=
  add_global ctx2' (28%positive, AST.Gfun (AST.Internal fn_allocate)).
Definition glob3 : @denote_glob_ctxt GCModel ctx3 :=
  @denote_glob_ctxt_extend GCModel ctx2'
    28%positive (AST.Gfun (AST.Internal fn_allocate))
    eq_refl d_allocate glob2'.

(* reverse *)
Definition d_reverse :=
  @denote_function GCModel ctx3 fn_reverse eq_refl glob3.
Definition ctx4 : Ctxt.ctxt Empty_set Empty_set Empty_set fundef vardef :=
  add_global ctx3 (41%positive, AST.Gfun (AST.Internal fn_reverse)).
Definition glob4 : @denote_glob_ctxt GCModel ctx4 :=
  @denote_glob_ctxt_extend GCModel ctx3
    41%positive (AST.Gfun (AST.Internal fn_reverse))
    eq_refl d_reverse glob3.

(* print_ll (external) *)
Definition d_print_ll :=
  @denote_external_function GCModel reverse_exfs print_ll_ef eq_refl.
Definition ctx5 : Ctxt.ctxt Empty_set Empty_set Empty_set fundef vardef :=
  add_global ctx4 (43%positive, AST.Gfun (AST.External print_ll_ef)).
Definition glob5 : @denote_glob_ctxt GCModel ctx5 :=
  @denote_glob_ctxt_extend GCModel ctx4
    43%positive (AST.Gfun (AST.External print_ll_ef))
    eq_refl d_print_ll glob4.

(* main *)
Definition d_main :=
  @denote_function GCModel ctx5 fn_main eq_refl glob5.
Definition ctx6 : Ctxt.ctxt Empty_set Empty_set Empty_set fundef vardef :=
  add_global ctx5 (47%positive, AST.Gfun (AST.Internal fn_main)).
Definition glob_reverse : @denote_glob_ctxt GCModel ctx6 :=
  @denote_glob_ctxt_extend GCModel ctx5
    47%positive (AST.Gfun (AST.Internal fn_main))
    eq_refl d_main glob5.

Lemma denote_allocate_correct : d_allocate = allocate.
Proof. reflexivity. Qed.

Lemma denote_reverse_correct : d_reverse = reverse.
Proof. reflexivity. Qed.

Lemma denote_main_correct : d_main = main.
Proof. reflexivity. Qed.
