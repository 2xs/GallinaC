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

From Stdlib Require Import PArith.
From Stdlib Require Import Strings.String.

From MetaRocq.Template Require Import All.

From compcert.common Require AST.
From compcert.backend Require Import SplitLong(sig_f_l, sig_l_f, sig_l_s, sig_ll_l, sig_li_l).

From GallinaC.Utils Require Import ListExt.
From GallinaC.Compiler.Common Require Import Types.
From GallinaC.Compiler.Deep Require Import Cmd Prog.

Import MonadNotation.
Local Open Scope bs_scope.

Inductive binding: Set :=
| Param (mr_id: ident) (cc_id: AST.ident) (t: type)
| Temp  (mr_id: ident) (cc_id: AST.ident) (t: type)
| Local (ofst: nat) (t: type)
.

Record reify_program_env :=
  {
    next_id : AST.ident;
    funs : list (kername * (AST.ident * fundef));
    current_module : modpath;
  }.

Definition init_reify_env module : reify_program_env :=
  {|
    next_id := 18%positive;
    funs := List.rev
      [ ((MPfile [], "malloc"), (1%positive, AST.External AST.EF_malloc));
        ((MPfile [], "free"), (2%positive, AST.External AST.EF_free));
        ((MPfile [], "__compcert_i64_dtos"),
          (3%positive, AST.External (AST.EF_runtime "__compcert_i64_dtos"%string sig_f_l)));
        ((MPfile [], "__compcert_i64_dtou"),
          (4%positive, AST.External (AST.EF_runtime "__compcert_i64_dtou"%string sig_f_l)));
        ((MPfile [], "__compcert_i64_stod"),
          (5%positive, AST.External (AST.EF_runtime "__compcert_i64_stod"%string sig_l_f)));
        ((MPfile [], "__compcert_i64_utod"),
          (6%positive, AST.External (AST.EF_runtime "__compcert_i64_utod"%string sig_l_f)));
        ((MPfile [], "__compcert_i64_stof"),
          (7%positive, AST.External (AST.EF_runtime "__compcert_i64_stof"%string sig_l_s)));
        ((MPfile [], "__compcert_i64_utof"),
          (8%positive, AST.External (AST.EF_runtime "__compcert_i64_utof"%string sig_l_s)));
        ((MPfile [], "__compcert_i64_sdiv"),
          (9%positive, AST.External (AST.EF_runtime "__compcert_i64_sdiv"%string sig_ll_l)));
        ((MPfile [], "__compcert_i64_udiv"),
          (10%positive, AST.External (AST.EF_runtime "__compcert_i64_udiv"%string sig_ll_l)));
        ((MPfile [], "__compcert_i64_smod"),
          (11%positive, AST.External (AST.EF_runtime "__compcert_i64_smod"%string sig_ll_l)));
        ((MPfile [], "__compcert_i64_umod"),
          (12%positive, AST.External (AST.EF_runtime "__compcert_i64_umod"%string sig_ll_l)));
        ((MPfile [], "__compcert_i64_shl"),
          (13%positive, AST.External (AST.EF_runtime "__compcert_i64_shl"%string sig_li_l)));
        ((MPfile [], "__compcert_i64_shr"),
          (14%positive, AST.External (AST.EF_runtime "__compcert_i64_shr"%string sig_li_l)));
        ((MPfile [], "__compcert_i64_sar"),
          (15%positive, AST.External (AST.EF_runtime "__compcert_i64_sar"%string sig_li_l)));
        ((MPfile [], "__compcert_i64_umulh"),
          (16%positive, AST.External (AST.EF_runtime "__compcert_i64_umulh"%string sig_ll_l)));
        ((MPfile [], "__compcert_i64_smulh"),
          (17%positive, AST.External (AST.EF_runtime "__compcert_i64_smulh"%string sig_ll_l)))
      ];
    current_module := module; |}.

Inductive ModelRef: Set :=
| ModelParam
| ModelKn (kn: kername)
| ModelUnknown
.

Record reify_funbody_env: Type :=
  {
    prog_renv :> reify_program_env;
    stack: list binding;
    stack_depth: nat;
    temps: list (AST.ident * type);
    model: ModelRef;
  }.

Fixpoint pop_until_temp st id :=
  match st with
  | [] => []
  | Temp id0 id1 t::st =>
      if Pos.eqb id1 id then
        st
      else
        Temp id0 id1 t::(pop_until_temp st id)
  | hd::st =>
      hd::(pop_until_temp st id)
  end.

Fixpoint pop_local st :=
  match st with
  | [] => []
  | Local _ _::st => st
  | hd::st => hd::(pop_local st)
  end.

Definition push_temp (renv: reify_funbody_env) binder type : (reify_funbody_env * positive) :=
  ({|
      prog_renv := {| next_id := Pos.succ renv.(next_id); funs := renv.(funs); current_module := renv.(current_module); |};
      stack := (Temp match binder with
                | nAnon => ""
                | nNamed binder => binder
                  end renv.(next_id) type)::renv.(stack);
      stack_depth := renv.(stack_depth);
      temps := List.app renv.(temps) [(renv.(next_id), type)];
      model := renv.(model);
    |},
    renv.(next_id)).

Definition push_local (renv: reify_funbody_env) type : reify_funbody_env :=
    {|
      prog_renv := renv;
      stack := Local renv.(stack_depth) type::renv.(stack);
      stack_depth := S renv.(stack_depth);
      temps := renv.(temps);
      model := renv.(model);
    |}.

Definition drop_temp (renv: reify_funbody_env) temp_id: reify_funbody_env :=
  {|
    prog_renv := renv;
    stack := pop_until_temp renv.(stack) temp_id;
    stack_depth := renv.(stack_depth);
    temps := renv.(temps);
    model := renv.(model);
  |}.

Definition drop_local (renv: reify_funbody_env): reify_funbody_env :=
  {|
    prog_renv := renv;
    stack := pop_local renv.(stack);
    stack_depth := Nat.pred renv.(stack_depth);
    temps := renv.(temps);
    model := renv.(model);
  |}.

Definition push_fun (renv: reify_program_env) mr_id f :=
  {|
    next_id := Pos.succ renv.(next_id);
    funs := (mr_id, (renv.(next_id), f))::renv.(funs);
    current_module := renv.(current_module);
  |}.
