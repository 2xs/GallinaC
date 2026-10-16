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

From Stdlib Require Import PArith Bool.

From compcert.common Require AST.

From GallinaC.Utils Require Import ListExt.
From GallinaC.Compiler.IR Require Import Cmd Prog.

Fixpoint chain_check (aliases: list AST.ident) (c: cmd): bool :=
  match c with
  | c_ret (e_var y) _ => existsb (Pos.eqb y) aliases
  | c_bind y _ c1 c2 _ => chain_check aliases c1 && chain_check (y :: aliases) c2
  | _ => false
  end.

Fixpoint transf_cmd (tail: bool) (c: cmd): cmd :=
  match c with
  | c_bind x t_b (c_app f t_out args) c_c t_c =>
      if tail && chain_check [x] c_c && type_eqb t_out t_c
      then c_app f t_out args
      else c_bind x t_b (c_app f t_out args) (transf_cmd tail c_c) t_c
  | c_bind x t_b c_b c_c t_c =>
      c_bind x t_b (transf_cmd false c_b) (transf_cmd tail c_c) t_c
  | c_if e c1 c2 t =>
      c_if e (transf_cmd tail c1) (transf_cmd tail c2) t
  | c_while c_cond id_cond c_body id_body =>
      c_while (transf_cmd false c_cond) id_cond (transf_cmd false c_body) id_body
  | _ => c
  end.

Definition rewrite_guard (tail: bool) (x: AST.ident) (c_b c_c: cmd) (t_c: type): bool :=
  match c_b with
  | c_app _ t_out _ => tail && chain_check [x] c_c && type_eqb t_out t_c
  | _ => false
  end.

Definition transf_function (f: function): function :=
  {|
    fn_return := f.(fn_return);
    fn_params := f.(fn_params);
    fn_temps := f.(fn_temps);
    fn_internals := f.(fn_internals);
    fn_body := transf_cmd true f.(fn_body);
    fn_extra := f.(fn_extra);
  |}.

Definition transf_fundef (fd: fundef): fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program): program :=
  {|
    prog_defs := List.map (AST.transform_program_globdef transf_fundef) p.(prog_defs);
    prog_public := p.(prog_public);
    prog_main := p.(prog_main);
    prog_extra := p.(prog_extra);
  |}.
