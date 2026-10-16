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

(* Stub for the CompCert command-line flags facilities *)

val option_small_const : int ref

val option_small_data : int ref

val option_dalloctrace : bool ref

val option_g : bool ref

val option_ffpu : bool ref

val option_fcommon : bool ref

val option_S : bool ref

val option_dasm : bool ref

val option_fpic : bool ref

val option_fpie : bool ref

val option_flongdouble : bool ref

val option_fstruct_passing : bool ref

val option_interp : bool ref

val option_funprototyped : bool ref

val option_fvararg_calls : bool ref

val option_finline_asm : bool ref

val main_function_name : string ref

val option_falignfunctions : int option ref

val option_gdwarf : int ref
