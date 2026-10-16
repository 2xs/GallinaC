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

let option_small_const = ref 0

let option_small_data = ref 0

let option_dalloctrace = ref false

let option_g = ref true

let option_ffpu = ref true

let option_fcommon = ref true

let option_S = ref false

let option_dasm = ref false

let option_fpic = ref false

let option_fpie = ref false

let option_flongdouble = ref false

let option_fstruct_passing = ref false

let option_interp = ref false

let option_funprototyped = ref false

let option_fvararg_calls = ref true

let option_finline_asm = ref true

let main_function_name = ref "main"

let option_falignfunctions = ref (None : int option)

let option_gdwarf = ref 3
