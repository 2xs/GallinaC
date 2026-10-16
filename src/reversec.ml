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

open ReverseReify

let rec positive_fmt: BinNums.positive -> string =
  function
  | BinNums.Coq_xI p -> "I" ^ (positive_fmt p)
  | BinNums.Coq_xO p -> "O" ^ (positive_fmt p)
  | BinNums.Coq_xH -> "H"


let compile_reverse () =
  List.iter
    (fun (s,p) ->
       Hashtbl.add Camlcoq.atom_of_string s p;
       Hashtbl.add Camlcoq.string_of_atom p s)
    deep_reverse_prog_symbols;
  let set_dest dst ext = dst := Some ("build/reverse" ^ ext) in
  set_dest PrintCminor.destination ".cm";
  (* set_dest PrintRTL.destination ".rtl"; *)
  (* set_dest Regalloc.destination_alloctrace ".alloctrace"; *)
  (* set_dest PrintLTL.destination ".ltl"; *)
  (* set_dest PrintMach.destination ".mach"; *)
  match Compiler.apply_partial
          (Driver.transf_gc_program deep_reverse_prog)
          Asmexpand.expand_program
  with
  | Errors.OK prog ->
    let oc = open_out "./build/reverse.S" in
    PrintAsm.print_program oc prog;
    close_out oc
  | Errors.Error msg ->
    List.iter
      (function
        | Errors.MSG msg -> Format.printf "MSG %s\n" msg
        | Errors.CTX p -> Format.printf "CTX %s\n" (positive_fmt p)
        | Errors.POS p -> Format.printf "POS %s\n" (positive_fmt p))
      msg;
    failwith "Error while compiling"

let () = compile_reverse ()
