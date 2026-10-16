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

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From GallinaC.Examples.Reverse Require Import ReverseReify.
From GallinaC.Compiler Require Import Driver.

From compcert.lib Require Import Floats.

Extraction Language OCaml.

From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNativeString.

Set Warnings "-extraction".
Set Extraction Output Directory "./extraction".

Unset Printing Notations.
Set Printing Implicit.

(* "Compile-time" configuration *)
Extract Constant Compiler.print_Clight => "(fun _ -> ())".
Extract Constant Compiler.print_Cminor => "PrintCminor.print_if".
Extract Constant Compiler.print_RTL => "PrintRTL.print_if".
Extract Constant Compiler.print_LTL => "PrintLTL.print_if".
Extract Constant Compiler.print_Mach => "PrintMach.print_if".
Extract Constant Compiler.print => "fun (f: 'a -> unit) (x: 'a) -> f x; x".

Extract Constant Compiler.time  => "(fun _ f x -> f x)".
Extract Constant Archi.win64 => "false".
Extract Constant SelectOp.symbol_is_relocatable => "(fun _ -> false)".
(* Always false for now, for comparision, here is the CompCert code *)
(* Also consider: `cfrontend/C2C.ml` and `x86/SelectOp.v` *)
(* match Configuration.system with *)
(*   | "macos" -> C2C.atom_is_external *)
(*   | "cygwin" -> if Archi.ptr64 then C2C.atom_is_external else (fun _ -> false) *)
(*   | _ -> C2C.atom_needs_GOT_access *)
Extract Constant Compopts.optim_for_size => "(fun () -> false)".
Extract Constant Compopts.propagate_float_constants => "(fun () -> true)".
Extract Constant Compopts.generate_float_constants => "(fun () -> true)".
Extract Constant Compopts.va_strict => "(fun () -> false)".
Extract Constant Compopts.optim_tailcalls => "(fun () -> true)".
Extract Constant Compopts.optim_constprop => "(fun () -> true)".
Extract Constant Compopts.optim_CSE => "(fun () -> true)".
Extract Constant Compopts.optim_redundancy => "(fun () -> true)".
Extract Constant Compopts.debug => "(fun () -> true)".

(* Untrusted functions from CompCert *)
Extract Constant RTLgen.more_likely => "(fun _ _ _ -> true)".
Extract Inlined Constant Compiler.print_RTL => "(fun _ _ -> ())".
Extract Inlined Constant Linearize.enumerate_aux => "Linearizeaux.enumerate_aux".
Extract Inlined Constant Inlining.inlining_info => "unit".
Extract Inlined Constant Inlining.inlining_analysis => "(fun _ -> ())".
Extract Inlined Constant Inlining.should_inline => "(fun _ _ _ -> false)".
Extract Inlined Constant Selection.if_conversion_heuristic => "(fun _ _ _ _ _ _ -> false)".
Extract Inlined Constant Allocation.regalloc => "Regalloc.regalloc".
Extract Inlined Constant Selection.compile_switch => "(fun _ _ _ -> failwith ""Switches unsupported"")".

(* "Optimizations" of the extracted code *)
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".
Extract Inlined Constant ListDef.map => "List.map".

Extraction Inline AST.Mptr AST.Xsize_t.
Extraction Inline EquivDec.EqDec EquivDec.equiv_dec Classes.EqDec.
Extraction Inline Errors.bind Errors.bind2.

Extract Inductive bool => "bool" [ "true" "false" ].

Extraction Blacklist List String Int.

Separate Extraction
  ReverseReify.deep_reverse_prog ReverseReify.deep_reverse_prog_symbols
  Driver.transf_gc_program
  Compiler.transf_cminor_program
  Initializers.transl_init Initializers.constval
  Ctypes.merge_attributes Ctypes.remove_attributes Ctypes.build_composite_env Ctypes.layout_struct Ctypes.make_program Ctypes.signature_of_type Ctypes.type Ctypes.fundef
  Ctyping.size_t Ctyping.econst_single Ctyping.econst_float Ctyping.evalof Ctyping.econst_long Ctyping.econst_int Ctyping.esizeof Ctyping.ealignof Ctyping.eunop Ctyping.ebinop Ctyping.eaddrof Ctyping.epreincr Ctyping.epredecr Ctyping.epostincr Ctyping.epostdecr Ctyping.eassign Ctyping.eassignop Ctyping.ecomma Ctyping.ecall Ctyping.ebuiltin Ctyping.eselection Ctyping.eseqand Ctyping.eseqor Ctyping.econdition Ctyping.ecast Ctyping.ederef Ctyping.efield
  Ctyping.sdo Ctyping.sifthenelse Ctyping.swhile Ctyping.sdowhile Ctyping.sfor Ctyping.sswitch
  Csyntax.Eindex Csyntax.Epreincr Csyntax.Eselection Csyntax.Sskip Csyntax.function Csyntax.type_of_function
  Clight.function
  AST.signature_main
  Float.of_bits Float.to_bits Float.from_parsed
  Float32.of_bits Float32.to_bits Float32.from_parsed
  Machregs.is_stack_reg Machregs.two_address_op Machregs.mregs_for_operation Machregs.mregs_for_builtin Machregs.destroyed_at_indirect_call
  Conventions1.is_float_reg Conventions1.allocatable_registers Conventions1.dummy_int_reg Conventions1.dummy_float_reg Conventions1.callee_save_type.
