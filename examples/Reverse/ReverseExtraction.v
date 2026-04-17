From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Examples.Reverse Require Import ReverseReify.
From Compiler Require Import Driver.

Extraction Language OCaml.

Set Warnings "-extraction".
Set Extraction Output Directory "./extraction".

Unset Printing Notations.
Set Printing Implicit.

(* "Compile-time" configuration *)
Extract Constant Compiler.print_Clight => "(fun _ -> ())".
Extract Constant Compiler.print_Cminor => "(fun _ -> ())".
Extract Constant Compiler.print_RTL => "(fun _ -> ())".
Extract Constant Compiler.print_LTL => "(fun _ -> ())".
Extract Constant Compiler.print_Mach => "(fun _ -> ())".
Extract Constant Compiler.print => "fun (f: 'a -> unit) (x: 'a) -> f x; x".
Extract Constant Compiler.time  => "(fun _ f x -> f x)".
Extract Constant Archi.win64 => "false".
Extract Constant SelectOp.symbol_is_relocatable =>
  "match Configuration.system with
    | ""macos"" -> C2C.atom_is_external
    | ""cygwin"" -> if Archi.ptr64 then C2C.atom_is_external else (fun _ -> false)
    | _ -> C2C.atom_needs_GOT_access".
Extract Constant Compopts.optim_for_size => "(fun () -> false)".
Extract Constant Compopts.propagate_float_constants => "(fun () -> true)".
Extract Constant Compopts.generate_float_constants => "(fun () -> true)".
Extract Constant Compopts.va_strict => "(fun () -> false)".
Extract Constant Compopts.optim_tailcalls => "(fun () -> true)".
Extract Constant Compopts.optim_constprop => "(fun () -> true)".
Extract Constant Compopts.optim_CSE => "(fun () -> true)".
Extract Constant Compopts.optim_redundancy => "(fun () -> true)".
Extract Constant Compopts.debug => "(fun () -> true)".
Extract Constant RTLgen.more_likely => "(fun _ _ _ => true)".

(* "Optimizations" of the extracted code *)
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

Extract Inlined Constant ListDef.map => "List.map".

Extraction Inline Archi.ptr64 AST.Mptr AST.Xsize_t.
Extraction Inline EquivDec.EqDec EquivDec.equiv_dec Classes.EqDec.
Extraction Inline Errors.bind Errors.bind2.

Extract Inductive bool => "bool" [ "true" "false" ].

Extraction Blacklist List String Int.

Separate Extraction ReverseReify.deep_reverse_prog Driver.transf_gc_program Compiler.transf_cminor_program.
