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

From MetaRocq.Template Require Import All.

From GallinaC.Utils Require Import ListExt MetaRocqExt.

From GallinaC.Compiler.Common Require Import Types.
From GallinaC.Compiler.Reify Require Export Env.

Local Open Scope bs_scope.

Polymorphic Inductive ModuleResolution :=
| CoreInitDatatypes | CoreInitPrelude | CoreNumbersBinNums
| StdNArithBinNatDef
| ImpMonad | ImpPrimitives | ImpWhile
| ImpHeap | ImpHeapPtr | ImpStateState | ImpStorableStorable | ImpValue
| ImpIntopsIntCarrier
| ImpIntopsUnsigned | ImpUint32
| ModelsPointerPointer
| CurrentModule | Other.

Polymorphic Definition resolve_modpath_simple (path: modpath): ModuleResolution :=
  match path with
  | MPfile ["Datatypes"; "Init"; "Corelib"] => CoreInitDatatypes
  | MPfile ["Prelude"; "Init"; "Corelib"] => CoreInitPrelude
  | MPfile ["BinNums"; "Numbers"; "Corelib"] => CoreNumbersBinNums
  | MPdot (MPfile ["BinNatDef"; "NArith"; "Stdlib"]) "N" => StdNArithBinNatDef
  | MPfile ["Monad"; "Imp"; "GallinaC"] => ImpMonad
  | MPfile ["Primitives"; "Imp"; "GallinaC"] => ImpPrimitives
  | MPfile ["While"; "Imp"; "GallinaC"] => ImpWhile
  | MPfile ["Heap"; "Imp"; "GallinaC"] => ImpHeap
  | MPdot (MPfile ["Heap"; "Imp"; "GallinaC"]) "Ptr" => ImpHeapPtr
  | MPdot (MPfile ["State"; "Imp"; "GallinaC"]) "State" => ImpStateState
  | MPdot (MPfile ["Storable"; "Imp"; "GallinaC"]) "Storable" => ImpStorableStorable
  | MPfile ["Value"; "Imp"; "GallinaC"] => ImpValue
  | MPdot (MPfile ["Intops"; "Imp"; "GallinaC"]) "IntCarrier" => ImpIntopsIntCarrier
  | MPdot (MPfile ["Intops"; "Imp"; "GallinaC"]) "Unsigned" => ImpIntopsUnsigned
  | MPfile ["Uint32"; "Imp"; "GallinaC"] => ImpUint32
  | MPdot (MPfile ["Pointer"; "Models"; "GallinaC"]) "Pointer" => ModelsPointerPointer
  | _ => Other
  end.

Polymorphic Definition resolve_modpath_ext (renv: reify_program_env) (path: modpath): ModuleResolution :=
  match resolve_modpath_simple path with
  | Other =>
      match ModPathComp.compare path renv.(current_module) with
      | Eq => CurrentModule
      | _ => Other
      end
  | path => path
  end.

Polymorphic Inductive MonadPrimitive := Bind | Ret.

Polymorphic Definition resolve_monad_primitive (prim: ident) : option MonadPrimitive :=
  match prim with
  | "bind" => Some Bind
  | "ret" => Some Ret
  | _ => None
  end.

Polymorphic Inductive GallinaCPrimitive :=
| WithVar | ReadVar | WriteVar
| AllocPtr | ReadPtr | WritePtr | FreePtr
| EqPtr | ShiftFWPtr | ShiftBWPtr
| While
.

Polymorphic Definition resolve_gallinac_primitive (prim: ident) : option GallinaCPrimitive :=
  match prim with
  | "with_var" => Some WithVar
  | "read_var"  => Some ReadVar
  | "write_var" => Some WriteVar
  | "alloc_ptr" => Some AllocPtr
  | "read_ptr" => Some ReadPtr
  | "write_ptr" => Some WritePtr
  | "free_ptr" => Some FreePtr
  | "eq_ptr" => Some EqPtr
  | "shift_fw_ptr" => Some ShiftFWPtr
  | "shift_bw_ptr" => Some ShiftBWPtr
  | "while" => Some While
  | _ => None
  end.

Polymorphic Inductive NumericPrimitive := Mdl | Div.

Polymorphic Definition resolve_numeric_primitive (prim: ident): option NumericPrimitive :=
  match prim with
  | "mdl" => Some Mdl
  | "div" => Some Div
  | _ => None
  end.

Polymorphic Definition resolve_prim_inductive (ind: inductive) : option type :=
  match resolve_modpath_simple (fst ind.(inductive_mind)) with
  | CoreInitDatatypes =>
      match snd ind.(inductive_mind) with
      | "unit" => Some t_unit
      | "nat" => Some t_nat
      | "bool" => Some t_bool
      | _ => None
      end
  | CoreNumbersBinNums =>
      match snd ind.(inductive_mind) with
      | "N" => Some t_ofst
      | _ => None
      end
  | _ => None
  end.

Polymorphic Inductive PrimExpr := NullPtr | Negb | Add | Eqb | Mul.

Polymorphic Definition resolve_expr_name (nm: ident): option PrimExpr :=
  match nm with
  | "NULL" => Some NullPtr
  | "null" => Some NullPtr
  | "negb" => Some Negb
  | "add" => Some Add
  | "eqb" => Some Eqb
  | "mul" => Some Mul
  | _ => None
  end.

Polymorphic Definition resolve_expr (kname: kername) : option PrimExpr :=
  match resolve_modpath_simple (fst kname) with
  | ImpHeap | ModelsPointerPointer =>
      match resolve_expr_name (snd kname) with
      | Some NullPtr => Some NullPtr
      | _ => None
      end
  | CoreInitDatatypes =>
      match resolve_expr_name (snd kname) with
      | Some Negb => Some Negb
      | _ => None
      end
  | ImpIntopsUnsigned =>
      match resolve_expr_name (snd kname) with
      | Some Add => Some Add
      | Some Eqb => Some Eqb
      | Some Mul => Some Mul
      | _ => None
      end
  | _ => None
  end.

Polymorphic Inductive storable :=
| UnitStorable | BoolStorable | NatStorable | OfstStorable | PtrStorable.

Polymorphic Inductive intkind := U32.

Polymorphic Inductive canstruct :=
| Storable: storable -> canstruct
| IntKind: intkind -> canstruct.

Polymorphic Definition resolve_canstruct_name (nm: ident): option canstruct :=
  sfind nm
    [("nat_uint32_t", IntKind U32);
     ("Datatypes_unit__canonical__Storable_Storable", Storable UnitStorable);
     ("Datatypes_bool__canonical__Storable_Storable", Storable BoolStorable);
     ("Datatypes_nat__canonical__Storable_Storable", Storable NatStorable);
     ("BinNums_N__canonical__Storable_Storable", Storable OfstStorable);
     ("Ptr_sort__canonical__Storable_Storable", Storable PtrStorable)].

Polymorphic Fixpoint resolve_int (tm: term): option intkind :=
  match tm with
  | tConst kname [] =>
      match resolve_modpath_simple (fst kname) with
      | ImpUint32 =>
          match resolve_canstruct_name (snd kname) with
          | Some (IntKind U32) => Some U32
          | _ => None
          end
      | ImpIntopsUnsigned =>
          None
      | _ => None
      end
  | tApp f args =>
      match f with
      | tConst kname [] =>
          match resolve_modpath_simple (fst kname) with
          | ImpIntopsUnsigned =>
              match snd kname with
              | "carrier" =>
                  match args with [arg] => resolve_int arg | _ => None end
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Polymorphic Definition resolve_storable_kername (kname: kername): option storable :=
  match resolve_canstruct_name (snd kname) with
  | Some (Storable storable) => Some storable
  | _ => None
  end.

Polymorphic Definition resolve_storable (tm: term): option storable :=
  match tm with
  | tConst kname [] => resolve_storable_kername kname
  | tApp (tConst kname []) _ => resolve_storable_kername kname
  | _ => None
  end.

Polymorphic Definition resolve_storable_type (s: storable): type :=
  match s with
  | UnitStorable => t_unit
  | BoolStorable => t_bool
  | NatStorable => t_nat
  | OfstStorable => t_ofst
  | PtrStorable => t_ptr
  end.

Polymorphic Definition resolve_int_kind_type (i: intkind): type :=
  match i with
  | U32 => t_nat
  end.

Polymorphic Definition resolve_prim_type (tm: term): option type :=
  match tm with
  | tConst kname [] =>
      match resolve_modpath_simple (fst kname) with
      | ModelsPointerPointer =>
          match snd kname with "t" => Some t_ptr | _ => None end
      | StdNArithBinNatDef =>
          match snd kname with "t" => Some t_ofst | _ => None end
      | _ => None
      end
  | tInd ind [] => resolve_prim_inductive ind
  | tApp (tConst kname []) args =>
      match resolve_modpath_simple (fst kname) with
      | ImpStorableStorable =>
          match snd kname with
          | "sort" =>
              match args with
              | [_; arg] =>
                  match resolve_storable arg with
                  | Some s => Some (resolve_storable_type s)
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      | ImpHeapPtr =>
          match snd kname with
          | "sort" =>
              match args with [_; _] => Some t_ptr | _ => None end
          | _ => None
          end
      | ImpIntopsIntCarrier =>
          match snd kname with
          | "carrier" =>
              match args with
              | [arg] =>
                  match resolve_int arg with
                  | Some kint => Some (resolve_int_kind_type kint)
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition match_name nm b :=
  match b with
  | Param mr_id _ _ | Temp mr_id _ _ => if IdentOTOrig.eq_dec mr_id nm then true else false
  | _ => false
  end.
Definition resolve_rel [A: Type] := @List.nth_error A.
Definition resolve_rel_temp renv n :=
  match resolve_rel renv.(stack) n with
  | (Some (Param _ id _ | Temp _ id _)) as x => Some id
  | _ => None
  end.
(* Definition resolve_rel_fun renv := resolve_rel renv.(funs). *)
Definition resolve_named_temp renv nm :=
  match List.find (match_name nm) renv.(stack) with
  | (Some (Param _ id _ | Temp _ id _)) as x => Some id
  | _ => None
  end.
Definition resolve_named_internal renv nm :=
  match ListExt.sfind nm renv.(funs) with
  | Some (id, AST.Internal f) => Some (id, f)
  | _ => None
  end.
Definition resolve_named_external renv nm: option (AST.ident * AST.external_function) :=
  match ListExt.sfind nm renv.(funs) with
  | Some (id, AST.External f) => Some (id, f)
  | _ => None
  end.

Fixpoint resolve_rel_locali st n :=
  match st, n with
  | [], _ => None
  | Local ofst _::_, 0 => Some ofst
  | _, 0 => None
  | _::st, S n => resolve_rel_locali st n
  end.

Notation resolve_rel_local renv := (resolve_rel_locali renv.(stack)).

Polymorphic Definition resolve_type_kername (kname: kername): option ModuleResolution :=
  match resolve_modpath_simple (fst kname), snd kname with
  | ImpStateState, "type" => Some ImpStateState
  | CoreInitPrelude, "reverse_coercion" => Some CoreInitPrelude
  | _, _ => None
  end.

Definition strip_reverse_coercion (tm: term): term :=
  match tm with
  | tApp (tConst kn _) [_; _; _; tm'] =>
      match resolve_type_kername kn with
      | Some CoreInitPrelude => tm'
      | _ => tm
      end
  | _ => tm
  end.

Definition is_state_structure (tm: term): bool :=
  match tm with
  | tInd {| inductive_mind := kn; inductive_ind := 0 |} [] =>
      match resolve_type_kername kn with
      | Some ImpStateState => true
      | _ => false
      end
  | _ => false
  end.

Definition model_of_state (tm: term): ModelRef :=
  match strip_reverse_coercion tm with
  | tInd {| inductive_mind := kn |} _ => ModelKn kn
  | tConst kn _ => ModelKn kn
  | _ => ModelUnknown
  end.

Definition is_model_term (renv: reify_funbody_env) (tm: term): bool :=
  match renv.(model) with
  | ModelParam =>
      match tm with
      | tRel i => Nat.eqb i (List.length renv.(stack))
      | _ => false
      end
  | ModelKn kn =>
      match strip_reverse_coercion tm with
      | tInd ind _ => Kernames.eq_kername ind.(inductive_mind) kn
      | tConst kn' _ => Kernames.eq_kername kn' kn
      | _ => false
      end
  | ModelUnknown => false
  end.

Definition drop_model_arg (renv: reify_funbody_env) (args: list term): list term :=
  match args with
  | tm::args' => if is_model_term renv tm then args' else args
  | [] => args
  end.
