From MetaRocq.Template Require Import All.

From GallinaC.Utils Require Import ListExt.

From GallinaC.Compiler.Reify Require Export Env.

Local Open Scope bs_scope.

Polymorphic Inductive ModuleResolution :=
| CoreInitDatatypes
| ImpMonad | ImpPrimitives | ImpWhile | ImpPointerPointer
| CurrentModule | Other.

Polymorphic Definition resolve_modpath (renv: reify_program_env) (path: modpath): ModuleResolution :=
  match path with
  | MPfile ["Datatypes"; "Init"; "Corelib"] => CoreInitDatatypes
  | MPdot (MPfile ["Pointer"; "Imp"; "GallinaC"]) "Pointer" => ImpPointerPointer
  | MPfile ["Monad"; "Imp"; "GallinaC"] => ImpMonad
  | MPfile ["Primitives"; "Imp"; "GallinaC"] => ImpPrimitives
  | MPfile ["While"; "Imp"; "GallinaC"] => ImpWhile

  | path =>
      match ModPathComp.compare path renv.(current_module) with
      | Eq => CurrentModule
      | _ => Other
      end
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
  | "free_ptr" => Some WritePtr
  | "eq_ptr" => Some EqPtr
  | "shift_fw_ptr" => Some ShiftFWPtr
  | "shift_bw_ptr" => Some ShiftBWPtr
  | "while" => Some While
  | _ => None
  end.

Polymorphic Inductive PrimTypes := TUnit | TBool | TNat | TN.

Polymorphic Definition resolve_expr_inductive (ind: inductive) : option PrimTypes :=
  match ind.(inductive_mind) with
  | (_, "unit") => Some TUnit
  | (_, "bool") => Some TBool
  | (_, "nat")  => Some TNat
  | (_, "N")    => Some TN
  | _ => None
  end.

Polymorphic Inductive PrimExpr := NullPtr | Negb | NatAdd | NatEqb.

Polymorphic Definition resolve_expr_name (nm: ident): option PrimExpr :=
  match nm with
  | "NULL" => Some NullPtr
  | "negb" => Some Negb
  | _ => None
  end.


Polymorphic Definition resolve_expr (renv: reify_program_env) (kname: kername) : option PrimExpr :=
  match resolve_modpath renv (fst kname) with
  | ImpPointerPointer =>
      match resolve_expr_name (snd kname) with
      | Some NullPtr => Some NullPtr
      | _ => None
      end
  | CoreInitDatatypes =>
      match resolve_expr_name (snd kname) with
      | Some Negb => Some Negb
      | _ => None
      end
  | _ => None
  end.
