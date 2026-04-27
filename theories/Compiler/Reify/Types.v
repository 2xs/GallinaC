From MetaRocq.Template Require Import All.

From GallinaC.Utils Require Import ListExt.

From GallinaC.Compiler.Common Require Export Types.

Import MonadNotation.
Local Open Scope bs_scope.

Module E_reify_type.
  Definition not_base_type := "Error in reify_type: not a base type.".

  Definition first_class_use_of_program := "You are probably trying to manipulate a program (command/function/procedure) as a first-class value. Doing so is forbidden as it would allow building (escaping) closures which are currently not supported (and will likely never be in scope).".

End E_reify_type.

Polymorphic Definition translate_storable (tm: term): TemplateMonad type :=
  match tm with
  | tConst (_, "ptr_storable") [] => tmReturn t_ptr
  | tConst (_, "nat_storable") [] => tmReturn t_nat
  | _ =>
      tmBind
        (tmPrint tm)
        (fun _ => tmFail "Error in reify_storable")
  end.

Polymorphic Definition translate_type (tm : term) : TemplateMonad type :=
  match tm with
  | tInd {| inductive_mind := (x, "unit") |} [] => tmReturn t_unit
  | tInd {| inductive_mind := (_, "bool") |} [] => tmReturn t_bool
  | tInd {| inductive_mind := (_, "nat") |} [] => tmReturn t_nat
  | (tConst (MPdot (MPfile ["BinNatDef"; "NArith"; "Stdlib"]) "N", "t") []) => tmReturn t_ofst
  | (tConst (MPdot (MPfile ("Pointer"::_)%list) "Pointer", "t") []%list) =>
      tmReturn t_ptr
  | tApp (tConst (MPfile ("Memval"::_), "obj") []) [storable] =>
      translate_storable storable
  (* Commented out for now because compilation time increases exponentially with match cases *)
  (* | tApp (tConst (_, "program") []) _ => *)
  (*     tmBind *)
  (*       (tmPrint tm) *)
  (*       (fun _ => tmFail (E_reify_type.not_base_type ++ " " ++ E_reify_type.first_class_use_of_program)) *)
  | _ =>
      tmBind
        (tmPrint tm)
        (fun _ => tmFail (E_reify_type.not_base_type ++ " Unknown context, good luck."))
  end.

Polymorphic Fixpoint translate_signature (sig: term): TemplateMonad (list (string * type) * type) :=
  match sig with
  | tApp (tConst (modpath, "program") []) [State; t_out] =>
      t_out <- translate_type t_out;;
      tmReturn ([], t_out)
  | tPro arg t_arg sig =>
      t_arg <- translate_type t_arg;;
      '(args, t_out) <- translate_signature sig;;
      tmEval cbv ((arg, t_arg)::args, t_out)
  | _ =>
      tmPrint sig;;
      tmFail "translate_signature: not a signature"
  end.

(* Notes for future self, our lookup is currently very crude *)
(* tInd is actually just a "smart identifier", i.e. it says little more than that there exists an inductive at a given path *)
(* to find more about this inductive, we need lookup_inductive *)
(* Provided a global environment it gives us (potentially):
 * - the mutual_inductive_body: the "full body" of the inductive, recall multiple mutually recursive inductives can be defined with Inductive I1 ... with I2 ...
 * - the one_inductive_body: the actual definition about the inductive we care about
 * If we want to support "light ADT", we will have to hook into this machinery
 *)

Definition reify_type (ident : string) (A : Type) : TemplateMonad type :=
  tm <- tmQuote A ;;
  t <- translate_type tm;;
  tmDefinition ident t.
