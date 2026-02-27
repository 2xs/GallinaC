From Stdlib Require Import PArith.

From MetaRocq.Template Require Import All.

From compcert.common Require AST.

From Utils Require Import ListExt.
From Compiler.Common Require Import Types.
From Compiler.Deep Require Import Cmd Prog.

Local Open Scope bs_scope.

Inductive binding: Set :=
| Param (mr_id: ident) (cc_id: AST.ident) (t: type)
| Temp  (mr_id: ident) (cc_id: AST.ident) (t: type)
| Local (ofst: nat) (t: type)
.

Definition binding_to_string bind: string :=
  match bind with
  | Param mr_id cc_id _ => "Param(" ++ mr_id ++ ", " ++ string_of_positive cc_id ++ ")"
  | Temp mr_id cc_id _ => "Temp(" ++ mr_id ++ ", " ++ string_of_positive cc_id ++ ")"
  | Local ofst _ => "Local(" ++ string_of_nat ofst ++ ")"
  end.

Record reify_program_env :=
  {
    next_id : AST.ident;
    funs : list (ident * (AST.ident * function));
    current_module : modpath;
  }.

Definition init_reify_env module : reify_program_env := {| next_id := 1%positive; funs := []; current_module := module; |}.

Record reify_funbody_env: Type :=
  {
    prog_renv :> reify_program_env;
    stack: list binding;
    stack_depth: nat;
    temps: list (AST.ident * type);
  }.

Definition reify_funbody_env_to_string (renv: reify_funbody_env): string :=
  ">>>>>>>>>>" ++ nl ++
    ("next_id: " ++ string_of_positive renv.(next_id) ++ nl) ++
    ("stack: [ " ++ List.fold_left (fun acc b => acc ++ binding_to_string b ++ ", ") renv.(stack) "" ++ " ]" ++ nl) ++
    ("stack_depth: " ++ string_of_nat renv.(stack_depth) ++ nl) ++
    ("funs: [ " ++ List.fold_left (fun acc '(i0, (i1, t)) => acc ++ i0 ++ " " ++ string_of_positive i1 ++ ", ") renv.(funs) "" ++ " ]" ++ nl) ++
    "<<<<<<<<<<"
.

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
Definition resolve_rel_fun renv := resolve_rel renv.(funs).
Definition resolve_named_temp renv nm :=
  match List.find (match_name nm) renv.(stack) with
  | (Some (Param _ id _ | Temp _ id _)) as x => Some id
  | _ => None
  end.
Definition resolve_named_fun renv nm := ListExt.sfind StringOTOrig.eq_dec nm renv.(funs).
Fixpoint resolve_rel_locali st n :=
  match st, n with
  | [], _ => None
  | Local ofst _::_, 0 => Some ofst
  | _, 0 => None
  | _::st, S n => resolve_rel_locali st n
  end.
Definition resolve_rel_local renv := resolve_rel_locali renv.(stack).

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
    |},
    renv.(next_id)).

Definition push_local (renv: reify_funbody_env) type : reify_funbody_env :=
    {|
      prog_renv := renv;
      stack := Local renv.(stack_depth) type::renv.(stack);
      stack_depth := S renv.(stack_depth);
      temps := renv.(temps)
    |}.

Definition drop_temp (renv: reify_funbody_env) temp_id: reify_funbody_env :=
  {|
    prog_renv := renv;
    stack := pop_until_temp renv.(stack) temp_id;
    stack_depth := renv.(stack_depth);
    temps := renv.(temps);
  |}.

Definition drop_local (renv: reify_funbody_env): reify_funbody_env :=
  {|
    prog_renv := renv;
    stack := pop_local renv.(stack);
    stack_depth := Nat.pred renv.(stack_depth);
    temps := renv.(temps);
  |}.

Definition push_fun (renv: reify_program_env) mr_id f :=
  {|
    next_id := Pos.succ renv.(next_id);
    funs := (mr_id, (renv.(next_id), f))::renv.(funs);
    current_module := renv.(current_module);
  |}.
