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

From Corelib Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

From Stdlib Require Import ZArith PArith Bool.

From compcert.common Require AST Globalenvs Events.
From compcert.lib Require Import Maps.
Import Globalenvs(Genv.t).

From GallinaC.Utils Require Import ListExt CompCertExt PosExt ProdExt ReflectExt.
From GallinaC.Utils Require Import Algebra.

From GallinaC.Imp Require Import Heap.

From GallinaC.Compiler.Common Require Import Types Value CCInj Ctxt.

Record function (cmd extra: Type): Type :=
  mkfunction
    {
      fn_return: type;
      fn_params: list (AST.ident * type);
      fn_temps: list (AST.ident * type);
      fn_internals: list (AST.ident * type);
      fn_body: cmd;
      fn_extra: extra;
    }.
Arguments fn_return [cmd extra].
Arguments fn_params [cmd extra].
Arguments fn_temps [cmd extra].
Arguments fn_internals [cmd extra].
Arguments fn_body [cmd extra].
Arguments fn_extra [cmd extra].

Definition function_eqb [cmd f_extra: EqDec.type]
  (f1 f2: function cmd f_extra): bool :=
  eqb f1.(fn_return) f2.(fn_return)
  && eqb f1.(fn_params) f2.(fn_params)
  && eqb f1.(fn_temps) f2.(fn_temps)
  && eqb f1.(fn_internals) f2.(fn_internals)
  && eqb f1.(fn_body) f2.(fn_body)
  && eqb f1.(fn_extra) f2.(fn_extra).

Lemma function_eqb_spec {cmd f_extra: EqDec.type}:
  forall x y: @function cmd f_extra, Bool.reflect (x = y) (function_eqb x y).
Proof.
  destruct x as [ ret1 params1 temps1 ints1 body1 extra1 ],
           y as [ ret2 params2 temps2 ints2 body2 extra2 ].
  unfold function_eqb; cbn -[eqb].
  repeat match goal with
  | |- context [ eqb ?x ?y ] => destruct (eqb_spec x y); [ cbn [andb] | right; congruence ]
  end; left; congruence.
Qed.

HB.instance Definition _ (cmd f_extra: EqDec.type) := hasEqDec.Build (@function cmd f_extra) (@function_eqb _ _) function_eqb_spec.

Notation fundef cmd extra := (AST.fundef (function cmd extra)).

Record vardef :=
  mkvardef
    {
      var_type: type;
    }.

Definition vardef_eqb (v1 v2: vardef): bool :=
  type_eqb v1.(var_type) v2.(var_type).

Lemma vardef_eqb_spec: forall x y, Bool.reflect (x = y) (vardef_eqb x y).
Proof.
  destruct x as [ t1 ], y as [ t2 ]; unfold vardef_eqb; cbn.
  destruct (type_eqb_spec t1 t2); constructor; congruence.
Qed.

HB.instance Definition _ := hasEqDec.Build vardef vardef_eqb vardef_eqb_spec.

Record signature: Type :=
  mk_signature
    {
      sig_args: list type;
      sig_res: type;
    }.

Definition signature_eqb (s1 s2: signature) :=
  eqb s1.(sig_args) s2.(sig_args) && eqb s1.(sig_res) s2.(sig_res).

Definition signature_eqb_spec (s1 s2: signature):
  Bool.reflect (s1 = s2) (signature_eqb s1 s2).
Proof.
  destruct s1, s2.
  rewrite /signature_eqb; cbn -[eqb].
  destruct (eqb_spec sig_args0 sig_args1);
    destruct (eqb_spec sig_res0 sig_res1);
    constructor; congruence.
Qed.

HB.instance Definition _ := hasEqDec.Build signature signature_eqb signature_eqb_spec.

Definition signature_of_signature (s: signature): AST.signature :=
  AST.mksignature
    (List.map type_to_xtype (List.filter Types.sized s.(sig_args)))
    (type_to_xtype s.(sig_res))
    AST.cc_default.
Coercion signature_of_signature: signature >-> AST.signature.

Definition fn_signature [cmd extra: Type] (f: function cmd extra): signature :=
  mk_signature
    (List.map snd f.(fn_params))
    f.(fn_return)
.

Inductive exf_funsig: AST.external_function -> signature -> Prop :=
| funsig_external: forall nm sig (SIZED: Forall Types.Sized sig.(sig_args)),
    exf_funsig (AST.EF_external nm (signature_of_signature sig)) sig
| funsig_malloc: exf_funsig AST.EF_malloc {| sig_args := [t_ofst]; sig_res := t_ptr; |}
| funsig_free: exf_funsig AST.EF_free {| sig_args := [t_ptr]; sig_res := t_unit; |}
.

Inductive funsig {cmd extra: Type}: (fundef cmd extra) -> signature -> Prop :=
| funsig_Internal: forall f, funsig (AST.Internal f) (fn_signature f)
| funsig_External: forall ef sig (SIG: exf_funsig ef sig), funsig (AST.External ef) sig
.

Notation globdef cmd extra := (AST.globdef (fundef cmd extra) vardef).

Notation genv cmd extra := (Genv.t (fundef cmd extra) vardef).

Record program (cmd f_extra p_extra: Type) :=
  mkprogram
    {
      prog_defs: list (AST.ident * (globdef cmd f_extra));
      prog_public: list AST.ident;
      prog_main: AST.ident;
      prog_extra: p_extra;
    }.
Arguments mkprogram [cmd f_extra p_extra] .
Arguments prog_defs [cmd f_extra p_extra].
Arguments prog_public [cmd f_extra p_extra].
Arguments prog_main [cmd f_extra p_extra].
Arguments prog_extra [cmd f_extra p_extra].

Definition program_of_program [cmd f_extra p_extra] (p: program cmd f_extra p_extra): AST.program (fundef cmd f_extra) vardef :=
  {|
    AST.prog_defs := p.(prog_defs);
    AST.prog_public := p.(prog_public);
    AST.prog_main := p.(prog_main);
  |}
.
#[global] Coercion program_of_program : program >-> AST.program.

(* ctx is the "global" context *)
(* global should be set to whatever
 * we overwrite stack since it should be empty
 * pure should be empty as well
 *)
#[local] Definition mk_pair_with_false [A: Type] (a: A):= (a,false).
#[local] Definition mk_uninit_pair (idt: AST.ident*type) := (fst idt, mk_pair_with_false (snd idt)).
#[local] Definition mk_pair_with_true [A: Type] (a: A):= (a,true).
#[local] Definition mk_init_pair (idt: AST.ident*type) := (fst idt, mk_pair_with_true (snd idt)).

Definition mk_typing_tree [V: Type] (b: bool) (l: list (AST.ident * V))
  (base: Maps.PTree.t (V * bool)): Maps.PTree.t (V * bool) :=
  List.fold_left (fun c idt => Maps.PTree.set (fst idt) (snd idt, b) c) l base.

(* [mk_function_ctxt params temps internals ctx] creates from a global context a context
for executing a function.

The context creation happens in three steps.

First, params _and_ temps are added to the context as uninitialized.
Second, parameters are set as initialized.
Third, the internals are set as uninitialized.

This two-step initialization is due to how Denotation works. If you change
this, expect breakage in Denotation.v and Agree.v *)
Definition mk_function_ctxt [cmd f_extra] (params: list (AST.ident * type)) (temps: list (AST.ident * type)) (internals: list (AST.ident * type)) (ctx: ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef): ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef :=
  Ctxt.with_internal
    (mk_typing_tree false internals Maps.PTree.Empty)
    (Ctxt.with_pure
       (mk_typing_tree true params (mk_typing_tree false (params ++ temps) Maps.PTree.Empty))
       (Ctxt.with_stack [] ctx)).

Definition mk_glob_ctxt [cmd f_extra p_extra] (p: program cmd f_extra p_extra): ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef :=
  with_global (Globalenvs.Genv.globalenv p) (ctxt_emp Empty_set Empty_set Empty_set Empty_set Empty_set []).

Definition exf_bound [P I S F GV] (ef: AST.external_function)
  (ctx: ctxt P I S (AST.fundef F) GV): Prop :=
  exists id, Ctxt.get_global id ctx = Some (AST.Gfun (AST.External ef)).

Definition unique_exf [F V] (ef: AST.external_function)
  (defs: list (AST.ident * AST.globdef (AST.fundef F) V)): Prop :=
  forall id id', In (id, AST.Gfun (AST.External ef)) defs ->
                 In (id', AST.Gfun (AST.External ef)) defs -> id = id'.

Definition exf_declared [F V: Type] (p: AST.program (AST.fundef F) V) (id: AST.ident)
  (ef: AST.external_function) : Prop :=
  Maps.PTree.get id (AST.prog_defmap p) = Some (AST.Gfun (AST.External ef)).

Section ExtDecide.

  Context [P I S GV: Type] [F: Type].

  Definition find_exf_genv (ef: AST.external_function)
    (c: ctxt P I S (AST.fundef F) GV): option AST.ident :=
    List.find
      (fun id => match Ctxt.get_global id c with
                 | Some (AST.Gfun (AST.External ef')) => ExtFun.eqb ef ef'
                 | _ => false
                 end)
      (List.map fst (Maps.PTree.elements
                       (Globalenvs.Genv.genv_symb (ctxt_global c)))).

  Lemma find_exf_genv_correct [ef c id] (EQ: find_exf_genv ef c = Some id):
    Ctxt.get_global id c = Some (AST.Gfun (AST.External ef)).
  Proof using Type.
    apply List.find_some in EQ as [ _ PRED ].
    destruct (Ctxt.get_global id c) as [ [ [ fn | ef' ] | gv ] | ] eqn:GET;
      try discriminate PRED.
    destruct (ExtFun.eqb_spec ef ef') as [ <- | ]; [ reflexivity | discriminate PRED ].
  Qed.

  Lemma find_exf_genv_complete [ef c id]
    (GET: Ctxt.get_global id c = Some (AST.Gfun (AST.External ef))):
    exists id', find_exf_genv ef c = Some id'.
  Proof using Type.
    destruct (find_exf_genv ef c) as [ id' | ] eqn:SRCH; [ now exists id' | exfalso ].
    assert (SYMB: exists b, Globalenvs.Genv.find_symbol (ctxt_global c) id = Some b).
    { unfold Ctxt.get_global in GET.
      destruct (Globalenvs.Genv.find_symbol (ctxt_global c) id) as [ b | ];
        [ now exists b | discriminate GET ]. }
    destruct SYMB as ( b & SYMB ).
    assert (IN: List.In id
                  (List.map fst (Maps.PTree.elements
                                   (Globalenvs.Genv.genv_symb (ctxt_global c))))).
    { apply List.in_map_iff; exists (id, b); split; [ reflexivity | ].
      exact (Maps.PTree.elements_correct _ _ SYMB). }
    pose proof (List.find_none _ _ SRCH id IN) as PRED.
    cbv beta in PRED.
    rewrite GET in PRED.
    now rewrite (ReflectExt.reflect_refl ExtFun.eqb_spec) in PRED.
  Qed.

  Lemma find_exf_genv_spec ef c:
    Bool.reflect (exf_bound ef c)
      (match find_exf_genv ef c with Some _ => true | None => false end).
  Proof using Type.
    destruct (find_exf_genv ef c) as [ id | ] eqn:SRCH.
    - apply ReflectT; exists id; exact (find_exf_genv_correct SRCH).
    - apply ReflectF; intros ( id & GET ).
      destruct (find_exf_genv_complete GET) as ( id' & SRCH' ).
      rewrite SRCH in SRCH'; discriminate SRCH'.
  Qed.

End ExtDecide.

Section ExtUnique.

  Context [F GV: Type].

  Definition exf_fun_uniq_id
    (defs: list (AST.ident * (AST.globdef (AST.fundef F) GV)))
    (o: option AST.ident) (ef: AST.external_function): bool :=
    List.forallb
      (fun idg => match snd idg with
                  | AST.Gfun (AST.External ef') =>
                      if ExtFun.eqb ef ef'
                      then match o with
                           | Some id => Pos.eqb (fst idg) id
                           | None => false
                           end
                      else true
                  | _ => true
                  end)
      defs.

  Lemma exf_fun_uniq_id_spec defs o ef:
    exf_fun_uniq_id defs o ef = true
    <-> (forall id, List.In (id, AST.Gfun (AST.External ef)) defs -> o = Some id).
  Proof using Type.
    unfold exf_fun_uniq_id; rewrite List.forallb_forall; split.
    - intros ALL id IN.
      pose proof (ALL _ IN) as PRED; cbn [fst snd] in PRED.
      rewrite (ReflectExt.reflect_refl ExtFun.eqb_spec) in PRED.
      destruct o as [ m | ]; [ | discriminate PRED ].
      now rewrite (Pos.eqb_eq id m) in PRED; rewrite PRED.
    - intros H [ i g ] IN; cbn [fst snd].
      destruct g as [ [ fn | ef' ] | gv ]; [ reflexivity | | reflexivity ].
      destruct (ExtFun.eqb_spec ef ef') as [ <- | ]; [ | reflexivity ].
      rewrite (H i IN); apply Pos.eqb_refl.
  Qed.

  Definition find_exf (defs: list (AST.ident * (AST.globdef (AST.fundef F) GV)))
    (ef: AST.external_function): option AST.ident :=
    option_map fst
      (List.find (fun idg => match snd idg with
                             | AST.Gfun (AST.External ef') => ExtFun.eqb ef ef'
                             | _ => false
                             end) defs).

  Lemma find_exf_not_None [defs ef id]
    (IN: List.In (id, AST.Gfun (AST.External ef)) defs):
    find_exf defs ef <> None.
  Proof using Type.
    unfold find_exf.
    destruct (List.find _ defs) as [ idg | ] eqn:FIND; [ discriminate | ].
    pose proof (List.find_none _ _ FIND _ IN) as PRED.
    cbn [snd] in PRED.
    now rewrite (ReflectExt.reflect_refl ExtFun.eqb_spec) in PRED.
  Qed.

  Lemma find_exf_In [defs ef id] (EQ: find_exf defs ef = Some id):
    List.In (id, AST.Gfun (AST.External ef)) defs.
  Proof using Type.
    unfold find_exf in EQ.
    destruct (List.find _ defs) as [ [ i g ] | ] eqn:FIND; [ | discriminate EQ ].
    cbn [option_map fst] in EQ; injection EQ as <-.
    apply List.find_some in FIND as [ IN PRED ]; cbn [snd] in PRED.
    destruct g as [ [ fn | ef' ] | gv ]; try discriminate PRED.
    destruct (ExtFun.eqb_spec ef ef') as [ <- | ]; [ exact IN | discriminate PRED ].
  Qed.

  Definition find_exf_defmap (dm: Maps.PTree.t (AST.globdef (AST.fundef F) GV)) (ef: AST.external_function)
    : option AST.ident :=
    find_exf (Maps.PTree.elements dm) ef.

  Lemma find_exf_defmap_correct [ef] [p: AST.program (AST.fundef F) GV] [id]
    (FIND: find_exf_defmap (AST.prog_defmap p) ef = Some id)
    : exf_declared p id ef.
  Proof using Type.
    exact (Maps.PTree.elements_complete _ _ _ (find_exf_In FIND)).
  Qed.

  Lemma exf_declared_symbol [tp: AST.program (AST.fundef F) GV] [id ef] (DECL: exf_declared tp id ef)
    : exists b, Globalenvs.Genv.find_symbol (Globalenvs.Genv.globalenv tp) id = Some b
                /\ Globalenvs.Genv.find_funct (Globalenvs.Genv.globalenv tp)
                     (Values.Vptr b Integers.Ptrofs.zero)
                   = Some (AST.External ef).
  Proof using Type.
    case: (proj1 (Globalenvs.Genv.find_def_symbol _ _ _) DECL) => b [SYMB DEF].
    exists b; split; first exact: SYMB.
    by rewrite Globalenvs.Genv.find_funct_find_funct_ptr; apply/Globalenvs.Genv.find_funct_ptr_iff.
  Qed.

  Definition unique_exfb (defs: list (AST.ident * (AST.globdef (AST.fundef F) GV)))
    (ef: AST.external_function): bool :=
    exf_fun_uniq_id defs (find_exf defs ef) ef.

  Lemma unique_exfb_spec defs ef:
    Bool.reflect (unique_exf ef defs) (unique_exfb defs ef).
  Proof using Type.
    apply Bool.iff_reflect; unfold unique_exfb; split.
    - intros UNQ; apply (proj2 (exf_fun_uniq_id_spec _ _ _)).
      intros id IN.
      destruct (find_exf defs ef) as [ i | ] eqn:FST;
        [ | now destruct (find_exf_not_None IN) ].
      now rewrite (UNQ i id (find_exf_In FST) IN).
    - intros CHK id id' IN IN'.
      pose proof (proj1 (exf_fun_uniq_id_spec defs (find_exf defs ef) ef)
                    CHK) as ALL.
      pose proof (ALL id IN) as E1; pose proof (ALL id' IN') as E2.
      rewrite E1 in E2; now injection E2 as <-.
  Qed.

End ExtUnique.

(* ctx here is the global program context *)
Record wt_function [cmd: Type] (f_extra: Type) (wt_f_extra: f_extra -> Prop) (wt_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Prop) (ctx: ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef) (func: (function cmd f_extra)): Prop :=
  {
    wt_fn_cmd: wt_cmd (mk_function_ctxt func.(fn_params) func.(fn_temps) func.(fn_internals) ctx) func.(fn_body) func.(fn_return);
    wt_fn_extra: wt_f_extra func.(fn_extra);

    wt_fn_params_sbinds: SBinds func.(fn_params);
    wt_fn_temps_sbinds: SBinds func.(fn_temps);
    wt_fn_params_temps_distinct: ListExt.DBinds func.(fn_params) func.(fn_temps);
    wt_fn_internals_sbinds: SBinds func.(fn_internals);
    wt_fn_locals_internals_distinct:
      ListExt.DBinds (func.(fn_params) ++ func.(fn_temps)) func.(fn_internals);
  }.
Arguments wt_fn_cmd [cmd f_extra wt_f_extra wt_cmd ctx func]: rename.
Arguments wt_fn_extra [cmd f_extra wt_f_extra wt_cmd ctx func]: rename.
Arguments wt_fn_params_sbinds [cmd f_extra wt_f_extra wt_cmd ctx func]: rename.
Arguments wt_fn_temps_sbinds [cmd f_extra wt_f_extra wt_cmd ctx func]: rename.
Arguments wt_fn_params_temps_distinct [cmd f_extra wt_f_extra wt_cmd ctx func]: rename.
Arguments wt_fn_internals_sbinds [cmd f_extra wt_f_extra wt_cmd ctx func]: rename.
Arguments wt_fn_locals_internals_distinct [cmd f_extra wt_f_extra wt_cmd ctx func]: rename.

Inductive wt_fundef [cmd: Type] (f_extra: Type) (wt_f_extra: f_extra -> Prop) (wt_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Prop): ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef -> (fundef cmd f_extra) -> Prop :=
| wt_Internal:
  forall ctx func
         (WTFUNCTION: wt_function f_extra wt_f_extra wt_cmd ctx func),
    wt_fundef f_extra wt_f_extra wt_cmd ctx (AST.Internal func)
| wt_External: forall ctx ef sig (SIG: exf_funsig ef sig), wt_fundef f_extra wt_f_extra wt_cmd ctx (AST.External ef)
| wt_External_runtime: forall ctx name sg, wt_fundef f_extra wt_f_extra wt_cmd ctx (AST.External (AST.EF_runtime name sg))
.

Inductive wt_fundef_call {Ad: Addr.type} {Pt: Ptr.type Ad} cmd f_extra: list (value Pt) -> (fundef cmd f_extra) -> Prop :=
| wt_call_Internal: forall args f, Forall2 (@wt_value Ad Pt) args (List.map snd f.(fn_params)) -> wt_fundef_call cmd f_extra args (AST.Internal f)
| wt_call_external: forall ef sig args
                            (SIG: exf_funsig ef sig)
                            (WTARGS: Forall2 (@wt_value Ad Pt) args sig.(sig_args)),
    wt_fundef_call cmd f_extra args (AST.External ef)
.

Inductive wt_init_data: list AST.init_data -> type -> Prop :=
| wt_init_data_unit:
  wt_init_data [ AST.Init_space (Z.of_nat memword_bytes) ] t_unit
| wt_init_data_bool: forall n,
    (Integers.Int.unsigned n = 0%Z \/ Integers.Int.unsigned n = 1%Z) ->
    wt_init_data
      [ AST.Init_int8 n; AST.Init_space (Z.of_nat memword_bytes - 1) ]
      t_bool
| wt_init_data_nat: forall n,
    wt_init_data
      [ AST.Init_int32 n; AST.Init_space (Z.of_nat memword_bytes - 4) ]
      t_nat
| wt_init_data_ptr64:
  Archi.ptr64 = true ->
  wt_init_data [ AST.Init_int64 Integers.Int64.zero ] t_ptr
| wt_init_data_ptr32:
  Archi.ptr64 = false ->
  wt_init_data [ AST.Init_int32 Integers.Int.zero ] t_ptr
.

Definition type_init_data (init: list AST.init_data) (t: type) : bool :=
  match t, init with
  | t_unit, [ AST.Init_space sz ] =>
      Z.eqb sz (Z.of_nat memword_bytes)
  | t_bool, [ AST.Init_int8 n; AST.Init_space pad ] =>
      (Z.eqb (Integers.Int.unsigned n) 0%Z || Z.eqb (Integers.Int.unsigned n) 1%Z)
      && Z.eqb pad (Z.of_nat memword_bytes - 1)
  | t_nat, [ AST.Init_int32 _; AST.Init_space pad ] =>
      Z.eqb pad (Z.of_nat memword_bytes - 4)
  | t_ptr, [ AST.Init_int64 n ] =>
      Archi.ptr64 && Z.eqb (Integers.Int64.unsigned n) 0%Z
  | t_ptr, [ AST.Init_int32 n ] =>
      negb Archi.ptr64 && Z.eqb (Integers.Int.unsigned n) 0%Z
  | _, _ => false
  end.

Definition value_of_init_data [Ad: Addr.type] [Pt: Ptr.type Ad] (t: type) (init: list AST.init_data): option (value Pt) :=
  match t, init with
  | t_unit, [ AST.Init_space sz ] =>
      if Z.eqb sz (Z.of_nat memword_bytes) then Some v_tt else None
  | t_bool, [ AST.Init_int8 n; AST.Init_space pad ] =>
      if (Z.eqb (Integers.Int.unsigned n) 0%Z || Z.eqb (Integers.Int.unsigned n) 1%Z)
         && Z.eqb pad (Z.of_nat memword_bytes - 1)
      then Some (v_bool (Z.eqb (Integers.Int.unsigned n) 1%Z)) else None
  | t_nat, [ AST.Init_int32 n; AST.Init_space pad ] =>
      if Z.eqb pad (Z.of_nat memword_bytes - 4)
      then Some (v_nat (Z.to_nat (Integers.Int.unsigned n))) else None
  | t_ptr, [ AST.Init_int64 n ] =>
      if Archi.ptr64 && Z.eqb (Integers.Int64.unsigned n) 0%Z
      then Some (v_ptr (null: Pt)) else None
  | t_ptr, [ AST.Init_int32 n ] =>
      if negb Archi.ptr64 && Z.eqb (Integers.Int.unsigned n) 0%Z
      then Some (v_ptr (null: Pt)) else None
  | _, _ => None
  end.

Record wt_globvar (id: AST.ident) (globvar: AST.globvar vardef): Prop :=
  {
    wt_globvar_init_type: wt_init_data globvar.(AST.gvar_init) globvar.(AST.gvar_info).(var_type);
    wt_globvar_readonly: globvar.(AST.gvar_readonly) = false;
    wt_globvar_volatile: globvar.(AST.gvar_volatile) = false;
  }.
Arguments wt_globvar_init_type [id globvar]: rename.
Arguments wt_globvar_readonly [id globvar]: rename.
Arguments wt_globvar_volatile [id globvar]: rename.

Inductive wt_globdef [cmd] f_extra wt_f_extra wt_cmd: ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef -> AST.ident -> (globdef cmd f_extra) -> Prop :=
| wt_Gfun: forall ctx id f, wt_fundef f_extra wt_f_extra wt_cmd ctx f -> wt_globdef f_extra wt_f_extra wt_cmd ctx id (AST.Gfun f)
| wt_Gvar: forall ctx id v, wt_globvar id v -> wt_globdef f_extra wt_f_extra wt_cmd ctx id (AST.Gvar v)
.

Record wt_program [cmd f_extra p_extra: Type] wt_f_extra wt_cmd (wt_p_extra: program cmd f_extra p_extra -> Prop) (p: program cmd f_extra p_extra): Prop :=
  {
    wt_prog_defs:
      (* Similar to typing Rocq modules *)
      (* Global definitions are typed one-by-one and added to the environment *)
    ListExt.FoldLeft
      (fun ctx idg => wt_globdef f_extra wt_f_extra wt_cmd ctx (fst idg) (snd idg))
      (fun ctx idg => Ctxt.add_global ctx idg)
      (ctxt_emp _ _ _ _ _ p.(prog_public))
      p.(prog_defs);
    wt_prog_public: forall id, In id p.(prog_public) -> exists gdef, In (id,gdef) p.(prog_defs);
    wt_prog_main: exists f_main, In (p.(prog_main), AST.Gfun f_main) p.(prog_defs);
    wt_prog_defs_sbinds: SBinds p.(prog_defs);
    wt_prog_extra: wt_p_extra p;
  }.
Arguments wt_prog_defs [cmd f_extra p_extra wt_f_extra wt_cmd wt_p_extra p]: rename.
Arguments wt_prog_public [cmd f_extra p_extra wt_f_extra wt_cmd wt_p_extra p]: rename.
Arguments wt_prog_main [cmd f_extra p_extra wt_f_extra wt_cmd wt_p_extra p]: rename.
Arguments wt_prog_defs_sbinds [cmd f_extra p_extra wt_f_extra wt_cmd wt_p_extra p]: rename.
Arguments wt_prog_extra [cmd f_extra p_extra wt_f_extra wt_cmd wt_p_extra p]: rename.

Module Facts.

  Lemma mk_uninit_pair_inj idt1 idt2 (EQ: mk_uninit_pair idt1 = mk_uninit_pair idt2): idt1 = idt2.
  Proof.
    destruct idt1 as [ id1 t1 ], idt2 as [ id2 t2 ].
    unfold mk_uninit_pair in EQ;
      cbn in EQ;
      unfold mk_pair_with_false in EQ.
    congruence.
  Qed.

  Lemma mk_uninit_pair_list_is_uninit {l ident t b}
    (IN: In (ident, (t, b)) (map mk_uninit_pair l))
    : b = false.
  Proof.
    induction l; [ contradiction | cbn in IN ].
    destruct IN as [ EQ | IN ]; [ cbv in EQ; congruence | apply IHl, IN ].
  Qed.

  Lemma mk_init_pair_inj idt1 idt2 (EQ: mk_init_pair idt1 = mk_init_pair idt2): idt1 = idt2.
  Proof.
    destruct idt1, idt2.
    unfold mk_init_pair, mk_pair_with_true in EQ; cbn in EQ; congruence.
  Qed.

  Lemma map_fst_mk_init_pair l : map fst (map mk_init_pair l) = map fst l.
  Proof.
    induction l as [| [id t] l IH]; cbn; [ reflexivity | now f_equal ].
  Qed.

  Lemma map_fst_mk_uninit_pair l : map fst (map mk_uninit_pair l) = map fst l.
  Proof.
    induction l as [| [id t] l IH]; cbn; [ reflexivity | now f_equal ].
  Qed.

  Lemma in_mk_init_pair_iff l id t :
    In (id, (t, true)) (map mk_init_pair l) <-> In (id, t) l.
  Proof.
    induction l as [| [id' t'] l IH]; cbn; [ tauto |].
    unfold mk_init_pair at 1, mk_pair_with_true at 1; cbn.
    split; intros [EQ | IN];
      try (left; inversion EQ; subst; reflexivity);
      try (right; apply IH; assumption).
  Qed.

  Lemma in_mk_uninit_pair_iff l id t :
    In (id, (t, false)) (map mk_uninit_pair l) <-> In (id, t) l.
  Proof.
    induction l as [| [id' t'] l IH]; cbn; [ tauto |].
    unfold mk_uninit_pair at 1, mk_pair_with_false at 1; cbn.
    split; intros [EQ | IN];
      try (left; inversion EQ; subst; reflexivity);
      try (right; apply IH; assumption).
  Qed.

  Lemma not_In_fst_AbsBind {V: Type} (l: list (AST.ident * V)) id :
    ~ In id (map fst l) -> ListExt.AbsBind id l.
  Proof.
    induction l as [ | [k v] rest IH ]; intros NOTIN; [ constructor | ].
    cbn in NOTIN.
    constructor.
    - intros ->; apply NOTIN; now left.
    - apply IH; intros IN; apply NOTIN; now right.
  Qed.

  Lemma mk_typing_tree_cons [V: Type] (b: bool) (k: AST.ident) (v: V)
    (rest: list (AST.ident * V)) (init: Maps.PTree.t (V * bool)) :
    mk_typing_tree b ((k, v) :: rest) init
    = mk_typing_tree b rest (Maps.PTree.set k (v, b) init).
  Proof. reflexivity. Qed.

  Lemma mk_typing_tree_app [V: Type] (b: bool) (l1 l2: list (AST.ident * V))
    (init: Maps.PTree.t (V * bool)) :
    mk_typing_tree b (l1 ++ l2) init = mk_typing_tree b l2 (mk_typing_tree b l1 init).
  Proof. apply List.fold_left_app. Qed.

  (* Applying [Maps.PTree.set] as a fold doesn't change the result of
     [Maps.PTree.get id], if [id] is absent from the folded list *)
  Lemma mk_typing_tree_get_other {V: Type} (entries: list (AST.ident * V)) (b: bool)
    (id: AST.ident) (init: Maps.PTree.t (V * bool))
    (ABS: ListExt.AbsBind id entries) :
    Maps.PTree.get id (mk_typing_tree b entries init) = Maps.PTree.get id init.
  Proof.
    revert init.
    induction entries as [ | [k v] rest IH ]; intros init.
    - reflexivity.
    - inversion ABS as [ | ? ? ? ? NE ABS' ]; subst.
      rewrite mk_typing_tree_cons (IH ABS').
      apply Maps.PTree.gso. cbn. exact NE.
  Qed.

  (* A [Maps.PTree.get] yields the value in the folded-over list *)
  Lemma mk_typing_tree_get_in {V: Type} (entries: list (AST.ident * V)) (b: bool)
    (id: AST.ident) (v: V) (init: Maps.PTree.t (V * bool))
    (SB: ListExt.SBinds entries) (IN: In (id, v) entries) :
    Maps.PTree.get id (mk_typing_tree b entries init) = Some (v, b).
  Proof.
    revert init.
    induction SB as [ | k v' rest ABS SB' IH ]; intros init; cbn in IN;
      [ contradiction | ].
    rewrite mk_typing_tree_cons.
    destruct IN as [ EQ | IN' ].
    - inversion EQ; subst k v'; clear EQ.
      rewrite (mk_typing_tree_get_other rest b id _ ABS).
      apply Maps.PTree.gss.
    - apply IH; exact IN'.
  Qed.

  (* If all tree bindings are "false", applying a false fold never produces a "true" binding  *)
  Lemma mk_typing_tree_false_not_true {V: Type} (entries: list (AST.ident * V))
    (init: Maps.PTree.t (V * bool))
    (INIT: forall id v, Maps.PTree.get id init = Some (v, true) -> False)
    id v :
    Maps.PTree.get id (mk_typing_tree false entries init) = Some (v, true) -> False.
  Proof.
    revert init INIT.
    induction entries as [ | [k v'] rest IH ]; intros init INIT GET.
    - exact (INIT _ _ GET).
    - rewrite mk_typing_tree_cons in GET.
      eapply IH; [ | exact GET ].
      intros id' v'' GET'.
      rewrite Maps.PTree.gsspec in GET'.
      destruct (Coqlib.peq id' k); [ discriminate GET' | exact (INIT _ _ GET') ].
  Qed.

  Lemma mk_typing_tree_get_inv {V: Type} (l: list (AST.ident * V)):
    forall (acc: Maps.PTree.t (V * bool)) id t b,
      Maps.PTree.get id (mk_typing_tree false l acc) = Some (t, b) ->
      In (id, t) l \/ Maps.PTree.get id acc = Some (t, b).
  Proof.
    induction l as [ | [ id1 t1 ] l IH ]; intros acc id t b GET.
    - right; exact GET.
    - rewrite mk_typing_tree_cons in GET.
      destruct (IH _ _ _ _ GET) as [ IN | GET' ]; [ left; now right | ].
      rewrite Maps.PTree.gsspec in GET'; cbn in GET'.
      destruct (Coqlib.peq id id1) as [ EQ | NE ];
        [ inversion GET'; subst; left; now left | right; exact GET' ].
  Qed.

  Lemma mk_function_ctxt_pure_get_param [cmd f_extra]
    (params temps internals: list (AST.ident * type))
    (ctx: ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef)
    (SBp: ListExt.SBinds params)
    (SBt: ListExt.SBinds temps)
    (DIST: ListExt.DBinds params temps)
    id t (IN: In (id, t) params) :
    Maps.PTree.get id
      (ctxt_pure (mk_function_ctxt params temps internals ctx)) = Some (t, true).
  Proof.
    unfold mk_function_ctxt; cbn [ctxt_pure with_pure with_internal].
    apply (mk_typing_tree_get_in params true id t _ SBp IN).
  Qed.

  Lemma mk_function_ctxt_pure_get_temp [cmd f_extra]
    (params temps internals: list (AST.ident * type))
    (ctx: ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef)
    (SBp: ListExt.SBinds params)
    (SBt: ListExt.SBinds temps)
    (DIST: ListExt.DBinds params temps)
    id t (IN: In (id, t) temps) :
    Maps.PTree.get id
      (ctxt_pure (mk_function_ctxt params temps internals ctx)) = Some (t, false).
  Proof.
    unfold mk_function_ctxt; cbn [ctxt_pure with_pure with_internal].
    rewrite (mk_typing_tree_get_other params true id _ (ListExt.DBinds_In_AbsBind_rev DIST IN)).
    rewrite mk_typing_tree_app.
    apply (mk_typing_tree_get_in temps false id t _ SBt IN).
  Qed.

  Lemma mk_function_ctxt_pure_get_none [cmd f_extra]
    (params temps internals: list (AST.ident * type))
    (ctx: ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef)
    id
    (ABSp: ListExt.AbsBind id params)
    (ABSt: ListExt.AbsBind id temps) :
    Maps.PTree.get id (ctxt_pure (mk_function_ctxt params temps internals ctx)) = None.
  Proof.
    unfold mk_function_ctxt; cbn [ctxt_pure with_pure with_internal].
    rewrite (mk_typing_tree_get_other params true id _ ABSp).
    rewrite mk_typing_tree_app.
    rewrite (mk_typing_tree_get_other temps false id _ ABSt).
    rewrite (mk_typing_tree_get_other params false id _ ABSp).
    apply Maps.PTree.gempty.
  Qed.

  Lemma mk_function_ctxt_internal_get_in [cmd f_extra]
    (params temps internals: list (AST.ident * type))
    (ctx: ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef)
    (SBi: ListExt.SBinds internals)
    id t
    (IN: In (id, t) internals) :
    Ctxt.get_internal id (mk_function_ctxt params temps internals ctx) = Some (t, false).
  Proof.
    unfold Ctxt.get_internal.
    unfold mk_function_ctxt; cbn [ctxt_internal with_internal].
    apply (mk_typing_tree_get_in internals false id t _ SBi IN).
  Qed.

  Lemma mk_function_ctxt_pure_get_inv [cmd f_extra]
    (params temps internals: list (AST.ident * type))
    (ctx: ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef)
    (SBp: ListExt.SBinds params)
    (SBt: ListExt.SBinds temps)
    id t b
    (GET: Maps.PTree.get id (ctxt_pure (mk_function_ctxt params temps internals ctx))
             = Some (t, b)) :
    (b = true /\ In (id, t) params) \/ (b = false /\ In (id, t) temps).
  Proof.
    unfold mk_function_ctxt in GET; cbn [ctxt_pure with_pure with_internal] in GET.
    destruct (List.in_dec Pos.eq_dec id (map fst params)) as [ INpfst | NOTINp ].
    - left.
      apply in_map_iff in INpfst as [ [id' t'] [FST INp] ]; cbn in FST; subst id'.
      rewrite (mk_typing_tree_get_in params true id t' _ SBp INp) in GET.
      inversion GET; subst; split; [ reflexivity | exact INp ].
    - right.
      assert (ABSp: ListExt.AbsBind id params) by (apply not_In_fst_AbsBind; exact NOTINp).
      rewrite (mk_typing_tree_get_other params true id _ ABSp) in GET.
      rewrite mk_typing_tree_app in GET.
      destruct (List.in_dec Pos.eq_dec id (map fst temps)) as [ INtfst | NOTINt ].
      + apply in_map_iff in INtfst as [ [id' t'] [FST INt] ]; cbn in FST; subst id'.
        rewrite (mk_typing_tree_get_in temps false id t' _ SBt INt) in GET.
        inversion GET; subst; split; [ reflexivity | exact INt ].
      + assert (ABSt: ListExt.AbsBind id temps) by (apply not_In_fst_AbsBind; exact NOTINt).
        rewrite (mk_typing_tree_get_other temps false id _ ABSt) in GET.
        rewrite (mk_typing_tree_get_other params false id _ ABSp) in GET.
        rewrite Maps.PTree.gempty in GET. discriminate GET.
  Qed.

  Lemma prog_main_is_prog_main [cmd f_extra p_extra]:
    forall (p: program cmd f_extra p_extra),
      prog_main p = AST.prog_main (program_of_program p).
  Proof.
    reflexivity.
  Qed.

  Lemma program_of_program_sound [cmd f_extra p_extra]:
    forall (p: program cmd f_extra p_extra) p',
      p' = (program_of_program p) -> p = (mkprogram p'.(AST.prog_defs) p'.(AST.prog_public) p'.(AST.prog_main) p.(prog_extra)).
  Proof.
    intros.
    destruct p, p'.
    f_equal; inversion H; auto.
  Qed.

  Lemma wt_function_incl_global [cmd f_extra: Type]
    [wt_f_extra: f_extra -> Prop]
    [wt_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Prop]
    (wt_cmd_incl_global:
       forall ctx ctx',
         Ctxt.ctxt_pure ctx = Ctxt.ctxt_pure ctx' ->
         Ctxt.ctxt_internal ctx = Ctxt.ctxt_internal ctx' ->
         Ctxt.ctxt_stack ctx = Ctxt.ctxt_stack ctx' ->
         (forall id g, Ctxt.get_global id ctx = Some g ->
                       Ctxt.get_global id ctx' = Some g) ->
         forall c t, wt_cmd ctx c t -> wt_cmd ctx' c t)
    ctx ctx' func
    (MONO: forall id g, Ctxt.get_global id ctx = Some g ->
                         Ctxt.get_global id ctx' = Some g):
    wt_function f_extra wt_f_extra wt_cmd ctx func ->
    wt_function f_extra wt_f_extra wt_cmd ctx' func.
  Proof.
    intros WT.
    refine {|
      wt_fn_cmd := _;
      wt_fn_extra := WT.(wt_fn_extra);
      wt_fn_params_sbinds := WT.(wt_fn_params_sbinds);
      wt_fn_temps_sbinds := WT.(wt_fn_temps_sbinds);
      wt_fn_params_temps_distinct := WT.(wt_fn_params_temps_distinct);
      wt_fn_internals_sbinds := WT.(wt_fn_internals_sbinds);
      wt_fn_locals_internals_distinct := WT.(wt_fn_locals_internals_distinct);
    |}.
    eapply wt_cmd_incl_global; [ | | | | exact WT.(wt_fn_cmd) ]; try reflexivity.
    intros id g GET.
    unfold mk_function_ctxt in *.
    rewrite Ctxt.Facts.get_global_with_internal Ctxt.Facts.get_global_with_pure
      Ctxt.Facts.get_global_with_stack in GET.
    rewrite Ctxt.Facts.get_global_with_internal Ctxt.Facts.get_global_with_pure
      Ctxt.Facts.get_global_with_stack.
    now apply MONO.
  Qed.

  Lemma wt_fundef_incl_global [cmd f_extra: Type]
    [wt_f_extra: f_extra -> Prop]
    [wt_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Prop]
    (wt_cmd_incl_global:
       forall ctx ctx',
         Ctxt.ctxt_pure ctx = Ctxt.ctxt_pure ctx' ->
         Ctxt.ctxt_internal ctx = Ctxt.ctxt_internal ctx' ->
         Ctxt.ctxt_stack ctx = Ctxt.ctxt_stack ctx' ->
         (forall id g, Ctxt.get_global id ctx = Some g ->
                       Ctxt.get_global id ctx' = Some g) ->
         forall c t, wt_cmd ctx c t -> wt_cmd ctx' c t)
    ctx ctx' f
    (MONO: forall id g, Ctxt.get_global id ctx = Some g ->
                         Ctxt.get_global id ctx' = Some g):
    wt_fundef f_extra wt_f_extra wt_cmd ctx f ->
    wt_fundef f_extra wt_f_extra wt_cmd ctx' f.
  Proof.
    intros WT.
    destruct WT as [ ? func WTf | ? ef WTef | ? name sg ].
    - constructor; eapply wt_function_incl_global; eauto.
    - eapply wt_External; eassumption.
    - apply wt_External_runtime.
  Qed.

  Lemma wt_globdef_incl_global [cmd f_extra: Type]
    [wt_f_extra: f_extra -> Prop]
    [wt_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Prop]
    (wt_cmd_incl_global:
       forall ctx ctx',
         Ctxt.ctxt_pure ctx = Ctxt.ctxt_pure ctx' ->
         Ctxt.ctxt_internal ctx = Ctxt.ctxt_internal ctx' ->
         Ctxt.ctxt_stack ctx = Ctxt.ctxt_stack ctx' ->
         (forall id g, Ctxt.get_global id ctx = Some g ->
                       Ctxt.get_global id ctx' = Some g) ->
         forall c t, wt_cmd ctx c t -> wt_cmd ctx' c t)
    ctx ctx' id g
    (MONO: forall id' g', Ctxt.get_global id' ctx = Some g' ->
                           Ctxt.get_global id' ctx' = Some g'):
    wt_globdef f_extra wt_f_extra wt_cmd ctx id g ->
    wt_globdef f_extra wt_f_extra wt_cmd ctx' id g.
  Proof.
    intros WT.
    destruct WT as [ ? ? fn WTf | ? ? v WTv ].
    - constructor; eapply wt_fundef_incl_global; eauto.
    - constructor; destruct WTv; constructor; assumption.
  Qed.

  Lemma globdef_in_mk_glob_ctxt [cmd f_extra p_extra: Type]
    (p: program cmd f_extra p_extra) (SBINDS: SBinds p.(prog_defs))
    [id g] (IN: In (id, g) p.(prog_defs))
    : get_global id (mk_glob_ctxt p) = Some g.
  Proof.
    edestruct (proj1 (Globalenvs.Genv.find_def_symbol p id g)) as (b & SYMB & DEF);
      [ apply AST.prog_defmap_norepet;
          [ apply (proj1 (ListExt.SBinds_list_norepet _)), SBINDS | exact IN ]
      | by unfold mk_glob_ctxt, get_global, with_global; cbn [ctxt_global];
        rewrite SYMB DEF ].
  Qed.

  Lemma wt_prog_defs_Forall_aux [cmd f_extra p_extra: Type]
    [wt_f_extra: f_extra -> Prop]
    [wt_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Prop]
    (wt_cmd_incl_global:
       forall ctx ctx',
         Ctxt.ctxt_pure ctx = Ctxt.ctxt_pure ctx' ->
         Ctxt.ctxt_internal ctx = Ctxt.ctxt_internal ctx' ->
         Ctxt.ctxt_stack ctx = Ctxt.ctxt_stack ctx' ->
         (forall id g, Ctxt.get_global id ctx = Some g ->
                       Ctxt.get_global id ctx' = Some g) ->
         forall c t, wt_cmd ctx c t -> wt_cmd ctx' c t)
    (p: program cmd f_extra p_extra) (SBINDS: SBinds p.(prog_defs))
    defs ctx
    (IN: forall idg, In idg defs -> In idg p.(prog_defs))
    (SUB: forall id g, get_global id ctx = Some g ->
                        get_global id (mk_glob_ctxt p) = Some g)
    (FF: ListExt.FoldLeft
           (fun c idg => wt_globdef f_extra wt_f_extra wt_cmd c (fst idg) (snd idg))
           (fun c idg => Ctxt.add_global c idg) ctx defs)
    : Forall (fun idg => wt_globdef f_extra wt_f_extra wt_cmd
                           (mk_glob_ctxt p) (fst idg) (snd idg)) defs.
  Proof.
    revert IN SUB.
    induction FF as [ | acc [id g] rest WT _ IH ]; intros IN SUB; constructor;
      [ eapply wt_globdef_incl_global; [ exact wt_cmd_incl_global | exact SUB | exact WT ] | ].
    apply IH; [ now intros ??; apply IN; right | ].
    intros id' g' GET; destruct (BinPos.Pos.eq_dec id id') as [ <- | NE ];
      [ rewrite Ctxt.Facts.get_global_add_global_eq in GET; injection GET as <-;
        apply globdef_in_mk_glob_ctxt; [ exact SBINDS | apply IN; now left ]
      | ].
    by rewrite Ctxt.Facts.get_global_add_global_neq in GET; first (cbn; congruence);
      apply SUB.
  Qed.

  Lemma wt_prog_defs_Forall [cmd f_extra p_extra: Type]
    [wt_f_extra: f_extra -> Prop]
    [wt_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Prop]
    [wt_p_extra: program cmd f_extra p_extra -> Prop]
    (wt_cmd_incl_global:
       forall ctx ctx',
         Ctxt.ctxt_pure ctx = Ctxt.ctxt_pure ctx' ->
         Ctxt.ctxt_internal ctx = Ctxt.ctxt_internal ctx' ->
         Ctxt.ctxt_stack ctx = Ctxt.ctxt_stack ctx' ->
         (forall id g, Ctxt.get_global id ctx = Some g ->
                       Ctxt.get_global id ctx' = Some g) ->
         forall c t, wt_cmd ctx c t -> wt_cmd ctx' c t)
    (p: program cmd f_extra p_extra)
    (WT: wt_program wt_f_extra wt_cmd wt_p_extra p)
    : Forall
        (fun idglob => wt_globdef f_extra wt_f_extra wt_cmd (mk_glob_ctxt p) (fst idglob) (snd idglob))
        p.(prog_defs).
  Proof.
    destruct WT as [ FOLD _ _ SBINDS _ ].
    apply wt_prog_defs_Forall_aux
      with (ctx := ctxt_emp _ _ _ _ _ p.(prog_public));
      [ exact wt_cmd_incl_global | exact SBINDS | tauto
      | intros ?? GET;
        unfold get_global, ctxt_emp, Globalenvs.Genv.find_symbol,
               Globalenvs.Genv.empty_genv in GET; cbn in GET; discriminate
      | exact FOLD ].
  Qed.

  Definition ef_sig_dec (ef: AST.external_function) : option signature :=
    match ef with
    | AST.EF_external _ sg =>
        match ListExt.map_opt xtype_to_type sg.(AST.sig_args), xtype_to_type sg.(AST.sig_res) with
        | Some args, Some res =>
            if forallb Types.sized args then
              if AST.signature_eq sg (signature_of_signature (mk_signature args res))
              then Some (mk_signature args res)
              else None
            else None
        | _, _ => None
        end
    | AST.EF_malloc => Some {| sig_args := [t_ofst]; sig_res := t_ptr; |}
    | AST.EF_free => Some {| sig_args := [t_ptr]; sig_res := t_unit; |}
    | _ => None
    end.
  Arguments ef_sig_dec : simpl never.

  Lemma is_runtime_ef_sig_dec_none ef (RT: ExtFun.is_runtime ef = true):
    ef_sig_dec ef = None.
  Proof.
    destruct ef; solve [ discriminate RT | reflexivity ].
  Qed.

  Lemma ef_sig_dec_some_not_runtime ef sig (DEC: ef_sig_dec ef = Some sig):
    ExtFun.is_runtime ef = false.
  Proof.
    destruct ef; solve [ reflexivity | discriminate DEC ].
  Qed.

  Lemma ef_sig_dec_spec: forall ef sig, exf_funsig ef sig <-> ef_sig_dec ef = Some sig.
  Proof.
    intros ef sig; split.
    - intros [ nm [ args res ] SIZED | | ]; [ | reflexivity | reflexivity ].
      cbn [sig_args] in SIZED.
      assert (DECODE: ListExt.map_opt xtype_to_type (List.map type_to_xtype args) = Some args).
      { clear SIZED.
        induction args as [ | t ts IH ]; [ reflexivity | cbn [List.map ListExt.map_opt] ].
        by rewrite type_to_xtype_to_type IH. }
      assert (ALLSIZED: forallb Types.sized args = true).
      { apply List.forallb_forall; intros t IN.
        exact (proj1 (Bool.reflect_iff _ _ (Types.sized_spec t))
                 (proj1 (List.Forall_forall _ _) SIZED t IN)). }
      pose proof (List.forallb_filter_id _ _ ALLSIZED) as FILTER.
      unfold ef_sig_dec, signature_of_signature;
        cbn [AST.sig_args AST.sig_res sig_args sig_res].
      rewrite FILTER DECODE type_to_xtype_to_type ALLSIZED; cbv beta iota; rewrite FILTER.
      destruct (AST.signature_eq _ _) as [ EQ | NE ]; [ reflexivity | exfalso; exact (NE eq_refl) ].
    - destruct ef as [ nm sg | | | | | | | | | | | ]; cbv beta iota delta [ef_sig_dec]; try discriminate.
      + destruct (ListExt.map_opt xtype_to_type sg.(AST.sig_args)) as [ args | ];
          [ | discriminate ].
        destruct (xtype_to_type sg.(AST.sig_res)) as [ res | ]; [ | discriminate ].
        destruct (forallb Types.sized args) eqn:ALLSIZED; [ | discriminate ].
        destruct (AST.signature_eq _ _) as [ EQ | NE ]; [ subst sg | discriminate ].
        intros [= <-].
        apply funsig_external; cbn [sig_args].
        apply List.Forall_forall; intros t IN.
        exact (proj2 (Bool.reflect_iff _ _ (Types.sized_spec t))
                 (proj1 (List.forallb_forall _ _) ALLSIZED t IN)).
      + intros [= <-]; constructor.
      + intros [= <-]; constructor.
  Qed.

  Lemma type_init_data_spec: forall init t,
      Bool.reflect (wt_init_data init t) (type_init_data init t).
  Proof.
    intros init t.
    destruct t; cbn.
    - destruct init as [ | [ | | | | | |sz| ] [ | ? ? ] ];
        try (apply ReflectF; intros H; inversion H); cbn.
      destruct (Z.eqb_spec sz (Z.of_nat memword_bytes));
        [ subst; left; constructor | right; intros contra; inversion contra; congruence ].
    - destruct init
        as [ | [i| | | | | | | ] [ | [ | | | | | |pad| ] [ | ? ? ] ] ];
        try (apply ReflectF; intros H; inversion H; congruence).
      destruct (Z.eqb_spec pad (Z.of_nat memword_bytes -1)%Z); [ | rewrite Bool.andb_false_r; right; intros contra; inversion contra as [ | ?b [ | ] | | | ]; congruence ].
      destruct (Z.eqb_spec (Integers.Int.unsigned i) 0%Z); [ now subst; repeat constructor | ].
      destruct (Z.eqb_spec (Integers.Int.unsigned i) 1%Z); [ now subst; repeat constructor | right; intros contra; inversion contra; firstorder ].
    - destruct init
        as [ | [ | |i| | | | | ] [ | [ | | | | | |pad|] [ | ? ? ] ] ];
        try (apply ReflectF; intros H; inversion H; congruence).
      destruct (Z.eqb_spec pad (Z.of_nat memword_bytes - 4));
        [ subst; now repeat constructor | right; intros contra; inversion contra; congruence ].
    - right; intros contra; inversion contra.
    - destruct Archi.ptr64 eqn:E;
        destruct init as [ | [ | |i|i| | | | ] [ | ? ? ] ]; cbn;
        try (apply ReflectF; intros H; inversion H; congruence).
      + destruct (Z.eqb_spec (Integers.Int64.unsigned i) 0%Z) as [ EQ0 | NE0 ].
        * left.
          rewrite (Integers.Int64.same_if_eq i Integers.Int64.zero); last by constructor.
          by rewrite /Integers.Int64.eq/Coqlib.zeq EQ0.
        * right; intros contra; inversion contra; subst; apply (NE0 Integers.Int64.unsigned_zero).
      + destruct (Z.eqb_spec (Integers.Int.unsigned i) 0%Z) as [ EQ0 | NE0 ].
        * left.
          rewrite (Integers.Int.same_if_eq i Integers.Int.zero); last by constructor.
          by rewrite /Integers.Int.eq/Coqlib.zeq EQ0.
        * right; intros contra; inversion contra; subst; apply (NE0 Integers.Int.unsigned_zero).
  Qed.

  Lemma value_of_init_data_sound [Ad] [Pt: Ptr.type Ad]: forall t init (mv: value Pt)
      (MV: value_of_init_data t init = Some mv),
      wt_init_data init t.
  Proof.
    intros t init mv.
    destruct t; cbn.
    - destruct init as [ | [ | | | | | |sz| ] [ | ? ? ] ]; try discriminate.
      destruct (Z.eqb_spec sz (Z.of_nat memword_bytes)); [ | discriminate ].
      subst; constructor.
    - destruct init
        as [ | [i| | | | | | | ] [ | [ | | | | | |pad| ] [ | ? ? ] ] ];
        try discriminate.
      destruct (Z.eqb_spec pad (Z.of_nat memword_bytes -1)%Z);
        [ | rewrite Bool.andb_false_r; discriminate ].
      destruct (Z.eqb_spec (Integers.Int.unsigned i) 0%Z) as [E0|NE0].
      + intro MV; inversion MV; subst; constructor; auto.
      + destruct (Z.eqb_spec (Integers.Int.unsigned i) 1%Z) as [E1|NE1]; [ | discriminate ].
        intro MV; inversion MV; subst; constructor; auto.
    - destruct init
        as [ | [ | |i| | | | | ] [ | [ | | | | | |pad|] [ | ? ? ] ] ];
        try discriminate.
      destruct (Z.eqb_spec pad (Z.of_nat memword_bytes - 4)); [ | discriminate ].
      subst; constructor.
    - discriminate.
    - destruct Archi.ptr64 eqn:E;
        destruct init as [ | [ | |i|i| | | | ] [ | ? ? ] ]; cbn;
        try discriminate;
        lazymatch goal with
        | |- context [ Integers.Int64.unsigned i ] =>
            destruct (Z.eqb_spec (Integers.Int64.unsigned i) 0%Z) as [ EQ0 | NE0 ]; [ | discriminate ];
            subst;
            rewrite (Integers.Int64.same_if_eq i Integers.Int64.zero);
            [ unfold Integers.Int64.eq, Coqlib.zeq; rewrite EQ0 Integers.Int64.unsigned_zero; reflexivity
            | constructor; auto]
        | |- context [ Integers.Int.unsigned i ] =>
            destruct (Z.eqb_spec (Integers.Int.unsigned i) 0%Z) as [ EQ0 | NE0 ]; [ | discriminate ];
            subst;
            rewrite (Integers.Int.same_if_eq i Integers.Int.zero);
              [ constructor; auto
              | unfold Integers.Int.eq, Coqlib.zeq; rewrite EQ0 Integers.Int.unsigned_zero; reflexivity ]
        end.
  Qed.

  Lemma value_of_init_data_complete [Ad] [Pt: Ptr.type Ad]: forall t init
      (WT: wt_init_data init t),
      exists mv: value Pt, value_of_init_data t init = Some mv.
  Proof.
    intros t init WT.
    destruct WT as [ | n BOOL | n | PTR64 | PTR32 ]; cbn.
    - now eexists; rewrite Z.eqb_refl.
    - now destruct BOOL as [BOOL|BOOL]; rewrite BOOL; cbn; eexists; rewrite Z.eqb_refl.
    - now eexists; rewrite Z.eqb_refl.
    - now eexists; rewrite PTR64; cbn; rewrite Integers.Int64.unsigned_zero.
    - now eexists; rewrite PTR32; cbn; rewrite Integers.Int.unsigned_zero.
  Qed.

  Lemma wt_globvar_init_size [id globvar]
    (WT: wt_globvar id globvar)
    : AST.init_data_list_size globvar.(AST.gvar_init) = Z.of_nat memword_bytes.
  Proof.
    now destruct WT as [[ ] _ _].
  Qed.

End Facts.

Definition type_external_function (ef: AST.external_function) : bool :=
  match Facts.ef_sig_dec ef with
  | Some _ => true
  | None => false
  end.

(* Computational counterpart of [funsig] *)
Definition type_funsig [cmd extra: Type] (f: fundef cmd extra) : option signature :=
  match f with
  | AST.Internal fn => Some (fn_signature fn)
  | AST.External ef => Facts.ef_sig_dec ef
  end.

Lemma type_funsig_complete [cmd extra: Type] (f: fundef cmd extra) sig:
  funsig f sig -> type_funsig f = Some sig.
Proof.
  destruct 1 as [ fn | ef sg SIG ]; cbn [type_funsig].
  - reflexivity.
  - exact (proj1 (Facts.ef_sig_dec_spec ef sg) SIG).
Qed.

Lemma type_funsig_correct [cmd extra: Type] (f: fundef cmd extra) sig
  (SIG: type_funsig f = Some sig): funsig f sig.
Proof.
  destruct f as [fn | ef]; cbn [type_funsig] in SIG.
  - injection SIG as <-. exact (funsig_Internal fn).
  - exact (funsig_External ef sig (proj2 (Facts.ef_sig_dec_spec ef sig) SIG)).
Qed.

(* Computational counterpart of [wt_fundef_call]'s argument condition:
   pointwise [type_eqb] of the runtime values' types against the callee
   signature's argument types (as computed by [type_funsig]). *)
Definition type_call_args [Ad: Addr.type] [Pt: Ptr.type Ad] (args: list (value Pt)) (ts: list type): bool :=
  ListExt.forall2b (fun v t => type_eqb (type_of_value v) t) args ts.

Lemma type_call_args_Forall2 [Ad] [Pt: Ptr.type Ad] (args: list (value Pt)) ts
  (ARGS: type_call_args args ts = true): Forall2 (@wt_value Ad Pt) args ts.
Proof.
  apply (proj1 (ListExt.forall2b_Forall2 _ _ _)) in ARGS.
  induction ARGS as [ | v t vs ts' EQ _ IH ]; constructor; last exact IH.
  - apply (ReflectExt.reflect_eq_of_true type_eqb_spec) in EQ; subst t;
      exact Value.Facts.type_of_value_correct.
Qed.

Lemma Forall2_type_call_args [Ad] [Pt: Ptr.type Ad] (args: list (value Pt)) ts
  (WT: Forall2 (@wt_value Ad Pt) args ts): type_call_args args ts = true.
Proof.
  apply (proj2 (ListExt.forall2b_Forall2 _ _ _)).
  induction WT as [ | v t vs ts' WTv _ IH ]; constructor.
  - rewrite (Value.Facts.type_of_value_complete WTv). apply: reflect_refl eqb_spec _.
  - exact IH.
Qed.

Lemma type_call_args_correct [Ad] [Pt: Ptr.type Ad] [cmd extra: Type] (f: fundef cmd extra) sig (args: list (value Pt))
  (SIG: type_funsig f = Some sig)
  (ARGS: type_call_args args sig.(sig_args) = true):
  wt_fundef_call cmd extra args f.
Proof.
  destruct f as [fn | ef]; cbn [type_funsig] in SIG.
  - injection SIG as <-.
    exact (wt_call_Internal cmd extra args fn (type_call_args_Forall2 _ _ ARGS)).
  - exact (wt_call_external cmd extra ef sig args
             (proj2 (Facts.ef_sig_dec_spec ef sig) SIG)
             (type_call_args_Forall2 _ _ ARGS)).
Qed.

Lemma type_call_args_complete [Ad] [Pt: Ptr.type Ad] [cmd extra: Type] (f: fundef cmd extra) sig (args: list (value Pt))
  (WT: wt_fundef_call cmd extra args f)
  (SIG: type_funsig f = Some sig):
  type_call_args args sig.(sig_args) = true.
Proof.
  destruct WT as [ args' fn WTARGS | ef sig0 args' SIG0 WTARGS ];
    cbn [type_funsig] in SIG.
  - injection SIG as <-. exact (Forall2_type_call_args _ _ WTARGS).
  - rewrite (proj1 (Facts.ef_sig_dec_spec ef sig0) SIG0) in SIG.
    injection SIG as <-. exact (Forall2_type_call_args _ _ WTARGS).
Qed.

Definition type_function [cmd f_extra: Type]
  (type_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (ctx: ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef)
  (func: function cmd f_extra) : bool :=
  (match type_cmd (mk_function_ctxt func.(fn_params) func.(fn_temps) func.(fn_internals) ctx)
                     func.(fn_body) with
      | Some t => type_eqb t func.(fn_return)
      | None => false
      end)
  && type_f_extra func.(fn_extra)
  && ListExt.sbinds Pos.eqb func.(fn_params)
  && ListExt.sbinds Pos.eqb func.(fn_temps)
  && ListExt.dbinds Pos.eqb func.(fn_params) func.(fn_temps)
  && ListExt.sbinds Pos.eqb func.(fn_internals)
  && ListExt.dbinds Pos.eqb (func.(fn_params) ++ func.(fn_temps))
                            func.(fn_internals).

Definition type_fundef [cmd f_extra: Type]
  (type_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (ctx: ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef)
  (fd: fundef cmd f_extra) : bool :=
  match fd with
  | AST.Internal func => type_function type_cmd type_f_extra ctx func
  | AST.External ef => ExtFun.is_runtime ef || type_external_function ef
  end.

Definition type_globvar [cmd f_extra: Type]
  (ctx: ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef)
  (id: AST.ident) (gv: AST.globvar vardef) : bool :=
  type_init_data gv.(AST.gvar_init) gv.(AST.gvar_info).(var_type)
  && negb gv.(AST.gvar_readonly)
  && negb gv.(AST.gvar_volatile).

Definition type_globdef [cmd f_extra: Type]
  (type_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (ctx: ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef)
  (id: AST.ident) (gd: globdef cmd f_extra) : bool :=
  match gd with
  | AST.Gfun f => type_fundef type_cmd type_f_extra ctx f
  | AST.Gvar v => type_globvar ctx id v
  end.

Definition type_prog_defs [cmd f_extra: Type]
  (type_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (ctx: ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef)
  (defs: list (AST.ident * globdef cmd f_extra)) : bool :=
  ListExt.fold_left_b
    (fun ctx idg => type_globdef type_cmd type_f_extra ctx (fst idg) (snd idg))
    (fun ctx idg => Ctxt.add_global ctx idg)
    ctx defs.

Definition type_program [cmd f_extra p_extra: Type]
  (type_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (type_p_extra: program cmd f_extra p_extra -> bool)
  (p: program cmd f_extra p_extra) : bool :=
  type_prog_defs type_cmd type_f_extra
                 (ctxt_emp _ _ _ _ _ p.(prog_public)) p.(prog_defs)
  && forallb
       (fun id => existsb (fun idg => Pos.eqb (fst idg) id) p.(prog_defs))
       p.(prog_public)
  && existsb
       (fun idg => Pos.eqb (fst idg) p.(prog_main)
                   && match snd idg with AST.Gfun _ => true | _ => false end)
       p.(prog_defs)
  && ListExt.sbinds Pos.eqb p.(prog_defs)
  && type_p_extra p.

Lemma type_external_function_spec ef:
  Bool.reflect (exists sig, exf_funsig ef sig) (type_external_function ef).
Proof.
  unfold type_external_function.
  destruct (Facts.ef_sig_dec ef) as [sig|] eqn:E.
  - apply Facts.ef_sig_dec_spec in E.
    apply ReflectT.
    exact (ex_intro _ sig E).
  - apply ReflectF.
    intros (sig & SIG).
    apply Facts.ef_sig_dec_spec in SIG; congruence.
Qed.

Lemma type_function_complete [cmd f_extra: Type]
  [wt_f_extra: f_extra -> Prop]
  [wt_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Prop]
  (type_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (CMDcomplete: forall ctx c t, wt_cmd ctx c t -> type_cmd ctx c = Some t)
  (FEcomplete: forall fx, wt_f_extra fx -> type_f_extra fx = true)
  ctx func
  (WT: wt_function f_extra wt_f_extra wt_cmd ctx func):
  type_function type_cmd type_f_extra ctx func = true.
Proof.
  destruct WT as [WTCMD WTEXTRA SBp SBt DIST SBi IDIST].
  unfold type_function.
  repeat (apply Bool.andb_true_iff; split).
  - rewrite (CMDcomplete _ _ _ WTCMD); apply: reflect_refl eqb_spec _.
  - exact (FEcomplete _ WTEXTRA).
  - exact (proj1 (Bool.reflect_iff _ _ (ListExt.sbinds_spec _ Pos.eqb_spec _)) SBp).
  - exact (proj1 (Bool.reflect_iff _ _ (ListExt.sbinds_spec _ Pos.eqb_spec _)) SBt).
  - exact (proj1 (Bool.reflect_iff _ _ (ListExt.dbinds_spec _ Pos.eqb_spec _ _)) DIST).
  - exact (proj1 (Bool.reflect_iff _ _ (ListExt.sbinds_spec _ Pos.eqb_spec _)) SBi).
  - exact (proj1 (Bool.reflect_iff _ _ (ListExt.dbinds_spec _ Pos.eqb_spec _ _)) IDIST).
Qed.

Lemma type_function_correct [cmd f_extra: Type]
  [wt_f_extra: f_extra -> Prop]
  [wt_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Prop]
  (type_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (CMDcorrect: forall ctx c t, type_cmd ctx c = Some t -> wt_cmd ctx c t)
  (FEcorrect: forall fx, type_f_extra fx = true -> wt_f_extra fx)
  ctx func
  (H: type_function type_cmd type_f_extra ctx func = true):
  wt_function f_extra wt_f_extra wt_cmd ctx func.
Proof.
  unfold type_function in H.
  apply Bool.andb_true_iff in H; destruct H as [H IDIST].
  apply Bool.andb_true_iff in H; destruct H as [H SBi].
  apply Bool.andb_true_iff in H; destruct H as [H DIST].
  apply Bool.andb_true_iff in H; destruct H as [H SBt].
  apply Bool.andb_true_iff in H; destruct H as [H SBp].
  apply Bool.andb_true_iff in H; destruct H as [MATCH WTEXTRA].
  destruct (type_cmd (mk_function_ctxt _ _ _ _) (fn_body func)) as [t|] eqn:ETC;
    [| discriminate MATCH].
  move: MATCH => /(reflect_eq_of_true eqb_spec (x:=t) (y:=fn_return func)) MATCH; subst t.
  refine {|
    wt_fn_cmd := CMDcorrect _ _ _ ETC;
    wt_fn_extra := FEcorrect _ WTEXTRA;
    wt_fn_params_sbinds := _;
    wt_fn_temps_sbinds := _;
    wt_fn_params_temps_distinct := _;
    wt_fn_internals_sbinds := _;
    wt_fn_locals_internals_distinct := _;
  |}.
  - exact (proj2 (Bool.reflect_iff _ _ (ListExt.sbinds_spec _ Pos.eqb_spec _)) SBp).
  - exact (proj2 (Bool.reflect_iff _ _ (ListExt.sbinds_spec _ Pos.eqb_spec _)) SBt).
  - exact (proj2 (Bool.reflect_iff _ _ (ListExt.dbinds_spec _ Pos.eqb_spec _ _)) DIST).
  - exact (proj2 (Bool.reflect_iff _ _ (ListExt.sbinds_spec _ Pos.eqb_spec _)) SBi).
  - exact (proj2 (Bool.reflect_iff _ _ (ListExt.dbinds_spec _ Pos.eqb_spec _ _)) IDIST).
Qed.

Lemma type_fundef_complete [cmd f_extra: Type]
  [wt_f_extra: f_extra -> Prop]
  [wt_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Prop]
  (type_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (CMDcomplete: forall ctx c t, wt_cmd ctx c t -> type_cmd ctx c = Some t)
  (FEcomplete: forall fx, wt_f_extra fx -> type_f_extra fx = true)
  ctx fd
  (WT: wt_fundef f_extra wt_f_extra wt_cmd ctx fd):
  type_fundef type_cmd type_f_extra ctx fd = true.
Proof.
  destruct WT as [? func WTFN | ? ef WTef | ? name sg]; cbn [type_fundef].
  - eapply type_function_complete; eassumption.
  - destruct (type_external_function_spec ef) as [ | FALSE ];
      [ apply Bool.orb_true_r | exfalso; apply FALSE; econstructor; eassumption ].
  - reflexivity.
Qed.

Lemma type_fundef_correct [cmd f_extra: Type]
  [wt_f_extra: f_extra -> Prop]
  [wt_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Prop]
  (type_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (CMDcorrect: forall ctx c t, type_cmd ctx c = Some t -> wt_cmd ctx c t)
  (FEcorrect: forall fx, type_f_extra fx = true -> wt_f_extra fx)
  ctx fd
  (H: type_fundef type_cmd type_f_extra ctx fd = true):
  wt_fundef f_extra wt_f_extra wt_cmd ctx fd.
Proof.
  destruct fd as [func | ef]; cbn [type_fundef] in H.
  - eapply wt_Internal, type_function_correct; eassumption.
  - destruct (ExtFun.is_runtime ef) eqn:RT.
    + destruct ef; try discriminate RT; apply wt_External_runtime.
    + cbn [orb] in H.
      destruct (type_external_function_spec ef) as [ (sig & SIG) | ]; [ clear H | discriminate ].
      eapply wt_External; eassumption.
Qed.

Lemma type_globvar_spec [cmd f_extra: Type]
  (ctx: ctxt Empty_set Empty_set Empty_set (fundef cmd f_extra) vardef) id (gv: AST.globvar vardef):
  Bool.reflect (wt_globvar id gv) (type_globvar ctx id gv).
Proof.
  unfold type_globvar.
  destruct (Facts.type_init_data_spec gv.(AST.gvar_init) gv.(AST.gvar_info).(var_type))
    as [WTINIT | NI]; cbn [andb];
    [| apply ReflectF; intros [WT _ _]; contradiction ].
  destruct gv.(AST.gvar_readonly) eqn:ER; cbn [negb andb];
    [ apply ReflectF; intros [_ RO _]; congruence |].
  destruct gv.(AST.gvar_volatile) eqn:EV; cbn [negb];
    [ apply ReflectF; intros [_ _ VOL]; congruence |].
  apply ReflectT; constructor; assumption.
Qed.

Lemma type_globdef_spec [cmd f_extra: Type]
  [wt_f_extra: f_extra -> Prop]
  [wt_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Prop]
  (type_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (CMDcomplete: forall ctx c t, wt_cmd ctx c t -> type_cmd ctx c = Some t)
  (CMDcorrect: forall ctx c t, type_cmd ctx c = Some t -> wt_cmd ctx c t)
  (FEcomplete: forall fx, wt_f_extra fx -> type_f_extra fx = true)
  (FEcorrect: forall fx, type_f_extra fx = true -> wt_f_extra fx)
  ctx id gd:
  Bool.reflect (wt_globdef f_extra wt_f_extra wt_cmd ctx id gd)
               (type_globdef type_cmd type_f_extra ctx id gd).
Proof.
  destruct gd as [f | v]; cbn [type_globdef].
  - destruct (type_fundef type_cmd type_f_extra ctx f) eqn:E.
    + apply ReflectT, wt_Gfun.
      eapply type_fundef_correct; eassumption.
    + apply ReflectF. intros W; inversion W as [? ? f' WTf | ]; subst.
      pose proof (type_fundef_complete type_cmd type_f_extra CMDcomplete FEcomplete _ _ WTf) as EQ.
      congruence.
  - destruct (type_globvar_spec ctx id v).
    + apply ReflectT, wt_Gvar; assumption.
    + apply ReflectF. intros W; inversion W as [ | ? ? v' WTv]; subst.
      contradiction.
Qed.

Lemma type_prog_defs_complete [cmd f_extra: Type]
  [wt_f_extra: f_extra -> Prop]
  [wt_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Prop]
  (type_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (CMDcomplete: forall ctx c t, wt_cmd ctx c t -> type_cmd ctx c = Some t)
  (CMDcorrect: forall ctx c t, type_cmd ctx c = Some t -> wt_cmd ctx c t)
  (FEcomplete: forall fx, wt_f_extra fx -> type_f_extra fx = true)
  (FEcorrect: forall fx, type_f_extra fx = true -> wt_f_extra fx)
  ctx defs
  (FF: ListExt.FoldLeft
         (fun ctx idg => wt_globdef f_extra wt_f_extra wt_cmd ctx (fst idg) (snd idg))
         (fun ctx idg => Ctxt.add_global ctx idg) ctx defs) :
  type_prog_defs type_cmd type_f_extra ctx defs = true.
Proof.
  unfold type_prog_defs.
  induction FF as [| acc x rest FFx FFrest IH]; cbn.
  - reflexivity.
  - apply Bool.andb_true_iff; split; [| exact IH ].
    exact (proj1 (Bool.reflect_iff _ _
                    (type_globdef_spec type_cmd type_f_extra
                       CMDcomplete CMDcorrect FEcomplete FEcorrect _ _ _)) FFx).
Qed.

Lemma type_prog_defs_correct [cmd f_extra: Type]
  [wt_f_extra: f_extra -> Prop]
  [wt_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Prop]
  (type_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (CMDcomplete: forall ctx c t, wt_cmd ctx c t -> type_cmd ctx c = Some t)
  (CMDcorrect: forall ctx c t, type_cmd ctx c = Some t -> wt_cmd ctx c t)
  (FEcomplete: forall fx, wt_f_extra fx -> type_f_extra fx = true)
  (FEcorrect: forall fx, type_f_extra fx = true -> wt_f_extra fx)
  ctx defs
  (H: type_prog_defs type_cmd type_f_extra ctx defs = true) :
  ListExt.FoldLeft
    (fun ctx idg => wt_globdef f_extra wt_f_extra wt_cmd ctx (fst idg) (snd idg))
    (fun ctx idg => Ctxt.add_global ctx idg) ctx defs.
Proof.
  unfold type_prog_defs in H.
  revert ctx H. induction defs as [| idg rest IH]; intros ctx H; cbn in H.
  - constructor.
  - apply Bool.andb_true_iff in H as [IDG REST].
    constructor.
    + exact (proj2 (Bool.reflect_iff _ _
                      (type_globdef_spec type_cmd type_f_extra
                         CMDcomplete CMDcorrect FEcomplete FEcorrect _ _ _)) IDG).
    + apply IH; exact REST.
Qed.

Lemma type_program_spec [cmd f_extra p_extra: Type]
  [wt_f_extra: f_extra -> Prop]
  [wt_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> type -> Prop]
  [wt_p_extra: program cmd f_extra p_extra -> Prop]
  (type_cmd: ctxt (type * bool) (type * bool) unit (fundef cmd f_extra) vardef -> cmd -> option type)
  (type_f_extra: f_extra -> bool)
  (type_p_extra: program cmd f_extra p_extra -> bool)
  (CMDcomplete: forall ctx c t, wt_cmd ctx c t -> type_cmd ctx c = Some t)
  (CMDcorrect: forall ctx c t, type_cmd ctx c = Some t -> wt_cmd ctx c t)
  (FEcomplete: forall fx, wt_f_extra fx -> type_f_extra fx = true)
  (FEcorrect: forall fx, type_f_extra fx = true -> wt_f_extra fx)
  (PEspec: forall p, Bool.reflect (wt_p_extra p) (type_p_extra p))
  p:
  Bool.reflect (wt_program wt_f_extra wt_cmd wt_p_extra p)
               (type_program type_cmd type_f_extra type_p_extra p).
Proof.
  unfold type_program.
  apply Bool.iff_reflect; split.
  - intros [DEFS PUB MAIN SB PE].
    repeat (apply Bool.andb_true_iff; split).
    + eapply type_prog_defs_complete; eassumption.
    + apply forallb_forall; intros id INid.
      destruct (PUB id INid) as [gd IN].
      apply existsb_exists. exists (id, gd); split; [exact IN |].
      now apply Pos.eqb_eq.
    + destruct MAIN as [f_main MAIN].
      apply existsb_exists. exists (prog_main p, AST.Gfun f_main).
      split; [exact MAIN |].
      apply Bool.andb_true_iff; split.
      * apply Pos.eqb_eq; reflexivity.
      * reflexivity.
    + exact (proj1 (Bool.reflect_iff _ _ (ListExt.sbinds_spec _ Pos.eqb_spec _)) SB).
    + exact (proj1 (Bool.reflect_iff _ _ (PEspec p)) PE).
  - intros H.
    apply Bool.andb_true_iff in H as [H PE].
    apply Bool.andb_true_iff in H as [H SB].
    apply Bool.andb_true_iff in H as [H MAIN].
    apply Bool.andb_true_iff in H as [DEFS PUB].
    refine {|
      wt_prog_defs := _;
      wt_prog_public := _;
      wt_prog_main := _;
      wt_prog_defs_sbinds := _;
      wt_prog_extra := _;
    |}.
    + eapply type_prog_defs_correct; eassumption.
    + intros id INid.
      pose proof (proj1 (forallb_forall _ _) PUB id INid) as EX.
      apply existsb_exists in EX as [[id' gd] [IN EQ]].
      cbn in EQ; apply Pos.eqb_eq in EQ; subst id'.
      exists gd; exact IN.
    + apply existsb_exists in MAIN as [[id gd] [IN EQ]].
      cbn in EQ.
      apply Bool.andb_true_iff in EQ as [IDEQ GF].
      apply Pos.eqb_eq in IDEQ; subst id.
      destruct gd as [f | v]; [| discriminate GF].
      exists f; exact IN.
    + exact (proj2 (Bool.reflect_iff _ _ (ListExt.sbinds_spec _ Pos.eqb_spec _)) SB).
    + exact (proj2 (Bool.reflect_iff _ _ (PEspec p)) PE).
Qed.
