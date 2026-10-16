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


From HB Require Import structures.

From GallinaC.Utils Require Import ListExt OptionExt UnitExt ReflectExt PTreeExt CompCertExt.
From GallinaC.Utils Require Import ProdExt BoolExt PosExt NatExt NExt.
From GallinaC.Imp Require Import While.
From GallinaC.Imp Require Import Addr Heap Store Storable State.
From GallinaC.Imp Require Import Primitives PrimitivesProp.
From GallinaC.Compiler.Common Require Import Types Ctxt Value Expr.
From GallinaC.Compiler.Deep Require Import Cmd Prog Typing.
From GallinaC.Compiler.Deep Require Export OpSem Denotation.
From GallinaC.Compiler.Deep Require Import Lemmas.
From Stdlib Require Import Eqdep_dec FunctionalExtensionality Morphisms ZArith PArith.
From compcert.lib Require Import Integers Floats.
From Corelib Require Import ssreflect.
Import OpSem.Typing(wt_state).

Local Open Scope separation_scope.

Section Agree.

Context {Sm: State.type}.
Context (exfs: @exf_env Sm).
Local Notation Nm := (@var_name Sm).
Local Notation Pt := (@ptr_t Sm).
Local Notation Vl := (value (@ptr_t Sm)).

Local Notation denote_type := (denote_type (Sm:=Sm)).
Local Notation denote_binding := (denote_binding (Sm:=Sm)).
Local Notation denote_type_memval := (denote_type_memval (Sm:=Sm)).
Local Notation denote_local := (denote_local (Sm:=Sm)).
Local Notation denote_globdef := (denote_globdef (Sm:=Sm)).
Local Notation denote_sig' := (denote_sig').
Local Notation denote_binding_eq := (denote_binding_eq (Sm:=Sm)).
Local Notation denote_binding_false_eq := (denote_binding_false_eq (Sm:=Sm)).
Local Notation denote_value := (denote_value (Sm:=Sm)).
Local Notation denote_value_eq := (denote_value_eq (Sm:=Sm)).
Local Notation denote_env := (denote_env (Sm:=Sm)).
Local Notation denote_ctxt := (denote_ctxt (Sm:=Sm)).
Local Notation denote_glob_ctxt_of_program := (denote_glob_ctxt_of_program (Sm:=Sm) exfs).
Local Notation denote_external_function := (denote_external_function (Sm:=Sm) exfs).
Local Notation denote_expr := (denote_expr (Sm:=Sm)).
Local Notation denote_cmd := (denote_cmd (Sm:=Sm)).
Local Notation denote_cont := (denote_cont (Sm:=Sm)).
Local Notation denote_state := (denote_state (Sm:=Sm) exfs).
Local Notation denote_fundef_call := (denote_fundef_call (Sm:=Sm) exfs).
Local Notation denote_globdef_value := (denote_globdef_value (Sm:=Sm) exfs).
Local Notation denote_prog_defs_fold := (denote_prog_defs_fold (Sm:=Sm) exfs).

Lemma conv_option_app [A: EqDec.type]
  [Q: option A -> Type] [T: Type] [X: option A]
  [fS: forall a, X = Some a -> Q (Some a) -> T]
  [fN: X = None -> Q None -> T]
  [a] (EQa: X = Some a) (W: Q X):
  (match X as o return (X = o -> Q o -> T) with
   | Some a0 => fS a0 | None => fN end) eq_refl W
  = fS a EQa (eq_rect X Q W (Some a) EQa).
Proof using Type.
  destruct X as [a0|]; [| discriminate EQa].
  assert (a0 = a) as -> by (injection EQa; auto).
  assert (EQa = eq_refl) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec (option A)))).
  reflexivity.
Qed.

Lemma conv_option_app_None [A: EqDec.type]
  [Q: option A -> Type] [T: Type] [X: option A]
  [fS: forall a, X = Some a -> Q (Some a) -> T]
  [fN: X = None -> Q None -> T]
  (EQn: X = None) (W: Q X):
  (match X as o return (X = o -> Q o -> T) with
   | Some a0 => fS a0 | None => fN end) eq_refl W
  = fN EQn (eq_rect X Q W None EQn).
Proof using Type.
  destruct X as [a0|]; [ discriminate EQn |].
  assert (EQn = eq_refl) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec (option A)))).
  reflexivity.
Qed.

Lemma conv_bool_app_false [Q: bool -> Type] [T: Type] [X: bool]
  [fT: X = true -> Q true -> T]
  [fF: X = false -> Q false -> T]
  (EQf: X = false) (W: Q X):
  (match X as b return (X = b -> Q b -> T) with
   | true => fT | false => fF end) eq_refl W
  = fF EQf (eq_rect X Q W false EQf).
Proof using Type.
  destruct X; [ discriminate EQf |].
  assert (EQf = eq_refl) as -> by (apply UIP_dec, Bool.bool_dec).
  reflexivity.
Qed.

Lemma conv_bool_app
  [Q: bool -> Type] [T: Type] [X: bool]
  [fT: X = true -> Q true -> T]
  [fF: X = false -> Q false -> T]
  (EQtrue: X = true) (W: Q X) :
  (if X as b return (X = b -> Q b -> T) then fT else fF) eq_refl W
  = fT EQtrue (eq_rect X (fun b => Q b) W true EQtrue).
Proof using Type.
  destruct X; [| discriminate EQtrue].
  assert (EQtrue = eq_refl) as -> by (apply UIP_dec, Bool.bool_dec).
  reflexivity.
Qed.

Lemma conv_bool_app'
  [Q: bool -> Type] [T: Type] [X: bool]
  [fT: Q true -> T] [fF: Q false -> T] (EQtrue: X = true) (W: Q X) :
  (match X as b return (Q b -> T) with true => fT | false => fF end) W
  = fT (eq_rect X Q W true EQtrue).
Proof using Type.
  destruct X; [ | discriminate EQtrue ].
  assert (EQtrue = eq_refl) as -> by (apply UIP_dec, Bool.bool_dec).
  reflexivity.
Qed.


Lemma convert_eq_refl_id (a: type) (E: a = a) (v: denote_type a) :
  convert_eq (f_equal denote_type E) v = v.
Proof using Type.
  now assert (E = eq_refl) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect type_eqb_spec)).
Qed.

Lemma denote_cont_pirr {ctx} {k: @OpSem.cont Sm} {t}
  (W1 W2: OpSem.Typing.type_cont ctx k = Some t) env stack
  (glob: denote_glob_ctxt Sm ctx) v :
  denote_cont W1 env stack glob v = denote_cont W2 env stack glob v.
Proof using Type.
  assert (W1 = W2) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec (option type)))).
  reflexivity.
Qed.

Lemma denote_cont_call_pirr {ctx} {k: @OpSem.cont Sm} {t}
  (W1 W2: OpSem.Typing.type_cont_call ctx k = Some t)
  (glob: denote_glob_ctxt Sm ctx) v :
  denote_cont_call W1 glob v = denote_cont_call W2 glob v.
Proof using Type.
  assert (W1 = W2) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec (option type)))).
  reflexivity.
Qed.

Lemma denote_cont_stack_eq {base: ctxt (type*bool) (type*bool) unit fundef vardef}
  {sl1 sl2: list unit} (E: sl1 = sl2) {k: @OpSem.cont Sm} {t}
  (WT1: OpSem.Typing.type_cont (with_stack sl1 base) k = Some t)
  (WT2: OpSem.Typing.type_cont (with_stack sl2 base) k = Some t)
  (env: denote_pure_ctxt Sm base) (stack1: denote_stack (denote_local) sl1)
  (glob: denote_glob_ctxt Sm base) v :
  denote_cont WT1 env stack1 glob v
  = denote_cont WT2 env (eq_rect sl1 (denote_stack (denote_local)) stack1 sl2 E) glob v.
Proof using Type.
  destruct E. apply denote_cont_pirr.
Qed.

Lemma denote_cmd_pirr {ctx} {c: cmd} {t}
  (W1 W2: type_cmd ctx c = Some t) (env: denote_ctxt ctx) :
  denote_cmd W1 env = denote_cmd W2 env.
Proof using Type.
  assert (W1 = W2) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec (option type)))).
  reflexivity.
Qed.

Lemma denote_cmd_stack_eq {base: ctxt (type*bool) (type*bool) unit fundef vardef}
  {sl1 sl2: list unit} (E: sl1 = sl2) {c: cmd} {t}
  (WT1: type_cmd (with_stack sl1 base) c = Some t)
  (WT2: type_cmd (with_stack sl2 base) c = Some t)
  (env: denote_pure_ctxt Sm base) (stack1: denote_stack (denote_local) sl1)
  (glob: denote_glob_ctxt Sm base) :
  denote_cmd WT1 (env, stack1, glob)
  = denote_cmd WT2 (env, eq_rect sl1 (denote_stack (denote_local)) stack1 sl2 E, glob).
Proof using Type.
  destruct E. apply denote_cmd_pirr.
Qed.

Lemma denote_state_State
  (p: Prog.program) (f:function) (c:cmd) (k: @OpSem.cont Sm) (e:Maps.PTree.t Vl)
  (locals:list (Nm)) (mem: Sm) (t:type)
  (WTp: type_program p = true)
  (WT: OpSem.Typing.type_state p (OpSem.State f c k e locals mem) = Some t)
  (ty_env: Maps.PTree.t (type*bool)) (TENV: OpSem.Typing.type_env f e = Some ty_env)
  (t_c: type) (WTCMD: type_cmd (OpSem.Typing.state_ctxt p f ty_env locals) c = Some t_c)
  (t_k: type) (WTCONT: OpSem.Typing.type_cont (OpSem.Typing.state_ctxt p f ty_env locals) k = Some t_k)
  (EQ: type_eqb t_c t_k = true)
  (WTFN: type_function (mk_glob_ctxt p) f = true) :
  denote_state WTp WT
  = (do v <- denote_cmd WTCMD (denote_env TENV, denote_locals locals, denote_glob_ctxt_of_program p WTp);
     denote_cont WTCONT (denote_env TENV) (denote_locals locals) (denote_glob_ctxt_of_program p WTp)
       (convert_eq (f_equal denote_type (reflect_eq_of_true type_eqb_spec EQ)) v))%program.
Proof using Type.
  unfold denote_state.
  rewrite (conv_bool_app WTFN).
  erewrite (conv_option_app TENV).
  erewrite (conv_option_app WTCMD).
  erewrite (conv_option_app WTCONT).
  erewrite (conv_bool_app EQ).
  reflexivity.
Qed.

Lemma denote_state_Callstate
  (p: Prog.program) (f: fundef) (args: list Vl) (k: @OpSem.cont Sm)
  (mem: Sm) (t: type)
  (WTp: type_program p = true)
  (WT: OpSem.Typing.type_state p (OpSem.Callstate f args k mem) = Some t)
  (sig: signature) (SIG: type_funsig f = Some sig)
  (WTFD: type_fundef (mk_glob_ctxt p) f = true)
  (t_k: type) (WTCONT: OpSem.Typing.type_cont_call (mk_glob_ctxt p) k = Some t_k)
  (EQ: type_eqb t_k sig.(sig_res) = true)
  (WTARGS: type_call_args args sig.(sig_args) = true) :
  denote_state WTp WT
  = (do v <- denote_fundef_call WTFD SIG (denote_glob_ctxt_of_program p WTp) args;
     denote_cont_call WTCONT (denote_glob_ctxt_of_program p WTp)
       (convert_eq (f_equal denote_type (eq_sym (reflect_eq_of_true type_eqb_spec EQ))) v))%program.
Proof using Type.
  unfold denote_state.
  erewrite (conv_option_app SIG).
  erewrite (conv_bool_app WTFD).
  erewrite (conv_bool_app WTARGS).
  erewrite (conv_option_app WTCONT).
  erewrite (conv_bool_app EQ).
  reflexivity.
Qed.

Lemma denote_state_Returnstate
  (p: Prog.program) (v: Vl) (k: @OpSem.cont Sm)
  (mem: Sm) (t: type)
  (WTp: type_program p = true)
  (WT: OpSem.Typing.type_state p (OpSem.Returnstate v k mem) = Some t)
  (t_k: type) (WTCONT: OpSem.Typing.type_cont_call (mk_glob_ctxt p) k = Some t_k)
  (EQ: type_eqb (Value.type_of_value v) t_k = true) :
  denote_state WTp WT
  = denote_cont_call WTCONT (denote_glob_ctxt_of_program p WTp)
      (denote_value_eq (reflect_eq_of_true type_eqb_spec EQ)).
Proof using Type.
  unfold denote_state.
  erewrite (conv_option_app WTCONT).
  erewrite (conv_bool_app EQ).
  reflexivity.
Qed.

Lemma denote_cmd_bind {ctx} {id_b t_b c_b c_c} {t_res}
  (WT: type_cmd ctx (c_bind id_b t_b c_b c_c) = Some t_res)
  (env: denote_ctxt ctx)
  (GET: get_pure id_b ctx = Some (t_b, false))
  (WTc1: type_cmd ctx c_b = Some t_b)
  (WTc2: type_cmd (set_pure id_b (t_b, true) ctx) c_c = Some t_res) :
  denote_cmd WT env =
  (do v <- denote_cmd WTc1 env;
   denote_cmd WTc2 (denote_tree_set id_b (denote_binding_eq t_b) v (fst (fst env)), snd (fst env), snd env))%program.
Proof using Type.
  cbn [denote_cmd].
  erewrite (conv_option_app GET).
  cbn match beta iota.
  erewrite (conv_bool_app (ReflectExt.reflect_refl type_eqb_spec t_b)).
  erewrite (conv_option_app WTc1).
  erewrite (conv_bool_app (ReflectExt.reflect_refl type_eqb_spec t_b)).
  erewrite (conv_option_app WTc2).
  rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  destruct t_b; reflexivity.
Qed.

Lemma denote_cont_kbind {ctx} {id t_b c k'}
  (WT: OpSem.Typing.type_cont ctx (OpSem.Kbind id c k') = Some t_b)
  (env: denote_pure_ctxt Sm ctx) (stack: denote_stack_ctxt Sm ctx)
  (glob: denote_glob_ctxt Sm ctx) (v: denote_type t_b)
  (GET: get_pure id ctx = Some (t_b, false))
  t_c (WTc: type_cmd (set_pure id (t_b, true) ctx) c = Some t_c)
  (WTk: OpSem.Typing.type_cont ctx k' = Some t_c) :
  denote_cont WT env stack glob v =
  (do v' <- denote_cmd WTc (denote_tree_set id (denote_binding_eq t_b) v env, stack, glob);
   denote_cont WTk env stack glob v')%program.
Proof using Type.
  cbn [denote_cont].
  erewrite (conv_option_app GET).
  cbn match beta iota.
  erewrite (conv_option_app WTc).
  erewrite (conv_option_app WTk).
  erewrite (conv_bool_app (ReflectExt.reflect_refl type_eqb_spec t_c)).
  rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  destruct t_c; reflexivity.
Qed.

Lemma denote_cmd_while {ctx} {c_cond c_body}
  (WT: type_cmd ctx (c_while c_cond c_body) = Some t_unit)
  (env: denote_ctxt ctx)
  (WTcond: type_cmd ctx c_cond = Some t_bool)
  (WTbody: type_cmd ctx c_body = Some t_unit) :
  denote_cmd WT env =
  while (denote_cmd WTcond env) (denote_cmd WTbody env).
Proof using Type.
  cbn [denote_cmd].
  erewrite (conv_option_app WTcond).
  cbn match beta iota.
  erewrite (conv_option_app WTbody).
  cbn match beta iota.
  rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  reflexivity.
Qed.

Lemma denote_cont_Kloop1 {ctx} {c_cond c_body} {k': @OpSem.cont Sm}
  (WT: OpSem.Typing.type_cont ctx (OpSem.Kloop1 c_cond c_body k') = Some t_bool)
  (env: denote_pure_ctxt Sm ctx) (stack: denote_stack_ctxt Sm ctx)
  (glob: denote_glob_ctxt Sm ctx) (v: denote_type t_bool)
  (WTcond: type_cmd ctx c_cond = Some t_bool)
  (WTbody: type_cmd ctx c_body = Some t_unit)
  (WTk: OpSem.Typing.type_cont ctx k' = Some t_unit) :
  denote_cont WT env stack glob v =
  (if v
   then (do _ <- denote_cmd WTbody (env, stack, glob);
         do _ <- while (denote_cmd WTcond (env, stack, glob)) (denote_cmd WTbody (env, stack, glob));
         denote_cont WTk env stack glob tt)
   else denote_cont WTk env stack glob tt)%program.
Proof using Type.
  cbn [denote_cont].
  erewrite (conv_option_app WTcond).
  cbn match beta iota.
  erewrite (conv_option_app WTbody).
  cbn match beta iota.
  erewrite (conv_option_app WTk).
  cbn match beta iota.
  rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  reflexivity.
Qed.

Lemma denote_cont_Kloop2 {ctx} {c_cond c_body} {k': @OpSem.cont Sm}
  (WT: OpSem.Typing.type_cont ctx (OpSem.Kloop2 c_cond c_body k') = Some t_unit)
  (env: denote_pure_ctxt Sm ctx) (stack: denote_stack_ctxt Sm ctx)
  (glob: denote_glob_ctxt Sm ctx) (v: denote_type t_unit)
  (WTcond: type_cmd ctx c_cond = Some t_bool)
  (WTbody: type_cmd ctx c_body = Some t_unit)
  (WTk: OpSem.Typing.type_cont ctx k' = Some t_unit) :
  denote_cont WT env stack glob v =
  (do _ <- while (denote_cmd WTcond (env, stack, glob)) (denote_cmd WTbody (env, stack, glob));
   denote_cont WTk env stack glob tt)%program.
Proof using Type.
  cbn [denote_cont].
  erewrite (conv_option_app WTcond).
  cbn match beta iota.
  erewrite (conv_option_app WTbody).
  cbn match beta iota.
  erewrite (conv_option_app WTk).
  cbn match beta iota.
  rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  reflexivity.
Qed.

Lemma denote_cont_Kscope_unbind {ctx} {id} {k': @OpSem.cont Sm} {t'}
  (WT: OpSem.Typing.type_cont ctx (OpSem.Kscope (OpSem.scope_bind id) k') = Some t')
  (env: denote_pure_ctxt Sm ctx) (stack: denote_stack_ctxt Sm ctx)
  (glob: denote_glob_ctxt Sm ctx) (v: denote_type t')
  t (GET: get_pure id ctx = Some (t, true))
  (WTk: OpSem.Typing.type_cont (set_pure id (t, false) ctx) k' = Some t') :
  denote_cont WT env stack glob v =
  denote_cont WTk (denote_tree_unset id (denote_binding_false_eq t) env) stack glob v.
Proof using Type.
  cbn [denote_cont].
  erewrite (conv_option_app GET).
  cbn match beta iota.
  apply denote_cont_pirr.
Qed.

Lemma denote_cont_Kscope_pop {ctx} {k': @OpSem.cont Sm} {t'}
  (WT: OpSem.Typing.type_cont ctx (OpSem.Kscope OpSem.scope_store k') = Some t')
  (env: denote_pure_ctxt Sm ctx) (stack: denote_stack_ctxt Sm ctx)
  (glob: denote_glob_ctxt Sm ctx) (v: denote_type t')
  s0 sl0 (STACK_NONEMPTY: ctxt_stack ctx = s0 :: sl0)
  (WTk: OpSem.Typing.type_cont (with_stack (removelast (ctxt_stack ctx)) ctx) k' = Some t') :
  denote_cont WT env stack glob v =
  (do s <- get;
   match pop (store s) with
   | Some st =>
       match mk_state_opt st (scnt s) (heap s) (alc s) with
       | Some s' =>
           put s';;
           denote_cont WTk env (denote_stack_removelast _ _ stack) glob v
       | None => fail
       end
   | None => fail
   end)%program.
Proof using Type.
  cbn [OpSem.Typing.type_cont] in WT.
  cbn [denote_cont].
  revert WT stack.
  destruct (ctxt_stack ctx) as [|s0' sl0'] eqn:E; [ congruence | ].
  intros WT stack.
  apply bind_Proper; [reflexivity|]; intros s.
  destruct (pop (store s)); [|reflexivity].
  destruct (mk_state_opt _ _ _ _); [|reflexivity].
  apply bind_Proper; [reflexivity|]; intros _.
  apply denote_cont_pirr.
Qed.

Lemma type_state_State_inv p f c k e locals mem t :
  @OpSem.Typing.type_state Sm p (OpSem.State f c k e locals mem) = Some t ->
  exists ty_env t_c t_k,
    OpSem.Typing.type_env f e = Some ty_env /\
    type_cmd (OpSem.Typing.state_ctxt p f ty_env locals) c = Some t_c /\
    OpSem.Typing.type_cont (OpSem.Typing.state_ctxt p f ty_env locals) k = Some t_k /\
    type_eqb t_c t_k = true /\ t_c = t /\
    type_function (mk_glob_ctxt p) f = true.
Proof using Type.
  cbn [OpSem.Typing.type_state]. intro H.
  destruct (type_function (mk_glob_ctxt p) f) eqn:WTFN; [|discriminate].
  destruct (OpSem.Typing.type_env f e) as [ty_env|] eqn:TENV; [|discriminate].
  destruct (type_cmd _ c) as [t_c|] eqn:WTCMD; [|discriminate].
  destruct (OpSem.Typing.type_cont _ k) as [t_k|] eqn:WTCONT; [|discriminate].
  destruct (type_eqb t_c t_k) eqn:EQ; [|discriminate].
  injection H as <-. eauto 12.
Qed.

Lemma type_state_Callstate_inv p f args k mem t :
  @OpSem.Typing.type_state Sm p (OpSem.Callstate f args k mem) = Some t ->
  exists sig t_k,
    type_funsig f = Some sig /\
    type_fundef (mk_glob_ctxt p) f = true /\
    OpSem.Typing.type_cont_call (mk_glob_ctxt p) k = Some t_k /\
    type_eqb t_k sig.(sig_res) = true /\ t_k = t /\
    type_call_args args sig.(sig_args) = true.
Proof using Type.
  cbn [OpSem.Typing.type_state]. intro H.
  destruct (type_funsig f) as [sig|] eqn:SIG; [|discriminate].
  destruct (type_fundef (mk_glob_ctxt p) f) eqn:WTFD; [|discriminate].
  destruct (type_call_args args sig.(sig_args)) eqn:WTARGS; [|discriminate].
  destruct (OpSem.Typing.type_cont_call (mk_glob_ctxt p) k) as [t_k|] eqn:WTCONT; [|discriminate].
  destruct (type_eqb t_k sig.(sig_res)) eqn:EQ; [|discriminate].
  injection H as <-. eauto 12.
Qed.

Lemma type_cmd_bind_inv ctx id_b t_b c_b c_c t :
  type_cmd ctx (c_bind id_b t_b c_b c_c) = Some t ->
  get_pure id_b ctx = Some (t_b, false) /\
  type_cmd ctx c_b = Some t_b /\
  type_cmd (set_pure id_b (t_b, true) ctx) c_c = Some t.
Proof using Type.
  cbn [type_cmd]. intro H.
  destruct (get_pure id_b ctx) as [[t1 [|]]|] eqn:GET; try discriminate.
  destruct (eqb_spec t_b t1); [subst t1|discriminate].
  destruct (type_cmd ctx c_b) as [t_b'|] eqn:WTc1; [|discriminate].
  destruct (eqb_spec t_b t_b'); [subst t_b'|discriminate].
  destruct (type_cmd (set_pure id_b (t_b, true) ctx) c_c) as [t_c|] eqn:WTc2; [|discriminate].
  injection H as <-. auto.
Qed.

Lemma type_cont_kbind_inv ctx id c (k': @OpSem.cont Sm) t :
  OpSem.Typing.type_cont ctx (OpSem.Kbind id c k') = Some t ->
  get_pure id ctx = Some (t, false) /\
  exists t_c, type_cmd (set_pure id (t, true) ctx) c = Some t_c /\
              OpSem.Typing.type_cont ctx k' = Some t_c.
Proof using Type.
  cbn [OpSem.Typing.type_cont]. intro H.
  destruct (get_pure id ctx) as [[t_b [|]]|] eqn:GET; try discriminate.
  destruct (type_cmd (set_pure id (t_b, true) ctx) c) as [t_c|] eqn:WTc; [|discriminate].
  destruct (OpSem.Typing.type_cont ctx k') as [t_c'|] eqn:WTk; [|discriminate].
  destruct (type_eqb_spec t_c t_c'); [subst t_c' |discriminate].
  injection H as <-. eauto.
Qed.

Lemma type_cmd_while_inv ctx c_cond c_body t :
  type_cmd ctx (c_while c_cond c_body) = Some t ->
  type_cmd ctx c_cond = Some t_bool /\
  type_cmd ctx c_body = Some t_unit /\
  t = t_unit.
Proof using Type.
  cbn [type_cmd]. intro H.
  destruct (type_cmd ctx c_cond) as [[ | | | | ]|] eqn:Wc; try discriminate.
  destruct (type_cmd ctx c_body) as [[ | | | | ]|] eqn:Wb; try discriminate.
  injection H as <-. auto.
Qed.

Lemma type_cont_Kloop1_inv ctx c_cond c_body (k': @OpSem.cont Sm) t :
  OpSem.Typing.type_cont ctx (OpSem.Kloop1 c_cond c_body k') = Some t ->
  type_cmd ctx c_cond = Some t_bool /\
  type_cmd ctx c_body = Some t_unit /\
  OpSem.Typing.type_cont ctx k' = Some t_unit /\
  t = t_bool.
Proof using Type.
  cbn [OpSem.Typing.type_cont]. intro H.
  destruct (type_cmd ctx c_cond) as [[ | | | | ]|] eqn:Wc; try discriminate.
  destruct (type_cmd ctx c_body) as [[ | | | | ]|] eqn:Wb; try discriminate.
  destruct (OpSem.Typing.type_cont ctx k') as [[ | | | | ]|] eqn:Wk; try discriminate.
  injection H as <-. auto.
Qed.

Lemma type_cont_Kloop2_inv ctx c_cond c_body (k': @OpSem.cont Sm) t :
  OpSem.Typing.type_cont ctx (OpSem.Kloop2 c_cond c_body k') = Some t ->
  type_cmd ctx c_cond = Some t_bool /\
  type_cmd ctx c_body = Some t_unit /\
  OpSem.Typing.type_cont ctx k' = Some t_unit /\
  t = t_unit.
Proof using Type.
  cbn [OpSem.Typing.type_cont]. intro H.
  destruct (type_cmd ctx c_cond) as [[ | | | | ]|] eqn:Wc; try discriminate.
  destruct (type_cmd ctx c_body) as [[ | | | | ]|] eqn:Wb; try discriminate.
  destruct (OpSem.Typing.type_cont ctx k') as [[ | | | | ]|] eqn:Wk; try discriminate.
  injection H as <-. auto.
Qed.

Lemma type_cont_Kscope_unbind_inv ctx id (k': @OpSem.cont Sm) t' :
  OpSem.Typing.type_cont ctx (OpSem.Kscope (OpSem.scope_bind id) k') = Some t' ->
  exists t, get_pure id ctx = Some (t, true) /\
            OpSem.Typing.type_cont (set_pure id (t, false) ctx) k' = Some t'.
Proof using Type.
  cbn [OpSem.Typing.type_cont]. intro H.
  destruct (get_pure id ctx) as [[t [|]]|] eqn:GET; try discriminate.
  eauto.
Qed.

Lemma type_cont_Kscope_pop_inv ctx (k': @OpSem.cont Sm) t' :
  OpSem.Typing.type_cont ctx (OpSem.Kscope OpSem.scope_store k') = Some t' ->
  exists s0 sl0, ctxt_stack ctx = s0 :: sl0 /\
                 OpSem.Typing.type_cont (with_stack (removelast (ctxt_stack ctx)) ctx) k' = Some t'.
Proof using Type.
  cbn [OpSem.Typing.type_cont]. intro H.
  destruct (ctxt_stack ctx) as [|s0 sl0] eqn:E.
  - discriminate H.
  - exists s0, sl0. split; [reflexivity|].
    exact H.
Qed.

Lemma type_state_Returnstate_inv p v (k: @OpSem.cont Sm) mem t :
  @OpSem.Typing.type_state Sm p (OpSem.Returnstate v k mem) = Some t ->
  exists t_k,
    OpSem.Typing.type_cont_call (mk_glob_ctxt p) k = Some t_k /\
    type_eqb (Value.type_of_value v) t_k = true /\ t_k = t.
Proof using Type.
  cbn [OpSem.Typing.type_state]. intro H.
  destruct (OpSem.Typing.type_cont_call (mk_glob_ctxt p) k) as [t_k|] eqn:WTCONT; [|discriminate].
  destruct (type_eqb (Value.type_of_value v) t_k) eqn:EQ; [|discriminate].
  injection H as <-. eauto.
Qed.

Lemma type_cont_call_Kcall_inv (gctx: ctxt Empty_set Empty_set Empty_set fundef vardef)
  f e locals (k': @OpSem.cont Sm) t :
  OpSem.Typing.type_cont_call gctx (OpSem.Kcall f e locals k') = Some t ->
  type_function gctx f = true /\
  exists tye, OpSem.Typing.type_env f e = Some tye /\
    OpSem.Typing.type_cont
      (with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty) (with_pure tye (with_stack (List.map (fun _ => tt) locals) gctx))) k' = Some t.
Proof using Type.
  cbn [OpSem.Typing.type_cont_call]. intro H.
  destruct (type_function gctx f) eqn:TF; [|discriminate].
  destruct (OpSem.Typing.type_env f e) as [tye|] eqn:TE; [|discriminate].
  eauto.
Qed.

Lemma denote_env_get {f e ty_env}
  (TENV: OpSem.Typing.type_env f e = Some ty_env)
  {id t} (GET: Maps.PTree.get id ty_env = Some (t, true))
  {v} (EV: Maps.PTree.get id e = Some v) (TYv: Value.type_of_value v = t) :
  denote_tree_lookup GET (denote_binding_eq t) (denote_env TENV)
  = denote_value_eq TYv.
Proof using Type.
  destruct ty_env as [|m]; [discriminate GET|].
  cbn [denote_tree_lookup denote_env].
  rewrite (denote_tree_lookup'_build_tree').
  cbn beta iota.
  destruct (OpSem.Typing.type_env_get_value TENV GET) as [v' EV' TYv'].
  assert (v' = v) as -> by congruence.
  destruct t;
    first [ now destruct (denote_value_eq TYv)
          | (rewrite (UIP_dec (ReflectExt.sumbool_of_reflect type_eqb_spec) TYv' TYv); reflexivity) ].
Qed.

Lemma denote_value_eq_irrel v t (H1 H2: Value.type_of_value v = t) :
  denote_value_eq H1 = denote_value_eq H2.
Proof using Type. assert (H1 = H2) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect type_eqb_spec)). reflexivity. Qed.

Lemma denote_env_set
  (f: function) (e: Maps.PTree.t Vl)
  (SBp: ListExt.SBinds f.(fn_params)) (SBt: ListExt.SBinds f.(fn_temps))
  (DIST: ListExt.DBinds f.(fn_params) f.(fn_temps))
  id t a (IN: List.In (id, t) (f.(fn_params) ++ f.(fn_temps)))
  (WT: Value.type_of_value a = t)
  (TENV : OpSem.Typing.type_env f e = Some (OpSem.Typing.type_env_tree f e))
  (TENV': OpSem.Typing.type_env f (Maps.PTree.set id a e)
          = Some (Maps.PTree.set id (t, true) (OpSem.Typing.type_env_tree f e))) :
  denote_env TENV'
  = denote_tree_set id (denote_binding_eq t) (denote_value_eq WT) (denote_env TENV).
Proof using Type.
  apply (denote_tree_ext).
  intros k [tk bk] a_d GET DEN.
  destruct bk; [| exfalso; destruct tk; cbn in DEN; discriminate DEN].
  apply (denote_tree_lookup_indep_DEN
           GET DEN (denote_binding_eq tk)).
  destruct (Pos.eq_dec k id) as [->|NE].
  - pose proof GET as G0. rewrite Maps.PTree.gss in G0.
    injection G0 as Etk. subst tk.
    rewrite (denote_tree_lookup_set_same
               (denote_binding_eq t) (denote_value_eq WT) (OpSem.Typing.type_env_tree f e) id
               (denote_env TENV) GET).
    assert (EV: Maps.PTree.get id (Maps.PTree.set id a e) = Some a)
      by apply Maps.PTree.gss.
    rewrite (denote_env_get TENV' GET EV WT).
    apply denote_value_eq_irrel.
  - assert (G': Maps.PTree.get k (OpSem.Typing.type_env_tree f e) = Some (tk, true)).
    { pose proof GET as g. rewrite (Maps.PTree.gso _ _ NE) in g. exact g. }
    rewrite (denote_tree_lookup_set_other
               (denote_binding_eq t) (denote_value_eq WT) (OpSem.Typing.type_env_tree f e)
               id k (not_eq_sym NE) (denote_env TENV) (denote_binding_eq tk) GET G').
    destruct (OpSem.Typing.type_env_get_value TENV G') as [vk EVk TYk].
    rewrite (denote_env_get TENV G' EVk TYk).
    assert (EV': Maps.PTree.get k (Maps.PTree.set id a e) = Some vk).
    { rewrite (Maps.PTree.gso _ _ NE). exact EVk. }
    rewrite (denote_env_get TENV' GET EV' TYk).
    reflexivity.
Qed.

Lemma binders_app_functional {params temps: list (AST.ident * type)} {id t t'}
  (SBp: ListExt.SBinds params) (SBt: ListExt.SBinds temps)
  (DIST: ListExt.DBinds params temps)
  (H: List.In (id, t) (params ++ temps)) (H': List.In (id, t') (params ++ temps)) :
  t' = t.
Proof using Type.
  apply List.in_app_or in H as [INp|TY]; apply List.in_app_or in H' as [INp'|TY'].
  - exact (ListExt.SBinds_same_In_eq SBp INp INp').
  - exfalso. exact (ListExt.AbsBind_In_False (ListExt.DBinds_In_AbsBind DIST INp) TY').
  - exfalso. exact (ListExt.AbsBind_In_False (ListExt.DBinds_In_AbsBind DIST INp') TY).
  - exact (ListExt.SBinds_same_In_eq SBt TY TY').
Qed.

Lemma type_env_ok_set (f: function) (e: Maps.PTree.t Vl)
  (SBp: ListExt.SBinds f.(fn_params)) (SBt: ListExt.SBinds f.(fn_temps))
  (DIST: ListExt.DBinds f.(fn_params) f.(fn_temps))
  id t a (IN: List.In (id, t) (f.(fn_params) ++ f.(fn_temps)))
  (TY: Value.type_of_value a = t)
  (OK: OpSem.Typing.type_env_ok (f.(fn_params) ++ f.(fn_temps)) e = true) :
  OpSem.Typing.type_env_ok (f.(fn_params) ++ f.(fn_temps)) (Maps.PTree.set id a e) = true.
Proof using Type.
  unfold OpSem.Typing.type_env_ok in *. setoid_rewrite forallb_forall in OK. setoid_rewrite forallb_forall.
  intros [id' t'] IN'. cbn [fst snd] in *.
  destruct (Pos.eq_dec id' id) as [->|NE].
  - rewrite Maps.PTree.gss.
    rewrite (binders_app_functional SBp SBt DIST IN IN') TY.
    apply (ReflectExt.reflect_refl type_eqb_spec).
  - rewrite (Maps.PTree.gso _ _ NE). exact (OK (id', t') IN').
Qed.

Lemma type_env_set_some (f: function) (e: Maps.PTree.t Vl) ty_env
  (SBp: ListExt.SBinds f.(fn_params)) (SBt: ListExt.SBinds f.(fn_temps))
  (DIST: ListExt.DBinds f.(fn_params) f.(fn_temps))
  id t a (IN: List.In (id, t) (f.(fn_params) ++ f.(fn_temps)))
  (TY: Value.type_of_value a = t)
  (TENV: OpSem.Typing.type_env f e = Some ty_env) :
  OpSem.Typing.type_env f (Maps.PTree.set id a e)
  = Some (Maps.PTree.set id (t, true) ty_env).
Proof using Type.
  pose proof TENV as TENV'. unfold OpSem.Typing.type_env in TENV' |- *.
  destruct (OpSem.Typing.type_env_ok (f.(fn_params) ++ f.(fn_temps)) e) eqn:OK;
    [| discriminate TENV'].
  injection TENV' as <-.
  rewrite (type_env_ok_set f e SBp SBt DIST id t a IN TY OK).
  f_equal. exact (OpSem.Typing.type_env_tree_set f e SBp SBt DIST id t a IN).
Qed.

Lemma type_env_ok_remove (f: function) (e: Maps.PTree.t Vl)
  id
  (OK: OpSem.Typing.type_env_ok (f.(fn_params) ++ f.(fn_temps)) e = true) :
  OpSem.Typing.type_env_ok (f.(fn_params) ++ f.(fn_temps)) (Maps.PTree.remove id e) = true.
Proof using Type.
  unfold OpSem.Typing.type_env_ok in *. setoid_rewrite forallb_forall in OK. setoid_rewrite forallb_forall.
  intros [id' t'] IN'. cbn [fst snd] in *.
  destruct (Pos.eq_dec id' id) as [->|NE].
  - rewrite Maps.PTree.grs. reflexivity.
  - rewrite (Maps.PTree.gro _ NE). exact (OK (id', t') IN').
Qed.

Lemma type_env_remove_some (f: function) (e: Maps.PTree.t Vl) ty_env
  (SBp: ListExt.SBinds f.(fn_params)) (SBt: ListExt.SBinds f.(fn_temps))
  (DIST: ListExt.DBinds f.(fn_params) f.(fn_temps))
  id t (IN: List.In (id, t) (f.(fn_params) ++ f.(fn_temps)))
  (TENV: OpSem.Typing.type_env f e = Some ty_env) :
  OpSem.Typing.type_env f (Maps.PTree.remove id e)
  = Some (Maps.PTree.set id (t, false) ty_env).
Proof using Type.
  pose proof TENV as TENV'. unfold OpSem.Typing.type_env in TENV' |- *.
  destruct (OpSem.Typing.type_env_ok (f.(fn_params) ++ f.(fn_temps)) e) eqn:OK;
    [| discriminate TENV'].
  injection TENV' as <-.
  rewrite (type_env_ok_remove f e id OK).
  f_equal. exact (OpSem.Typing.type_env_tree_remove f e SBp SBt DIST id t IN).
Qed.

Lemma denote_env_pirr {f e ty_env}
  (H1 H2: OpSem.Typing.type_env f e = Some ty_env) :
  denote_env H1 = denote_env H2.
Proof using Type.
  assert (H1 = H2) as -> by
    (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec (option (Maps.PTree.t (type * bool)))))).
  reflexivity.
Qed.

Lemma denote_env_set' (f: function) (e: Maps.PTree.t Vl)
  (SBp: ListExt.SBinds f.(fn_params)) (SBt: ListExt.SBinds f.(fn_temps))
  (DIST: ListExt.DBinds f.(fn_params) f.(fn_temps))
  id t a (IN: List.In (id, t) (f.(fn_params) ++ f.(fn_temps)))
  (WT: Value.type_of_value a = t)
  done_tree (TENV: OpSem.Typing.type_env f e = Some done_tree)
  (TENV': OpSem.Typing.type_env f (Maps.PTree.set id a e)
          = Some (Maps.PTree.set id (t, true) done_tree)) :
  denote_env TENV'
  = denote_tree_set id (denote_binding_eq t) (denote_value_eq WT) (denote_env TENV).
Proof using Type.
  assert (DT: done_tree = OpSem.Typing.type_env_tree f e).
  { unfold OpSem.Typing.type_env in TENV.
    destruct (OpSem.Typing.type_env_ok _ e); [ injection TENV; auto | discriminate TENV ]. }
  subst done_tree.
  exact (denote_env_set f e SBp SBt DIST id t a IN WT TENV TENV').
Qed.

Lemma denote_env_unset
  (f: function) (e: Maps.PTree.t Vl)
  (SBp: ListExt.SBinds f.(fn_params)) (SBt: ListExt.SBinds f.(fn_temps))
  (DIST: ListExt.DBinds f.(fn_params) f.(fn_temps))
  id t (IN: List.In (id, t) (f.(fn_params) ++ f.(fn_temps)))
  (TENV : OpSem.Typing.type_env f e = Some (OpSem.Typing.type_env_tree f e))
  (TENV': OpSem.Typing.type_env f (Maps.PTree.remove id e)
          = Some (Maps.PTree.set id (t, false) (OpSem.Typing.type_env_tree f e))) :
  denote_env TENV'
  = denote_tree_unset id (denote_binding_false_eq t) (denote_env TENV).
Proof using Type.
  apply (denote_tree_ext).
  intros k [tk bk] a_d GET DEN.
  destruct bk; [| exfalso; destruct tk; cbn in DEN; discriminate DEN].
  apply (denote_tree_lookup_indep_DEN
           GET DEN (denote_binding_eq tk)).
  destruct (Pos.eq_dec k id) as [->|NE].
  - exfalso. pose proof GET as G0. rewrite Maps.PTree.gss in G0.
    injection G0 as _ Ebk. discriminate Ebk.
  - assert (G': Maps.PTree.get k (OpSem.Typing.type_env_tree f e) = Some (tk, true)).
    { pose proof GET as g. rewrite (Maps.PTree.gso _ _ NE) in g. exact g. }
    rewrite (denote_tree_lookup_unset_other
               (denote_binding_false_eq t) (OpSem.Typing.type_env_tree f e)
               id k (not_eq_sym NE) (denote_env TENV) (denote_binding_eq tk) GET G').
    destruct (OpSem.Typing.type_env_get_value TENV G') as [vk EVk TYk].
    rewrite (denote_env_get TENV G' EVk TYk).
    assert (EV': Maps.PTree.get k (Maps.PTree.remove id e) = Some vk).
    { rewrite (Maps.PTree.gro _ NE). exact EVk. }
    rewrite (denote_env_get TENV' GET EV' TYk).
    reflexivity.
Qed.

Lemma denote_env_unset' (f: function) (e: Maps.PTree.t Vl)
  (SBp: ListExt.SBinds f.(fn_params)) (SBt: ListExt.SBinds f.(fn_temps))
  (DIST: ListExt.DBinds f.(fn_params) f.(fn_temps))
  id t (IN: List.In (id, t) (f.(fn_params) ++ f.(fn_temps)))
  done_tree (TENV: OpSem.Typing.type_env f e = Some done_tree)
  (TENV': OpSem.Typing.type_env f (Maps.PTree.remove id e)
          = Some (Maps.PTree.set id (t, false) done_tree)) :
  denote_env TENV'
  = denote_tree_unset id (denote_binding_false_eq t) (denote_env TENV).
Proof using Type.
  assert (DT: done_tree = OpSem.Typing.type_env_tree f e).
  { unfold OpSem.Typing.type_env in TENV.
    destruct (OpSem.Typing.type_env_ok _ e); [ injection TENV; auto | discriminate TENV ]. }
  subst done_tree.
  exact (denote_env_unset f e SBp SBt DIST id t IN TENV TENV').
Qed.

Lemma denote_value_eq_eq_rect {a t} (EQ WT: Value.type_of_value a = t) :
  eq_rect (Value.type_of_value a) denote_type (denote_value a) t EQ
  = denote_value_eq WT.
Proof using Type.
  assert (EQ = WT) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  unfold denote_value_eq, convert_eq. destruct WT. reflexivity.
Qed.

Lemma denote_expr_var ctx var_id t
  (WT: type_expr ctx (e_var var_id) = Some t)
  (env: denote_tree denote_binding ctx)
  (GET: Maps.PTree.get var_id ctx = Some (t, true)) :
  denote_expr WT env = denote_tree_lookup GET (denote_binding_eq t) env.
Proof using Type.
  cbn [denote_expr].
  erewrite (conv_option_app GET).
  cbn match beta iota.
  destruct t; rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)); reflexivity.
Qed.

Lemma denote_expr_pirr ctx e t (W1 W2: type_expr ctx e = Some t)
  (env: denote_tree denote_binding ctx) :
  denote_expr W1 env = denote_expr W2 env.
Proof using Type.
  assert (W1 = W2) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec (option type)))). reflexivity.
Qed.

Lemma denote_expr_nat ctx n (WT: type_expr ctx (e_nat n) = Some t_nat) env :
  denote_expr WT env = n.
Proof using Type.
  assert (BIT: Z.leb (Z.of_nat n) (Intops.Unsigned.max_unsigned nat_uint32_t) = true).
  { cbn in WT. destruct (Z.leb (Z.of_nat n) _); [reflexivity | discriminate WT]. }
  cbn [denote_expr].
  now erewrite (conv_bool_app' BIT).
Qed.

Lemma denote_expr_ofst ctx o (WT: type_expr ctx (e_ofst o) = Some t_ofst) env :
  denote_expr WT env = o.
Proof using Type.
  assert (BIT: Z.leb (Z.of_N o) (Intops.Unsigned.max_unsigned n_ofst_t) = true).
  { cbn in WT. destruct (Z.leb (Z.of_N o) _); [reflexivity | discriminate WT]. }
  cbn [denote_expr].
  now erewrite (conv_bool_app' BIT).
Qed.

Lemma denote_expr_neg ctx e1 (WT: type_expr ctx (e_neg e1) = Some t_bool) env
  (TYPe: type_expr ctx e1 = Some t_bool) :
  denote_expr WT env = negb (denote_expr TYPe env).
Proof using Type.
  cbn [denote_expr].
  erewrite (conv_option_app TYPe).
  now rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
Qed.

Lemma denote_expr_add ctx e1 e2 (WT: type_expr ctx (e_add e1 e2) = Some t_nat) env
  (T1: type_expr ctx e1 = Some t_nat) (T2: type_expr ctx e2 = Some t_nat) :
  denote_expr WT env
  = Intops.Unsigned.add (denote_expr T1 env) (denote_expr T2 env).
Proof using Type.
  cbn [denote_expr].
  erewrite (conv_option_app T1).
  erewrite (conv_option_app T2).
  now rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
Qed.

Lemma denote_expr_eqb ctx e1 e2 (WT: type_expr ctx (e_eqb e1 e2) = Some t_bool) env
  (T1: type_expr ctx e1 = Some t_nat) (T2: type_expr ctx e2 = Some t_nat) :
  denote_expr WT env
  = Intops.Unsigned.eqb (denote_expr T1 env) (denote_expr T2 env).
Proof using Type.
  cbn [denote_expr].
  erewrite (conv_option_app T1).
  erewrite (conv_option_app T2).
  now rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
Qed.

Lemma denote_expr_mul ctx e1 e2 (WT: type_expr ctx (e_mul e1 e2) = Some t_nat) env
  (T1: type_expr ctx e1 = Some t_nat) (T2: type_expr ctx e2 = Some t_nat) :
  denote_expr WT env
  = Intops.Unsigned.mul (denote_expr T1 env) (denote_expr T2 env).
Proof using Type.
  cbn [denote_expr].
  erewrite (conv_option_app T1).
  erewrite (conv_option_app T2).
  now rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
Qed.

Lemma type_expr_var_inv ctx var_id t :
  type_expr ctx (e_var var_id) = Some t ->
  Maps.PTree.get var_id ctx = Some (t, true).
Proof using Type.
  intro H. cbn [type_expr] in H.
  destruct (Maps.PTree.get var_id ctx) as [[t' [|]]|] eqn:EGET; try discriminate H.
  destruct t'; injection H as <-; reflexivity.
  destruct t'; discriminate.
Qed.

Lemma type_expr_neg_inv ctx e1 t :
  type_expr ctx (e_neg e1) = Some t ->
  type_expr ctx e1 = Some t_bool /\ t = t_bool.
Proof using Type.
  intro H. cbn [type_expr] in H.
  destruct (type_expr ctx e1) as [ [ | | | | ] | ] eqn:E1; try discriminate H;
    injection H as <-; auto.
Qed.

Lemma type_expr_add_inv ctx e1 e2 t :
  type_expr ctx (e_add e1 e2) = Some t ->
  type_expr ctx e1 = Some t_nat /\ type_expr ctx e2 = Some t_nat /\ t = t_nat.
Proof using Type.
  intro H. cbn [type_expr] in H.
  destruct (type_expr ctx e1) as [ [ | | | | ] | ] eqn:E1; try discriminate H;
    destruct (type_expr ctx e2) as [ [ | | | | ] | ] eqn:E2; try discriminate H;
    injection H as <-; auto.
Qed.

Lemma type_expr_eqb_inv ctx e1 e2 t :
  type_expr ctx (e_eqb e1 e2) = Some t ->
  type_expr ctx e1 = Some t_nat /\ type_expr ctx e2 = Some t_nat /\ t = t_bool.
Proof using Type.
  intro H. cbn [type_expr] in H.
  destruct (type_expr ctx e1) as [ [ | | | | ] | ] eqn:E1; try discriminate H;
    destruct (type_expr ctx e2) as [ [ | | | | ] | ] eqn:E2; try discriminate H;
    injection H as <-; auto.
Qed.

Lemma type_expr_mul_inv ctx e1 e2 t :
  type_expr ctx (e_mul e1 e2) = Some t ->
  type_expr ctx e1 = Some t_nat /\ type_expr ctx e2 = Some t_nat /\ t = t_nat.
Proof using Type.
  intro H. cbn [type_expr] in H.
  destruct (type_expr ctx e1) as [ [ | | | | ] | ] eqn:E1; try discriminate H;
    destruct (type_expr ctx e2) as [ [ | | | | ] | ] eqn:E2; try discriminate H;
    injection H as <-; auto.
Qed.

Lemma denote_expr_eval f env_v ty_env
  (TENV: OpSem.Typing.type_env f env_v = Some ty_env) :
  forall e t v (WT: type_expr ty_env e = Some t) (EVAL: eval e env_v = Some v),
  exists (TY: Value.type_of_value v = t),
    denote_expr WT (denote_env TENV) = denote_value_eq TY.
Proof using Type.
  induction e as [ var_id | | b | n | ofst | | e1 IH1 | e1 IH1 e2 IH2 | e1 IH1 e2 IH2
                 | e1 IH1 e2 IH2 ];
    intros t v WT EVAL.
  - pose proof (type_expr_var_inv _ _ _ WT) as GET.
    cbn in EVAL.
    destruct (OpSem.Typing.type_env_get_value TENV GET) as [v0 EV0 TY0].
    assert (v0 = v) as -> by congruence.
    exists TY0.
    rewrite (denote_expr_var _ _ _ WT _ GET).
    apply (denote_env_get TENV GET EVAL TY0).
  - cbn in WT, EVAL. injection WT as <-. injection EVAL as <-.
    now exists eq_refl.
  - cbn in WT, EVAL. injection WT as <-. injection EVAL as <-.
    now exists eq_refl.
  - cbn in EVAL; injection EVAL as <-.
    assert (t = t_nat) as ->
      by (cbn in WT; destruct (Z.leb (Z.of_nat n) _); congruence).
    exists eq_refl. rewrite (denote_expr_nat _ _ WT). reflexivity.
  - cbn in EVAL; injection EVAL as <-.
    assert (t = t_ofst) as ->
      by (cbn in WT; destruct (Z.leb (Z.of_N ofst) _); congruence).
    exists eq_refl. rewrite (denote_expr_ofst _ _ WT). reflexivity.
  - cbn in WT, EVAL. injection WT as <-. injection EVAL as <-.
    now exists eq_refl.
  - cbn in EVAL.
    destruct (eval e1 env_v) as [ [ | b | | | ] | ] eqn:E1; try discriminate EVAL.
    injection EVAL as <-.
    destruct (type_expr_neg_inv _ _ _ WT) as [T1 ->].
    exists eq_refl.
    rewrite (denote_expr_neg _ _ WT _ T1).
    destruct (IH1 _ _ T1 eq_refl) as [TY1 EQ1].
    rewrite EQ1 (denote_value_eq_irrel _ _ TY1 eq_refl).
    reflexivity.
  - cbn in EVAL.
    destruct (eval e1 env_v) as [ [ | | nl | | ] | ] eqn:E1; try discriminate EVAL.
    destruct (eval e2 env_v) as [ [ | | nr | | ] | ] eqn:E2; try discriminate EVAL.
    injection EVAL as <-.
    destruct (type_expr_add_inv _ _ _ _ WT) as (T1 & T2 & ->).
    exists eq_refl.
    rewrite (denote_expr_add _ _ _ WT _ T1 T2).
    destruct (IH1 _ _ T1 eq_refl) as [TY1 EQ1].
    destruct (IH2 _ _ T2 eq_refl) as [TY2 EQ2].
    rewrite EQ1 EQ2
      (denote_value_eq_irrel _ _ TY1 eq_refl) (denote_value_eq_irrel _ _ TY2 eq_refl).
    reflexivity.
  - cbn in EVAL.
    destruct (eval e1 env_v) as [ [ | | nl | | ] | ] eqn:E1; try discriminate EVAL.
    destruct (eval e2 env_v) as [ [ | | nr | | ] | ] eqn:E2; try discriminate EVAL.
    injection EVAL as <-.
    destruct (type_expr_mul_inv _ _ _ _ WT) as (T1 & T2 & ->).
    exists eq_refl.
    rewrite (denote_expr_mul _ _ _ WT _ T1 T2).
    destruct (IH1 _ _ T1 eq_refl) as [TY1 EQ1].
    destruct (IH2 _ _ T2 eq_refl) as [TY2 EQ2].
    rewrite EQ1 EQ2
      (denote_value_eq_irrel _ _ TY1 eq_refl) (denote_value_eq_irrel _ _ TY2 eq_refl).
    reflexivity.
  - cbn in EVAL.
    destruct (eval e1 env_v) as [ [ | | nl | | ] | ] eqn:E1; try discriminate EVAL.
    destruct (eval e2 env_v) as [ [ | | nr | | ] | ] eqn:E2; try discriminate EVAL.
    injection EVAL as <-.
    destruct (type_expr_eqb_inv _ _ _ _ WT) as (T1 & T2 & ->).
    exists eq_refl.
    rewrite (denote_expr_eqb _ _ _ WT _ T1 T2).
    destruct (IH1 _ _ T1 eq_refl) as [TY1 EQ1].
    destruct (IH2 _ _ T2 eq_refl) as [TY2 EQ2].
    rewrite EQ1 EQ2
      (denote_value_eq_irrel _ _ TY1 eq_refl) (denote_value_eq_irrel _ _ TY2 eq_refl).
    reflexivity.
Qed.

Lemma denote_expr_eval_bool {f env_v ty_env} (TENV: OpSem.Typing.type_env f env_v = Some ty_env)
  {e b} (WT: type_expr ty_env e = Some t_bool) (EVAL: eval e env_v = Some (v_bool b)) :
  denote_expr WT (denote_env TENV) = b.
Proof using Type.
  destruct (denote_expr_eval _ _ _ TENV _ _ _ WT EVAL) as [TY EQ].
  rewrite EQ (denote_value_eq_irrel _ _ TY eq_refl). reflexivity.
Qed.

Lemma type_cmd_if_inv ctx e_i c_t c_e t :
  type_cmd ctx (c_if e_i c_t c_e) = Some t ->
  type_expr ctx.(ctxt_pure) e_i = Some t_bool /\
  type_cmd ctx c_t = Some t /\
  exists t_e, type_cmd ctx c_e = Some t_e /\ type_eqb t t_e = true.
Proof using Type.
  cbn [type_cmd]. intro H.
  destruct (type_expr ctx.(ctxt_pure) e_i) as [ [ | | | | ] | ] eqn:TYPe; try discriminate H.
  destruct (type_cmd ctx c_t) as [t_t|] eqn:Wt; try discriminate H.
  destruct (type_cmd ctx c_e) as [t_e|] eqn:We; try discriminate H.
  destruct (eqb_spec t_t t_e); [ subst t_e | discriminate H ].
  injection H as <-.
  repeat split; auto.
  exists t_t.
  split; [ reflexivity | apply (ReflectExt.reflect_refl type_eqb_spec) ].
Qed.

Lemma denote_cmd_if {ctx} {e_i c_t c_e} {t_res}
  (WT: type_cmd ctx (c_if e_i c_t c_e) = Some t_res)
  (env: denote_ctxt ctx)
  (WTcond: type_expr ctx.(ctxt_pure) e_i = Some t_bool)
  (WTthen: type_cmd ctx c_t = Some t_res)
  (WTelse: type_cmd ctx c_e = Some t_res) :
  denote_cmd WT env =
  (if denote_expr WTcond (fst (fst env))
   then denote_cmd WTthen env
   else denote_cmd WTelse env).
Proof using Type.
  cbn [denote_cmd].
  erewrite (conv_option_app WTcond).
  erewrite (conv_option_app WTthen).
  erewrite (conv_option_app WTelse).
  erewrite (conv_bool_app (ReflectExt.reflect_refl type_eqb_spec t_res)).
  rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  now destruct t_res.
Qed.

Lemma step_bind_correct p f id_b t_b c_b c_c (k: @OpSem.cont Sm)
  env locals (mem: Sm) t t' WTp
  (Ts: OpSem.Typing.type_state p (OpSem.State f (c_bind id_b t_b c_b c_c) k env locals mem) = Some t)
  (Ts': OpSem.Typing.type_state p (OpSem.State f c_b (Kbind id_b c_c k) env locals mem) = Some t') :
  denote_state WTp Ts = denote_state WTp Ts'.
Proof using Type.
  destruct (type_state_State_inv _ _ _ _ _ _ _ _ Ts)
    as (ty_env & t_cL & t_kL & TENV & WTCMDl & WTCONTl & EQl & EtcL & WTFNl).
  destruct (type_state_State_inv _ _ _ _ _ _ _ _ Ts')
    as (ty_env2 & t_cR & t_kR & TENV2 & WTCMDr & WTCONTr & EQr & EtcR & WTFNr).
  assert (ty_env2 = ty_env) by congruence; subst ty_env2.
  erewrite (denote_state_State _ _ _ _ _ _ _ _ _ Ts _ TENV _ WTCMDl _ WTCONTl EQl WTFNl).
  erewrite (denote_state_State _ _ _ _ _ _ _ _ _ Ts' _ TENV _ WTCMDr _ WTCONTr EQr WTFNr).
  destruct (type_cmd_bind_inv _ _ _ _ _ _ WTCMDl) as (GETL & WTc1 & WTc2).
  destruct (type_cont_kbind_inv _ _ _ _ _ WTCONTr) as (GETR & t_cc & WTcc & WTkk).
  assert (t_kR = t_b) by congruence; subst t_kR.
  subst t_cL t_cR.
  assert (t' = t_b) by congruence; subst t'.
  assert (t = t_cc) by congruence; subst t.
  assert (t_kL = t_cc) by congruence; subst t_kL.
  rewrite (denote_cmd_bind WTCMDl _ GETL WTc1 WTc2).
  rewrite bind_assoc.
  cbn [fst snd].
  setoid_rewrite (convert_eq_refl_id _ (reflect_eq_of_true type_eqb_spec EQr)).
  setoid_rewrite (denote_cont_kbind WTCONTr (denote_env TENV) (denote_locals locals)
                    (denote_glob_ctxt_of_program p WTp) _ GETR _ WTcc WTkk).
  setoid_rewrite (convert_eq_refl_id _ (reflect_eq_of_true type_eqb_spec EQl)).
  rewrite (denote_cmd_pirr WTCMDr WTc1).
  setoid_rewrite (denote_cmd_pirr WTcc WTc2).
  setoid_rewrite (denote_cont_pirr WTkk WTCONTl).
  reflexivity.
Qed.

Lemma step_while_correct p f c_cond c_body (k: @OpSem.cont Sm)
  env locals (mem: Sm) t t' WTp
  (Ts: OpSem.Typing.type_state p (OpSem.State f (c_while c_cond c_body) k env locals mem) = Some t)
  (Ts': OpSem.Typing.type_state p (OpSem.State f c_cond (Kloop1 c_cond c_body k) env locals mem) = Some t') :
  denote_state WTp Ts = denote_state WTp Ts'.
Proof using Type.
  destruct (type_state_State_inv _ _ _ _ _ _ _ _ Ts)
    as (ty_env & t_cL & t_kL & TENV & WTCMDl & WTCONTl & EQl & EtcL & WTFNl).
  destruct (type_state_State_inv _ _ _ _ _ _ _ _ Ts')
    as (ty_env2 & t_cR & t_kR & TENV2 & WTCMDr & WTCONTr & EQr & EtcR & WTFNr).
  assert (ty_env2 = ty_env) by congruence; subst ty_env2.
  erewrite (denote_state_State _ _ _ _ _ _ _ _ _ Ts _ TENV _ WTCMDl _ WTCONTl EQl WTFNl).
  erewrite (denote_state_State _ _ _ _ _ _ _ _ _ Ts' _ TENV _ WTCMDr _ WTCONTr EQr WTFNr).
  destruct (type_cmd_while_inv _ _ _ _ WTCMDl) as (Wcond & Wbody & EL).
  destruct (type_cont_Kloop1_inv _ _ _ _ _ WTCONTr) as (WcondR & WbodyR & WkR & ER).
  assert (t_cL = t_unit) as -> by congruence.
  assert (t_kL = t_unit) as -> by congruence.
  assert (t_cR = t_bool) as -> by congruence.
  assert (t_kR = t_bool) as -> by congruence.
  rewrite (denote_cmd_while WTCMDl _ Wcond Wbody).
  setoid_rewrite (convert_eq_refl_id _ (reflect_eq_of_true type_eqb_spec EQl)).
  setoid_rewrite (convert_eq_refl_id _ (reflect_eq_of_true type_eqb_spec EQr)).
  setoid_rewrite (denote_cont_Kloop1 WTCONTr _ _ _ _ WcondR WbodyR WkR).
  rewrite (denote_cmd_pirr WTCMDr Wcond).
  setoid_rewrite while_fixpoint at 1.
  rewrite bind_assoc.
  f_equiv. intros b.
  destruct b; cbn beta iota.
  - rewrite (denote_cmd_pirr WbodyR Wbody).
    rewrite (denote_cmd_pirr WcondR Wcond).
    rewrite (denote_cont_pirr WkR WTCONTl).
    rewrite bind_assoc.
    f_equiv. intros _.
    f_equiv. intros v0. destruct v0. reflexivity.
  - rewrite (denote_cont_pirr WkR WTCONTl).
    rewrite ret_left. reflexivity.
Qed.

Lemma step_ifthenelse_correct p f e_i c_t c_e (k: @OpSem.cont Sm)
  env locals (mem: Sm) b t t' WTp
  (EVAL: eval e_i env = Some (v_bool b))
  (Ts: OpSem.Typing.type_state p (OpSem.State f (c_if e_i c_t c_e) k env locals mem) = Some t)
  (Ts': OpSem.Typing.type_state p (OpSem.State f (if b then c_t else c_e) k env locals mem) = Some t') :
  denote_state WTp Ts = denote_state WTp Ts'.
Proof using Type.
  destruct (type_state_State_inv _ _ _ _ _ _ _ _ Ts)
    as (ty_env & t_cL & t_kL & TENV & WTCMDl & WTCONTl & EQl & EtcL & WTFNl).
  destruct (type_state_State_inv _ _ _ _ _ _ _ _ Ts')
    as (ty_env2 & t_cR & t_kR & TENV2 & WTCMDr & WTCONTr & EQr & EtcR & WTFNr).
  clear EtcL EtcR.
  assert (ty_env2 = ty_env) by congruence; subst ty_env2.
  assert (t_kR = t_kL) by congruence; subst t_kR.
  erewrite (denote_state_State _ _ _ _ _ _ _ _ _ Ts _ TENV _ WTCMDl _ WTCONTl EQl WTFNl).
  erewrite (denote_state_State _ _ _ _ _ _ _ _ _ Ts' _ TENV _ WTCMDr _ WTCONTr EQr WTFNr).
  destruct (type_cmd_if_inv _ _ _ _ _ WTCMDl) as (WTcond & WTthen & t_e & WTelse & EQte).
  assert (t_cL = t_e) by (destruct (type_eqb_spec t_cL t_e); congruence); subst t_e.
  rewrite (denote_cmd_if WTCMDl _ WTcond WTthen WTelse).
  cbn [fst snd].
  replace (denote_expr WTcond (denote_env TENV)) with b
    by (symmetry; exact (denote_expr_eval_bool TENV WTcond EVAL)).
  destruct b; cbn beta iota.
  - assert (t_cR = t_cL) by congruence; subst t_cR.
    rewrite (denote_cmd_pirr WTthen WTCMDr).
    assert (EQl = EQr) as -> by (apply UIP_dec, Bool.bool_dec).
    setoid_rewrite (denote_cont_pirr WTCONTl WTCONTr).
    reflexivity.
  - assert (t_cR = t_cL) by congruence; subst t_cR.
    rewrite (denote_cmd_pirr WTelse WTCMDr).
    assert (EQl = EQr) as -> by (apply UIP_dec, Bool.bool_dec).
    setoid_rewrite (denote_cont_pirr WTCONTl WTCONTr).
    reflexivity.
Qed.

Lemma denote_cont_Kstop {ctx}
  (WT: OpSem.Typing.type_cont ctx (@OpSem.Kstop Sm) = Some t_nat)
  (env: denote_pure_ctxt Sm ctx) (stack: denote_stack_ctxt Sm ctx)
  (glob: denote_glob_ctxt Sm ctx) (v: denote_type t_nat) :
  denote_cont WT env stack glob v = ret v.
Proof using Type.
  cbn [OpSem.Typing.type_cont] in WT.
  cbn [denote_cont].
  revert WT stack.
  destruct (ctxt_stack ctx) as [|s0 sl0] eqn:E; intros WT stack;
    [ rewrite (UIP_dec (ReflectExt.sumbool_of_reflect eqb_spec) WT eq_refl); reflexivity
    | discriminate WT ].
Qed.

Lemma denote_cont_call_Kstop {ctx}
  (WT: OpSem.Typing.type_cont_call ctx (@OpSem.Kstop Sm) = Some t_nat)
  (glob: denote_glob_ctxt Sm ctx) (v: denote_type t_nat) :
  denote_cont_call WT glob v = ret v.
Proof using Type.
  rewrite (UIP_dec (ReflectExt.sumbool_of_reflect eqb_spec) WT eq_refl). reflexivity.
Qed.

Lemma denote_cont_Kcall {ctx} {fn e locals} {k': @OpSem.cont Sm} {t}
  (WT: OpSem.Typing.type_cont ctx (OpSem.Kcall fn e locals k') = Some t)
  (env: denote_pure_ctxt Sm ctx) (stack: denote_stack_ctxt Sm ctx)
  (glob: denote_glob_ctxt Sm ctx) (v: denote_type t)
  (TF: type_function (to_glob_ctxt ctx) fn = true)
  {tye} (TE: OpSem.Typing.type_env fn e = Some tye)
  (WT': OpSem.Typing.type_cont
          (with_internal (mk_typing_tree false fn.(fn_internals) Maps.PTree.Empty) (with_pure tye (with_stack (List.map (fun _ => tt) locals) ctx))) k' = Some t) :
  denote_cont WT env stack glob v
  = denote_cont WT' (denote_env TE) (denote_locals locals) glob v.
Proof using Type.
  cbn [OpSem.Typing.type_cont] in WT.
  cbn [denote_cont].
  revert WT stack.
  destruct (ctxt_stack ctx) as [|s0 sl0] eqn:E; intros WT stack;
    [ | discriminate WT ].
  erewrite (conv_bool_app TF).
  erewrite (conv_option_app TE).
  apply denote_cont_pirr.
Qed.

Lemma denote_cont_call_Kcall {gctx} {fn e locals} {k': @OpSem.cont Sm} {t}
  (WT: OpSem.Typing.type_cont_call gctx (OpSem.Kcall fn e locals k') = Some t)
  (glob: denote_glob_ctxt Sm gctx) (v: denote_type t)
  (TF: type_function gctx fn = true)
  {tye} (TE: OpSem.Typing.type_env fn e = Some tye)
  (WT': OpSem.Typing.type_cont
          (with_internal (mk_typing_tree false fn.(fn_internals) Maps.PTree.Empty) (with_pure tye (with_stack (List.map (fun _ => tt) locals) gctx))) k' = Some t) :
  denote_cont_call WT glob v
  = denote_cont WT' (denote_env TE) (denote_locals locals) glob v.
Proof using Type.
  cbn [denote_cont_call].
  erewrite (conv_bool_app TF).
  erewrite (conv_option_app TE).
  apply denote_cont_pirr.
Qed.

Lemma denote_cont_call_eq_denote_cont
  (gctx: ctxt Empty_set Empty_set Empty_set fundef vardef) (f: function)
  (ty_env0: Maps.PTree.t (type * bool))
  (sl: list unit)
  (k: @OpSem.cont Sm) (CALLK: OpSem.is_call_cont k) (t: type)
  (WTCC: OpSem.Typing.type_cont_call gctx k = Some t)
  (WTK: OpSem.Typing.type_cont (with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty) (with_pure ty_env0 (with_stack sl gctx))) k = Some t)
  (env: denote_pure_ctxt Sm (with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty) (with_pure ty_env0 (with_stack sl gctx))))
  (stack: denote_stack_ctxt Sm (with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty) (with_pure ty_env0 (with_stack sl gctx))))
  (glob: denote_glob_ctxt Sm gctx)
  (v: denote_type t) :
  denote_cont_call WTCC glob v = denote_cont WTK env stack glob v.
Proof using Type.
  destruct CALLK as [ | fn e locals k' ].
  - assert (t = t_nat) as -> by (cbn in WTCC; congruence).
    rewrite (denote_cont_call_Kstop WTCC glob v).
    rewrite (denote_cont_Kstop WTK env stack glob v).
    reflexivity.
  - pose proof WTCC as WTCC'. cbn [OpSem.Typing.type_cont_call] in WTCC'.
    destruct (type_function gctx fn) eqn:TFcc; [| discriminate WTCC'].
    destruct (OpSem.Typing.type_env fn e) as [tye|] eqn:TE; [| discriminate WTCC'].
    pose proof WTK as WTK'. cbn [OpSem.Typing.type_cont] in WTK'.
    destruct sl as [|s0 sl0] eqn:Esl.
    2: { discriminate WTK'. }
    destruct (type_function (to_glob_ctxt ((with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty) (with_pure ty_env0 (with_stack [] gctx))))) fn)
      eqn:TFc; [| discriminate WTK'].
    rewrite TE in WTK'.
    rewrite (denote_cont_call_Kcall WTCC glob v TFcc TE WTCC').
    rewrite (denote_cont_Kcall WTK env stack glob v TFc TE WTK').
    apply denote_cont_pirr.
Qed.

Lemma denote_cont_resolve_call
  (gctx: ctxt Empty_set Empty_set Empty_set fundef vardef) (f: function)
  (k k0: @OpSem.cont Sm) (CALLK: OpSem.resolve_call_cont k k0) :
  forall (ty_env: Maps.PTree.t (type*bool)) (sl: list unit) t
    (WTK: OpSem.Typing.type_cont (with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty) (with_pure ty_env (with_stack sl gctx))) k = Some t)
    (WTCC: OpSem.Typing.type_cont_call gctx k0 = Some t)
    (env: denote_pure_ctxt Sm (with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty) (with_pure ty_env (with_stack sl gctx))))
    (stack: denote_stack_ctxt Sm (with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty) (with_pure ty_env (with_stack sl gctx))))
    (glob: denote_glob_ctxt Sm gctx)
    (v: denote_type t) (s s'': Sm)
    (POPS: OpSem.pop_stack_n (length sl) s = Some s''),
    denote_cont WTK env stack glob v s = denote_cont_call WTCC glob v s''.
Proof using Type.
  induction CALLK as [k1 CALLK1 | sx k1 k1' RES IH];
    intros ty_env sl t WTK WTCC env stack glob v s s'' POPS.
  - assert (SL: sl = []).
    { destruct CALLK1; cbn [OpSem.Typing.type_cont] in WTK;
        (destruct sl as [|s0 sl0]; [reflexivity | discriminate WTK]). }
    subst sl. rewrite pop_stack_n_O in POPS. injection POPS as <-.
    rewrite (denote_cont_call_eq_denote_cont gctx f ty_env [] k1 CALLK1 t WTCC WTK env stack glob v).
    reflexivity.
  - destruct sx as [id | ].
    + destruct (type_cont_Kscope_unbind_inv _ _ _ _ WTK) as (t_b & GETu & WTk).
      rewrite (denote_cont_Kscope_unbind WTK env stack glob v t_b GETu WTk).
      exact (IH (Maps.PTree.set id (t_b, false) ty_env) sl t WTk WTCC
               (denote_tree_unset id (denote_binding_false_eq t_b) env) stack glob v s s'' POPS).
    + destruct (type_cont_Kscope_pop_inv _ _ _ WTK) as (s0 & sl0 & STKne & WTk).
      assert (Esl: sl = s0 :: sl0) by exact STKne.
      rewrite (denote_cont_Kscope_pop WTK env stack glob v s0 sl0 STKne WTk).
      unfold Monad.bind, Monad.get, Monad.put; cbn beta iota.
      rewrite Esl in POPS. cbn [Datatypes.length] in POPS.
      unfold OpSem.pop_stack_n in POPS. rewrite Nat2N.inj_succ in POPS.
      destruct (pop (store s)) as [st|] eqn:POPeq;
        [ rewrite (state_pop_n_succ_r POPeq) in POPS| rewrite (state_pop_n_succ_r_None POPeq) in POPS; discriminate POPS ].
      rewrite (mk_state_opt_of_dominates st (scnt s) (heap s) (alc s)
                 (dominates_pop (store s) st (scnt s) POPeq (state_store_dominates s))
                 (state_heap_dominates s)).
      cbn beta iota.
      set (s1 := mk_state st (scnt s) (heap s) (alc s) _ _).
      assert (POPS': OpSem.pop_stack_n (length (removelast sl)) s1 = Some s'').
      { unfold OpSem.pop_stack_n.
        rewrite ListExt.length_removelast Esl.
        cbn [Datatypes.length Nat.sub]. rewrite Nat.sub_0_r. exact POPS. }
      exact (IH ty_env (removelast sl) t WTk WTCC env
               (denote_stack_removelast (denote_local)
                  (ctxt_stack (with_internal (mk_typing_tree false f.(fn_internals) Maps.PTree.Empty) (with_pure ty_env (with_stack sl gctx)))) stack)
               glob v s1 s'' POPS').
Qed.

Lemma cast_bind_inj {A: EqDec.type} {a a_d}
  {denote: A -> option Type} (DEN: denote a = Some a_d)
  (x y: match denote a with Some d => d | None => unit end) :
  cast_bind (eq_refl: Some a = Some a) DEN x = cast_bind eq_refl DEN y -> x = y.
Proof using Type.
  rewrite !(cast_bind_eq_rect eq_refl DEN).
  intro H. match type of H with eq_rect _ ?P _ _ ?e = _ => exact (eq_rect_inj P e H) end.
Qed.

Lemma curry_tree_eq_type_env_tree
  (ctx: ctxt Empty_set Empty_set Empty_set fundef vardef) (fn: function) (args: list Vl)
  (SBp: ListExt.SBinds fn.(fn_params))
  (SBt: ListExt.SBinds fn.(fn_temps))
  (DIST: ListExt.DBinds fn.(fn_params) fn.(fn_temps))
  (WTARGS: Forall2 (wt_value (Pt := Pt)) args (List.map snd fn.(fn_params))) :
  ctxt_pure (mk_function_ctxt fn.(fn_params) fn.(fn_temps) fn.(fn_internals) ctx)
  = OpSem.Typing.type_env_tree fn (OpSem.set_params fn.(fn_params) args).
Proof using Type.
  apply Maps.PTree.extensionality. intro id.
  destruct (List.in_dec Pos.eq_dec id (List.map fst fn.(fn_params))) as [INp|NINp].
  - apply List.in_map_iff in INp as [[id' t] [FST INp]]; cbn in FST; subst id'.
    rewrite (Prog.Facts.mk_function_ctxt_pure_get_param _ _ _ ctx SBp SBt DIST _ _ INp).
    rewrite (OpSem.Typing.type_env_tree_get_param fn _ SBp DIST _ _ INp).
    destruct (OpSem.Typing.set_params_in_some_wt SBp WTARGS INp) as [v [TYv _]].
    unfold OpSem.Typing.type_env_bit. rewrite TYv. reflexivity.
  - destruct (List.in_dec Pos.eq_dec id (List.map fst fn.(fn_temps))) as [INt|NINt].
    + apply List.in_map_iff in INt as [[id' t] [FST INt]]; cbn in FST; subst id'.
      rewrite (Prog.Facts.mk_function_ctxt_pure_get_temp _ _ _ ctx SBp SBt DIST _ _ INt).
      rewrite (OpSem.Typing.type_env_tree_get_temp fn _ SBt _ _ INt).
      unfold OpSem.Typing.type_env_bit.
      now rewrite (OpSem.Typing.set_params_get_not_in NINp).
    + assert (NI: ~ List.In id (List.map fst (fn.(fn_params) ++ fn.(fn_temps)))).
      { rewrite List.map_app List.in_app_iff. tauto. }
      rewrite (OpSem.Typing.type_env_tree_get_none fn _ _ NI).
      destruct (Maps.PTree.get id (ctxt_pure (mk_function_ctxt fn.(fn_params) fn.(fn_temps) fn.(fn_internals) ctx)))
        as [[t b]|] eqn:E; [| reflexivity].
      exfalso.
      destruct (Prog.Facts.mk_function_ctxt_pure_get_inv _ _ _ ctx SBp SBt _ _ _ E)
        as [[_ IN]|[_ IN]].
      * apply NINp, List.in_map_iff; exists (id, t); auto.
      * apply NINt, List.in_map_iff; exists (id, t); auto.
Qed.

Lemma denote_app_values_function_curried
  (ctx: ctxt Empty_set Empty_set Empty_set fundef vardef) (f: function)
  (SBp: ListExt.SBinds f.(fn_params)) (SBt: ListExt.SBinds f.(fn_temps))
  (DIST: ListExt.DBinds f.(fn_params) f.(fn_temps))
  (body: cmd) (tout: type) (glob: denote_glob_ctxt Sm ctx)
  (internal: Maps.PTree.t (type * bool)) :
  forall (params_todo: list (AST.ident * type)) (args: list Vl)
    (e0: Maps.PTree.t Vl) (done_tree: Maps.PTree.t (type * bool))
    (TENV0: OpSem.Typing.type_env f e0 = Some done_tree)
    (WTbody0: type_cmd (with_internal internal
                (with_pure (mk_typing_tree true params_todo done_tree)
                   (with_stack [] ctx))) body = Some tout)
    (WT_ARGS: Forall2 (wt_value (Pt := Pt)) args (List.map snd params_todo))
    (INall: List.Forall (fun idt => List.In idt (f.(fn_params) ++ f.(fn_temps))) params_todo)
    (TENVfin: OpSem.Typing.type_env f
             (List.fold_left (fun e p => Maps.PTree.set (fst (fst p)) (snd p) e)
                (List.combine params_todo args) e0)
           = Some (mk_typing_tree true params_todo done_tree)),
  denote_app_values (List.map snd params_todo) tout
    (denote_function_curried internal params_todo done_tree body tout (denote_env TENV0) WTbody0 glob) args
  = denote_cmd WTbody0 (denote_env TENVfin, tt, glob).
Proof using Type.
  induction params_todo as [| [id t] rest IH]; intros.
  - inversion WT_ARGS; subst args.
    cbn [denote_app_values denote_function_curried List.combine List.fold_left] in *.
    rewrite (denote_env_pirr TENVfin TENV0). reflexivity.
  - inversion WT_ARGS as [| a0 t0 args0 ts0 WTa WT_ARGS' AE TEa]; subst.
    pose proof (List.Forall_inv INall) as INhead.
    pose proof (List.Forall_inv_tail INall) as INtail.
    pose proof (Value.Facts.type_of_value_complete WTa) as TY.
    cbn [List.map fst snd denote_app_values List.combine List.fold_left] in *.
    destruct ((ReflectExt.sumbool_of_reflect type_eqb_spec) (Value.type_of_value a0) t) as [EQ|NE]; [| contradiction].
    rewrite (denote_value_eq_eq_rect EQ TY).
    cbn [denote_function_curried].
    pose (TENV0' := type_env_set_some f e0 done_tree SBp SBt DIST id t a0 INhead TY TENV0).
    rewrite -(denote_env_set' f e0 SBp SBt DIST id t a0 INhead TY done_tree TENV0 TENV0').
    exact (IH args0 (Maps.PTree.set id a0 e0) (Maps.PTree.set id (t, true) done_tree)
             TENV0' WTbody0 WT_ARGS' INtail TENVfin).
Qed.

Lemma ptree_set_comm {A} (id1 id2: positive) (a b: A) (m: Maps.PTree.t A)
  (NE: id1 <> id2) :
  Maps.PTree.set id1 a (Maps.PTree.set id2 b m)
  = Maps.PTree.set id2 b (Maps.PTree.set id1 a m).
Proof using Type.
  apply Maps.PTree.extensionality. intro k.
  destruct (Pos.eq_dec k id1) as [->|H1].
  - rewrite Maps.PTree.gss (Maps.PTree.gso _ _ NE) Maps.PTree.gss. reflexivity.
  - destruct (Pos.eq_dec k id2) as [->|H2].
    + rewrite (Maps.PTree.gso _ _ H1) Maps.PTree.gss Maps.PTree.gss. reflexivity.
    + rewrite (Maps.PTree.gso _ _ H1) (Maps.PTree.gso _ _ H2)
              (Maps.PTree.gso _ _ H2) (Maps.PTree.gso _ _ H1). reflexivity.
Qed.

Lemma fold_set_push {A} (id: positive) (v: A) :
  forall (params: list (AST.ident * type)) (args: list A) (e0: Maps.PTree.t A),
    ListExt.AbsBind id params ->
    List.fold_left (fun e p => Maps.PTree.set (fst (fst p)) (snd p) e)
                   (List.combine params args) (Maps.PTree.set id v e0)
    = Maps.PTree.set id v
        (List.fold_left (fun e p => Maps.PTree.set (fst (fst p)) (snd p) e)
                        (List.combine params args) e0).
Proof using Type.
  induction params as [|[id' t'] params' IH]; intros args e0 ABS.
  - reflexivity.
  - destruct args as [|v' args'].
    + reflexivity.
    + cbn [List.combine List.fold_left fst snd].
      assert (AUX: id <> id' /\ ListExt.AbsBind id params')
        by (inversion ABS; subst; split; assumption).
      destruct AUX as [NE ABS'].
      rewrite (ptree_set_comm id' id v' v e0 (not_eq_sym NE)).
      exact (IH args' (Maps.PTree.set id' v' e0) ABS').
Qed.

Lemma combine_fold_set_eq_set_params :
  forall (params: list (AST.ident * type)) (args: list Vl),
    ListExt.SBinds params ->
    List.fold_left (fun e p => Maps.PTree.set (fst (fst p)) (snd p) e)
                   (List.combine params args) Maps.PTree.Empty
    = OpSem.set_params params args.
Proof using Type.
  induction params as [|[id t] params' IH]; intros args SB.
  - destruct args; reflexivity.
  - assert (AUX: ListExt.AbsBind id params' /\ ListExt.SBinds params')
      by (inversion SB; subst; split; assumption).
    destruct AUX as [ABS SB'].
    destruct args as [|v args'].
    + reflexivity.
    + cbn [List.combine List.fold_left OpSem.set_params fst snd].
      rewrite (fold_set_push id v params' args' Maps.PTree.Empty ABS).
      rewrite (IH args' SB').
      reflexivity.
Qed.

Lemma denote_function_curried_pirr
  [gctx: ctxt Empty_set Empty_set Empty_set fundef vardef]
  (internal: Maps.PTree.t (type * bool))
  (params: list (AST.ident * type)) (dt: Maps.PTree.t (type * bool))
  (body: cmd) (tout: type) (env: denote_tree denote_binding dt)
  (W1 W2: type_cmd
            (with_internal internal
               (with_pure (mk_typing_tree true params dt)
                  (with_stack [] gctx))) body = Some tout)
  (glob: denote_glob_ctxt Sm gctx) :
  denote_function_curried internal params dt body tout env W1 glob
  = denote_function_curried internal params dt body tout env W2 glob.
Proof using Type.
  assert (W1 = W2) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec (option type)))).
  reflexivity.
Qed.

Lemma type_env_Empty (f: function) :
  OpSem.Typing.type_env f (Maps.PTree.Empty: Maps.PTree.t Vl)
  = Some (mk_typing_tree false (f.(fn_params) ++ f.(fn_temps)) Maps.PTree.Empty).
Proof using Type.
  unfold OpSem.Typing.type_env.
  assert (OK: OpSem.Typing.type_env_ok (f.(fn_params) ++ f.(fn_temps))
                (Maps.PTree.Empty: Maps.PTree.t Vl) = true).
  { unfold OpSem.Typing.type_env_ok. rewrite forallb_forall.
    intros [id t] _. cbn [fst snd]. rewrite Maps.PTree.gempty. reflexivity. }
  rewrite OK. reflexivity.
Qed.

Lemma uninit_eq_denote_env (f: function)
  (H: forall p a, Maps.PTree.get p
        (mk_typing_tree false (f.(fn_params) ++ f.(fn_temps)) Maps.PTree.Empty) = Some a
      -> denote_binding a = None)
  (TENV: OpSem.Typing.type_env f Maps.PTree.Empty
         = Some (mk_typing_tree false (f.(fn_params) ++ f.(fn_temps)) Maps.PTree.Empty)) :
  denote_tree_uninit _ H = denote_env TENV.
Proof using Type.
  apply (denote_tree_ext).
  intros k [tk bk] a_d GET DEN.
  destruct bk.
  - exfalso.
    refine (Prog.Facts.mk_typing_tree_false_not_true (f.(fn_params) ++ f.(fn_temps))
              Maps.PTree.Empty _ k tk GET).
    intros id v TYv. rewrite Maps.PTree.gempty in TYv. discriminate TYv.
  - destruct tk; discriminate DEN.
Qed.

Lemma denote_function_eq
  [gctx: ctxt Empty_set Empty_set Empty_set fundef vardef] [fn: function]
  (WT: type_function gctx fn = true)
  (glob: denote_glob_ctxt Sm gctx)
  (WTbody: type_cmd (mk_function_ctxt fn.(fn_params) fn.(fn_temps) fn.(fn_internals) gctx)
             fn.(fn_body) = Some fn.(fn_return))
  (TENVempty: OpSem.Typing.type_env fn Maps.PTree.Empty
               = Some (mk_typing_tree false (fn.(fn_params) ++ fn.(fn_temps))
                         Maps.PTree.Empty)) :
  denote_function WT glob
  = denote_function_curried (mk_typing_tree false fn.(fn_internals) Maps.PTree.Empty)
      fn.(fn_params)
      (mk_typing_tree false (fn.(fn_params) ++ fn.(fn_temps)) Maps.PTree.Empty)
      fn.(fn_body) fn.(fn_return)
      (denote_env TENVempty) WTbody glob.
Proof using Type.
  unfold denote_function.
  erewrite (conv_option_app WTbody).
  erewrite (conv_bool_app (ReflectExt.reflect_refl type_eqb_spec fn.(fn_return))).
  rewrite (uninit_eq_denote_env fn _ TENVempty).
  apply denote_function_curried_pirr.
Qed.

Lemma denote_fundef_call_Internal_raw
  [gctx: ctxt Empty_set Empty_set Empty_set fundef vardef] [fn: function]
  (WTFD: type_fundef gctx (AST.Internal fn) = true)
  (SIG: type_funsig (AST.Internal fn) = Some (fn_signature fn))
  (glob: denote_glob_ctxt Sm gctx) (args: list Vl) :
  denote_fundef_call WTFD SIG glob args
  = denote_app_values (List.map snd fn.(fn_params)) fn.(fn_return)
      (denote_function WTFD glob) args.
Proof using Type.
  cbn [denote_fundef_call].
  rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect signature_eqb_spec)).
  reflexivity.
Qed.

Lemma denote_fundef_call_Internal
  [gctx: ctxt Empty_set Empty_set Empty_set fundef vardef] [fn: function]
  (WTFD: type_fundef gctx (AST.Internal fn) = true)
  (SIG: type_funsig (AST.Internal fn) = Some (fn_signature fn))
  (glob: denote_glob_ctxt Sm gctx) (args: list Vl)
  (SBp: ListExt.SBinds fn.(fn_params)) (SBt: ListExt.SBinds fn.(fn_temps))
  (DIST: ListExt.DBinds fn.(fn_params) fn.(fn_temps))
  (WT_ARGS: Forall2 (wt_value (Pt := Pt)) args (List.map snd fn.(fn_params)))
  (WTbody: type_cmd (mk_function_ctxt fn.(fn_params) fn.(fn_temps) fn.(fn_internals) gctx)
             fn.(fn_body) = Some fn.(fn_return))
  (TENVfin: OpSem.Typing.type_env fn (OpSem.set_params fn.(fn_params) args)
         = Some (ctxt_pure (mk_function_ctxt fn.(fn_params) fn.(fn_temps) fn.(fn_internals) gctx))) :
  denote_fundef_call WTFD SIG glob args
  = denote_cmd WTbody (denote_env TENVfin, tt, glob).
Proof using Type.
  rewrite (denote_fundef_call_Internal_raw WTFD SIG glob args).
  rewrite (denote_function_eq WTFD glob WTbody (type_env_Empty fn)).
  assert (INall: List.Forall
            (fun idt => List.In idt (fn.(fn_params) ++ fn.(fn_temps))) fn.(fn_params))
    by (apply List.Forall_forall; intros idt IN; apply List.in_or_app; left; exact IN).
  pose proof (combine_fold_set_eq_set_params fn.(fn_params) args SBp) as Ecomb.
  assert (TENVfinc: OpSem.Typing.type_env fn
            (List.fold_left (fun e p => Maps.PTree.set (fst (fst p)) (snd p) e)
               (List.combine fn.(fn_params) args) Maps.PTree.Empty)
          = Some (mk_typing_tree true fn.(fn_params)
                    (mk_typing_tree false (fn.(fn_params) ++ fn.(fn_temps))
                       Maps.PTree.Empty))).
  { rewrite Ecomb. exact TENVfin. }
  rewrite (denote_app_values_function_curried gctx fn SBp SBt DIST
             fn.(fn_body) fn.(fn_return) glob
             (mk_typing_tree false fn.(fn_internals) Maps.PTree.Empty)
             fn.(fn_params) args Maps.PTree.Empty
             (mk_typing_tree false (fn.(fn_params) ++ fn.(fn_temps)) Maps.PTree.Empty)
             (type_env_Empty fn) WTbody WT_ARGS INall TENVfinc).
  revert TENVfinc. rewrite Ecomb. intro TENVfinc.
  rewrite (denote_env_pirr TENVfinc TENVfin).
  reflexivity.
Qed.

Lemma step_internal_function_correct p f args (k: @OpSem.cont Sm)
  (s: Sm) t t' WTp
  (WT_ARGS: Forall2 (wt_value (Pt := Pt)) args (List.map snd f.(fn_params)))
  (CALLK: OpSem.is_call_cont k)
  (Ts:  OpSem.Typing.type_state p (OpSem.Callstate (AST.Internal f) args k s) = Some t)
  (Ts': OpSem.Typing.type_state p
          (OpSem.State f f.(fn_body) k (OpSem.set_params f.(fn_params) args) [] s) = Some t') :
  denote_state WTp Ts = denote_state WTp Ts'.
Proof using Type.
  destruct (type_state_Callstate_inv _ _ _ _ _ _ Ts)
    as (sig & t_kS & SIGs & WTFDs & WTCONTs & EQs & TYs & WTARGSs).
  assert (sig = fn_signature f) as Esig by (cbn [type_funsig] in SIGs; congruence).
  subst sig.
  erewrite (denote_state_Callstate p (AST.Internal f) args k s t WTp Ts
              (fn_signature f) SIGs WTFDs t_kS WTCONTs EQs WTARGSs).
  destruct (type_state_State_inv _ _ _ _ _ _ _ _ Ts')
    as (ty_env & t_cR & t_kR & TENV & WTCMD & WTCONTr & EQr & EtcR & WTFNr).
  clear EtcR.
  erewrite (denote_state_State p f f.(fn_body) k (OpSem.set_params f.(fn_params) args) []
              s t' WTp Ts' ty_env TENV t_cR WTCMD t_kR WTCONTr EQr WTFNr).
  pose proof (type_function_correct (mk_glob_ctxt p) f WTFDs) as WTfn.
  pose proof (wt_fn_params_sbinds WTfn) as SBp.
  pose proof (wt_fn_temps_sbinds WTfn) as SBt.
  pose proof (wt_fn_params_temps_distinct WTfn) as DIST.
  pose proof (type_cmd_complete (wt_fn_cmd WTfn)) as WTbody.
  pose proof (curry_tree_eq_type_env_tree (mk_glob_ctxt p) f args SBp SBt DIST WT_ARGS)
    as TREEEQ.
  assert (TY: OpSem.Typing.type_env_tree f (OpSem.set_params f.(fn_params) args) = ty_env).
  { unfold OpSem.Typing.type_env in TENV.
    destruct (OpSem.Typing.type_env_ok (f.(fn_params) ++ f.(fn_temps))
                (OpSem.set_params f.(fn_params) args));
      [ injection TENV as ->; reflexivity | discriminate TENV ]. }
  assert (TYENV: ty_env = ctxt_pure (mk_function_ctxt f.(fn_params) f.(fn_temps) f.(fn_internals) (mk_glob_ctxt p)))
    by (rewrite -TY; symmetry; exact TREEEQ).
  clear TY TREEEQ. subst ty_env.
  setoid_rewrite (denote_fundef_call_Internal WTFDs SIGs (denote_glob_ctxt_of_program p WTp) args
             SBp SBt DIST WT_ARGS WTbody TENV).
  pose proof (reflect_eq_of_true type_eqb_spec EQs) as EkS.
  cbn [fn_signature sig_res] in EkS. clear TYs. subst t_kS.
  assert (EcR: t_cR = f.(fn_return)).
  { assert (WTCMD': type_cmd (mk_function_ctxt f.(fn_params) f.(fn_temps) f.(fn_internals) (mk_glob_ctxt p))
              f.(fn_body) = Some t_cR) by exact WTCMD.
    congruence. }
  subst t_cR.
  pose proof (reflect_eq_of_true type_eqb_spec EQr) as EkR. subst t_kR.
  cbn [denote_locals].
  rewrite (denote_cmd_pirr WTbody WTCMD).
  f_equiv. intro v.
  cbn [fn_signature sig_res].
  rewrite (convert_eq_refl_id _ _ v).
  rewrite (convert_eq_refl_id _ _ v).
  exact (denote_cont_call_eq_denote_cont (mk_glob_ctxt p) f
           (ctxt_pure (mk_function_ctxt f.(fn_params) f.(fn_temps) f.(fn_internals) (mk_glob_ctxt p)))
           []
           k CALLK f.(fn_return) WTCONTs WTCONTr (denote_env TENV) tt
           (denote_glob_ctxt_of_program p WTp) v).
Qed.

Lemma denote_cmd_free_ptr {ctx} {e_ptr} {id_f}
  (WT: type_cmd ctx (c_free_ptr e_ptr) = Some t_unit)
  (env: denote_ctxt ctx)
  (SRCH: find_exf_genv AST.EF_free ctx = Some id_f)
  (WTptr: type_expr ctx.(ctxt_pure) e_ptr = Some t_ptr) :
  denote_cmd WT env = free_ptr (denote_expr WTptr (fst (fst env))).
Proof using Type.
  cbn [denote_cmd].
  erewrite (conv_option_app SRCH).
  erewrite (conv_option_app WTptr).
  rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  reflexivity.
Qed.

Lemma denote_cmd_read_ptr {ctx} {e_ptr t_val}
  (WT: type_cmd ctx (c_read_ptr e_ptr t_val) = Some t_val)
  (env: denote_ctxt ctx)
  (WTptr: type_expr ctx.(ctxt_pure) e_ptr = Some t_ptr) :
  denote_cmd WT env =
  convert_eq (eq_sym (f_equal (Monad.program Sm) (denote_types_agree t_val)))
    (read_ptr (So := denote_type_memval t_val) (denote_expr WTptr (fst (fst env)))).
Proof using Type.
  cbn [denote_cmd].
  erewrite (conv_option_app WTptr).
  rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  reflexivity.
Qed.

Lemma denote_cmd_shift_fw_ptr {ctx} {e_ptr e_ofst}
  (WT: type_cmd ctx (c_shift_fw_ptr e_ptr e_ofst) = Some t_ptr)
  (env: denote_ctxt ctx)
  (WTptr: type_expr ctx.(ctxt_pure) e_ptr = Some t_ptr)
  (WTofst: type_expr ctx.(ctxt_pure) e_ofst = Some t_ofst) :
  denote_cmd WT env =
  shift_fw_ptr (denote_expr WTptr (fst (fst env))) (denote_expr WTofst (fst (fst env))).
Proof using Type.
  cbn [denote_cmd].
  erewrite (conv_option_app WTptr).
  erewrite (conv_option_app WTofst).
  now rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
Qed.

Lemma denote_cmd_shift_bw_ptr {ctx} {e_ptr e_ofst}
  (WT: type_cmd ctx (c_shift_bw_ptr e_ptr e_ofst) = Some t_ptr)
  (env: denote_ctxt ctx)
  (WTptr: type_expr ctx.(ctxt_pure) e_ptr = Some t_ptr)
  (WTofst: type_expr ctx.(ctxt_pure) e_ofst = Some t_ofst) :
  denote_cmd WT env =
  shift_bw_ptr (denote_expr WTptr (fst (fst env))) (denote_expr WTofst (fst (fst env))).
Proof using Type.
  cbn [denote_cmd].
  now erewrite (conv_option_app WTptr),
    (conv_option_app WTofst),
    <- (Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
Qed.

Lemma denote_cmd_ptr_eq {ctx} {e_ptr_l e_ptr_r}
  (WT: type_cmd ctx (c_ptr_eq e_ptr_l e_ptr_r) = Some t_bool)
  (env: denote_ctxt ctx)
  (WTl: type_expr ctx.(ctxt_pure) e_ptr_l = Some t_ptr)
  (WTr: type_expr ctx.(ctxt_pure) e_ptr_r = Some t_ptr) :
  denote_cmd WT env =
  eq_ptr (denote_expr WTl (fst (fst env))) (denote_expr WTr (fst (fst env))).
Proof using Type.
  cbn [denote_cmd].
  now erewrite (conv_option_app WTl),
    (conv_option_app WTr),
    <- (Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
Qed.

Lemma denote_cmd_div {ctx} {e_l e_r}
  (WT: type_cmd ctx (c_div e_l e_r) = Some t_nat)
  (env: denote_ctxt ctx)
  (WTl: type_expr ctx.(ctxt_pure) e_l = Some t_nat)
  (WTr: type_expr ctx.(ctxt_pure) e_r = Some t_nat) :
  denote_cmd WT env =
  Intops.Unsigned.div (denote_expr WTl (fst (fst env))) (denote_expr WTr (fst (fst env))).
Proof using Type.
  cbn [denote_cmd].
  now erewrite (conv_option_app WTl),
    (conv_option_app WTr),
    <- (Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
Qed.

Lemma denote_cmd_mod {ctx} {e_l e_r}
  (WT: type_cmd ctx (c_mod e_l e_r) = Some t_nat)
  (env: denote_ctxt ctx)
  (WTl: type_expr ctx.(ctxt_pure) e_l = Some t_nat)
  (WTr: type_expr ctx.(ctxt_pure) e_r = Some t_nat) :
  denote_cmd WT env =
  Intops.Unsigned.mdl (denote_expr WTl (fst (fst env))) (denote_expr WTr (fst (fst env))).
Proof using Type.
  cbn [denote_cmd].
  now erewrite (conv_option_app WTl),
    (conv_option_app WTr),
    <- (Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
Qed.

Lemma denote_cmd_ret {ctx} {e t}
  (WT: type_cmd ctx (c_ret e) = Some t)
  (env: denote_ctxt ctx)
  (WTe: type_expr ctx.(ctxt_pure) e = Some t) :
  denote_cmd WT env = ret (denote_expr WTe (fst (fst env))).
Proof using Type.
  cbn [denote_cmd]. f_equal. apply denote_expr_pirr.
Qed.

Lemma denote_cmd_alloc_ptr {ctx} {e_size t_init e_init} {id_m}
  (WT: type_cmd ctx (c_alloc_ptr e_size t_init e_init) = Some t_ptr)
  (env: denote_ctxt ctx)
  (SRCH: find_exf_genv AST.EF_malloc ctx = Some id_m)
  (WTsize: type_expr ctx.(ctxt_pure) e_size = Some t_ofst)
  (WTinit: type_expr ctx.(ctxt_pure) e_init = Some t_init) :
  denote_cmd WT env =
  alloc_ptr (So := denote_type_memval t_init)
    (denote_expr WTsize (fst (fst env)))
    (convert_eq (denote_types_agree t_init) (denote_expr WTinit (fst (fst env)))).
Proof using Type.
  cbn [denote_cmd].
  erewrite (conv_option_app SRCH).
  erewrite (conv_option_app WTsize),
    (conv_option_app WTinit),
    (conv_bool_app (ReflectExt.reflect_refl type_eqb_spec t_init)),
    <- (Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  destruct t_init; reflexivity.
Qed.

Lemma denote_cmd_write_ptr {ctx} {e_ptr t_val e_val}
  (WT: type_cmd ctx (c_write_ptr e_ptr t_val e_val) = Some t_unit)
  (env: denote_ctxt ctx)
  (WTptr: type_expr ctx.(ctxt_pure) e_ptr = Some t_ptr)
  (WTval: type_expr ctx.(ctxt_pure) e_val = Some t_val) :
  denote_cmd WT env =
  write_ptr (So := denote_type_memval t_val)
    (denote_expr WTptr (fst (fst env)))
    (convert_eq (denote_types_agree t_val) (denote_expr WTval (fst (fst env)))).
Proof using Type.
  cbn [denote_cmd].
  erewrite (conv_option_app WTptr),
    (conv_option_app WTval),
    (conv_bool_app (ReflectExt.reflect_refl type_eqb_spec t_val)),
    <- (Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  destruct t_val; reflexivity.
Qed.

Lemma denote_cmd_read_var {ctx} {o_v t_v}
  (WT: type_cmd ctx (c_read_var o_v t_v) = Some t_v)
  (env: denote_ctxt ctx)
  (NTH: get_stack o_v ctx = Some tt) :
  denote_cmd WT env =
  convert_eq (eq_sym (f_equal (Monad.program Sm) (denote_types_agree t_v)))
    (read_var (So := denote_type_memval t_v)
       (denote_stack_lookup NTH eq_refl (snd (fst env)))).
Proof using Type.
  cbn [denote_cmd].
  erewrite (conv_option_app NTH).
  rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  reflexivity.
Qed.

Lemma denote_cmd_write_var {ctx} {o_v t_v e_v}
  (WT: type_cmd ctx (c_write_var o_v t_v e_v) = Some t_unit)
  (env: denote_ctxt ctx)
  (WTval: type_expr ctx.(ctxt_pure) e_v = Some t_v)
  (NTH: get_stack o_v ctx = Some tt) :
  denote_cmd WT env =
  write_var (So := denote_type_memval t_v)
    (denote_stack_lookup NTH eq_refl (snd (fst env)))
    (convert_eq (denote_types_agree t_v) (denote_expr WTval (fst (fst env)))).
Proof using Type.
  cbn [denote_cmd].
  erewrite (conv_option_app WTval).
  erewrite (conv_option_app NTH).
  erewrite (conv_bool_app (ReflectExt.reflect_refl type_eqb_spec t_v)).
  rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  destruct t_v; reflexivity.
Qed.

Lemma denote_cmd_with_var {ctx} {t_v e_v c_c t_c}
  (WT: type_cmd ctx (c_with_var t_v e_v c_c) = Some t_c)
  (env: denote_ctxt ctx)
  (WTinit: type_expr ctx.(ctxt_pure) e_v = Some t_v)
  (WTc: type_cmd (push_stack tt ctx) c_c = Some t_c) :
  denote_cmd WT env =
  with_var (So := denote_type_memval t_v)
    (convert_eq (denote_types_agree t_v) (denote_expr WTinit (fst (fst env))))
    (fun x => denote_cmd WTc
                (fst (fst env), denote_stack_push (snd (fst env)) eq_refl x, snd env)).
Proof using Type.
  cbn [denote_cmd].
  erewrite (conv_option_app WTinit).
  erewrite (conv_option_app WTc).
  erewrite (conv_bool_app (ReflectExt.reflect_refl type_eqb_spec t_v)).
  rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  destruct t_v; reflexivity.
Qed.

Definition pure_agree
  (T1 T2: Maps.PTree.t (type * bool))
  (env1: denote_tree denote_binding T1) (env2: denote_tree denote_binding T2) : Prop :=
  forall id t (G1: Maps.PTree.get id T1 = Some (t, true))
              (G2: Maps.PTree.get id T2 = Some (t, true)),
    denote_tree_lookup G1 (denote_binding_eq t) env1
    = denote_tree_lookup G2 (denote_binding_eq t) env2.

Lemma denote_expr_frame
  (T1 T2: Maps.PTree.t (type * bool))
  (env1: denote_tree denote_binding T1) (env2: denote_tree denote_binding T2)
  (AG: pure_agree T1 T2 env1 env2) :
  forall e t (WT1: type_expr T1 e = Some t) (WT2: type_expr T2 e = Some t),
  denote_expr WT1 env1 = denote_expr WT2 env2.
Proof using Type.
  induction e as [ var_id | | b | n | ofst | | e1 IH1 | e1 IH1 e2 IH2 | e1 IH1 e2 IH2
                 | e1 IH1 e2 IH2 ];
    intros t WT1 WT2.
  - pose proof (type_expr_var_inv _ _ _ WT1) as G1.
    pose proof (type_expr_var_inv _ _ _ WT2) as G2.
    rewrite (denote_expr_var _ _ _ WT1 _ G1) (denote_expr_var _ _ _ WT2 _ G2).
    apply AG.
  - assert (t = t_unit) as -> by (cbn in WT1; congruence). reflexivity.
  - assert (t = t_bool) as -> by (cbn in WT1; congruence). reflexivity.
  - assert (t = t_nat) as -> by (cbn in WT1; destruct (Z.leb _ _); congruence).
    rewrite (denote_expr_nat _ _ WT1) (denote_expr_nat _ _ WT2). reflexivity.
  - assert (t = t_ofst) as -> by (cbn in WT1; destruct (Z.leb _ _); congruence).
    rewrite (denote_expr_ofst _ _ WT1) (denote_expr_ofst _ _ WT2). reflexivity.
  - assert (t = t_ptr) as -> by (cbn in WT1; congruence). reflexivity.
  - destruct (type_expr_neg_inv _ _ _ WT1) as [T1a ->].
    destruct (type_expr_neg_inv _ _ _ WT2) as [T2a _].
    rewrite (denote_expr_neg _ _ WT1 _ T1a) (denote_expr_neg _ _ WT2 _ T2a).
    f_equal. apply IH1.
  - destruct (type_expr_add_inv _ _ _ _ WT1) as (T1a & T1b & ->).
    destruct (type_expr_add_inv _ _ _ _ WT2) as (T2a & T2b & _).
    rewrite (denote_expr_add _ _ _ WT1 _ T1a T1b) (denote_expr_add _ _ _ WT2 _ T2a T2b).
    f_equal; [apply IH1 | apply IH2].
  - destruct (type_expr_mul_inv _ _ _ _ WT1) as (T1a & T1b & ->).
    destruct (type_expr_mul_inv _ _ _ _ WT2) as (T2a & T2b & _).
    rewrite (denote_expr_mul _ _ _ WT1 _ T1a T1b) (denote_expr_mul _ _ _ WT2 _ T2a T2b).
    f_equal; [apply IH1 | apply IH2].
  - destruct (type_expr_eqb_inv _ _ _ _ WT1) as (T1a & T1b & ->).
    destruct (type_expr_eqb_inv _ _ _ _ WT2) as (T2a & T2b & _).
    rewrite (denote_expr_eqb _ _ _ WT1 _ T1a T1b) (denote_expr_eqb _ _ _ WT2 _ T2a T2b).
    f_equal; [apply IH1 | apply IH2].
Qed.

Lemma forall2b_opt_cons_inv {ctx a args' t params'}
  (WT: ListExt.forall2b_opt type_eqb (type_expr ctx) (a :: args') (t :: params') = true) :
  type_expr ctx a = Some t
  /\ ListExt.forall2b_opt type_eqb (type_expr ctx) args' params' = true.
Proof using Type.
  cbn in WT.
  destruct (type_expr ctx a) as [t'|] eqn:TYPa; [ | discriminate WT ].
  apply andb_prop in WT as [EQb REST].
  apply (reflect_eq_of_true type_eqb_spec) in EQb. subst t'. auto.
Qed.

Lemma denote_app_pirr {ctx params ret args}
  (d_fn: denote_sig' params ret) (env: denote_pure_ctxt Sm ctx)
  (W1 W2: ListExt.forall2b_opt type_eqb (type_expr ctx.(ctxt_pure)) args params = true) :
  denote_app d_fn env W1 = denote_app d_fn env W2.
Proof using Type. assert (W1 = W2) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec bool))). reflexivity. Qed.

Lemma denote_app_nil {ctx ret}
  (d_fn: denote_sig' [] ret) (env: denote_pure_ctxt Sm ctx)
  (WT: ListExt.forall2b_opt type_eqb (type_expr ctx.(ctxt_pure)) [] [] = true) :
  denote_app d_fn env WT = d_fn.
Proof using Type. cbn [denote_app]. reflexivity. Qed.

Lemma denote_app_cons {ctx t params' ret a args'}
  (d_fn: denote_sig' (t :: params') ret)
  (env: denote_pure_ctxt Sm ctx)
  (WT: ListExt.forall2b_opt type_eqb (type_expr ctx.(ctxt_pure)) (a :: args') (t :: params') = true)
  (WTa: type_expr ctx.(ctxt_pure) a = Some t)
  (WT': ListExt.forall2b_opt type_eqb (type_expr ctx.(ctxt_pure)) args' params' = true) :
  denote_app d_fn env WT = denote_app (d_fn (denote_expr WTa env)) env WT'.
Proof using Type.
  cbn [denote_app].
  erewrite (conv_option_app WTa).
  erewrite (conv_bool_app (ReflectExt.reflect_refl type_eqb_spec t)).
  destruct t; apply denote_app_pirr.
Qed.

Lemma denote_app_frame (args: list expr) :
  forall {ctx1 ctx2: ctxt (type * bool) (type * bool) unit fundef vardef} {params ret}
         (d_fn: denote_sig' params ret)
         (env1: denote_pure_ctxt Sm ctx1) (env2: denote_pure_ctxt Sm ctx2)
         (AG: pure_agree (ctxt_pure ctx1) (ctxt_pure ctx2) env1 env2)
         (WT1: ListExt.forall2b_opt type_eqb (type_expr ctx1.(ctxt_pure)) args params = true)
         (WT2: ListExt.forall2b_opt type_eqb (type_expr ctx2.(ctxt_pure)) args params = true),
  denote_app d_fn env1 WT1 = denote_app d_fn env2 WT2.
Proof using Type.
  induction args as [| a args' IH];
    intros ctx1 ctx2 params ret d_fn env1 env2 AG WT1 WT2.
  - destruct params as [| t params'].
    + rewrite (denote_app_nil d_fn env1 WT1) (denote_app_nil d_fn env2 WT2). reflexivity.
    + cbn in WT1; discriminate.
  - destruct params as [| t params'].
    + cbn in WT1; discriminate.
    + destruct (forall2b_opt_cons_inv WT1) as [WTa1 WT1'].
      destruct (forall2b_opt_cons_inv WT2) as [WTa2 WT2'].
      rewrite (denote_app_cons d_fn env1 WT1 WTa1 WT1').
      rewrite (denote_app_cons d_fn env2 WT2 WTa2 WT2').
      rewrite (denote_expr_frame _ _ _ _ AG a t WTa1 WTa2).
      apply (IH _ _ params' ret (d_fn (denote_expr WTa2 env2)) env1 env2 AG WT1' WT2').
Qed.

Lemma denote_app_eq_denote_app_values
  [f env_v] [ctx: ctxt (type * bool) (type * bool) unit fundef vardef]
  (TENV: OpSem.Typing.type_env f env_v = Some (ctxt_pure ctx))
  [params ret args v_args]
  (d_fn: denote_sig' params ret)
  (WTargs: ListExt.forall2b_opt type_eqb (type_expr ctx.(ctxt_pure)) args params = true)
  (EVAL: ListExt.map_opt (fun e => eval e env_v) args = Some v_args) :
  denote_app d_fn (denote_env TENV) WTargs
  = denote_app_values params ret d_fn v_args.
Proof using Type.
  revert params ret d_fn v_args WTargs EVAL.
  induction args as [| a args' IH]; intros params ret d_fn v_args WTargs EVAL.
  - destruct params as [| t params']; [ | cbn in WTargs; discriminate ].
    cbn [ListExt.map_opt] in EVAL; injection EVAL as <-.
    rewrite (denote_app_nil d_fn (denote_env TENV) WTargs). reflexivity.
  - destruct params as [| t params']; [ cbn in WTargs; discriminate | ].
    destruct (forall2b_opt_cons_inv WTargs) as [WTa WTargs'].
    cbn [ListExt.map_opt] in EVAL.
    destruct (eval a env_v) as [v|] eqn:Ev; [ | discriminate ].
    destruct (ListExt.map_opt (fun e => eval e env_v) args') as [v_args'|] eqn:Evs;
      [ | discriminate ].
    injection EVAL as <-.
    rewrite (denote_app_cons d_fn (denote_env TENV) WTargs WTa WTargs').
    destruct (denote_expr_eval f env_v (ctxt_pure ctx) TENV a t v WTa Ev) as [TY EQ].
    rewrite EQ.
    cbn [denote_app_values].
    destruct ((ReflectExt.sumbool_of_reflect type_eqb_spec) (Value.type_of_value v) t) as [EQ0 | n];
      [ | exfalso; apply n; exact TY ].
    rewrite (denote_value_eq_eq_rect EQ0 TY).
    exact (IH params' ret (d_fn (denote_value_eq TY)) v_args' WTargs' eq_refl).
Qed.

Lemma pure_agree_set {T1 T2: Maps.PTree.t (type * bool)}
  {env1: denote_tree denote_binding T1} {env2: denote_tree denote_binding T2}
  (AG: pure_agree T1 T2 env1 env2)
  (id: positive) (t: type) (v: denote_type t) :
  pure_agree (Maps.PTree.set id (t, true) T1) (Maps.PTree.set id (t, true) T2)
    (denote_tree_set id (denote_binding_eq t) v env1)
    (denote_tree_set id (denote_binding_eq t) v env2).
Proof using Type.
  intros id0 t0 G1 G2.
  destruct (Pos.eq_dec id0 id) as [->|NE].
  - assert (t0 = t) as ->.
    { pose proof G1 as H. rewrite Maps.PTree.gss in H. congruence. }
    rewrite (denote_tree_lookup_set_same
               (denote_binding_eq t) v T1 id env1 G1).
    rewrite (denote_tree_lookup_set_same
               (denote_binding_eq t) v T2 id env2 G2).
    reflexivity.
  - pose proof G1 as G1'. rewrite Maps.PTree.gso in G1'; first by exact NE.
    pose proof G2 as G2'. rewrite Maps.PTree.gso in G2'; first by exact NE.
    rewrite (denote_tree_lookup_set_other
               (denote_binding_eq t) v T1 id id0 (not_eq_sym NE) env1
               (denote_binding_eq t0) G1 G1').
    rewrite (denote_tree_lookup_set_other
               (denote_binding_eq t) v T2 id id0 (not_eq_sym NE) env2
               (denote_binding_eq t0) G2 G2').
    exact (AG id0 t0 G1' G2').
Qed.

Lemma pure_agree_unset {T1 T2: Maps.PTree.t (type * bool)}
  {env1: denote_tree denote_binding T1} {env2: denote_tree denote_binding T2}
  (AG: pure_agree T1 T2 env1 env2)
  (id: positive) (t: type) :
  pure_agree (Maps.PTree.set id (t, false) T1) (Maps.PTree.set id (t, false) T2)
    (denote_tree_unset id (denote_binding_false_eq t) env1)
    (denote_tree_unset id (denote_binding_false_eq t) env2).
Proof using Type.
  intros id0 t0 G1 G2.
  destruct (Pos.eq_dec id0 id) as [->|NE].
  - exfalso. pose proof G1 as H. rewrite Maps.PTree.gss in H. discriminate H.
  - pose proof G1 as G1'. rewrite Maps.PTree.gso in G1'; first by exact NE.
    pose proof G2 as G2'. rewrite Maps.PTree.gso in G2'; first by exact NE.
    rewrite (denote_tree_lookup_unset_other
               (denote_binding_false_eq t) T1 id id0 (not_eq_sym NE) env1
               (denote_binding_eq t0) G1 G1').
    rewrite (denote_tree_lookup_unset_other
               (denote_binding_false_eq t) T2 id id0 (not_eq_sym NE) env2
               (denote_binding_eq t0) G2 G2').
    exact (AG id0 t0 G1' G2').
Qed.

Lemma type_cmd_read_var_inv ctx o_v t_v t :
  type_cmd ctx (c_read_var o_v t_v) = Some t ->
  get_stack o_v ctx = Some tt /\ t = t_v.
Proof using Type.
  intro H; cbn [type_cmd] in H.
  destruct (get_stack o_v ctx) as [u|] eqn:NTH; [ destruct u | discriminate H ].
  now injection H as <-.
Qed.

Lemma type_cmd_write_var_inv ctx o_v t_v e_v t :
  type_cmd ctx (c_write_var o_v t_v e_v) = Some t ->
  type_expr ctx.(ctxt_pure) e_v = Some t_v /\ get_stack o_v ctx = Some tt /\ t = t_unit.
Proof using Type.
  intro H; cbn [type_cmd] in H.
  destruct (type_expr ctx.(ctxt_pure) e_v) as [t'|] eqn:T1; try discriminate H.
  destruct (get_stack o_v ctx) as [u|] eqn:NTH; [ destruct u | discriminate H ].
  destruct (eqb_spec t_v t'); [ subst t' | discriminate H ].
  now injection H as <-.
Qed.

Lemma type_cmd_with_var_inv ctx t_v e_v c_c t :
  type_cmd ctx (c_with_var t_v e_v c_c) = Some t ->
  type_expr ctx.(ctxt_pure) e_v = Some t_v /\ type_cmd (push_stack tt ctx) c_c = Some t.
Proof using Type.
  intro H; cbn [type_cmd] in H.
  destruct (type_expr ctx.(ctxt_pure) e_v) as [t'|] eqn:T1; try discriminate H.
  destruct (type_cmd (push_stack tt ctx) c_c) as [t_c|] eqn:T2; try discriminate H.
  destruct (eqb_spec t_v t'); [ subst t' | discriminate H ].
  now injection H as <-.
Qed.

Lemma type_cmd_alloc_ptr_inv ctx e_size t_init e_init t :
  type_cmd ctx (c_alloc_ptr e_size t_init e_init) = Some t ->
  (exists id_m, find_exf_genv AST.EF_malloc ctx = Some id_m)
  /\ type_expr ctx.(ctxt_pure) e_size = Some t_ofst /\ type_expr ctx.(ctxt_pure) e_init = Some t_init /\ t = t_ptr.
Proof using Type.
  intro H; cbn [type_cmd] in H.
  destruct (find_exf_genv AST.EF_malloc ctx) as [ id_m | ] eqn:SRCH; [ | discriminate H ].
  split; [ now exists id_m | ].
  destruct (type_expr ctx.(ctxt_pure) e_size) as [ [ | | | | ] | ] eqn:T1; try discriminate H.
  destruct (type_expr ctx.(ctxt_pure) e_init) as [t'|] eqn:T2; try discriminate H.
  destruct (eqb_spec t_init t'); [ subst t' | discriminate H ].
  now injection H as <-.
Qed.

Lemma type_cmd_read_ptr_inv ctx e_ptr t_val t :
  type_cmd ctx (c_read_ptr e_ptr t_val) = Some t ->
  type_expr ctx.(ctxt_pure) e_ptr = Some t_ptr /\ t = t_val.
Proof using Type.
  intro H; cbn [type_cmd] in H.
  destruct (type_expr ctx.(ctxt_pure) e_ptr) as [ [ | | | | ] | ] eqn:T1; try discriminate H.
  injection H as <-. auto.
Qed.

Lemma type_cmd_write_ptr_inv ctx e_ptr t_val e_val t :
  type_cmd ctx (c_write_ptr e_ptr t_val e_val) = Some t ->
  type_expr ctx.(ctxt_pure) e_ptr = Some t_ptr /\ type_expr ctx.(ctxt_pure) e_val = Some t_val /\ t = t_unit.
Proof using Type.
  intro H; cbn [type_cmd] in H.
  destruct (type_expr ctx.(ctxt_pure) e_ptr) as [ [ | | | | ] | ] eqn:T1; try discriminate H.
  destruct (type_expr ctx.(ctxt_pure) e_val) as [t'|] eqn:T2; try discriminate H.
  destruct (eqb_spec t_val t'); [ subst t' | discriminate H ].
  injection H as <-. auto.
Qed.

Lemma type_cmd_free_ptr_inv ctx e_ptr t :
  type_cmd ctx (c_free_ptr e_ptr) = Some t ->
  (exists id_f, find_exf_genv AST.EF_free ctx = Some id_f)
  /\ type_expr ctx.(ctxt_pure) e_ptr = Some t_ptr /\ t = t_unit.
Proof using Type.
  intro H; cbn [type_cmd] in H.
  destruct (find_exf_genv AST.EF_free ctx) as [ id_f | ] eqn:SRCH; [ | discriminate H ].
  split; [ now exists id_f | ].
  destruct (type_expr ctx.(ctxt_pure) e_ptr) as [ [ | | | | ] | ] eqn:T1; try discriminate H.
  injection H as <-. auto.
Qed.

Lemma type_cmd_shift_fw_ptr_inv ctx e_ptr e_shift t :
  type_cmd ctx (c_shift_fw_ptr e_ptr e_shift) = Some t ->
  type_expr ctx.(ctxt_pure) e_ptr = Some t_ptr /\ type_expr ctx.(ctxt_pure) e_shift = Some t_ofst /\ t = t_ptr.
Proof using Type.
  intro H; cbn [type_cmd] in H.
  destruct (type_expr ctx.(ctxt_pure) e_ptr) as [ [ | | | | ] | ] eqn:T1; try discriminate H.
  destruct (type_expr ctx.(ctxt_pure) e_shift) as [ [ | | | | ] | ] eqn:T2; try discriminate H.
  injection H as <-. auto.
Qed.

Lemma type_cmd_shift_bw_ptr_inv ctx e_ptr e_shift t :
  type_cmd ctx (c_shift_bw_ptr e_ptr e_shift) = Some t ->
  type_expr ctx.(ctxt_pure) e_ptr = Some t_ptr /\ type_expr ctx.(ctxt_pure) e_shift = Some t_ofst /\ t = t_ptr.
Proof using Type.
  intro H; cbn [type_cmd] in H.
  destruct (type_expr ctx.(ctxt_pure) e_ptr) as [ [ | | | | ] | ] eqn:T1; try discriminate H.
  destruct (type_expr ctx.(ctxt_pure) e_shift) as [ [ | | | | ] | ] eqn:T2; try discriminate H.
  injection H as <-. auto.
Qed.

Lemma type_cmd_ptr_eq_inv ctx e_l e_r t :
  type_cmd ctx (c_ptr_eq e_l e_r) = Some t ->
  type_expr ctx.(ctxt_pure) e_l = Some t_ptr /\ type_expr ctx.(ctxt_pure) e_r = Some t_ptr /\ t = t_bool.
Proof using Type.
  intro H; cbn [type_cmd] in H.
  destruct (type_expr ctx.(ctxt_pure) e_l) as [ [ | | | | ] | ] eqn:T1; try discriminate H.
  destruct (type_expr ctx.(ctxt_pure) e_r) as [ [ | | | | ] | ] eqn:T2; try discriminate H.
  injection H as <-. auto.
Qed.

Lemma type_cmd_div_inv ctx e_l e_r t :
  type_cmd ctx (c_div e_l e_r) = Some t ->
  type_expr ctx.(ctxt_pure) e_l = Some t_nat /\ type_expr ctx.(ctxt_pure) e_r = Some t_nat /\ t = t_nat.
Proof using Type.
  intro H; cbn [type_cmd] in H.
  destruct (type_expr ctx.(ctxt_pure) e_l) as [ [ | | | | ] | ] eqn:T1; try discriminate H.
  destruct (type_expr ctx.(ctxt_pure) e_r) as [ [ | | | | ] | ] eqn:T2; try discriminate H.
  injection H as <-. auto.
Qed.

Lemma type_cmd_mod_inv ctx e_l e_r t :
  type_cmd ctx (c_mod e_l e_r) = Some t ->
  type_expr ctx.(ctxt_pure) e_l = Some t_nat /\ type_expr ctx.(ctxt_pure) e_r = Some t_nat /\ t = t_nat.
Proof using Type.
  intro H; cbn [type_cmd] in H.
  destruct (type_expr ctx.(ctxt_pure) e_l) as [ [ | | | | ] | ] eqn:T1; try discriminate H.
  destruct (type_expr ctx.(ctxt_pure) e_r) as [ [ | | | | ] | ] eqn:T2; try discriminate H.
  injection H as <-. auto.
Qed.

Lemma denote_tree_lookup_pirr {A: EqDec.type}
  {denote: A -> option Type} {m k a a_d}
  (G G': Maps.PTree.get k m = Some a) (D: denote a = Some a_d) (m_d: denote_tree denote m) :
  denote_tree_lookup G D m_d = denote_tree_lookup G' D m_d.
Proof using Type.
  destruct m as [|m']; [ discriminate G | ].
  unfold denote_tree_lookup; cbn beta iota.
  rewrite denote_tree_lookup'_tot_eq.
  rewrite denote_tree_lookup'_tot_eq.
  rewrite (denote_tree_lookup'_tot_pirr k G G' m_d).
  reflexivity.
Qed.

Definition genv_fn_lookup (ctx: ctxt (type * bool) (type * bool) unit fundef vardef) f_id fn
  (glob: denote_glob_ctxt Sm ctx)
  (FIND: get_global f_id ctx = Some (AST.Gfun (AST.Internal fn))) : denote_fn_sig Sm fn :=
  match Globalenvs.Genv.find_symbol (ctxt_global ctx) f_id as fs
    return (match fs with
            | Some b => Globalenvs.Genv.find_def (ctxt_global ctx) b
            | None => None
            end = Some (AST.Gfun (AST.Internal fn)) -> denote_fn_sig Sm fn)
  with
  | Some _ => fun GET' => denote_tree_lookup GET' eq_refl glob
  | None => fun GET' => False_rect _
      (eq_rect None (fun o => match o with Some _ => False | None => True end) I
         (Some (AST.Gfun (AST.Internal fn))) GET')
  end FIND.

Lemma genv_fn_lookup_frame (base: ctxt (type * bool) (type * bool) unit fundef vardef)
  (T1 T2: Maps.PTree.t (type * bool)) f_id fn (glob: denote_glob_ctxt Sm base)
  (FIND1: get_global f_id (with_pure T1 base) = Some (AST.Gfun (AST.Internal fn)))
  (FIND2: get_global f_id (with_pure T2 base) = Some (AST.Gfun (AST.Internal fn))) :
  genv_fn_lookup (with_pure T1 base) f_id fn glob FIND1
  = genv_fn_lookup (with_pure T2 base) f_id fn glob FIND2.
Proof using Type.
  unfold genv_fn_lookup, get_global in *.
  cbn [ctxt_global with_pure] in *.
  destruct (Globalenvs.Genv.find_symbol (ctxt_global base) f_id) as [b|] eqn:FS;
    [ | discriminate FIND1 ].
  apply (denote_tree_lookup_pirr).
Qed.

Lemma denote_cmd_app_internal {ctx f_id args fn t_args}
  (WT: type_cmd ctx (c_app f_id args) = Some fn.(fn_return))
  (env: denote_ctxt ctx)
  (FIND: get_global f_id ctx = Some (AST.Gfun (AST.Internal fn)))
  (MAP: ListExt.map_opt (type_expr ctx.(ctxt_pure)) args = Some t_args)
  (F2: ListExt.forall2b type_eqb t_args (List.map snd fn.(fn_params)) = true) :
  denote_cmd WT env =
  denote_app (genv_fn_lookup ctx f_id fn (snd env) FIND) (fst (fst env))
    (eq_trans (ListExt.forall2b_opt_map_opt _ _ _ _ _ MAP) F2).
Proof using Type.
  cbn [denote_cmd].
  erewrite (conv_option_app FIND).
  erewrite (conv_option_app MAP).
  erewrite (conv_bool_app F2).
  rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  unfold genv_fn_lookup. apply denote_app_pirr.
Qed.

Lemma denote_cmd_app_external {ctx f_id args ef sig t_args}
  (WT: type_cmd ctx (c_app f_id args) = Some sig.(sig_res))
  (env: denote_ctxt ctx)
  (FIND: get_global f_id ctx = Some (AST.Gfun (AST.External ef)))
  (DEC: Facts.ef_sig_dec ef = Some sig)
  (MAP: ListExt.map_opt (type_expr ctx.(ctxt_pure)) args = Some t_args)
  (F2: ListExt.forall2b type_eqb t_args sig.(sig_args) = true) :
  denote_cmd WT env =
  denote_app_exf FIND DEC (eq_trans (ListExt.forall2b_opt_map_opt _ _ _ _ _ MAP) F2) env.
Proof using Type.
  destruct ef as [ nm sg | | | | | | | | | | | ];
    try (exfalso; pose proof WT as WT'; cbn [type_cmd] in WT'; rewrite FIND in WT'; discriminate WT').
  cbn [denote_cmd].
  erewrite (conv_option_app FIND).
  erewrite (conv_option_app MAP).
  erewrite (conv_option_app DEC).
  erewrite (conv_bool_app F2).
  rewrite -(Eqdep_dec.eq_rect_eq_dec (ReflectExt.sumbool_of_reflect type_eqb_spec)).
  unfold denote_app_exf. apply denote_app_pirr.
Qed.

Lemma denote_app_exf_frame (base: ctxt (type * bool) (type * bool) unit fundef vardef)
  (T1 T2: Maps.PTree.t (type * bool)) f_id args ef sig
  (envp1: denote_tree denote_binding T1) (envp2: denote_tree denote_binding T2)
  (stk: denote_stack_ctxt Sm base) (glob: denote_glob_ctxt Sm base)
  (AG: pure_agree T1 T2 envp1 envp2)
  (FIND1: get_global f_id (with_pure T1 base) = Some (AST.Gfun (AST.External ef)))
  (FIND2: get_global f_id (with_pure T2 base) = Some (AST.Gfun (AST.External ef)))
  (DEC1 DEC2: Facts.ef_sig_dec ef = Some sig)
  (W1: ListExt.forall2b_opt type_eqb (type_expr (with_pure T1 base).(ctxt_pure)) args sig.(sig_args) = true)
  (W2: ListExt.forall2b_opt type_eqb (type_expr (with_pure T2 base).(ctxt_pure)) args sig.(sig_args) = true) :
  denote_app_exf FIND1 DEC1 W1 (envp1, stk, glob)
  = denote_app_exf FIND2 DEC2 W2 (envp2, stk, glob).
Proof using Type.
  assert (DEC1 = DEC2) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec (option signature)))).
  unfold denote_app_exf.
  cbn [ctxt_global with_pure ctxt_pure fst snd] in *.
  revert FIND1 FIND2.
  unfold get_global. cbn [ctxt_global with_pure] in *.
  destruct (Globalenvs.Genv.find_symbol (ctxt_global base) f_id) as [b|] eqn:FS;
    intros FIND1 FIND2; [ | discriminate FIND1 ].
  erewrite (denote_tree_lookup_pirr _ FIND2).
  apply (denote_app_frame args (ctx1:=with_pure T1 base) (ctx2:=with_pure T2 base) _ envp1 envp2 AG).
Qed.

Lemma type_cmd_app_inv ctx f_id args t :
  type_cmd ctx (c_app f_id args) = Some t ->
  (exists fn t_args, get_global f_id ctx = Some (AST.Gfun (AST.Internal fn))
       /\ ListExt.map_opt (type_expr ctx.(ctxt_pure)) args = Some t_args
       /\ ListExt.forall2b type_eqb t_args (List.map snd fn.(fn_params)) = true
       /\ t = fn.(fn_return))
  \/ (exists ef sig t_args, get_global f_id ctx = Some (AST.Gfun (AST.External ef))
       /\ ListExt.map_opt (type_expr ctx.(ctxt_pure)) args = Some t_args
       /\ Facts.ef_sig_dec ef = Some sig
       /\ ListExt.forall2b type_eqb t_args sig.(sig_args) = true
       /\ t = sig.(sig_res)).
Proof using Type.
  intro H; cbn [type_cmd] in H.
  destruct (get_global f_id ctx) as [ [ [ fn | [ nm sg | | | | | | | | | | | ] ] | gv ] | ] eqn:FIND;
    try discriminate H.
  - destruct (ListExt.map_opt (type_expr ctx.(ctxt_pure)) args) as [t_args|] eqn:MAP; [|discriminate H].
    destruct (ListExt.forall2b eqb t_args (List.map snd fn.(fn_params))) eqn:F2; [|discriminate H].
    injection H as <-. left. exists fn, t_args. auto.
  - destruct (ListExt.map_opt (type_expr ctx.(ctxt_pure)) args) as [t_args|] eqn:MAP; [|discriminate H].
    destruct (Facts.ef_sig_dec (AST.EF_external nm sg)) as [sig|] eqn:DEC; [|discriminate H].
    destruct (ListExt.forall2b eqb t_args sig.(sig_args)) eqn:F2; [|discriminate H].
    injection H as <-. right. exists (AST.EF_external nm sg), sig, t_args. auto.
Qed.

Local Ltac frame_e AG e t W1 W2 ev1 ev2 :=
  replace (denote_expr W1 ev1) with (denote_expr W2 ev2) by
    (first [ apply (denote_expr_frame _ _ _ _ AG e t W1 W2)
           | symmetry; apply (denote_expr_frame _ _ _ _ AG e t W1 W2) ]).

Lemma denote_cmd_frame (c: cmd) :
  forall (base: ctxt (type * bool) (type * bool) unit fundef vardef)
         (T1 T2: Maps.PTree.t (type * bool))
         (env1: denote_tree denote_binding T1)
         (env2: denote_tree denote_binding T2)
         (stk: denote_stack_ctxt Sm base)
         (glob: denote_glob_ctxt Sm base)
         (AG: pure_agree T1 T2 env1 env2)
         t (WT1: type_cmd (with_pure T1 base) c = Some t)
           (WT2: type_cmd (with_pure T2 base) c = Some t),
  denote_cmd WT1 (env1, stk, glob) = denote_cmd WT2 (env2, stk, glob).
Proof using Type.
  induction c as
    [ e
    | id_b t_b c_b IHc_b c_c IHc_c
    | e_if c_then IHc_then c_else IHc_else
    | c_cond IHc_cond c_body IHc_body
    | t_v e_v c_c IHc_c
    | o_v t_v
    | o_v t_v e_v
    | e_size t_init e_init
    | e_ptr t_val
    | e_ptr t_val e_val
    | e_ptr
    | e_ptr e_shift
    | e_ptr e_shift
    | e_l e_r
    | f_id args
    | e_l e_r
    | e_l e_r ];
    intros base T1 T2 env1 env2 stk glob AG t WT1 WT2.
  - rewrite (denote_cmd_ret WT1 (env1, stk, glob) WT1).
    rewrite (denote_cmd_ret WT2 (env2, stk, glob) WT2).
    cbn [fst snd]. f_equal. apply (denote_expr_frame _ _ _ _ AG e t WT1 WT2).
  - destruct (type_cmd_bind_inv _ _ _ _ _ _ WT1) as (GET1 & WTb1 & WTcc1).
    destruct (type_cmd_bind_inv _ _ _ _ _ _ WT2) as (GET2 & WTb2 & WTcc2).
    rewrite (denote_cmd_bind WT1 (env1, stk, glob) GET1 WTb1 WTcc1).
    rewrite (denote_cmd_bind WT2 (env2, stk, glob) GET2 WTb2 WTcc2).
    cbn [fst snd].
    rewrite (IHc_b base T1 T2 env1 env2 stk glob AG t_b WTb1 WTb2).
    f_equal. apply functional_extensionality; intro v.
    apply (IHc_c base (Maps.PTree.set id_b (t_b, true) T1)
                 (Maps.PTree.set id_b (t_b, true) T2) _ _ stk glob
                 (pure_agree_set AG id_b t_b v) t WTcc1 WTcc2).
  - destruct (type_cmd_if_inv _ _ _ _ _ WT1) as (WTc1 & WTt1 & te1 & WTe1 & EQ1).
    destruct (type_cmd_if_inv _ _ _ _ _ WT2) as (WTc2 & WTt2 & te2 & WTe2 & EQ2).
    apply (reflect_eq_of_true type_eqb_spec) in EQ1; subst te1.
    apply (reflect_eq_of_true type_eqb_spec) in EQ2; subst te2.
    rewrite (denote_cmd_if WT1 (env1, stk, glob) WTc1 WTt1 WTe1).
    rewrite (denote_cmd_if WT2 (env2, stk, glob) WTc2 WTt2 WTe2).
    cbn [fst snd].
    frame_e AG e_if t_bool WTc1 WTc2 env1 env2.
    destruct (denote_expr WTc2 env2).
    + apply (IHc_then base T1 T2 env1 env2 stk glob AG t WTt1 WTt2).
    + apply (IHc_else base T1 T2 env1 env2 stk glob AG t WTe1 WTe2).
  - destruct (type_cmd_while_inv _ _ _ _ WT1) as (WTcond1 & WTbody1 & ->).
    destruct (type_cmd_while_inv _ _ _ _ WT2) as (WTcond2 & WTbody2 & _).
    rewrite (denote_cmd_while WT1 (env1, stk, glob) WTcond1 WTbody1).
    rewrite (denote_cmd_while WT2 (env2, stk, glob) WTcond2 WTbody2).
    rewrite (IHc_cond base T1 T2 env1 env2 stk glob AG t_bool WTcond1 WTcond2).
    rewrite (IHc_body base T1 T2 env1 env2 stk glob AG t_unit WTbody1 WTbody2).
    reflexivity.
  - destruct (type_cmd_with_var_inv _ _ _ _ _ WT1) as (WTi1 & WTcc1).
    destruct (type_cmd_with_var_inv _ _ _ _ _ WT2) as (WTi2 & WTcc2).
    rewrite (denote_cmd_with_var WT1 (env1, stk, glob) WTi1 WTcc1).
    rewrite (denote_cmd_with_var WT2 (env2, stk, glob) WTi2 WTcc2).
    cbn [fst snd].
    frame_e AG e_v t_v WTi1 WTi2 env1 env2.
    f_equal. apply functional_extensionality; intro x.
    apply (IHc_c (push_stack tt base) T1 T2 env1 env2
                 (denote_stack_push stk eq_refl x) glob AG t WTcc1 WTcc2).
  - destruct (type_cmd_read_var_inv _ _ _ _ WT1) as (NTH & ->).
    rewrite (denote_cmd_read_var WT1 (env1, stk, glob) NTH).
    rewrite (denote_cmd_read_var WT2 (env2, stk, glob) NTH).
    cbn [fst snd]. reflexivity.
  - destruct (type_cmd_write_var_inv _ _ _ _ _ WT1) as (WTval1 & NTH & ->).
    destruct (type_cmd_write_var_inv _ _ _ _ _ WT2) as (WTval2 & _ & _).
    rewrite (denote_cmd_write_var WT1 (env1, stk, glob) WTval1 NTH).
    rewrite (denote_cmd_write_var WT2 (env2, stk, glob) WTval2 NTH).
    cbn [fst snd].
    frame_e AG e_v t_v WTval1 WTval2 env1 env2. reflexivity.
  - destruct (type_cmd_alloc_ptr_inv _ _ _ _ _ WT1) as (( id_m & SR1 ) & WTs1 & WTi1 & ->).
    destruct (type_cmd_alloc_ptr_inv _ _ _ _ _ WT2) as (( id_m' & SR2 ) & WTs2 & WTi2 & _).
    rewrite (denote_cmd_alloc_ptr WT1 (env1, stk, glob) SR1 WTs1 WTi1).
    rewrite (denote_cmd_alloc_ptr WT2 (env2, stk, glob) SR2 WTs2 WTi2).
    cbn [fst snd].
    frame_e AG e_size t_ofst WTs1 WTs2 env1 env2.
    frame_e AG e_init t_init WTi1 WTi2 env1 env2. reflexivity.
  - destruct (type_cmd_read_ptr_inv _ _ _ _ WT1) as (WTp1 & ->).
    destruct (type_cmd_read_ptr_inv _ _ _ _ WT2) as (WTp2 & _).
    rewrite (denote_cmd_read_ptr WT1 (env1, stk, glob) WTp1).
    rewrite (denote_cmd_read_ptr WT2 (env2, stk, glob) WTp2).
    cbn [fst snd].
    frame_e AG e_ptr t_ptr WTp1 WTp2 env1 env2. reflexivity.
  - destruct (type_cmd_write_ptr_inv _ _ _ _ _ WT1) as (WTp1 & WTv1 & ->).
    destruct (type_cmd_write_ptr_inv _ _ _ _ _ WT2) as (WTp2 & WTv2 & _).
    rewrite (denote_cmd_write_ptr WT1 (env1, stk, glob) WTp1 WTv1).
    rewrite (denote_cmd_write_ptr WT2 (env2, stk, glob) WTp2 WTv2).
    cbn [fst snd].
    frame_e AG e_ptr t_ptr WTp1 WTp2 env1 env2.
    frame_e AG e_val t_val WTv1 WTv2 env1 env2. reflexivity.
  - destruct (type_cmd_free_ptr_inv _ _ _ WT1) as (( id_f & SR1 ) & WTp1 & ->).
    destruct (type_cmd_free_ptr_inv _ _ _ WT2) as (( id_f' & SR2 ) & WTp2 & _).
    rewrite (denote_cmd_free_ptr WT1 (env1, stk, glob) SR1 WTp1).
    rewrite (denote_cmd_free_ptr WT2 (env2, stk, glob) SR2 WTp2).
    cbn [fst snd].
    frame_e AG e_ptr t_ptr WTp1 WTp2 env1 env2. reflexivity.
  - destruct (type_cmd_shift_fw_ptr_inv _ _ _ _ WT1) as (WTp1 & WTo1 & ->).
    destruct (type_cmd_shift_fw_ptr_inv _ _ _ _ WT2) as (WTp2 & WTo2 & _).
    rewrite (denote_cmd_shift_fw_ptr WT1 (env1, stk, glob) WTp1 WTo1).
    rewrite (denote_cmd_shift_fw_ptr WT2 (env2, stk, glob) WTp2 WTo2).
    cbn [fst snd].
    frame_e AG e_ptr t_ptr WTp1 WTp2 env1 env2.
    frame_e AG e_shift t_ofst WTo1 WTo2 env1 env2. reflexivity.
  - destruct (type_cmd_shift_bw_ptr_inv _ _ _ _ WT1) as (WTp1 & WTo1 & ->).
    destruct (type_cmd_shift_bw_ptr_inv _ _ _ _ WT2) as (WTp2 & WTo2 & _).
    rewrite (denote_cmd_shift_bw_ptr WT1 (env1, stk, glob) WTp1 WTo1).
    rewrite (denote_cmd_shift_bw_ptr WT2 (env2, stk, glob) WTp2 WTo2).
    cbn [fst snd].
    frame_e AG e_ptr t_ptr WTp1 WTp2 env1 env2.
    frame_e AG e_shift t_ofst WTo1 WTo2 env1 env2. reflexivity.
  - destruct (type_cmd_ptr_eq_inv _ _ _ _ WT1) as (WTl1 & WTr1 & ->).
    destruct (type_cmd_ptr_eq_inv _ _ _ _ WT2) as (WTl2 & WTr2 & _).
    rewrite (denote_cmd_ptr_eq WT1 (env1, stk, glob) WTl1 WTr1).
    rewrite (denote_cmd_ptr_eq WT2 (env2, stk, glob) WTl2 WTr2).
    cbn [fst snd].
    frame_e AG e_l t_ptr WTl1 WTl2 env1 env2.
    frame_e AG e_r t_ptr WTr1 WTr2 env1 env2. reflexivity.
  - destruct (type_cmd_app_inv _ _ _ _ WT1)
      as [(fn & ta1 & FIND1 & MAP1 & F21 & ->)
         | (ef & sig & ta1 & FIND1 & MAP1 & DEC1 & F21 & ->)];
    destruct (type_cmd_app_inv _ _ _ _ WT2)
      as [(fn2 & ta2 & FIND2 & MAP2 & F22 & R2)
         | (ef2 & sig2 & ta2 & FIND2 & MAP2 & DEC2 & F22 & R2)].
    + assert (fn2 = fn) as ->.
      { pose proof (eq_trans (eq_sym FIND1) FIND2) as EQFIND. congruence. }
      rewrite (denote_cmd_app_internal WT1 (env1, stk, glob) FIND1 MAP1 F21).
      rewrite (denote_cmd_app_internal WT2 (env2, stk, glob) FIND2 MAP2 F22).
      cbn [fst snd].
      rewrite (genv_fn_lookup_frame base T1 T2 f_id fn glob FIND1 FIND2).
      apply (denote_app_frame args (ctx1 := with_pure T1 base)
               (ctx2 := with_pure T2 base) _ env1 env2 AG).
    + exfalso. pose proof (eq_trans (eq_sym FIND1) FIND2) as EQFIND; discriminate EQFIND.
    + exfalso. pose proof (eq_trans (eq_sym FIND1) FIND2) as EQFIND; discriminate EQFIND.
    + assert (ef2 = ef) as ->.
      { pose proof (eq_trans (eq_sym FIND1) FIND2) as EQFIND. congruence. }
      assert (sig2 = sig) as -> by congruence.
      rewrite (denote_cmd_app_external WT1 (env1, stk, glob) FIND1 DEC1 MAP1 F21).
      rewrite (denote_cmd_app_external WT2 (env2, stk, glob) FIND2 DEC2 MAP2 F22).
      cbn [fst snd].
      apply (denote_app_exf_frame base T1 T2 f_id args ef sig env1 env2 stk glob
               AG FIND1 FIND2 DEC1 DEC2).
  - destruct (type_cmd_div_inv _ _ _ _ WT1) as (WTl1 & WTr1 & ->).
    destruct (type_cmd_div_inv _ _ _ _ WT2) as (WTl2 & WTr2 & _).
    rewrite (denote_cmd_div WT1 (env1, stk, glob) WTl1 WTr1).
    rewrite (denote_cmd_div WT2 (env2, stk, glob) WTl2 WTr2).
    cbn [fst snd].
    frame_e AG e_l t_nat WTl1 WTl2 env1 env2.
    frame_e AG e_r t_nat WTr1 WTr2 env1 env2. reflexivity.
  - destruct (type_cmd_mod_inv _ _ _ _ WT1) as (WTl1 & WTr1 & ->).
    destruct (type_cmd_mod_inv _ _ _ _ WT2) as (WTl2 & WTr2 & _).
    rewrite (denote_cmd_mod WT1 (env1, stk, glob) WTl1 WTr1).
    rewrite (denote_cmd_mod WT2 (env2, stk, glob) WTl2 WTr2).
    cbn [fst snd].
    frame_e AG e_l t_nat WTl1 WTl2 env1 env2.
    frame_e AG e_r t_nat WTr1 WTr2 env1 env2. reflexivity.
Qed.

Definition type_agree (T1 T2: Maps.PTree.t (type * bool)) : Prop :=
  forall id t1 t2,
    Maps.PTree.get id T1 = Some (t1, true) ->
    Maps.PTree.get id T2 = Some (t2, true) -> t1 = t2.

Lemma type_agree_set (T1 T2: Maps.PTree.t (type * bool)) (TA: type_agree T1 T2)
  id t :
  type_agree (Maps.PTree.set id (t, true) T1) (Maps.PTree.set id (t, true) T2).
Proof using Type.
  intros id0 t1 t2 G1 G2.
  destruct (Pos.eq_dec id0 id) as [->|NE].
  - rewrite Maps.PTree.gss in G1. rewrite Maps.PTree.gss in G2. congruence.
  - rewrite (Maps.PTree.gso _ _ NE) in G1. rewrite (Maps.PTree.gso _ _ NE) in G2. exact (TA _ _ _ G1 G2).
Qed.

Lemma type_agree_unset (T1 T2: Maps.PTree.t (type * bool)) (TA: type_agree T1 T2)
  id t :
  type_agree (Maps.PTree.set id (t, false) T1) (Maps.PTree.set id (t, false) T2).
Proof using Type.
  intros id0 t1 t2 G1 G2.
  destruct (Pos.eq_dec id0 id) as [->|NE].
  - rewrite Maps.PTree.gss in G1. discriminate G1.
  - rewrite (Maps.PTree.gso _ _ NE) in G1. rewrite (Maps.PTree.gso _ _ NE) in G2. exact (TA _ _ _ G1 G2).
Qed.

Lemma type_agree_self (T: Maps.PTree.t (type * bool)) id t
  (GET: Maps.PTree.get id T = Some (t, false)) :
  type_agree T (Maps.PTree.set id (t, true) T).
Proof using Type.
  intros id0 s1 s2 G1 G2.
  destruct (Pos.eq_dec id0 id) as [->|NE].
  - rewrite GET in G1; discriminate G1.
  - rewrite (Maps.PTree.gso _ _ NE) in G2. congruence.
Qed.

Lemma type_expr_det (T1 T2: Maps.PTree.t (type * bool)) (TA: type_agree T1 T2) e :
  forall t1 t2, type_expr T1 e = Some t1 -> type_expr T2 e = Some t2 -> t1 = t2.
Proof using Type.
  induction e; intros t1 t2 H1 H2.
  - exact (TA _ _ _ (type_expr_var_inv _ _ _ H1) (type_expr_var_inv _ _ _ H2)).
  - cbn in H1, H2; congruence.
  - cbn in H1, H2; congruence.
  - cbn in H1, H2; destruct (Z.leb _ _) in H1; destruct (Z.leb _ _) in H2; congruence.
  - cbn in H1, H2; destruct (Z.leb _ _) in H1; destruct (Z.leb _ _) in H2; congruence.
  - cbn in H1, H2; congruence.
  - destruct (type_expr_neg_inv _ _ _ H1) as [_ ->];
      destruct (type_expr_neg_inv _ _ _ H2) as [_ ->]; reflexivity.
  - destruct (type_expr_add_inv _ _ _ _ H1) as (_ & _ & ->);
      destruct (type_expr_add_inv _ _ _ _ H2) as (_ & _ & ->); reflexivity.
  - destruct (type_expr_mul_inv _ _ _ _ H1) as (_ & _ & ->);
      destruct (type_expr_mul_inv _ _ _ _ H2) as (_ & _ & ->); reflexivity.
  - destruct (type_expr_eqb_inv _ _ _ _ H1) as (_ & _ & ->);
      destruct (type_expr_eqb_inv _ _ _ _ H2) as (_ & _ & ->); reflexivity.
Qed.

Lemma type_cmd_det (c: cmd) :
  forall (base: ctxt (type * bool) (type * bool) unit fundef vardef)
         (T1 T2: Maps.PTree.t (type * bool)) (TA: type_agree T1 T2) t1 t2,
    type_cmd (with_pure T1 base) c = Some t1 ->
    type_cmd (with_pure T2 base) c = Some t2 -> t1 = t2.
Proof using Type.
  induction c as
    [ e
    | id_b t_b c_b IHc_b c_c IHc_c
    | e_if c_then IHc_then c_else IHc_else
    | c_cond IHc_cond c_body IHc_body
    | t_v e_v c_c IHc_c
    | o_v t_v
    | o_v t_v e_v
    | e_size t_init e_init
    | e_ptr t_val
    | e_ptr t_val e_val
    | e_ptr
    | e_ptr e_shift
    | e_ptr e_shift
    | e_l e_r
    | f_id args
    | e_l e_r
    | e_l e_r ];
    intros base T1 T2 TA t1 t2 H1 H2.
  - cbn [type_cmd] in H1, H2. exact (type_expr_det T1 T2 TA e t1 t2 H1 H2).
  - destruct (type_cmd_bind_inv _ _ _ _ _ _ H1) as (_ & _ & WTcc1).
    destruct (type_cmd_bind_inv _ _ _ _ _ _ H2) as (_ & _ & WTcc2).
    exact (IHc_c base (Maps.PTree.set id_b (t_b, true) T1)
             (Maps.PTree.set id_b (t_b, true) T2)
             (type_agree_set T1 T2 TA id_b t_b) t1 t2 WTcc1 WTcc2).
  - destruct (type_cmd_if_inv _ _ _ _ _ H1) as (_ & WTt1 & _ & _ & _).
    destruct (type_cmd_if_inv _ _ _ _ _ H2) as (_ & WTt2 & _ & _ & _).
    exact (IHc_then base T1 T2 TA t1 t2 WTt1 WTt2).
  - destruct (type_cmd_while_inv _ _ _ _ H1) as (_ & _ & ->).
    destruct (type_cmd_while_inv _ _ _ _ H2) as (_ & _ & ->). reflexivity.
  - destruct (type_cmd_with_var_inv _ _ _ _ _ H1) as (_ & WTcc1).
    destruct (type_cmd_with_var_inv _ _ _ _ _ H2) as (_ & WTcc2).
    exact (IHc_c (push_stack tt base) T1 T2 TA t1 t2 WTcc1 WTcc2).
  - destruct (type_cmd_read_var_inv _ _ _ _ H1) as (_ & ->).
    destruct (type_cmd_read_var_inv _ _ _ _ H2) as (_ & ->). reflexivity.
  - destruct (type_cmd_write_var_inv _ _ _ _ _ H1) as (_ & _ & ->).
    destruct (type_cmd_write_var_inv _ _ _ _ _ H2) as (_ & _ & ->). reflexivity.
  - destruct (type_cmd_alloc_ptr_inv _ _ _ _ _ H1) as (_ & _ & _ & ->).
    destruct (type_cmd_alloc_ptr_inv _ _ _ _ _ H2) as (_ & _ & _ & ->). reflexivity.
  - destruct (type_cmd_read_ptr_inv _ _ _ _ H1) as (_ & ->).
    destruct (type_cmd_read_ptr_inv _ _ _ _ H2) as (_ & ->). reflexivity.
  - destruct (type_cmd_write_ptr_inv _ _ _ _ _ H1) as (_ & _ & ->).
    destruct (type_cmd_write_ptr_inv _ _ _ _ _ H2) as (_ & _ & ->). reflexivity.
  - destruct (type_cmd_free_ptr_inv _ _ _ H1) as (_ & _ & ->).
    destruct (type_cmd_free_ptr_inv _ _ _ H2) as (_ & _ & ->). reflexivity.
  - destruct (type_cmd_shift_fw_ptr_inv _ _ _ _ H1) as (_ & _ & ->).
    destruct (type_cmd_shift_fw_ptr_inv _ _ _ _ H2) as (_ & _ & ->). reflexivity.
  - destruct (type_cmd_shift_bw_ptr_inv _ _ _ _ H1) as (_ & _ & ->).
    destruct (type_cmd_shift_bw_ptr_inv _ _ _ _ H2) as (_ & _ & ->). reflexivity.
  - destruct (type_cmd_ptr_eq_inv _ _ _ _ H1) as (_ & _ & ->).
    destruct (type_cmd_ptr_eq_inv _ _ _ _ H2) as (_ & _ & ->). reflexivity.
  - destruct (type_cmd_app_inv _ _ _ _ H1)
      as [(fn & _ & FIND1 & _ & _ & ->) | (ef & sig & _ & FIND1 & _ & DEC1 & _ & ->)];
    destruct (type_cmd_app_inv _ _ _ _ H2)
      as [(fn2 & _ & FIND2 & _ & _ & ->) | (ef2 & sig2 & _ & FIND2 & _ & DEC2 & _ & ->)].
    + pose proof (eq_trans (eq_sym FIND1) FIND2) as EQFIND. congruence.
    + exfalso. pose proof (eq_trans (eq_sym FIND1) FIND2) as EQFIND; discriminate EQFIND.
    + exfalso. pose proof (eq_trans (eq_sym FIND1) FIND2) as EQFIND; discriminate EQFIND.
    + pose proof (eq_trans (eq_sym FIND1) FIND2) as EQFIND.
      assert (ef2 = ef) as -> by congruence.
      assert (sig2 = sig) as -> by congruence. reflexivity.
  - destruct (type_cmd_div_inv _ _ _ _ H1) as (_ & _ & ->).
    destruct (type_cmd_div_inv _ _ _ _ H2) as (_ & _ & ->). reflexivity.
  - destruct (type_cmd_mod_inv _ _ _ _ H1) as (_ & _ & ->).
    destruct (type_cmd_mod_inv _ _ _ _ H2) as (_ & _ & ->). reflexivity.
Qed.

Lemma type_cont_Kcall_inv ctx fn e locals (k': @OpSem.cont Sm) t :
  OpSem.Typing.type_cont ctx (OpSem.Kcall fn e locals k') = Some t ->
  type_function (to_glob_ctxt ctx) fn = true /\
  exists tye, OpSem.Typing.type_env fn e = Some tye /\
    OpSem.Typing.type_cont
      (with_internal (mk_typing_tree false fn.(fn_internals) Maps.PTree.Empty) (with_pure tye (with_stack (List.map (fun _ => tt) locals) ctx))) k' = Some t.
Proof using Type.
  cbn [OpSem.Typing.type_cont]. intro H.
  destruct (ctxt_stack ctx) as [|s0 sl0] eqn:Estk; [|discriminate].
  destruct (type_function (to_glob_ctxt ctx) fn) eqn:TF;
    [|discriminate].
  destruct (OpSem.Typing.type_env fn e) as [tye|] eqn:TE; [|discriminate].
  eauto.
Qed.

Lemma denote_cont_frame (k: cont) :
  forall (base: ctxt (type * bool) (type * bool) unit fundef vardef)
         (T1 T2: Maps.PTree.t (type * bool))
         (env1: denote_tree denote_binding T1)
         (env2: denote_tree denote_binding T2)
         (stk: denote_stack_ctxt Sm base)
         (glob: denote_glob_ctxt Sm base)
         (TA: type_agree T1 T2)
         (AG: pure_agree T1 T2 env1 env2)
         t (WT1: OpSem.Typing.type_cont (with_pure T1 base) k = Some t)
           (WT2: OpSem.Typing.type_cont (with_pure T2 base) k = Some t)
         (v: denote_type t),
  denote_cont WT1 env1 stk glob v = denote_cont WT2 env2 stk glob v.
Proof using Type.
  induction k as
    [ | id c k' IHk | c_cond c_body k' IHk | c_cond c_body k' IHk | fn e locals k' IHk
    | sx2 k2 IHk ];
    intros base T1 T2 env1 env2 stk glob TA AG t WT1 WT2 v.
  - assert (t = t_nat) as ->.
    { cbn [OpSem.Typing.type_cont] in WT1.
      destruct (ctxt_stack (with_pure T1 base)); [congruence | discriminate WT1]. }
    rewrite (denote_cont_Kstop WT1 env1 stk glob v).
    rewrite (denote_cont_Kstop WT2 env2 stk glob v). reflexivity.
  - destruct (type_cont_kbind_inv _ _ _ _ _ WT1) as (GET1 & t_c1 & WTc1 & WTk1).
    destruct (type_cont_kbind_inv _ _ _ _ _ WT2) as (GET2 & t_c2 & WTc2 & WTk2).
    assert (t_c1 = t_c2) as ->.
    { exact (type_cmd_det c base (Maps.PTree.set id (t, true) T1)
               (Maps.PTree.set id (t, true) T2)
               (type_agree_set T1 T2 TA id t) t_c1 t_c2 WTc1 WTc2). }
    rewrite (denote_cont_kbind WT1 env1 stk glob v GET1 t_c2 WTc1 WTk1).
    rewrite (denote_cont_kbind WT2 env2 stk glob v GET2 t_c2 WTc2 WTk2).
    f_equal.
    + apply (denote_cmd_frame c base (Maps.PTree.set id (t, true) T1)
               (Maps.PTree.set id (t, true) T2)
               (denote_tree_set id (denote_binding_eq t) v env1)
               (denote_tree_set id (denote_binding_eq t) v env2)
               stk glob (pure_agree_set AG id t v) t_c2 WTc1 WTc2).
    + apply functional_extensionality; intro v'.
      apply (IHk base T1 T2 env1 env2 stk glob TA AG t_c2 WTk1 WTk2 v').
  - destruct (type_cont_Kloop1_inv _ _ _ _ _ WT1) as (WTcond1 & WTbody1 & WTk1 & ->).
    destruct (type_cont_Kloop1_inv _ _ _ _ _ WT2) as (WTcond2 & WTbody2 & WTk2 & _).
    rewrite (denote_cont_Kloop1 WT1 env1 stk glob v WTcond1 WTbody1 WTk1).
    rewrite (denote_cont_Kloop1 WT2 env2 stk glob v WTcond2 WTbody2 WTk2).
    destruct v;
      repeat first
        [ apply (denote_cmd_frame c_cond base T1 T2 env1 env2 stk glob AG t_bool WTcond1 WTcond2)
        | apply (denote_cmd_frame c_body base T1 T2 env1 env2 stk glob AG t_unit WTbody1 WTbody2)
        | apply (IHk base T1 T2 env1 env2 stk glob TA AG t_unit WTk1 WTk2 tt)
        | (apply functional_extensionality; intro)
        | reflexivity
        | f_equal ].
  - destruct (type_cont_Kloop2_inv _ _ _ _ _ WT1) as (WTcond1 & WTbody1 & WTk1 & ->).
    destruct (type_cont_Kloop2_inv _ _ _ _ _ WT2) as (WTcond2 & WTbody2 & WTk2 & _).
    rewrite (denote_cont_Kloop2 WT1 env1 stk glob v WTcond1 WTbody1 WTk1).
    rewrite (denote_cont_Kloop2 WT2 env2 stk glob v WTcond2 WTbody2 WTk2).
    repeat first
      [ apply (denote_cmd_frame c_cond base T1 T2 env1 env2 stk glob AG t_bool WTcond1 WTcond2)
      | apply (denote_cmd_frame c_body base T1 T2 env1 env2 stk glob AG t_unit WTbody1 WTbody2)
      | apply (IHk base T1 T2 env1 env2 stk glob TA AG t_unit WTk1 WTk2 tt)
      | (apply functional_extensionality; intro)
      | reflexivity
      | f_equal ].
  - destruct (type_cont_Kcall_inv _ _ _ _ _ _ WT1) as (TF1 & tye1 & TE1 & WTk1).
    destruct (type_cont_Kcall_inv _ _ _ _ _ _ WT2) as (TF2 & tye2 & TE2 & WTk2).
    rewrite (denote_cont_Kcall WT1 env1 stk glob v TF1 TE1 WTk1).
    rewrite (denote_cont_Kcall WT2 env2 stk glob v TF2 TE2 WTk2).
    assert (tye2 = tye1) as -> by congruence.
    assert (TE2 = TE1) as ->
      by (apply (UIP_dec (ReflectExt.sumbool_of_reflect (@eqb_spec (option (Maps.PTree.t (type * bool))))))).
    apply denote_cont_pirr.
  - destruct sx2 as [id2 | ].
    + destruct (type_cont_Kscope_unbind_inv _ _ _ _ WT1) as (t_b1 & GET1 & WTk1).
      destruct (type_cont_Kscope_unbind_inv _ _ _ _ WT2) as (t_b2 & GET2 & WTk2).
      assert (t_b1 = t_b2) by (exact (TA id2 t_b1 t_b2 GET1 GET2)).
      subst t_b2.
      rewrite (denote_cont_Kscope_unbind WT1 env1 stk glob v t_b1 GET1 WTk1).
      rewrite (denote_cont_Kscope_unbind WT2 env2 stk glob v t_b1 GET2 WTk2).
      apply (IHk base (Maps.PTree.set id2 (t_b1, false) T1) (Maps.PTree.set id2 (t_b1, false) T2)
               (denote_tree_unset id2 (denote_binding_false_eq t_b1) env1)
               (denote_tree_unset id2 (denote_binding_false_eq t_b1) env2)
               stk glob (type_agree_unset T1 T2 TA id2 t_b1) (pure_agree_unset AG id2 t_b1)
               t WTk1 WTk2 v).
    + destruct (type_cont_Kscope_pop_inv _ _ _ WT1) as (s01 & sl01 & STK1 & WTk1).
      destruct (type_cont_Kscope_pop_inv _ _ _ WT2) as (s02 & sl02 & STK2 & WTk2).
      rewrite (denote_cont_Kscope_pop WT1 env1 stk glob v s01 sl01 STK1 WTk1).
      rewrite (denote_cont_Kscope_pop WT2 env2 stk glob v s02 sl02 STK2 WTk2).
      apply bind_Proper; [reflexivity|]; intro s.
      destruct (pop (store s)); [|reflexivity].
      destruct (mk_state_opt _ _ _ _); [|reflexivity].
      apply bind_Proper; [reflexivity|]; intros _.
      apply (IHk (with_stack (removelast (ctxt_stack base)) base) T1 T2 env1 env2
               (denote_stack_removelast _ _ stk) glob TA AG t WTk1 WTk2 v).
Qed.

Lemma pure_agree_refl (T: Maps.PTree.t (type * bool))
  (env: denote_tree denote_binding T) : pure_agree T T env env.
Proof using Type.
  intros id t G1 G2.
  apply (denote_tree_lookup_pirr G1 G2).
Qed.

Definition glob_agree
  (G1 G2: Globalenvs.Genv.t fundef vardef)
  (glob1: denote_tree (denote_globdef) (Globalenvs.Genv.genv_defs G1))
  (glob2: denote_tree (denote_globdef) (Globalenvs.Genv.genv_defs G2)) : Prop :=
  (forall f_id b gd,
      Globalenvs.Genv.find_symbol G1 f_id = Some b ->
      Globalenvs.Genv.find_def G1 b = Some gd ->
      Globalenvs.Genv.find_symbol G2 f_id = Some b
      /\ Globalenvs.Genv.find_def G2 b = Some gd)
  /\ (forall b a a_d
        (Gd1: Maps.PTree.get b (Globalenvs.Genv.genv_defs G1) = Some a)
        (Gd2: Maps.PTree.get b (Globalenvs.Genv.genv_defs G2) = Some a)
        (D: denote_globdef a = Some a_d),
        denote_tree_lookup Gd1 D glob1 = denote_tree_lookup Gd2 D glob2).

Lemma glob_agree_get_global
  (base: ctxt (type * bool) (type * bool) unit fundef vardef)
  (G1 G2: Globalenvs.Genv.t fundef vardef)
  (glob1: denote_tree (denote_globdef) (Globalenvs.Genv.genv_defs G1))
  (glob2: denote_tree (denote_globdef) (Globalenvs.Genv.genv_defs G2))
  (AG: glob_agree G1 G2 glob1 glob2) f_id gd :
  get_global f_id (with_global G1 base) = Some gd ->
  get_global f_id (with_global G2 base) = Some gd.
Proof using Type.
  destruct AG as [AGres _].
  unfold get_global; cbn [ctxt_global with_global].
  destruct (Globalenvs.Genv.find_symbol G1 f_id) as [b|] eqn:FS1; [ | discriminate ].
  intro FD1.
  destruct (AGres f_id b gd FS1 FD1) as [FS2 FD2].
  rewrite FS2. exact FD2.
Qed.

Lemma genv_fn_lookup_glob_agree
  (base: ctxt (type * bool) (type * bool) unit fundef vardef)
  (G1 G2: Globalenvs.Genv.t fundef vardef)
  (glob1: denote_tree (denote_globdef) (Globalenvs.Genv.genv_defs G1))
  (glob2: denote_tree (denote_globdef) (Globalenvs.Genv.genv_defs G2))
  (AG: glob_agree G1 G2 glob1 glob2)
  f_id fn
  (FIND1: get_global f_id (with_global G1 base) = Some (AST.Gfun (AST.Internal fn)))
  (FIND2: get_global f_id (with_global G2 base) = Some (AST.Gfun (AST.Internal fn))) :
  genv_fn_lookup (with_global G1 base) f_id fn glob1 FIND1
  = genv_fn_lookup (with_global G2 base) f_id fn glob2 FIND2.
Proof using Type.
  destruct AG as [AGres AGlk].
  unfold genv_fn_lookup, get_global in *.
  cbn [ctxt_global with_global] in *.
  revert FIND1 FIND2.
  destruct (Globalenvs.Genv.find_symbol G1 f_id) as [b1|] eqn:FS1;
    [ | intro FIND1; discriminate FIND1 ].
  intro FIND1.
  destruct (AGres f_id b1 (AST.Gfun (AST.Internal fn)) FS1 FIND1) as [FS2 FD2].
  rewrite FS2. intro FIND2.

  unfold Globalenvs.Genv.find_def in *.
  exact (AGlk b1 (AST.Gfun (AST.Internal fn)) (denote_fn_sig Sm fn) FIND1 FIND2 eq_refl).
Qed.

Lemma denote_app_exf_glob_agree
  (base: ctxt (type * bool) (type * bool) unit fundef vardef)
  (G1 G2: Globalenvs.Genv.t fundef vardef)
  (glob1: denote_tree (denote_globdef) (Globalenvs.Genv.genv_defs G1))
  (glob2: denote_tree (denote_globdef) (Globalenvs.Genv.genv_defs G2))
  (AG: glob_agree G1 G2 glob1 glob2)
  f_id args ef sig
  (env_p: denote_tree denote_binding (ctxt_pure base))
  (stk: denote_stack (denote_local) (ctxt_stack base))
  (FIND1: get_global f_id (with_global G1 base) = Some (AST.Gfun (AST.External ef)))
  (FIND2: get_global f_id (with_global G2 base) = Some (AST.Gfun (AST.External ef)))
  (DEC1 DEC2: Facts.ef_sig_dec ef = Some sig)
  (W1: ListExt.forall2b_opt type_eqb (type_expr (with_global G1 base).(ctxt_pure)) args sig.(sig_args) = true)
  (W2: ListExt.forall2b_opt type_eqb (type_expr (with_global G2 base).(ctxt_pure)) args sig.(sig_args) = true) :
  denote_app_exf FIND1 DEC1 W1 (env_p, stk, glob1)
  = denote_app_exf FIND2 DEC2 W2 (env_p, stk, glob2).
Proof using Type.
  destruct AG as [AGres AGlk].
  assert (DEC1 = DEC2) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec (option signature)))).
  unfold denote_app_exf.
  cbn [ctxt_global with_global ctxt_pure fst snd] in *.
  revert FIND1 FIND2.
  unfold get_global. cbn [ctxt_global with_global] in *.
  destruct (Globalenvs.Genv.find_symbol G1 f_id) as [b1|] eqn:FS1;
    [ | intro FIND1; discriminate FIND1 ].
  intro FIND1.
  destruct (AGres f_id b1 (AST.Gfun (AST.External ef)) FS1 FIND1) as [FS2 FD2].
  rewrite FS2. intro FIND2.

  unfold Globalenvs.Genv.find_def in *.
  erewrite (AGlk b1 (AST.Gfun (AST.External ef)) (denote_sig Sm sig) FIND1 FIND2).
  apply (denote_app_frame args (ctx1 := with_global G1 base) (ctx2 := with_global G2 base)
           _ env_p env_p (pure_agree_refl _ env_p)).
Qed.

Local Ltac glob_e e t W1 W2 ev :=
  replace (denote_expr W1 ev) with (denote_expr W2 ev) by
    (first [ apply (denote_expr_frame _ _ _ _ (pure_agree_refl _ ev) e t W1 W2)
           | symmetry; apply (denote_expr_frame _ _ _ _ (pure_agree_refl _ ev) e t W1 W2) ]).

Lemma denote_cmd_glob_frame (c: cmd) :
  forall (base: ctxt (type * bool) (type * bool) unit fundef vardef)
         (G1 G2: Globalenvs.Genv.t fundef vardef)
         (glob1: denote_tree (denote_globdef) (Globalenvs.Genv.genv_defs G1))
         (glob2: denote_tree (denote_globdef) (Globalenvs.Genv.genv_defs G2))
         (env: denote_tree denote_binding (ctxt_pure base))
         (stk: denote_stack (denote_local) (ctxt_stack base))
         (AG: glob_agree G1 G2 glob1 glob2)
         t (WT1: type_cmd (with_global G1 base) c = Some t)
           (WT2: type_cmd (with_global G2 base) c = Some t),
  denote_cmd WT1 (env, stk, glob1) = denote_cmd WT2 (env, stk, glob2).
Proof using Type.
  induction c as
    [ e
    | id_b t_b c_b IHc_b c_c IHc_c
    | e_if c_then IHc_then c_else IHc_else
    | c_cond IHc_cond c_body IHc_body
    | t_v e_v c_c IHc_c
    | o_v t_v
    | o_v t_v e_v
    | e_size t_init e_init
    | e_ptr t_val
    | e_ptr t_val e_val
    | e_ptr
    | e_ptr e_shift
    | e_ptr e_shift
    | e_l e_r
    | f_id args
    | e_l e_r
    | e_l e_r ];
    intros base G1 G2 glob1 glob2 env stk AG t WT1 WT2.
  - rewrite (denote_cmd_ret WT1 (env, stk, glob1) WT1).
    rewrite (denote_cmd_ret WT2 (env, stk, glob2) WT2).
    cbn [fst snd]. f_equal.
    apply (denote_expr_frame _ _ _ _ (pure_agree_refl _ env) e t WT1 WT2).
  - destruct (type_cmd_bind_inv _ _ _ _ _ _ WT1) as (GET1 & WTb1 & WTcc1).
    destruct (type_cmd_bind_inv _ _ _ _ _ _ WT2) as (GET2 & WTb2 & WTcc2).
    rewrite (denote_cmd_bind WT1 (env, stk, glob1) GET1 WTb1 WTcc1).
    rewrite (denote_cmd_bind WT2 (env, stk, glob2) GET2 WTb2 WTcc2).
    cbn [fst snd].
    rewrite (IHc_b base G1 G2 glob1 glob2 env stk AG t_b WTb1 WTb2).
    f_equal. apply functional_extensionality; intro v.
    apply (IHc_c (set_pure id_b (t_b, true) base) G1 G2 glob1 glob2
             (denote_tree_set id_b (denote_binding_eq t_b) v env) stk AG t WTcc1 WTcc2).
  - destruct (type_cmd_if_inv _ _ _ _ _ WT1) as (WTc1 & WTt1 & te1 & WTe1 & EQ1).
    destruct (type_cmd_if_inv _ _ _ _ _ WT2) as (WTc2 & WTt2 & te2 & WTe2 & EQ2).
    apply (reflect_eq_of_true type_eqb_spec) in EQ1; subst te1.
    apply (reflect_eq_of_true type_eqb_spec) in EQ2; subst te2.
    rewrite (denote_cmd_if WT1 (env, stk, glob1) WTc1 WTt1 WTe1).
    rewrite (denote_cmd_if WT2 (env, stk, glob2) WTc2 WTt2 WTe2).
    cbn [fst snd].
    glob_e e_if t_bool WTc1 WTc2 env.
    destruct (denote_expr WTc2 env).
    + apply (IHc_then base G1 G2 glob1 glob2 env stk AG t WTt1 WTt2).
    + apply (IHc_else base G1 G2 glob1 glob2 env stk AG t WTe1 WTe2).
  - destruct (type_cmd_while_inv _ _ _ _ WT1) as (WTcond1 & WTbody1 & ->).
    destruct (type_cmd_while_inv _ _ _ _ WT2) as (WTcond2 & WTbody2 & _).
    rewrite (denote_cmd_while WT1 (env, stk, glob1) WTcond1 WTbody1).
    rewrite (denote_cmd_while WT2 (env, stk, glob2) WTcond2 WTbody2).
    rewrite (IHc_cond base G1 G2 glob1 glob2 env stk AG t_bool WTcond1 WTcond2).
    rewrite (IHc_body base G1 G2 glob1 glob2 env stk AG t_unit WTbody1 WTbody2).
    reflexivity.
  - destruct (type_cmd_with_var_inv _ _ _ _ _ WT1) as (WTi1 & WTcc1).
    destruct (type_cmd_with_var_inv _ _ _ _ _ WT2) as (WTi2 & WTcc2).
    rewrite (denote_cmd_with_var WT1 (env, stk, glob1) WTi1 WTcc1).
    rewrite (denote_cmd_with_var WT2 (env, stk, glob2) WTi2 WTcc2).
    cbn [fst snd].
    glob_e e_v t_v WTi1 WTi2 env.
    f_equal. apply functional_extensionality; intro x.
    apply (IHc_c (push_stack tt base) G1 G2 glob1 glob2 env
             (denote_stack_push stk eq_refl x) AG t WTcc1 WTcc2).
  - destruct (type_cmd_read_var_inv _ _ _ _ WT1) as (NTH & ->).
    rewrite (denote_cmd_read_var WT1 (env, stk, glob1) NTH).
    rewrite (denote_cmd_read_var WT2 (env, stk, glob2) NTH).
    cbn [fst snd]. reflexivity.
  - destruct (type_cmd_write_var_inv _ _ _ _ _ WT1) as (WTval1 & NTH & ->).
    destruct (type_cmd_write_var_inv _ _ _ _ _ WT2) as (WTval2 & _ & _).
    rewrite (denote_cmd_write_var WT1 (env, stk, glob1) WTval1 NTH).
    rewrite (denote_cmd_write_var WT2 (env, stk, glob2) WTval2 NTH).
    cbn [fst snd]. glob_e e_v t_v WTval1 WTval2 env. reflexivity.
  - destruct (type_cmd_alloc_ptr_inv _ _ _ _ _ WT1) as (( id_m1 & SR1 ) & WTs1 & WTi1 & ->).
    destruct (type_cmd_alloc_ptr_inv _ _ _ _ _ WT2) as (( id_m2 & SR2 ) & WTs2 & WTi2 & _).
    rewrite (denote_cmd_alloc_ptr WT1 (env, stk, glob1) SR1 WTs1 WTi1).
    rewrite (denote_cmd_alloc_ptr WT2 (env, stk, glob2) SR2 WTs2 WTi2).
    cbn [fst snd].
    glob_e e_size t_ofst WTs1 WTs2 env.
    glob_e e_init t_init WTi1 WTi2 env. reflexivity.
  - destruct (type_cmd_read_ptr_inv _ _ _ _ WT1) as (WTp1 & ->).
    destruct (type_cmd_read_ptr_inv _ _ _ _ WT2) as (WTp2 & _).
    rewrite (denote_cmd_read_ptr WT1 (env, stk, glob1) WTp1).
    rewrite (denote_cmd_read_ptr WT2 (env, stk, glob2) WTp2).
    cbn [fst snd]. glob_e e_ptr t_ptr WTp1 WTp2 env. reflexivity.
  - destruct (type_cmd_write_ptr_inv _ _ _ _ _ WT1) as (WTp1 & WTv1 & ->).
    destruct (type_cmd_write_ptr_inv _ _ _ _ _ WT2) as (WTp2 & WTv2 & _).
    rewrite (denote_cmd_write_ptr WT1 (env, stk, glob1) WTp1 WTv1).
    rewrite (denote_cmd_write_ptr WT2 (env, stk, glob2) WTp2 WTv2).
    cbn [fst snd].
    glob_e e_ptr t_ptr WTp1 WTp2 env.
    glob_e e_val t_val WTv1 WTv2 env. reflexivity.
  - destruct (type_cmd_free_ptr_inv _ _ _ WT1) as (( id_f1 & SR1 ) & WTp1 & ->).
    destruct (type_cmd_free_ptr_inv _ _ _ WT2) as (( id_f2 & SR2 ) & WTp2 & _).
    rewrite (denote_cmd_free_ptr WT1 (env, stk, glob1) SR1 WTp1).
    rewrite (denote_cmd_free_ptr WT2 (env, stk, glob2) SR2 WTp2).
    cbn [fst snd]. glob_e e_ptr t_ptr WTp1 WTp2 env. reflexivity.
  - destruct (type_cmd_shift_fw_ptr_inv _ _ _ _ WT1) as (WTp1 & WTo1 & ->).
    destruct (type_cmd_shift_fw_ptr_inv _ _ _ _ WT2) as (WTp2 & WTo2 & _).
    rewrite (denote_cmd_shift_fw_ptr WT1 (env, stk, glob1) WTp1 WTo1).
    rewrite (denote_cmd_shift_fw_ptr WT2 (env, stk, glob2) WTp2 WTo2).
    cbn [fst snd].
    glob_e e_ptr t_ptr WTp1 WTp2 env.
    glob_e e_shift t_ofst WTo1 WTo2 env. reflexivity.
  - destruct (type_cmd_shift_bw_ptr_inv _ _ _ _ WT1) as (WTp1 & WTo1 & ->).
    destruct (type_cmd_shift_bw_ptr_inv _ _ _ _ WT2) as (WTp2 & WTo2 & _).
    rewrite (denote_cmd_shift_bw_ptr WT1 (env, stk, glob1) WTp1 WTo1).
    rewrite (denote_cmd_shift_bw_ptr WT2 (env, stk, glob2) WTp2 WTo2).
    cbn [fst snd].
    glob_e e_ptr t_ptr WTp1 WTp2 env.
    glob_e e_shift t_ofst WTo1 WTo2 env. reflexivity.
  - destruct (type_cmd_ptr_eq_inv _ _ _ _ WT1) as (WTl1 & WTr1 & ->).
    destruct (type_cmd_ptr_eq_inv _ _ _ _ WT2) as (WTl2 & WTr2 & _).
    rewrite (denote_cmd_ptr_eq WT1 (env, stk, glob1) WTl1 WTr1).
    rewrite (denote_cmd_ptr_eq WT2 (env, stk, glob2) WTl2 WTr2).
    cbn [fst snd].
    glob_e e_l t_ptr WTl1 WTl2 env.
    glob_e e_r t_ptr WTr1 WTr2 env. reflexivity.
  - destruct (type_cmd_app_inv _ _ _ _ WT1)
      as [(fn & ta1 & FIND1 & MAP1 & F21 & ->)
         | (ef & sig & ta1 & FIND1 & MAP1 & DEC1 & F21 & ->)];
    destruct (type_cmd_app_inv _ _ _ _ WT2)
      as [(fn2 & ta2 & FIND2 & MAP2 & F22 & R2)
         | (ef2 & sig2 & ta2 & FIND2 & MAP2 & DEC2 & F22 & R2)].
    + assert (fn2 = fn) as ->.
      { pose proof (glob_agree_get_global base G1 G2 glob1 glob2 AG f_id _ FIND1) as EQFIND.
        rewrite FIND2 in EQFIND. congruence. }
      rewrite (denote_cmd_app_internal WT1 (env, stk, glob1) FIND1 MAP1 F21).
      rewrite (denote_cmd_app_internal WT2 (env, stk, glob2) FIND2 MAP2 F22).
      cbn [fst snd].
      rewrite (genv_fn_lookup_glob_agree base G1 G2 glob1 glob2 AG f_id fn FIND1 FIND2).
      apply (denote_app_frame args (ctx1 := with_global G1 base)
               (ctx2 := with_global G2 base) _ env env (pure_agree_refl _ env)).
    + exfalso.
      pose proof (glob_agree_get_global base G1 G2 glob1 glob2 AG f_id _ FIND1) as EQFIND.
      rewrite FIND2 in EQFIND. discriminate EQFIND.
    + exfalso.
      pose proof (glob_agree_get_global base G1 G2 glob1 glob2 AG f_id _ FIND1) as EQFIND.
      rewrite FIND2 in EQFIND. discriminate EQFIND.
    + assert (ef2 = ef) as ->.
      { pose proof (glob_agree_get_global base G1 G2 glob1 glob2 AG f_id _ FIND1) as EQFIND.
        rewrite FIND2 in EQFIND. congruence. }
      assert (sig2 = sig) as -> by congruence.
      rewrite (denote_cmd_app_external WT1 (env, stk, glob1) FIND1 DEC1 MAP1 F21).
      rewrite (denote_cmd_app_external WT2 (env, stk, glob2) FIND2 DEC2 MAP2 F22).
      apply (denote_app_exf_glob_agree base G1 G2 glob1 glob2 AG
               f_id args ef sig env stk FIND1 FIND2 DEC1 DEC2).
  - destruct (type_cmd_div_inv _ _ _ _ WT1) as (WTl1 & WTr1 & ->).
    destruct (type_cmd_div_inv _ _ _ _ WT2) as (WTl2 & WTr2 & _).
    rewrite (denote_cmd_div WT1 (env, stk, glob1) WTl1 WTr1).
    rewrite (denote_cmd_div WT2 (env, stk, glob2) WTl2 WTr2).
    cbn [fst snd].
    glob_e e_l t_nat WTl1 WTl2 env.
    glob_e e_r t_nat WTr1 WTr2 env. reflexivity.
  - destruct (type_cmd_mod_inv _ _ _ _ WT1) as (WTl1 & WTr1 & ->).
    destruct (type_cmd_mod_inv _ _ _ _ WT2) as (WTl2 & WTr2 & _).
    rewrite (denote_cmd_mod WT1 (env, stk, glob1) WTl1 WTr1).
    rewrite (denote_cmd_mod WT2 (env, stk, glob2) WTl2 WTr2).
    cbn [fst snd].
    glob_e e_l t_nat WTl1 WTl2 env.
    glob_e e_r t_nat WTr1 WTr2 env. reflexivity.
Qed.

Lemma denote_function_curried_glob_frame
  (gctx1 gctx2: ctxt Empty_set Empty_set Empty_set fundef vardef)
  (glob1: denote_glob_ctxt Sm gctx1) (glob2: denote_glob_ctxt Sm gctx2)
  (AG: glob_agree (ctxt_global gctx1) (ctxt_global gctx2) glob1 glob2)
  (internal: Maps.PTree.t (type * bool))
  (params_todo: list (AST.ident * type)) :
  forall (done_tree: Maps.PTree.t (type * bool)) (body: cmd) (tout: type)
         (env: denote_tree denote_binding done_tree)
         (WTbody1: type_cmd
            (with_internal internal
               (with_pure (mk_typing_tree true params_todo done_tree)
                  (with_stack [] gctx1))) body = Some tout)
         (WTbody2: type_cmd
            (with_internal internal
               (with_pure (mk_typing_tree true params_todo done_tree)
                  (with_stack [] gctx2))) body = Some tout),
  denote_function_curried internal params_todo done_tree body tout env WTbody1 glob1
  = denote_function_curried internal params_todo done_tree body tout env WTbody2 glob2.
Proof using Type.
  induction params_todo as [| [id t] rest IH];
    intros done_tree body tout env WTbody1 WTbody2.
  - cbn [denote_function_curried].
    apply (denote_cmd_glob_frame body
             (with_internal internal (with_pure done_tree (with_stack [] gctx1)))
             (ctxt_global gctx1) (ctxt_global gctx2) glob1 glob2 env tt AG tout
             WTbody1 WTbody2).
  - cbn [denote_function_curried].
    apply functional_extensionality; intro x.
    apply (IH (Maps.PTree.set id (t, true) done_tree) body tout
             (denote_tree_set id (denote_binding_eq t) x env) WTbody1 WTbody2).
Qed.

Lemma denote_function_incl_global
  (gctx1 gctx2: ctxt Empty_set Empty_set Empty_set fundef vardef) (fn: function)
  (WT1: type_function gctx1 fn = true) (WT2: type_function gctx2 fn = true)
  (glob1: denote_glob_ctxt Sm gctx1) (glob2: denote_glob_ctxt Sm gctx2)
  (AG: glob_agree (ctxt_global gctx1) (ctxt_global gctx2) glob1 glob2) :
  denote_function WT1 glob1 = denote_function WT2 glob2.
Proof using Type.
  pose proof (type_cmd_complete (wt_fn_cmd (type_function_correct gctx1 fn WT1))) as WTbody1.
  pose proof (type_cmd_complete (wt_fn_cmd (type_function_correct gctx2 fn WT2))) as WTbody2.
  rewrite (denote_function_eq WT1 glob1 WTbody1 (type_env_Empty fn)).
  rewrite (denote_function_eq WT2 glob2 WTbody2 (type_env_Empty fn)).
  apply (denote_function_curried_glob_frame gctx1 gctx2 glob1 glob2 AG
           (mk_typing_tree false fn.(fn_internals) Maps.PTree.Empty)
           fn.(fn_params)
           (mk_typing_tree false (fn.(fn_params) ++ fn.(fn_temps)) Maps.PTree.Empty)
           fn.(fn_body) fn.(fn_return)
           (denote_env (type_env_Empty fn)) WTbody1 WTbody2).
Qed.

Lemma denote_globdef_value_pirr
  [ctx: ctxt Empty_set Empty_set Empty_set fundef vardef] [id gd]
  (H1 H2: type_globdef ctx id gd = true) (glob: denote_glob_ctxt Sm ctx) :
  denote_globdef_value H1 glob = denote_globdef_value H2 glob.
Proof using Type. assert (H1 = H2) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec bool))). reflexivity. Qed.

Lemma denote_glob_ctxt_extend_pirr
  [ctx: ctxt Empty_set Empty_set Empty_set fundef vardef] [id gd]
  (H1 H2: type_globdef ctx id gd = true)
  (d_gd: match denote_globdef gd with Some d => d | None => Empty_set end)
  (glob: denote_tree (denote_globdef)
           (Globalenvs.Genv.genv_defs (ctxt_global ctx))) :
  denote_glob_ctxt_extend H1 d_gd glob = denote_glob_ctxt_extend H2 d_gd glob.
Proof using Type. assert (H1 = H2) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec bool))). reflexivity. Qed.

Lemma denote_prog_defs_fold_pirr
  (defs: list (AST.ident * globdef)) (ctx: ctxt Empty_set Empty_set Empty_set fundef vardef)
  (H1 H2: type_prog_defs ctx defs = true) (glob: denote_glob_ctxt Sm ctx) :
  denote_prog_defs_fold defs ctx H1 glob = denote_prog_defs_fold defs ctx H2 glob.
Proof using Type. assert (H1 = H2) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec bool))). reflexivity. Qed.

Lemma denote_prog_defs_fold_nil
  (ctx: ctxt Empty_set Empty_set Empty_set fundef vardef)
  (H: type_prog_defs ctx [] = true) (glob: denote_glob_ctxt Sm ctx) :
  denote_prog_defs_fold [] ctx H glob = glob.
Proof using Type. reflexivity. Qed.

Lemma denote_prog_defs_fold_cons
  id gd rest (ctx: ctxt Empty_set Empty_set Empty_set fundef vardef)
  (H: type_prog_defs ctx ((id, gd) :: rest) = true)
  (WTGD: type_globdef ctx id gd = true)
  (H': type_prog_defs (add_global ctx (id, gd)) rest = true)
  (glob: denote_glob_ctxt Sm ctx) :
  denote_prog_defs_fold ((id, gd) :: rest) ctx H glob
  = denote_prog_defs_fold rest (add_global ctx (id, gd)) H'
      (denote_glob_ctxt_extend WTGD (denote_globdef_value WTGD glob) glob).
Proof using Type.
  cbn [denote_prog_defs_fold].
  erewrite (conv_bool_app WTGD H).
  erewrite (denote_prog_defs_fold_pirr rest (add_global ctx (id, gd)) _ H').
  reflexivity.
Qed.

Lemma denote_glob_ctxt_extend_lookup_other
  [ctx: ctxt Empty_set Empty_set Empty_set fundef vardef] [id gd]
  (WTGD: type_globdef ctx id gd = true)
  (d_gd: match denote_globdef gd with Some d => d | None => Empty_set end)
  (glob: denote_tree (denote_globdef) (Globalenvs.Genv.genv_defs (ctxt_global ctx)))
  (b: positive) (a: globdef) (a_d: Type)
  (NEQ: b <> Globalenvs.Genv.genv_next (ctxt_global ctx))
  (D: denote_globdef a = Some a_d)
  (G': Maps.PTree.get b
         (Globalenvs.Genv.genv_defs (ctxt_global (add_global ctx (id, gd)))) = Some a)
  (G0: Maps.PTree.get b (Globalenvs.Genv.genv_defs (ctxt_global ctx)) = Some a) :
  denote_tree_lookup G' D (denote_glob_ctxt_extend WTGD d_gd glob)
  = denote_tree_lookup G0 D glob.
Proof using Type.
  unfold denote_glob_ctxt_extend, eq_rect_r, genv_defs_add_global; cbn [eq_rect eq_sym].
  destruct gd as [[fn|ef]|v]; cbn [denote_globdef] in *.
  - apply (denote_tree_lookup_set_other _ d_gd
             (Globalenvs.Genv.genv_defs (ctxt_global ctx))
             (Globalenvs.Genv.genv_next (ctxt_global ctx)) b (not_eq_sym NEQ) glob D G' G0).
  - assert (SIG: (exists s, Facts.ef_sig_dec ef = Some s) \/ Facts.ef_sig_dec ef = None).
    { destruct (Facts.ef_sig_dec ef) as [s|]; [ left; eauto | right; reflexivity ]. }
    destruct SIG as [ [s0 SIG] | SIG ].
    + erewrite (conv_option_app SIG).
      apply (denote_tree_lookup_set_other _ _
               (Globalenvs.Genv.genv_defs (ctxt_global ctx))
               (Globalenvs.Genv.genv_next (ctxt_global ctx)) b (not_eq_sym NEQ) glob D G' G0).
    + erewrite (conv_option_app_None SIG).
      apply (denote_tree_lookup_set_other _ _
               (Globalenvs.Genv.genv_defs (ctxt_global ctx))
               (Globalenvs.Genv.genv_next (ctxt_global ctx)) b (not_eq_sym NEQ) glob D G' G0).
  - destruct v as [[t] vinit vread vvol].
    apply (denote_tree_lookup_set_other _ _
             (Globalenvs.Genv.genv_defs (ctxt_global ctx))
             (Globalenvs.Genv.genv_next (ctxt_global ctx)) b (not_eq_sym NEQ) glob D G' G0).
Qed.

Lemma type_prog_defs_cons_inv (ctx: ctxt Empty_set Empty_set Empty_set fundef vardef) id gd rest :
  type_prog_defs ctx ((id, gd) :: rest) = true ->
  type_globdef ctx id gd = true
  /\ type_prog_defs (add_global ctx (id, gd)) rest = true.
Proof using Type.
  unfold type_prog_defs, Prog.type_prog_defs; cbn [ListExt.fold_left_b fst snd].
  intro AND. apply andb_prop in AND. exact AND.
Qed.

Lemma denote_prog_defs_fold_preserves
  (defs: list (AST.ident * globdef)) :
  forall (ctx: ctxt Empty_set Empty_set Empty_set fundef vardef)
         (H: type_prog_defs ctx defs = true)
         (glob: denote_glob_ctxt Sm ctx)
         (b: positive) (a: globdef) (a_d: Type)
         (D: denote_globdef a = Some a_d)
         (G0: Maps.PTree.get b (Globalenvs.Genv.genv_defs (ctxt_global ctx)) = Some a)
         (Gfin: Maps.PTree.get b
                  (Globalenvs.Genv.genv_defs
                     (List.fold_left (@Globalenvs.Genv.add_global fundef vardef) defs
                        (ctxt_global ctx))) = Some a),
  denote_tree_lookup Gfin D (denote_prog_defs_fold defs ctx H glob)
  = denote_tree_lookup G0 D glob.
Proof using Type.
  induction defs as [|[id gd] rest IH]; intros ctx H glob b a a_d D G0 Gfin.
  - rewrite (denote_prog_defs_fold_nil ctx H glob).
    apply (denote_tree_lookup_pirr).
  - destruct (type_prog_defs_cons_inv ctx id gd rest H) as [WTGD H'].
    pose proof (denote_prog_defs_fold_cons id gd rest ctx H WTGD H' glob) as Erw.
    assert (NEQ: b <> Globalenvs.Genv.genv_next (ctxt_global ctx)).
    { intro EQ; subst b.
      eapply Coqlib.Plt_strict.
      eapply (Globalenvs.Genv.genv_defs_range (ctxt_global ctx)).
      exact G0. }
    assert (G0': Maps.PTree.get b
              (Globalenvs.Genv.genv_defs (ctxt_global (add_global ctx (id, gd)))) = Some a).
    { unfold add_global; cbn [ctxt_global with_global].
      rewrite (genv_defs_add_global _ _ (ctxt_global ctx) (id, gd)); cbn [snd].
      rewrite Maps.PTree.gso; first by congruence. exact G0. }
    transitivity (denote_tree_lookup Gfin D
                    (denote_prog_defs_fold rest (add_global ctx (id, gd)) H'
                       (denote_glob_ctxt_extend WTGD (denote_globdef_value WTGD glob) glob))).
    + exact (f_equal (denote_tree_lookup Gfin D) Erw).
    + transitivity (denote_tree_lookup G0' D
                      (denote_glob_ctxt_extend WTGD (denote_globdef_value WTGD glob) glob)).
      * exact (IH (add_global ctx (id, gd)) H'
                 (denote_glob_ctxt_extend WTGD (denote_globdef_value WTGD glob) glob)
                 b a a_d D G0' Gfin).
      * exact (denote_glob_ctxt_extend_lookup_other WTGD
                 (denote_globdef_value WTGD glob) glob b a a_d NEQ D G0' G0).
Qed.

Lemma denote_function_pirr
  [gctx: ctxt Empty_set Empty_set Empty_set fundef vardef] [fn: function]
  (W1 W2: type_function gctx fn = true) (glob: denote_glob_ctxt Sm gctx) :
  denote_function W1 glob = denote_function W2 glob.
Proof using Type. assert (W1 = W2) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec bool))). reflexivity. Qed.

Lemma denote_globdef_value_internal
  [ctx: ctxt Empty_set Empty_set Empty_set fundef vardef] [id fn]
  (WTGD: type_globdef ctx id (AST.Gfun (AST.Internal fn)) = true)
  (WTFN: type_function ctx fn = true)
  (glob: denote_glob_ctxt Sm ctx) :
  denote_globdef_value WTGD glob = denote_function WTFN glob.
Proof using Type.
  cbn [denote_globdef_value]. apply denote_function_pirr.
Qed.

Lemma denote_glob_ctxt_extend_lookup_internal
  [ctx: ctxt Empty_set Empty_set Empty_set fundef vardef] [id fn]
  (WTGD: type_globdef ctx id (AST.Gfun (AST.Internal fn)) = true)
  (glob: denote_glob_ctxt Sm ctx)
  (G: Maps.PTree.get (Globalenvs.Genv.genv_next (ctxt_global ctx))
        (Globalenvs.Genv.genv_defs (ctxt_global (add_global ctx (id, AST.Gfun (AST.Internal fn)))))
      = Some (AST.Gfun (AST.Internal fn))) :
  denote_tree_lookup G eq_refl
    (denote_glob_ctxt_extend WTGD (denote_globdef_value WTGD glob) glob)
  = denote_globdef_value WTGD glob.
Proof using Type.
  unfold denote_glob_ctxt_extend, eq_rect_r, genv_defs_add_global;
    cbn [eq_rect eq_sym denote_globdef].
  apply (denote_tree_lookup_set_same).
Qed.

Lemma find_symbol_add_globals_pre (defs: list (AST.ident * globdef)) :
  forall (ge: Globalenvs.Genv.t fundef vardef) f bb,
    Globalenvs.Genv.find_symbol ge f = Some bb ->
    ~ List.In f (List.map fst defs) ->
    Globalenvs.Genv.find_symbol (Globalenvs.Genv.add_globals ge defs) f = Some bb.
Proof using Type.
  induction defs as [|[id g] rest IH]; intros ge f bb WTf NIN; cbn [Globalenvs.Genv.add_globals].
  - exact WTf.
  - apply IH.
    + unfold Globalenvs.Genv.find_symbol, Globalenvs.Genv.add_global; cbn.
      rewrite Maps.PTree.gso.
      * intro EQ; subst id; apply NIN; left; reflexivity.
      * exact WTf.
    + intro IN; apply NIN; right; exact IN.
Qed.

Lemma find_def_add_globals_pre (defs: list (AST.ident * globdef)) :
  forall (ge: Globalenvs.Genv.t fundef vardef) bb g,
    Globalenvs.Genv.find_def ge bb = Some g ->
    Globalenvs.Genv.find_def (Globalenvs.Genv.add_globals ge defs) bb = Some g.
Proof using Type.
  induction defs as [|[id gd] rest IH]; intros ge bb g BIT; cbn [Globalenvs.Genv.add_globals].
  - exact BIT.
  - apply IH.
    unfold Globalenvs.Genv.find_def, Globalenvs.Genv.add_global; cbn.
    rewrite Maps.PTree.gso.
    + intro EQ; subst bb.
      eapply Coqlib.Plt_strict.
      eapply Globalenvs.Genv.genv_defs_range. exact BIT.
    + exact BIT.
Qed.

Lemma glob_agree_fold
  (defs: list (AST.ident * globdef))
  (ctx0: ctxt Empty_set Empty_set Empty_set fundef vardef)
  (H: type_prog_defs ctx0 defs = true)
  (glob0: denote_glob_ctxt Sm ctx0)
  (DSJ: forall f bb, Globalenvs.Genv.find_symbol (ctxt_global ctx0) f = Some bb ->
                      ~ List.In f (List.map fst defs)) :
  glob_agree (ctxt_global ctx0)
             (Globalenvs.Genv.add_globals (ctxt_global ctx0) defs)
             glob0 (denote_prog_defs_fold defs ctx0 H glob0).
Proof using Type.
  split.
  - intros f_id b gd FS FD. split.
    + apply find_symbol_add_globals_pre. exact FS. exact (DSJ f_id b FS).
    + apply find_def_add_globals_pre. exact FD.
  - intros b a a_d Gd1 Gd2 D.
    symmetry.
    exact (denote_prog_defs_fold_preserves defs ctx0 H glob0 b a a_d D Gd1 Gd2).
Qed.

Lemma prog_defs_norepet (p: Prog.program) (WTp': type_program p = true) :
  Coqlib.list_norepet (List.map fst p.(prog_defs)).
Proof using Type.
  pose proof (proj2 (Bool.reflect_iff _ _ (type_program_spec p)) WTp') as WTp.
  exact (proj1 (ListExt.SBinds_list_norepet p.(prog_defs)) (Prog.wt_prog_defs_sbinds WTp)).
Qed.

Lemma glob_agree_refl
  (G: Globalenvs.Genv.t fundef vardef)
  (glob: denote_tree (denote_globdef) (Globalenvs.Genv.genv_defs G)) :
  glob_agree G G glob glob.
Proof using Type.
  split.
  - intros f_id b gd FS FD. split; assumption.
  - intros b a a_d Gd1 Gd2 D. apply (denote_tree_lookup_pirr).
Qed.

Lemma add_globals_cons F V (ge: Globalenvs.Genv.t F V) a l :
  Globalenvs.Genv.add_globals ge (a :: l)
  = Globalenvs.Genv.add_globals (Globalenvs.Genv.add_global ge a) l.
Proof using Type. reflexivity. Qed.

Lemma find_symbol_add_global_other F V (ge: Globalenvs.Genv.t F V) idg f bb :
  f <> fst idg ->
  Globalenvs.Genv.find_symbol (Globalenvs.Genv.add_global ge idg) f = Some bb ->
  Globalenvs.Genv.find_symbol ge f = Some bb.
Proof using Type.
  intros NE.
  unfold Globalenvs.Genv.find_symbol, Globalenvs.Genv.add_global; cbn [Globalenvs.Genv.genv_symb].
  rewrite Maps.PTree.gso; first by congruence. exact (fun H => H).
Qed.

Lemma denote_prog_defs_fold_lookup_internal
  (defs: list (AST.ident * globdef)) :
  forall (ctx0: ctxt Empty_set Empty_set Empty_set fundef vardef)
         (H: type_prog_defs ctx0 defs = true)
         (glob0: denote_glob_ctxt Sm ctx0)
         (NOREP: Coqlib.list_norepet (List.map fst defs))
         (DSJ0: forall f bb, Globalenvs.Genv.find_symbol (ctxt_global ctx0) f = Some bb ->
                              ~ List.In f (List.map fst defs))
         (b: positive) (fn: function)
         (G0none: Maps.PTree.get b (Globalenvs.Genv.genv_defs (ctxt_global ctx0)) = None)
         (WTFN: type_function
                 (with_global (Globalenvs.Genv.add_globals (ctxt_global ctx0) defs) ctx0) fn = true)
         (Gfin: Maps.PTree.get b
                  (Globalenvs.Genv.genv_defs (Globalenvs.Genv.add_globals (ctxt_global ctx0) defs))
                = Some (AST.Gfun (AST.Internal fn))),
  denote_tree_lookup Gfin eq_refl (denote_prog_defs_fold defs ctx0 H glob0)
  = denote_function WTFN (denote_prog_defs_fold defs ctx0 H glob0).
Proof using Type.
  induction defs as [|[id gd] rest IH];
    intros ctx0 H glob0 NOREP DSJ0 b fn G0none WTFN Gfin.
  - exfalso. cbn [Globalenvs.Genv.add_globals List.fold_left] in Gfin. congruence.
  - destruct (type_prog_defs_cons_inv ctx0 id gd rest H) as [WTGD H'].
    pose proof (denote_prog_defs_fold_cons id gd rest ctx0 H WTGD H' glob0) as Erw.
    inversion NOREP as [|x0 l0 NOTIN REST [Ex0 El0]]; subst x0 l0.
    destruct (Coqlib.peq b (Globalenvs.Genv.genv_next (ctxt_global ctx0))) as [Eb | NEb].
    + subst b.
      assert (G0'b : Maps.PTree.get (Globalenvs.Genv.genv_next (ctxt_global ctx0))
                       (Globalenvs.Genv.genv_defs (ctxt_global (add_global ctx0 (id, gd)))) = Some gd).
      { unfold add_global; cbn [ctxt_global with_global].
        rewrite (genv_defs_add_global _ _ (ctxt_global ctx0) (id, gd)); cbn [snd].
        apply Maps.PTree.gss. }
      assert (FINDDEF: Globalenvs.Genv.find_def
                    (Globalenvs.Genv.add_globals (ctxt_global ctx0) ((id, gd) :: rest))
                    (Globalenvs.Genv.genv_next (ctxt_global ctx0)) = Some gd).
      { rewrite add_globals_cons.
        apply (find_def_add_globals_pre rest (Globalenvs.Genv.add_global (ctxt_global ctx0) (id, gd))
                 (Globalenvs.Genv.genv_next (ctxt_global ctx0)) gd).
        exact G0'b. }
      unfold Globalenvs.Genv.find_def in FINDDEF.
      assert (Egd: gd = AST.Gfun (AST.Internal fn)) by congruence.
      subst gd.
      assert (WTFN0: type_function ctx0 fn = true) by exact WTGD.
      transitivity (denote_tree_lookup Gfin eq_refl
                      (denote_prog_defs_fold rest (add_global ctx0 (id, AST.Gfun (AST.Internal fn))) H'
                         (denote_glob_ctxt_extend WTGD
                            (denote_globdef_value WTGD glob0) glob0))).
      { exact (f_equal (denote_tree_lookup Gfin eq_refl) Erw). }
      transitivity (denote_tree_lookup G0'b eq_refl
                      (denote_glob_ctxt_extend WTGD (denote_globdef_value WTGD glob0) glob0)).
      { exact (denote_prog_defs_fold_preserves rest
                 (add_global ctx0 (id, AST.Gfun (AST.Internal fn))) H'
                 (denote_glob_ctxt_extend WTGD (denote_globdef_value WTGD glob0) glob0)
                 (Globalenvs.Genv.genv_next (ctxt_global ctx0))
                 (AST.Gfun (AST.Internal fn)) _ eq_refl G0'b Gfin). }
      transitivity (denote_globdef_value WTGD glob0).
      { exact (denote_glob_ctxt_extend_lookup_internal WTGD glob0 G0'b). }
      transitivity (denote_function WTFN0 glob0).
      { exact (denote_globdef_value_internal WTGD WTFN0 glob0). }
      exact (denote_function_incl_global ctx0
               (with_global (Globalenvs.Genv.add_globals (ctxt_global ctx0)
                               ((id, AST.Gfun (AST.Internal fn)) :: rest)) ctx0)
               fn WTFN0 WTFN glob0
               (denote_prog_defs_fold ((id, AST.Gfun (AST.Internal fn)) :: rest) ctx0 H glob0)
               (glob_agree_fold ((id, AST.Gfun (AST.Internal fn)) :: rest) ctx0 H glob0 DSJ0)).
    + set (ctx0' := add_global ctx0 (id, gd)) in *.
      set (glob1 := denote_glob_ctxt_extend WTGD (denote_globdef_value WTGD glob0) glob0) in *.
      assert (DSJ0': forall f bb, Globalenvs.Genv.find_symbol (ctxt_global ctx0') f = Some bb ->
                                   ~ List.In f (List.map fst rest)).
      { intros f bb FSf.
        destruct (Coqlib.peq f id) as [->|NE].
        - exact NOTIN.
        - unfold ctx0', add_global in FSf; cbn [ctxt_global with_global] in FSf.
          pose proof (find_symbol_add_global_other _ _ (ctxt_global ctx0) (id, gd) f bb NE FSf) as FS0.
          intro IN. apply (DSJ0 f bb FS0). cbn [List.map fst]. right; exact IN. }
      assert (G0none': Maps.PTree.get b (Globalenvs.Genv.genv_defs (ctxt_global ctx0')) = None).
      { unfold ctx0', add_global; cbn [ctxt_global with_global].
        rewrite (genv_defs_add_global _ _ (ctxt_global ctx0) (id, gd)); cbn [snd].
        rewrite Maps.PTree.gso; first by exact NEb. exact G0none. }
      transitivity (denote_tree_lookup Gfin eq_refl
                      (denote_prog_defs_fold rest ctx0' H' glob1)).
      { exact (f_equal (denote_tree_lookup Gfin eq_refl) Erw). }
      transitivity (denote_function WTFN (denote_prog_defs_fold rest ctx0' H' glob1)).
      { exact (IH ctx0' H' glob1 REST DSJ0' b fn G0none' WTFN Gfin). }
      exact (f_equal (denote_function WTFN) (eq_sym Erw)).
Qed.

Lemma denote_glob_ctxt_of_program_eq (p: Prog.program) (WTp: type_program p = true)
  (H0: type_prog_defs (ctxt_emp Empty_set Empty_set Empty_set fundef vardef p.(prog_public)) p.(prog_defs) = true) :
  @denote_glob_ctxt_of_program p WTp
  = denote_prog_defs_fold p.(prog_defs)
      (ctxt_emp Empty_set Empty_set Empty_set fundef vardef p.(prog_public)) H0 tt.
Proof using Type.
  unfold denote_glob_ctxt_of_program.
  pose proof H0 as H0'. unfold type_prog_defs in H0'.
  erewrite (conv_bool_app H0' WTp).

  rewrite (denote_prog_defs_fold_pirr p.(prog_defs)
             (ctxt_emp Empty_set Empty_set Empty_set fundef vardef p.(prog_public)) _ H0 tt).
  reflexivity.
Qed.

Lemma denote_glob_lookup_internal
  (p: Prog.program) (WTp: type_program p = true) (b: positive) (fn: function)
  (FD: Maps.PTree.get b (Globalenvs.Genv.genv_defs (Globalenvs.Genv.globalenv p))
       = Some (AST.Gfun (AST.Internal fn)))
  (WTFDs: type_function (mk_glob_ctxt p) fn = true) :
  denote_tree_lookup FD eq_refl (@denote_glob_ctxt_of_program p WTp)
  = denote_function WTFDs (@denote_glob_ctxt_of_program p WTp).
Proof using Type.
  assert (H0: type_prog_defs (ctxt_emp Empty_set Empty_set Empty_set fundef vardef p.(prog_public))
                p.(prog_defs) = true).
  { unfold type_program, Prog.type_program in WTp.
    repeat (apply Bool.andb_true_iff in WTp; destruct WTp as [WTp _]). exact WTp. }
  pose proof (denote_glob_ctxt_of_program_eq p WTp H0) as Eglob.
  transitivity (denote_tree_lookup FD eq_refl
                  (denote_prog_defs_fold p.(prog_defs)
                     (ctxt_emp Empty_set Empty_set Empty_set fundef vardef p.(prog_public)) H0 tt)).
  { exact (f_equal (denote_tree_lookup FD eq_refl) Eglob). }
  transitivity (denote_function WTFDs
                  (denote_prog_defs_fold p.(prog_defs)
                     (ctxt_emp Empty_set Empty_set Empty_set fundef vardef p.(prog_public)) H0 tt)).
  2: { exact (f_equal (denote_function WTFDs) (eq_sym Eglob)). }
  apply (denote_prog_defs_fold_lookup_internal p.(prog_defs)
           (ctxt_emp Empty_set Empty_set Empty_set fundef vardef p.(prog_public)) H0 tt).
  - exact (prog_defs_norepet p WTp).
  - intros f bb FS. exfalso.
    unfold Globalenvs.Genv.find_symbol, ctxt_emp in FS; cbn [ctxt_global] in FS.
    rewrite Maps.PTree.gempty in FS. discriminate FS.
  - apply Maps.PTree.gempty.
Qed.

Lemma genv_fn_lookup_some
  (ctx: ctxt (type * bool) (type * bool) unit fundef vardef) id_f fn
  (glob: denote_glob_ctxt Sm ctx) b
  (FIND: get_global id_f ctx = Some (AST.Gfun (AST.Internal fn)))
  (FS: Globalenvs.Genv.find_symbol (ctxt_global ctx) id_f = Some b)
  (FD: Globalenvs.Genv.find_def (ctxt_global ctx) b = Some (AST.Gfun (AST.Internal fn))) :
  genv_fn_lookup ctx id_f fn glob FIND = denote_tree_lookup FD eq_refl glob.
Proof using Type.
  unfold genv_fn_lookup, get_global in *. revert FS FIND.
  destruct (Globalenvs.Genv.find_symbol (ctxt_global ctx) id_f) as [b'|] eqn:FS';
    [ intros FS FIND | intros FS FIND; discriminate FS ].
  assert (b' = b) by congruence. subst b'.
  apply (denote_tree_lookup_pirr).
Qed.

Lemma genv_fn_lookup_eq_denote_function
  (p: Prog.program) (WTp: type_program p = true) (f: function) id_f fn b ty_env
  (locals: list (Nm))
  (FS: Globalenvs.Genv.find_symbol (Globalenvs.Genv.globalenv p) id_f = Some b)
  (FIND: get_global id_f (OpSem.Typing.state_ctxt p f ty_env locals)
         = Some (AST.Gfun (AST.Internal fn)))
  (WTFDs: type_function (mk_glob_ctxt p) fn = true) :
  genv_fn_lookup (OpSem.Typing.state_ctxt p f ty_env locals) id_f fn
    (@denote_glob_ctxt_of_program p WTp) FIND
  = denote_function WTFDs (@denote_glob_ctxt_of_program p WTp).
Proof using Type.
  assert (FS2: Globalenvs.Genv.find_symbol
                 (ctxt_global (OpSem.Typing.state_ctxt p f ty_env locals)) id_f = Some b).
  { cbn [ctxt_global OpSem.Typing.state_ctxt with_pure with_stack to_glob_ctxt with_internal mk_glob_ctxt with_global].
    exact FS. }
  assert (FD: Globalenvs.Genv.find_def
                (ctxt_global (OpSem.Typing.state_ctxt p f ty_env locals)) b
              = Some (AST.Gfun (AST.Internal fn))).
  { unfold get_global in FIND. revert FIND. rewrite FS2.
    exact (fun H => H). }
  rewrite (genv_fn_lookup_some (OpSem.Typing.state_ctxt p f ty_env locals) id_f fn
             (@denote_glob_ctxt_of_program p WTp) b FIND FS2 FD).
  exact (denote_glob_lookup_internal p WTp b fn FD WTFDs).
Qed.

Definition exf_lookup_denote [ef sig]
  (DEC: Facts.ef_sig_dec ef = Some sig)
  : denote_globdef (AST.Gfun (AST.External ef)) = Some (denote_sig Sm sig) :=
  eq_rect (Some sig)
    (fun o => match o with
              | Some s => Some (denote_sig Sm s)
              | None => Some (unit: Type)
              end = Some (denote_sig Sm sig))
    eq_refl (Facts.ef_sig_dec ef) (eq_sym DEC).

Definition exf_fn [ef sig]
  (DEC: Facts.ef_sig_dec ef = Some sig)
  (WTEXF: type_external_function ef = true)
  : denote_sig Sm sig :=
  eq_rect (Facts.ef_sig_dec ef)
    (fun o => match o with
              | Some s0 => denote_sig Sm s0
              | None => Empty_set
              end)
    (denote_external_function ef WTEXF) (Some sig) DEC.

Lemma denote_external_function_pirr ef
  (H1 H2: type_external_function ef = true) :
  @denote_external_function ef H1 = denote_external_function ef H2.
Proof using Type. assert (H1 = H2) as -> by (apply UIP_dec, Bool.bool_dec). reflexivity. Qed.

Lemma exf_fn_pirr [ef sig] (DEC: Facts.ef_sig_dec ef = Some sig)
  (H1 H2: type_external_function ef = true) :
  @exf_fn ef sig DEC H1 = exf_fn DEC H2.
Proof using Type.
  unfold exf_fn. f_equal. apply denote_external_function_pirr.
Qed.

Lemma denote_app_exf_some
  (ctx: ctxt (type * bool) (type * bool) unit fundef vardef) f_id args ef sig
  (env: denote_ctxt ctx) b
  (FIND: get_global f_id ctx = Some (AST.Gfun (AST.External ef)))
  (DEC: Facts.ef_sig_dec ef = Some sig)
  (W: ListExt.forall2b_opt type_eqb (type_expr ctx.(ctxt_pure)) args sig.(sig_args) = true)
  (FS: Globalenvs.Genv.find_symbol (ctxt_global ctx) f_id = Some b)
  (FD: Globalenvs.Genv.find_def (ctxt_global ctx) b = Some (AST.Gfun (AST.External ef))) :
  denote_app_exf FIND DEC W env
  = denote_app (denote_tree_lookup FD (exf_lookup_denote DEC) (snd env))
      (fst (fst env)) W.
Proof using Type.
  unfold denote_app_exf, get_global in *. revert FS FIND.
  destruct (Globalenvs.Genv.find_symbol (ctxt_global ctx) f_id) as [b'|] eqn:FS';
    [ intros FS FIND | intros FS FIND; discriminate FS ].
  assert (b' = b) by congruence. subst b'.
  f_equal.
  apply (denote_tree_lookup_pirr).
Qed.

Lemma denote_glob_ctxt_extend_lookup_external
  [ctx: ctxt Empty_set Empty_set Empty_set fundef vardef] [id ef sig]
  (DEC: Facts.ef_sig_dec ef = Some sig)
  (WTEXF: type_external_function ef = true)
  (WTGD: type_globdef ctx id (AST.Gfun (AST.External ef)) = true)
  (glob: denote_glob_ctxt Sm ctx)
  (G: Maps.PTree.get (Globalenvs.Genv.genv_next (ctxt_global ctx))
        (Globalenvs.Genv.genv_defs
           (ctxt_global (add_global ctx (id, AST.Gfun (AST.External ef)))))
      = Some (AST.Gfun (AST.External ef))) :
  denote_tree_lookup G (exf_lookup_denote DEC)
    (denote_glob_ctxt_extend WTGD (denote_globdef_value WTGD glob) glob)
  = exf_fn DEC WTEXF.
Proof using Type.
  unfold denote_glob_ctxt_extend, eq_rect_r, genv_defs_add_global;
    cbn [eq_rect eq_sym denote_globdef].
  erewrite (conv_option_app DEC).

  change (Globalenvs.Genv.genv_defs
            (ctxt_global (add_global ctx (id, AST.Gfun (AST.External ef)))))
    with (Maps.PTree.set (Globalenvs.Genv.genv_next (ctxt_global ctx))
            (AST.Gfun (AST.External ef))
            (Globalenvs.Genv.genv_defs (ctxt_global ctx))).
  rewrite (denote_tree_lookup_set_D).
  unfold exf_lookup_denote, exf_fn.
  cbn [denote_globdef_value denote_globdef].
  erewrite (conv_bool_app_false (Facts.ef_sig_dec_some_not_runtime ef sig DEC)).
  erewrite (denote_external_function_pirr ef _ WTEXF).
  generalize (@denote_external_function ef WTEXF).
  revert DEC.
  generalize (Facts.ef_sig_dec ef).
  intro o. destruct o as [s|]; intros DEC dv; [ | discriminate DEC ].
  assert (Es: s = sig) by congruence. subst s.
  assert (DEC = eq_refl) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec (option signature)))).
  cbn. reflexivity.
Qed.

Lemma denote_prog_defs_fold_lookup_external
  (defs: list (AST.ident * globdef)) :
  forall (ctx0: ctxt Empty_set Empty_set Empty_set fundef vardef)
         (H: type_prog_defs ctx0 defs = true)
         (glob0: denote_glob_ctxt Sm ctx0)
         (b: positive) ef sig
         (DEC: Facts.ef_sig_dec ef = Some sig)
         (WTEXF: type_external_function ef = true)
         (G0none: Maps.PTree.get b (Globalenvs.Genv.genv_defs (ctxt_global ctx0)) = None)
         (Gfin: Maps.PTree.get b
                  (Globalenvs.Genv.genv_defs
                     (Globalenvs.Genv.add_globals (ctxt_global ctx0) defs))
                = Some (AST.Gfun (AST.External ef))),
  denote_tree_lookup Gfin (exf_lookup_denote DEC) (denote_prog_defs_fold defs ctx0 H glob0)
  = exf_fn DEC WTEXF.
Proof using Type.
  induction defs as [|[id gd] rest IH];
    intros ctx0 H glob0 b ef sig DEC WTEXF G0none Gfin.
  - exfalso. cbn [Globalenvs.Genv.add_globals List.fold_left] in Gfin. congruence.
  - destruct (type_prog_defs_cons_inv ctx0 id gd rest H) as [WTGD H'].
    pose proof (denote_prog_defs_fold_cons id gd rest ctx0 H WTGD H' glob0) as Erw.
    destruct (Coqlib.peq b (Globalenvs.Genv.genv_next (ctxt_global ctx0))) as [Eb | NEb].
    + subst b.
      assert (G0'b : Maps.PTree.get (Globalenvs.Genv.genv_next (ctxt_global ctx0))
                       (Globalenvs.Genv.genv_defs (ctxt_global (add_global ctx0 (id, gd)))) = Some gd).
      { unfold add_global; cbn [ctxt_global with_global].
        rewrite (genv_defs_add_global _ _ (ctxt_global ctx0) (id, gd)); cbn [snd].
        apply Maps.PTree.gss. }
      assert (FINDDEF: Globalenvs.Genv.find_def
                    (Globalenvs.Genv.add_globals (ctxt_global ctx0) ((id, gd) :: rest))
                    (Globalenvs.Genv.genv_next (ctxt_global ctx0)) = Some gd).
      { rewrite add_globals_cons.
        apply (find_def_add_globals_pre rest (Globalenvs.Genv.add_global (ctxt_global ctx0) (id, gd))
                 (Globalenvs.Genv.genv_next (ctxt_global ctx0)) gd).
        exact G0'b. }
      unfold Globalenvs.Genv.find_def in FINDDEF.
      assert (Egd: gd = AST.Gfun (AST.External ef)) by congruence.
      subst gd.
      transitivity (denote_tree_lookup Gfin (exf_lookup_denote DEC)
                      (denote_prog_defs_fold rest (add_global ctx0 (id, AST.Gfun (AST.External ef))) H'
                         (denote_glob_ctxt_extend WTGD
                            (denote_globdef_value WTGD glob0) glob0))).
      { exact (f_equal (denote_tree_lookup Gfin (exf_lookup_denote DEC)) Erw). }
      transitivity (denote_tree_lookup G0'b (exf_lookup_denote DEC)
                      (denote_glob_ctxt_extend WTGD (denote_globdef_value WTGD glob0) glob0)).
      { exact (denote_prog_defs_fold_preserves rest
                 (add_global ctx0 (id, AST.Gfun (AST.External ef))) H'
                 (denote_glob_ctxt_extend WTGD (denote_globdef_value WTGD glob0) glob0)
                 (Globalenvs.Genv.genv_next (ctxt_global ctx0))
                 (AST.Gfun (AST.External ef)) _ (exf_lookup_denote DEC) G0'b Gfin). }
      exact (denote_glob_ctxt_extend_lookup_external DEC WTEXF WTGD glob0 G0'b).
    + assert (G0none': Maps.PTree.get b
                (Globalenvs.Genv.genv_defs (ctxt_global (add_global ctx0 (id, gd)))) = None).
      { unfold add_global; cbn [ctxt_global with_global].
        rewrite (genv_defs_add_global _ _ (ctxt_global ctx0) (id, gd)); cbn [snd].
        rewrite Maps.PTree.gso; first by exact NEb. exact G0none. }
      transitivity (denote_tree_lookup Gfin (exf_lookup_denote DEC)
                      (denote_prog_defs_fold rest (add_global ctx0 (id, gd)) H'
                         (denote_glob_ctxt_extend WTGD (denote_globdef_value WTGD glob0) glob0))).
      { exact (f_equal (denote_tree_lookup Gfin (exf_lookup_denote DEC)) Erw). }
      exact (IH (add_global ctx0 (id, gd)) H'
               (denote_glob_ctxt_extend WTGD (denote_globdef_value WTGD glob0) glob0)
               b ef sig DEC WTEXF G0none' Gfin).
Qed.

Lemma denote_glob_lookup_external
  (p: Prog.program) (WTp: type_program p = true) (b: positive) ef sig
  (DEC: Facts.ef_sig_dec ef = Some sig)
  (WTEXF: type_external_function ef = true)
  (FD: Maps.PTree.get b (Globalenvs.Genv.genv_defs (Globalenvs.Genv.globalenv p))
       = Some (AST.Gfun (AST.External ef))) :
  denote_tree_lookup FD (exf_lookup_denote DEC) (@denote_glob_ctxt_of_program p WTp)
  = exf_fn DEC WTEXF.
Proof using Type.
  assert (H0: type_prog_defs (ctxt_emp Empty_set Empty_set Empty_set fundef vardef p.(prog_public))
                p.(prog_defs) = true).
  { unfold type_program, Prog.type_program in WTp.
    repeat (apply Bool.andb_true_iff in WTp; destruct WTp as [WTp _]). exact WTp. }
  pose proof (denote_glob_ctxt_of_program_eq p WTp H0) as Eglob.
  transitivity (denote_tree_lookup FD (exf_lookup_denote DEC)
                  (denote_prog_defs_fold p.(prog_defs)
                     (ctxt_emp Empty_set Empty_set Empty_set fundef vardef p.(prog_public)) H0 tt)).
  { exact (f_equal (denote_tree_lookup FD (exf_lookup_denote DEC)) Eglob). }
  apply (denote_prog_defs_fold_lookup_external p.(prog_defs)
           (ctxt_emp Empty_set Empty_set Empty_set fundef vardef p.(prog_public)) H0 tt).
  apply Maps.PTree.gempty.
Qed.

Lemma denote_app_exf_eq_exf_fn
  (p: Prog.program) (WTp: type_program p = true) (f: function) id_f ef sig b ty_env
  (locals: list (Nm)) args
  (FS: Globalenvs.Genv.find_symbol (Globalenvs.Genv.globalenv p) id_f = Some b)
  (FIND: get_global id_f (OpSem.Typing.state_ctxt p f ty_env locals)
         = Some (AST.Gfun (AST.External ef)))
  (DEC: Facts.ef_sig_dec ef = Some sig)
  (WTEXF: type_external_function ef = true)
  (W: ListExt.forall2b_opt type_eqb
        (type_expr (OpSem.Typing.state_ctxt p f ty_env locals).(ctxt_pure)) args sig.(sig_args) = true)
  (env_p: denote_pure_ctxt Sm (OpSem.Typing.state_ctxt p f ty_env locals))
  (stk: denote_stack_ctxt Sm (OpSem.Typing.state_ctxt p f ty_env locals)) :
  denote_app_exf FIND DEC W (env_p, stk, @denote_glob_ctxt_of_program p WTp)
  = denote_app (exf_fn DEC WTEXF) env_p W.
Proof using Type.
  assert (FS2: Globalenvs.Genv.find_symbol
                 (ctxt_global (OpSem.Typing.state_ctxt p f ty_env locals)) id_f = Some b).
  { cbn [ctxt_global OpSem.Typing.state_ctxt with_pure with_stack to_glob_ctxt with_internal mk_glob_ctxt with_global].
    exact FS. }
  assert (FD: Globalenvs.Genv.find_def
                (ctxt_global (OpSem.Typing.state_ctxt p f ty_env locals)) b
              = Some (AST.Gfun (AST.External ef))).
  { unfold get_global in FIND. revert FIND. rewrite FS2.
    exact (fun H => H). }
  rewrite (denote_app_exf_some (OpSem.Typing.state_ctxt p f ty_env locals) id_f args ef sig
             (env_p, stk, @denote_glob_ctxt_of_program p WTp) b FIND DEC W FS2 FD).
  cbn [fst snd].
  f_equal.
  exact (denote_glob_lookup_external p WTp b ef sig DEC WTEXF FD).
Qed.

Lemma denote_fundef_call_External_raw
  [gctx: ctxt Empty_set Empty_set Empty_set fundef vardef] [ef] [sig: Prog.signature]
  (WTFD: type_fundef gctx (AST.External ef) = true)
  (SIG: type_funsig (AST.External ef) = Some sig)
  (WTEXF: type_external_function ef = true)
  (glob: denote_glob_ctxt Sm gctx) (args: list Vl) :
  denote_fundef_call WTFD SIG glob args
  = denote_app_values sig.(sig_args) sig.(sig_res) (exf_fn SIG WTEXF) args.
Proof using Type.
  cbn [denote_fundef_call].
  unfold exf_fn.
  f_equal.
  f_equal.
  apply denote_external_function_pirr.
Qed.

Lemma resolve_seq_denote p f env locals (k: @OpSem.cont Sm) v
  c_next k' env' n (mem mem': Sm) tye t_k0 t' WTp
  (RESOLVE: OpSem.resolve_seq_cont k env v c_next env' k' n)
  (TE: OpSem.Typing.type_env f env = Some tye)
  (WTk: OpSem.Typing.type_cont (OpSem.Typing.state_ctxt p f tye locals) k = Some t_k0)
  (TYEQ: type_eqb (Value.type_of_value v) t_k0 = true)
  (SBp: ListExt.SBinds f.(fn_params)) (SBt: ListExt.SBinds f.(fn_temps))
  (DIST: ListExt.DBinds f.(fn_params) f.(fn_temps))
  (POPS: OpSem.pop_stack_n n mem = Some mem')
  (Ts': OpSem.Typing.type_state p (OpSem.State f c_next k' env' (removelast_n n locals) mem') = Some t') :
  denote_cont WTk (denote_env TE) (denote_locals locals)
    (denote_glob_ctxt_of_program p WTp) (denote_value_eq (reflect_eq_of_true type_eqb_spec TYEQ)) mem
  = denote_state WTp Ts' mem'.
Proof using Type.
  revert locals mem mem' tye t_k0 TE WTk TYEQ POPS t' Ts'.
  induction RESOLVE as
    [ id_b c_next0 k0 env0 v0
    | c_cond c_body k0 env0 b
    | c_cond c_body k0 env0
    | id0 k0 env0 v0 c_next0 env0' k0' n0 RES IH
    | k0 env0 v0 c_next0 env0' k0' n0 RES IH ];
    intros locals mem mem' tye t_k0 TE WTk TYEQ POPS t' Ts'.
  - rewrite pop_stack_n_O in POPS. injection POPS as <-.
    cbn [removelast_n] in Ts'.
    enough (E: denote_cont WTk (denote_env TE) (denote_locals locals)
                 (denote_glob_ctxt_of_program p WTp)
                 (denote_value_eq (reflect_eq_of_true type_eqb_spec TYEQ)) = denote_state WTp Ts')
      by (rewrite E; reflexivity).
    destruct (type_state_State_inv _ _ _ _ _ _ _ _ Ts')
      as (tye' & t_c' & t_k' & TENV' & WTCMD' & WTCONT' & EQ' & Etc' & WTFN').
    erewrite (denote_state_State p f c_next0 (OpSem.Kscope (OpSem.scope_bind id_b) k0)
                (Maps.PTree.set id_b v0 env0) locals mem t' WTp Ts'
                tye' TENV' t_c' WTCMD' t_k' WTCONT' EQ' WTFN').
    clear Etc'.
    pose proof (reflect_eq_of_true type_eqb_spec TYEQ) as TYv.
    rewrite (denote_value_eq_irrel v0 _ (reflect_eq_of_true type_eqb_spec TYEQ) TYv).
    assert (TYTREE: tye = OpSem.Typing.type_env_tree f env0).
    { unfold OpSem.Typing.type_env in TE.
      destruct (OpSem.Typing.type_env_ok (f.(fn_params) ++ f.(fn_temps)) env0);
        [ injection TE as <-; reflexivity | discriminate TE ]. }
    destruct (type_cont_kbind_inv _ _ _ _ _ WTk) as (GETb & t_cb & WTcb & WTkb).
    assert (GT: Maps.PTree.get id_b tye = Some (t_k0, false)) by exact GETb.
    pose proof GT as GTT. rewrite TYTREE in GTT.
    destruct (OpSem.Typing.type_env_tree_get_inv f env0 SBp SBt id_b t_k0 false GTT)
      as (IN & _).
    pose proof (type_env_set_some f env0 tye SBp SBt DIST id_b t_k0 v0 IN TYv TE) as SET.
    assert (Etye': tye' = Maps.PTree.set id_b (t_k0, true) tye) by congruence.
    subst tye'.
    assert (Ecb: t_cb = t_c').
    { pose proof WTcb as W. pose proof WTCMD' as H'.
      change (type_cmd (set_pure id_b (t_k0, true) (OpSem.Typing.state_ctxt p f tye locals)) c_next0
              = Some t_cb) in W.
      change (type_cmd (set_pure id_b (t_k0, true) (OpSem.Typing.state_ctxt p f tye locals)) c_next0
              = Some t_c') in H'.
      congruence. }
    subst t_cb.
    destruct (type_cont_Kscope_unbind_inv _ _ _ _ WTCONT') as (t_b2 & GET2 & WTk2).
    assert (Et_b2: t_b2 = t_k0).
    { assert (G: Maps.PTree.get id_b (Maps.PTree.set id_b (t_k0, true) tye) = Some (t_b2, true))
        by exact GET2.
      rewrite Maps.PTree.gss in G. congruence. }
    subst t_b2.
    assert (Ek': t_k' = t_c').
    { symmetry; exact (reflect_eq_of_true type_eqb_spec EQ'). }
    subst t_k'.
    rewrite (denote_cont_kbind WTk (denote_env TE) (denote_locals locals)
               (denote_glob_ctxt_of_program p WTp) _ GETb t_c' WTcb WTkb).
    cbn [ctxt_pure with_pure to_glob_ctxt with_internal OpSem.Typing.state_ctxt] in *.
    rewrite -(denote_env_set' f env0 SBp SBt DIST id_b t_k0 v0 IN TYv tye TE TENV').
    assert (AG: pure_agree tye (Maps.PTree.set id_b (t_k0, true) tye)
                  (denote_env TE) (denote_env TENV')).
    { intros id1 sb G1 G2.
      destruct (Pos.eq_dec id1 id_b) as [->|NE].
      - exfalso. rewrite GT in G1. discriminate G1.
      - destruct (OpSem.Typing.type_env_get_value TE G1) as [w EVw TYw].
        rewrite (denote_env_get TE G1 EVw TYw).
        assert (EVw': Maps.PTree.get id1 (Maps.PTree.set id_b v0 env0) = Some w)
          by (rewrite (Maps.PTree.gso _ _ NE); exact EVw).
        rewrite (denote_env_get TENV' G2 EVw' TYw). reflexivity. }
    f_equiv.
    + apply (denote_cmd_pirr WTcb WTCMD').
    + intro v'.
      rewrite (convert_eq_refl_id _ (reflect_eq_of_true type_eqb_spec EQ') v').
      rewrite (denote_cont_Kscope_unbind WTCONT' (denote_env TENV') (denote_locals locals)
                 (denote_glob_ctxt_of_program p WTp) v' t_k0 GET2 WTk2).
      assert (TA2: type_agree
                     tye (Maps.PTree.set id_b (t_k0, false) (Maps.PTree.set id_b (t_k0, true) tye))).
      { intros id1 s1 s2 G1 G2.
        destruct (Pos.eq_dec id1 id_b) as [->|NE].
        - exfalso. pose proof G2 as H. rewrite Maps.PTree.gss in H. discriminate H.
        - pose proof G2 as H. rewrite Maps.PTree.gso in H; first by exact NE.
          rewrite Maps.PTree.gso in H; first by exact NE.
          congruence. }
      assert (AG2: pure_agree
                     tye (Maps.PTree.set id_b (t_k0, false) (Maps.PTree.set id_b (t_k0, true) tye))
                     (denote_env TE)
                     (denote_tree_unset id_b (denote_binding_false_eq t_k0) (denote_env TENV'))).
      { intros id1 t1 G1 G2.
        destruct (Pos.eq_dec id1 id_b) as [->|NE].
        - exfalso. pose proof G2 as H. rewrite Maps.PTree.gss in H. discriminate H.
        - pose proof G2 as G2a. rewrite Maps.PTree.gso in G2a; first by exact NE.
          rewrite (denote_tree_lookup_unset_other
                     (denote_binding_false_eq t_k0) (Maps.PTree.set id_b (t_k0, true) tye) id_b id1
                     (not_eq_sym NE) (denote_env TENV') (denote_binding_eq t1) G2 G2a).
          destruct (OpSem.Typing.type_env_get_value TE G1) as [w EVw TYw].
          rewrite (denote_env_get TE G1 EVw TYw).
          assert (EVw': Maps.PTree.get id1 (Maps.PTree.set id_b v0 env0) = Some w)
            by (rewrite (Maps.PTree.gso _ _ NE); exact EVw).
          rewrite (denote_env_get TENV' G2a EVw' TYw). reflexivity. }
      exact (denote_cont_frame k0
               (OpSem.Typing.state_ctxt p f tye locals)
               tye (Maps.PTree.set id_b (t_k0, false) (Maps.PTree.set id_b (t_k0, true) tye))
               (denote_env TE)
               (denote_tree_unset id_b (denote_binding_false_eq t_k0) (denote_env TENV'))
               (denote_locals locals) (denote_glob_ctxt_of_program p WTp)
               TA2 AG2 t_c' WTkb WTk2 v').
  - rewrite pop_stack_n_O in POPS. injection POPS as <-.
    cbn [removelast_n] in Ts'.
    enough (E: denote_cont WTk (denote_env TE) (denote_locals locals)
                 (denote_glob_ctxt_of_program p WTp)
                 (denote_value_eq (reflect_eq_of_true type_eqb_spec TYEQ)) = denote_state WTp Ts')
      by (rewrite E; reflexivity).
    destruct (type_state_State_inv _ _ _ _ _ _ _ _ Ts')
      as (tye' & t_c' & t_k' & TENV' & WTCMD' & WTCONT' & EQ' & Etc' & WTFN').
    erewrite (denote_state_State p f (if b then c_body else c_ret e_tt)
                (if b then OpSem.Kloop2 c_cond c_body k0 else k0) env0 locals mem t' WTp Ts'
                tye' TENV' t_c' WTCMD' t_k' WTCONT' EQ' WTFN').
    clear Etc'.
    destruct (type_cont_Kloop1_inv _ _ _ _ _ WTk) as (WTcond & WTbody & WTkb & Et0).
    subst t_k0.
    pose proof (reflect_eq_of_true type_eqb_spec TYEQ) as TYv.
    rewrite (denote_value_eq_irrel _ _ (reflect_eq_of_true type_eqb_spec TYEQ) TYv).
    assert (Etye': tye' = tye) by congruence. subst tye'.
    rewrite (denote_cont_Kloop1 WTk (denote_env TE) (denote_locals locals)
               (denote_glob_ctxt_of_program p WTp)
               (denote_value_eq TYv) WTcond WTbody WTkb).
    assert (VB: denote_value_eq TYv = b).
    { unfold denote_value_eq, convert_eq. cbn in TYv.
      rewrite (UIP_dec (ReflectExt.sumbool_of_reflect type_eqb_spec) TYv eq_refl). reflexivity. }
    rewrite VB.
    destruct b; cbn beta iota.
    + destruct (type_cont_Kloop2_inv _ _ _ _ _ WTCONT') as (WTcond' & WTbody' & WTkb' & Etk').
      subst t_k'.
      assert (t_c' = t_unit) as -> by exact (reflect_eq_of_true type_eqb_spec EQ').
      setoid_rewrite (denote_cont_Kloop2 WTCONT' (denote_env TENV') (denote_locals locals)
                 (denote_glob_ctxt_of_program p WTp) _ WTcond' WTbody' WTkb').
      setoid_rewrite (denote_cont_pirr WTkb' WTkb).
      rewrite (denote_env_pirr TENV' TE).
      rewrite (denote_cmd_pirr WTCMD' WTbody').
      rewrite (denote_cmd_pirr WTcond WTcond').
      rewrite (denote_cmd_pirr WTbody WTbody').
      reflexivity.
    + assert (t_c' = t_unit) as -> by (cbn [type_cmd type_expr] in WTCMD'; congruence).
      assert (t_k' = t_unit) as -> by (symmetry; exact (reflect_eq_of_true type_eqb_spec EQ')).
      rewrite (denote_cmd_ret WTCMD' (denote_env TENV', denote_locals locals,
                                     denote_glob_ctxt_of_program p WTp) WTCMD').
      cbn [fst snd]. rewrite ret_left.
      rewrite (convert_eq_refl_id _ (reflect_eq_of_true type_eqb_spec EQ') _).
      rewrite (denote_env_pirr TENV' TE).
      destruct (denote_expr WTCMD' (denote_env TE)).
      apply (denote_cont_pirr WTkb WTCONT').
  - rewrite pop_stack_n_O in POPS. injection POPS as <-.
    cbn [removelast_n] in Ts'.
    enough (E: denote_cont WTk (denote_env TE) (denote_locals locals)
                 (denote_glob_ctxt_of_program p WTp)
                 (denote_value_eq (reflect_eq_of_true type_eqb_spec TYEQ)) = denote_state WTp Ts')
      by (rewrite E; reflexivity).
    destruct (type_state_State_inv _ _ _ _ _ _ _ _ Ts')
      as (tye' & t_c' & t_k' & TENV' & WTCMD' & WTCONT' & EQ' & Etc' & WTFN').
    erewrite (denote_state_State p f c_cond (OpSem.Kloop1 c_cond c_body k0) env0 locals mem t' WTp Ts'
                tye' TENV' t_c' WTCMD' t_k' WTCONT' EQ' WTFN').
    clear Etc'.
    destruct (type_cont_Kloop2_inv _ _ _ _ _ WTk) as (WTcond & WTbody & WTkb & Et0).
    subst t_k0.
    pose proof (reflect_eq_of_true type_eqb_spec TYEQ) as TYv.
    rewrite (denote_value_eq_irrel _ _ (reflect_eq_of_true type_eqb_spec TYEQ) TYv).
    assert (Etye': tye' = tye) by congruence. subst tye'.
    rewrite (denote_cont_Kloop2 WTk (denote_env TE) (denote_locals locals)
               (denote_glob_ctxt_of_program p WTp)
               (denote_value_eq TYv) WTcond WTbody WTkb).
    destruct (type_cont_Kloop1_inv _ _ _ _ _ WTCONT') as (WTcond' & WTbody' & WTkb' & Etk').
    subst t_k'.
    assert (t_c' = t_bool) as -> by exact (reflect_eq_of_true type_eqb_spec EQ').
    setoid_rewrite (denote_cont_Kloop1 WTCONT' (denote_env TENV') (denote_locals locals)
               (denote_glob_ctxt_of_program p WTp) _ WTcond' WTbody' WTkb').
    rewrite (denote_env_pirr TENV' TE).
    rewrite (denote_cmd_pirr WTCMD' WTcond').
    rewrite (denote_cmd_pirr WTcond WTcond').
    rewrite (denote_cmd_pirr WTbody WTbody').
    setoid_rewrite (denote_cont_pirr WTkb' WTkb).
    setoid_rewrite while_fixpoint at 1.
    rewrite bind_assoc.
    f_equiv. intro b.
    rewrite (convert_eq_refl_id _ (reflect_eq_of_true type_eqb_spec EQ') b).
    destruct b; cbn beta iota.
    + rewrite bind_assoc. reflexivity.
    + rewrite ret_left. apply (denote_cont_pirr WTkb WTkb').
  - destruct (type_cont_Kscope_unbind_inv _ _ _ _ WTk) as (t_b & GETu & WTku).
    rewrite (denote_cont_Kscope_unbind WTk (denote_env TE) (denote_locals locals)
               (denote_glob_ctxt_of_program p WTp) _ t_b GETu WTku).
    assert (TYTREE: tye = OpSem.Typing.type_env_tree f env0).
    { unfold OpSem.Typing.type_env in TE.
      destruct (OpSem.Typing.type_env_ok (f.(fn_params) ++ f.(fn_temps)) env0);
        [ injection TE as <-; reflexivity | discriminate TE ]. }
    assert (GTT: Maps.PTree.get id0 (OpSem.Typing.type_env_tree f env0) = Some (t_b, true)).
    { rewrite -TYTREE. exact GETu. }
    destruct (OpSem.Typing.type_env_tree_get_inv f env0 SBp SBt id0 t_b true GTT) as (IN & _).
    pose proof (type_env_remove_some f env0 tye SBp SBt DIST id0 t_b IN TE) as TE'.
    pose proof (denote_env_unset' f env0 SBp SBt DIST id0 t_b IN tye TE TE') as UNSET.
    pose proof (IH locals mem mem' (Maps.PTree.set id0 (t_b, false) tye) t_k0 TE' WTku TYEQ POPS t' Ts') as IH'.
    rewrite UNSET in IH'.
    exact IH'.
  - destruct (type_cont_Kscope_pop_inv _ _ _ WTk) as (s0 & sl0 & STKne & WTk').
    rewrite (denote_cont_Kscope_pop WTk (denote_env TE) (denote_locals locals)
               (denote_glob_ctxt_of_program p WTp)
               (denote_value_eq (reflect_eq_of_true type_eqb_spec TYEQ)) s0 sl0 STKne WTk').
    unfold OpSem.pop_stack_n in POPS. rewrite Nat2N.inj_succ in POPS.
    unfold Monad.bind, Monad.get, Monad.put; cbn beta iota.
    destruct (pop (store mem)) as [st|] eqn:POPeq;
      [ rewrite (state_pop_n_succ_r POPeq) in POPS| rewrite (state_pop_n_succ_r_None POPeq) in POPS; discriminate POPS ].
    rewrite (mk_state_opt_of_dominates st (scnt mem) (heap mem) (alc mem)
               (dominates_pop (store mem) st (scnt mem) POPeq (state_store_dominates mem))
               (state_heap_dominates mem)).
    cbn beta iota.
    set (mem1 := mk_state st (scnt mem) (heap mem) (alc mem) _ _).
    assert (POPS1: OpSem.pop_stack_n n0 mem1 = Some mem').
    { exact POPS. }
    clear POPS. rename POPS1 into POPS.
    pose proof WTk' as WT2.
    cbn [OpSem.Typing.state_ctxt ctxt_stack with_pure with_stack to_glob_ctxt with_internal] in WT2.
    rewrite ListExt.map_removelast in WT2.
    cbn [OpSem.Typing.state_ctxt ctxt_stack with_pure with_stack to_glob_ctxt with_internal].
    rewrite (denote_cont_stack_eq (map_removelast (fun _ => tt) locals) WTk' WT2
               (denote_env TE)
               (denote_stack_removelast (denote_local) (List.map (fun _ => tt) locals)
                  (denote_locals locals))
               (denote_glob_ctxt_of_program p WTp)
               (denote_value_eq (reflect_eq_of_true type_eqb_spec TYEQ))).
    rewrite denote_locals_removelast.
    exact (IH (removelast locals) mem1 mem'
             tye t_k0 TE WT2 TYEQ POPS t' Ts').
Qed.

Lemma step_return_call_seq_correct p v f env locals (k: @OpSem.cont Sm)
  (mem mem': Sm) c_next k' env' n t t' WTp
  (RESOLVE: OpSem.resolve_seq_cont k env v c_next env' k' n)
  (POPS: OpSem.pop_stack_n n mem = Some mem')
  (Ts:  OpSem.Typing.type_state p (OpSem.Returnstate v (OpSem.Kcall f env locals k) mem) = Some t)
  (Ts': OpSem.Typing.type_state p (OpSem.State f c_next k' env' (removelast_n n locals) mem') = Some t') :
  denote_state WTp Ts mem = denote_state WTp Ts' mem'.
Proof using Type.
  destruct (type_state_Returnstate_inv _ _ _ _ _ Ts) as (t_k0 & WTcc & TYEQ & TY0).
  erewrite (denote_state_Returnstate p v (OpSem.Kcall f env locals k) mem t WTp Ts t_k0 WTcc TYEQ).
  destruct (type_cont_call_Kcall_inv (mk_glob_ctxt p) f env locals k t_k0 WTcc)
    as (TF & tye & TE & WTk).
  rewrite (denote_cont_call_Kcall WTcc (denote_glob_ctxt_of_program p WTp)
             (denote_value_eq (reflect_eq_of_true type_eqb_spec TYEQ)) TF TE WTk).
  pose proof (type_function_correct (mk_glob_ctxt p) f TF) as WTfn.
  exact (resolve_seq_denote p f env locals k v c_next k' env' n mem mem' tye t_k0 t' WTp RESOLVE TE WTk TYEQ
           (wt_fn_params_sbinds WTfn) (wt_fn_temps_sbinds WTfn) (wt_fn_params_temps_distinct WTfn)
           POPS Ts').
Qed.

Lemma convert_eq_program_run {A B} (EQ: B = A)
  (m: Monad.program Sm A) (s: Sm) (b: B) s' :
  m s = Some (Monad.Success (convert_eq EQ b, s')) ->
  convert_eq (eq_sym (f_equal (Monad.program Sm) EQ)) m s
  = Some (Monad.Success (b, s')).
Proof using Type.
  destruct EQ. cbn. auto.
Qed.

Lemma denote_value_eq_refl_eq (v: Vl) :
  denote_value_eq (eq_refl: Value.type_of_value v = Value.type_of_value v)
  = denote_value v.
Proof using Type. reflexivity. Qed.

Local Ltac br_raw TENV WT EV :=
  let H := fresh "BR" in let TY := fresh "TYbr" in
  destruct (denote_expr_eval _ _ _ TENV _ _ _ WT EV) as [TY H];
  replace (denote_expr WT (denote_env TENV)) with (denote_value_eq TY)
    by (symmetry; exact H);
  rewrite (denote_value_eq_irrel _ _ TY eq_refl) denote_value_eq_refl_eq;
  cbn [denote_value]; clear H TY.

Local Ltac br_enc TENV WT EV TY :=
  let H := fresh "BE" in
  destruct (denote_expr_eval _ _ _ TENV _ _ _ WT EV) as [TY H];
  replace (denote_expr WT (denote_env TENV)) with (denote_value_eq TY)
    by (symmetry; exact H);
  clear H.

Lemma builtin_exec p f c ge env locals (s: Sm) v s' ty_env t_c
  (WTp: type_program p = true)
  (TENV: OpSem.Typing.type_env f env = Some ty_env)
  (WTc: type_cmd (OpSem.Typing.state_ctxt p f ty_env locals) c = Some t_c)
  (BUILTIN: OpSem.builtin c ge env locals s v s') :
  exists (TY: Value.type_of_value v = t_c),
    denote_cmd WTc
      (denote_env TENV, denote_locals locals, denote_glob_ctxt_of_program p WTp) s
    = Some (Monad.Success (denote_value_eq TY, s')).
Proof using Type.
  inversion BUILTIN; subst.
  - assert (WTe: type_expr (OpSem.Typing.state_ctxt p f ty_env locals).(ctxt_pure) e = Some t_c) by exact WTc.
    destruct (denote_expr_eval _ _ _ TENV _ _ _ WTe EVAL) as [TY EQ].
    exists TY.
    rewrite (denote_cmd_ret WTc _ WTe). cbn [fst snd].
    replace (denote_expr WTe (denote_env TENV)) with (denote_value_eq TY)
      by (symmetry; exact EQ).
    reflexivity.
  - destruct (type_cmd_read_var_inv _ _ _ _ WTc) as (NTH & ->).
    pose proof (Value.Facts.type_of_value_complete WT) as TY.
    exists TY.
    rewrite (denote_cmd_read_var WTc _ NTH). cbn [fst snd].
    match goal with
    | |- context[denote_stack_lookup ?G ?D ?E] =>
        replace (denote_stack_lookup G D E) with nm
          by (symmetry; exact (denote_stack_lookup_locals locals n nm G DEREF))
    end.
    apply (convert_eq_program_run (denote_types_agree t)).
    unfold read_var. cbn [Monad.bind Monad.get].
    rewrite LOOKUP (decode_value_memval _ _ _ TY VMV). cbn [Monad.ret]. reflexivity.
  - destruct (type_cmd_write_var_inv _ _ _ _ _ WTc) as (WTval & NTH & ->).
    exists eq_refl.
    rewrite (denote_cmd_write_var WTc _ WTval NTH). cbn [fst snd].
    match goal with
    | |- context[denote_stack_lookup ?G ?D ?E] =>
        replace (denote_stack_lookup G D E) with nm
          by (symmetry; exact (denote_stack_lookup_locals locals n nm G DEREF))
    end.
    br_enc TENV WTval EVAL TYd.
    unfold state_mutate_store.
    match goal with
    | |- context [mk_state ?a ?b ?c ?d ?D1 ?D2] => generalize D1 D2
    end.
    intros DOMs DOMh.
    unfold write_var. cbn [Monad.bind Monad.get].
    rewrite (encode_denote_value v0 t TYd).
    rewrite (MUTATE: mutate (store s) nm v0 = Some st').
    erewrite (mk_state_opt_of_dominates st' (scnt s) (heap s) (alc s)).
    cbn [Monad.put]. reflexivity.
  - destruct (type_cmd_alloc_ptr_inv _ _ _ _ _ WTc) as (( id_m & SRCH ) & WTsize & WTinit & ->).
    exists eq_refl.
    rewrite (denote_cmd_alloc_ptr WTc _ SRCH WTsize WTinit). cbn [fst snd].
    br_raw TENV WTsize EVAL_SIZE.
    br_enc TENV WTinit EVAL_INIT TYi.
    unfold state_alloc.
    match goal with
    | |- context [mk_state ?a ?b ?c ?d ?D1 ?D2] => generalize D1 D2
    end.
    intros DOMs DOMh.
    unfold alloc_ptr.
    rewrite (proj2 (N.leb_le _ _) BND).
    cbn [Monad.bind Monad.get].
    rewrite (encode_denote_value v_init t TYi).
    rewrite (ALLOC: alloc (heap s) (alc s) v_size v_init = Some (hp', alc', ptr)).
    erewrite (mk_state_opt_of_dominates (store s) (scnt s) hp' alc').
    cbn [Monad.bind Monad.put Monad.ret]. reflexivity.
  - destruct (type_cmd_read_ptr_inv _ _ _ _ WTc) as (WTptr & ->).
    pose proof (Value.Facts.type_of_value_complete WT) as TY.
    exists TY.
    rewrite (denote_cmd_read_ptr WTc _ WTptr). cbn [fst snd].
    br_raw TENV WTptr EVAL.
    apply (convert_eq_program_run (denote_types_agree t)).
    unfold read_ptr. cbn [Monad.bind Monad.get].
    rewrite LOOKUP (decode_value_memval _ _ _ TY VMV). cbn [Monad.ret]. reflexivity.
  - destruct (type_cmd_write_ptr_inv _ _ _ _ _ WTc) as (WTptr & WTval & ->).
    exists eq_refl.
    rewrite (denote_cmd_write_ptr WTc _ WTptr WTval). cbn [fst snd].
    br_raw TENV WTptr EVAL_ptr.
    br_enc TENV WTval EVAL_data TYd.
    unfold state_mutate_heap.
    match goal with
    | |- context [mk_state ?a ?b ?c ?d ?D1 ?D2] => generalize D1 D2
    end.
    intros DOMs DOMh.
    unfold write_ptr. cbn [Monad.bind Monad.get].
    rewrite (encode_denote_value v_data t TYd).
    rewrite (MUTATE: mutate (heap s) _ v_data = Some hp').
    erewrite (mk_state_opt_of_dominates (store s) (scnt s) hp' (alc s)).
    cbn [Monad.put]. reflexivity.
  - destruct (type_cmd_free_ptr_inv _ _ _ WTc) as (( id_f & SRCH ) & WTptr & ->).
    exists eq_refl.
    rewrite (denote_cmd_free_ptr WTc _ SRCH WTptr). cbn [fst snd].
    br_raw TENV WTptr EVAL.
    unfold state_free.
    match goal with
    | |- context [mk_state ?a ?b ?c ?d ?D1 ?D2] => generalize D1 D2
    end.
    intros DOMs DOMh.
    unfold free_ptr. cbn [Monad.bind Monad.get].
    rewrite FREE.
    erewrite (mk_state_opt_of_dominates (store s) (scnt s) hp' (alc s)).
    cbn [Monad.put]. reflexivity.
  - destruct (type_cmd_shift_fw_ptr_inv _ _ _ _ WTc) as (WTptr & WTofst & ->).
    exists eq_refl.
    rewrite (denote_cmd_shift_fw_ptr WTc _ WTptr WTofst). cbn [fst snd].
    br_raw TENV WTptr EVAL_ptr.
    br_raw TENV WTofst EVAL_shift.
    unfold shift_fw_ptr. cbn [Monad.bind Monad.get].
    rewrite (proj1 (Bool.reflect_iff _ _ (weakly_valid_spec _ _)) WVALID_pre).
    rewrite SHIFT.
    rewrite (proj1 (Bool.reflect_iff _ _ (weakly_valid_spec _ _)) WVALID_post).
    cbn [Monad.ret]. reflexivity.
  - destruct (type_cmd_shift_bw_ptr_inv _ _ _ _ WTc) as (WTptr & WTofst & ->).
    exists eq_refl.
    rewrite (denote_cmd_shift_bw_ptr WTc _ WTptr WTofst). cbn [fst snd].
    br_raw TENV WTptr EVAL_ptr.
    br_raw TENV WTofst EVAL_shift.
    unfold shift_bw_ptr. cbn [Monad.bind Monad.get].
    rewrite (proj1 (Bool.reflect_iff _ _ (weakly_valid_spec _ _)) WVALID_pre).
    rewrite SHIFT.
    rewrite (proj1 (Bool.reflect_iff _ _ (weakly_valid_spec _ _)) WVALID_post).
    cbn [Monad.ret]. reflexivity.
  - destruct (type_cmd_ptr_eq_inv _ _ _ _ WTc) as (WTl & WTr & ->).
    exists eq_refl.
    rewrite (denote_cmd_ptr_eq WTc _ WTl WTr). cbn [fst snd].
    br_raw TENV WTl EVAL_l.
    br_raw TENV WTr EVAL_r.
    unfold eq_ptr. cbn [Monad.bind Monad.get].
    rewrite (proj1 (Bool.reflect_iff _ _ (cmp_valid_spec _ _ _)) CMPVALID).
    rewrite CMP.
    cbn [Monad.ret]. reflexivity.
  - destruct (type_cmd_div_inv _ _ _ _ WTc) as (WTl & WTr & ->).
    exists eq_refl.
    rewrite (denote_cmd_div WTc _ WTl WTr). cbn [fst snd].
    br_raw TENV WTl EVAL_l.
    br_raw TENV WTr EVAL_r.
    rewrite denote_value_eq_refl_eq. cbn [denote_value].
    exact DIV.
  - destruct (type_cmd_mod_inv _ _ _ _ WTc) as (WTl & WTr & ->).
    exists eq_refl.
    rewrite (denote_cmd_mod WTc _ WTl WTr). cbn [fst snd].
    br_raw TENV WTl EVAL_l.
    br_raw TENV WTr EVAL_r.
    rewrite denote_value_eq_refl_eq. cbn [denote_value].
    exact MDL.
Qed.

Lemma convert_eq_denote_value_eq v t1 t2
  (E1: Value.type_of_value v = t1) (E2: t1 = t2) :
  convert_eq (f_equal denote_type E2) (denote_value_eq E1) = denote_value_eq (eq_trans E1 E2).
Proof using Type. destruct E2. reflexivity. Qed.


Lemma step_builtin_seq_cont_correct p f c (k: @OpSem.cont Sm) env locals
  (s s' s'': Sm) v c_next k' env' n ge t t' WTp
  (RESOLVE: OpSem.resolve_seq_cont k env v c_next env' k' n)
  (BUILTIN: OpSem.builtin c ge env locals s v s')
  (POPS: OpSem.pop_stack_n n s' = Some s'')
  (SBp: ListExt.SBinds f.(fn_params)) (SBt: ListExt.SBinds f.(fn_temps))
  (DIST: ListExt.DBinds f.(fn_params) f.(fn_temps))
  (Ts: OpSem.Typing.type_state p (OpSem.State f c k env locals s) = Some t)
  (Ts': OpSem.Typing.type_state p (OpSem.State f c_next k' env' (removelast_n n locals) s'') = Some t') :
  denote_state WTp Ts s = denote_state WTp Ts' s''.
Proof using Type.
  destruct (type_state_State_inv _ _ _ _ _ _ _ _ Ts)
    as (tye & t_c & t_k & TENV & WTCMD & WTCONT & EQ & Etc & WTFN).
  erewrite (denote_state_State p f c k env locals s t WTp Ts
              tye TENV t_c WTCMD t_k WTCONT EQ WTFN).
  destruct (builtin_exec p f c ge env locals s v s' tye t_c WTp TENV WTCMD BUILTIN)
    as [TY BE].
  unfold Monad.bind at 1. rewrite BE.
  rewrite convert_eq_denote_value_eq.
  pose (TYEQ := proj1 (Bool.reflect_iff _ _ (type_eqb_spec (Value.type_of_value v) t_k))
                   (eq_trans TY (reflect_eq_of_true type_eqb_spec EQ))).
  rewrite (denote_value_eq_irrel v t_k
             (eq_trans TY (reflect_eq_of_true type_eqb_spec EQ))
             (reflect_eq_of_true type_eqb_spec TYEQ)).
  rewrite (resolve_seq_denote p f env locals k v c_next k' env' n s' s'' tye t_k t' WTp
             RESOLVE TENV WTCONT TYEQ SBp SBt DIST POPS Ts').
  reflexivity.
Qed.

Lemma step_builtin_call_cont_correct p f c (k k0: @OpSem.cont Sm) env locals
  (s s' s'': Sm) v ge t t' WTp
  (CALLK: OpSem.resolve_call_cont k k0)
  (BUILTIN: OpSem.builtin c ge env locals s v s')
  (POP: OpSem.pop_stack locals s' = Some s'')
  (Ts: OpSem.Typing.type_state p (OpSem.State f c k env locals s) = Some t)
  (Ts': OpSem.Typing.type_state p (OpSem.Returnstate v k0 s'') = Some t') :
  denote_state WTp Ts s = denote_state WTp Ts' s''.
Proof using Type.
  destruct (type_state_State_inv _ _ _ _ _ _ _ _ Ts)
    as (tye & t_c & t_k & TENV & WTCMD & WTCONT & EQ & Etc & WTFN). clear Etc.
  erewrite (denote_state_State p f c k env locals s t WTp Ts
              tye TENV t_c WTCMD t_k WTCONT EQ WTFN).
  destruct (builtin_exec p f c ge env locals s v s' tye t_c WTp TENV WTCMD BUILTIN)
    as [TY BE].
  unfold Monad.bind at 1. rewrite BE.
  rewrite convert_eq_denote_value_eq.
  pose (TYEQ := proj1 (Bool.reflect_iff _ _ (type_eqb_spec (Value.type_of_value v) t_k))
                   (eq_trans TY (reflect_eq_of_true type_eqb_spec EQ))).
  rewrite (denote_value_eq_irrel v t_k
             (eq_trans TY (reflect_eq_of_true type_eqb_spec EQ))
             (reflect_eq_of_true type_eqb_spec TYEQ)).
  destruct (type_state_Returnstate_inv _ _ _ _ _ Ts')
    as (t_kc & WTCC & EQc & Etkc). clear Etkc.
  erewrite (denote_state_Returnstate p v k0 s'' t' WTp Ts' t_kc WTCC EQc).
  assert (Et: t_kc = t_k).
  { transitivity (Value.type_of_value v); [symmetry|]; apply (reflect_eq_of_true type_eqb_spec); assumption. }
  subst t_kc.
  assert (POPS': OpSem.pop_stack_n (length (List.map (fun _ => tt) locals)) s' = Some s'').
  { rewrite List.length_map -OpSem.Facts.pop_stack_n_length. exact POP. }
  etransitivity.
  { exact (denote_cont_resolve_call (mk_glob_ctxt p) f k k0 CALLK tye
             (List.map (fun _ => tt) locals) t_k WTCONT WTCC
             (denote_env TENV) (denote_locals locals) (denote_glob_ctxt_of_program p WTp)
             (denote_value_eq (reflect_eq_of_true type_eqb_spec TYEQ)) s' s'' POPS'). }
  rewrite (denote_value_eq_irrel v t_k (reflect_eq_of_true type_eqb_spec TYEQ)
             (reflect_eq_of_true type_eqb_spec EQc)).
  reflexivity.
Qed.

Lemma step_app_correct (p: Prog.program) (f: function) id_f args
  (k: @OpSem.cont Sm) (env: Maps.PTree.t Vl) (locals: list (Nm))
  (mem: Sm) (fd: fundef) v_args bblk t t' WTp
  (EVAL: ListExt.map_opt (fun e => eval e env) args = Some v_args)
  (FIND_SYMB: Globalenvs.Genv.find_symbol (Globalenvs.Genv.globalenv p) id_f = Some bblk)
  (FIND_FUNC: Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv p) bblk = Some fd)
  (Ts:  OpSem.Typing.type_state p (OpSem.State f (c_app id_f args) k env locals mem) = Some t)
  (Ts': OpSem.Typing.type_state p
          (OpSem.Callstate fd v_args (OpSem.Kcall f env locals k) mem) = Some t') :
  denote_state WTp Ts = denote_state WTp Ts'.
Proof using Type.
  destruct (type_state_State_inv _ _ _ _ _ _ _ _ Ts)
    as (ty_env & t_c & t_kS & TENV & WTCMD & WTCONTs & EQs & EtcS & WTFNs).
  clear EtcS.
  destruct (type_cmd_app_inv _ _ _ _ WTCMD) as
    [ (fn & t_args & FIND & MAP & F2 & Etc)
    | (ef & sig0 & t_args & FIND & MAP & DEC & F2 & Etc) ].
  - subst t_c.
    assert (FDdef: Globalenvs.Genv.find_def (Globalenvs.Genv.globalenv p) bblk
                   = Some (AST.Gfun (AST.Internal fn))).
    { assert (FS2: Globalenvs.Genv.find_symbol
                     (ctxt_global (OpSem.Typing.state_ctxt p f ty_env locals)) id_f = Some bblk).
      { cbn [ctxt_global OpSem.Typing.state_ctxt with_pure with_stack to_glob_ctxt with_internal mk_glob_ctxt with_global].
        exact FIND_SYMB. }
      unfold get_global in FIND. revert FIND. rewrite FS2.
      exact (fun H => H). }
    assert (Efd: fd = AST.Internal fn).
    { unfold Globalenvs.Genv.find_funct_ptr in FIND_FUNC.
      rewrite FDdef in FIND_FUNC. injection FIND_FUNC as <-. reflexivity. }
    subst fd.
    destruct (type_state_Callstate_inv _ _ _ _ _ _ Ts')
      as (sig & t_kC & SIG & WTFD & WTCONTc & EQc & EtkC & WTARGSc).
    clear EtkC.
    assert (Esig: sig = fn_signature fn) by (cbn [type_funsig] in SIG; congruence).
    subst sig.
    pose proof (reflect_eq_of_true type_eqb_spec EQs) as EkS.
    pose proof (reflect_eq_of_true type_eqb_spec EQc) as EkC. cbn [fn_signature sig_res] in EkC.
    subst t_kS. subst t_kC.
    erewrite (denote_state_State p f (c_app id_f args) k env locals mem t WTp Ts
                ty_env TENV fn.(fn_return) WTCMD fn.(fn_return) WTCONTs EQs WTFNs).
    erewrite (denote_state_Callstate p (AST.Internal fn) v_args (OpSem.Kcall f env locals k) mem t'
                WTp Ts' (fn_signature fn) SIG WTFD fn.(fn_return) WTCONTc EQc WTARGSc).
    rewrite (denote_cmd_app_internal WTCMD
               (denote_env TENV, denote_locals locals, denote_glob_ctxt_of_program p WTp)
               FIND MAP F2).
    cbn [fst snd].
    setoid_rewrite (denote_app_eq_denote_app_values (ctx := OpSem.Typing.state_ctxt p f ty_env locals) TENV
               (genv_fn_lookup (OpSem.Typing.state_ctxt p f ty_env locals) id_f fn
                  (denote_glob_ctxt_of_program p WTp) FIND)
               (eq_trans (ListExt.forall2b_opt_map_opt _ _ _ _ _ MAP) F2) EVAL).
    setoid_rewrite (denote_fundef_call_Internal_raw WTFD SIG (denote_glob_ctxt_of_program p WTp) v_args).
    rewrite (genv_fn_lookup_eq_denote_function p WTp f id_f fn bblk ty_env locals FIND_SYMB FIND WTFD).
    f_equiv. intro v.
    cbn [fn_signature sig_res].
    rewrite (convert_eq_refl_id _ _ v).
    destruct (type_cont_call_Kcall_inv (mk_glob_ctxt p) f env locals k fn.(fn_return) WTCONTc)
      as (TF & tye & TE & WTk).
    rewrite (denote_cont_call_Kcall WTCONTc (denote_glob_ctxt_of_program p WTp) _ TF TE WTk).
    cbn [fn_signature sig_res].
    rewrite (convert_eq_refl_id _ _ v).
    assert (tye = ty_env) by congruence. subst tye.
    rewrite (denote_env_pirr TE TENV).
    exact (denote_cont_pirr WTCONTs WTk (denote_env TENV) (denote_locals locals)
             (denote_glob_ctxt_of_program p WTp) v).
  - subst t_c.
    assert (FDdef: Globalenvs.Genv.find_def (Globalenvs.Genv.globalenv p) bblk
                   = Some (AST.Gfun (AST.External ef))).
    { assert (FS2: Globalenvs.Genv.find_symbol
                     (ctxt_global (OpSem.Typing.state_ctxt p f ty_env locals)) id_f = Some bblk).
      { cbn [ctxt_global OpSem.Typing.state_ctxt with_pure with_stack to_glob_ctxt with_internal mk_glob_ctxt with_global].
        exact FIND_SYMB. }
      unfold get_global in FIND. revert FIND. rewrite FS2.
      exact (fun H => H). }
    assert (Efd: fd = AST.External ef).
    { unfold Globalenvs.Genv.find_funct_ptr in FIND_FUNC.
      rewrite FDdef in FIND_FUNC. injection FIND_FUNC as <-. reflexivity. }
    subst fd.
    destruct (type_state_Callstate_inv _ _ _ _ _ _ Ts')
      as (sig & t_kC & SIG & WTFD & WTCONTc & EQc & EtkC & WTARGSc).
    clear EtkC.
    assert (Esig: sig = sig0).
    { cbn [type_funsig] in SIG. congruence. }
    subst sig.
    assert (WTEXF: type_external_function ef = true)
      by (unfold type_external_function; rewrite DEC; reflexivity).
    pose proof (reflect_eq_of_true type_eqb_spec EQs) as EkS.
    pose proof (reflect_eq_of_true type_eqb_spec EQc) as EkC.
    subst t_kS. subst t_kC.
    erewrite (denote_state_State p f (c_app id_f args) k env locals mem t WTp Ts
                ty_env TENV sig0.(sig_res) WTCMD sig0.(sig_res) WTCONTs EQs WTFNs).
    erewrite (denote_state_Callstate p (AST.External ef) v_args (OpSem.Kcall f env locals k) mem t'
                WTp Ts' sig0 SIG WTFD sig0.(sig_res) WTCONTc EQc WTARGSc).
    rewrite (denote_cmd_app_external WTCMD
               (denote_env TENV, denote_locals locals, denote_glob_ctxt_of_program p WTp)
               FIND DEC MAP F2).
    setoid_rewrite (denote_app_exf_eq_exf_fn p WTp f id_f ef sig0 bblk ty_env locals args
               FIND_SYMB FIND DEC WTEXF
               (eq_trans (ListExt.forall2b_opt_map_opt _ _ _ _ _ MAP) F2)
               (denote_env TENV) (denote_locals locals)).
    setoid_rewrite (denote_app_eq_denote_app_values (ctx := OpSem.Typing.state_ctxt p f ty_env locals) TENV
               (exf_fn DEC WTEXF)
               (eq_trans (ListExt.forall2b_opt_map_opt _ _ _ _ _ MAP) F2) EVAL).
    rewrite (denote_fundef_call_External_raw WTFD SIG WTEXF
               (denote_glob_ctxt_of_program p WTp) v_args).
    assert (SIG = DEC) as -> by (apply UIP_dec, (ReflectExt.sumbool_of_reflect (@eqb_spec (option signature)))).
    f_equiv. intro v.
    rewrite (convert_eq_refl_id _ _ v).
    destruct (type_cont_call_Kcall_inv (mk_glob_ctxt p) f env locals k sig0.(sig_res) WTCONTc)
      as (TF & tye & TE & WTk).
    rewrite (denote_cont_call_Kcall WTCONTc (denote_glob_ctxt_of_program p WTp) _ TF TE WTk).
    rewrite (convert_eq_refl_id _ _ v).
    assert (tye = ty_env) by congruence. subst tye.
    rewrite (denote_env_pirr TE TENV).
    exact (denote_cont_pirr WTCONTs WTk (denote_env TENV) (denote_locals locals)
             (denote_glob_ctxt_of_program p WTp) v).
Qed.

Lemma step_with_var_correct p f t_v e_init c_next (k: @OpSem.cont Sm) env locals
  (s mem': Sm) v st' sg' nm t t' WTp
  (EVAL: eval e_init env = Some v)
  (PUSH: push (store s) (scnt s) (encode v) = Some (st', sg', nm))
  (MK: mk_state_opt st' sg' (heap s) (alc s) = Some mem')
  (Ts: OpSem.Typing.type_state p (OpSem.State f (c_with_var t_v e_init c_next) k env locals s) = Some t)
  (Ts': OpSem.Typing.type_state p
          (OpSem.State f c_next (OpSem.Kscope OpSem.scope_store k) env (locals ++ [nm])
             mem') = Some t') :
  denote_state WTp Ts s
  = denote_state WTp Ts' mem'.
Proof using Type.
  destruct (type_state_State_inv _ _ _ _ _ _ _ _ Ts)
    as (tye & t_c & t_kS & TENV & WTCMD & WTCONT & EQ & Etc & WTFN). clear Etc.
  destruct (type_state_State_inv _ _ _ _ _ _ _ _ Ts')
    as (tye' & t_c' & t_kS' & TENV' & WTCMD' & WTCONT' & EQ' & Etc' & WTFN'). clear Etc'.
  assert (Etye: tye' = tye) by congruence. subst tye'.
  destruct (type_cmd_with_var_inv _ _ _ _ _ WTCMD) as (WTinit & WTc).
  destruct (type_cont_Kscope_pop_inv _ _ _ WTCONT') as (s0 & sl0 & STKne & WTk').
  assert (Ectx: push_stack tt (OpSem.Typing.state_ctxt p f tye locals)
                = OpSem.Typing.state_ctxt p f tye (locals ++ [nm])).
  { unfold push_stack, OpSem.Typing.state_ctxt, with_pure, with_stack, with_internal.
    cbn [ctxt_stack ctxt_pure ctxt_global]. rewrite List.map_app. reflexivity. }
  assert (Etcc: t_c' = t_c).
  { pose proof WTc as WTc2. rewrite Ectx in WTc2. congruence. }
  subst t_c'.
  assert (EctxK: with_stack (removelast (ctxt_stack (OpSem.Typing.state_ctxt p f tye (locals ++ [nm]))))
                   (OpSem.Typing.state_ctxt p f tye (locals ++ [nm]))
                 = OpSem.Typing.state_ctxt p f tye locals).
  { unfold OpSem.Typing.state_ctxt, with_pure, with_stack, with_internal.
    cbn [ctxt_stack ctxt_pure ctxt_global]. rewrite List.map_app.
    cbn [List.map]. rewrite List.removelast_last. reflexivity. }
  assert (EkS: t_kS' = t_kS).
  { pose proof WTk' as WTk2. rewrite EctxK in WTk2. congruence. }
  subst t_kS'.
  erewrite (denote_state_State p f (c_with_var t_v e_init c_next) k env locals s t WTp Ts
              tye TENV t_c WTCMD t_kS WTCONT EQ WTFN).
  erewrite (denote_state_State p f c_next (OpSem.Kscope OpSem.scope_store k) env (locals ++ [nm])
              mem' t' WTp Ts' tye TENV' t_c WTCMD' t_kS WTCONT' EQ' WTFN').
  rewrite (denote_cmd_with_var WTCMD
             (denote_env TENV, denote_locals locals, denote_glob_ctxt_of_program p WTp) WTinit WTc).
  cbn [fst snd].
  br_enc TENV WTinit EVAL TY.
  rewrite (bind_with_var_step _ _ _ s mem' st' sg' nm
             (eq_trans (f_equal (push (store s) (scnt s))
                          (encode_denote_value v t_v TY)) PUSH) MK).
  match goal with |- ?L ?m = ?R ?m => enough (E: L = R) by (rewrite E; reflexivity) end.
  f_equiv.
  - rewrite (denote_env_pirr TENV' TENV).
    setoid_rewrite (denote_cmd_stack_eq (base := OpSem.Typing.state_ctxt p f tye locals)
               (sl1 := List.map (fun _ => tt) (locals ++ [nm]))
               (sl2 := List.map (fun _ => tt) locals ++ [tt])
               (map_app (fun _ => tt) locals [nm]) WTCMD' WTc
               (denote_env TENV) (denote_locals (locals ++ [nm]))
               (denote_glob_ctxt_of_program p WTp)).
    rewrite denote_locals_push. reflexivity.
  - intro v0.
    rewrite (denote_cont_Kscope_pop WTCONT' (denote_env TENV') (denote_locals (locals ++ [nm]))
               (denote_glob_ctxt_of_program p WTp)
               (convert_eq (f_equal denote_type (reflect_eq_of_true type_eqb_spec EQ')) v0)
               s0 sl0 STKne WTk').
    apply bind_Proper; [reflexivity|]; intro sx.
    destruct (pop (store sx)) as [st2|]; [| reflexivity].
    destruct (mk_state_opt st2 (scnt sx) (heap sx) (alc sx)) as [sy|]; [| reflexivity].
    apply bind_Proper; [reflexivity|]; intros _.
    setoid_rewrite (denote_cont_stack_eq
               (eq_trans (map_removelast (fun _ => tt) (locals ++ [nm]))
                         (f_equal (List.map (fun _ => tt)) (List.removelast_last locals nm)))
               WTk' WTCONT (denote_env TENV')
               (denote_stack_removelast (denote_local)
                  (ctxt_stack (OpSem.Typing.state_ctxt p f tye (locals ++ [nm])))
                  (denote_locals (locals ++ [nm])))
               (denote_glob_ctxt_of_program p WTp)
               (convert_eq (f_equal denote_type (reflect_eq_of_true type_eqb_spec EQ')) v0)).
    change (ctxt_stack (OpSem.Typing.state_ctxt p f tye (locals ++ [nm])))
      with (List.map (fun _ => tt) (locals ++ [nm])).
    rewrite denote_stack_removelast_locals_snoc.
    rewrite (denote_env_pirr TENV' TENV).
    assert (EQ' = EQ) as -> by (apply UIP_dec, Bool.bool_dec).
    reflexivity.
Qed.

Lemma step_correct
  [p events s s' t t']
  (WTp: type_program p = true)
  (WTs: wt_state p s)
  (Ts: @Typing.type_state Sm p s = Some t)
  (Ts': Typing.type_state p s' = Some t')
  (STEP: step (Globalenvs.Genv.globalenv p) s events s') :
  denote_state WTp Ts (state_of_state s) = denote_state WTp Ts' (state_of_state s').
Proof using Type.
  inversion STEP; subst.
  - rewrite (step_bind_correct _ _ _ _ _ _ _ _ _ _ _ _ _ Ts Ts'); reflexivity.
  - cbn [state_of_state].
    exact (step_with_var_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             EVAL PUSH (mk_state_opt_of_dominates _ _ _ _ _ _) Ts Ts').
  - cbn [state_of_state].
    exact (step_builtin_call_cont_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             CALLK BUILTIN POP_STACK Ts Ts').
  - inversion WTs as [fw cw kw ew lw mw ctxw tw WTS GLBw | | ]; subst.
    pose proof (wt_fn_params_sbinds (OpSem.Typing.State_wt_function _ _ _ _ _ _ _ _ WTS)) as SBp.
    pose proof (wt_fn_temps_sbinds (OpSem.Typing.State_wt_function _ _ _ _ _ _ _ _ WTS)) as SBt.
    pose proof (wt_fn_params_temps_distinct (OpSem.Typing.State_wt_function _ _ _ _ _ _ _ _ WTS)) as DIST.
    cbn [state_of_state].
    exact (step_builtin_seq_cont_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             RESOLVE BUILTIN POPS SBp SBt DIST Ts Ts').
  - rewrite (step_app_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _
               EVAL FIND_SYMB FIND_FUNC Ts Ts'); reflexivity.
  - rewrite (step_ifthenelse_correct _ _ _ _ _ _ _ _ _ _ _ _ _ EVAL Ts Ts'); reflexivity.
  - rewrite (step_while_correct _ _ _ _ _ _ _ _ _ _ _ Ts Ts'); reflexivity.
  - rewrite (step_internal_function_correct _ _ _ _ _ _ _ _ WT_ARGS CALLK Ts Ts'); reflexivity.
  - rewrite (step_return_call_seq_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RESOLVE POPS Ts Ts'); reflexivity.
Qed.

Lemma step_star_correct p events s s' t
  (WTp': type_program p = true)
  (WTs: wt_state p s)
  (Ts: @Typing.type_state Sm p s = Some t)
  (STAR: OpSem.step_star (Globalenvs.Genv.globalenv p) s events s') :
  exists t' (Ts': Typing.type_state p s' = Some t'),
    denote_state WTp' Ts (state_of_state s) = denote_state WTp' Ts' (state_of_state s').
Proof.
  assert (WTp: Typing.wt_program p)
    by exact (proj2 (Bool.reflect_iff _ _ (type_program_spec p)) WTp').
  revert t WTs Ts.
  induction STAR as [ s0 | s0 tr1 s2 tr2 s3 tr STEP STAR IH ETrace ];
    intros t0 WTs0 Ts0.
  - exists t0, Ts0. reflexivity.
  - pose proof (Typing.step_preservation p s0 s2 tr1 WTp WTs0 STEP) as WTs2.
    destruct (Typing.type_state_complete p s2 WTs2) as [t2 Ts2].
    destruct (IH t2 WTs2 Ts2) as [t' [Ts' IHeq]].
    exists t', Ts'.
    rewrite (step_correct WTp' WTs0 Ts0 Ts2 STEP).
    exact IHeq.
Qed.

Lemma denote_state_entry (p: Prog.program) (f: fundef)
  (args: list Vl) (mem: Sm) (sig_args: list type)
  (WTp: type_program p = true)
  (Ts: OpSem.Typing.type_state p (OpSem.Callstate f args OpSem.Kstop mem) = Some t_nat)
  (WTFD: type_fundef (mk_glob_ctxt p) f = true)
  (SIG: type_funsig f = Some (mk_signature sig_args t_nat)) :
  denote_state WTp Ts
  = denote_fundef_call WTFD SIG (denote_glob_ctxt_of_program p WTp) args.
Proof.
  destruct (type_state_Callstate_inv _ _ _ _ _ _ Ts)
    as (sig0 & t_k0 & SIG0 & _ & _ & _ & _ & WTARGS0).
  assert (Esig: sig0 = mk_signature sig_args t_nat) by congruence.
  subst sig0.
  rewrite (denote_state_Callstate p f args OpSem.Kstop mem t_nat WTp Ts _ SIG WTFD
             t_nat eq_refl (ReflectExt.reflect_refl type_eqb_spec t_nat) WTARGS0).
  etransitivity; [| exact (Monad.ret_right _)].
  apply bind_Proper; [reflexivity |].
  intro v.
  rewrite (denote_cont_call_Kstop eq_refl).
  rewrite (convert_eq_refl_id t_nat _ v).
  reflexivity.
Qed.

Lemma denote_state_final (p: Prog.program) (n: nat)
  (mem: Sm) (t: type)
  (WTp: type_program p = true)
  (Ts: OpSem.Typing.type_state p
         (OpSem.Returnstate (v_nat n) OpSem.Kstop mem) = Some t) :
  denote_state WTp Ts = ret n.
Proof.
  pose proof Ts as Ts'.
  cbn [OpSem.Typing.type_state OpSem.Typing.type_cont_call Value.type_of_value type_eqb]
    in Ts'.
  injection Ts' as TY. subst t.
  rewrite (denote_state_Returnstate p (v_nat n) OpSem.Kstop mem t_nat WTp Ts
             t_nat eq_refl (ReflectExt.reflect_refl type_eqb_spec t_nat)).
  rewrite (denote_cont_call_Kstop eq_refl).
  unfold denote_value_eq.
  rewrite convert_eq_refl_id.
  reflexivity.
Qed.

Theorem denote_initial_final (p: Prog.program)
  (s0 s': @OpSem.state Sm) (tr: Events.trace) (r: Integers.int)
  (INIT: OpSem.initial_state p s0)
  (STAR: OpSem.step_star (Globalenvs.Genv.globalenv p) s0 tr s')
  (FINAL: OpSem.final_state s' r) :
  exists (n: nat) (f: fundef)
         (WTp: type_program p = true)
         (WTFD: type_fundef (mk_glob_ctxt p) f = true)
         (SIG: type_funsig f = Some (mk_signature [] t_nat)),
    r = Integers.Int.repr (Z.of_nat n)
    /\ get_global p.(prog_main) (mk_glob_ctxt p) = Some (AST.Gfun f)
    /\ denote_fundef_call WTFD SIG (denote_glob_ctxt_of_program p WTp) []
         (emp_state)
       = Some (Monad.Success (n, OpSem.state_of_state s')).
Proof.
  pose proof (OpSem.Typing.wt_initial_state p s0 INIT) as WTs0.
  inversion INIT; subst.
  pose proof (type_program_complete WT) as WTp.
  assert (GET: get_global p.(prog_main) (mk_glob_ctxt p) = Some (AST.Gfun f)).
  { unfold get_global.
    change (ctxt_global (mk_glob_ctxt p)) with (Globalenvs.Genv.globalenv p).
    rewrite (Prog.Facts.prog_main_is_prog_main p).
    rewrite FIND_SYMB.
    apply (proj1 (Globalenvs.Genv.find_funct_ptr_iff (Globalenvs.Genv.globalenv p) b f)).
    exact FIND_FUNC. }
  pose proof (type_fundef_complete _ _ (wt_glob_fundef p WT _ _ GET)) as WTFD.
  pose proof (type_funsig_complete _ _ MAIN_SIG) as SIG.
  assert (Ts0: @OpSem.Typing.type_state Sm p
                 (OpSem.Callstate f [] OpSem.Kstop (emp_state)) = Some t_nat).
  { cbn [OpSem.Typing.type_state]. rewrite SIG WTFD. reflexivity. }
  destruct (step_star_correct p tr (OpSem.Callstate f [] OpSem.Kstop (emp_state))
              s' t_nat WTp WTs0 Ts0 STAR) as [t' [Ts' EQ]].
  inversion FINAL as [n0 mem']; subst.
  exists n0, f, WTp, WTFD, SIG.
  split; [reflexivity |].
  split; [exact GET |].
  cbn [OpSem.state_of_state] in EQ.
  rewrite (denote_state_entry p f [] (emp_state) [] WTp Ts0 WTFD SIG) in EQ.
  rewrite (denote_state_final p n0 mem' t' WTp Ts') in EQ.
  exact EQ.
Qed.

End Agree.
