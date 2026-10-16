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

From Stdlib Require Import PArith NArith ZArith Arith List Bool ssreflect.

From compcert.lib Require Import Maps.

From GallinaC.Utils Require Import ListExt CompCertExt.

From GallinaC.Imp Require Import Uint32 Uintptr.

From GallinaC.Compiler.Common Require Import Ctxt Value Types Expr CCInj.
From GallinaC.Compiler.IR Require Import Cmd Prog.

Inductive wt_cmd: ctxt (type * bool) (type * bool) unit fundef vardef -> cmd -> type -> Prop :=
| wt_ret : forall
    [ctx e t]
    (WTexpr: wt_expr ctx.(ctxt_pure) e t)
  , wt_cmd ctx (c_ret e t) t
| wt_bind : forall
    [ctx id_b t_b b_b c_b c_c t_c]
    (BINDABLE: get_pure id_b ctx = Some (t_b, b_b))
    (WTbind: wt_cmd ctx c_b t_b)
    (WTcont: wt_cmd (set_pure id_b (t_b, true) ctx) c_c t_c)
  , wt_cmd ctx (c_bind id_b t_b c_b c_c t_c) t_c
| wt_if : forall
    [ctx e c1 c2 t]
    (WTcond: wt_expr ctx.(ctxt_pure) e t_bool)
    (WTthen: wt_cmd ctx c1 t)
    (WTelse: wt_cmd ctx c2 t)
  , wt_cmd ctx (c_if e c1 c2 t) t
| wt_while: forall
    [ctx c_cond c_body id_cond id_body b_c b_b]
    (BOUNDcond: get_internal id_cond ctx = Some (t_bool, b_c))
    (BOUNDbody: get_internal id_body ctx = Some (t_unit, b_b))
    (WTcond: wt_cmd ctx c_cond t_bool)
    (WTbody: wt_cmd ctx c_body t_unit)
  , wt_cmd ctx (c_while c_cond id_cond c_body id_body) t_unit
| wt_read_var : forall {ctx n t},
    wt_cmd ctx (c_read_var n t) t
| wt_write_var : forall
    [ctx n e t]
    (WTval: wt_expr ctx.(ctxt_pure) e t)
  , wt_cmd ctx (c_write_var n t e) t_unit
| wt_alloc_ptr : forall
    [ctx n t e id_ptr id_count id_init b_p b_c b_i]
    (MALLOC: exf_bound AST.EF_malloc ctx)
    (INTptr: get_internal id_ptr ctx = Some (t_ptr, b_p))
    (INTcount: get_internal id_count ctx = Some (t_ofst, b_c))
    (INTinit: get_internal id_init ctx = Some (t, b_i))
    (NEptrcount: id_ptr <> id_count)
    (NEptrinit: id_ptr <> id_init)
    (NEcountinit: id_count <> id_init)
    (WTcount: wt_expr ctx.(ctxt_pure) n t_ofst)
    (WTinit: wt_expr ctx.(ctxt_pure) e t)
  , wt_cmd ctx (c_alloc_ptr n t e id_ptr id_count id_init) t_ptr
| wt_read_ptr : forall
    [ctx t p]
    (WTptr: wt_expr ctx.(ctxt_pure) p t_ptr)
  , wt_cmd ctx (c_read_ptr p t) t
| wt_write_ptr : forall
    [ctx p t e]
    (WTptr: wt_expr ctx.(ctxt_pure) p t_ptr)
    (WTval: wt_expr ctx.(ctxt_pure) e t)
  , wt_cmd ctx (c_write_ptr p t e) t_unit
| wt_free_ptr : forall
    [ctx p]
    (FREE: exf_bound AST.EF_free ctx)
    (WTptr: wt_expr ctx.(ctxt_pure) p t_ptr)
  , wt_cmd ctx (c_free_ptr p) t_unit
| wt_shift_fw_ptr: forall
    [ctx p n]
    (WTptr: wt_expr ctx.(ctxt_pure) p t_ptr)
    (WTofst: wt_expr ctx.(ctxt_pure) n t_ofst)
  , wt_cmd ctx (c_shift_fw_ptr p n) t_ptr
| wt_shift_bw_ptr: forall
    [ctx p n]
    (WTptr: wt_expr ctx.(ctxt_pure) p t_ptr)
    (WTofst: wt_expr ctx.(ctxt_pure) n t_ofst)
  , wt_cmd ctx (c_shift_bw_ptr p n) t_ptr
| wt_ptr_eq: forall
    [ctx ptr_l ptr_r]
    (WTptr_l: wt_expr ctx.(ctxt_pure) ptr_l t_ptr)
    (WTptr_r: wt_expr ctx.(ctxt_pure) ptr_r t_ptr)
  , wt_cmd ctx (c_ptr_eq ptr_l ptr_r) t_bool
| wt_app : forall
    [ctx f_id args fn]
    (FINDfn: Ctxt.get_global f_id ctx = Some (AST.Gfun (AST.Internal fn)))
    (EQargs: List.map snd fn.(fn_params) = List.map snd args)
    (WTargs: Forall2 (wt_expr ctx.(ctxt_pure)) (List.map fst args) (List.map snd args))
  , wt_cmd ctx (c_app f_id fn.(fn_return) args) fn.(fn_return)
| wt_app_exf : forall
    [ctx: ctxt (type * bool) (type * bool) unit fundef vardef] [f_id args t_out nm sg]
    (FINDfn: Ctxt.get_global f_id ctx = Some (AST.Gfun (AST.External (AST.EF_external nm sg))))
    (SIG: exf_funsig (AST.EF_external nm sg)
            {| sig_args := List.map snd args; sig_res := t_out |})
    (WTargs: Forall2 (wt_expr ctx.(ctxt_pure)) (List.map fst args) (List.map snd args))
  , wt_cmd ctx (c_app f_id t_out args) t_out
| wt_div: forall
    [ctx e_l e_r]
    (WTl: wt_expr ctx.(ctxt_pure) e_l t_nat)
    (WTr: wt_expr ctx.(ctxt_pure) e_r t_nat)
  , wt_cmd ctx (c_div e_l e_r) t_nat
| wt_mod: forall
    [ctx e_l e_r]
    (WTl: wt_expr ctx.(ctxt_pure) e_l t_nat)
    (WTr: wt_expr ctx.(ctxt_pure) e_r t_nat)
  , wt_cmd ctx (c_mod e_l e_r) t_nat
.

Definition wt_f_extra (f_extra: f_extra): Prop :=
  (f_extra.(fn_stackspace) <= Unsigned.max_unsigned n_ofst_t / Z.of_nat memword_bytes)%Z.

Definition wt_p_extra (p: program): Prop := True.

Definition wt_function := wt_function f_extra wt_f_extra wt_cmd.

Definition function_internals [P S GF GV: Type] (ctx: ctxt P (type * bool) S GF GV) (f: function): Prop :=
  forall id ty b, Ctxt.get_internal id ctx = Some (ty, b) -> In (id, ty) f.(fn_internals).

Definition wt_fundef := wt_fundef f_extra wt_f_extra wt_cmd.

Definition wt_fundef_call [Ad Pt] := @wt_fundef_call Ad Pt cmd f_extra.

Notation wt_globvar := Prog.wt_globvar.

Definition wt_globdef := wt_globdef f_extra wt_f_extra wt_cmd.

Definition wt_program := wt_program wt_f_extra wt_cmd wt_p_extra.

Lemma wt_cmd_incl_global
  [ctx ctx': ctxt (type * bool) (type * bool) unit fundef vardef]
  (EQpure: Ctxt.ctxt_pure ctx = Ctxt.ctxt_pure ctx')
  (EQinternal: Ctxt.ctxt_internal ctx = Ctxt.ctxt_internal ctx')
  (GLOBext: forall id g, Ctxt.get_global id ctx = Some g ->
                         Ctxt.get_global id ctx' = Some g)
  [c t]
  (WTcmd: wt_cmd ctx c t)
  : wt_cmd ctx' c t.
Proof.
  revert ctx' EQpure EQinternal GLOBext.
  induction WTcmd; intros.
  - apply wt_ret; rewrite <- EQpure; assumption.
  - apply (wt_bind (t_b := t_b) (b_b := b_b)).
    + unfold get_pure in *; rewrite <- EQpure; assumption.
    + apply IHWTcmd1; assumption.
    + apply IHWTcmd2.
      * unfold set_pure, with_pure; cbn; f_equal; assumption.
      * unfold set_pure, with_pure; cbn; assumption.
      * intros id' g GLOBext'.
        unfold set_pure, with_pure, get_global in *; cbn in *.
        now apply GLOBext.
  - now apply wt_if;
      [ rewrite <- EQpure
      | apply IHWTcmd1
      | apply IHWTcmd2 ].
  - apply (wt_while (b_c := b_c) (b_b := b_b)).
    + unfold get_internal in *; rewrite <- EQinternal; assumption.
    + unfold get_internal in *; rewrite <- EQinternal; assumption.
    + apply IHWTcmd1; assumption.
    + apply IHWTcmd2; assumption.
  - now apply wt_read_var.
  - now apply wt_write_var; rewrite <- EQpure.
  - apply (wt_alloc_ptr (b_p := b_p) (b_c := b_c) (b_i := b_i));
      [ destruct MALLOC as ( id_m & GET ); exists id_m; exact (GLOBext _ _ GET)
      | unfold get_internal in *; rewrite <- EQinternal; assumption
      | unfold get_internal in *; rewrite <- EQinternal; assumption
      | unfold get_internal in *; rewrite <- EQinternal; assumption
      | exact NEptrcount
      | exact NEptrinit
      | exact NEcountinit
      | exact (eq_rect _ (fun q => wt_expr q n t_ofst) WTcount _ EQpure)
      | exact (eq_rect _ (fun q => wt_expr q e t) WTinit _ EQpure) ].
  - now apply wt_read_ptr; rewrite <- EQpure.
  - now apply wt_write_ptr;
      [ rewrite <- EQpure
      | rewrite <- EQpure
      ].
  - apply wt_free_ptr;
      [ destruct FREE as ( id_f & GET ); exists id_f; exact (GLOBext _ _ GET)
      | exact (eq_rect _ (fun q => wt_expr q p t_ptr) WTptr _ EQpure) ].
  - now apply wt_shift_fw_ptr; rewrite <- EQpure.
  - now apply wt_shift_bw_ptr; rewrite <- EQpure.
  - now apply wt_ptr_eq; rewrite <- EQpure.
  - apply (wt_app (fn := fn)).
    + now apply GLOBext.
    + assumption.
    + clear -EQpure WTargs.
      replace (ctxt_pure ctx') with (ctxt_pure ctx).
      eapply Forall2_impl; [ | apply WTargs ].
      by rewrite EQpure.
  - apply (wt_app_exf (nm := nm) (sg := sg)).
    + by apply GLOBext.
    + exact SIG.
    + clear -EQpure WTargs.
      replace (ctxt_pure ctx') with (ctxt_pure ctx).
      eapply Forall2_impl; [ | apply WTargs ].
      by rewrite EQpure.
  - now apply wt_div; rewrite <- EQpure.
  - now apply wt_mod; rewrite <- EQpure.
Qed.

Lemma wt_cmd_incl_global_stack
  [ctx ctx': ctxt (type * bool) (type * bool) unit fundef vardef]
  (EQpure: Ctxt.ctxt_pure ctx = Ctxt.ctxt_pure ctx')
  (EQinternal: Ctxt.ctxt_internal ctx = Ctxt.ctxt_internal ctx')
  (EQstack: Ctxt.ctxt_stack ctx = Ctxt.ctxt_stack ctx')
  (GLOBext: forall id g, Ctxt.get_global id ctx = Some g ->
                         Ctxt.get_global id ctx' = Some g)
  [c t]
  (WTcmd: wt_cmd ctx c t)
  : wt_cmd ctx' c t.
Proof.
  exact (wt_cmd_incl_global EQpure EQinternal GLOBext WTcmd).
Qed.

Definition type_f_extra (fx: f_extra): bool :=
  Z.leb fx.(fn_stackspace) (Unsigned.max_unsigned n_ofst_t / Z.of_nat memword_bytes).

Lemma type_f_extra_complete fx: wt_f_extra fx -> type_f_extra fx = true.
Proof.
  intro LE; apply Z.leb_le, LE.
Qed.

Lemma type_f_extra_correct fx: type_f_extra fx = true -> wt_f_extra fx.
Proof.
  intro LE; apply Z.leb_le, LE.
Qed.

Fixpoint type_cmd (ctx: ctxt (type * bool) (type * bool) unit fundef vardef) (c: cmd) {struct c}: option type :=
  match c with
  | c_ret e t =>
      match type_expr ctx.(ctxt_pure) e with
      | Some t' => if eqb t t' then Some t else None
      | None => None
      end
  | c_bind id_b t_b c_b c_c t_c =>
      match get_pure id_b ctx with
      | Some (t_b', _) =>
          if eqb t_b t_b' then
            match type_cmd ctx c_b with
            | Some t_b'' =>
                if eqb t_b t_b'' then
                  match type_cmd (set_pure id_b (t_b, true) ctx) c_c with
                  | Some t_c' => if eqb t_c t_c' then Some t_c else None
                  | None => None
                  end
                else None
            | None => None
            end
          else None
      | _ => None
      end
  | c_if e_if c_then c_else t =>
      match type_expr ctx.(ctxt_pure) e_if with
      | Some t_bool =>
          match type_cmd ctx c_then, type_cmd ctx c_else with
          | Some t_t, Some t_e =>
              if eqb t t_t then if eqb t t_e then Some t else None else None
          | _, _ => None
          end
      | _ => None
      end
  | c_while c_cond id_cond c_body id_body =>
      match get_internal id_cond ctx, get_internal id_body ctx with
      | Some (t_bool, _), Some (t_unit, _) =>
          match type_cmd ctx c_cond, type_cmd ctx c_body with
          | Some t_bool, Some t_unit => Some t_unit
          | _, _ => None
          end
      | _, _ => None
      end
  | c_read_var n t => Some t
  | c_write_var n t e =>
      match type_expr ctx.(ctxt_pure) e with
      | Some t' => if eqb t t' then Some t_unit else None
      | None => None
      end
  | c_alloc_ptr e_count t e_init id_ptr id_count id_init =>
      match find_exf_genv AST.EF_malloc ctx with
      | Some _ =>
          if Pos.eqb id_ptr id_count then None
          else if Pos.eqb id_ptr id_init then None
          else if Pos.eqb id_count id_init then None
          else
          match get_internal id_ptr ctx, get_internal id_count ctx,
            get_internal id_init ctx with
          | Some (t_ptr, _), Some (t_ofst, _), Some (t_i, _) =>
              if eqb t t_i
              then
                match type_expr ctx.(ctxt_pure) e_count, type_expr ctx.(ctxt_pure) e_init with
                | Some t_ofst, Some t' => if eqb t t' then Some t_ptr else None
                | _, _ => None
                end
              else None
          | _, _, _ => None
          end
      | None => None
      end
  | c_read_ptr e_ptr t =>
      match type_expr ctx.(ctxt_pure) e_ptr with
      | Some t_ptr => Some t
      | _ => None
      end
  | c_write_ptr e_ptr t e_data =>
      match type_expr ctx.(ctxt_pure) e_ptr, type_expr ctx.(ctxt_pure) e_data with
      | Some t_ptr, Some t' => if eqb t t' then Some t_unit else None
      | _, _ => None
      end
  | c_free_ptr e_ptr =>
      match find_exf_genv AST.EF_free ctx with
      | Some _ =>
          match type_expr ctx.(ctxt_pure) e_ptr with
          | Some t_ptr => Some t_unit
          | _ => None
          end
      | None => None
      end
  | c_shift_fw_ptr e_ptr e_shift
  | c_shift_bw_ptr e_ptr e_shift =>
      match type_expr ctx.(ctxt_pure) e_ptr, type_expr ctx.(ctxt_pure) e_shift with
      | Some t_ptr, Some t_ofst => Some t_ptr
      | _, _ => None
      end
  | c_ptr_eq e_ptr_l e_ptr_r =>
      match type_expr ctx.(ctxt_pure) e_ptr_l, type_expr ctx.(ctxt_pure) e_ptr_r with
      | Some t_ptr, Some t_ptr => Some t_bool
      | _, _ => None
      end
  | c_app f_id t_out args =>
      match Ctxt.get_global f_id ctx with
      | Some (AST.Gfun (AST.Internal fn)) =>
          if eqb t_out fn.(fn_return)
          then if ListExt.forall2b eqb (List.map snd fn.(fn_params)) (List.map snd args)
               then if ListExt.forall2b
                         (fun e t => match type_expr ctx.(ctxt_pure) e with
                                     | Some t' => eqb t' t
                                     | None => false
                                     end)
                         (List.map fst args) (List.map snd args)
                    then Some fn.(fn_return)
                    else None
               else None
          else None
      | Some (AST.Gfun (AST.External (AST.EF_external nm sg))) =>
          match Facts.ef_sig_dec (AST.EF_external nm sg) with
          | Some sig =>
              if eqb sig {| sig_args := List.map snd args; sig_res := t_out |}
              then if ListExt.forall2b
                        (fun e t => match type_expr ctx.(ctxt_pure) e with
                                    | Some t' => eqb t' t
                                    | None => false
                                    end)
                        (List.map fst args) (List.map snd args)
                   then Some t_out
                   else None
              else None
          | None => None
          end
      | _ => None
      end
  | c_div e_l e_r
  | c_mod e_l e_r =>
      match type_expr ctx.(ctxt_pure) e_l, type_expr ctx.(ctxt_pure) e_r with
      | Some t_nat, Some t_nat => Some t_nat
      | _, _ => None
      end
  end.

Lemma type_cmd_complete [ctx c t] (WT: wt_cmd ctx c t): type_cmd ctx c = Some t.
Proof.
  induction WT; cbn [type_cmd].
  - by rewrite (Expr.Facts.type_expr_correct WTexpr) (ReflectExt.reflect_refl eqb_spec _).
  - by rewrite BINDABLE (ReflectExt.reflect_refl eqb_spec _) IHWT1 (ReflectExt.reflect_refl eqb_spec _) IHWT2 (ReflectExt.reflect_refl eqb_spec _).
  - by rewrite (Expr.Facts.type_expr_correct WTcond) IHWT1 IHWT2 (ReflectExt.reflect_refl eqb_spec _).
  - by rewrite BOUNDcond BOUNDbody IHWT1 IHWT2.
  - reflexivity.
  - by rewrite (Expr.Facts.type_expr_correct WTval) (ReflectExt.reflect_refl eqb_spec _).
  - destruct MALLOC as ( id_m & GET ).
    destruct (find_exf_genv_complete (ef := AST.EF_malloc) GET) as ( id_m' & SRCH ).
    by rewrite SRCH
         (proj2 (Pos.eqb_neq id_ptr id_count) NEptrcount)
         (proj2 (Pos.eqb_neq id_ptr id_init) NEptrinit)
         (proj2 (Pos.eqb_neq id_count id_init) NEcountinit)
         INTptr INTcount INTinit
         (ReflectExt.reflect_refl eqb_spec _)
         (Expr.Facts.type_expr_correct WTcount)
         (Expr.Facts.type_expr_correct WTinit)
         (ReflectExt.reflect_refl eqb_spec _).
  - by rewrite (Expr.Facts.type_expr_correct WTptr).
  - by rewrite (Expr.Facts.type_expr_correct WTptr)
      (Expr.Facts.type_expr_correct WTval) (ReflectExt.reflect_refl eqb_spec _).
  - destruct FREE as ( id_f & GET ).
    destruct (find_exf_genv_complete (ef := AST.EF_free) GET) as ( id_f' & SRCH ).
    by rewrite SRCH (Expr.Facts.type_expr_correct WTptr).
  - by rewrite (Expr.Facts.type_expr_correct WTptr)
      (Expr.Facts.type_expr_correct WTofst).
  - by rewrite (Expr.Facts.type_expr_correct WTptr)
      (Expr.Facts.type_expr_correct WTofst).
  - by rewrite (Expr.Facts.type_expr_correct WTptr_l)
      (Expr.Facts.type_expr_correct WTptr_r).
  - by rewrite
         (FINDfn : @get_global _ _ _ fundef _ f_id ctx = _)
         (ReflectExt.reflect_refl eqb_spec _)
         EQargs
         ((ListExt.list_eqb_refl eqb eqb_spec)
           : forall l, ListExt.forall2b eqb l l = true)
         ((Expr.Facts.forall2_wt_expr_forall2b_type_expr WTargs)
           : ListExt.forall2b
               (fun e t => match type_expr (@ctxt_pure _ _ _ fundef _ ctx) e with
                           | Some t' => eqb t' t
                           | None => false
                           end)
               (List.map fst args) (List.map snd args) = true).
  - by rewrite
         (FINDfn : @get_global _ _ _ fundef _ f_id ctx = _)
         (proj1 (Facts.ef_sig_dec_spec _ _) SIG)
         (ReflectExt.reflect_refl eqb_spec _)
         ((Expr.Facts.forall2_wt_expr_forall2b_type_expr WTargs)
           : ListExt.forall2b
               (fun e t => match type_expr (@ctxt_pure _ _ _ fundef _ ctx) e with
                           | Some t' => eqb t' t
                           | None => false
                           end)
               (List.map fst args) (List.map snd args) = true).
  - by rewrite (Expr.Facts.type_expr_correct WTl)
      (Expr.Facts.type_expr_correct WTr).
  - by rewrite (Expr.Facts.type_expr_correct WTl)
      (Expr.Facts.type_expr_correct WTr).
Qed.

Lemma type_cmd_correct [ctx c t] (EQ: type_cmd ctx c = Some t): wt_cmd ctx c t.
Proof.
  revert ctx t EQ;
    induction c as [
      e t
    | id_b t_b c1 IHc1 c2 IHc2 t_c
    | e c1 IHc1 c2 IHc2 t_te
    | c1 IHc1 id_cond c2 IHc2 id_body
    | n t
    | n t e
    | e_count t e_init id_ptr id_count id_init
    | e_ptr t
    | e_ptr t e_data
    | e_ptr
    | e_ptr e_shift
    | e_ptr e_shift
    | e_l e_r
    | f_id t_out args
    | e_l e_r
    | e_l e_r
    ]; intros ctx t' EQ; cbn [type_cmd] in EQ.
  - destruct (type_expr ctx.(ctxt_pure) e) as [t''|] eqn:TYP; [| discriminate].
    destruct (eqb_spec t t''); [| discriminate]; subst t''.
    inversion EQ; subst.
    apply: wt_ret (Expr.Facts.type_expr_complete TYP).
  - destruct (get_pure id_b ctx) as [[t1 b1]|] eqn:GETP; [| discriminate].
    destruct (eqb_spec t_b t1); [| discriminate]; subst t1.
    destruct (type_cmd ctx c1) as [t_b'|] eqn:TYPb; [| discriminate].
    destruct (eqb_spec t_b t_b'); [| discriminate]; subst t_b'.
    destruct (type_cmd (set_pure id_b (t_b, true) ctx) c2) as [t_c'|] eqn:TYPc;
      [| discriminate].
    destruct (eqb_spec t_c t_c'); [| discriminate]; subst t_c'.
    inversion EQ; subst.
    apply: wt_bind GETP (IHc1 _ _ TYPb) (IHc2 _ _ TYPc).
  - destruct (type_expr ctx.(ctxt_pure) e) as [[ | | | | ] | ] eqn:TYPi; try discriminate.
    destruct (type_cmd ctx c1) as [t_t|] eqn:TYPt; [| discriminate].
    destruct (type_cmd ctx c2) as [t_e|] eqn:TYPe; [| discriminate].
    destruct (eqb_spec t_te t_t); [| discriminate]; subst t_t.
    destruct (eqb_spec t_te t_e); [| discriminate]; subst t_e.
    inversion EQ; subst.
    apply: wt_if (Expr.Facts.type_expr_complete TYPi)
             (IHc1 _ _ TYPt) (IHc2 _ _ TYPe).
  - destruct (get_internal id_cond ctx) as [ [ [ | | | | ] b_c ] | ] eqn:GPcd;
      try discriminate.
    destruct (get_internal id_body ctx) as [ [ [ | | | | ] b_b ] | ] eqn:GPbd;
      try discriminate.
    destruct (type_cmd ctx c1) as [[ | | | | ] | ] eqn:TYPcd; try discriminate.
    destruct (type_cmd ctx c2) as [[ | | | | ] | ] eqn:TYPb; try discriminate.
    inversion EQ; subst.
    apply (wt_while GPcd GPbd (IHc1 _ _ TYPcd) (IHc2 _ _ TYPb)).
  - inversion EQ; subst.
    apply wt_read_var.
  - destruct (type_expr ctx.(ctxt_pure) e) as [t''|] eqn:TYP; [| discriminate].
    destruct (eqb_spec t t''); [| discriminate]; subst t''.
    inversion EQ; subst.
    apply (wt_write_var (Expr.Facts.type_expr_complete TYP)).
  - destruct (find_exf_genv AST.EF_malloc ctx) as [ id_m | ] eqn:SRCH; [ | discriminate ].
    destruct (Pos.eqb id_ptr id_count) eqn:EQpc; [ discriminate | ].
    destruct (Pos.eqb id_ptr id_init) eqn:EQpi; [ discriminate | ].
    destruct (Pos.eqb id_count id_init) eqn:EQci; [ discriminate | ].
    destruct (get_internal id_ptr ctx) as [ [ [ | | | | ] b_p ] | ] eqn:GIp;
      try discriminate.
    destruct (get_internal id_count ctx) as [ [ [ | | | | ] b_c ] | ] eqn:GIc;
      try discriminate.
    destruct (get_internal id_init ctx) as [ [ t_i b_i ] | ] eqn:GIi;
      [ | discriminate ].
    destruct (eqb_spec t t_i); [| discriminate]; subst t_i.
    destruct (type_expr ctx.(ctxt_pure) e_count) as [[ | | | | ] | ] eqn:TYPc; try discriminate.
    destruct (type_expr ctx.(ctxt_pure) e_init) as [t''|] eqn:TYPi; [| discriminate].
    destruct (eqb_spec t t''); [| discriminate]; subst t''.
    inversion EQ; subst.
    apply (wt_alloc_ptr (ex_intro _ id_m (find_exf_genv_correct SRCH))
             GIp GIc GIi
             (proj1 (Pos.eqb_neq id_ptr id_count) EQpc)
             (proj1 (Pos.eqb_neq id_ptr id_init) EQpi)
             (proj1 (Pos.eqb_neq id_count id_init) EQci)
             (Expr.Facts.type_expr_complete TYPc)
             (Expr.Facts.type_expr_complete TYPi)).
  - destruct (type_expr ctx.(ctxt_pure) e_ptr) as [[ | | | | ] | ] eqn:TYPp; try discriminate.
    inversion EQ; subst.
    apply (wt_read_ptr (Expr.Facts.type_expr_complete TYPp)).
  - destruct (type_expr ctx.(ctxt_pure) e_ptr) as [[ | | | | ] | ] eqn:TYPp; try discriminate.
    destruct (type_expr ctx.(ctxt_pure) e_data) as [t''|] eqn:TYPd; [| discriminate].
    destruct (eqb_spec t t''); [| discriminate]; subst t''.
    inversion EQ; subst.
    apply (wt_write_ptr (Expr.Facts.type_expr_complete TYPp)
             (Expr.Facts.type_expr_complete TYPd)).
  - destruct (find_exf_genv AST.EF_free ctx) as [ id_f | ] eqn:SRCH; [ | discriminate ].
    destruct (type_expr ctx.(ctxt_pure) e_ptr) as [[ | | | | ] | ] eqn:TYPp; try discriminate.
    inversion EQ; subst.
    apply (wt_free_ptr (ex_intro _ id_f (find_exf_genv_correct SRCH))
             (Expr.Facts.type_expr_complete TYPp)).
  - destruct (type_expr ctx.(ctxt_pure) e_ptr) as [[ | | | | ] | ] eqn:TYPp; try discriminate.
    destruct (type_expr ctx.(ctxt_pure) e_shift) as [[ | | | | ] | ] eqn:TYPs; try discriminate.
    inversion EQ; subst.
    apply (wt_shift_fw_ptr (Expr.Facts.type_expr_complete TYPp)
             (Expr.Facts.type_expr_complete TYPs)).
  - destruct (type_expr ctx.(ctxt_pure) e_ptr) as [[ | | | | ] | ] eqn:TYPp; try discriminate.
    destruct (type_expr ctx.(ctxt_pure) e_shift) as [[ | | | | ] | ] eqn:TYPs; try discriminate.
    inversion EQ; subst.
    apply (wt_shift_bw_ptr (Expr.Facts.type_expr_complete TYPp)
             (Expr.Facts.type_expr_complete TYPs)).
  - destruct (type_expr ctx.(ctxt_pure) e_l) as [[ | | | | ] | ] eqn:TYPl; try discriminate.
    destruct (type_expr ctx.(ctxt_pure) e_r) as [[ | | | | ] | ] eqn:TYPr; try discriminate.
    inversion EQ; subst.
    apply (wt_ptr_eq (Expr.Facts.type_expr_complete TYPl)
             (Expr.Facts.type_expr_complete TYPr)).
  - destruct (Ctxt.get_global f_id ctx) as [[[fn|ef]|gv]|] eqn:GETG; try discriminate.
    + destruct (eqb_spec t_out fn.(fn_return)); [| discriminate]; subst t_out.
      destruct (ListExt.forall2b eqb (List.map snd fn.(fn_params)) (List.map snd args))
        eqn:EPARAMS; [| discriminate].
      destruct (ListExt.forall2b (fun e t => match type_expr (ctxt_pure ctx) e with Some t' => eqb t' t | None => false end) (List.map fst args) (List.map snd args))
        eqn:ECHK; [| discriminate].
      specialize (ListExt.list_eqb_spec eqb (List.map snd fn.(fn_params))
                    (List.map snd args) eqb_spec) as EL.
      unfold ListExt.list_eqb in EL; rewrite EPARAMS in EL.
      inversion EL as [EARGS|]; subst.
      inversion EQ; subst.
      apply (wt_app GETG EARGS (Expr.Facts.forall2b_type_expr_forall2_wt_expr ECHK)).
    + destruct ef as [ nm sg | | | | | | | | | | | ]; try discriminate.
      destruct (Facts.ef_sig_dec (AST.EF_external nm sg)) as [sig|] eqn:DEC; [| discriminate].
      destruct (eqb_spec sig {| sig_args := List.map snd args; sig_res := t_out |});
        [| discriminate]; subst sig.
      destruct (ListExt.forall2b (fun e t => match type_expr (ctxt_pure ctx) e with Some t' => eqb t' t | None => false end) (List.map fst args) (List.map snd args))
        eqn:ECHK; [| discriminate].
      injection EQ as <-.
      apply (wt_app_exf (nm := nm) (sg := sg));
        [ exact GETG | exact (proj2 (Facts.ef_sig_dec_spec _ _) DEC)
        | exact (Expr.Facts.forall2b_type_expr_forall2_wt_expr ECHK) ].
  - destruct (type_expr ctx.(ctxt_pure) e_l) as [[ | | | | ] | ] eqn:TYPl; try discriminate.
    destruct (type_expr ctx.(ctxt_pure) e_r) as [[ | | | | ] | ] eqn:TYPr; try discriminate.
    inversion EQ; subst.
    apply (wt_div (Expr.Facts.type_expr_complete TYPl)
             (Expr.Facts.type_expr_complete TYPr)).
  - destruct (type_expr ctx.(ctxt_pure) e_l) as [[ | | | | ] | ] eqn:TYPl; try discriminate.
    destruct (type_expr ctx.(ctxt_pure) e_r) as [[ | | | | ] | ] eqn:TYPr; try discriminate.
    inversion EQ; subst.
    apply (wt_mod (Expr.Facts.type_expr_complete TYPl)
             (Expr.Facts.type_expr_complete TYPr)).
Qed.

Definition type_p_extra (p: program): bool := true.

Lemma type_p_extra_spec p: Bool.reflect (wt_p_extra p) (type_p_extra p).
Proof.
  exact (ReflectT _ I).
Qed.

Definition type_function := Prog.type_function (cmd := cmd) (f_extra := f_extra) type_cmd type_f_extra.

Definition type_fundef := Prog.type_fundef (cmd := cmd) (f_extra := f_extra) type_cmd type_f_extra.

Definition type_globvar := Prog.type_globvar (cmd := cmd) (f_extra := f_extra).

Definition type_globdef := Prog.type_globdef (cmd := cmd) (f_extra := f_extra) type_cmd type_f_extra.

Definition type_prog_defs := Prog.type_prog_defs (cmd := cmd) (f_extra := f_extra) type_cmd type_f_extra.

Definition type_program :=
  Prog.type_program (cmd := cmd) (f_extra := f_extra) (p_extra := p_extra)
    type_cmd type_f_extra type_p_extra.

Lemma type_function_correct ctx func:
  type_function ctx func = true -> wt_function ctx func.
Proof.
  apply Prog.type_function_correct;
    [ apply type_cmd_correct | apply type_f_extra_correct ].
Qed.

Lemma type_function_complete ctx func:
  wt_function ctx func -> type_function ctx func = true.
Proof.
  apply Prog.type_function_complete;
    [ apply type_cmd_complete | apply type_f_extra_complete ].
Qed.

Lemma type_fundef_correct ctx fd:
  type_fundef ctx fd = true -> wt_fundef ctx fd.
Proof.
  apply Prog.type_fundef_correct;
    [ apply type_cmd_correct | apply type_f_extra_correct ].
Qed.

Lemma type_fundef_complete ctx fd:
  wt_fundef ctx fd -> type_fundef ctx fd = true.
Proof.
  apply Prog.type_fundef_complete;
    [ apply type_cmd_complete | apply type_f_extra_complete ].
Qed.

Lemma type_globdef_spec ctx id gd:
  Bool.reflect (wt_globdef ctx id gd) (type_globdef ctx id gd).
Proof.
  apply Prog.type_globdef_spec;
    [ apply type_cmd_complete | apply type_cmd_correct
    | apply type_f_extra_complete | apply type_f_extra_correct ].
Qed.

Lemma type_program_spec p:
  Bool.reflect (wt_program p) (type_program p).
Proof.
  apply Prog.type_program_spec;
    [ apply type_cmd_complete | apply type_cmd_correct
    | apply type_f_extra_complete | apply type_f_extra_correct
    | apply type_p_extra_spec ].
Qed.

Lemma type_program_complete [p]: wt_program p -> type_program p = true.
Proof.
  intro WT; exact (proj1 (Bool.reflect_iff _ _ (type_program_spec p)) WT).
Qed.

Lemma wt_glob_fundef [p: program] (WT: wt_program p)
  [id fd] (GET: Ctxt.get_global id (mk_glob_ctxt p) = Some (AST.Gfun fd)) :
  wt_fundef (mk_glob_ctxt p) fd.
Proof.
  unfold Ctxt.get_global in GET.
  destruct (Globalenvs.Genv.find_symbol
              (Ctxt.ctxt_global (mk_glob_ctxt p)) id) as [ b | ] eqn:SYMB;
    [ | discriminate GET ].
  destruct (Globalenvs.Genv.find_def_inversion _ _ GET) as ( id' & IN ).
  pose proof (proj1 (Forall_forall _ _)
                (Prog.Facts.wt_prog_defs_Forall wt_cmd_incl_global_stack p WT) _ IN) as WTg.
  cbn in WTg.
  inversion WTg; subst; assumption.
Qed.
