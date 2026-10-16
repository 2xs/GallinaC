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

From Stdlib Require Import PArith NArith Arith List.

From compcert.common Require Globalenvs.
From compcert.lib Require Import Maps.

From GallinaC.Utils Require Import Algebra ReflectExt.

From GallinaC.Imp Require Import Uint32 Uintptr.

From GallinaC.Compiler.Common Require Import Ctxt Value Types Expr.
From GallinaC.Compiler.Deep Require Import Cmd Prog.

Fixpoint type_cmd (ty_ctxt: ctxt (type * bool) (type * bool) unit fundef vardef) c: option type :=
  match c with
  | c_ret e => type_expr ty_ctxt.(ctxt_pure) e
  | c_bind b_id t_b c_b c_c =>
      match get_pure b_id ty_ctxt with
      | Some (t1, false) =>
          if eqb t_b t1 then
            match type_cmd ty_ctxt c_b with
            | Some t_b' =>
                if eqb t_b t_b' then
                  match type_cmd (set_pure b_id (t_b, true) ty_ctxt) c_c with
                  | Some t_c => Some (t_c)
                  | None => None
                  end
                else
                  None
            | None => None
            end
          else None
      | _ => None
      end
  | c_if e_i c_t c_e =>
      match type_expr ty_ctxt.(ctxt_pure) e_i with
      | Some t_bool =>
          match type_cmd ty_ctxt c_t, type_cmd ty_ctxt c_e with
          | Some t_t, Some t_e =>
              if eqb t_t t_e then
                Some t_t
              else
                None
          | _, _ => None
          end
      | _ => None
      end
  | c_while c_cond c_body =>
      match type_cmd ty_ctxt c_cond, type_cmd ty_ctxt c_body with
      | Some t_bool, Some t_unit => Some t_unit
      | _, _ => None
      end
  | c_with_var t_v e_v c_c =>
      match type_expr ty_ctxt.(ctxt_pure) e_v, type_cmd (push_stack tt ty_ctxt) c_c with
      | Some t_v', Some t_c =>
          if eqb t_v t_v' then Some t_c else None
      | _, _ => None
      end
  | c_read_var n t =>
      match get_stack n ty_ctxt with
      | Some tt => Some t
      | None => None
      end
  | c_write_var n t e =>
      match type_expr ty_ctxt.(ctxt_pure) e, get_stack n ty_ctxt with
      | Some t', Some tt => if eqb t t' then Some t_unit else None
      | _, _ => None
      end
  | c_alloc_ptr e_size t t_init =>
      match find_exf_genv AST.EF_malloc ty_ctxt with
      | Some _ =>
          match type_expr ty_ctxt.(ctxt_pure) e_size, type_expr ty_ctxt.(ctxt_pure) t_init with
          | Some t_ofst, Some t' => if eqb t t' then Some t_ptr else None
          | _, _ => None
          end
      | None => None
      end
  | c_read_ptr e_ptr t =>
      match type_expr ty_ctxt.(ctxt_pure) e_ptr with
      | Some t_ptr => Some t
      | _ => None
      end
  | c_write_ptr e_ptr t e_val =>
      match type_expr ty_ctxt.(ctxt_pure) e_ptr, type_expr ty_ctxt.(ctxt_pure) e_val with
      | Some t_ptr, Some t' => if eqb t t' then Some t_unit else None
      | _, _ => None
      end
  | c_free_ptr e_ptr =>
      match find_exf_genv AST.EF_free ty_ctxt with
      | Some _ =>
          match type_expr ty_ctxt.(ctxt_pure) e_ptr with
          | Some t_ptr => Some t_unit
          | _ => None
          end
      | None => None
      end
  | c_shift_fw_ptr e_ptr e_shift | c_shift_bw_ptr e_ptr e_shift =>
                                     match type_expr ty_ctxt.(ctxt_pure) e_ptr, type_expr ty_ctxt.(ctxt_pure) e_shift with
                                     | Some t_ptr, Some t_ofst => Some t_ptr
                                     | _, _ => None
                                     end
  | c_ptr_eq e_ptr_l e_ptr_r =>
      match type_expr ty_ctxt.(ctxt_pure) e_ptr_l, type_expr ty_ctxt.(ctxt_pure) e_ptr_r with
      | Some t_ptr, Some t_ptr => Some t_bool
      | _, _ => None
      end
  | c_app f_id args =>
      match Ctxt.get_global f_id ty_ctxt, ListExt.map_opt (type_expr ty_ctxt.(ctxt_pure)) args with
      | Some (AST.Gfun (AST.Internal fn)), Some t_args =>
          if ListExt.forall2b eqb t_args (List.map snd fn.(fn_params)) then
            Some fn.(fn_return)
          else
            None
      | Some (AST.Gfun (AST.External (AST.EF_external nm sg))), Some t_args =>
          match Facts.ef_sig_dec (AST.EF_external nm sg) with
          | Some sig =>
              if ListExt.forall2b eqb t_args sig.(sig_args) then
                Some sig.(sig_res)
              else
                None
          | None => None
          end
      | _, _ => None
      end
  | c_div e_l e_r =>
      match type_expr ty_ctxt.(ctxt_pure) e_l, type_expr ty_ctxt.(ctxt_pure) e_r with
      | Some t_nat, Some t_nat => Some t_nat
      | _, _ => None
      end
  | c_mod e_l e_r =>
      match type_expr ty_ctxt.(ctxt_pure) e_l, type_expr ty_ctxt.(ctxt_pure) e_r with
      | Some t_nat, Some t_nat => Some t_nat
      | _, _ => None
      end
  end.

Inductive wt_cmd: ctxt (type * bool) (type * bool) unit fundef vardef -> cmd -> type -> Prop :=
| wt_ret : forall {ty_ctxt e t}
                  (WTe: wt_expr ty_ctxt.(ctxt_pure) e t),
    wt_cmd ty_ctxt (c_ret e) t
| wt_bind : forall {ty_ctxt x c1 c2 t1 t2}
                   (UNBOUND: get_pure x ty_ctxt = Some (t1, false))
                   (WTm: wt_cmd ty_ctxt c1 t1)
                   (WTf: wt_cmd (set_pure x (t1, true) ty_ctxt) c2 t2),
    wt_cmd ty_ctxt (c_bind x t1 c1 c2) t2
| wt_if : forall {ty_ctxt e c1 c2 t}
                 (WTcond:wt_expr ty_ctxt.(ctxt_pure) e t_bool)
                 (WTthen: wt_cmd ty_ctxt c1 t)
                 (WTelse: wt_cmd ty_ctxt c2 t),
    wt_cmd ty_ctxt (c_if e c1 c2) t
| wt_while: forall {ty_ctxt c_cond c_body}
                   (WTcond: wt_cmd ty_ctxt c_cond t_bool) (WTbody: wt_cmd ty_ctxt c_body t_unit),
    wt_cmd ty_ctxt (c_while c_cond c_body) t_unit
| wt_with_var: forall {ty_ctxt t_v e_v c_c t_c}
                      (WTinit: wt_expr ty_ctxt.(ctxt_pure) e_v t_v) (WTcont: wt_cmd (push_stack tt ty_ctxt) c_c t_c),
    wt_cmd ty_ctxt (c_with_var t_v e_v c_c) t_c
| wt_read_var : forall {ty_ctxt} {n} {t}
                       (Nth: get_stack n ty_ctxt = Some tt),
    wt_cmd ty_ctxt (c_read_var n t) t
| wt_write_var : forall {ty_ctxt} {n} {e t}
                        (WT: wt_expr ty_ctxt.(ctxt_pure) e t)
                        (Nth: get_stack n ty_ctxt = Some tt),
    wt_cmd ty_ctxt (c_write_var n t e) t_unit
| wt_alloc_ptr : forall {ty_ctxt n t e}
                        (MALLOC: exf_bound AST.EF_malloc ty_ctxt)
                        (WTsize: wt_expr ty_ctxt.(ctxt_pure) n t_ofst)
                        (WTinit: wt_expr ty_ctxt.(ctxt_pure) e t),
    wt_cmd ty_ctxt (c_alloc_ptr n t e) t_ptr
| wt_read_ptr : forall {ty_ctxt t p}
                       (WTptr: wt_expr ty_ctxt.(ctxt_pure) p t_ptr),
    wt_cmd ty_ctxt (c_read_ptr p t) t
| wt_write_ptr : forall {ty_ctxt p t e}
                        (WTptr: wt_expr ty_ctxt.(ctxt_pure) p t_ptr)
                        (WTval: wt_expr ty_ctxt.(ctxt_pure) e t),
    wt_cmd ty_ctxt (c_write_ptr p t e) t_unit
| wt_free_ptr : forall {ty_ctxt p}
                       (FREE: exf_bound AST.EF_free ty_ctxt)
                       (WTptr: wt_expr ty_ctxt.(ctxt_pure) p t_ptr),
    wt_cmd ty_ctxt (c_free_ptr p) t_unit
| wt_shift_fw_ptr: forall {ty_ctxt p n}
                          (WTptr: wt_expr ty_ctxt.(ctxt_pure) p t_ptr)
                          (WTofst: wt_expr ty_ctxt.(ctxt_pure) n t_ofst),
    wt_cmd ty_ctxt (c_shift_fw_ptr p n) t_ptr
| wt_shift_bw_ptr: forall {ty_ctxt p n}
                          (WTptr: wt_expr ty_ctxt.(ctxt_pure) p t_ptr)
                          (WTofst: wt_expr ty_ctxt.(ctxt_pure) n t_ofst),
    wt_cmd ty_ctxt (c_shift_bw_ptr p n) t_ptr
| wt_ptr_eq: forall {ty_ctxt p1 p2}
                    (WTl: wt_expr ty_ctxt.(ctxt_pure) p1 t_ptr)
                    (WTr: wt_expr ty_ctxt.(ctxt_pure) p2 t_ptr),
    wt_cmd ty_ctxt (c_ptr_eq p1 p2) t_bool
| wt_app : forall
    {ty_ctxt f_id args fn t_out}
    (FINDFN: Ctxt.get_global f_id ty_ctxt = Some (AST.Gfun (AST.Internal fn)))
    (RETURN: t_out = fn.(fn_return))
    (WT_args: Forall2 (wt_expr ty_ctxt.(ctxt_pure)) args (List.map snd fn.(fn_params))),
    wt_cmd ty_ctxt (c_app f_id args) t_out
| wt_app_exf : forall
    {ty_ctxt f_id args nm sg sig t_out}
    (FINDFN: Ctxt.get_global f_id ty_ctxt = Some (AST.Gfun (AST.External (AST.EF_external nm sg))))
    (SIG: exf_funsig (AST.EF_external nm sg) sig)
    (RETURN: t_out = sig.(sig_res))
    (WT_args: Forall2 (wt_expr ty_ctxt.(ctxt_pure)) args sig.(sig_args)),
    wt_cmd ty_ctxt (c_app f_id args) t_out
| wt_div: forall {ty_ctxt e_l e_r}
                 (WTl: wt_expr ty_ctxt.(ctxt_pure) e_l t_nat)
                 (WTr: wt_expr ty_ctxt.(ctxt_pure) e_r t_nat),
    wt_cmd ty_ctxt (c_div e_l e_r) t_nat
| wt_mod: forall {ty_ctxt e_l e_r}
                 (WTl: wt_expr ty_ctxt.(ctxt_pure) e_l t_nat)
                 (WTr: wt_expr ty_ctxt.(ctxt_pure) e_r t_nat),
    wt_cmd ty_ctxt (c_mod e_l e_r) t_nat
.

(* Global-env monotonicity for [wt_cmd]

If a command is well-typed under a context, then it is well-typed under another
context, if that second context shares the same pure and stack environment, and
the second's global environment at least contains all bindings present in the
first one's.

 *)
Lemma wt_cmd_incl_global [ctx c t] (WT: wt_cmd ctx c t) :
  forall (ctx': ctxt (type * bool) (type * bool) unit fundef vardef),
    ctxt_pure ctx = ctxt_pure ctx' ->
    ctxt_stack ctx = ctxt_stack ctx' ->
    (forall id g, Ctxt.get_global id ctx = Some g -> Ctxt.get_global id ctx' = Some g) ->
    wt_cmd ctx' c t.
Proof.
  elim: WT => {ctx c t} [
      ty_ctxt e t WTe
    | ty_ctxt x c1 c2 t1 t2 UNBOUND WTm IHWTm WTf IHWTf
    | ty_ctxt e c1 c2 t WTcond WTthen IHWTthen WTelse IHWTelse
    | ty_ctxt c_cond c_body WTcond IHWTcond WTbody IHWTbody
    | ty_ctxt t_v e_v c_c t_c WTinit WTcont IHWTcont
    | ty_ctxt n t Nth
    | ty_ctxt n e t WT Nth
    | ty_ctxt n t e MALLOC WTsize WTinit
    | ty_ctxt t p WTptr
    | ty_ctxt p t e WTptr WTval
    | ty_ctxt p FREE WTptr
    | ty_ctxt p n WTptr WTofst
    | ty_ctxt p n WTptr WTofst
    | ty_ctxt p1 p2 WTl WTr
    | ty_ctxt f_id args fn t_out FINDFN -> WT_args
    | ty_ctxt f_id args nm sg sig t_out FINDFN SIG -> WT_args
    | ty_ctxt e_l e_r WTl WTr
    | ty_ctxt e_l e_r WTl WTr
    ] ty_ctxt' PURE STACK MONO.
  - by apply: wt_ret; rewrite -PURE.
  - apply: (wt_bind (t1 := t1)); first by rewrite /get_pure -PURE.
    + exact: IHWTm.
    + apply: IHWTf => /=.
      * by rewrite PURE.
      * exact: STACK.
      * move=> id g; rewrite !Ctxt.Facts.get_global_set_pure; exact: MONO.
  - by apply: wt_if; [rewrite -PURE | exact: IHWTthen | exact: IHWTelse].
  - by apply: wt_while; [exact: IHWTcond | exact: IHWTbody].
  - apply: wt_with_var; first by rewrite -PURE.
    apply: IHWTcont.
    + exact: PURE.
    + by rewrite /push_stack /= STACK.
    + move=> id g; rewrite !Ctxt.Facts.get_global_with_stack; exact: MONO.
  - by apply: wt_read_var; rewrite /get_stack -STACK.
  - by apply: wt_write_var; [rewrite -PURE | rewrite /get_stack -STACK].
  - apply: wt_alloc_ptr; [ | by rewrite -PURE | by rewrite -PURE ].
    by case: MALLOC => id_m GET; exists id_m; exact: MONO.
  - by apply: wt_read_ptr; rewrite -PURE.
  - by apply: wt_write_ptr; rewrite -PURE.
  - apply: wt_free_ptr; last by rewrite -PURE.
    by case: FREE => id_f GET; exists id_f; exact: MONO.
  - by apply: wt_shift_fw_ptr; rewrite -PURE.
  - by apply: wt_shift_bw_ptr; rewrite -PURE.
  - by apply: wt_ptr_eq; rewrite -PURE.
  - apply: (wt_app (fn := fn)); [exact: MONO | by [] | ].
    by move: WT_args; apply: Forall2_impl => e t' WTe'; rewrite -PURE.
  - apply: (wt_app_exf (nm := nm) (sg := sg) (sig := sig)); [exact: MONO | exact: SIG | by [] | ].
    by move: WT_args; apply: Forall2_impl => e t' WTe'; rewrite -PURE.
  - by apply: wt_div; rewrite -PURE.
  - by apply: wt_mod; rewrite -PURE.
Qed.

Lemma type_cmd_complete [ctx c t] (WT: wt_cmd ctx c t): type_cmd ctx c = Some t.
Proof.
  elim: WT => {ctx c t} [
      ty_ctxt e t WTe
    | ty_ctxt x c1 c2 t1 t2 UNBOUND WTm IHWTm WTf IHWTf
    | ty_ctxt e c1 c2 t WTcond WTthen IHWTthen WTelse IHWTelse
    | ty_ctxt c_cond c_body WTcond IHWTcond WTbody IHWTbody
    | ty_ctxt t_v e_v c_c t_c WTinit WTcont IHWTcont
    | ty_ctxt n t Nth
    | ty_ctxt n e t WT Nth
    | ty_ctxt n t e MALLOC WTsize WTinit
    | ty_ctxt t p WTptr
    | ty_ctxt p t e WTptr WTval
    | ty_ctxt p FREE WTptr
    | ty_ctxt p n WTptr WTofst
    | ty_ctxt p n WTptr WTofst
    | ty_ctxt p1 p2 WTl WTr
    | ty_ctxt f_id args fn t_out FINDFN -> WT_args
    | ty_ctxt f_id args nm sg sig t_out FINDFN SIG -> WT_args
    | ty_ctxt e_l e_r WTl WTr
    | ty_ctxt e_l e_r WTl WTr
    ] /=.
  - exact: Expr.Facts.type_expr_correct.
  - by rewrite UNBOUND (reflect_refl eqb_spec _) IHWTm (reflect_refl eqb_spec _) IHWTf.
  - by rewrite (Expr.Facts.type_expr_correct WTcond) IHWTthen IHWTelse (reflect_refl eqb_spec _).
  - by rewrite IHWTcond IHWTbody.
  - by rewrite (Expr.Facts.type_expr_correct WTinit) IHWTcont (reflect_refl eqb_spec _).
  - by rewrite Nth.
  - by rewrite (Expr.Facts.type_expr_correct WT) Nth (reflect_refl eqb_spec _).
  - case: MALLOC => id_m GET.
    case: (find_exf_genv_complete (ef := AST.EF_malloc) GET) => id_m' SRCH.
    by rewrite SRCH (Expr.Facts.type_expr_correct WTsize)
      (Expr.Facts.type_expr_correct WTinit) (reflect_refl eqb_spec _).
  - by rewrite (Expr.Facts.type_expr_correct WTptr).
  - by rewrite (Expr.Facts.type_expr_correct WTptr)
      (Expr.Facts.type_expr_correct WTval) (reflect_refl eqb_spec _).
  - case: FREE => id_f GET.
    case: (find_exf_genv_complete (ef := AST.EF_free) GET) => id_f' SRCH.
    by rewrite SRCH (Expr.Facts.type_expr_correct WTptr).
  - by rewrite (Expr.Facts.type_expr_correct WTptr) (Expr.Facts.type_expr_correct WTofst).
  - by rewrite (Expr.Facts.type_expr_correct WTptr) (Expr.Facts.type_expr_correct WTofst).
  - by rewrite (Expr.Facts.type_expr_correct WTl) (Expr.Facts.type_expr_correct WTr).
  - rewrite FINDFN (ListExt.map_opt_Forall2 (@Expr.Facts.type_expr_correct _) WT_args).
    by rewrite (ListExt.list_eqb_refl eqb eqb_spec : forall l, ListExt.forall2b eqb l l = true).
  - rewrite FINDFN (ListExt.map_opt_Forall2 (@Expr.Facts.type_expr_correct _) WT_args).
    rewrite (proj1 (Facts.ef_sig_dec_spec _ sig) SIG).
    by rewrite (ListExt.list_eqb_refl eqb eqb_spec : forall l, ListExt.forall2b eqb l l = true).
  - by rewrite (Expr.Facts.type_expr_correct WTl) (Expr.Facts.type_expr_correct WTr).
  - by rewrite (Expr.Facts.type_expr_correct WTl) (Expr.Facts.type_expr_correct WTr).
Qed.

Lemma type_cmd_correct [ctx c t] (EQ: type_cmd ctx c = Some t): wt_cmd ctx c t.
Proof.
  elim: c ctx t EQ => [
      e
    | id_b t_b c1 IHc1 c2 IHc2
    | e_if c1 IHc1 c2 IHc2
    | c1 IHc1 c2 IHc2
    | t_v e_v c IHc
    | o_v t_v
    | o_v t_v e_v
    | e_size t_init e_init
    | e_ptr t_val
    | e_ptr t_val e_val
    | e_ptr
    | e_ptr e_ofst
    | e_ptr e_ofst
    | e_ptr_l e_ptr_r
    | f_id args
    | e_l e_r
    | e_l e_r
    ] ctx t /=.
  - by move=> EQ; apply/wt_ret/Expr.Facts.type_expr_complete.
  - case GETP: (get_pure id_b ctx) => [ [t1 [ | ]] | ] //.
    case: (eqb_spec t_b t1) => // E; subst t1.
    case TYPb: (type_cmd ctx c1) => [ t_b' | ] //.
    case: (eqb_spec t_b t_b') => // E; subst t_b'.
    case TYPc: (type_cmd (set_pure id_b (t_b, true) ctx) c2) => [ t_c | ] // [<-].
    exact: (wt_bind GETP (IHc1 _ _ TYPb) (IHc2 _ _ TYPc)).
  - case TYPi: (type_expr (ctxt_pure ctx) e_if) => [ [ | | | | ] | ] //.
    case TYPt: (type_cmd ctx c1) => [ t_t | ] //.
    case TYPe: (type_cmd ctx c2) => [ t_e | ] //.
    case: (eqb_spec t_t t_e) => // E [<-]; subst t_e.
    exact: (wt_if (Expr.Facts.type_expr_complete TYPi) (IHc1 _ _ TYPt) (IHc2 _ _ TYPe)).
  - case TYPcd: (type_cmd ctx c1) => [ [ | | | | ] | ] //.
    case TYPb: (type_cmd ctx c2) => [ [ | | | | ] | ] // [<-].
    exact: (wt_while (IHc1 _ _ TYPcd) (IHc2 _ _ TYPb)).
  - case TYPv: (type_expr (ctxt_pure ctx) e_v) => [ t_v' | ] //.
    case TYPc: (type_cmd (push_stack tt ctx) c) => [ t_c | ] //.
    case: (eqb_spec t_v t_v') => // E [<-]; subst t_v'.
    exact: (wt_with_var (Expr.Facts.type_expr_complete TYPv) (IHc _ _ TYPc)).
  - case NTH: (get_stack o_v ctx) => [ [] | ] // [<-].
    exact: (wt_read_var NTH).
  - case TYPv: (type_expr (ctxt_pure ctx) e_v) => [ t' | ] //.
    case NTH: (get_stack o_v ctx) => [ [] | ] //.
    case: (eqb_spec t_v t') => // E [<-]; subst t'.
    exact: (wt_write_var (Expr.Facts.type_expr_complete TYPv) NTH).
  - case SRCH: (find_exf_genv AST.EF_malloc ctx) => [ id_m | ] //.
    case TYPs: (type_expr (ctxt_pure ctx) e_size) => [ [ | | | | ] | ] //.
    case TYPi: (type_expr (ctxt_pure ctx) e_init) => [ t' | ] //.
    case: (eqb_spec t_init t') => // E [<-]; subst t'.
    exact: (wt_alloc_ptr (ex_intro _ id_m (find_exf_genv_correct SRCH))
              (Expr.Facts.type_expr_complete TYPs) (Expr.Facts.type_expr_complete TYPi)).
  - case TYPp: (type_expr (ctxt_pure ctx) e_ptr) => [ [ | | | | ] | ] // [<-].
    exact: (wt_read_ptr (Expr.Facts.type_expr_complete TYPp)).
  - case TYPp: (type_expr (ctxt_pure ctx) e_ptr) => [ [ | | | | ] | ] //.
    case TYPv: (type_expr (ctxt_pure ctx) e_val) => [ t' | ] //.
    case: (eqb_spec t_val t') => // E [<-]; subst t'.
    exact: (wt_write_ptr (Expr.Facts.type_expr_complete TYPp)
              (Expr.Facts.type_expr_complete TYPv)).
  - case SRCH: (find_exf_genv AST.EF_free ctx) => [ id_f | ] //.
    case TYPp: (type_expr (ctxt_pure ctx) e_ptr) => [ [ | | | | ] | ] // [<-].
    exact: (wt_free_ptr (ex_intro _ id_f (find_exf_genv_correct SRCH))
              (Expr.Facts.type_expr_complete TYPp)).
  - case TYPp: (type_expr (ctxt_pure ctx) e_ptr) => [ [ | | | | ] | ] //.
    case TYPo: (type_expr (ctxt_pure ctx) e_ofst) => [ [ | | | | ] | ] // [<-].
    exact: (wt_shift_fw_ptr (Expr.Facts.type_expr_complete TYPp)
              (Expr.Facts.type_expr_complete TYPo)).
  - case TYPp: (type_expr (ctxt_pure ctx) e_ptr) => [ [ | | | | ] | ] //.
    case TYPo: (type_expr (ctxt_pure ctx) e_ofst) => [ [ | | | | ] | ] // [<-].
    exact: (wt_shift_bw_ptr (Expr.Facts.type_expr_complete TYPp)
              (Expr.Facts.type_expr_complete TYPo)).
  - case TYPl: (type_expr (ctxt_pure ctx) e_ptr_l) => [ [ | | | | ] | ] //.
    case TYPr: (type_expr (ctxt_pure ctx) e_ptr_r) => [ [ | | | | ] | ] // [<-].
    exact: (wt_ptr_eq (Expr.Facts.type_expr_complete TYPl)
              (Expr.Facts.type_expr_complete TYPr)).
  - case GET: (Ctxt.get_global f_id ctx) => [ [ [fn | [ nm sg | | | | | | | | | | | ] ] | gv] | ] //.
    + case WTargs: (ListExt.map_opt (type_expr (ctxt_pure ctx)) args) => [ t_args | ] //.
      rewrite -[ListExt.forall2b _ _ _]/(ListExt.list_eqb _ _ _).
      case: (ListExt.list_eqb_spec eqb t_args _ eqb_spec) => // E [<-]; subst t_args.
      exact: (wt_app GET erefl
                (ListExt.map_opt_Forall2_inv (@Expr.Facts.type_expr_complete _) WTargs)).
    + case WTargs: (ListExt.map_opt (type_expr (ctxt_pure ctx)) args) => [ t_args | ] //.
      case Edec: (Facts.ef_sig_dec (AST.EF_external nm sg)) => [ sig | ] //.
      rewrite -[ListExt.forall2b _ _ _]/(ListExt.list_eqb _ _ _).
      case: (ListExt.list_eqb_spec eqb t_args _ eqb_spec) => // E [<-]; subst t_args.
      exact: (wt_app_exf GET (proj2 (Facts.ef_sig_dec_spec _ sig) Edec) erefl
                (ListExt.map_opt_Forall2_inv (@Expr.Facts.type_expr_complete _) WTargs)).
  - case WTl: (type_expr (ctxt_pure ctx) e_l) => [ [ | | | | ] | ] //.
    case WTr: (type_expr (ctxt_pure ctx) e_r) => [ [ | | | | ] | ] // [<-].
    exact: (wt_div (Expr.Facts.type_expr_complete WTl) (Expr.Facts.type_expr_complete WTr)).
  - case WTl: (type_expr (ctxt_pure ctx) e_l) => [ [ | | | | ] | ] //.
    case WTr: (type_expr (ctxt_pure ctx) e_r) => [ [ | | | | ] | ] // [<-].
    exact: (wt_mod (Expr.Facts.type_expr_complete WTl) (Expr.Facts.type_expr_complete WTr)).
Qed.

Definition wt_f_extra (f_extra: unit): Prop := True.

Record wt_p_extra (p: program): Prop :=
  {
    wt_prog_malloc_unique: unique_exf AST.EF_malloc p.(prog_defs);
    wt_prog_free_unique: unique_exf AST.EF_free p.(prog_defs);
  }.
Arguments wt_prog_malloc_unique [p]: rename.
Arguments wt_prog_free_unique [p]: rename.

Definition type_p_extra (p: program): bool :=
  unique_exfb p.(prog_defs) AST.EF_malloc
  && unique_exfb p.(prog_defs) AST.EF_free.

Definition wt_function := wt_function unit wt_f_extra wt_cmd.

Definition wt_fundef := wt_fundef unit wt_f_extra wt_cmd.

Definition wt_fundef_call [Ad Pt] := @wt_fundef_call Ad Pt cmd unit.

Notation wt_globvar := Prog.wt_globvar.

Definition wt_globdef := wt_globdef unit wt_f_extra wt_cmd.

Definition wt_program := wt_program wt_f_extra wt_cmd wt_p_extra.
Definition type_function := Prog.type_function (cmd := cmd) (f_extra := unit) type_cmd (fun _ => true).
Definition type_fundef := Prog.type_fundef (cmd := cmd) (f_extra := unit) type_cmd (fun _ => true).
Definition type_globvar := Prog.type_globvar (cmd := cmd) (f_extra := unit).
Definition type_globdef := Prog.type_globdef (cmd := cmd) (f_extra := unit) type_cmd (fun _ => true).
Definition type_prog_defs := Prog.type_prog_defs (cmd := cmd) (f_extra := unit) type_cmd (fun _ => true).
Definition type_program := Prog.type_program (cmd := cmd) (f_extra := unit) (p_extra := p_extra) type_cmd (fun _ => true) type_p_extra.

Lemma wt_f_extra_complete (fx: unit): wt_f_extra fx -> (fun _: unit => true) fx = true.
Proof. by []. Qed.

Lemma wt_f_extra_correct (fx: unit): (fun _: unit => true) fx = true -> wt_f_extra fx.
Proof. by []. Qed.

Lemma wt_p_extra_spec (p: program): Bool.reflect (wt_p_extra p) (type_p_extra p).
Proof.
  rewrite /type_p_extra; apply: (iffP andP).
  - by move=> [CM CF]; split; apply/unique_exfb_spec.
  - by move=> [UM UF]; split; apply/unique_exfb_spec.
Qed.

Lemma type_function_correct ctx func:
  type_function ctx func = true -> wt_function ctx func.
Proof.
  by apply: Prog.type_function_correct; [exact: type_cmd_correct | exact: wt_f_extra_correct].
Qed.

Lemma type_function_complete ctx func:
  wt_function ctx func -> type_function ctx func = true.
Proof.
  by apply: Prog.type_function_complete; [exact: type_cmd_complete | exact: wt_f_extra_complete].
Qed.

Lemma type_fundef_correct ctx fd:
  type_fundef ctx fd = true -> wt_fundef ctx fd.
Proof.
  by apply: Prog.type_fundef_correct; [exact: type_cmd_correct | exact: wt_f_extra_correct].
Qed.

Lemma type_fundef_complete ctx fd:
  wt_fundef ctx fd -> type_fundef ctx fd = true.
Proof.
  by apply: Prog.type_fundef_complete; [exact: type_cmd_complete | exact: wt_f_extra_complete].
Qed.

Lemma type_globvar_spec ctx id gv:
  Bool.reflect (wt_globvar id gv) (type_globvar ctx id gv).
Proof. exact: Prog.type_globvar_spec. Qed.

Lemma type_globdef_spec ctx id gd:
  Bool.reflect (wt_globdef ctx id gd) (type_globdef ctx id gd).
Proof.
  by apply: Prog.type_globdef_spec;
    [ exact: type_cmd_complete | exact: type_cmd_correct
    | exact: wt_f_extra_complete | exact: wt_f_extra_correct ].
Qed.

Lemma type_program_spec p:
  Bool.reflect (wt_program p) (type_program p).
Proof.
  by apply: Prog.type_program_spec;
    [ exact: type_cmd_complete | exact: type_cmd_correct
    | exact: wt_f_extra_complete | exact: wt_f_extra_correct
    | exact: wt_p_extra_spec ].
Qed.

Lemma type_program_complete [p]: wt_program p -> type_program p = true.
Proof. by move/type_program_spec. Qed.

(* Usually, global definitions are typed incrementally. The first type checks
in an empty global environment. The second in a global environment contains only
the first, etc. Just like definitions are typed in a Gallina module.

 This lemma shows that global definitions remain well-typed, if they are typed
 in a global environment composed of all global definitions.

 *)
Lemma wt_prog_defs_Forall (p: program) (WT: wt_program p) :
  Forall (fun idglob => wt_globdef (mk_glob_ctxt p) (fst idglob) (snd idglob)) p.(prog_defs).
Proof.
  (* [wt_cmd_incl_global] defines arguments in a different order than
     [wt_prog_defs_Forall] expects them. Hence, we manually shuffle them around. *)
  exact: (Prog.Facts.wt_prog_defs_Forall
            (wt_cmd := wt_cmd)
            (fun ctx ctx' PURE INTERNAL STACK MONO c t WTc =>
               wt_cmd_incl_global WTc ctx' PURE STACK MONO)
            p WT).
Qed.

Lemma wt_glob_fundef (p: program) (WT: wt_program p)
  id fd (GET: get_global id (mk_glob_ctxt p) = Some (AST.Gfun fd)) :
  wt_fundef (mk_glob_ctxt p) fd.
Proof.
  move: GET; rewrite /get_global.
  case SYMB: (Globalenvs.Genv.find_symbol (ctxt_global (mk_glob_ctxt p)) id) => [ b | ] // GET.
  case: (Globalenvs.Genv.find_def_inversion _ _ GET) => id' IN.
  have := proj1 (Forall_forall _ _) (wt_prog_defs_Forall p WT) _ IN.
  by move=> /= WTg; inversion WTg.
Qed.
