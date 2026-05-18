From Stdlib Require Import PArith NArith Arith.

From compcert.lib Require Import Maps.

From GallinaC.Imp Require Import Uint32 Uintptr.

From GallinaC.Compiler.Common Require Import Ctxt Value Types Expr.
From GallinaC.Compiler.Deep Require Import Cmd Prog.

Fixpoint type_cmd (ty_ctxt: ctxt (type * bool) unit fundef vardef) c: option type :=
  match c with
  | c_ret e => type_expr ty_ctxt e
  | c_bind b_id t_b c_b c_c =>
      match get_pure b_id ty_ctxt with
      | Some (t1, false) =>
          if type_eqb t_b t1 then
            match type_cmd ty_ctxt c_b with
            | Some t_b' =>
                if type_eqb t_b t_b' then
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
      match type_expr ty_ctxt e_i with
      | Some t_bool =>
          match type_cmd ty_ctxt c_t, type_cmd ty_ctxt c_e with
          | Some t_t, Some t_e =>
              if type_eqb t_t t_e then
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
      match type_expr ty_ctxt e_v, type_cmd (push_stack tt ty_ctxt) c_c with
      | Some t_v', Some t_c =>
          if type_eqb t_v t_v' then Some t_c else None
      | _, _ => None
      end
  | c_read_var n t =>
      if ground t then
        match get_stack n ty_ctxt with
        | Some tt => Some t
        | None => None
        end
      else None
  | c_write_var n t e =>
      match type_expr ty_ctxt e, get_stack n ty_ctxt with
      | Some t', Some tt => if type_eqb t t' then Some t_unit else None
      | _, _ => None
      end
  | c_alloc_ptr e_size t t_init =>
      match type_expr ty_ctxt e_size, type_expr ty_ctxt t_init with
      | Some t_ofst, Some t' => if type_eqb t t' then Some t_ptr else None
      | _, _ => None
      end
  | c_read_ptr e_ptr t =>
      if ground t then
        match type_expr ty_ctxt e_ptr with
        | Some t_ptr => Some t
        | _ => None
        end
      else None
  | c_write_ptr e_ptr t e_val =>
      match type_expr ty_ctxt e_ptr, type_expr ty_ctxt e_val with
      | Some t_ptr, Some t' => if type_eqb t t' then Some t_unit else None
      | _, _ => None
      end
  | c_free_ptr e_ptr =>
      match type_expr ty_ctxt e_ptr with
      | Some t_ptr => Some t_unit
      | _ => None
      end
  | c_shift_fw_ptr e_ptr e_shift | c_shift_bw_ptr e_ptr e_shift =>
                                     match type_expr ty_ctxt e_ptr, type_expr ty_ctxt e_shift with
                                     | Some t_ptr, Some t_ofst => Some t_ptr
                                     | _, _ => None
                                     end
  | c_ptr_eq e_ptr_l e_ptr_r =>
      match type_expr ty_ctxt e_ptr_l, type_expr ty_ctxt e_ptr_r with
      | Some t_ptr, Some t_ptr => Some t_bool
      | _, _ => None
      end
  | c_app f_id args =>
      match Ctxt.get_global f_id ty_ctxt, ListExt.map_opt (type_expr ty_ctxt) args with
      | Some (AST.Gfun (AST.Internal fn)), Some t_args =>
          if ground fn.(fn_return) then
            if ListExt.forall2 type_eqb t_args (List.map snd fn.(fn_params)) then
              Some fn.(fn_return)
            else
              None
          else
            None
      | _, _ => None
      end
  end.

(* TODO find a way to guarantee have a somewhat usable progress implied by wt_cmd *)
(* TODO previous effort added an output context, but failed at the if *)
Inductive wt_cmd: ctxt (type * bool) unit fundef vardef -> cmd -> type -> Type :=
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
                       (GROUND: Ground t)
                       (Nth: get_stack n ty_ctxt = Some tt),
                       wt_cmd ty_ctxt (c_read_var n t) t
| wt_write_var : forall {ty_ctxt} {n} {e t}
                        (WT: wt_expr ty_ctxt.(ctxt_pure) e t)
                        (GROUND: Ground t)
                        (Nth: get_stack n ty_ctxt = Some tt),
    wt_cmd ty_ctxt (c_write_var n t e) t_unit
| wt_alloc_ptr : forall {ty_ctxt n t e}
                        (WTsize: wt_expr ty_ctxt.(ctxt_pure) n t_ofst)
                        (WTinit: wt_expr ty_ctxt.(ctxt_pure) e t)
                        (GROUND: Ground t),
    wt_cmd ty_ctxt (c_alloc_ptr n t e) t_ptr
| wt_read_ptr : forall {ty_ctxt t p}
                       (WTptr: wt_expr ty_ctxt.(ctxt_pure) p t_ptr)
                       (GROUND: Ground t),
    wt_cmd ty_ctxt (c_read_ptr p t) t
| wt_write_ptr : forall {ty_ctxt p t e}
                        (WTptr: wt_expr ty_ctxt.(ctxt_pure) p t_ptr)
                        (WTval: wt_expr ty_ctxt e t)
                        (GROUND: Ground t),
    wt_cmd ty_ctxt (c_write_ptr p t e) t_unit
| wt_free_ptr : forall {ty_ctxt p}
                       (WTptr: wt_expr ty_ctxt.(ctxt_pure) p t_ptr),
    wt_cmd ty_ctxt (c_free_ptr p) t_unit
| wt_shift_fw_ptr: forall {ty_ctxt p n}
                          (WTptr: wt_expr ty_ctxt.(ctxt_pure) p t_ptr)
                          (WTofst: wt_expr ty_ctxt n t_ofst),
    wt_cmd ty_ctxt (c_shift_fw_ptr p n) t_ptr
| wt_shift_bw_ptr: forall {ty_ctxt p n}
                          (WTptr: wt_expr ty_ctxt.(ctxt_pure) p t_ptr)
                          (WTofst: wt_expr ty_ctxt n t_ofst),
    wt_cmd ty_ctxt (c_shift_bw_ptr p n) t_ptr
| wt_ptr_eq: forall {ty_ctxt p1 p2}
                    (WTl: wt_expr ty_ctxt.(ctxt_pure) p1 t_ptr)
                    (WTr: wt_expr ty_ctxt p2 t_ptr),
    wt_cmd ty_ctxt (c_ptr_eq p1 p2) t_bool
| wt_app : forall
    {ty_ctxt f_id args fn}
    (Hfind_fn: Ctxt.get_global f_id ty_ctxt = Some (AST.Gfun (AST.Internal fn)))
    (Hreturn_ground: Ground fn.(fn_return))
    (WT_args: ListExt.Forall2T (wt_expr ty_ctxt) args (List.map snd fn.(fn_params))),
    wt_cmd ty_ctxt (c_app f_id args) fn.(fn_return)
.

Lemma type_cmd_complete [ctx c t] (WT: wt_cmd ctx c t): type_cmd ctx c = Some t.
Proof.
  induction WT as [
    ty_ctxt e t WTe
  | ty_ctxt x c1 c2 t1 t2 UNBOUND WTm IHWTm WTf IHWTf
  | ty_ctxt e c1 c2 t WTcond WTthen IHWTthen WTelse IHWTelse
  | ty_ctxt c_cond c_body WTcond IHWTcond WTbody IHWTbody
  | ty_ctxt t_v e_v c_c t_c WTinit WTcont IHWTcont
  | ty_ctxt n t GROUND Nth
  | ty_ctxt n e t WT GROUND Nth
  | ty_ctxt n t e WTsize WTinit GROUND
  | ty_ctxt t p WTptr GROUND
  | ty_ctxt p t e WTptr WTval GROUND
  | ty_ctxt p WTptr
  | ty_ctxt p n WTptr WTofst
  | ty_ctxt p n WTptr WTofst
  | ty_ctxt p1 p2 WTl WTr
  | ty_ctxt f_id args fn Hfind_fn Hreturn_ground WT_args
  ]; cbn [type_cmd].
  - apply Expr.Facts.type_expr_correct; exact WTe.
  - rewrite UNBOUND, type_eqb_refl, IHWTm, type_eqb_refl, IHWTf; reflexivity.
  - rewrite (Expr.Facts.type_expr_correct _ _ _ WTcond), IHWTthen, IHWTelse, type_eqb_refl; reflexivity.
  - rewrite IHWTcond, IHWTbody; reflexivity.
  - rewrite (Expr.Facts.type_expr_correct _ _ _ WTinit), IHWTcont, type_eqb_refl; reflexivity.
  - destruct (ground_spec t) as [_|NG]; [| exfalso; apply NG; exact GROUND].
    rewrite Nth; reflexivity.
  - rewrite (Expr.Facts.type_expr_correct _ _ _ WT), Nth, type_eqb_refl; reflexivity.
  - rewrite (Expr.Facts.type_expr_correct _ _ _ WTsize),
            (Expr.Facts.type_expr_correct _ _ _ WTinit), type_eqb_refl; reflexivity.
  - destruct (ground_spec t) as [_|NG]; [| exfalso; apply NG; exact GROUND].
    rewrite (Expr.Facts.type_expr_correct _ _ _ WTptr); reflexivity.
  - rewrite (Expr.Facts.type_expr_correct _ _ _ WTptr),
            (Expr.Facts.type_expr_correct _ _ _ WTval), type_eqb_refl; reflexivity.
  - rewrite (Expr.Facts.type_expr_correct _ _ _ WTptr); reflexivity.
  - rewrite (Expr.Facts.type_expr_correct _ _ _ WTptr),
            (Expr.Facts.type_expr_correct _ _ _ WTofst); reflexivity.
  - rewrite (Expr.Facts.type_expr_correct _ _ _ WTptr),
            (Expr.Facts.type_expr_correct _ _ _ WTofst); reflexivity.
  - rewrite (Expr.Facts.type_expr_correct _ _ _ WTl),
            (Expr.Facts.type_expr_correct _ _ _ WTr); reflexivity.
  - rewrite (Hfind_fn : @get_global _ _ fundef _ f_id ty_ctxt = _),
            ((ListExt.map_opt_Forall2T (Expr.Facts.type_expr_correct _) WT_args)
               : ListExt.map_opt (type_expr (@ctxt_pure _ _ fundef _ ty_ctxt)) args = _).
    destruct (ground_spec fn.(fn_return)) as [_|NG]; [| exfalso; apply NG; exact Hreturn_ground].
    rewrite ((ListExt.list_eqb_refl type_eqb type_eqb_spec)
               : forall l, ListExt.forall2 type_eqb l l = true).
    reflexivity.
Qed.

Lemma type_cmd_correct [ctx c t] (EQ: type_cmd ctx c = Some t): wt_cmd ctx c t.
Proof.
  revert ctx t EQ; induction c; intros ctx t EQ; cbn [type_cmd] in EQ.
  - apply wt_ret, Expr.Facts.type_expr_complete, EQ.
  - destruct (get_pure id_b ctx) as [[t1 [|]]|] eqn:GETP;
      cbn in EQ; try discriminate.
    destruct (type_eqb_spec t_b t1); [| discriminate]; subst t1.
    destruct (type_cmd ctx c1) as [t_b'|] eqn:TYPb; [| discriminate].
    destruct (type_eqb_spec t_b t_b'); [| discriminate]; subst t_b'.
    destruct (type_cmd (set_pure id_b (t_b, true) ctx) c2) as [t_c|] eqn:TYPc;
      [| discriminate].
    inversion EQ; subst.
    apply (wt_bind GETP (IHc1 _ _ TYPb) (IHc2 _ _ TYPc)).
  - destruct (type_expr ctx e_if) as [[ | | | | | ] | ] eqn:TYPi; try discriminate.
    destruct (type_cmd ctx c1) as [t_t|] eqn:TYPt; [| discriminate].
    destruct (type_cmd ctx c2) as [t_e|] eqn:TYPe; [| discriminate].
    destruct (type_eqb_spec t_t t_e); [| discriminate]; subst t_e.
    inversion EQ; subst.
    apply (wt_if (Expr.Facts.type_expr_complete _ _ _ TYPi)
                 (IHc1 _ _ TYPt) (IHc2 _ _ TYPe)).
  - destruct (type_cmd ctx c1) as [[ | | | | | ] | ] eqn:TYPcd; try discriminate.
    destruct (type_cmd ctx c2) as [[ | | | | | ] | ] eqn:TYPb; try discriminate.
    inversion EQ; subst.
    apply (wt_while (IHc1 _ _ TYPcd) (IHc2 _ _ TYPb)).
  - destruct (type_expr ctx e_v) as [t_v'|] eqn:TYPv; [| discriminate].
    destruct (type_cmd (push_stack tt ctx) c) as [t_c|] eqn:TYPc; [| discriminate].
    destruct (type_eqb_spec t_v t_v'); [| discriminate]; subst t_v'.
    inversion EQ; subst.
    apply (wt_with_var (Expr.Facts.type_expr_complete _ _ _ TYPv)
                       (IHc _ _ TYPc)).
  - destruct (ground_spec t_v) as [GR|NG]; [| discriminate].
    destruct (get_stack o_v ctx) as [[]|] eqn:NTH; [| discriminate].
    inversion EQ; subst.
    apply (wt_read_var GR NTH).
  - destruct (type_expr ctx e_v) as [t'|] eqn:TYPv; [| discriminate].
    destruct (get_stack o_v ctx) as [[]|] eqn:NTH; [| discriminate].
    destruct (type_eqb_spec t_v t'); [| discriminate]; subst t'.
    inversion EQ; subst.
    specialize (Expr.Facts.type_expr_complete _ _ _ TYPv) as Hwt.
    apply (wt_write_var Hwt (Expr.Facts.wt_expr_ground Hwt) NTH).
  - destruct (type_expr ctx e_size) as [[ | | | | | ] | ] eqn:TYPs; try discriminate.
    destruct (type_expr ctx e_init) as [t'|] eqn:TYPi; [| discriminate].
    destruct (type_eqb_spec t_init t'); [| discriminate]; subst t'.
    inversion EQ; subst.
    specialize (Expr.Facts.type_expr_complete _ _ _ TYPs) as Hsize.
    specialize (Expr.Facts.type_expr_complete _ _ _ TYPi) as Hinit.
    apply (wt_alloc_ptr Hsize Hinit (Expr.Facts.wt_expr_ground Hinit)).
  - destruct (ground_spec t_val) as [GR|NG]; [| discriminate].
    destruct (type_expr ctx e_ptr) as [[ | | | | | ] | ] eqn:TYPp; try discriminate.
    inversion EQ; subst.
    apply (wt_read_ptr (Expr.Facts.type_expr_complete _ _ _ TYPp) GR).
  - destruct (type_expr ctx e_ptr) as [[ | | | | | ] | ] eqn:TYPp; try discriminate.
    destruct (type_expr ctx e_val) as [t'|] eqn:TYPv; [| discriminate].
    destruct (type_eqb_spec t_val t'); [| discriminate]; subst t'.
    inversion EQ; subst.
    specialize (Expr.Facts.type_expr_complete _ _ _ TYPp) as Hptr.
    specialize (Expr.Facts.type_expr_complete _ _ _ TYPv) as Hval.
    apply (wt_write_ptr Hptr Hval (Expr.Facts.wt_expr_ground Hval)).
  - destruct (type_expr ctx e_ptr) as [[ | | | | | ] | ] eqn:TYPp; try discriminate.
    inversion EQ; subst.
    apply (wt_free_ptr (Expr.Facts.type_expr_complete _ _ _ TYPp)).
  - destruct (type_expr ctx e_ptr) as [[ | | | | | ] | ] eqn:TYPp; try discriminate.
    destruct (type_expr ctx e_ofst) as [[ | | | | | ] | ] eqn:TYPo; try discriminate.
    inversion EQ; subst.
    apply (wt_shift_fw_ptr (Expr.Facts.type_expr_complete _ _ _ TYPp)
                           (Expr.Facts.type_expr_complete _ _ _ TYPo)).
  - destruct (type_expr ctx e_ptr) as [[ | | | | | ] | ] eqn:TYPp; try discriminate.
    destruct (type_expr ctx e_ofst) as [[ | | | | | ] | ] eqn:TYPo; try discriminate.
    inversion EQ; subst.
    apply (wt_shift_bw_ptr (Expr.Facts.type_expr_complete _ _ _ TYPp)
                           (Expr.Facts.type_expr_complete _ _ _ TYPo)).
  - destruct (type_expr ctx e_ptr_l) as [[ | | | | | ] | ] eqn:TYPl; try discriminate.
    destruct (type_expr ctx e_ptr_r) as [[ | | | | | ] | ] eqn:TYPr; try discriminate.
    inversion EQ; subst.
    apply (wt_ptr_eq (Expr.Facts.type_expr_complete _ _ _ TYPl)
                     (Expr.Facts.type_expr_complete _ _ _ TYPr)).
  - destruct (Ctxt.get_global f_id ctx) as [[fd|gv]|] eqn:GET; try discriminate.
    destruct fd as [fn|ef]; [| discriminate].
    destruct (ListExt.map_opt (type_expr ctx) args) as [t_args|] eqn:WTargs;
      [| discriminate].
    destruct (ground_spec fn.(fn_return)) as [GR|NG]; [| discriminate].
    destruct (ListExt.forall2 type_eqb t_args (List.map snd fn.(fn_params))) eqn:Eforall;
      [| discriminate].
    specialize (ListExt.list_eqb_spec type_eqb t_args (List.map snd fn.(fn_params)) type_eqb_spec) as EQ'.
    unfold ListExt.list_eqb in EQ'; rewrite Eforall in EQ'.
    inversion EQ'; subst t_args.
    inversion EQ; subst.
    apply (wt_app GET GR (ListExt.map_opt_Forall2T_inv (Expr.Facts.type_expr_complete _) WTargs)).
Qed.

Definition wt_f_extra (f_extra: f_extra): Prop := True.

Definition wt_p_extra (p_extra: program): Prop := True.

Definition wt_function := wt_function f_extra wt_f_extra wt_cmd.

Definition wt_fundef := wt_fundef f_extra wt_f_extra wt_cmd.

Definition wt_fundef_call := wt_fundef_call cmd f_extra.

Definition wt_globvar := wt_globvar cmd f_extra.

Definition wt_globdef := wt_globdef f_extra wt_f_extra wt_cmd.

Definition wt_program := wt_program wt_f_extra wt_cmd wt_p_extra.
Definition type_function := Prog.type_function (cmd := cmd) (f_extra := f_extra) type_cmd (fun _ => true).
Definition type_fundef := Prog.type_fundef (cmd := cmd) (f_extra := f_extra) type_cmd (fun _ => true).
Definition type_globvar := Prog.type_globvar (cmd := cmd) (f_extra := f_extra).
Definition type_globdef := Prog.type_globdef (cmd := cmd) (f_extra := f_extra) type_cmd (fun _ => true).
Definition type_prog_defs := Prog.type_prog_defs (cmd := cmd) (f_extra := f_extra) type_cmd (fun _ => true).
Definition type_program := Prog.type_program (cmd := cmd) (f_extra := f_extra) (p_extra := p_extra) type_cmd (fun _ => true) (fun _ => true).

Lemma wt_f_extra_complete (fx: f_extra): wt_f_extra fx -> (fun _: f_extra => true) fx = true.
Proof. reflexivity. Qed.

Lemma wt_f_extra_correct (fx: f_extra): (fun _: f_extra => true) fx = true -> wt_f_extra fx.
Proof. intros _; exact I. Qed.

Lemma wt_p_extra_spec (p: program): Bool.reflect (wt_p_extra p) ((fun _: program => true) p).
Proof. apply ReflectT; exact I. Qed.

Lemma type_function_correct ctx func:
  type_function ctx func = true -> wt_function ctx func.
Proof.
  apply Prog.type_function_correct;
    [ apply type_cmd_correct | apply wt_f_extra_correct ].
Qed.

Lemma type_function_complete ctx func:
  wt_function ctx func -> type_function ctx func = true.
Proof.
  apply Prog.type_function_complete;
    [ apply type_cmd_complete | apply wt_f_extra_complete ].
Qed.

Lemma type_fundef_correct ctx fd:
  type_fundef ctx fd = true -> wt_fundef ctx fd.
Proof.
  apply Prog.type_fundef_correct;
    [ apply type_cmd_correct | apply wt_f_extra_correct ].
Qed.

Lemma type_fundef_complete ctx fd:
  wt_fundef ctx fd -> type_fundef ctx fd = true.
Proof.
  apply Prog.type_fundef_complete;
    [ apply type_cmd_complete | apply wt_f_extra_complete ].
Qed.

Lemma type_globvar_spec ctx id gv:
  Bool.reflect (wt_globvar ctx id gv) (type_globvar ctx id gv).
Proof. apply Prog.type_globvar_spec. Qed.

Lemma type_globdef_spec ctx id gd:
  Bool.reflect (wt_globdef ctx id gd) (type_globdef ctx id gd).
Proof.
  apply Prog.type_globdef_spec;
    [ apply type_cmd_complete | apply type_cmd_correct
    | apply wt_f_extra_complete | apply wt_f_extra_correct ].
Qed.

Lemma type_program_spec p:
  Bool.reflect (wt_program p) (type_program p).
Proof.
  apply Prog.type_program_spec;
    [ apply type_cmd_complete | apply type_cmd_correct
    | apply wt_f_extra_complete | apply wt_f_extra_correct
    | apply wt_p_extra_spec ].
Qed.
