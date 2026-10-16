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

From Stdlib Require Import ZArith PArith Arith List Psatz Bool.
Import ListNotations.

From compcert.common Require Globalenvs.
From compcert.common Require Linking.
From compcert.common Require Import Errors.
From compcert.lib Require Import Coqlib Maps.

From HB Require Import structures.

From GallinaC.Utils Require ReflectExt.
From GallinaC.Utils Require Import ListExt CompCertExt Algebra.

From GallinaC.Imp Require Import State.

From GallinaC.Compiler.Common Require CCInj Value.
From GallinaC.Compiler.Common Require Import Types Ctxt Expr.
From GallinaC.Compiler.Deep Require Typing OpSem.
From GallinaC.Compiler.Deep Require Import Cmd Prog Linker.
From GallinaC.Compiler.IR Require Prog Cmd Typing Linker.
Import (canonicals) IR.Prog IR.Cmd.
From GallinaC.Compiler.Passes Require Import IRgen.

Lemma stack_usage_nonneg c: (0 <= stack_usage c)%Z.
Proof.
  induction c; cbn; lia.
Qed.

Lemma cenv_add_bind_pure b (t: type) (cenv: cmd_compilenv):
  ctxt_pure (cenv_ctxt (cenv_add_bind b t cenv))
  = Maps.PTree.set b (t, true) (ctxt_pure (cenv_ctxt cenv)).
Proof. reflexivity. Qed.

Lemma cenv_add_bind_stack b (t: type) (cenv: cmd_compilenv):
  ctxt_stack (cenv_ctxt (cenv_add_bind b t cenv)) = ctxt_stack (cenv_ctxt cenv).
Proof. reflexivity. Qed.

Lemma cenv_add_bind_next_id b (t: type) (cenv: cmd_compilenv):
  (cenv_add_bind b t cenv).(next_id) = cenv.(next_id).
Proof. reflexivity. Qed.

Lemma cenv_push_stack_pure (cenv: cmd_compilenv):
  ctxt_pure (cenv_ctxt (cenv_push_stack cenv)) = ctxt_pure (cenv_ctxt cenv).
Proof. reflexivity. Qed.

Lemma cenv_push_stack_stack (cenv: cmd_compilenv):
  ctxt_stack (cenv_ctxt (cenv_push_stack cenv))
  = ctxt_stack (cenv_ctxt cenv) ++ [tt].
Proof. reflexivity. Qed.

Lemma cenv_push_stack_next_id (cenv: cmd_compilenv):
  (cenv_push_stack cenv).(next_id) = cenv.(next_id).
Proof. reflexivity. Qed.

Lemma cenv_new_temp_eq (t_t: type) (cenv: cmd_compilenv):
  cenv_new_temp t_t cenv
  = (cenv.(next_id),
     {| next_id := Pos.succ cenv.(next_id);
        new_temps := (cenv.(next_id), t_t) :: cenv.(new_temps);
        new_internals := cenv.(new_internals);
        cenv_ctxt := Ctxt.set_pure cenv.(next_id) (t_t, false) cenv.(cenv_ctxt) |}).
Proof. reflexivity. Qed.

Lemma cenv_new_internal_eq (t_i: type) (cenv: cmd_compilenv):
  cenv_new_internal t_i cenv
  = (cenv.(next_id),
     {| next_id := Pos.succ cenv.(next_id);
        new_temps := cenv.(new_temps);
        new_internals := (cenv.(next_id), t_i) :: cenv.(new_internals);
        cenv_ctxt := cenv.(cenv_ctxt) |}).
Proof. reflexivity. Qed.

Lemma cenv_new_internal_id [t_i: type] [cenv: cmd_compilenv] [id_i cenv']
  (NI: cenv_new_internal t_i cenv = (id_i, cenv')):
  id_i = cenv.(next_id).
Proof.
  rewrite cenv_new_internal_eq in NI; injection NI as <- _; reflexivity.
Qed.

Lemma cenv_new_internal_next_id [t_i: type] [cenv: cmd_compilenv] [id_i cenv']
  (NI: cenv_new_internal t_i cenv = (id_i, cenv')):
  cenv'.(next_id) = Pos.succ cenv.(next_id).
Proof.
  rewrite cenv_new_internal_eq in NI; injection NI as _ <-; reflexivity.
Qed.

Lemma cenv_new_internal_temps [t_i: type] [cenv: cmd_compilenv] [id_i cenv']
  (NI: cenv_new_internal t_i cenv = (id_i, cenv')):
  cenv'.(new_temps) = cenv.(new_temps).
Proof.
  rewrite cenv_new_internal_eq in NI; injection NI as _ <-; reflexivity.
Qed.

Lemma cenv_new_internal_internals [t_i: type] [cenv: cmd_compilenv] [id_i cenv']
  (NI: cenv_new_internal t_i cenv = (id_i, cenv')):
  cenv'.(new_internals) = (id_i, t_i) :: cenv.(new_internals).
Proof.
  rewrite cenv_new_internal_eq in NI; injection NI as <- <-; reflexivity.
Qed.

Lemma cenv_new_temp_id [t_t: type] [cenv: cmd_compilenv] [id_t cenv']
  (NT: cenv_new_temp t_t cenv = (id_t, cenv')):
  id_t = cenv.(next_id).
Proof.
  rewrite cenv_new_temp_eq in NT; injection NT as <- _; reflexivity.
Qed.

Lemma cenv_new_temp_next_id [t_t: type] [cenv: cmd_compilenv] [id_t cenv']
  (NT: cenv_new_temp t_t cenv = (id_t, cenv')):
  cenv'.(next_id) = Pos.succ cenv.(next_id).
Proof.
  rewrite cenv_new_temp_eq in NT; injection NT as _ <-; reflexivity.
Qed.

Lemma cenv_new_temp_stack [t_t: type] [cenv: cmd_compilenv] [id_t cenv']
  (NT: cenv_new_temp t_t cenv = (id_t, cenv')):
  ctxt_stack (cenv_ctxt cenv') = ctxt_stack (cenv_ctxt cenv).
Proof.
  rewrite cenv_new_temp_eq in NT; injection NT as _ <-; reflexivity.
Qed.

Lemma cenv_new_temp_pure [t_t: type] [cenv: cmd_compilenv] [id_t cenv']
  (NT: cenv_new_temp t_t cenv = (id_t, cenv')):
  ctxt_pure (cenv_ctxt cenv')
  = Maps.PTree.set cenv.(next_id) (t_t, false) (ctxt_pure (cenv_ctxt cenv)).
Proof.
  rewrite cenv_new_temp_eq in NT; injection NT as _ <-; reflexivity.
Qed.

Lemma cenv_new_temp_temps [t_t: type] [cenv: cmd_compilenv] [id_t cenv']
  (NT: cenv_new_temp t_t cenv = (id_t, cenv')):
  cenv'.(new_temps) = (id_t, t_t) :: cenv.(new_temps).
Proof.
  rewrite cenv_new_temp_eq in NT; injection NT as <- <-; reflexivity.
Qed.

Lemma transl_fundef_external cenv ef:
  transl_fundef cenv (AST.External ef) = OK (AST.External ef, cenv).
Proof. reflexivity. Qed.

Record cenv_shape (W: list AST.ident) (cenv cenv': cmd_compilenv): Prop :=
  mk_cenv_shape {

      shape_next_id: (cenv.(next_id) <= cenv'.(next_id))%positive;

      shape_stack: ctxt_stack (cenv_ctxt cenv') = ctxt_stack (cenv_ctxt cenv);

      shape_new: exists Dt Di,
        cenv'.(new_temps) = Dt ++ cenv.(new_temps)
        /\ cenv'.(new_internals) = Di ++ cenv.(new_internals)
        /\ (forall id ty, In (id, ty) Dt ->
                          (cenv.(next_id) <= id)%positive
                          /\ (id < cenv'.(next_id))%positive)
        /\ (forall id ty, In (id, ty) Di ->
                          (cenv.(next_id) <= id)%positive
                          /\ (id < cenv'.(next_id))%positive)
        /\ ListExt.SBinds Dt
        /\ ListExt.SBinds Di
        /\ ListExt.DBinds Dt Di;

      shape_pure: forall id,
        (id < cenv.(next_id))%positive ->
        ~ In id W ->
        Maps.PTree.get id (ctxt_pure (cenv_ctxt cenv'))
        = Maps.PTree.get id (ctxt_pure (cenv_ctxt cenv));
    }.

Lemma cenv_shape_refl W cenv: cenv_shape W cenv cenv.
Proof.
  constructor.
  - reflexivity.
  - reflexivity.
  - exists (@nil (AST.ident * type)), (@nil (AST.ident * type)).
    split; [ reflexivity | ].
    split; [ reflexivity | ].
    split; [ intros id ty IN; destruct IN | ].
    split; [ intros id ty IN; destruct IN | ].
    split; [ constructor | ].
    split; [ constructor | constructor ].
  - intros id _ _; reflexivity.
Qed.

Lemma cenv_shape_trans [W1 W2 W cenv0 cenv1 cenv2]
  (SH1: cenv_shape W1 cenv0 cenv1)
  (SH2: cenv_shape W2 cenv1 cenv2)
  (INCL1: incl W1 W)
  (INCL2: incl W2 W):
  cenv_shape W cenv0 cenv2.
Proof.
  destruct SH1 as [ NID1 STK1 [ Dt1 [ Di1 (TMP1 & INT1 & RNGt1 & RNGi1 & SBt1 & SBi1 & DB1) ] ] PUR1 ].
  destruct SH2 as [ NID2 STK2 [ Dt2 [ Di2 (TMP2 & INT2 & RNGt2 & RNGi2 & SBt2 & SBi2 & DB2) ] ] PUR2 ].
  assert (RNGt2': forall id ty, In (id, ty) Dt2 -> (cenv1.(next_id) <= id)%positive)
    by (intros id ty IN; exact (proj1 (RNGt2 _ _ IN))).
  assert (RNGi2': forall id ty, In (id, ty) Di2 -> (cenv1.(next_id) <= id)%positive)
    by (intros id ty IN; exact (proj1 (RNGi2 _ _ IN))).
  assert (RNGt1': forall id ty, In (id, ty) Dt1 -> (id < cenv1.(next_id))%positive)
    by (intros id ty IN; exact (proj2 (RNGt1 _ _ IN))).
  assert (RNGi1': forall id ty, In (id, ty) Di1 -> (id < cenv1.(next_id))%positive)
    by (intros id ty IN; exact (proj2 (RNGi1 _ _ IN))).
  constructor.
  - lia.
  - rewrite STK2; exact STK1.
  - exists (Dt2 ++ Dt1), (Di2 ++ Di1).
    split; [ rewrite TMP2, TMP1, <- app_assoc; reflexivity | ].
    split; [ rewrite INT2, INT1, <- app_assoc; reflexivity | ].
    split.
    { intros id ty IN; apply in_app_or in IN as [ IN | IN ];
        [ specialize (RNGt2 _ _ IN) | specialize (RNGt1 _ _ IN) ]; lia. }
    split.
    { intros id ty IN; apply in_app_or in IN as [ IN | IN ];
        [ specialize (RNGi2 _ _ IN) | specialize (RNGi1 _ _ IN) ]; lia. }
    split; [ exact (ListExt.SBinds_app_by_range SBt2 SBt1 RNGt2' RNGt1') | ].
    split; [ exact (ListExt.SBinds_app_by_range SBi2 SBi1 RNGi2' RNGi1') | ].
    apply (proj2 (DBinds_iff_disjoint_fst _ _)).
    intros x INx INy.
    apply in_map_iff in INx as ( [ idx tyx ] & EQx & INx ).
    apply in_map_iff in INy as ( [ idy tyy ] & EQy & INy ).
    cbn [fst] in EQx, EQy; subst x; subst idy.
    apply in_app_or in INx as [ INx | INx ]; apply in_app_or in INy as [ INy | INy ].
    + exact (proj1 (DBinds_iff_disjoint_fst _ _) DB2 idx
               (in_map fst _ _ INx) (in_map fst _ _ INy)).
    + specialize (RNGt2 _ _ INx); specialize (RNGi1 _ _ INy); lia.
    + specialize (RNGt1 _ _ INx); specialize (RNGi2 _ _ INy); lia.
    + exact (proj1 (DBinds_iff_disjoint_fst _ _) DB1 idx
               (in_map fst _ _ INx) (in_map fst _ _ INy)).
  - intros id LT NIN.
    assert (LT1: (id < cenv1.(next_id))%positive) by lia.
    rewrite (PUR2 id LT1 (fun IN => NIN (INCL2 _ IN))).
    exact (PUR1 id LT (fun IN => NIN (INCL1 _ IN))).
Qed.

Lemma cenv_shape_new_temp [W cenv0 cenv1 t_t id_t cenv2]
  (SH: cenv_shape W cenv0 cenv1)
  (NT: cenv_new_temp t_t cenv1 = (id_t, cenv2)):
  cenv_shape W cenv0 cenv2 /\ id_t = cenv1.(next_id).
Proof.
  unfold cenv_new_temp, cenv_get_next_id in NT; cbn in NT.
  injection NT as EID ECENV; subst id_t; subst cenv2.
  destruct SH as [ NID STK [ Dt [ Di (TMP & INT & RNGt & RNGi & SBt & SBi & DB) ] ] PUR ].
  split; [ | reflexivity ].
  constructor; cbn.
  - lia.
  - exact STK.
  - exists ((cenv1.(next_id), t_t) :: Dt), Di.
    split; [ cbn; f_equal; exact TMP | ].
    split; [ exact INT | ].
    split.
    { intros id ty [ EQ | IN ];
        [ injection EQ as <- <- | specialize (RNGt _ _ IN) ]; lia. }
    split.
    { intros id ty IN; specialize (RNGi _ _ IN); lia. }
    split.
    { constructor; [ | exact SBt ].
      apply (proj2 (ListExt.AbsBind_iff_not_In_fst _ _)).
      intros IN; apply in_map_iff in IN as ( [ id ty ] & EQ & IN ); cbn in EQ; subst id.
      specialize (RNGt _ _ IN); lia. }
    split; [ exact SBi | ].
    constructor; [ | exact DB ].
    apply (proj2 (ListExt.AbsBind_iff_not_In_fst _ _)).
    intros IN; apply in_map_iff in IN as ( [ id ty ] & EQ & IN ); cbn in EQ; subst id.
    specialize (RNGi _ _ IN); lia.
  - intros id LT NIN.
    rewrite Maps.PTree.gso by lia.
    exact (PUR _ LT NIN).
Qed.

Lemma cenv_shape_new_internal [W cenv0 cenv1 t_i id_i cenv2]
  (SH: cenv_shape W cenv0 cenv1)
  (NI: cenv_new_internal t_i cenv1 = (id_i, cenv2)):
  cenv_shape W cenv0 cenv2 /\ id_i = cenv1.(next_id).
Proof.
  unfold cenv_new_internal, cenv_get_next_id in NI; cbn in NI.
  injection NI as EID ECENV; subst id_i; subst cenv2.
  destruct SH as [ NID STK [ Dt [ Di (TMP & INT & RNGt & RNGi & SBt & SBi & DB) ] ] PUR ].
  split; [ | reflexivity ].
  constructor; cbn.
  - lia.
  - exact STK.
  - exists Dt, ((cenv1.(next_id), t_i) :: Di).
    split; [ exact TMP | ].
    split; [ cbn; f_equal; exact INT | ].
    split.
    { intros id ty IN; specialize (RNGt _ _ IN); lia. }
    split.
    { intros id ty [ EQ | IN ];
        [ injection EQ as <- <- | specialize (RNGi _ _ IN) ]; lia. }
    split; [ exact SBt | ].
    split.
    { constructor; [ | exact SBi ].
      apply (proj2 (ListExt.AbsBind_iff_not_In_fst _ _)).
      intros IN; apply in_map_iff in IN as ( [ id ty ] & EQ & IN ); cbn in EQ; subst id.
      specialize (RNGi _ _ IN); lia. }
    apply (proj2 (DBinds_iff_disjoint_fst _ _)).
    intros x INx [ EQ | INy ].
    + apply in_map_iff in INx as ( [ idx tyx ] & EQx & INx ).
      cbn [fst] in EQx, EQ; subst x.
      specialize (RNGt _ _ INx); lia.
    + exact (proj1 (DBinds_iff_disjoint_fst _ _) DB x INx INy).
  - intros id LT NIN.
    exact (PUR _ LT NIN).
Qed.

Lemma cenv_shape_add_bind [W cenv0 b_id t_b cenv1]
  (SH: cenv_shape W (cenv_add_bind b_id t_b cenv0) cenv1):
  cenv_shape (b_id :: W) cenv0 cenv1.
Proof.
  destruct SH as [ NID STK [ Dt [ Di (TMP & INT & RNGt & RNGi & SBt & SBi & DB) ] ] PUR ];
    cbn in NID, STK, TMP, INT, RNGt, RNGi, PUR.
  constructor.
  - exact NID.
  - exact STK.
  - exact (ex_intro _ Dt (ex_intro _ Di
             (conj TMP (conj INT (conj RNGt (conj RNGi (conj SBt (conj SBi DB)))))))).
  - intros id LT NIN.
    rewrite (PUR id LT (fun IN => NIN (or_intror IN))); cbn.
    apply Maps.PTree.gso.
    intros ->; exact (NIN (or_introl eq_refl)).
Qed.

Lemma cenv_shape_with_var [W cenv cenv1 cenv2 t_t id_var]
  (NT: cenv_new_temp t_t cenv = (id_var, cenv1))
  (SH: cenv_shape W (cenv_add_bind id_var t_t (cenv_push_stack cenv1)) cenv2):
  cenv_shape W cenv (cenv_pop_stack cenv2).
Proof.
  unfold cenv_new_temp, cenv_get_next_id in NT; cbn in NT.
  injection NT as EID ECENV; subst id_var; subst cenv1.
  destruct SH as [ NID STK [ Dt [ Di (TMP & INT & RNGt & RNGi & SBt & SBi & DB) ] ] PUR ];
    cbn in NID, STK, TMP, INT, RNGt, RNGi, PUR.
  constructor; cbn.
  - lia.
  - rewrite STK; cbn; rewrite removelast_last; reflexivity.
  - exists (Dt ++ [ (cenv.(next_id), t_t) ]), Di.
    split; [ rewrite TMP, <- app_assoc; reflexivity | ].
    split; [ exact INT | ].
    split.
    { intros id ty IN; apply in_app_or in IN as [ IN | [ EQ | [] ] ];
        [ specialize (RNGt _ _ IN) | injection EQ as <- <- ]; lia. }
    split.
    { intros id ty IN; specialize (RNGi _ _ IN); lia. }
    split.
    { apply (proj2 (SBinds_app _ _)).
      split; [ exact SBt | ].
      split; [ constructor; [ constructor | constructor ] | ].
      apply (proj2 (DBinds_iff_disjoint_fst _ _)).
      intros x INx [ EQ | [] ].
      apply in_map_iff in INx as ( [ idx tyx ] & EQx & INx ).
      cbn [fst] in EQx, EQ; subst x.
      specialize (RNGt _ _ INx); lia. }
    split; [ exact SBi | ].
    apply (proj2 (DBinds_iff_disjoint_fst _ _)).
    intros x INx INy.
    rewrite map_app in INx; cbn [List.map fst] in INx.
    apply in_app_or in INx as [ INx | [ EQ | [] ] ].
    + exact (proj1 (DBinds_iff_disjoint_fst _ _) DB x INx INy).
    + apply in_map_iff in INy as ( [ idy tyy ] & EQy & INy ).
      cbn [fst] in EQy; subst x; subst idy.
      specialize (RNGi _ _ INy); lia.
  - intros id LT NIN.
    rewrite (PUR id ltac:(cbn; lia) NIN); cbn.
    rewrite Maps.PTree.gso by lia.
    rewrite Maps.PTree.gso by lia.
    reflexivity.
Qed.

Local Ltac transl_red H := cbn [transl_cmd Errors.bind] in H.

Lemma transl_cmd_app_inv [cenv tail f_id args tc t cenv']
  (TRANSL: transl_cmd cenv tail (c_app f_id args) = OK (tc, t, cenv')):
  tail = false
  /\ cenv' = cenv
  /\ exists t_args,
      ListExt.map_opt (type_expr (ctxt_pure (cenv_ctxt cenv))) args = Some t_args
      /\ tc = IR.Cmd.c_app f_id t (List.combine args t_args).
Proof.
  destruct tail; cbn [transl_cmd Errors.bind negb] in TRANSL; [ discriminate | ].
  destruct (Globalenvs.Genv.find_symbol (ctxt_global (cenv_ctxt cenv)) f_id)
    as [ b | ]; [ | discriminate ].
  destruct (Globalenvs.Genv.find_funct_ptr (ctxt_global (cenv_ctxt cenv)) b)
    as [ [ fn | ef ] | ];
    destruct (ListExt.map_opt (type_expr (ctxt_pure (cenv_ctxt cenv))) args)
    as [ t_args | ];
    try discriminate.
  - destruct (ListExt.forall2b type_eqb t_args (List.map snd fn.(fn_params)));
      [ | discriminate ].
    injection TRANSL as <- <- <-.
    split; [ reflexivity | split; [ reflexivity | exists t_args; split; reflexivity ] ].
  - destruct ef as [ nm sg | | | | | | | | | | | ]; try discriminate.
    destruct (Facts.ef_sig_dec (AST.EF_external nm sg)) as [ sig | ]; [ | discriminate ].
    destruct (ListExt.forall2b type_eqb t_args sig.(sig_args)); [ | discriminate ].
    injection TRANSL as <- <- <-.
    split; [ reflexivity | split; [ reflexivity | exists t_args; split; reflexivity ] ].
  - destruct ef; discriminate.
Qed.

Lemma transl_cmd_shape:
  forall c cenv tail tc t cenv'
         (TRANSL: transl_cmd cenv tail c = OK (tc, t, cenv')),
    cenv_shape (List.map fst (Deep.Cmd.cmd_temps c)) cenv cenv'.
Proof.
  induction c as [ e
                 | id_b t_b c_b IHb c_c IHc
                 | e_if c_then IHt c_else IHe
                 | c_cond IHcond c_body IHbody
                 | t_v e_v c_c IHc
                 | o_v t_v
                 | o_v t_v e_v
                 | e_size t_init e_init
                 | e_ptr t_val
                 | e_ptr t_val e_val
                 | e_ptr
                 | e_ptr e_ofst
                 | e_ptr e_ofst
                 | e_l e_r
                 | f_id args
                 | e_l e_r
                 | e_l e_r ];
    intros cenv tail tc t cenv' TRANSL; transl_red TRANSL.
  - destruct (type_expr _ e) as [ t0 | ]; [ | discriminate ].
    injection TRANSL as <- <- <-; apply cenv_shape_refl.
  - destruct (transl_cmd cenv false c_b) as [ [ [ tcb tb' ] cenv1 ] | ] eqn:E1;
      transl_red TRANSL; [ | discriminate ].
    destruct (type_eqb t_b tb'); [ | discriminate ].
    destruct (transl_cmd (cenv_add_bind id_b t_b cenv1) tail c_c)
      as [ [ [ tcc tc0 ] cenv2 ] | ] eqn:E2;
      transl_red TRANSL; [ | discriminate ].
    injection TRANSL as <- <- <-.
    rewrite cmd_temps_bind; cbn; rewrite map_app.
    apply (cenv_shape_trans (IHb _ _ _ _ _ E1)
             (cenv_shape_add_bind (IHc _ _ _ _ _ E2)));
      intros x IN; cbn.
    + right; apply in_or_app; left; exact IN.
    + destruct IN as [ <- | IN ]; [ left; reflexivity | ].
      right; apply in_or_app; right; exact IN.
  - destruct (transl_cmd cenv tail c_then) as [ [ [ tc1 t1 ] cenv1 ] | ] eqn:E1;
      transl_red TRANSL; [ | discriminate ].
    destruct (transl_cmd cenv1 tail c_else) as [ [ [ tc2 t2 ] cenv2 ] | ] eqn:E2;
      transl_red TRANSL; [ | discriminate ].
    destruct (type_eqb t1 t2); [ | discriminate ].
    injection TRANSL as <- <- <-.
    rewrite cmd_temps_if, map_app.
    apply (cenv_shape_trans (IHt _ _ _ _ _ E1) (IHe _ _ _ _ _ E2));
      intros x IN; apply in_or_app; [ left | right ]; exact IN.
  - destruct (transl_cmd cenv false c_cond) as [ [ [ tc1 t1 ] cenv1 ] | ] eqn:E1;
      transl_red TRANSL; [ | discriminate ].
    destruct (transl_cmd cenv1 false c_body) as [ [ [ tc2 t2 ] cenv2 ] | ] eqn:E2;
      transl_red TRANSL; [ | discriminate ].
    destruct (type_eqb t1 t_bool); [ | discriminate ].
    destruct (type_eqb t2 t_unit); [ | discriminate ].
    destruct (cenv_new_internal t_bool cenv2) as [ id_cond cenv3 ] eqn:E3.
    destruct (cenv_new_internal t_unit cenv3) as [ id_body cenv4 ] eqn:E4.
    injection TRANSL as <- <- <-.
    rewrite cmd_temps_while, map_app.
    assert (SH12: cenv_shape (List.map fst (Deep.Cmd.cmd_temps c_cond)
                                ++ List.map fst (Deep.Cmd.cmd_temps c_body)) cenv cenv2)
      by (apply (cenv_shape_trans (IHcond _ _ _ _ _ E1) (IHbody _ _ _ _ _ E2));
          intros x IN; apply in_or_app; [ left | right ]; exact IN).
    destruct (cenv_shape_new_internal SH12 E3) as [ SH3 _ ].
    destruct (cenv_shape_new_internal SH3 E4) as [ SH4 _ ].
    exact SH4.
  - destruct (cenv_new_temp t_unit cenv) as [ id_var cenv1 ] eqn:E1.
    destruct (transl_cmd (cenv_add_bind id_var t_unit (cenv_push_stack cenv1)) tail c_c)
      as [ [ [ tc1 t1 ] cenv2 ] | ] eqn:E2;
      transl_red TRANSL; [ | discriminate ].
    injection TRANSL as <- <- <-.
    rewrite cmd_temps_with_var.
    exact (cenv_shape_with_var E1 (IHc _ _ _ _ _ E2)).
  - injection TRANSL as <- <- <-; apply cenv_shape_refl.
  - injection TRANSL as <- <- <-; apply cenv_shape_refl.
  - destruct (cenv_new_internal t_ptr cenv) as [ id1 cenv1 ] eqn:E1.
    destruct (cenv_new_internal t_ofst cenv1) as [ id2 cenv2 ] eqn:E2.
    destruct (cenv_new_internal t_init cenv2) as [ id3 cenv3 ] eqn:E3.
    injection TRANSL as <- <- <-.
    destruct (cenv_shape_new_internal (cenv_shape_refl [] cenv) E1) as [ SH1 _ ].
    destruct (cenv_shape_new_internal SH1 E2) as [ SH2 _ ].
    destruct (cenv_shape_new_internal SH2 E3) as [ SH3 _ ].
    exact SH3.
  - injection TRANSL as <- <- <-; apply cenv_shape_refl.
  - injection TRANSL as <- <- <-; apply cenv_shape_refl.
  - injection TRANSL as <- <- <-; apply cenv_shape_refl.
  - injection TRANSL as <- <- <-; apply cenv_shape_refl.
  - injection TRANSL as <- <- <-; apply cenv_shape_refl.
  - injection TRANSL as <- <- <-; apply cenv_shape_refl.
  - destruct (transl_cmd_app_inv TRANSL) as ( _ & -> & _ ).
    apply cenv_shape_refl.
  - injection TRANSL as <- <- <-; apply cenv_shape_refl.
  - injection TRANSL as <- <- <-; apply cenv_shape_refl.
Qed.

Lemma transl_cmd_next_id_mono [c cenv tail tc t cenv']
  (TRANSL: transl_cmd cenv tail c = OK (tc, t, cenv')):
  (cenv.(next_id) <= cenv'.(next_id))%positive.
Proof. exact (shape_next_id _ _ _ (transl_cmd_shape _ _ _ _ _ _ TRANSL)). Qed.

Lemma transl_cmd_new_temps [c cenv tail tc t cenv']
  (TRANSL: transl_cmd cenv tail c = OK (tc, t, cenv')):
  exists D,
    cenv'.(new_temps) = D ++ cenv.(new_temps)
    /\ (forall id ty, In (id, ty) D ->
                      (cenv.(next_id) <= id)%positive /\ (id < cenv'.(next_id))%positive)
    /\ ListExt.SBinds D.
Proof.
  destruct (shape_new _ _ _ (transl_cmd_shape _ _ _ _ _ _ TRANSL))
    as ( Dt & Di & TMP & _ & RNGt & _ & SBt & _ & _ ).
  exact (ex_intro _ Dt (conj TMP (conj RNGt SBt))).
Qed.

Lemma transl_cmd_new_internals [c cenv tail tc t cenv']
  (TRANSL: transl_cmd cenv tail c = OK (tc, t, cenv')):
  exists Dt Di,
    cenv'.(new_temps) = Dt ++ cenv.(new_temps)
    /\ cenv'.(new_internals) = Di ++ cenv.(new_internals)
    /\ (forall id ty, In (id, ty) Di ->
                      (cenv.(next_id) <= id)%positive /\ (id < cenv'.(next_id))%positive)
    /\ ListExt.SBinds Di
    /\ ListExt.DBinds Dt Di.
Proof.
  destruct (shape_new _ _ _ (transl_cmd_shape _ _ _ _ _ _ TRANSL))
    as ( Dt & Di & TMP & INT & _ & RNGi & _ & SBi & DB ).
  exact (ex_intro _ Dt (ex_intro _ Di
           (conj TMP (conj INT (conj RNGi (conj SBi DB)))))).
Qed.

Lemma transl_cmd_stack_restored [c cenv tail tc t cenv']
  (TRANSL: transl_cmd cenv tail c = OK (tc, t, cenv')):
  ctxt_stack (cenv_ctxt cenv') = ctxt_stack (cenv_ctxt cenv).
Proof. exact (shape_stack _ _ _ (transl_cmd_shape _ _ _ _ _ _ TRANSL)). Qed.

Lemma transl_cmd_pure_stable [c cenv tail tc t cenv'] id
  (TRANSL: transl_cmd cenv tail c = OK (tc, t, cenv'))
  (LT: (id < cenv.(next_id))%positive)
  (NIN: ~ In id (List.map fst (Deep.Cmd.cmd_temps c))):
  Maps.PTree.get id (ctxt_pure (cenv_ctxt cenv'))
  = Maps.PTree.get id (ctxt_pure (cenv_ctxt cenv)).
Proof.
  exact (shape_pure _ _ _ (transl_cmd_shape _ _ _ _ _ _ TRANSL) id LT NIN).
Qed.

Lemma transl_cmd_advance [c cenv tail tc t cenv'] [floor] [ctx]
  (TRANSL: transl_cmd cenv tail c = OK (tc, t, cenv'))
  (FLOOR: (floor <= cenv.(next_id))%positive)
  (GDOM: forall id p, Maps.PTree.get id ctx = Some p -> (id < floor)%positive)
  (DSJ: forall id ty, Maps.PTree.get id ctx = Some (ty, true) ->
                      ~ In id (List.map fst (Deep.Cmd.cmd_temps c)))
  (AGREE: forall id ty, Maps.PTree.get id ctx = Some (ty, true) ->
                        Maps.PTree.get id (ctxt_pure (cenv_ctxt cenv))
                        = Some (ty, true)):
  ctxt_stack (cenv_ctxt cenv') = ctxt_stack (cenv_ctxt cenv)
  /\ (cenv.(next_id) <= cenv'.(next_id))%positive
  /\ (forall id ty, Maps.PTree.get id ctx = Some (ty, true) ->
                    Maps.PTree.get id (ctxt_pure (cenv_ctxt cenv'))
                    = Some (ty, true)).
Proof.
  split; [ exact (transl_cmd_stack_restored TRANSL) | ].
  split; [ exact (transl_cmd_next_id_mono TRANSL) | ].
  intros id ty GET.
  assert (LTid := GDOM id (ty, true) GET).
  rewrite (transl_cmd_pure_stable id TRANSL ltac:(lia) (DSJ id ty GET)).
  exact (AGREE id ty GET).
Qed.

Inductive tr_cmd (floor: AST.ident) (SS: Z):
  Maps.PTree.t (type * bool) -> nat -> bool -> cmd -> IR.Cmd.cmd -> type -> Prop :=
| tr_ret: forall ctx d tail e t
                 (TYPE: forall t', type_expr ctx e = Some t' -> t' = t),
    tr_cmd floor SS ctx d tail (c_ret e) (IR.Cmd.c_ret e t) t
| tr_bind: forall ctx d tail b_id t_b c_b c_c tc_b tc_c t_c
                  (BINDER: (b_id < floor)%positive)
                  (TRb: tr_cmd floor SS ctx d false c_b tc_b t_b)
                  (TRc: tr_cmd floor SS (Maps.PTree.set b_id (t_b, true) ctx) d tail c_c tc_c t_c),
    tr_cmd floor SS ctx d tail (c_bind b_id t_b c_b c_c)
      (IR.Cmd.c_bind b_id t_b tc_b tc_c t_c) t_c
| tr_if: forall ctx d tail e c_t c_e tc_t tc_e t
                (TRt: tr_cmd floor SS ctx d tail c_t tc_t t)
                (TRe: tr_cmd floor SS ctx d tail c_e tc_e t),
    tr_cmd floor SS ctx d tail (c_if e c_t c_e) (IR.Cmd.c_if e tc_t tc_e t) t
| tr_while: forall ctx d tail c_cond c_body tc_cond tc_body id_cond id_body
                   (FRESHc: (floor <= id_cond)%positive)
                   (FRESHb: (floor <= id_body)%positive)
                   (NEQ: id_cond <> id_body)
                   (TRcond: tr_cmd floor SS ctx d false c_cond tc_cond t_bool)
                   (TRbody: tr_cmd floor SS ctx d false c_body tc_body t_unit),
    tr_cmd floor SS ctx d tail (c_while c_cond c_body)
      (IR.Cmd.c_while tc_cond id_cond tc_body id_body) t_unit
| tr_with_var: forall ctx d tail t_v e_v c_c tc_c t id_var
                      (LT: (Z.of_nat d < SS)%Z)
                      (FRESH: (floor <= id_var)%positive)
                      (TRc: tr_cmd floor SS ctx (S d) tail c_c tc_c t),
    tr_cmd floor SS ctx d tail (c_with_var t_v e_v c_c)
      (IR.Cmd.c_bind id_var t_unit (IR.Cmd.c_write_var d t_v e_v) tc_c t) t
| tr_read_var: forall ctx d tail n t,
    tr_cmd floor SS ctx d tail (c_read_var n t) (IR.Cmd.c_read_var n t) t
| tr_write_var: forall ctx d tail n t e,
    tr_cmd floor SS ctx d tail (c_write_var n t e) (IR.Cmd.c_write_var n t e) t_unit
| tr_alloc_ptr: forall ctx d tail e_size t e_init id_p id_c id_i
                       (FRESH1: (floor <= id_p)%positive)
                       (FRESH2: (floor <= id_c)%positive)
                       (FRESH3: (floor <= id_i)%positive)
                       (NEQpc: id_p <> id_c)
                       (NEQpi: id_p <> id_i)
                       (NEQci: id_c <> id_i),
    tr_cmd floor SS ctx d tail (c_alloc_ptr e_size t e_init)
      (IR.Cmd.c_alloc_ptr e_size t e_init id_p id_c id_i) t_ptr
| tr_read_ptr: forall ctx d tail e_ptr t,
    tr_cmd floor SS ctx d tail (c_read_ptr e_ptr t) (IR.Cmd.c_read_ptr e_ptr t) t
| tr_write_ptr: forall ctx d tail e_ptr t e_val,
    tr_cmd floor SS ctx d tail (c_write_ptr e_ptr t e_val)
      (IR.Cmd.c_write_ptr e_ptr t e_val) t_unit
| tr_free_ptr: forall ctx d tail e_ptr,
    tr_cmd floor SS ctx d tail (c_free_ptr e_ptr) (IR.Cmd.c_free_ptr e_ptr) t_unit
| tr_shift_fw_ptr: forall ctx d tail e_ptr e_ofst,
    tr_cmd floor SS ctx d tail (c_shift_fw_ptr e_ptr e_ofst)
      (IR.Cmd.c_shift_fw_ptr e_ptr e_ofst) t_ptr
| tr_shift_bw_ptr: forall ctx d tail e_ptr e_ofst,
    tr_cmd floor SS ctx d tail (c_shift_bw_ptr e_ptr e_ofst)
      (IR.Cmd.c_shift_bw_ptr e_ptr e_ofst) t_ptr
| tr_ptr_eq: forall ctx d tail e_l e_r,
    tr_cmd floor SS ctx d tail (c_ptr_eq e_l e_r) (IR.Cmd.c_ptr_eq e_l e_r) t_bool
| tr_app: forall ctx d f_id args t_out t_args
                 (LEN: List.length t_args = List.length args)
                 (TARGS: forall ts, ListExt.map_opt (type_expr ctx) args = Some ts ->
                                    ts = t_args),
    tr_cmd floor SS ctx d false (c_app f_id args)
      (IR.Cmd.c_app f_id t_out (List.combine args t_args)) t_out
| tr_div: forall ctx d tail e_l e_r,
    tr_cmd floor SS ctx d tail (c_div e_l e_r) (IR.Cmd.c_div e_l e_r) t_nat
| tr_mod: forall ctx d tail e_l e_r,
    tr_cmd floor SS ctx d tail (c_mod e_l e_r) (IR.Cmd.c_mod e_l e_r) t_nat
.

Lemma transl_cmd_charact:
  forall c cenv tail tc t cenv' floor ctx SS
         (TRANSL: transl_cmd cenv tail c = OK (tc, t, cenv'))
         (SPACE: (Z.of_nat (List.length (ctxt_stack (cenv_ctxt cenv)))
                  + stack_usage c <= SS)%Z)
         (FLOOR: (floor <= cenv.(next_id))%positive)
         (BINDERS: Forall (fun p => (fst p < floor)%positive) (Deep.Cmd.cmd_temps c))
         (SBINDS: ListExt.SBinds (Deep.Cmd.cmd_temps c))
         (GDOM: forall id p, Maps.PTree.get id ctx = Some p -> (id < floor)%positive)
         (DSJ: forall id ty, Maps.PTree.get id ctx = Some (ty, true) ->
                             ~ In id (List.map fst (Deep.Cmd.cmd_temps c)))
         (AGREE: forall id ty, Maps.PTree.get id ctx = Some (ty, true) ->
                               Maps.PTree.get id (ctxt_pure (cenv_ctxt cenv))
                               = Some (ty, true)),
    tr_cmd floor SS ctx (List.length (ctxt_stack (cenv_ctxt cenv))) tail c tc t.
Proof.
  induction c as [ e
                 | id_b t_b c_b IHb c_c IHc
                 | e_if c_then IHt c_else IHe
                 | c_cond IHcond c_body IHbody
                 | t_v e_v c_c IHc
                 | o_v t_v
                 | o_v t_v e_v
                 | e_size t_init e_init
                 | e_ptr t_val
                 | e_ptr t_val e_val
                 | e_ptr
                 | e_ptr e_ofst
                 | e_ptr e_ofst
                 | e_l e_r
                 | f_id args
                 | e_l e_r
                 | e_l e_r ];
    intros cenv tail tc t cenv' floor ctx SS
      TRANSL SPACE FLOOR BINDERS SBINDS GDOM DSJ AGREE;
    transl_red TRANSL;
    cbn [Deep.Cmd.cmd_temps stack_usage] in SPACE, BINDERS, SBINDS, DSJ;
    cbn [List.map fst] in DSJ.
  - destruct (type_expr (ctxt_pure (cenv_ctxt cenv)) e) as [ t0 | ] eqn:ETY;
      [ | discriminate ].
    injection TRANSL as <- <- <-.
    apply tr_ret.
    intros t' TE.
    assert (TE2 := Expr.Facts.type_expr_incl AGREE TE).
    congruence.
  - destruct (transl_cmd cenv false c_b) as [ [ [ tcb tb' ] cenv1 ] | ] eqn:E1;
      transl_red TRANSL; [ | discriminate ].
    destruct (type_eqb t_b tb') eqn:ETB; [ | discriminate ].
    apply (ReflectExt.reflect_eq_of_true type_eqb_spec) in ETB; subst tb'.
    destruct (transl_cmd (cenv_add_bind id_b t_b cenv1) tail c_c)
      as [ [ [ tcc tc0 ] cenv2 ] | ] eqn:E2;
      transl_red TRANSL; [ | discriminate ].
    injection TRANSL as <- <- <-.
    rewrite map_app in DSJ.
    apply Forall_cons_iff in BINDERS as [ Bhd Btl ]; cbn in Bhd.
    apply Forall_app in Btl as [ Bb Bc ].
    inversion SBINDS as [ | ?a ?b ?l NIB SBt ]; subst.
    apply (proj1 (SBinds_app _ _)) in SBt as ( SBb & SBc & _ ).
    assert (DSJb: forall id ty, Maps.PTree.get id ctx = Some (ty, true) ->
                                ~ In id (List.map fst (Deep.Cmd.cmd_temps c_b))).
    { intros id ty GET IN; apply (DSJ id ty GET); right; apply in_or_app; now left. }
    assert (DSJc: forall id ty, Maps.PTree.get id ctx = Some (ty, true) ->
                                ~ In id (List.map fst (Deep.Cmd.cmd_temps c_c))).
    { intros id ty GET IN; apply (DSJ id ty GET); right; apply in_or_app; now right. }
    destruct (transl_cmd_advance E1 FLOOR GDOM DSJb AGREE)
      as ( STK1 & NID1 & AGREE1 ).
    assert (SPACEb: (Z.of_nat (List.length (ctxt_stack (cenv_ctxt cenv)))
                     + stack_usage c_b <= SS)%Z) by lia.
    assert (TRb := IHb cenv false tcb t_b cenv1 floor ctx SS E1
                     SPACEb FLOOR Bb SBb GDOM DSJb AGREE).
    assert (SPACEc: (Z.of_nat (List.length (ctxt_stack
                                              (cenv_ctxt (cenv_add_bind id_b t_b cenv1))))
                     + stack_usage c_c <= SS)%Z).
    { rewrite cenv_add_bind_stack, STK1; lia. }
    assert (FLOORc: (floor <= (cenv_add_bind id_b t_b cenv1).(next_id))%positive).
    { rewrite cenv_add_bind_next_id; lia. }
    assert (GDOMc: forall id p,
               Maps.PTree.get id (Maps.PTree.set id_b (t_b, true) ctx) = Some p ->
               (id < floor)%positive).
    { intros id p GET.
      destruct (Pos.eq_dec id id_b) as [ -> | NE ]; [ exact Bhd | ].
      rewrite Maps.PTree.gso in GET by exact NE; exact (GDOM id p GET). }
    assert (DSJc2: forall id ty,
               Maps.PTree.get id (Maps.PTree.set id_b (t_b, true) ctx) = Some (ty, true) ->
               ~ In id (List.map fst (Deep.Cmd.cmd_temps c_c))).
    { intros id ty GET.
      destruct (Pos.eq_dec id id_b) as [ -> | NE ].
      - intros IN; refine (proj1 (ListExt.AbsBind_iff_not_In_fst _ _) NIB _).
        rewrite map_app; apply in_or_app; now right.
      - rewrite Maps.PTree.gso in GET by exact NE; exact (DSJc id ty GET). }
    assert (AGREEc: forall id ty,
               Maps.PTree.get id (Maps.PTree.set id_b (t_b, true) ctx) = Some (ty, true) ->
               Maps.PTree.get id (ctxt_pure (cenv_ctxt (cenv_add_bind id_b t_b cenv1)))
               = Some (ty, true)).
    { intros id ty GET.
      rewrite cenv_add_bind_pure.
      destruct (Pos.eq_dec id id_b) as [ -> | NE ].
      - rewrite Maps.PTree.gss in GET |- *; congruence.
      - rewrite Maps.PTree.gso in GET |- * by exact NE.
        exact (AGREE1 id ty GET). }
    assert (TRc := IHc (cenv_add_bind id_b t_b cenv1) tail tcc tc0 cenv2 floor
                     (Maps.PTree.set id_b (t_b, true) ctx) SS E2 SPACEc FLOORc Bc SBc
                     GDOMc DSJc2 AGREEc).
    rewrite cenv_add_bind_stack, STK1 in TRc.
    eapply tr_bind; [ exact Bhd | exact TRb | exact TRc ].
  - destruct (transl_cmd cenv tail c_then) as [ [ [ tc1 t1 ] cenv1 ] | ] eqn:E1;
      transl_red TRANSL; [ | discriminate ].
    destruct (transl_cmd cenv1 tail c_else) as [ [ [ tc2 t2 ] cenv2 ] | ] eqn:E2;
      transl_red TRANSL; [ | discriminate ].
    destruct (type_eqb t1 t2) eqn:ETY; [ | discriminate ].
    apply (ReflectExt.reflect_eq_of_true type_eqb_spec) in ETY; subst t2.
    injection TRANSL as <- <- <-.
    rewrite map_app in DSJ.
    apply Forall_app in BINDERS as [ Bt Be ].
    apply (proj1 (SBinds_app _ _)) in SBINDS as ( SBt & SBe & _ ).
    assert (DSJt: forall id ty, Maps.PTree.get id ctx = Some (ty, true) ->
                                ~ In id (List.map fst (Deep.Cmd.cmd_temps c_then))).
    { intros id ty GET IN; apply (DSJ id ty GET); apply in_or_app; now left. }
    assert (DSJe: forall id ty, Maps.PTree.get id ctx = Some (ty, true) ->
                                ~ In id (List.map fst (Deep.Cmd.cmd_temps c_else))).
    { intros id ty GET IN; apply (DSJ id ty GET); apply in_or_app; now right. }
    destruct (transl_cmd_advance E1 FLOOR GDOM DSJt AGREE)
      as ( STK1 & NID1 & AGREE1 ).
    assert (SPACEt: (Z.of_nat (List.length (ctxt_stack (cenv_ctxt cenv)))
                     + stack_usage c_then <= SS)%Z) by lia.
    assert (SPACEe: (Z.of_nat (List.length (ctxt_stack (cenv_ctxt cenv1)))
                     + stack_usage c_else <= SS)%Z) by (rewrite STK1; lia).
    assert (TRt := IHt cenv tail tc1 t1 cenv1 floor ctx SS E1
                     SPACEt FLOOR Bt SBt GDOM DSJt AGREE).
    assert (TRe := IHe cenv1 tail tc2 t1 cenv2 floor ctx SS E2
                     SPACEe ltac:(lia) Be SBe GDOM DSJe AGREE1).
    rewrite STK1 in TRe.
    apply tr_if; [ exact TRt | exact TRe ].
  - destruct (transl_cmd cenv false c_cond) as [ [ [ tc1 t1 ] cenv1 ] | ] eqn:E1;
      transl_red TRANSL; [ | discriminate ].
    destruct (transl_cmd cenv1 false c_body) as [ [ [ tc2 t2 ] cenv2 ] | ] eqn:E2;
      transl_red TRANSL; [ | discriminate ].
    destruct (type_eqb t1 t_bool) eqn:ET1; [ | discriminate ].
    destruct (type_eqb t2 t_unit) eqn:ET2; [ | discriminate ].
    apply (ReflectExt.reflect_eq_of_true type_eqb_spec) in ET1;
      apply (ReflectExt.reflect_eq_of_true type_eqb_spec) in ET2;
      subst t1; subst t2.
    destruct (cenv_new_internal t_bool cenv2) as [ id_cond cenv3 ] eqn:E3.
    destruct (cenv_new_internal t_unit cenv3) as [ id_body cenv4 ] eqn:E4.
    injection TRANSL as <- <- <-.
    pose proof (cenv_new_internal_id E3) as EIC.
    pose proof (cenv_new_internal_next_id E3) as ENID3.
    pose proof (cenv_new_internal_id E4) as EIB.
    pose proof (cenv_new_internal_next_id E4) as ENID4.
    rewrite map_app in DSJ.
    apply Forall_app in BINDERS as [ Bcond Bbody ].
    apply (proj1 (SBinds_app _ _)) in SBINDS as ( SBcond & SBbody & _ ).
    assert (NID2: (cenv1.(next_id) <= cenv2.(next_id))%positive)
      by exact (transl_cmd_next_id_mono E2).
    assert (DSJcond: forall id ty, Maps.PTree.get id ctx = Some (ty, true) ->
                                   ~ In id (List.map fst (Deep.Cmd.cmd_temps c_cond))).
    { intros id ty GET IN; apply (DSJ id ty GET); apply in_or_app; now left. }
    assert (DSJbody: forall id ty, Maps.PTree.get id ctx = Some (ty, true) ->
                                   ~ In id (List.map fst (Deep.Cmd.cmd_temps c_body))).
    { intros id ty GET IN; apply (DSJ id ty GET); apply in_or_app; now right. }
    destruct (transl_cmd_advance E1 FLOOR GDOM DSJcond AGREE)
      as ( STK1 & NID1 & AGREE1 ).
    assert (SPACEcond: (Z.of_nat (List.length (ctxt_stack (cenv_ctxt cenv)))
                        + stack_usage c_cond <= SS)%Z) by lia.
    assert (SPACEbody: (Z.of_nat (List.length (ctxt_stack (cenv_ctxt cenv1)))
                        + stack_usage c_body <= SS)%Z) by (rewrite STK1; lia).
    assert (TRcond := IHcond cenv false tc1 t_bool cenv1 floor ctx SS E1
                        SPACEcond FLOOR Bcond SBcond GDOM DSJcond AGREE).
    assert (TRbody := IHbody cenv1 false tc2 t_unit cenv2 floor ctx SS E2
                        SPACEbody ltac:(lia) Bbody SBbody GDOM DSJbody AGREE1).
    rewrite STK1 in TRbody.
    apply tr_while; [ lia | lia | lia | exact TRcond | exact TRbody ].
  - destruct (cenv_new_temp t_unit cenv) as [ id_var cenv1 ] eqn:E1.
    destruct (transl_cmd (cenv_add_bind id_var t_unit (cenv_push_stack cenv1)) tail c_c)
      as [ [ [ tc1 t1 ] cenv2 ] | ] eqn:E2;
      transl_red TRANSL; [ | discriminate ].
    injection TRANSL as <- <- <-.
    pose proof (cenv_new_temp_id E1) as EIV.
    pose proof (cenv_new_temp_next_id E1) as ENID1.
    pose proof (cenv_new_temp_stack E1) as ESTK1.
    pose proof (cenv_new_temp_pure E1) as EPURE1.
    assert (USAGE := stack_usage_nonneg c_c).
    assert (DEPTH: List.length (ctxt_stack (cenv_ctxt
                                              (cenv_add_bind id_var t_unit (cenv_push_stack cenv1))))
                   = S (List.length (ctxt_stack (cenv_ctxt cenv)))).
    { rewrite cenv_add_bind_stack, cenv_push_stack_stack, ESTK1.
      apply last_length. }
    assert (SPACEc: (Z.of_nat (List.length (ctxt_stack (cenv_ctxt
                                                          (cenv_add_bind id_var t_unit (cenv_push_stack cenv1)))))
                     + stack_usage c_c <= SS)%Z).
    { rewrite DEPTH; lia. }
    assert (FLOORc: (floor <= (cenv_add_bind id_var t_unit
                                 (cenv_push_stack cenv1)).(next_id))%positive).
    { rewrite cenv_add_bind_next_id, cenv_push_stack_next_id; lia. }
    assert (AGREEc: forall id ty, Maps.PTree.get id ctx = Some (ty, true) ->
                                  Maps.PTree.get id (ctxt_pure (cenv_ctxt
                                                                  (cenv_add_bind id_var t_unit (cenv_push_stack cenv1))))
                                  = Some (ty, true)).
    { intros id ty GET.
      assert (LTid := GDOM id (ty, true) GET).
      rewrite cenv_add_bind_pure, cenv_push_stack_pure, EPURE1.
      rewrite Maps.PTree.gso by lia.
      rewrite Maps.PTree.gso by lia.
      exact (AGREE id ty GET). }
    assert (TRc := IHc (cenv_add_bind id_var t_unit (cenv_push_stack cenv1)) tail
                     tc1 t1 cenv2 floor ctx SS E2 SPACEc FLOORc BINDERS SBINDS
                     GDOM DSJ AGREEc).
    rewrite DEPTH in TRc.
    apply tr_with_var; [ lia | lia | exact TRc ].
  - injection TRANSL as <- <- <-; apply tr_read_var.
  - injection TRANSL as <- <- <-; apply tr_write_var.
  - destruct (cenv_new_internal t_ptr cenv) as [ id1 cenv1 ] eqn:E1.
    destruct (cenv_new_internal t_ofst cenv1) as [ id2 cenv2 ] eqn:E2.
    destruct (cenv_new_internal t_init cenv2) as [ id3 cenv3 ] eqn:E3.
    injection TRANSL as <- <- <-.
    pose proof (cenv_new_internal_id E1) as EI1.
    pose proof (cenv_new_internal_next_id E1) as EN1.
    pose proof (cenv_new_internal_id E2) as EI2.
    pose proof (cenv_new_internal_next_id E2) as EN2.
    pose proof (cenv_new_internal_id E3) as EI3.
    pose proof (cenv_new_internal_next_id E3) as EN3.
    apply tr_alloc_ptr; lia.
  - injection TRANSL as <- <- <-; apply tr_read_ptr.
  - injection TRANSL as <- <- <-; apply tr_write_ptr.
  - injection TRANSL as <- <- <-; apply tr_free_ptr.
  - injection TRANSL as <- <- <-; apply tr_shift_fw_ptr.
  - injection TRANSL as <- <- <-; apply tr_shift_bw_ptr.
  - injection TRANSL as <- <- <-; apply tr_ptr_eq.
  - destruct (transl_cmd_app_inv TRANSL) as ( -> & _ & t_args & EARGS & -> ).
    apply tr_app; [ exact (map_opt_length EARGS) | ].
    intros ts TS.
    pose proof (Expr.Facts.map_opt_type_expr_incl AGREE TS) as TS'.
    congruence.
  - injection TRANSL as <- <- <-; apply tr_div.
  - injection TRANSL as <- <- <-; apply tr_mod.
Qed.

Lemma transl_cmd_cover:
  forall c cenv tail tc t cenv'
         (TRANSL: transl_cmd cenv tail c = OK (tc, t, cenv')),
    (forall id ty, In (id, ty) (IR.Cmd.cmd_temps tc) ->
                   In (id, ty) (Deep.Cmd.cmd_temps c) \/ In (id, ty) cenv'.(new_temps))
    /\ (forall id ty, In (id, ty) (IR.Cmd.cmd_internals tc) -> In (id, ty) cenv'.(new_internals)).
Proof.
  induction c as [ e
                 | id_b t_b c_b IHb c_c IHc
                 | e_if c_then IHt c_else IHe
                 | c_cond IHcond c_body IHbody
                 | t_v e_v c_c IHc
                 | o_v t_v
                 | o_v t_v e_v
                 | e_size t_init e_init
                 | e_ptr t_val
                 | e_ptr t_val e_val
                 | e_ptr
                 | e_ptr e_ofst
                 | e_ptr e_ofst
                 | e_l e_r
                 | f_id args
                 | e_l e_r
                 | e_l e_r ];
    intros cenv tail tc t cenv' TRANSL; transl_red TRANSL.
  - destruct (type_expr _ e) as [ t0 | ]; [ | discriminate ].
    injection TRANSL as <- <- <-.
    split; intros id ty [].
  - destruct (transl_cmd cenv false c_b) as [ [ [ tcb tb' ] cenv1 ] | ] eqn:E1;
      transl_red TRANSL; [ | discriminate ].
    destruct (type_eqb t_b tb'); [ | discriminate ].
    destruct (transl_cmd (cenv_add_bind id_b t_b cenv1) tail c_c)
      as [ [ [ tcc tc0 ] cenv2 ] | ] eqn:E2;
      transl_red TRANSL; [ | discriminate ].
    injection TRANSL as <- <- <-.
    cbn [IR.Cmd.cmd_temps IR.Cmd.cmd_internals].
    destruct (IHb _ _ _ _ _ E1) as [ COVb INTb ].
    destruct (IHc _ _ _ _ _ E2) as [ COVc INTc ].
    destruct (transl_cmd_new_internals E2) as ( D2 & D2I & END2 & END2I & _ ).
    cbn [cenv_add_bind new_temps new_internals] in END2, END2I.
    rewrite cmd_temps_bind.
    split.
    + intros id ty [ EQ | IN ]; [ left; left; exact EQ | ].
      apply in_app_or in IN as [ IN | IN ].
      * destruct (COVb id ty IN) as [ INb | INt ].
        -- left; right; apply in_or_app; left; exact INb.
        -- right; rewrite END2; apply in_or_app; right; exact INt.
      * destruct (COVc id ty IN) as [ INc | INt ].
        -- left; right; apply in_or_app; right; exact INc.
        -- right; exact INt.
    + intros id ty IN.
      apply in_app_or in IN as [ IN | IN ].
      * rewrite END2I; apply in_or_app; right; exact (INTb id ty IN).
      * exact (INTc id ty IN).
  - destruct (transl_cmd cenv tail c_then) as [ [ [ tc1 t1 ] cenv1 ] | ] eqn:E1;
      transl_red TRANSL; [ | discriminate ].
    destruct (transl_cmd cenv1 tail c_else) as [ [ [ tc2 t2 ] cenv2 ] | ] eqn:E2;
      transl_red TRANSL; [ | discriminate ].
    destruct (type_eqb t1 t2); [ | discriminate ].
    injection TRANSL as <- <- <-.
    cbn [IR.Cmd.cmd_temps IR.Cmd.cmd_internals].
    destruct (IHt _ _ _ _ _ E1) as [ COVt INTt ].
    destruct (IHe _ _ _ _ _ E2) as [ COVe INTe ].
    destruct (transl_cmd_new_internals E2) as ( D2 & D2I & END2 & END2I & _ ).
    rewrite cmd_temps_if.
    split.
    + intros id ty IN.
      apply in_app_or in IN as [ IN | IN ].
      * destruct (COVt id ty IN) as [ INb | INt ].
        -- left; apply in_or_app; left; exact INb.
        -- right; rewrite END2; apply in_or_app; right; exact INt.
      * destruct (COVe id ty IN) as [ INb | INt ].
        -- left; apply in_or_app; right; exact INb.
        -- right; exact INt.
    + intros id ty IN.
      apply in_app_or in IN as [ IN | IN ].
      * rewrite END2I; apply in_or_app; right; exact (INTt id ty IN).
      * exact (INTe id ty IN).
  - destruct (transl_cmd cenv false c_cond) as [ [ [ tc1 t1 ] cenv1 ] | ] eqn:E1;
      transl_red TRANSL; [ | discriminate ].
    destruct (transl_cmd cenv1 false c_body) as [ [ [ tc2 t2 ] cenv2 ] | ] eqn:E2;
      transl_red TRANSL; [ | discriminate ].
    destruct (type_eqb t1 t_bool); [ | discriminate ].
    destruct (type_eqb t2 t_unit); [ | discriminate ].
    destruct (cenv_new_internal t_bool cenv2) as [ id_cond cenv3 ] eqn:E3.
    destruct (cenv_new_internal t_unit cenv3) as [ id_body cenv4 ] eqn:E4.
    injection TRANSL as <- <- <-.
    cbn [IR.Cmd.cmd_temps IR.Cmd.cmd_internals].
    destruct (IHcond _ _ _ _ _ E1) as [ COVcond INTcond ].
    destruct (IHbody _ _ _ _ _ E2) as [ COVbody INTbody ].
    destruct (transl_cmd_new_internals E2) as ( D2 & D2I & END2 & END2I & _ ).
    rewrite cmd_temps_while.
    rewrite (cenv_new_internal_temps E4), (cenv_new_internal_temps E3).
    rewrite (cenv_new_internal_internals E4), (cenv_new_internal_internals E3).
    split.
    + intros id ty IN.
      apply in_app_or in IN as [ IN | IN ].
      * destruct (COVcond id ty IN) as [ INb | INt ].
        -- left; apply in_or_app; left; exact INb.
        -- right; rewrite END2; apply in_or_app; right; exact INt.
      * destruct (COVbody id ty IN) as [ INb | INt ].
        -- left; apply in_or_app; right; exact INb.
        -- right; exact INt.
    + intros id ty [ EQ | [ EQ | IN ] ].
      * right; left; exact EQ.
      * left; exact EQ.
      * right; right.
        apply in_app_or in IN as [ IN | IN ].
        -- rewrite END2I; apply in_or_app; right; exact (INTcond id ty IN).
        -- exact (INTbody id ty IN).
  - destruct (cenv_new_temp t_unit cenv) as [ id_var cenv1 ] eqn:E1.
    destruct (transl_cmd (cenv_add_bind id_var t_unit (cenv_push_stack cenv1)) tail c_c)
      as [ [ [ tc1 t1 ] cenv2 ] | ] eqn:E2;
      transl_red TRANSL; [ | discriminate ].
    injection TRANSL as <- <- <-.
    destruct (IHc _ _ _ _ _ E2) as [ COVc INTc ].
    destruct (transl_cmd_new_internals E2) as ( D2 & D2I & END2 & END2I & _ ).
    cbn [cenv_add_bind cenv_push_stack new_temps new_internals] in END2, END2I.
    rewrite cmd_temps_with_var.
    cbn [cenv_pop_stack new_temps new_internals IR.Cmd.cmd_temps IR.Cmd.cmd_internals app].
    split.
    + intros id ty [ EQ | IN ].
      * right; rewrite END2; apply in_or_app; right.
        rewrite (cenv_new_temp_temps E1); left; exact EQ.
      * exact (COVc id ty IN).
    + exact INTc.
  - injection TRANSL as <- <- <-; split; intros id ty [].
  - injection TRANSL as <- <- <-; split; intros id ty [].
  - destruct (cenv_new_internal t_ptr cenv) as [ id1 cenv1 ] eqn:E1.
    destruct (cenv_new_internal t_ofst cenv1) as [ id2 cenv2 ] eqn:E2.
    destruct (cenv_new_internal t_init cenv2) as [ id3 cenv3 ] eqn:E3.
    injection TRANSL as <- <- <-.
    cbn [IR.Cmd.cmd_temps IR.Cmd.cmd_internals].
    split; [ intros id ty [] | ].
    rewrite (cenv_new_internal_internals E3), (cenv_new_internal_internals E2),
      (cenv_new_internal_internals E1).
    intros id ty [ EQ | [ EQ | [ EQ | [] ] ] ].
    + right; right; left; exact EQ.
    + right; left; exact EQ.
    + left; exact EQ.
  - injection TRANSL as <- <- <-; split; intros id ty [].
  - injection TRANSL as <- <- <-; split; intros id ty [].
  - injection TRANSL as <- <- <-; split; intros id ty [].
  - injection TRANSL as <- <- <-; split; intros id ty [].
  - injection TRANSL as <- <- <-; split; intros id ty [].
  - injection TRANSL as <- <- <-; split; intros id ty [].
  - destruct (transl_cmd_app_inv TRANSL) as ( _ & _ & t_args & _ & -> ).
    split; intros id ty [].
  - injection TRANSL as <- <- <-; split; intros id ty [].
  - injection TRANSL as <- <- <-; split; intros id ty [].
Qed.

Lemma map_fst_params (params: list (AST.ident * type)):
  List.map fst (List.map (fun '(id, t) => (id, (t, true))) params)
  = List.map fst params.
Proof.
  induction params as [ | [ id t ] l IH ]; cbn; [ reflexivity | now f_equal ].
Qed.

Lemma transl_fundef_body_charact:
  forall cenv (fn: function) body t_body cenv1 ctx
         (SBpb: ListExt.SBinds (fn.(fn_params) ++ Deep.Cmd.cmd_temps fn.(fn_body)))
         (BOUND: forall id ty,
             In (id, ty) (fn.(fn_params) ++ fn.(fn_temps)
                                                 ++ Deep.Cmd.cmd_temps fn.(fn_body)) ->
             (id < cenv.(next_id))%positive)
         (E: transl_cmd (mk_cmd_compilenv cenv fn.(fn_params)) true fn.(fn_body)
             = OK (body, t_body, cenv1))
         (GTRUE: forall id ty, Maps.PTree.get id ctx = Some (ty, true) ->
                               In (id, ty) fn.(fn_params))
         (GDOM0: forall id p, Maps.PTree.get id ctx = Some p ->
                              In id (List.map fst (fn.(fn_params) ++ fn.(fn_temps)))),
    tr_cmd cenv.(next_id) (stack_usage fn.(fn_body)) ctx 0 true
                  fn.(fn_body) body t_body.
Proof.
  intros cenv fn body t_body cenv1 ctx SBpb BOUND E GTRUE GDOM0.
  destruct (proj1 (SBinds_app _ _) SBpb) as ( SBpar & SBbb & DBpb ).
  pose proof (proj1 (DBinds_iff_disjoint_fst _ _) DBpb) as DSJpb.
  assert (NRpar := proj1 (ListExt.SBinds_list_norepet _) SBpar).
  assert (STK0: ctxt_stack (cenv_ctxt (mk_cmd_compilenv cenv fn.(fn_params)))
                = @nil unit) by reflexivity.
  assert (NID0: (mk_cmd_compilenv cenv fn.(fn_params)).(next_id) = cenv.(next_id))
    by reflexivity.
  assert (PURE0: ctxt_pure (cenv_ctxt (mk_cmd_compilenv cenv fn.(fn_params)))
                 = Maps.PTree_Properties.of_list
                     (List.map (fun '(id, t) => (id, (t, true))) fn.(fn_params)))
    by reflexivity.
  replace (0%nat) with (List.length
                          (ctxt_stack (cenv_ctxt (mk_cmd_compilenv cenv fn.(fn_params)))))
    by (rewrite STK0; reflexivity).
  apply (transl_cmd_charact fn.(fn_body) (mk_cmd_compilenv cenv fn.(fn_params)) true
                                 body t_body cenv1 cenv.(next_id) ctx (stack_usage fn.(fn_body)) E).
  - rewrite STK0; cbn; lia.
  - rewrite NID0; lia.
  - apply Forall_forall; intros [ id ty ] IN; cbn.
    apply (BOUND id ty); apply in_or_app; right; apply in_or_app; now right.
  - exact SBbb.
  - intros id p GET.
    assert (IND := GDOM0 id p GET).
    apply in_map_iff in IND as ( [ id' ty ] & EQ & IN ); cbn in EQ; subst id'.
    apply (BOUND id ty).
    apply in_app_or in IN as [ IN | IN ]; apply in_or_app;
      [ now left | right; apply in_or_app; now left ].
  - intros id ty GET IN.
    refine (DSJpb id _ IN).
    apply in_map_iff; exists (id, ty); split; [ reflexivity | exact (GTRUE id ty GET) ].
  - intros id ty GET.
    rewrite PURE0.
    apply Maps.PTree_Properties.of_list_norepet.
    + rewrite map_fst_params; exact NRpar.
    + exact (in_map (fun '(id, t) => (id, (t, true))) _ _ (GTRUE id ty GET)).
Qed.

Record tr_function_at (floor: AST.ident) (fn: function) (tfn: IR.Prog.function): Prop :=
  mk_tr_function_at {

      tr_fn_return: tfn.(fn_return) = fn.(fn_return);

      tr_fn_params: tfn.(fn_params) = fn.(fn_params);

      tr_fn_stackspace:
      tfn.(fn_extra).(IR.Prog.fn_stackspace) = stack_usage fn.(fn_body);

      tr_fn_extra: IR.Typing.wt_f_extra tfn.(fn_extra);

      tr_fn_source_bound: forall id ty,
        In (id, ty) (fn.(fn_params) ++ fn.(fn_temps) ++ Deep.Cmd.cmd_temps fn.(fn_body)) ->
        (id < floor)%positive;

      tr_fn_temps: exists D,
        tfn.(fn_temps) = List.rev_append fn.(fn_temps) D
        /\ Forall (fun p => (floor <= fst p)%positive) D
        /\ ListExt.SBinds D;

      tr_fn_internals_sbinds: ListExt.SBinds tfn.(fn_internals);

      tr_fn_internals_floor: Forall (fun p => (floor <= fst p)%positive) tfn.(fn_internals);

      tr_fn_temps_internals_distinct: ListExt.DBinds tfn.(fn_temps) tfn.(fn_internals);

      tr_fn_body: forall ctx
                         (GTRUE: forall id ty, Maps.PTree.get id ctx = Some (ty, true) ->
                                               In (id, ty) fn.(fn_params))
                         (GDOM0: forall id p, Maps.PTree.get id ctx = Some p ->
                                              In id (List.map fst (fn.(fn_params) ++ fn.(fn_temps)))),
        tr_cmd floor (stack_usage fn.(fn_body)) ctx 0 true
          fn.(fn_body) tfn.(fn_body) fn.(fn_return);

      tr_fn_temps_cover: forall id ty,
        In (id, ty) (IR.Cmd.cmd_temps tfn.(fn_body)) -> (floor <= id)%positive ->
        In (id, ty) tfn.(fn_temps);

      tr_fn_internals_cover: forall id ty,
        In (id, ty) (IR.Cmd.cmd_internals tfn.(fn_body)) -> In (id, ty) tfn.(fn_internals);
    }.

Definition tr_function (fn: function) (tfn: IR.Prog.function): Prop :=
  exists floor, tr_function_at floor fn tfn.

Lemma transl_fundef_Internal_inv [cenv fn tfd cenv']
  (TRANSL: transl_fundef cenv (AST.Internal fn) = OK (tfd, cenv')):
  exists body cenv1,
    ListExt.SBinds (fn.(fn_params) ++ Deep.Cmd.cmd_temps fn.(fn_body))
    /\ (forall id ty,
           In (id, ty) (fn.(fn_params) ++ fn.(fn_temps)
                                               ++ Deep.Cmd.cmd_temps fn.(fn_body)) ->
           (id < cenv.(next_id))%positive)
    /\ transl_cmd (mk_cmd_compilenv cenv fn.(fn_params)) true fn.(fn_body)
       = OK (body, fn.(fn_return), cenv1)
    /\ IR.Typing.type_f_extra
         {| IR.Prog.fn_stackspace := stack_usage fn.(fn_body) |} = true
    /\ tfd = AST.Internal
               {| fn_return := fn.(fn_return);
                 fn_params := fn.(fn_params);
                 fn_temps := List.rev_append fn.(fn_temps) cenv1.(new_temps);
                 fn_internals := cenv1.(new_internals);
                 fn_body := body;
                 fn_extra := {| IR.Prog.fn_stackspace := stack_usage fn.(fn_body) |};
               |}
    /\ cenv' = mk_prog_compilenv cenv1.
Proof.
  unfold transl_fundef in TRANSL.
  destruct (ListExt.sbinds Pos.eqb (fn.(fn_params) ++ Deep.Cmd.cmd_temps fn.(fn_body)))
    eqn:SB; [ | discriminate ].
  destruct (forallb (fun '(id, _) => Pos.ltb id cenv.(next_id))
              (fn.(fn_params) ++ fn.(fn_temps) ++ Deep.Cmd.cmd_temps fn.(fn_body)))
    eqn:FB; [ | discriminate ].
  destruct (transl_cmd (mk_cmd_compilenv cenv fn.(fn_params)) true fn.(fn_body))
    as [ [ [ body t_body ] cenv1 ] | ] eqn:E;
    cbn [Errors.bind] in TRANSL; [ | discriminate ].
  destruct (type_eqb t_body fn.(fn_return)) eqn:ETB; [ | discriminate ].
  destruct (IR.Typing.type_f_extra
              {| IR.Prog.fn_stackspace := stack_usage fn.(fn_body) |}) eqn:ESS;
    [ | discriminate ].
  apply (ReflectExt.reflect_eq_of_true type_eqb_spec) in ETB; subst t_body.
  injection TRANSL as <- <-.
  exists body, cenv1.
  rewrite forallb_forall in FB.
  split;
    [ exact (proj2 (Bool.reflect_iff _ _ (ListExt.sbinds_spec Pos.eqb Pos.eqb_spec _)) SB) | ].
  split; [ intros id ty IN; exact (proj1 (Pos.ltb_lt _ _) (FB (id, ty) IN)) | ].
  split; [ reflexivity | ].
  split; [ reflexivity | ].
  split; reflexivity.
Qed.

Lemma transl_fundef_charact:
  forall cenv fn tfd cenv'
         (TRANSL: transl_fundef cenv (AST.Internal fn) = OK (tfd, cenv')),
  exists tfn, tfd = AST.Internal tfn /\ tr_function_at cenv.(next_id) fn tfn.
Proof.
  intros cenv fn tfd cenv' TRANSL.
  destruct (transl_fundef_Internal_inv TRANSL)
    as ( body & cenv1 & SBpb & BOUND & E & ESS & -> & _ ).
  eexists; split; [ reflexivity | ].
  assert (NT0: (mk_cmd_compilenv cenv fn.(fn_params)).(new_temps)
               = @nil (AST.ident * type)) by reflexivity.
  destruct (transl_cmd_new_internals E)
    as ( DT & DI & ENDT & ENDI & DIRANGE & DINR & DBtmpint ).
  cbn [mk_cmd_compilenv new_temps new_internals next_id] in ENDT, ENDI, DIRANGE.
  rewrite app_nil_r in ENDT, ENDI.
  assert (DILOW: forall id ty, In (id, ty) cenv1.(new_internals) ->
                               (cenv.(next_id) <= id)%positive).
  { intros id ty IN; rewrite ENDI in IN; exact (proj1 (DIRANGE id ty IN)). }
  destruct (transl_cmd_cover _ _ _ _ _ _ E) as [ COVB COVI ].
  constructor; cbn [fn_return fn_params fn_temps fn_internals fn_body fn_extra].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact (IR.Typing.type_f_extra_correct _ ESS).
  - exact BOUND.
  - destruct (transl_cmd_new_temps E) as ( D & ETMP & RNG & SB ).
    rewrite NT0, app_nil_r in ETMP.
    exists D.
    split; [ rewrite <- ETMP; reflexivity | ].
    split; [ | exact SB ].
    apply Forall_forall; intros [ id ty ] IN; cbn.
    exact (proj1 (RNG id ty IN)).
  - rewrite ENDI; exact DINR.
  - apply Forall_forall; intros [ id ty ] IN; exact (DILOW id ty IN).
  - apply (proj2 (DBinds_iff_disjoint_fst _ _)).
    intros x INx INy.
    apply List.in_map_iff in INx as ( [ id ty ] & EQX & INx ).
    apply List.in_map_iff in INy as ( [ id' ty' ] & EQY & INy ).
    cbn [fst] in EQX, EQY; subst x; subst id'.
    destruct (proj1 (In_rev_append _ _ _) INx) as [ INt | IND ].
    + pose proof (DILOW _ _ INy) as LO.
      pose proof (BOUND id ty
                    (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl INt))))) as HI.
      lia.
    + rewrite ENDT in IND; rewrite ENDI in INy.
      exact (proj1 (DBinds_iff_disjoint_fst _ _) DBtmpint id
               (in_map fst _ _ IND) (in_map fst _ _ INy)).
  - intros ctx GTRUE GDOM0.
    exact (transl_fundef_body_charact cenv fn body fn.(fn_return) cenv1 ctx
                                                        SBpb BOUND E GTRUE GDOM0).
  - intros id ty IN LE.
    destruct (COVB id ty IN) as [ INb | INt ].
    + pose proof (BOUND id ty
                    (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror INb))))) as HI.
      lia.
    + apply (proj2 (In_rev_append _ _ _)); right; exact INt.
  - exact COVI.
Qed.

Lemma params_preserved [fn tfn] (TR: tr_function fn tfn):
  tfn.(fn_params) = fn.(fn_params).
Proof. destruct TR as [ floor TRA ]; exact (tr_fn_params _ _ _ TRA). Qed.

Lemma return_preserved [fn tfn] (TR: tr_function fn tfn):
  tfn.(fn_return) = fn.(fn_return).
Proof. destruct TR as [ floor TRA ]; exact (tr_fn_return _ _ _ TRA). Qed.

Lemma params_temps_bound [floor fn tfn] (TRA: tr_function_at floor fn tfn):
  forall id ty, In (id, ty) (fn.(fn_params) ++ fn.(fn_temps)) ->
                (id < floor)%positive.
Proof.
  intros id ty IN.
  apply (tr_fn_source_bound _ _ _ TRA id ty).
  rewrite List.app_assoc; apply List.in_or_app; left; exact IN.
Qed.

Lemma sig_preserved [fn tfn] (TR: tr_function fn tfn):
  fn_signature tfn = fn_signature fn.
Proof.
  unfold fn_signature.
  rewrite (params_preserved TR), (return_preserved TR); reflexivity.
Qed.

Inductive match_fundef: fundef -> IR.Prog.fundef -> Prop :=
| match_fundef_internal: forall fn tfn
                                (TR: tr_function fn tfn),
    match_fundef (AST.Internal fn) (AST.Internal tfn)
| match_fundef_external: forall ef,
    match_fundef (AST.External ef) (AST.External ef)
.

Lemma transl_fundef_match [cenv fd tfd cenv']
  (TRANSL: transl_fundef cenv fd = OK (tfd, cenv')):
  match_fundef fd tfd.
Proof.
  destruct fd as [ fn | ef ].
  - destruct (transl_fundef_charact cenv fn tfd cenv' TRANSL) as ( tfn & -> & TRA ).
    apply match_fundef_internal.
    exists cenv.(next_id); exact TRA.
  - rewrite transl_fundef_external in TRANSL.
    injection TRANSL as <- <-.
    apply match_fundef_external.
Qed.

Definition match_varinfo: vardef -> vardef -> Prop := eq.

Definition match_prog (p: program) (tp: IR.Prog.program): Prop :=
  Linking.match_program_gen (fun _: program => match_fundef) match_varinfo p
    (program_of_program p) (program_of_program tp).

Lemma transl_globdefs_match:
  forall (ctx: program) gdefs cenv acc tgl cenv'
         (TRANSL: transl_globdefs cenv gdefs acc = OK (tgl, cenv')),
  exists tl,
    tgl = List.rev acc ++ tl
    /\ list_forall2
         (Linking.match_ident_globdef (fun _: program => match_fundef) match_varinfo ctx)
         gdefs tl.
Proof.
  intros ctx gdefs.
  induction gdefs as [ | [ g_id d ] gdefs IH ]; intros cenv acc tgl cenv' TRANSL.
  - cbn in TRANSL.
    injection TRANSL as <- <-.
    exists (@nil (AST.ident * IR.Prog.globdef)).
    rewrite app_nil_r.
    split; [ reflexivity | constructor ].
  - destruct d as [ fd | var_info ]; cbn in TRANSL.
    + destruct (transl_fundef cenv fd) as [ [ tfd cenv1 ] | ] eqn:E;
        cbn [Errors.bind] in TRANSL; [ | discriminate ].
      destruct (IH _ _ _ _ TRANSL) as ( tl & ETGL & MT ).
      exists ((g_id, AST.Gfun tfd) :: tl).
      split.
      * rewrite ETGL; cbn [List.rev]; rewrite <- app_assoc; reflexivity.
      * constructor; [ | exact MT ].
        split; [ reflexivity | ].
        cbn [fst snd].
        apply (Linking.match_globdef_fun _ _ _ ctx).
        -- apply Linking.linkorder_refl.
        -- exact (transl_fundef_match E).
    + destruct (type_init_data var_info.(AST.gvar_init)
                                          var_info.(AST.gvar_info).(var_type)
                && negb var_info.(AST.gvar_readonly)
                && negb var_info.(AST.gvar_volatile));
        [ | discriminate ].
      destruct (IH _ _ _ _ TRANSL) as ( tl & ETGL & MT ).
      exists ((g_id, AST.Gvar var_info) :: tl).
      split.
      * rewrite ETGL; cbn [List.rev]; rewrite <- app_assoc; reflexivity.
      * constructor; [ | exact MT ].
        split; [ reflexivity | ].
        cbn [fst snd].
        apply Linking.match_globdef_var.
        destruct var_info as [ info init ro vo ].
        apply Linking.match_globvar_intro.
        reflexivity.
Qed.

Lemma transf_program_match:
  forall p tp (TRANSL: transl_program p = OK tp), match_prog p tp.
Proof.
  intros p tp TRANSL.
  unfold transl_program in TRANSL.
  destruct (forallb (fun '(id, _) => Pos.ltb id p.(prog_extra).(prog_next_id))
              p.(prog_defs)); [ | discriminate ].
  destruct (transl_globdefs
              {| next_id := p.(prog_extra).(prog_next_id);
                new_temps := [];
                cenv_ctxt := ctxt_emp _ _ _ _ _ (List.map fst p.(prog_defs)) |}
              p.(prog_defs) [])
    as [ [ tgl cenv ] | ] eqn:E;
    cbn [Errors.bind] in TRANSL; [ | discriminate ].
  injection TRANSL as <-.
  destruct (transl_globdefs_match p _ _ _ _ _ E) as ( tl & ETGL & MT ).
  split; [ | split; reflexivity ].
  cbn [AST.prog_defs program_of_program prog_defs].
  rewrite ETGL.
  exact MT.
Qed.

Definition globals_match [Pd Id Sd Pi Ii Si: Type]
  (dctx: ctxt Pd Id Sd fundef vardef)
  (ictx: ctxt Pi Ii Si IR.Prog.fundef vardef): Prop :=
  forall id fd, Ctxt.get_global id dctx = Some (AST.Gfun fd) ->
                exists tfd, Ctxt.get_global id ictx = Some (AST.Gfun tfd)
                            /\ match_fundef fd tfd.

Lemma globals_match_ext [Pd Id Sd Pi Ii Si Pd' Id' Sd' Pi' Ii' Si': Type]
  [dctx: ctxt Pd Id Sd fundef vardef]
  [ictx: ctxt Pi Ii Si IR.Prog.fundef vardef]
  [dctx': ctxt Pd' Id' Sd' fundef vardef]
  [ictx': ctxt Pi' Ii' Si' IR.Prog.fundef vardef]
  (GM: globals_match dctx ictx)
  (GLd: ctxt_global dctx' = ctxt_global dctx)
  (GLi: ctxt_global ictx' = ctxt_global ictx):
  globals_match dctx' ictx'.
Proof.
  intros id fd GET.
  rewrite (Ctxt.Facts.get_global_ctxt_global_eq GLd) in GET.
  rewrite (Ctxt.Facts.get_global_ctxt_global_eq GLi).
  exact (GM id fd GET).
Qed.

Lemma globals_match_exf_bound [Pd Id Sd Pi Ii Si: Type]
  [dctx: ctxt Pd Id Sd fundef vardef]
  [ictx: ctxt Pi Ii Si IR.Prog.fundef vardef]
  (GM: globals_match dctx ictx) [ef]
  (DECL: exf_bound ef dctx):
  exf_bound ef ictx.
Proof.
  destruct DECL as ( id & GETd ).
  destruct (GM id _ GETd) as ( tfd & GETi & MF ).
  inversion MF; subst.
  exists id; exact GETi.
Qed.

Lemma globals_match_emp {Pd Id Sd Pi Ii Si: Type} {pubd pubi}:
  globals_match (ctxt_emp Pd Id Sd fundef vardef pubd)
    (ctxt_emp Pi Ii Si IR.Prog.fundef vardef pubi).
Proof.
  intros id fd GET.
  rewrite Ctxt.Facts.get_global_ctxt_emp in GET; discriminate GET.
Qed.

Lemma globals_match_add [Pd Id Sd Pi Ii Si: Type]
  [dctx: ctxt Pd Id Sd fundef vardef]
  [ictx: ctxt Pi Ii Si IR.Prog.fundef vardef]
  (GM: globals_match dctx ictx) (ctx: program) id g tg
  (MG: Linking.match_globdef (fun _: program => match_fundef) match_varinfo ctx g tg):
  globals_match (Ctxt.add_global dctx (id, g)) (Ctxt.add_global ictx (id, tg)).
Proof.
  intros id' fd GET.
  destruct (Coqlib.peq id' id) as [ -> | NE ].
  - rewrite Ctxt.Facts.get_global_add_global_eq in GET.
    injection GET as ->.
    inversion MG as [ ctx' fd' tfd LO MF | ]; subst.
    exists tfd; split; [ exact (Ctxt.Facts.get_global_add_global_eq _ _ _) | exact MF ].
  - rewrite Ctxt.Facts.get_global_add_global_neq in GET
      by (cbn [fst]; exact (not_eq_sym NE)).
    rewrite Ctxt.Facts.get_global_add_global_neq
      by (cbn [fst]; exact (not_eq_sym NE)).
    exact (GM id' fd GET).
Qed.

Lemma tr_cmd_wt:
  forall floor SS ctx d tail c tc t
         (TR: tr_cmd floor SS ctx d tail c tc t)
         (NT: list (AST.ident * type))
         (dctx: ctxt (type * bool) (type * bool) unit fundef vardef)
         (ictx: ctxt (type * bool) (type * bool) unit IR.Prog.fundef vardef)
         (WTd: Deep.Typing.wt_cmd dctx c t)
         (EPURE: ctxt_pure dctx = ctx)
         (INCL: forall id v, Maps.PTree.get id ctx = Some v ->
                             Maps.PTree.get id (ctxt_pure ictx) = Some v)
         (FLOOR: forall id v, Maps.PTree.get id ctx = Some v -> (id < floor)%positive)
         (SBNT: ListExt.SBinds NT)
         (TEMPS: forall id ty, In (id, ty) NT -> (floor <= id)%positive ->
                               exists b, Ctxt.get_pure id ictx = Some (ty, b))
         (COVT: forall id ty, In (id, ty) (IR.Cmd.cmd_temps tc) -> (floor <= id)%positive ->
                              In (id, ty) NT)
         (INTS: forall id ty, In (id, ty) (IR.Cmd.cmd_internals tc) ->
                              exists b, Ctxt.get_internal id ictx = Some (ty, b))
         (GM: globals_match dctx ictx),
    IR.Typing.wt_cmd ictx tc t.
Proof.
  intros floor SS ctx d tail c tc t TR.
  induction TR as [ ctx d tail e t TYPE
                  | ctx d tail b_id t_b c_b c_c tc_b tc_c t_c BINDER TRb IHb TRc IHc
                  | ctx d tail e c_t c_e tc_t tc_e t TRt IHt TRe IHe
                  | ctx d tail c_cond c_body tc_cond tc_body id_cond id_body
                        FRESHc FRESHb NEQ TRcond IHcond TRbody IHbody
                  | ctx d tail t_v e_v c_c tc_c t id_var LT FRESH TRc IHc
                  | ctx d tail n t
                  | ctx d tail n t e
                  | ctx d tail e_size t e_init id_p id_c id_i
                        FRESH1 FRESH2 FRESH3 NEQpc NEQpi NEQci
                  | ctx d tail e_ptr t
                  | ctx d tail e_ptr t e_val
                  | ctx d tail e_ptr
                  | ctx d tail e_ptr e_ofst
                  | ctx d tail e_ptr e_ofst
                  | ctx d tail e_l e_r
                  | ctx d f_id args t_out t_args LEN TARGS
                  | ctx d tail e_l e_r
                  | ctx d tail e_l e_r ];
    intros NT dctx ictx WTd EPURE INCL FLOOR SBNT TEMPS COVT INTS GM;
    subst ctx;
    assert (INCLt: forall id ty, Maps.PTree.get id (ctxt_pure dctx) = Some (ty, true) ->
                                 Maps.PTree.get id (ctxt_pure ictx) = Some (ty, true))
      by (intros id ty GET; exact (INCL id _ GET));
    cbn [IR.Cmd.cmd_temps IR.Cmd.cmd_internals] in COVT, INTS.
  - inversion WTd; subst.
    apply IR.Typing.wt_ret.
    exact (Expr.Facts.wt_expr_true_incl INCLt WTe).
  - inversion WTd as [ | ?dctx ?x ?c1 ?c2 ?t1 ?t2 UNBOUND WTm WTf | | | | | | | | | | | | | | | | ];
      subst.
    apply (IR.Typing.wt_bind (t_b := t_b) (b_b := false)).
    + exact (INCL b_id _ UNBOUND).
    + refine (IHb NT dctx ictx WTm eq_refl INCL FLOOR SBNT TEMPS _ _ GM).
      * intros id ty IN LE; exact (COVT id ty (or_intror (in_or_app _ _ _ (or_introl IN))) LE).
      * intros id ty IN; apply (INTS id ty); apply in_or_app; left; exact IN.
    + refine (IHc NT (Ctxt.set_pure b_id (t_b, true) dctx)
                (Ctxt.set_pure b_id (t_b, true) ictx) WTf eq_refl _ _ SBNT _ _ _ _).
      * intros id v GET; cbn [Ctxt.set_pure ctxt_pure] in GET |- *.
        rewrite Maps.PTree.gsspec in GET |- *.
        destruct (Coqlib.peq id b_id); [ exact GET | exact (INCL id v GET) ].
      * intros id v GET; cbn [Ctxt.set_pure ctxt_pure] in GET.
        rewrite Maps.PTree.gsspec in GET.
        destruct (Coqlib.peq id b_id) as [ -> | NE ]; [ exact BINDER | exact (FLOOR id v GET) ].
      * intros id ty IN LE.
        unfold Ctxt.get_pure; cbn [Ctxt.set_pure ctxt_pure].
        rewrite Maps.PTree.gso by (intros ->; lia).
        exact (TEMPS id ty IN LE).
      * intros id ty IN LE; exact (COVT id ty (or_intror (in_or_app _ _ _ (or_intror IN))) LE).
      * intros id ty IN.
        rewrite Ctxt.Facts.get_internal_set_pure.
        apply (INTS id ty); apply in_or_app; right; exact IN.
      * exact (globals_match_ext GM eq_refl eq_refl).
  - inversion WTd; subst.
    apply IR.Typing.wt_if.
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTcond).
    + refine (IHt NT dctx ictx WTthen eq_refl INCL FLOOR SBNT TEMPS _ _ GM).
      * intros id ty IN LE; exact (COVT id ty (in_or_app _ _ _ (or_introl IN)) LE).
      * intros id ty IN; apply (INTS id ty); apply in_or_app; left; exact IN.
    + refine (IHe NT dctx ictx WTelse eq_refl INCL FLOOR SBNT TEMPS _ _ GM).
      * intros id ty IN LE; exact (COVT id ty (in_or_app _ _ _ (or_intror IN)) LE).
      * intros id ty IN; apply (INTS id ty); apply in_or_app; right; exact IN.
  - inversion WTd; subst.
    destruct (INTS id_cond t_bool (or_introl eq_refl)) as ( b_c & INc ).
    destruct (INTS id_body t_unit (or_intror (or_introl eq_refl))) as ( b_b & INb ).
    apply (IR.Typing.wt_while (b_c := b_c) (b_b := b_b)).
    + exact INc.
    + exact INb.
    + refine (IHcond NT dctx ictx WTcond eq_refl INCL FLOOR SBNT TEMPS _ _ GM).
      * intros id ty IN LE; exact (COVT id ty (in_or_app _ _ _ (or_introl IN)) LE).
      * intros id ty IN; apply (INTS id ty); right; right; apply in_or_app; left; exact IN.
    + refine (IHbody NT dctx ictx WTbody eq_refl INCL FLOOR SBNT TEMPS _ _ GM).
      * intros id ty IN LE; exact (COVT id ty (in_or_app _ _ _ (or_intror IN)) LE).
      * intros id ty IN; apply (INTS id ty); right; right; apply in_or_app; right; exact IN.
  - inversion WTd; subst.
    assert (INV: In (id_var, t_unit) NT) by exact (COVT id_var t_unit (or_introl eq_refl) FRESH).
    destruct (TEMPS id_var t_unit INV FRESH) as ( b_v & GETv ).
    apply (IR.Typing.wt_bind (t_b := t_unit) (b_b := b_v)).
    + exact GETv.
    + apply IR.Typing.wt_write_var.
      exact (Expr.Facts.wt_expr_true_incl INCLt WTinit).
    + refine (IHc NT (Ctxt.push_stack tt dctx)
                (Ctxt.set_pure id_var (t_unit, true) ictx) WTcont eq_refl _ FLOOR SBNT _ _ _ _).
      * intros id v GET; cbn [Ctxt.set_pure ctxt_pure].
        rewrite Maps.PTree.gso by (intros ->; pose proof (FLOOR _ _ GET); lia).
        exact (INCL id v GET).
      * intros id ty IN LE.
        unfold Ctxt.get_pure; cbn [Ctxt.set_pure ctxt_pure].
        rewrite Maps.PTree.gsspec.
        destruct (Coqlib.peq id id_var) as [ -> | NE ];
          [ | exact (TEMPS id ty IN LE) ].
        rewrite (ListExt.SBinds_same_In_eq SBNT INV IN).
        exists true; reflexivity.
      * intros id ty IN LE; exact (COVT id ty (or_intror IN) LE).
      * intros id ty IN.
        rewrite Ctxt.Facts.get_internal_set_pure.
        exact (INTS id ty IN).
      * exact (globals_match_ext GM eq_refl eq_refl).
  - apply IR.Typing.wt_read_var.
  - inversion WTd; subst.
    apply IR.Typing.wt_write_var.
    exact (Expr.Facts.wt_expr_true_incl INCLt WT).
  - inversion WTd; subst.
    destruct (INTS id_p t_ptr (or_introl eq_refl)) as ( b_p & INp ).
    destruct (INTS id_c t_ofst (or_intror (or_introl eq_refl))) as ( b_c & INc ).
    destruct (INTS id_i t (or_intror (or_intror (or_introl eq_refl)))) as ( b_i & INi ).
    apply (IR.Typing.wt_alloc_ptr (b_p := b_p) (b_c := b_c) (b_i := b_i)).
    + exact (globals_match_exf_bound GM MALLOC).
    + exact INp.
    + exact INc.
    + exact INi.
    + exact NEQpc.
    + exact NEQpi.
    + exact NEQci.
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTsize).
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTinit).
  - inversion WTd; subst.
    apply IR.Typing.wt_read_ptr.
    exact (Expr.Facts.wt_expr_true_incl INCLt WTptr).
  - inversion WTd; subst.
    apply IR.Typing.wt_write_ptr.
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTptr).
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTval).
  - inversion WTd; subst.
    apply IR.Typing.wt_free_ptr.
    + exact (globals_match_exf_bound GM FREE).
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTptr).
  - inversion WTd; subst.
    apply IR.Typing.wt_shift_fw_ptr.
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTptr).
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTofst).
  - inversion WTd; subst.
    apply IR.Typing.wt_shift_bw_ptr.
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTptr).
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTofst).
  - inversion WTd; subst.
    apply IR.Typing.wt_ptr_eq.
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTl).
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTr).
  - inversion WTd; subst.
    + destruct (GM f_id _ FINDFN) as ( tfd & GETi & MF ).
      inversion MF as [ ?fn_d tfn TRf | ]; subst.
      assert (EARGS: ListExt.map_opt (type_expr (ctxt_pure dctx)) args
                     = Some (List.map snd fn.(fn_params))).
      { refine (ListExt.map_opt_Forall2 _ WT_args).
        intros ea ta TYa; exact (Expr.Facts.type_expr_correct TYa). }
      pose proof (TARGS _ EARGS) as ETA; subst t_args.
      rewrite <- (return_preserved TRf).
      apply (IR.Typing.wt_app (fn := tfn)).
      * exact GETi.
      * rewrite (map_snd_combine _ _ LEN), (params_preserved TRf); reflexivity.
      * rewrite (map_fst_combine _ _ LEN), (map_snd_combine _ _ LEN).
        eapply Forall2_impl; [ | exact WT_args ].
        intros ea ta TYa; exact (Expr.Facts.wt_expr_true_incl INCLt TYa).
    + destruct (GM f_id _ FINDFN) as ( tfd & GETi & MF ).
      inversion MF; subst.
      assert (EARGS: ListExt.map_opt (type_expr (ctxt_pure dctx)) args = Some sig.(sig_args)).
      { refine (ListExt.map_opt_Forall2 _ WT_args).
        intros ea ta TYa; exact (Expr.Facts.type_expr_correct TYa). }
      pose proof (TARGS _ EARGS) as ETA; subst t_args.
      apply (IR.Typing.wt_app_exf (nm := nm) (sg := sg)).
      * exact GETi.
      * rewrite (map_snd_combine _ _ LEN); destruct sig; exact SIG.
      * rewrite (map_fst_combine _ _ LEN), (map_snd_combine _ _ LEN).
        eapply Forall2_impl; [ | exact WT_args ].
        intros ea ta TYa; exact (Expr.Facts.wt_expr_true_incl INCLt TYa).
  - inversion WTd; subst.
    apply IR.Typing.wt_div.
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTl).
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTr).
  - inversion WTd; subst.
    apply IR.Typing.wt_mod.
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTl).
    + exact (Expr.Facts.wt_expr_true_incl INCLt WTr).
Qed.

Lemma tr_function_wt [fn tfn]
  [dglob: ctxt Empty_set Empty_set Empty_set fundef vardef]
  [iglob: ctxt Empty_set Empty_set Empty_set IR.Prog.fundef vardef]
  (TR: tr_function fn tfn)
  (WTd: Deep.Typing.wt_function dglob fn)
  (GM: globals_match dglob iglob):
  IR.Typing.wt_function iglob tfn.
Proof.
  destruct TR as [ floor TRA ].
  destruct (tr_fn_temps _ _ _ TRA) as ( D & ETMP & DFLOOR & SBD ).
  pose proof (params_temps_bound TRA) as BOUND.
  pose proof (tr_fn_params _ _ _ TRA) as EPAR.
  pose proof WTd.(wt_fn_params_sbinds) as SBp.
  pose proof WTd.(wt_fn_temps_sbinds) as SBt.
  assert (DLOW: forall id ty, In (id, ty) D -> (floor <= id)%positive)
    by (intros id ty IN; exact (proj1 (Forall_forall _ _) DFLOOR (id, ty) IN)).
  assert (ILOW: forall id ty, In (id, ty) tfn.(fn_internals) -> (floor <= id)%positive)
    by (intros id ty IN;
        exact (proj1 (Forall_forall _ _) (tr_fn_internals_floor _ _ _ TRA) (id, ty) IN)).
  assert (SBi: ListExt.SBinds tfn.(fn_temps)).
  { rewrite ETMP.
    apply SBinds_rev_append_intro; [ exact SBt | exact SBD | ].
    apply (proj2 (DBinds_iff_disjoint_fst _ _)).
    intros x INx INy.
    apply List.in_map_iff in INx as ( [ id ty ] & EQX & INx ).
    apply List.in_map_iff in INy as ( [ id' ty' ] & EQY & INy ).
    cbn [fst] in EQX, EQY; subst x id'.
    pose proof (DLOW _ _ INy) as LO.
    pose proof (BOUND id ty (in_or_app _ _ _ (or_intror INx))) as HI.
    lia. }
  assert (DBi: ListExt.DBinds fn.(fn_params) tfn.(fn_temps)).
  { rewrite ETMP.
    refine (proj2 (ListExt.DBinds_rev_append _ _ _)
              (conj WTd.(wt_fn_params_temps_distinct) _)).
    apply (proj2 (DBinds_iff_disjoint_fst _ _)).
    intros x INx INy.
    apply List.in_map_iff in INx as ( [ id ty ] & EQX & INx ).
    apply List.in_map_iff in INy as ( [ id' ty' ] & EQY & INy ).
    cbn [fst] in EQX, EQY; subst x id'.
    pose proof (DLOW _ _ INy) as LO.
    pose proof (BOUND id ty (in_or_app _ _ _ (or_introl INx))) as HI.
    lia. }
  constructor.
  - rewrite (tr_fn_return _ _ _ TRA), EPAR.
    pose (dctx := mk_function_ctxt fn.(fn_params) fn.(fn_temps) fn.(fn_internals) dglob).
    assert (GETINV: forall id ty b, Maps.PTree.get id (ctxt_pure dctx) = Some (ty, b) ->
                                    (b = true /\ In (id, ty) fn.(fn_params))
                                    \/ (b = false /\ In (id, ty) fn.(fn_temps)))
      by exact (Prog.Facts.mk_function_ctxt_pure_get_inv _ _ _ _ SBp SBt).
    refine (tr_cmd_wt _ _ _ _ _ _ _ _
              (tr_fn_body _ _ _ TRA (ctxt_pure dctx) _ _)
              tfn.(fn_temps) dctx _ WTd.(wt_fn_cmd) eq_refl _ _ SBi _
              (tr_fn_temps_cover _ _ _ TRA) _ _).
    + intros id ty GET.
      destruct (GETINV id ty true GET) as [ ( _ & INp ) | ( CONTRA & _ ) ];
        [ exact INp | discriminate CONTRA ].
    + intros id [ ty b ] GET.
      rewrite map_app; apply in_or_app.
      destruct (GETINV id ty b GET) as [ ( _ & INp ) | ( _ & INt ) ];
        [ left | right ]; exact (in_map fst _ _ ltac:(eassumption)).
    + intros id [ ty b ] GET.
      destruct (GETINV id ty b GET) as [ ( -> & INp ) | ( -> & INt ) ].
      * exact (Prog.Facts.mk_function_ctxt_pure_get_param _ _ _ _ SBp SBi DBi id ty INp).
      * refine (Prog.Facts.mk_function_ctxt_pure_get_temp _ _ _ _ SBp SBi DBi id ty _).
        rewrite ETMP; apply (proj2 (In_rev_append _ _ _)); left; exact INt.
    + intros id [ ty b ] GET.
      destruct (GETINV id ty b GET) as [ ( _ & IN ) | ( _ & IN ) ];
        apply (BOUND id ty); apply in_or_app; [ left | right ]; exact IN.
    + intros id ty IN _.
      exists false.
      exact (Prog.Facts.mk_function_ctxt_pure_get_temp _ _ _ _ SBp SBi DBi id ty IN).
    + intros id ty IN.
      exists false.
      exact (Prog.Facts.mk_function_ctxt_internal_get_in _ _ _ _
               (tr_fn_internals_sbinds _ _ _ TRA) id ty (tr_fn_internals_cover _ _ _ TRA id ty IN)).
    + exact (globals_match_ext GM eq_refl eq_refl).
  - exact (tr_fn_extra _ _ _ TRA).
  - rewrite EPAR; exact SBp.
  - exact SBi.
  - rewrite EPAR; exact DBi.
  - exact (tr_fn_internals_sbinds _ _ _ TRA).
  - apply (proj2 (DBinds_iff_disjoint_fst _ _)).
    intros x INx INy.
    rewrite map_app in INx; apply in_app_or in INx as [ INx | INx ].
    + rewrite EPAR in INx.
      apply List.in_map_iff in INx as ( [ id ty ] & EQX & INx ).
      apply List.in_map_iff in INy as ( [ id' ty' ] & EQY & INy ).
      cbn [fst] in EQX, EQY; subst x id'.
      pose proof (ILOW _ _ INy) as LO.
      pose proof (BOUND id ty (in_or_app _ _ _ (or_introl INx))) as HI.
      lia.
    + exact (proj1 (DBinds_iff_disjoint_fst _ _) (tr_fn_temps_internals_distinct _ _ _ TRA) x INx INy).
Qed.

Lemma match_globdefs_wt:
  forall (ctx: program) dl tl
         (MDEFS: list_forall2
                   (Linking.match_ident_globdef (fun _: program => match_fundef) match_varinfo ctx)
                   dl tl)
         (dctx: ctxt Empty_set Empty_set Empty_set fundef vardef)
         (ictx: ctxt Empty_set Empty_set Empty_set IR.Prog.fundef vardef)
         (WTd: ListExt.FoldLeft
                 (fun c idg => Deep.Typing.wt_globdef c (fst idg) (snd idg))
                 (fun c idg => Ctxt.add_global c idg) dctx dl)
         (GM: globals_match dctx ictx),
    ListExt.FoldLeft
      (fun c idg => IR.Typing.wt_globdef c (fst idg) (snd idg))
      (fun c idg => Ctxt.add_global c idg) ictx tl.
Proof.
  intros ctx dl tl MDEFS.
  induction MDEFS as [ | [ id g ] dl [ tid tg ] tl MIG MDEFS IH ];
    intros dctx ictx WTd GM; [ constructor | ].
  destruct MIG as ( EID & MG ); cbn [fst snd] in EID, MG; subst tid.
  inversion WTd as [ | ?acc ?x ?rest WTdef WTrest ]; subst.
  constructor.
  - cbn [fst snd] in WTdef |- *.
    inversion MG as [ ctx' fd tfd LO MF | v tv MV ]; subst.
    + inversion WTdef as [ ?c ?i ?f WTfd | ]; subst.
      inversion MF as [ fn tfn TRf | ef ]; subst.
      * inversion WTfd as [ ?c ?func WTf | | ]; subst.
        exact (wt_Gfun _ _ _ ictx id (AST.Internal tfn)
                 (wt_Internal _ _ _ ictx tfn (tr_function_wt TRf WTf GM))).
      * inversion WTfd as [ | ?c ?ef0 sig SIG | ?c nm sg ]; subst.
        -- exact (wt_Gfun _ _ _ ictx id (AST.External ef)
                    (wt_External _ _ _ ictx ef sig SIG)).
        -- exact (wt_Gfun _ _ _ ictx id (AST.External (AST.EF_runtime nm sg))
                    (wt_External_runtime _ _ _ ictx nm sg)).
    + inversion WTdef as [ | ?c ?i ?v WTv ]; subst.
      inversion MV as [ i1 i2 init ro vo MVI ]; subst.
      unfold match_varinfo in MVI; subst i2.
      exact (wt_Gvar _ _ _ ictx id _ WTv).
  - exact (IH _ _ WTrest (globals_match_add GM ctx id g tg MG)).
Qed.

Lemma match_prog_wt [p tp]
  (MP: match_prog p tp)
  (WTp: Deep.Typing.wt_program p):
  IR.Typing.wt_program tp.
Proof.
  destruct MP as ( MDEFS & EMAIN & EPUB ).
  cbn [AST.prog_defs AST.prog_main AST.prog_public program_of_program
         prog_defs prog_main prog_public] in MDEFS, EMAIN, EPUB.
  constructor; cbn [prog_defs prog_public prog_main prog_extra].
  - exact (match_globdefs_wt p _ _ MDEFS _ _ WTp.(wt_prog_defs)
             globals_match_emp).
  - intros id IN.
    rewrite EPUB in IN.
    destruct (WTp.(wt_prog_public) id IN) as ( gdef & INg ).
    assert (INf: In id (List.map fst tp.(prog_defs))).
    { rewrite (MatchDefs.match_defs_map_fst MDEFS); exact (in_map fst _ _ INg). }
    apply List.in_map_iff in INf as ( [ id' gdef' ] & EQ & INf ).
    cbn [fst] in EQ; subst id'.
    exists gdef'; exact INf.
  - rewrite EMAIN.
    destruct WTp.(wt_prog_main) as ( f_main & INm ).
    exact (MatchDefs.match_defs_In_fun MDEFS INm).
  - exact (MatchDefs.match_defs_norepet MDEFS WTp.(wt_prog_defs_sbinds)).
  - exact I.
Qed.

Section Env.

  Context [Ad: Addr.type] [Pt: Ptr.type Ad].

  Definition env_incl (e1 e2: Maps.PTree.t (value Pt)): Prop :=
    forall x v, Maps.PTree.get x e1 = Some v -> Maps.PTree.get x e2 = Some v.

  Definition env_dom [A: Type] (binders: list (AST.ident * A))
    (e: Maps.PTree.t (value Pt)): Prop :=
    forall x v, Maps.PTree.get x e = Some v -> In x (List.map fst binders).

  Lemma env_incl_refl e: env_incl e e.
  Proof using Type. intros x v GET; exact GET. Qed.

  Lemma env_incl_set [e1 e2] x v (ENV: env_incl e1 e2):
    env_incl (Maps.PTree.set x v e1) (Maps.PTree.set x v e2).
  Proof using Type.
    intros y w GET.
    rewrite Maps.PTree.gsspec in GET |- *.
    destruct (Coqlib.peq y x); [ exact GET | exact (ENV y w GET) ].
  Qed.

  Lemma env_incl_remove_l [e1 e2] x (ENV: env_incl e1 e2):
    env_incl (Maps.PTree.remove x e1) e2.
  Proof using Type.
    intros y w GET.
    rewrite Maps.PTree.grspec in GET.
    destruct (Maps.PTree.elt_eq y x); [ discriminate GET | exact (ENV y w GET) ].
  Qed.

  Lemma env_incl_set_fresh [e1 e2] x v
    (FRESH: Maps.PTree.get x e1 = None)
    (ENV: env_incl e1 e2):
    env_incl e1 (Maps.PTree.set x v e2).
  Proof using Type.
    intros y w GET.
    rewrite Maps.PTree.gsspec.
    destruct (Coqlib.peq y x) as [ -> | NE ];
      [ rewrite FRESH in GET; discriminate GET | exact (ENV y w GET) ].
  Qed.

  Lemma env_dom_set [A: Type] [bs: list (AST.ident * A)] [e] x t v
    (IN: In (x, t) bs) (D: env_dom bs e):
    env_dom bs (Maps.PTree.set x v e).
  Proof using Type.
    intros y w GET.
    rewrite Maps.PTree.gsspec in GET.
    destruct (Coqlib.peq y x) as [ -> | NE ];
      [ exact (in_map fst _ _ IN) | exact (D y w GET) ].
  Qed.

  Lemma env_dom_remove [A: Type] [bs: list (AST.ident * A)] [e] x (D: env_dom bs e):
    env_dom bs (Maps.PTree.remove x e).
  Proof using Type.
    intros y w GET.
    rewrite Maps.PTree.grspec in GET.
    destruct (Maps.PTree.elt_eq y x); [ discriminate GET | exact (D y w GET) ].
  Qed.

  Lemma env_dom_fresh [A: Type] [bs: list (AST.ident * A)] [e] x (D: env_dom bs e)
    (NIN: ~ In x (List.map fst bs)):
    Maps.PTree.get x e = None.
  Proof using Type.
    destruct (Maps.PTree.get x e) as [ v | ] eqn:GET; [ | reflexivity ].
    exact (False_ind _ (NIN (D x v GET))).
  Qed.

  Lemma env_dom_empty [A: Type] (bs: list (AST.ident * A)):
    env_dom bs Maps.PTree.Empty.
  Proof using Type.
    intros x v GET; rewrite Maps.PTree.gempty in GET; discriminate GET.
  Qed.

  Lemma eval_incl [e1 e2] (ENV: env_incl e1 e2) [ex v]
    (EVAL: eval ex e1 = Some v):
    eval ex e2 = Some v.
  Proof using Type.
    revert v EVAL.
    induction ex; intros v' EVAL; cbn in EVAL |- *.
    - exact (ENV _ _ EVAL).
    - exact EVAL.
    - exact EVAL.
    - exact EVAL.
    - exact EVAL.
    - exact EVAL.
    - destruct (eval ex e1) as [ w | ] eqn:E1; [ | discriminate EVAL ].
      rewrite (IHex _ eq_refl); exact EVAL.
    - destruct (eval ex1 e1) as [ w1 | ] eqn:E1; [ | discriminate EVAL ].
      destruct (eval ex2 e1) as [ w2 | ] eqn:E2;
        [ | destruct w1; discriminate EVAL ].
      rewrite (IHex1 _ eq_refl), (IHex2 _ eq_refl); exact EVAL.
    - destruct (eval ex1 e1) as [ w1 | ] eqn:E1; [ | discriminate EVAL ].
      destruct (eval ex2 e1) as [ w2 | ] eqn:E2;
        [ | destruct w1; discriminate EVAL ].
      rewrite (IHex1 _ eq_refl), (IHex2 _ eq_refl); exact EVAL.
    - destruct (eval ex1 e1) as [ w1 | ] eqn:E1; [ | discriminate EVAL ].
      destruct (eval ex2 e1) as [ w2 | ] eqn:E2;
        [ | destruct w1; discriminate EVAL ].
      rewrite (IHex1 _ eq_refl), (IHex2 _ eq_refl); exact EVAL.
  Qed.

  Lemma eval_list_incl [e1 e2] (ENV: env_incl e1 e2) [exs vs]
    (EVAL: ListExt.map_opt (fun ex => eval ex e1) exs = Some vs):
    ListExt.map_opt (fun ex => eval ex e2) exs = Some vs.
  Proof using Type.
    revert vs EVAL.
    induction exs as [ | ex exs IH ]; intros vs EVAL; cbn in EVAL |- *;
      [ exact EVAL | ].
    destruct (eval ex e1) as [ v | ] eqn:E1; [ | discriminate EVAL ].
    destruct (ListExt.map_opt (fun ex => eval ex e1) exs) as [ ws | ] eqn:E2;
      [ | discriminate EVAL ].
    rewrite (eval_incl ENV E1), (IH _ eq_refl).
    exact EVAL.
  Qed.

End Env.

Section EnvState.

  Context {Sm: State.type}.

  Lemma env_dom_set_params [A: Type] (bs: list (AST.ident * A)) inits:
    env_dom bs (OpSem.set_params (Sm := Sm) bs inits).
  Proof using Type.
    revert inits.
    induction bs as [ | [ id a ] bs IH ]; intros [ | v inits ];
      cbn [OpSem.set_params]; try apply env_dom_empty.
    intros y w GET.
    rewrite Maps.PTree.gsspec in GET.
    destruct (Coqlib.peq y id) as [ -> | NE ];
      [ left; reflexivity | ].
    right; exact (IH inits y w GET).
  Qed.

End EnvState.

Lemma symbols_preserved [p tp] (MP: match_prog p tp) (id: AST.ident):
  Globalenvs.Genv.find_symbol (Globalenvs.Genv.globalenv tp) id
  = Globalenvs.Genv.find_symbol (Globalenvs.Genv.globalenv p) id.
Proof.
  exact (Globalenvs.Genv.find_symbol_match MP id).
Qed.

Lemma function_ptr_translated [p tp] (MP: match_prog p tp) [b fd]
  (FIND: Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv p) b = Some fd):
  exists tfd,
    Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv tp) b = Some tfd
    /\ match_fundef fd tfd.
Proof.
  destruct (Globalenvs.Genv.find_funct_ptr_match MP _ FIND)
    as ( cunit & tfd & FINDt & MF & _ ).
  exists tfd; split; assumption.
Qed.

Lemma senv_preserved [p tp] (MP: match_prog p tp):
  Globalenvs.Senv.equiv (Globalenvs.Genv.to_senv (Globalenvs.Genv.globalenv p))
    (Globalenvs.Genv.to_senv (Globalenvs.Genv.globalenv tp)).
Proof.
  exact (Globalenvs.Genv.senv_match MP).
Qed.
