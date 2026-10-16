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

From compcert.common Require AST Linking.
From compcert.common Require Import Globalenvs.
From compcert.lib Require Import Coqlib Maps.

From GallinaC.Utils Require NExt ReflectExt.
From GallinaC.Utils Require Import ListExt.

From GallinaC.Imp Require Intops.
From GallinaC.Imp Require Import Store State.

From GallinaC.Compiler.Common Require Linker.
From GallinaC.Compiler.Common Require Import Types Ctxt Semantics.
From GallinaC.Compiler.IR Require Lemmas Linker Semantics.
From GallinaC.Compiler.IR Require Import Cmd Prog Typing.
From GallinaC.Compiler.Passes Require Import TCO.

Inductive is_chain: list AST.ident -> cmd -> Prop :=
| is_chain_ret: forall aliases y t
                       (IN: In y aliases),
    is_chain aliases (c_ret (e_var y) t)
| is_chain_bind: forall aliases y t_b c1 c2 t_c
                        (CHAIN1: is_chain aliases c1)
                        (CHAIN2: is_chain (y :: aliases) c2),
    is_chain aliases (c_bind y t_b c1 c2 t_c)
.

Lemma chain_check_spec:
  forall aliases c, Bool.reflect (is_chain aliases c) (chain_check aliases c).
Proof.
  intros aliases c.
  apply Bool.iff_reflect; split.
  - intros CHAIN; induction CHAIN; cbn.
    + apply existsb_exists.
      exists y; split; [ exact IN | apply Pos.eqb_refl ].
    + rewrite IHCHAIN1, IHCHAIN2; reflexivity.
  - revert aliases; induction c; intros aliases CHK; cbn in CHK; try discriminate.
    + destruct e; try discriminate.
      apply existsb_exists in CHK as ( z & IN & EQ ).
      apply Pos.eqb_eq in EQ; subst.
      apply is_chain_ret; exact IN.
    + apply andb_prop in CHK as [ CHK1 CHK2 ].
      apply is_chain_bind.
      * apply IHc1; exact CHK1.
      * apply IHc2; exact CHK2.
Qed.

Lemma transf_cmd_bind_eq:
  forall tail x t_b c_b c_c t_c,
    transf_cmd tail (c_bind x t_b c_b c_c t_c)
    = if rewrite_guard tail x c_b c_c t_c
      then c_b
      else c_bind x t_b (transf_cmd false c_b) (transf_cmd tail c_c) t_c.
Proof.
  intros tail x t_b c_b c_c t_c.
  destruct c_b; reflexivity.
Qed.

Lemma transf_cmd_false:
  forall c, transf_cmd false c = c.
Proof.
  induction c as [ | x t_b c_b IHb c_c IHc t_c | e c1 IH1 c2 IH2 t
                 | c_cond IHcond id_cond c_body IHbody id_body | | | | | | | | | | | | ];
    try reflexivity.
  - rewrite transf_cmd_bind_eq, IHb, IHc.
    destruct c_b; reflexivity.
  - cbn [ transf_cmd ]; rewrite IH1, IH2; reflexivity.
  - cbn [ transf_cmd ]; rewrite IHcond, IHbody; reflexivity.
Qed.

Lemma sig_preserved:
  forall fd sig (FS: funsig fd sig), funsig (transf_fundef fd) sig.
Proof.
  intros fd sig FS.
  destruct fd; inversion FS; subst; cbn.
  - apply (funsig_Internal (transf_function f)).
  - apply funsig_External; assumption.
Qed.

Definition transf_globdef (g: globdef): globdef :=
  match g with
  | AST.Gfun fd => AST.Gfun (transf_fundef fd)
  | AST.Gvar v => AST.Gvar v
  end.

Lemma transform_program_globdef_pair:
  forall (idg: AST.ident * globdef),
    AST.transform_program_globdef transf_fundef idg = (fst idg, transf_globdef (snd idg)).
Proof.
  intros [ id [ fd | v ] ]; reflexivity.
Qed.

Definition gmatch (g tg: globdef): Prop := tg = transf_globdef g.

Lemma get_global_match
  [P I S: Type] [ctx ctx': ctxt P I S fundef vardef]
  (MGE: Genv.match_genvs gmatch (ctxt_global ctx) (ctxt_global ctx'))
  [id g]
  (GET: get_global id ctx = Some g)
  : get_global id ctx' = Some (transf_globdef g).
Proof.
  destruct MGE as [ MNEXT MSYMB MDEFS ].
  unfold get_global in *.
  assert (FS: Genv.find_symbol (ctxt_global ctx') id = Genv.find_symbol (ctxt_global ctx) id)
    by apply MSYMB.
  rewrite FS.
  destruct (Genv.find_symbol (ctxt_global ctx) id) as [ b | ]; [ | discriminate ].
  specialize (MDEFS b).
  change (Genv.find_def (ctxt_global ctx) b = Some g) in GET.
  change (option_rel gmatch (Genv.find_def (ctxt_global ctx) b)
                            (Genv.find_def (ctxt_global ctx') b)) in MDEFS.
  rewrite GET in MDEFS.
  inversion MDEFS as [ | g1 g2 REL E1 E2 ].
  unfold gmatch in REL; subst.
  congruence.
Qed.

Lemma transf_cmd_wt
  [ctx ctx': ctxt (type * bool) (type * bool) unit fundef vardef]
  (EQPURE: ctxt_pure ctx = ctxt_pure ctx')
  (EQINTERNAL: ctxt_internal ctx = ctxt_internal ctx')
  (GMAP: forall id g, get_global id ctx = Some g ->
                      get_global id ctx' = Some (transf_globdef g))
  [c t]
  (WT: wt_cmd ctx c t)
  (tail: bool)
  : wt_cmd ctx' (transf_cmd tail c) t.
Proof.
  revert ctx' EQPURE EQINTERNAL GMAP tail.
  induction WT; intros ctx' EQPURE EQINTERNAL GMAP tail;
    destruct ctx' as [ pure' internal' stack' glob' ];
    cbn in EQPURE, EQINTERNAL; subst pure' internal';
    try (cbn; econstructor; eassumption; fail).
  - rewrite transf_cmd_bind_eq.
    destruct (rewrite_guard tail id_b c_b c_c t_c) eqn:GUARD.
    + destruct c_b as [ | | | | | | | | | | | | | f t_out args | | ];
        try discriminate GUARD.
      apply andb_prop in GUARD as [ _ GTYPE ].
      apply (ReflectExt.reflect_eq_of_true type_eqb_spec) in GTYPE; subst t_c.
      assert (TB: t_b = t_out) by (inversion WT1; subst; reflexivity).
      subst t_b.
      refine (IHWT1 _ _ _ _ false); [ reflexivity | reflexivity | exact GMAP ].
    + apply (wt_bind (t_b := t_b) (b_b := b_b)).
      * exact BINDABLE.
      * apply IHWT1; [ reflexivity | reflexivity | exact GMAP ].
      * apply IHWT2; [ reflexivity | reflexivity | exact GMAP ].
  - cbn; apply wt_if.
    + exact WTcond.
    + apply IHWT1; [ reflexivity | reflexivity | exact GMAP ].
    + apply IHWT2; [ reflexivity | reflexivity | exact GMAP ].
  - cbn; apply (wt_while (b_c := b_c) (b_b := b_b)).
    + exact BOUNDcond.
    + exact BOUNDbody.
    + apply IHWT1; [ reflexivity | reflexivity | exact GMAP ].
    + apply IHWT2; [ reflexivity | reflexivity | exact GMAP ].
  - cbn; apply (wt_alloc_ptr (b_p := b_p) (b_c := b_c) (b_i := b_i)); try assumption.
    destruct MALLOC as ( id_m & GET ).
    exists id_m; exact (GMAP _ _ GET).
  - cbn; apply wt_free_ptr; [ | exact WTptr ].
    destruct FREE as ( id_f & GET ).
    exists id_f; exact (GMAP _ _ GET).
  - cbn; apply (wt_app (fn := transf_function fn)).
    + exact (GMAP _ _ FINDfn).
    + exact EQargs.
    + exact WTargs.
  - cbn; apply (wt_app_exf (nm := nm) (sg := sg)).
    + exact (GMAP _ _ FINDfn).
    + exact SIG.
    + exact WTargs.
Qed.

Lemma transf_function_wt
  [ctx ctx': ctxt Empty_set Empty_set Empty_set fundef vardef]
  (GMAP: forall id g, get_global id ctx = Some g ->
                      get_global id ctx' = Some (transf_globdef g))
  [f: function]
  (WT: wt_function ctx f)
  : wt_function ctx' (transf_function f).
Proof.
  destruct WT as [ WTCMD WTEXTRA SBPARAMS SBTEMPS DBLOCALS SBINTERNALS DBINTERNALS ].
  constructor; try assumption.
  refine (transf_cmd_wt _ _ _ WTCMD true).
  - reflexivity.
  - reflexivity.
  - exact GMAP.
Qed.

Lemma transf_fundef_wt
  [ctx ctx': ctxt Empty_set Empty_set Empty_set fundef vardef]
  (GMAP: forall id g, get_global id ctx = Some g ->
                      get_global id ctx' = Some (transf_globdef g))
  [fd: fundef]
  (WT: wt_fundef ctx fd)
  : wt_fundef ctx' (transf_fundef fd).
Proof.
  destruct WT as [ ? f WTF | ? ef sig SIG | ? name sg ]; cbn.
  - apply wt_Internal.
    exact (transf_function_wt GMAP WTF).
  - eapply wt_External; exact SIG.
  - apply wt_External_runtime.
Qed.

Lemma transf_globdef_wt
  [ctx ctx': ctxt Empty_set Empty_set Empty_set fundef vardef]
  (GMAP: forall id g, get_global id ctx = Some g ->
                      get_global id ctx' = Some (transf_globdef g))
  [id g]
  (WT: wt_globdef ctx id g)
  : wt_globdef ctx' id (transf_globdef g).
Proof.
  destruct WT as [ ? ? fd WTF | ? ? v WTV ]; cbn.
  - apply wt_Gfun.
    exact (transf_fundef_wt GMAP WTF).
  - apply wt_Gvar.
    exact WTV.
Qed.

Lemma match_genvs_add_global
  [P I S: Type] [ctx ctx': ctxt P I S fundef vardef]
  (MGE: Genv.match_genvs gmatch (ctxt_global ctx) (ctxt_global ctx'))
  (id: AST.ident) (g: globdef)
  : Genv.match_genvs gmatch
      (ctxt_global (add_global ctx (id, g)))
      (ctxt_global (add_global ctx' (id, transf_globdef g))).
Proof.
  apply Genv.add_global_match; [ exact MGE | reflexivity ].
Qed.

Lemma transf_prog_defs_wt:
  forall defs (ctx ctx': ctxt Empty_set Empty_set Empty_set fundef vardef)
         (MGE: Genv.match_genvs gmatch (ctxt_global ctx) (ctxt_global ctx'))
         (WTDEFS: FoldLeft
                    (fun ctx idg => wt_globdef ctx (fst idg) (snd idg))
                    (fun ctx idg => add_global ctx idg)
                    ctx defs),
    FoldLeft
      (fun ctx idg => wt_globdef ctx (fst idg) (snd idg))
      (fun ctx idg => add_global ctx idg)
      ctx' (List.map (AST.transform_program_globdef transf_fundef) defs).
Proof.
  induction defs as [ | [ id g ] rest IH ]; intros ctx ctx' MGE WTDEFS;
    inversion WTDEFS as [ | ? ? ? WTG WTREST ]; subst; cbn [ List.map ].
  - constructor.
  - rewrite transform_program_globdef_pair; cbn [ fst snd ].
    constructor; cbn [ fst snd ].
    + apply (transf_globdef_wt (ctx := ctx)); [ | exact WTG ].
      intros id' g' GET.
      exact (get_global_match MGE GET).
    + apply (IH (add_global ctx (id, g))).
      * apply match_genvs_add_global; exact MGE.
      * exact WTREST.
Qed.

Lemma map_transform_program_globdef_eq:
  forall defs,
    List.map (AST.transform_program_globdef transf_fundef) defs
    = List.map (fun ab => (fst ab, transf_globdef (snd ab))) defs.
Proof.
  induction defs as [ | idg rest IH ]; cbn; [ reflexivity | ].
  rewrite transform_program_globdef_pair, IH; reflexivity.
Qed.

Lemma transf_program_wt:
  forall p (WTp: wt_program p),
    wt_program (transf_program p).
Proof.
  intros p WTp.
  destruct WTp as [ DEFS PUBLIC MAIN SBINDS _ ].
  constructor; cbn [ transf_program prog_defs prog_public prog_main prog_extra ].
  - apply (transf_prog_defs_wt _ (ctxt_emp _ _ _ _ _ p.(prog_public))); [ | exact DEFS ].
    constructor; cbn; intros.
    + reflexivity.
    + reflexivity.
    + rewrite ! PTree.gempty; constructor.
  - intros id IN.
    destruct (PUBLIC id IN) as [ gdef INDEF ].
    exists (transf_globdef gdef).
    rewrite map_transform_program_globdef_eq.
    exact (in_map (fun ab => (fst ab, transf_globdef (snd ab))) _ _ INDEF).
  - destruct MAIN as [ f_main IN ].
    exists (transf_fundef f_main).
    exact (in_map (AST.transform_program_globdef transf_fundef) _ _ IN).
  - rewrite map_transform_program_globdef_eq.
    apply SBinds_map; exact SBINDS.
  - exact I.
Qed.

Section Match.

  Definition match_fundef (p: program): fundef -> fundef -> Prop :=
    fun fd tfd => tfd = transf_fundef fd.

  Definition match_varinfo: vardef -> vardef -> Prop := eq.

  Definition match_prog (p tp: program): Prop :=
    Linking.match_program_gen
      match_fundef
      match_varinfo
      p
      (program_of_program p)
      (program_of_program tp).

  Lemma transf_program_match:
    forall p, match_prog p (transf_program p).
  Proof.
    intros p.
    split; [ | split; reflexivity ].
    cbn [ transf_program program_of_program AST.prog_defs prog_defs ].
    induction (prog_defs p) as [ | [ id g ] rest IH ]; cbn.
    - constructor.
    - constructor; [ | exact IH ].
      split; cbn.
      + destruct g; reflexivity.
      + destruct g as [ fd | v ]; cbn.
        * apply (Linking.match_globdef_fun _ _ _ p);
            [ apply Linking.linkorder_refl | reflexivity ].
        * apply Linking.match_globdef_var.
          destruct v; constructor; reflexivity.
  Qed.

End Match.

Lemma match_prog_transf_program:
  forall p tp (MATCH: match_prog p tp), tp = transf_program p.
Proof.
  intros p tp MATCH.
  destruct MATCH as ( DEFS & MAIN & PUBLIC ).
  destruct tp as [ tdefs tpublic tmain [] ].
  cbn in DEFS, MAIN, PUBLIC.
  unfold transf_program.
  subst tpublic tmain.
  destruct (prog_extra p).
  f_equal.
  induction DEFS as [ | [ id g ] rest [ tid tg ] trest REL DEFS IH ]; cbn.
  - reflexivity.
  - rewrite <- IH; f_equal.
    destruct REL as [ ID MG ]; cbn in ID, MG; subst tid.
    destruct MG as [ ctx' fd tfd LO MF | v tv MV ].
    + unfold match_fundef in MF; subst tfd; reflexivity.
    + destruct MV as [ info tinfo init ro vo MI ].
      unfold match_varinfo in MI; subst tinfo; reflexivity.
Qed.

Section TRANSLATION.

  Variable prog tprog: program.
  Hypothesis TRANSL: match_prog prog tprog.

  Let ge := Genv.globalenv (program_of_program prog).
  Let tge := Genv.globalenv (program_of_program tprog).

  Lemma symbols_preserved:
    forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
  Proof using TRANSL.
    intros id.
    apply (Genv.find_symbol_match TRANSL).
  Qed.

  Lemma function_ptr_translated:
    forall b fd
           (FIND: Genv.find_funct_ptr ge b = Some fd),
      Genv.find_funct_ptr tge b = Some (transf_fundef fd).
  Proof using TRANSL.
    intros b fd FIND.
    destruct (Genv.find_funct_ptr_match TRANSL _ FIND) as ( cu & tf & FIND' & MF & _ ).
    unfold match_fundef in MF; subst tf.
    exact FIND'.
  Qed.

  Lemma senv_preserved:
    Senv.equiv ge tge.
  Proof using TRANSL.
    apply (Genv.senv_match TRANSL).
  Qed.

  Lemma match_program_main:
    tprog.(prog_main) = prog.(prog_main).
  Proof using TRANSL.
    destruct TRANSL as ( _ & MAIN & _ ).
    exact MAIN.
  Qed.

End TRANSLATION.

Section InitState.

  Context {Sm: State.type}.

  Lemma transf_init_state:
    forall p,
      IR.Semantics.init_state (Sm := Sm) (transf_program p)
      = IR.Semantics.init_state (Sm := Sm) p.
  Proof.
    intros p.
    unfold IR.Semantics.init_state; cbn [ transf_program prog_defs ].
    generalize (State.emp_state (Sm := Sm)) as s.
    induction (prog_defs p) as [ | [ id g ] rest IH ]; intros s; [ reflexivity | ].
    destruct g as [ fd | v ];
      cbn [ List.map AST.transform_program_globdef IR.Semantics.alloc_globals ].
    - exact (IH s).
    - destruct (IR.Semantics.alloc_global s (AST.Gvar v)); [ apply IH | reflexivity ].
  Qed.

End InitState.

Section STORE_MATCH.

  Context {Sm: State.type}.

  Local Open Scope separation_scope.

  Inductive stack_block :=
  | sb_live (nms: list (@var_name Sm))
  | sb_dead (nms: list (@var_name Sm)).

  Fixpoint smatch (F: list stack_block) (st_s st_t: @m_st Sm): Prop :=
    match F with
    | [] => st_s = st_t
    | sb_live nms :: F' =>
        exists st_s0 st_t0: @m_st Sm,
          smatch F' st_s0 st_t0
          /\ layered st_s0 nms st_s
          /\ layered st_t0 nms st_t
          /\ st_t $<= st_s
    | sb_dead nms :: F' =>
        exists st_s0: @m_st Sm,
          smatch F' st_s0 st_t
          /\ layered st_s0 nms st_s
    end.

  Record state_match (F: list stack_block) (s ts: Sm): Prop :=
    mk_state_match {
        sm_store: smatch F (store s) (store ts);
        sm_scnt: scnt ts = scnt s;
        sm_heap: heap ts = heap s;
        sm_alc: alc ts = alc s;
      }.

  Lemma smatch_init: forall st: @m_st Sm, smatch [] st st.
  Proof using Type.
    intros st; exact eq_refl.
  Qed.

  Lemma smatch_sub:
    forall F (st_s st_t: @m_st Sm) (SM: smatch F st_s st_t), st_t $<= st_s.
  Proof using Type.
    induction F as [ | [ nms | nms ] F IH ]; intros st_s st_t SM; cbn [smatch] in SM.
    - subst st_t; exact (substate_refl _).
    - destruct SM as ( _ & _ & _ & _ & _ & SUB ); exact SUB.
    - destruct SM as ( st_s0 & SM0 & LAYS ).
      exact (substate_tran _ _ _ (IH _ _ SM0) (layered_sub LAYS)).
  Qed.

  Lemma smatch_dominates:
    forall F (st_s st_t: @m_st Sm) [Cn: Counter.type] (c: Cn)
           (SM: smatch F st_s st_t)
           (DOM: dominates st_s c),
      dominates st_t c.
  Proof using Type.
    intros F st_s st_t Cn c SM DOM.
    exact (dominates_sub_mem _ _ _ (smatch_sub F st_s st_t SM) DOM).
  Qed.

  Lemma smatch_stack_block_alloc:
    forall F (st_s st_t: @m_st Sm) (c: SCnt Sm) (v: value (@ptr_t Sm)) (n: N)
           st_s' c' nms
           (SM: smatch F st_s st_t)
           (DOM: dominates st_s c)
           (ALLOC: stack_block_alloc v n st_s c = Some (st_s', c', nms)),
    exists st_t',
      stack_block_alloc v n st_t c = Some (st_t', c', nms)
      /\ smatch (sb_live nms :: F) st_s' st_t'.
  Proof using Type.
    intros F st_s st_t c v n st_s' c' nms SM DOM ALLOC.
    destruct (stack_block_alloc_sub v n (smatch_sub F st_s st_t SM) ALLOC)
      as ( st_t' & ALLOCT & SUB' ).
    exists st_t'; split; [ exact ALLOCT | ].
    cbn [smatch]; exists st_s, st_t.
    split; [ exact SM | ].
    split; [ exact (stack_block_alloc_layered DOM v ALLOC) | ].
    split; [ | exact SUB' ].
    exact (stack_block_alloc_layered (smatch_dominates F st_s st_t c SM DOM) v ALLOCT).
  Qed.

  Lemma smatch_lookup:
    forall nms F (st_s st_t: @m_st Sm) n nm
           (SM: smatch (sb_live nms :: F) st_s st_t)
           (NTH: List.nth_error nms n = Some nm),
      lookup st_t nm = lookup st_s nm.
  Proof using Type.
    intros nms F st_s st_t n nm SM NTH.
    cbn [smatch] in SM.
    destruct SM as ( st_s0 & st_t0 & _ & _ & LAYT & SUB ).
    destruct (layered_nth LAYT n nm NTH) as ( a & w & REF & _ & CELL ).
    exact (eq_sym (lookup_mono SUB REF CELL)).
  Qed.

  Lemma smatch_mutate:
    forall nms F (st_s st_t: @m_st Sm) n nm (v: value (@ptr_t Sm)) (st_s': @m_st Sm)
           (SM: smatch (sb_live nms :: F) st_s st_t)
           (NTH: List.nth_error nms n = Some nm)
           (MUTATE: mutate st_s nm v = Some st_s'),
    exists st_t': @m_st Sm,
      mutate st_t nm v = Some st_t'
      /\ smatch (sb_live nms :: F) st_s' st_t'.
  Proof using Type.
    intros nms F st_s st_t n nm v st_s' SM NTH MUTATE.
    cbn [smatch] in SM.
    destruct SM as ( st_s0 & st_t0 & SM0 & LAYS & LAYT & SUB ).
    destruct (layered_replace LAYT n nm NTH v) as ( st_t' & MUTT & LAYT' ).
    destruct SUB as ( d & SUMD ).
    destruct (mutate_partition SUMD MUTT) as ( st_s'' & MUTS & SUMD' ).
    assert (EST: st_s'' = st_s') by congruence; subst st_s''.
    exists st_t'; split; [ exact MUTT | ].
    cbn [smatch]; exists st_s0, st_t0.
    split; [ exact SM0 | ].
    split; [ exact (layered_mutate LAYS NTH MUTATE) | ].
    split; [ exact LAYT' | ].
    exists d; exact SUMD'.
  Qed.

  Lemma smatch_pop_lockstep:
    forall nms F (st_s st_t: @m_st Sm) st_s0
           (SM: smatch (sb_live nms :: F) st_s st_t)
           (POP: NExt.iter_opt (fun st => pop st) (N.of_nat (List.length nms)) st_s
                 = Some st_s0),
    exists st_t0,
      NExt.iter_opt (fun st => pop st) (N.of_nat (List.length nms)) st_t = Some st_t0
      /\ smatch F st_s0 st_t0.
  Proof using Type.
    intros nms F st_s st_t st_s0 SM POP.
    cbn [smatch] in SM.
    destruct SM as ( st_s1 & st_t1 & SM1 & LAYS & LAYT & _ ).
    rewrite (layered_pop_all LAYS) in POP; injection POP as <-.
    exists st_t1; split; [ exact (layered_pop_all LAYT) | exact SM1 ].
  Qed.

  Lemma smatch_kill_block:
    forall nms F (st_s st_t: @m_st Sm)
           (SM: smatch (sb_live nms :: F) st_s st_t),
    exists st_t0,
      NExt.iter_opt (fun st => pop st) (N.of_nat (List.length nms)) st_t = Some st_t0
      /\ smatch (sb_dead nms :: F) st_s st_t0.
  Proof using Type.
    intros nms F st_s st_t SM.
    cbn [smatch] in SM.
    destruct SM as ( st_s1 & st_t1 & SM1 & LAYS & LAYT & _ ).
    exists st_t1; split; [ exact (layered_pop_all LAYT) | ].
    cbn [smatch]; exists st_s1; split; [ exact SM1 | exact LAYS ].
  Qed.

  Lemma smatch_pop_dead:
    forall nms F (st_s st_t: @m_st Sm) st_s0
           (SM: smatch (sb_dead nms :: F) st_s st_t)
           (POP: NExt.iter_opt (fun st => pop st) (N.of_nat (List.length nms)) st_s
                 = Some st_s0),
      smatch F st_s0 st_t.
  Proof using Type.
    intros nms F st_s st_t st_s0 SM POP.
    cbn [smatch] in SM.
    destruct SM as ( st_s1 & SM1 & LAYS ).
    rewrite (layered_pop_all LAYS) in POP; injection POP as <-.
    exact SM1.
  Qed.

  Lemma state_match_init: forall s: Sm, state_match [] s s.
  Proof using Type.
    intros s.
    constructor; [ exact (smatch_init (store s)) | reflexivity | reflexivity | reflexivity ].
  Qed.

  Lemma state_match_stack_block_alloc:
    forall F (s ts: Sm) (v: value (@ptr_t Sm)) (n: N) st sg nms (s': Sm)
           (SM: state_match F s ts)
           (ALLOC: stack_block_alloc v n (store s) (scnt s) = Some (st, sg, nms))
           (MK: mk_state_opt st sg (heap s) (alc s) = Some s'),
    exists st_t (ts': Sm),
      stack_block_alloc v n (store ts) (scnt ts) = Some (st_t, sg, nms)
      /\ mk_state_opt st_t sg (heap ts) (alc ts) = Some ts'
      /\ state_match (sb_live nms :: F) s' ts'.
  Proof using Type.
    intros F s ts v n st sg nms s' SM ALLOC MK.
    destruct SM as [ SMST ESCNT EHEAP EALC ].
    destruct (smatch_stack_block_alloc F (store s) (store ts) (scnt s) v n st sg nms
                SMST (state_store_dominates s) ALLOC)
      as ( st_t & ALLOCT & SMST' ).
    rewrite <- ESCNT in ALLOCT.
    destruct (stack_block_alloc_inv (state_store_dominates ts) v n st_t sg nms ALLOCT)
      as ( _ & DOMT & _ ).
    exists st_t, (mk_state st_t sg (heap ts) (alc ts) DOMT (state_heap_dominates ts)).
    split; [ exact ALLOCT | ].
    split; [ exact (mk_state_opt_of_dominates _ _ _ _ DOMT (state_heap_dominates ts)) | ].
    destruct (proj1 (mk_state_opt_some st sg (heap s) (alc s) s') MK)
      as ( ESTS & ESGS & EHPS & EALCS ).
    constructor.
    - rewrite ESTS, store_mk_state; exact SMST'.
    - rewrite ESGS, scnt_mk_state; reflexivity.
    - rewrite EHPS, heap_mk_state; exact EHEAP.
    - rewrite EALCS, alc_mk_state; exact EALC.
  Qed.

  Lemma state_match_pop_lockstep:
    forall nms F (s ts s0: Sm)
           (SM: state_match (sb_live nms :: F) s ts)
           (POP: state_pop_n (N.of_nat (List.length nms)) s = Some s0),
    exists ts0: Sm,
      state_pop_n (N.of_nat (List.length nms)) ts = Some ts0
      /\ state_match F s0 ts0.
  Proof using Type.
    intros nms F s ts s0 SM POP.
    destruct SM as [ SMST ESCNT EHEAP EALC ].
    destruct (proj1 state_pop_n_some POP) as ( ITER & ESCNT0 & EHEAP0 & EALC0 ).
    destruct (smatch_pop_lockstep nms F (store s) (store ts) (store s0) SMST ITER)
      as ( st_t0 & ITERT & SMST0 ).
    pose proof (dominates_iter_opt_pop _ _ _ _ ITERT (state_store_dominates ts)) as DOMT.
    exists (mk_state st_t0 (scnt ts) (heap ts) (alc ts) DOMT (state_heap_dominates ts)).
    split; [ exact (state_pop_n_of_dominates DOMT ITERT) | ].
    constructor.
    - rewrite store_mk_state; exact SMST0.
    - rewrite scnt_mk_state, ESCNT0; exact ESCNT.
    - rewrite heap_mk_state, EHEAP0; exact EHEAP.
    - rewrite alc_mk_state, EALC0; exact EALC.
  Qed.

  Lemma state_match_kill_block:
    forall nms F (s ts: Sm)
           (SM: state_match (sb_live nms :: F) s ts),
    exists ts0: Sm,
      state_pop_n (N.of_nat (List.length nms)) ts = Some ts0
      /\ state_match (sb_dead nms :: F) s ts0.
  Proof using Type.
    intros nms F s ts SM.
    destruct SM as [ SMST ESCNT EHEAP EALC ].
    destruct (smatch_kill_block nms F (store s) (store ts) SMST)
      as ( st_t0 & ITERT & SMST0 ).
    pose proof (dominates_iter_opt_pop _ _ _ _ ITERT (state_store_dominates ts)) as DOMT.
    exists (mk_state st_t0 (scnt ts) (heap ts) (alc ts) DOMT (state_heap_dominates ts)).
    split; [ exact (state_pop_n_of_dominates DOMT ITERT) | ].
    constructor.
    - rewrite store_mk_state; exact SMST0.
    - rewrite scnt_mk_state; exact ESCNT.
    - rewrite heap_mk_state; exact EHEAP.
    - rewrite alc_mk_state; exact EALC.
  Qed.

  Lemma state_match_pop_dead:
    forall nms F (s ts s0: Sm)
           (SM: state_match (sb_dead nms :: F) s ts)
           (POP: state_pop_n (N.of_nat (List.length nms)) s = Some s0),
      state_match F s0 ts.
  Proof using Type.
    intros nms F s ts s0 SM POP.
    destruct SM as [ SMST ESCNT EHEAP EALC ].
    destruct (proj1 state_pop_n_some POP) as ( ITER & ESCNT0 & EHEAP0 & EALC0 ).
    constructor.
    - exact (smatch_pop_dead nms F (store s) (store ts) (store s0) SMST ITER).
    - rewrite ESCNT0; exact ESCNT.
    - rewrite EHEAP0; exact EHEAP.
    - rewrite EALC0; exact EALC.
  Qed.

  Lemma state_match_lookup:
    forall nms F (s ts: Sm) n nm
           (SM: state_match (sb_live nms :: F) s ts)
           (NTH: List.nth_error nms n = Some nm),
      lookup (store ts) nm = lookup (store s) nm.
  Proof using Type.
    intros nms F s ts n nm SM NTH.
    destruct SM as [ SMST _ _ _ ].
    exact (smatch_lookup nms F (store s) (store ts) n nm SMST NTH).
  Qed.

  Lemma state_match_mutate:
    forall nms F (s ts: Sm) n nm (v: value (@ptr_t Sm)) (st': @m_st Sm)
           (SM: state_match (sb_live nms :: F) s ts)
           (NTH: List.nth_error nms n = Some nm)
           (MUTATE: mutate (store s) nm v = Some st'),
    exists (st_t': @m_st Sm) (MUTATE_T: mutate (store ts) nm v = Some st_t'),
      state_match (sb_live nms :: F)
        (state_mutate_store s MUTATE) (state_mutate_store ts MUTATE_T).
  Proof using Type.
    intros nms F s ts n nm v st' SM NTH MUTATE.
    destruct SM as [ SMST ESCNT EHEAP EALC ].
    destruct (smatch_mutate nms F (store s) (store ts) n nm v st' SMST NTH MUTATE)
      as ( st_t' & MUTATET & SMST' ).
    exists st_t', MUTATET.
    constructor.
    - rewrite !store_state_mutate_store; exact SMST'.
    - rewrite !scnt_state_mutate_store; exact ESCNT.
    - rewrite !heap_state_mutate_store; exact EHEAP.
    - rewrite !alc_state_mutate_store; exact EALC.
  Qed.

End STORE_MATCH.

Section SIMULATION.

  Context {Sm: State.type}.
  Variable prog: program.

  Inductive chain_cont (v: value (@ptr_t Sm)) (e: @IR.Semantics.env Sm)
            (k0: @IR.Semantics.cont Sm): @IR.Semantics.cont Sm -> Prop :=
  | cc_base: chain_cont v e k0 k0
  | cc_bind: forall aliases y c K
                    (CHAIN: is_chain (y :: aliases) c)
                    (ALIASES: forall z, In z aliases -> PTree.get z e = Some v)
                    (REST: chain_cont v e k0 K),
      chain_cont v e k0 (IR.Semantics.Kbind y c K).

  Definition chain_state (v: value (@ptr_t Sm)) (e: @IR.Semantics.env Sm) (c: cmd)
             (K k0: @IR.Semantics.cont Sm): Prop :=
    exists aliases,
      is_chain aliases c
      /\ (forall z, In z aliases -> PTree.get z e = Some v)
      /\ chain_cont v e k0 K.

  Inductive match_cont: list (@stack_block Sm) -> @IR.Semantics.cont Sm -> @IR.Semantics.cont Sm -> Prop :=
  | mk_stop:
      match_cont [] IR.Semantics.Kstop IR.Semantics.Kstop
  | mk_bind: forall F id c k tk b
                    (TAILB: b = true -> IR.Semantics.is_call_cont k)
                    (MK: match_cont F k tk),
      match_cont F (IR.Semantics.Kbind id c k) (IR.Semantics.Kbind id (transf_cmd b c) tk)
  | mk_loop1: forall F c_cond id_cond c_body id_body k tk
                     (MK: match_cont F k tk),
      match_cont F (IR.Semantics.Kloop1 c_cond id_cond c_body id_body k)
                   (IR.Semantics.Kloop1 c_cond id_cond c_body id_body tk)
  | mk_loop2: forall F c_cond id_cond c_body id_body k tk
                     (MK: match_cont F k tk),
      match_cont F (IR.Semantics.Kloop2 c_cond id_cond c_body id_body k)
                   (IR.Semantics.Kloop2 c_cond id_cond c_body id_body tk)
  | mk_call: forall F fn e locals k tk
                    (LEN: List.length locals = Z.to_nat fn.(fn_extra).(fn_stackspace))
                    (MK: match_cont F k tk),
      match_cont (sb_live locals :: F)
                 (IR.Semantics.Kcall fn e locals k)
                 (IR.Semantics.Kcall (transf_function fn) e locals tk)
  | mk_tail: forall F fn e locals x chain k tk
                    (CHAIN: is_chain [x] chain)
                    (LEN: List.length locals = Z.to_nat fn.(fn_extra).(fn_stackspace))
                    (CALLCONT: IR.Semantics.is_call_cont k)
                    (MK: match_cont F k tk),
      match_cont (sb_dead locals :: F)
                 (IR.Semantics.Kcall fn e locals (IR.Semantics.Kbind x chain k))
                 tk.

  Inductive match_states: @IR.Semantics.state Sm -> @IR.Semantics.state Sm -> Prop :=
  | match_state_normal:
      forall fn c k e locals s b tk ts F
             (WT: IR.Semantics.wt_state prog (IR.Semantics.State fn c k e locals s))
             (TAILB: b = true -> IR.Semantics.is_call_cont k)
             (MK: match_cont F k tk)
             (LEN: List.length locals = Z.to_nat fn.(fn_extra).(fn_stackspace))
             (SM: state_match (sb_live locals :: F) s ts),
      match_states (IR.Semantics.State fn c k e locals s)
                   (IR.Semantics.State (transf_function fn) (transf_cmd b c) tk e locals ts)
  | match_state_precall:
      forall fn f t_out args x chain k e locals s tk ts F
             (WT: IR.Semantics.wt_state prog
                    (IR.Semantics.State fn (c_app f t_out args) (IR.Semantics.Kbind x chain k)
                       e locals s))
             (CHAIN: is_chain [x] chain)
             (CALLCONT: IR.Semantics.is_call_cont k)
             (MK: match_cont F k tk)
             (LEN: List.length locals = Z.to_nat fn.(fn_extra).(fn_stackspace))
             (SM: state_match (sb_live locals :: F) s ts),
      match_states (IR.Semantics.State fn (c_app f t_out args) (IR.Semantics.Kbind x chain k)
                      e locals s)
                   (IR.Semantics.State (transf_function fn) (c_app f t_out args) tk e locals ts)
  | match_state_call:
      forall fd args k s tk ts F
             (WT: IR.Semantics.wt_state prog (IR.Semantics.Callstate fd args k s))
             (MK: match_cont F k tk)
             (SM: state_match F s ts),
      match_states (IR.Semantics.Callstate fd args k s)
                   (IR.Semantics.Callstate (transf_fundef fd) args tk ts)
  | match_state_return:
      forall v k s tk ts F
             (WT: IR.Semantics.wt_state prog (IR.Semantics.Returnstate v k s))
             (MK: match_cont F k tk)
             (SM: state_match F s ts),
      match_states (IR.Semantics.Returnstate v k s) (IR.Semantics.Returnstate v tk ts)
  | match_state_interm:
      forall fn c K e locals s v k tk ts F
             (WT: IR.Semantics.wt_state prog (IR.Semantics.State fn c K e locals s))
             (CHST: chain_state v e c K k)
             (CALLCONT: IR.Semantics.is_call_cont k)
             (MK: match_cont F k tk)
             (LEN: List.length locals = Z.to_nat fn.(fn_extra).(fn_stackspace))
             (SM: state_match (sb_dead locals :: F) s ts),
      match_states (IR.Semantics.State fn c K e locals s) (IR.Semantics.Returnstate v tk ts).

  Lemma match_cont_call_cont:
    forall F k tk
           (MK: match_cont F k tk)
           (CALLK: IR.Semantics.is_call_cont k),
      IR.Semantics.is_call_cont tk.
  Proof using Type.
    intros F k tk MK.
    induction MK as [ | | | | F fn e locals k tk LEN MK IH
                    | F fn e locals x chain k tk CHAIN LEN CALLCONT MK IH ];
      intros CALLK; inversion CALLK; subst.
    - apply IR.Semantics.call_cont_Kstop.
    - apply IR.Semantics.call_cont_Kcall.
    - exact (IH CALLCONT).
  Qed.

  Lemma match_cont_seq_cont:
    forall F k tk
           (MK: match_cont F k tk)
           (SEQ: IR.Semantics.is_seq_cont k),
      IR.Semantics.is_seq_cont tk.
  Proof using Type.
    intros F k tk MK SEQ.
    destruct MK; inversion SEQ; constructor.
  Qed.

  Lemma match_cont_seq_target:
    forall F k tk id
           (MK: match_cont F k tk)
           (TARGET: IR.Semantics.seq_cont_target k id),
      IR.Semantics.seq_cont_target tk id.
  Proof using Type.
    intros F k tk id MK TARGET.
    destruct MK; inversion TARGET; subst; constructor.
  Qed.

  Lemma match_cont_resolve:
    forall F k tk v c' k'
           (MK: match_cont F k tk)
           (RESOLVE: IR.Semantics.resolve_seq_cont k v c' k'),
    exists b tk',
      IR.Semantics.resolve_seq_cont tk v (transf_cmd b c') tk'
      /\ match_cont F k' tk'
      /\ (b = true -> IR.Semantics.is_call_cont k').
  Proof using Type.
    intros F k tk v c' k' MK RESOLVE.
    destruct RESOLVE as [ id c k v | c_cond id_cond c_body id_body k [ | ]
                        | c_cond id_cond c_body id_body k ];
      inversion MK; subst.
    - eexists _, _.
      split; [ apply IR.Semantics.resolve_seq_Kbind | ].
      split; eassumption.
    - exists false; rewrite transf_cmd_false; eexists.
      split; [ apply IR.Semantics.resolve_seq_Kloop1 | ].
      split; [ apply mk_loop2; assumption | discriminate ].
    - exists false; rewrite transf_cmd_false; eexists.
      split; [ apply IR.Semantics.resolve_seq_Kloop1 | ].
      split; [ assumption | discriminate ].
    - exists false; rewrite transf_cmd_false; eexists.
      split; [ apply IR.Semantics.resolve_seq_Kloop2 | ].
      split; [ apply mk_loop1; assumption | discriminate ].
  Qed.

  Lemma match_cont_call_cont_shape:
    forall F k tk
           (MK: match_cont F k tk)
           (CALLK: IR.Semantics.is_call_cont k),
      (k = IR.Semantics.Kstop /\ F = [] /\ tk = IR.Semantics.Kstop)
      \/ (exists fn e locals k1 tk1 F1,
             k = IR.Semantics.Kcall fn e locals k1
             /\ tk = IR.Semantics.Kcall (transf_function fn) e locals tk1
             /\ F = sb_live locals :: F1
             /\ List.length locals = Z.to_nat fn.(fn_extra).(fn_stackspace)
             /\ match_cont F1 k1 tk1)
      \/ (exists fn e locals x chain k1 F1,
             k = IR.Semantics.Kcall fn e locals (IR.Semantics.Kbind x chain k1)
             /\ F = sb_dead locals :: F1
             /\ is_chain [x] chain
             /\ List.length locals = Z.to_nat fn.(fn_extra).(fn_stackspace)
             /\ IR.Semantics.is_call_cont k1
             /\ match_cont F1 k1 tk).
  Proof using Type.
    intros F k tk MK CALLK.
    destruct MK as [ | | | | F fn e locals k tk LEN MK
                   | F fn e locals x chain k tk CHAIN LEN CALLCONT MK ];
      inversion CALLK; subst.
    - left; split; [ reflexivity | split; reflexivity ].
    - right; left.
      exists fn, e, locals, k, tk, F.
      split; [ reflexivity | split; [ reflexivity | split; [ reflexivity | ] ] ].
      split; [ exact LEN | exact MK ].
    - right; right.
      exists fn, e, locals, x, chain, k, F.
      split; [ reflexivity | split; [ reflexivity | ] ].
      split; [ exact CHAIN | split; [ exact LEN | split; [ exact CALLCONT | exact MK ] ] ].
  Qed.

  Lemma chain_cont_set:
    forall v e k0 K y
           (CC: chain_cont v e k0 K),
      chain_cont v (PTree.set y v e) k0 K.
  Proof using Type.
    intros v e k0 K y CC.
    induction CC as [ | aliases z c K CHAIN ALIASES REST IH ].
    - apply cc_base.
    - apply (cc_bind _ _ _ aliases z c K CHAIN); [ | exact IH ].
      intros w IN.
      destruct (peq w y) as [ -> | NE ].
      + apply PTree.gss.
      + rewrite PTree.gso by exact NE.
        exact (ALIASES w IN).
  Qed.

  Lemma chain_state_start:
    forall v e x chain k
           (CHAIN: is_chain [x] chain),
      chain_state v (PTree.set x v e) chain k k.
  Proof using Type.
    intros v e x chain k CHAIN.
    exists [x].
    split; [ exact CHAIN | split; [ | apply cc_base ] ].
    intros z [ <- | [] ].
    apply PTree.gss.
  Qed.

  Lemma chain_state_bind:
    forall v e y t_b c1 c2 t_c K k0
           (CHST: chain_state v e (c_bind y t_b c1 c2 t_c) K k0),
      chain_state v e c1 (IR.Semantics.Kbind y c2 K) k0.
  Proof using Type.
    intros v e y t_b c1 c2 t_c K k0 CHST.
    destruct CHST as ( aliases & CHAIN & ALIASES & CC ).
    inversion CHAIN as [ | aliases' y' t_b' c1' c2' t_c' CHAIN1 CHAIN2 ]; subst.
    exists aliases.
    split; [ exact CHAIN1 | split; [ exact ALIASES | ] ].
    exact (cc_bind _ _ _ aliases y c2 K CHAIN2 ALIASES CC).
  Qed.

  Lemma chain_state_ret_final:
    forall v e z t K k0
           (CHST: chain_state v e (c_ret (e_var z) t) K k0),
      PTree.get z e = Some v.
  Proof using Type.
    intros v e z t K k0 CHST.
    destruct CHST as ( aliases & CHAIN & ALIASES & _ ).
    inversion CHAIN as [ aliases' z' t' IN | ]; subst.
    exact (ALIASES z IN).
  Qed.

  Lemma chain_state_ret_seq:
    forall v e z t y c K k0
           (CHST: chain_state v e (c_ret (e_var z) t) (IR.Semantics.Kbind y c K) k0)
           (CALLK0: IR.Semantics.is_call_cont k0),
      PTree.get z e = Some v /\ chain_state v (PTree.set y v e) c K k0.
  Proof using Type.
    intros v e z t y c K k0 CHST CALLK0.
    split; [ exact (chain_state_ret_final v e z t _ k0 CHST) | ].
    destruct CHST as ( _ & _ & _ & CC ).
    inversion CC as [ EQ | aliases y' c' K' CHAIN ALIASES REST ]; subst.
    - inversion CALLK0.
    - exists (y :: aliases).
      split; [ exact CHAIN | split ].
      + intros w [ <- | IN ]; [ apply PTree.gss | ].
        destruct (peq w y) as [ -> | NE ]; [ apply PTree.gss | ].
        rewrite PTree.gso by exact NE.
        exact (ALIASES w IN).
      + exact (chain_cont_set v e k0 K y REST).
  Qed.

  Lemma chain_state_shape:
    forall v e c K k0
           (CHST: chain_state v e c K k0),
      (exists z t, c = c_ret (e_var z) t)
      \/ (exists y t_b c1 c2 t_c, c = c_bind y t_b c1 c2 t_c).
  Proof using Type.
    intros v e c K k0 CHST.
    destruct CHST as ( aliases & CHAIN & _ & _ ).
    destruct CHAIN as [ aliases z t _ | aliases y t_b c1 c2 t_c _ _ ].
    - left; exists z, t; reflexivity.
    - right; exists y, t_b, c1, c2, t_c; reflexivity.
  Qed.

  Lemma chain_state_call_cont:
    forall v e c K k0
           (CHST: chain_state v e c K k0)
           (CALLK: IR.Semantics.is_call_cont K),
      K = k0.
  Proof using Type.
    intros v e c K k0 CHST CALLK.
    destruct CHST as ( _ & _ & _ & CC ).
    destruct CC as [ | aliases y c' K' _ _ _ ]; [ reflexivity | inversion CALLK ].
  Qed.

  Lemma chain_state_seq_target:
    forall v e c K k0 id
           (CHST: chain_state v e c K k0)
           (CALLK0: IR.Semantics.is_call_cont k0)
           (TARGET: IR.Semantics.seq_cont_target K id),
    exists c' K', K = IR.Semantics.Kbind id c' K'.
  Proof using Type.
    intros v e c K k0 id CHST CALLK0 TARGET.
    destruct CHST as ( _ & _ & _ & CC ).
    destruct CC as [ | aliases y c' K' _ _ _ ].
    - destruct CALLK0; inversion TARGET.
    - inversion TARGET; subst.
      exists c', K'; reflexivity.
  Qed.

  Fixpoint chain_measure (c: cmd): nat :=
    match c with
    | c_ret _ _ => 1
    | c_bind _ _ c1 c2 _ => 1 + chain_measure c1 + chain_measure c2
    | _ => 0
    end.

  Fixpoint cont_measure (k: @IR.Semantics.cont Sm): nat :=
    match k with
    | IR.Semantics.Kstop => 0
    | IR.Semantics.Kbind _ c k => chain_measure c + cont_measure k
    | IR.Semantics.Kloop1 _ _ _ _ k => cont_measure k
    | IR.Semantics.Kloop2 _ _ _ _ k => cont_measure k
    | IR.Semantics.Kcall _ _ _ k => 2 + cont_measure k
    end.

  Definition measure (st: @IR.Semantics.state Sm): nat :=
    match st with
    | IR.Semantics.State _ c k _ _ _ => cont_measure k + chain_measure c + 1
    | IR.Semantics.Callstate _ _ k _ => cont_measure k
    | IR.Semantics.Returnstate _ k _ => cont_measure k
    end.

  Lemma measure_redex_bind:
    forall fn fn' x t_b f t_out args chain t_c k e e' locals locals' s s',
      (measure (IR.Semantics.State fn' (c_app f t_out args) (IR.Semantics.Kbind x chain k)
                  e' locals' s')
       < measure (IR.Semantics.State fn (c_bind x t_b (c_app f t_out args) chain t_c) k
                    e locals s))%nat.
  Proof using Type.
    intros; cbn; lia.
  Qed.

  Lemma measure_return_dead:
    forall fn fn' e e' locals locals' s s' v x chain k,
      (measure (IR.Semantics.State fn' chain k e' locals' s')
       < measure (IR.Semantics.Returnstate v
                    (IR.Semantics.Kcall fn e locals (IR.Semantics.Kbind x chain k)) s))%nat.
  Proof using Type.
    intros; cbn; lia.
  Qed.

  Lemma measure_chain_bind:
    forall fn fn' y t_b c1 c2 t_c K e e' locals locals' s s',
      (measure (IR.Semantics.State fn' c1 (IR.Semantics.Kbind y c2 K) e' locals' s')
       < measure (IR.Semantics.State fn (c_bind y t_b c1 c2 t_c) K e locals s))%nat.
  Proof using Type.
    intros; cbn; lia.
  Qed.

  Lemma measure_chain_ret_seq:
    forall fn fn' r t y c K e e' locals locals' s s',
      (measure (IR.Semantics.State fn' c K e' locals' s')
       < measure (IR.Semantics.State fn (c_ret r t) (IR.Semantics.Kbind y c K) e locals s))%nat.
  Proof using Type.
    intros; cbn; lia.
  Qed.

  Lemma measure_chain_final:
    forall fn r t k e locals s v s',
      (measure (IR.Semantics.Returnstate v k s')
       < measure (IR.Semantics.State fn (c_ret r t) k e locals s))%nat.
  Proof using Type.
    intros; cbn; lia.
  Qed.

  Lemma builtin_sim:
    forall c (ge tge: genv) e locals F (s ts: Sm) v s'
           (BUILTIN: IR.Semantics.builtin c ge e locals s v s')
           (SM: state_match (sb_live locals :: F) s ts),
    exists ts': Sm,
      IR.Semantics.builtin c tge e locals ts v ts'
      /\ state_match (sb_live locals :: F) s' ts'.
  Proof using Type.
    intros c ge tge e locals F s ts v s' BUILTIN SM.
    revert SM.
    destruct BUILTIN as
      [ e0 t ge0 env locals0 s0 v0 EVAL WT
      | n t ge0 env locals0 s0 v0 nm DEREF LOOKUP WT
      | n t e0 ge0 env locals0 s0 st' v0 nm EVAL DEREF MUTATE WT
      | e_size t e_init id_ptr id_count id_init ge0 env locals0 s0 ptr hp' alc' v_size v_init
          EVAL_SIZE EVAL_INIT WT BND ALLOC_GC
      | e_ptr t ge0 env locals0 s0 v_read v_ptr EVAL LOOKUP WT
      | e_ptr t e_data ge0 env locals0 s0 hp' v_ptr v_data EVAL_ptr EVAL_data MUTATE WT
      | e_ptr ge0 env locals0 s0 hp' ptr EVAL FREE_GC
      | e_ptr e_shift ge0 env locals0 s0 v_ptr' v_ptr v_shift EVAL_ptr EVAL_shift SHIFT
          WVALID_pre WVALID_post
      | e_ptr e_shift ge0 env locals0 s0 v_ptr' v_ptr v_shift EVAL_ptr EVAL_shift SHIFT
          WVALID_pre WVALID_post
      | e_ptr_l e_ptr_r ge0 env locals0 s0 b v_ptr_l v_ptr_r EVAL_l EVAL_r CMPVALID CMP
      | e_l e_r ge0 env locals0 s0 l r q EVAL_l EVAL_r DIV
      | e_l e_r ge0 env locals0 s0 l r q EVAL_l EVAL_r MDL ];
      intros SM; pose proof SM as SM0; destruct SM0 as [ SMST ESCNT EHEAP EALC ].
    - exists ts; split; [ exact (IR.Semantics.builtin_ret e0 t tge env locals0 ts v0 EVAL WT) | exact SM ].
    - exists ts; split; [ | exact SM ].
      apply (IR.Semantics.builtin_read_var n t tge env locals0 ts v0 nm DEREF); [ | exact WT ].
      rewrite (state_match_lookup locals0 F s0 ts n nm SM DEREF); exact LOOKUP.
    - destruct (state_match_mutate locals0 F s0 ts n nm _ st' SM DEREF MUTATE)
        as ( st_t' & MUTATE_T & SM' ).
      exists (state_mutate_store ts MUTATE_T); split; [ | exact SM' ].
      exact (IR.Semantics.builtin_write_var n t e0 tge env locals0 ts st_t' v0 nm
               EVAL DEREF MUTATE_T WT).
    - pose proof ALLOC_GC as ALLOC_T; rewrite <- EHEAP, <- EALC in ALLOC_T.
      exists (state_alloc ts ALLOC_T); split.
      + exact (IR.Semantics.builtin_alloc_ptr e_size t e_init id_ptr id_count id_init tge env
                 locals0 ts ptr hp' alc' v_size v_init EVAL_SIZE EVAL_INIT WT BND ALLOC_T).
      + constructor.
        * rewrite !store_state_alloc; exact SMST.
        * rewrite !scnt_state_alloc; exact ESCNT.
        * rewrite !heap_state_alloc; reflexivity.
        * rewrite !alc_state_alloc; reflexivity.
    - exists ts; split; [ | exact SM ].
      apply (IR.Semantics.builtin_read_ptr e_ptr t tge env locals0 ts v_read v_ptr EVAL);
        [ rewrite EHEAP; exact LOOKUP | exact WT ].
    - pose proof MUTATE as MUTATE_T; rewrite <- EHEAP in MUTATE_T.
      exists (state_mutate_heap ts MUTATE_T); split.
      + exact (IR.Semantics.builtin_write_ptr e_ptr t e_data tge env locals0 ts hp' v_ptr v_data
                 EVAL_ptr EVAL_data MUTATE_T WT).
      + constructor.
        * rewrite !store_state_mutate_heap; exact SMST.
        * rewrite !scnt_state_mutate_heap; exact ESCNT.
        * rewrite !heap_state_mutate_heap; reflexivity.
        * rewrite !alc_state_mutate_heap; exact EALC.
    - pose proof FREE_GC as FREE_T; rewrite <- EHEAP in FREE_T.
      exists (state_free ts FREE_T); split.
      + exact (IR.Semantics.builtin_free_ptr e_ptr tge env locals0 ts hp' ptr EVAL FREE_T).
      + constructor.
        * rewrite !store_state_free; exact SMST.
        * rewrite !scnt_state_free; exact ESCNT.
        * rewrite !heap_state_free; reflexivity.
        * rewrite !alc_state_free; exact EALC.
    - exists ts; split; [ | exact SM ].
      apply (IR.Semantics.builtin_shift_fw_ptr e_ptr e_shift tge env locals0 ts v_ptr' v_ptr v_shift
               EVAL_ptr EVAL_shift SHIFT); rewrite EHEAP; assumption.
    - exists ts; split; [ | exact SM ].
      apply (IR.Semantics.builtin_shift_bw_ptr e_ptr e_shift tge env locals0 ts v_ptr' v_ptr v_shift
               EVAL_ptr EVAL_shift SHIFT); rewrite EHEAP; assumption.
    - exists ts; split; [ | exact SM ].
      apply (IR.Semantics.builtin_eq_ptr e_ptr_l e_ptr_r tge env locals0 ts b v_ptr_l v_ptr_r
               EVAL_l EVAL_r); [ rewrite EHEAP; exact CMPVALID | exact CMP ].
    - exists ts; split; [ | exact SM ].
      exact (IR.Semantics.builtin_div e_l e_r tge env locals0 ts l r q EVAL_l EVAL_r
               (Intops.Unsigned.Facts.div_state_indep DIV)).
    - exists ts; split; [ | exact SM ].
      exact (IR.Semantics.builtin_mod e_l e_r tge env locals0 ts l r q EVAL_l EVAL_r
               (Intops.Unsigned.Facts.mdl_state_indep MDL)).
  Qed.

  Lemma transf_initial_states:
    forall S (INIT: IR.Semantics.initial_state prog S),
    exists T, IR.Semantics.initial_state (transf_program prog) T /\ match_states S T.
  Proof using Type.
    intros S INIT.
    pose proof (IR.Lemmas.wt_initial_state INIT) as WT.
    destruct INIT as [ ge b f s0 WTp INITGENV INITSTATE FINDMAINB FINDMAINF MAINSIG ].
    subst ge.
    exists (IR.Semantics.Callstate (transf_fundef f) [] IR.Semantics.Kstop s0).
    split.
    - apply (IR.Semantics.initial_state_intro _ (Genv.globalenv (transf_program prog)) b).
      + exact (transf_program_wt prog WTp).
      + reflexivity.
      + rewrite transf_init_state; exact INITSTATE.
      + rewrite (symbols_preserved _ _ (transf_program_match prog)).
        cbn [program_of_program AST.prog_main].
        rewrite (match_program_main _ _ (transf_program_match prog)).
        exact FINDMAINB.
      + exact (function_ptr_translated _ _ (transf_program_match prog) b f FINDMAINF).
      + exact (sig_preserved f _ MAINSIG).
    - apply (match_state_call f [] IR.Semantics.Kstop s0 IR.Semantics.Kstop s0 []).
      + exact WT.
      + exact mk_stop.
      + exact (state_match_init s0).
  Qed.

  Lemma transf_final_states:
    forall S T r
           (MS: match_states S T)
           (FINAL: IR.Semantics.final_state S r),
      IR.Semantics.final_state T r.
  Proof using Type.
    intros S T r MS FINAL.
    destruct FINAL as [ r s ].
    inversion MS as [ | | | v k s1 tk ts F WT MK SM | ]; subst.
    inversion MK; subst.
    apply IR.Semantics.final_state_intro.
  Qed.

  Lemma step_call_sim:
    forall fd args k s tk ts F t S1'
           (WT: IR.Semantics.wt_state prog (IR.Semantics.Callstate fd args k s))
           (MK: match_cont F k tk)
           (SM: state_match F s ts)
           (STEP: IR.Semantics.step (Genv.globalenv prog) (IR.Semantics.Callstate fd args k s) t S1'),
      (exists S2',
          IR.Semantics.step (Genv.globalenv (transf_program prog))
            (IR.Semantics.Callstate (transf_fundef fd) args tk ts) t S2'
          /\ match_states S1' S2')
      \/ (measure S1' < measure (IR.Semantics.Callstate fd args k s)
          /\ t = Events.E0
          /\ match_states S1' (IR.Semantics.Callstate (transf_fundef fd) args tk ts))%nat.
  Proof using Type.
    intros fd args k s tk ts F t S1' WT MK SM STEP.
    pose proof (IR.Lemmas.preservation WT STEP) as WT'.
    left.
    remember (IR.Semantics.Callstate fd args k s) as S1 eqn:ES1.
    revert ES1.
    destruct STEP as [ | | | | | |
                     | ge0 fn args0 k0 locals s0 s' env st sg WTargs PARAMS LOCALS STACKBL CONTcall
                     | ];
      intros ES1; try discriminate ES1.
    injection ES1 as <- -> -> ->.
    destruct (state_match_stack_block_alloc F s ts _ _ st sg locals s' SM LOCALS STACKBL)
      as ( st_t & ts' & ALLOCT & MKT & SM' ).
    destruct (stack_block_alloc_inv (state_store_dominates s) _ _ st sg locals LOCALS)
      as ( LENL & _ ).
    exists (IR.Semantics.State (transf_function fn) (transf_cmd true (fn_body fn)) tk env locals ts').
    split.
    - apply (IR.Semantics.step_internal_function _ (transf_function fn) args tk locals ts ts'
               env st_t sg).
      + exact WTargs.
      + exact PARAMS.
      + exact ALLOCT.
      + exact MKT.
      + exact (match_cont_call_cont F k tk MK CONTcall).
    - apply (match_state_normal fn (fn_body fn) k env locals s' true tk ts' F).
      + exact WT'.
      + intros _; exact CONTcall.
      + exact MK.
      + rewrite LENL; exact (Znat.Z_N_nat _).
      + exact SM'.
  Qed.

  Lemma step_precall_sim:
    forall fn f t_out args x chain k e locals s tk ts F t S1'
           (WT: IR.Semantics.wt_state prog
                  (IR.Semantics.State fn (c_app f t_out args) (IR.Semantics.Kbind x chain k)
                     e locals s))
           (CHAIN: is_chain [x] chain)
           (CALLCONT: IR.Semantics.is_call_cont k)
           (MK: match_cont F k tk)
           (LEN: List.length locals = Z.to_nat fn.(fn_extra).(fn_stackspace))
           (SM: state_match (sb_live locals :: F) s ts)
           (STEP: IR.Semantics.step (Genv.globalenv prog)
                    (IR.Semantics.State fn (c_app f t_out args) (IR.Semantics.Kbind x chain k)
                       e locals s) t S1'),
      (exists S2',
          IR.Semantics.step (Genv.globalenv (transf_program prog))
            (IR.Semantics.State (transf_function fn) (c_app f t_out args) tk e locals ts) t S2'
          /\ match_states S1' S2')
      \/ (measure S1' < measure (IR.Semantics.State fn (c_app f t_out args)
                                   (IR.Semantics.Kbind x chain k) e locals s)
          /\ t = Events.E0
          /\ match_states S1'
               (IR.Semantics.State (transf_function fn) (c_app f t_out args) tk e locals ts))%nat.
  Proof using Type.
    intros fn f t_out args x chain k e locals s tk ts F t S1' WT CHAIN CALLCONT MK LEN SM STEP.
    pose proof (IR.Lemmas.preservation WT STEP) as WT'.
    left.
    remember (Genv.globalenv prog) as ge eqn:EGE.
    remember (IR.Semantics.State fn (c_app f t_out args) (IR.Semantics.Kbind x chain k) e locals s)
      as S1 eqn:ES1.
    revert EGE ES1.
    destruct STEP as [
                     | ge0 f0 c0 k0 env0 locals0 s0 v s' s'' CONTcall BUILTIN POPSTACK
                     | ge0 f0 c0 k0 env0 locals0 s0 c_next k' target_id v s' SEQtarget SEQresolve
                         BUILTIN
                     | ge0 fn0 id t_out0 args0 k0 env0 locals0 s0 v_args b fd EVALargs FINDsymb
                         FINDfunct CONTseq
                     | ge0 fn0 f_id t_out0 args0 k0 env0 locals0 s0 fd v_args s' b EVALargs FINDsymb
                         FINDfunct POPSTACK CONTcall
                     | | | | ];
      intros EGE ES1; try discriminate ES1.
    - injection ES1 as -> -> -> -> -> ->.
      inversion CONTcall.
    - injection ES1 as -> -> -> -> -> ->.
      inversion BUILTIN.
    - injection ES1 as -> -> -> -> -> -> -> ->.
      subst ge0.
      destruct (state_match_kill_block locals F s ts SM) as ( ts0 & POP & SM' ).
      exists (IR.Semantics.Callstate (transf_fundef fd) v_args tk ts0).
      split.
      + apply (IR.Semantics.step_tailapp _ (transf_function fn) f t_out args tk e locals ts
                 (transf_fundef fd) v_args ts0 b).
        * exact EVALargs.
        * rewrite (symbols_preserved _ _ (transf_program_match prog)); exact FINDsymb.
        * exact (function_ptr_translated _ _ (transf_program_match prog) b fd FINDfunct).
        * exact (eq_trans (IR.Lemmas.pop_stack_length _ ts locals LEN) POP).
        * exact (match_cont_call_cont F k tk MK CALLCONT).
      + apply (match_state_call fd v_args _ s tk ts0 (sb_dead locals :: F)).
        * exact WT'.
        * exact (mk_tail F fn e locals x chain k tk CHAIN LEN CALLCONT MK).
        * exact SM'.
    - injection ES1 as -> -> -> -> -> -> -> ->.
      inversion CONTcall.
  Qed.

  Lemma transf_cmd_builtin:
    forall c (ge: genv) e locals (s: Sm) v s'
           (BUILTIN: IR.Semantics.builtin c ge e locals s v s')
           (b: bool),
      transf_cmd b c = c.
  Proof using Type.
    intros c ge e locals s v s' BUILTIN b.
    destruct BUILTIN; reflexivity.
  Qed.

  Lemma step_normal_sim:
    forall fn c k e locals s b tk ts F t S1'
           (WT: IR.Semantics.wt_state prog (IR.Semantics.State fn c k e locals s))
           (TAILB: b = true -> IR.Semantics.is_call_cont k)
           (MK: match_cont F k tk)
           (LEN: List.length locals = Z.to_nat fn.(fn_extra).(fn_stackspace))
           (SM: state_match (sb_live locals :: F) s ts)
           (STEP: IR.Semantics.step (Genv.globalenv prog)
                    (IR.Semantics.State fn c k e locals s) t S1'),
      (exists S2',
          IR.Semantics.step (Genv.globalenv (transf_program prog))
            (IR.Semantics.State (transf_function fn) (transf_cmd b c) tk e locals ts) t S2'
          /\ match_states S1' S2')
      \/ (measure S1' < measure (IR.Semantics.State fn c k e locals s)
          /\ t = Events.E0
          /\ match_states S1'
               (IR.Semantics.State (transf_function fn) (transf_cmd b c) tk e locals ts))%nat.
  Proof using Type.
    intros fn c k e locals s b tk ts F t S1' WT TAILB MK LEN SM STEP.
    pose proof (IR.Lemmas.preservation WT STEP) as WT'.
    remember (Genv.globalenv prog) as ge eqn:EGE.
    remember (IR.Semantics.State fn c k e locals s) as S1 eqn:ES1.
    revert EGE ES1.
    destruct STEP as [ ge0 f0 id_b t_b c_b c_c t_c k0 env0 locals0 s0
                     | ge0 f0 c0 k0 env0 locals0 s0 v s' s'' CONTcall BUILTIN POPSTACK
                     | ge0 f0 c0 k0 env0 locals0 s0 c_next k' target_id v s' SEQtarget SEQresolve
                         BUILTIN
                     | ge0 fn0 id t_out args k0 env0 locals0 s0 v_args b0 fd EVALargs FINDsymb
                         FINDfunct CONTseq
                     | ge0 fn0 f_id t_out args k0 env0 locals0 s0 fd v_args s' b0 EVALargs FINDsymb
                         FINDfunct POPSTACK CONTcall
                     | ge0 fn0 e_i c_t c_e t0 k0 env0 locals0 s0 bb EVALif
                     | ge0 fn0 c_cond id_cond c_body id_body k0 env0 locals0 s0
                     | | ];
      intros EGE ES1; try discriminate ES1; subst ge0.
    - injection ES1 as -> <- -> -> -> ->.
      rewrite transf_cmd_bind_eq.
      destruct (rewrite_guard b id_b c_b c_c t_c) eqn:GUARD.
      + destruct c_b as [ | | | | | | | | | | | | | f t_out args | | ]; try discriminate GUARD.
        cbn [ rewrite_guard ] in GUARD.
        apply andb_prop in GUARD as [ GUARD _ ].
        apply andb_prop in GUARD as [ BTRUE CHK ].
        subst b.
        right.
        split; [ apply measure_redex_bind | split; [ reflexivity | ] ].
        apply (match_state_precall fn f t_out args id_b c_c k e locals s tk ts F).
        * exact WT'.
        * exact (proj2 (Bool.reflect_iff _ _ (chain_check_spec [id_b] c_c)) CHK).
        * exact (TAILB eq_refl).
        * exact MK.
        * exact LEN.
        * exact SM.
      + left.
        exists (IR.Semantics.State (transf_function fn) (transf_cmd false c_b)
                  (IR.Semantics.Kbind id_b (transf_cmd b c_c) tk) e locals ts).
        split; [ apply IR.Semantics.step_bind | ].
        apply (match_state_normal fn c_b (IR.Semantics.Kbind id_b c_c k) e locals s false
                 (IR.Semantics.Kbind id_b (transf_cmd b c_c) tk) ts F).
        * exact WT'.
        * intros EQ; discriminate EQ.
        * exact (mk_bind F id_b c_c k tk b TAILB MK).
        * exact LEN.
        * exact SM.
    - injection ES1 as -> -> -> -> -> ->.
      rewrite (transf_cmd_builtin c _ e locals s v s' BUILTIN b).
      destruct (builtin_sim c _ (Genv.globalenv (transf_program prog)) e locals F s ts v s'
                  BUILTIN SM)
        as ( ts' & BUILTIN_T & SM' ).
      destruct (state_match_pop_lockstep locals F s' ts' s'' SM'
                  (eq_trans (eq_sym (IR.Lemmas.pop_stack_length _ s' locals LEN)) POPSTACK))
        as ( ts'' & POPT & SM'' ).
      left.
      exists (IR.Semantics.Returnstate v tk ts'').
      split.
      + apply (IR.Semantics.step_builtin_call_cont _ (transf_function fn) c tk e locals ts v ts' ts'').
        * exact (match_cont_call_cont F k tk MK CONTcall).
        * exact BUILTIN_T.
        * exact (eq_trans (IR.Lemmas.pop_stack_length _ ts' locals LEN) POPT).
      + exact (match_state_return v k s'' tk ts'' F WT' MK SM'').
    - injection ES1 as -> -> -> -> -> ->.
      rewrite (transf_cmd_builtin c _ e locals s v s' BUILTIN b).
      destruct (builtin_sim c _ (Genv.globalenv (transf_program prog)) e locals F s ts v s'
                  BUILTIN SM)
        as ( ts' & BUILTIN_T & SM' ).
      destruct (match_cont_resolve F k tk v c_next k' MK SEQresolve)
        as ( b' & tk' & RESOLVE_T & MK' & TAILB' ).
      left.
      exists (IR.Semantics.State (transf_function fn) (transf_cmd b' c_next) tk'
                (PTree.set target_id v e) locals ts').
      split.
      + apply (IR.Semantics.step_builtin_seq_cont _ (transf_function fn) c tk e locals ts
                 (transf_cmd b' c_next) tk' target_id v ts').
        * exact (match_cont_seq_target F k tk target_id MK SEQtarget).
        * exact RESOLVE_T.
        * exact BUILTIN_T.
      + exact (match_state_normal fn c_next k' (PTree.set target_id v e) locals s' b' tk' ts' F
                 WT' TAILB' MK' LEN SM').
    - injection ES1 as -> <- -> -> -> ->.
      left.
      exists (IR.Semantics.Callstate (transf_fundef fd) v_args
                (IR.Semantics.Kcall (transf_function fn) e locals tk) ts).
      split.
      + change (transf_cmd b (c_app id t_out args)) with (c_app id t_out args).
        apply (IR.Semantics.step_app _ (transf_function fn) id t_out args tk e locals ts v_args b0
                 (transf_fundef fd)).
        * exact EVALargs.
        * rewrite (symbols_preserved _ _ (transf_program_match prog)); exact FINDsymb.
        * exact (function_ptr_translated _ _ (transf_program_match prog) b0 fd FINDfunct).
        * exact (match_cont_seq_cont F k tk MK CONTseq).
      + apply (match_state_call fd v_args (IR.Semantics.Kcall fn e locals k) s
                 (IR.Semantics.Kcall (transf_function fn) e locals tk) ts (sb_live locals :: F)).
        * exact WT'.
        * exact (mk_call F fn e locals k tk LEN MK).
        * exact SM.
    - injection ES1 as -> <- -> -> -> ->.
      destruct (state_match_pop_lockstep locals F s ts s' SM
                  (eq_trans (eq_sym (IR.Lemmas.pop_stack_length _ s locals LEN)) POPSTACK))
        as ( ts' & POPT & SM' ).
      left.
      exists (IR.Semantics.Callstate (transf_fundef fd) v_args tk ts').
      split.
      + change (transf_cmd b (c_app f_id t_out args)) with (c_app f_id t_out args).
        apply (IR.Semantics.step_tailapp _ (transf_function fn) f_id t_out args tk e locals ts
                 (transf_fundef fd) v_args ts' b0).
        * exact EVALargs.
        * rewrite (symbols_preserved _ _ (transf_program_match prog)); exact FINDsymb.
        * exact (function_ptr_translated _ _ (transf_program_match prog) b0 fd FINDfunct).
        * exact (eq_trans (IR.Lemmas.pop_stack_length _ ts locals LEN) POPT).
        * exact (match_cont_call_cont F k tk MK CONTcall).
      + exact (match_state_call fd v_args k s' tk ts' F WT' MK SM').
    - injection ES1 as -> <- -> -> -> ->.
      left.
      exists (IR.Semantics.State (transf_function fn) (transf_cmd b (if bb then c_t else c_e))
                tk e locals ts).
      split.
      + replace (transf_cmd b (if bb then c_t else c_e))
          with (if bb then transf_cmd b c_t else transf_cmd b c_e)
          by (destruct bb; reflexivity).
        change (transf_cmd b (c_if e_i c_t c_e t0))
          with (c_if e_i (transf_cmd b c_t) (transf_cmd b c_e) t0).
        exact (IR.Semantics.step_ifthenelse _ (transf_function fn) e_i (transf_cmd b c_t)
                 (transf_cmd b c_e) t0 tk e locals ts bb EVALif).
      + exact (match_state_normal fn (if bb then c_t else c_e) k e locals s b tk ts F
                 WT' TAILB MK LEN SM).
    - injection ES1 as -> <- -> -> -> ->.
      left.
      exists (IR.Semantics.State (transf_function fn) (transf_cmd false c_cond)
                (IR.Semantics.Kloop1 c_cond id_cond c_body id_body tk) e locals ts).
      split.
      + change (transf_cmd b (c_while c_cond id_cond c_body id_body))
          with (c_while (transf_cmd false c_cond) id_cond (transf_cmd false c_body) id_body).
        rewrite !transf_cmd_false.
        apply IR.Semantics.step_while.
      + apply (match_state_normal fn c_cond (IR.Semantics.Kloop1 c_cond id_cond c_body id_body k)
                 e locals s false (IR.Semantics.Kloop1 c_cond id_cond c_body id_body tk) ts F).
        * exact WT'.
        * intros EQ; discriminate EQ.
        * exact (mk_loop1 F c_cond id_cond c_body id_body k tk MK).
        * exact LEN.
        * exact SM.
  Qed.

  Lemma step_return_sim:
    forall v k s tk ts F t S1'
           (WT: IR.Semantics.wt_state prog (IR.Semantics.Returnstate v k s))
           (MK: match_cont F k tk)
           (SM: state_match F s ts)
           (STEP: IR.Semantics.step (Genv.globalenv prog) (IR.Semantics.Returnstate v k s) t S1'),
      (exists S2',
          IR.Semantics.step (Genv.globalenv (transf_program prog))
            (IR.Semantics.Returnstate v tk ts) t S2'
          /\ match_states S1' S2')
      \/ (measure S1' < measure (IR.Semantics.Returnstate v k s)
          /\ t = Events.E0
          /\ match_states S1' (IR.Semantics.Returnstate v tk ts))%nat.
  Proof using Type.
    intros v k s tk ts F t S1' WT MK SM STEP.
    pose proof (IR.Lemmas.preservation WT STEP) as WT'.
    remember (IR.Semantics.Returnstate v k s) as S1 eqn:ES1.
    revert ES1.
    destruct STEP as [ | | | | | | |
                     | ge0 v0 fn env locals k0 s0 c_next k' target_id SEQtarget SEQresolve ];
      intros ES1; try discriminate ES1.
    injection ES1 as -> <- ->.
    destruct (match_cont_call_cont_shape F _ tk MK (IR.Semantics.call_cont_Kcall fn env locals k0))
      as [ ( EK & _ & _ )
         | [ ( fn1 & e1 & locals1 & k1 & tk1 & F1 & EK & ETK & EF & LEN & MK1 )
           | ( fn1 & e1 & locals1 & x & chain & k1 & F1 & EK & EF & CHAIN & LEN & CALLCONT & MK1 ) ] ].
    - discriminate EK.
    - injection EK as <- <- <- <-.
      subst tk F.
      destruct (match_cont_resolve F1 k0 tk1 v c_next k' MK1 SEQresolve)
        as ( b' & tk' & RESOLVE_T & MK' & TAILB' ).
      left.
      exists (IR.Semantics.State (transf_function fn) (transf_cmd b' c_next) tk'
                (PTree.set target_id v env) locals ts).
      split.
      + exact (IR.Semantics.step_return_call_seq _ v (transf_function fn) env locals tk1 ts
                 (transf_cmd b' c_next) tk' target_id
                 (match_cont_seq_target F1 k0 tk1 target_id MK1 SEQtarget) RESOLVE_T).
      + exact (match_state_normal fn c_next k' (PTree.set target_id v env) locals s b' tk' ts F1
                 WT' TAILB' MK' LEN SM).
    - injection EK as <- <- <- ->.
      subst F.
      pose proof (IR.Lemmas.seq_cont_target_fun (IR.Semantics.seq_target_Kbind x chain k1) SEQtarget)
        as ETARGET.
      destruct (IR.Lemmas.resolve_seq_cont_fun (IR.Semantics.resolve_seq_Kbind x chain k1 v) SEQresolve)
        as ( ENEXT & EK' ).
      subst target_id c_next k'.
      right.
      split; [ apply measure_return_dead | split; [ reflexivity | ] ].
      exact (match_state_interm fn chain k1 (PTree.set x v env) locals s v k1 tk ts F1
               WT' (chain_state_start v env x chain k1 CHAIN) CALLCONT MK1 LEN SM).
  Qed.

  Lemma step_interm_sim:
    forall fn c K e locals s v k tk ts F t S1'
           (WT: IR.Semantics.wt_state prog (IR.Semantics.State fn c K e locals s))
           (CHST: chain_state v e c K k)
           (CALLCONT: IR.Semantics.is_call_cont k)
           (MK: match_cont F k tk)
           (LEN: List.length locals = Z.to_nat fn.(fn_extra).(fn_stackspace))
           (SM: state_match (sb_dead locals :: F) s ts)
           (STEP: IR.Semantics.step (Genv.globalenv prog)
                    (IR.Semantics.State fn c K e locals s) t S1'),
      (exists S2',
          IR.Semantics.step (Genv.globalenv (transf_program prog))
            (IR.Semantics.Returnstate v tk ts) t S2'
          /\ match_states S1' S2')
      \/ (measure S1' < measure (IR.Semantics.State fn c K e locals s)
          /\ t = Events.E0
          /\ match_states S1' (IR.Semantics.Returnstate v tk ts))%nat.
  Proof using Type.
    intros fn c K e locals s v k tk ts F t S1' WT CHST CALLCONT MK LEN SM STEP.
    pose proof (IR.Lemmas.preservation WT STEP) as WT'.
    right.
    remember (IR.Semantics.State fn c K e locals s) as S1 eqn:ES1.
    revert ES1.
    destruct STEP as [ ge0 f0 id_b t_b c_b c_c t_c k0 env0 locals0 s0
                     | ge0 f0 c0 k0 env0 locals0 s0 v0 s' s'' CONTcall BUILTIN POPSTACK
                     | ge0 f0 c0 k0 env0 locals0 s0 c_next k' target_id v0 s' SEQtarget SEQresolve
                         BUILTIN
                     | ge0 fn0 id t_out args k0 env0 locals0 s0 v_args b0 fd EVALargs FINDsymb
                         FINDfunct CONTseq
                     | ge0 fn0 f_id t_out args k0 env0 locals0 s0 fd v_args s' b0 EVALargs FINDsymb
                         FINDfunct POPSTACK CONTcall
                     | ge0 fn0 e_i c_t c_e t0 k0 env0 locals0 s0 bb EVALif
                     | ge0 fn0 c_cond id_cond c_body id_body k0 env0 locals0 s0
                     | | ];
      intros ES1; try discriminate ES1.
    - injection ES1 as -> <- -> -> -> ->.
      split; [ apply measure_chain_bind | split; [ reflexivity | ] ].
      exact (match_state_interm fn c_b (IR.Semantics.Kbind id_b c_c K) e locals s v k tk ts F
               WT' (chain_state_bind v e id_b t_b c_b c_c t_c K k CHST) CALLCONT MK LEN SM).
    - injection ES1 as -> -> -> -> -> ->.
      destruct (chain_state_shape v e c K k CHST)
        as [ ( z & t_r & -> ) | ( y & t_b & c1 & c2 & t_c & -> ) ];
        [ | inversion BUILTIN ].
      pose proof (chain_state_ret_final v e z t_r K k CHST) as GETZ.
      pose proof (chain_state_call_cont v e _ K k CHST CONTcall) as EK.
      subst K.
      assert (RET: eval (e_var z) e = Some v0 /\ s' = s)
        by (inversion BUILTIN; subst; split; [ assumption | reflexivity ]).
      destruct RET as ( EVAL & -> ).
      cbn [ eval ] in EVAL.
      assert (EV: v0 = v) by congruence.
      subst v0.
      pose proof (state_match_pop_dead locals F s ts s'' SM
                    (eq_trans (eq_sym (IR.Lemmas.pop_stack_length _ s locals LEN)) POPSTACK))
        as SM'.
      split; [ apply measure_chain_final | split; [ reflexivity | ] ].
      exact (match_state_return v k s'' tk ts F WT' MK SM').
    - injection ES1 as -> -> -> -> -> ->.
      destruct (chain_state_seq_target v e c K k target_id CHST CALLCONT SEQtarget)
        as ( c' & K' & -> ).
      destruct (IR.Lemmas.resolve_seq_cont_fun (IR.Semantics.resolve_seq_Kbind target_id c' K' v0)
                  SEQresolve)
        as ( ENEXT & EK' ).
      subst c_next k'.
      destruct (chain_state_shape v e c _ k CHST)
        as [ ( z & t_r & -> ) | ( y & t_b & c1 & c2 & t_c & -> ) ];
        [ | inversion BUILTIN ].
      destruct (chain_state_ret_seq v e z t_r target_id c' K' k CHST CALLCONT) as ( GETZ & CHST' ).
      assert (RET: eval (e_var z) e = Some v0 /\ s' = s)
        by (inversion BUILTIN; subst; split; [ assumption | reflexivity ]).
      destruct RET as ( EVAL & -> ).
      cbn [ eval ] in EVAL.
      assert (EV: v0 = v) by congruence.
      subst v0.
      split; [ apply measure_chain_ret_seq | split; [ reflexivity | ] ].
      exact (match_state_interm fn c' K' (PTree.set target_id v e) locals s v k tk ts F
               WT' CHST' CALLCONT MK LEN SM).
    - injection ES1 as -> <- -> -> -> ->.
      destruct CHST as ( aliases & CHAIN & _ & _ ).
      inversion CHAIN.
    - injection ES1 as -> <- -> -> -> ->.
      destruct CHST as ( aliases & CHAIN & _ & _ ).
      inversion CHAIN.
    - injection ES1 as -> <- -> -> -> ->.
      destruct CHST as ( aliases & CHAIN & _ & _ ).
      inversion CHAIN.
    - injection ES1 as -> <- -> -> -> ->.
      destruct CHST as ( aliases & CHAIN & _ & _ ).
      inversion CHAIN.
  Qed.

  Lemma transf_step_correct:
    forall S1 t S1'
           (STEP: IR.Semantics.step (Genv.globalenv prog) S1 t S1')
           S2 (MS: match_states S1 S2),
      (exists S2',
          IR.Semantics.step (Genv.globalenv (transf_program prog)) S2 t S2'
          /\ match_states S1' S2')
      \/ (measure S1' < measure S1 /\ t = Events.E0 /\ match_states S1' S2)%nat.
  Proof using Type.
    intros S1 t S1' STEP S2 MS.
    revert STEP.
    destruct MS as [ fn c k e locals s b tk ts F WT TAILB MK LEN SM
                   | fn f t_out args x chain k e locals s tk ts F WT CHAIN CALLCONT MK LEN SM
                   | fd args k s tk ts F WT MK SM
                   | v k s tk ts F WT MK SM
                   | fn c K e locals s v k tk ts F WT CHST CALLCONT MK LEN SM ];
      intros STEP.
    - exact (step_normal_sim fn c k e locals s b tk ts F t S1' WT TAILB MK LEN SM STEP).
    - exact (step_precall_sim fn f t_out args x chain k e locals s tk ts F t S1'
               WT CHAIN CALLCONT MK LEN SM STEP).
    - exact (step_call_sim fd args k s tk ts F t S1' WT MK SM STEP).
    - exact (step_return_sim v k s tk ts F t S1' WT MK SM STEP).
    - exact (step_interm_sim fn c K e locals s v k tk ts F t S1'
               WT CHST CALLCONT MK LEN SM STEP).
  Qed.

  Theorem transf_program_correct:
    forall tprog (TRANSL: match_prog prog tprog),
      Smallstep.forward_simulation (@IR.Semantics.semantics Sm prog)
                                   (@IR.Semantics.semantics Sm tprog).
  Proof using Type.
    intros tprog TRANSL.
    rewrite (match_prog_transf_program prog tprog TRANSL).
    apply Smallstep.forward_simulation_opt
      with (match_states := match_states) (measure := measure).
    - intros id.
      exact (proj1 (proj2 (senv_preserved prog (transf_program prog) (transf_program_match prog))) id).
    - exact transf_initial_states.
    - exact transf_final_states.
    - exact transf_step_correct.
  Qed.

End SIMULATION.

Section Link.

  Local Transparent Linker.Linker_fundef Linker.Linker_program.

  Lemma link_fundef_transf:
    forall (f1 f2: fundef),
      Linking.link (transf_fundef f1) (transf_fundef f2)
      = option_map transf_fundef (Linking.link f1 f2).
  Proof.
    intros [ fn1 | ef1 ] [ fn2 | ef2 ]; cbn.
    - reflexivity.
    - destruct ef2 as [ nm sg | | | | | | | | | | | ]; reflexivity.
    - destruct ef1 as [ nm sg | | | | | | | | | | | ]; reflexivity.
    - destruct (AST.external_function_eq ef1 ef2); reflexivity.
  Qed.

  Local Lemma link_match_fundef:
    forall (ctx1 ctx2: program) f1 tf1 f2 tf2 f
           (LINK: Linking.link f1 f2 = Some f)
           (MF1: match_fundef ctx1 f1 tf1)
           (MF2: match_fundef ctx2 f2 tf2),
      exists tf, Linking.link tf1 tf2 = Some tf
                 /\ (match_fundef ctx1 f tf \/ match_fundef ctx2 f tf).
  Proof.
    intros ctx1 ctx2 f1 tf1 f2 tf2 f LINK MF1 MF2.
    unfold match_fundef in MF1, MF2; subst tf1 tf2.
    exists (transf_fundef f); split; [ | left; reflexivity ].
    rewrite link_fundef_transf, LINK; reflexivity.
  Qed.

  Global Instance TransfTCOLink: Linking.TransfLink match_prog.
  Proof.
    intros p1 p2 tp1 tp2 p LINK MATCH1 MATCH2.
    apply match_prog_transf_program in MATCH1, MATCH2; subst tp1 tp2.
    exists (transf_program p); split; [ | apply transf_program_match ].
    destruct (Linking.link_linkorder _ _ _ LINK) as [ LO1 LO2 ].
    cbn [ Linking.link Linker.Linker_program ] in LINK |- *.
    destruct (Linking.link_match_program match_fundef match_varinfo
                link_match_fundef Common.Linker.link_match_varinfo_eq
                p1 p2 p _ _ _ _ _ (Linker.link_program_inv LINK)
                (transf_program_match p1) (transf_program_match p2)
                LO1 LO2)
      as ( TP & TLINK & TMATCH ).
    unfold Linker.link_program; rewrite TLINK.
    apply (f_equal Some), match_prog_transf_program.
    destruct TP as [ TPdefs TPpublic TPmain ].
    exact TMATCH.
  Qed.

End Link.
