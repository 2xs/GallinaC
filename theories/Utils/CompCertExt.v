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

From Stdlib Require Import Bool ZArith Lia.

From compcert Require AST Integers Floats Linking Smallstep.
From compcert.lib Require Coqlib.
From compcert.common Require Memory.

From GallinaC.Utils Require Import ListExt OptionExt Algebra.

(* [norm_state] vm-normalizes the source state of a [Smallstep.star]
   goal. Building block for tactics like [OpSem.one_step] and [IR.one_step] *)
Ltac norm_state :=
  match goal with
  | |- Smallstep.star _ _ ?S _ _ =>
      let S' := eval vm_compute in S in
        change S with S'
  end.

Module Typ.

  Export AST.

  Definition eqb (t1 t2: typ): bool :=
    match t1, t2 with
    | Tint, Tint => true
    | Tlong, Tlong => true
    | Tfloat, Tfloat => true
    | Tsingle, Tsingle => true
    | Tany32, Tany32 => true
    | Tany64, Tany64 => true
    | (Tint|Tfloat|Tlong|Tsingle|Tany32|Tany64), _ => false
    end.

  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
  Proof.
    destruct x, y; constructor; congruence.
  Qed.

End Typ.

HB.instance Definition _ := hasEqDec.Build _ Typ.eqb Typ.eqb_spec.

Module XType.

  Export AST.

  Definition eqb (t1 t2: xtype): bool :=
    match t1, t2 with
    | Xbool, Xbool => true
    | Xint8signed, Xint8signed => true
    | Xint8unsigned, Xint8unsigned => true
    | Xint16signed, Xint16signed => true
    | Xint16unsigned, Xint16unsigned => true
    | Xint, Xint => true
    | Xlong, Xlong => true
    | Xfloat, Xfloat => true
    | Xsingle, Xsingle => true
    | Xptr, Xptr => true
    | Xany32, Xany32 => true
    | Xany64, Xany64 => true
    | Xvoid, Xvoid => true
    | _, _ => false
    end.

  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
  Proof.
    destruct x, y; constructor;
      solve
        [ reflexivity
        | intros contra; discriminate ].
  Qed.

End XType.

HB.instance Definition _ := hasEqDec.Build _ XType.eqb XType.eqb_spec.

Module CallingConvention.

  Export AST.

  Definition eqb (cc1 cc2: AST.calling_convention): bool :=
    option_eqb Z.eqb cc1.(cc_vararg) cc2.(cc_vararg)
    && Bool.eqb cc1.(cc_unproto) cc2.(cc_unproto)
    && Bool.eqb cc1.(cc_structret) cc2.(cc_structret).

  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
  Proof.
    destruct x, y.
    unfold eqb; cbn.
    destruct (option_eqb_spec Z.eqb_spec cc_vararg cc_vararg0);
      [ cbn | right; congruence ].
    destruct (Bool.eqb_spec cc_unproto cc_unproto0);
      [ cbn | right; congruence ].
    destruct (Bool.eqb_spec cc_structret cc_structret0);
      constructor; congruence.
  Qed.

End CallingConvention.

HB.instance Definition _ := hasEqDec.Build _ CallingConvention.eqb CallingConvention.eqb_spec.

Module Sig.
  Export AST.

  Definition eqb (sig1 sig2: AST.signature): bool :=
    list_eqb XType.eqb sig1.(sig_args) sig2.(sig_args)
    && XType.eqb sig1.(sig_res) sig2.(sig_res)
    && CallingConvention.eqb sig1.(sig_cc) sig2.(sig_cc).

  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
  Proof.
    destruct x, y.
    unfold eqb; cbn -[list_eqb].
    destruct (list_eqb_spec _ sig_args sig_args0 XType.eqb_spec); [ cbn | right; congruence ].
    destruct (XType.eqb_spec sig_res sig_res0); [ cbn | right; congruence ].
    destruct (CallingConvention.eqb_spec sig_cc sig_cc0);
      constructor;
      congruence.
  Qed.

End Sig.

HB.instance Definition _ := hasEqDec.Build _ Sig.eqb Sig.eqb_spec.

Module MChunk.

  Export AST.

  Definition eqb (mc1 mc2: memory_chunk): bool :=
    match mc1, mc2 with
    | Mbool, Mbool => true
    | Mint8signed, Mint8signed => true
    | Mint8unsigned, Mint8unsigned => true
    | Mint16signed, Mint16signed => true
    | Mint16unsigned, Mint16unsigned => true
    | Mint32, Mint32 => true
    | Mint64, Mint64 => true
    | Mfloat32, Mfloat32 => true
    | Mfloat64, Mfloat64 => true
    | Many32, Many32 => true
    | Many64, Many64 => true
    | _, _ => false
    end.

  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
  Proof.
    destruct x, y; constructor; congruence.
  Qed.

End MChunk.

HB.instance Definition _ := hasEqDec.Build _ MChunk.eqb MChunk.eqb_spec.

Module ExtFun.

  Export AST.

  Definition is_runtime (ef: AST.external_function): bool :=
    match ef with
    | AST.EF_runtime _ _ => true
    | _ => false
    end.

  Definition eqb (ef1 ef2: external_function): bool :=
    match ef1, ef2 with
    | EF_external s1 sig1, EF_external s2 sig2
    | EF_builtin s1 sig1, EF_builtin s2 sig2
    | EF_runtime s1 sig1, EF_runtime s2 sig2
      => String.eqb s1 s2 && Sig.eqb sig1 sig2
    | EF_vload mc1, EF_vload mc2
    | EF_vstore mc1, EF_vstore mc2 =>
        MChunk.eqb mc1 mc2
    | EF_malloc, EF_malloc => true
    | EF_free, EF_free => true
    | EF_memcpy n1 m1, EF_memcpy n2 m2 =>
        Z.eqb n1 n2 && Z.eqb m1 m2
    | EF_annot p1 s1 args1, EF_annot p2 s2 args2 =>
        Pos.eqb p1 p2 && String.eqb s1 s2 && list_eqb Typ.eqb args1 args2
    | EF_annot_val p1 s1 t1, EF_annot_val p2 s2 t2 =>
        Pos.eqb p1 p2 && String.eqb s1 s2 && Typ.eqb t1 t2
    | EF_inline_asm s1 sig1 sl1, EF_inline_asm s2 sig2 sl2 =>
        String.eqb s1 s2 && Sig.eqb sig1 sig2 && list_eqb String.eqb sl1 sl2
    | EF_debug p1 id1 typs1, EF_debug p2 id2 typs2 =>
        Pos.eqb p1 p2 && Pos.eqb id1 id2 && list_eqb Typ.eqb typs1 typs2
    | _, _ => false
    end.

  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
  Proof.
    destruct x, y;
      cbn;
      repeat first
        [ constructor; congruence
        | match goal with
          | |- context [String.eqb ?x ?y] =>
              destruct (String.eqb_spec x y); [ cbn | right; congruence ]
          | |- context [Sig.eqb ?x ?y] =>
              destruct (Sig.eqb_spec x y); [ cbn | right; congruence ]
          | |- context [MChunk.eqb ?x ?y] =>
              destruct (MChunk.eqb_spec x y); [ cbn | right; congruence ]
          | |- context [Z.eqb ?x ?y] =>
              destruct (Z.eqb_spec x y); [ cbn | right; congruence ]
          | |- context [Pos.eqb ?x ?y] =>
              destruct (Pos.eqb_spec x y); [ cbn | right; congruence ]
          | |- context [Typ.eqb ?x ?y] =>
              destruct (Typ.eqb_spec x y); [ cbn | right; congruence ]
          | |- context [list_eqb Typ.eqb ?x ?y] =>
              destruct (list_eqb_spec _ x y Typ.eqb_spec); [ cbn | right; congruence ]
          | |- context [list_eqb String.eqb ?x ?y] =>
              destruct (list_eqb_spec _ x y String.eqb_spec); [ cbn | right; congruence ]
          end
        ].
  Qed.

End ExtFun.

HB.instance Definition _ := hasEqDec.Build _ ExtFun.eqb ExtFun.eqb_spec.

Module InitData.

  Export AST.

  Definition eqb (x y: init_data): bool :=
    match x, y with
    | Init_int8 i1, Init_int8 i2
    | Init_int16 i1, Init_int16 i2
    | Init_int32 i1, Init_int32 i2 =>
        if Integers.Int.eq_dec i1 i2 then true else false
    | Init_int64 i1, Init_int64 i2 =>
        if Integers.Int64.eq_dec i1 i2 then true else false
    | Init_float32 f1, Init_float32 f2 =>
        if Floats.Float32.eq_dec f1 f2 then true else false
    | Init_float64 f1, Init_float64 f2 =>
        if Floats.Float.eq_dec f1 f2 then true else false
    | Init_space z1, Init_space z2 =>
        Z.eqb z1 z2
    | Init_addrof id1 o1, Init_addrof id2 o2 =>
        Pos.eqb id1 id2 && (if Integers.Ptrofs.eq_dec o1 o2 then true else false)
    | _, _ => false
    end.

  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
  Proof.
    destruct x, y;
      cbn [eqb];
      repeat first
        [ constructor; congruence
        | match goal with
          | |- context [Integers.Int.eq_dec ?x ?y] =>
              destruct (Integers.Int.eq_dec x y); [ cbn [andb] | right; congruence ]
          | |- context [Integers.Int64.eq_dec ?x ?y] =>
              destruct (Integers.Int64.eq_dec x y); [ cbn [andb] | right; congruence ]
          | |- context [Floats.Float32.eq_dec ?x ?y] =>
              destruct (Floats.Float32.eq_dec x y); [ cbn [andb] | right; congruence ]
          | |- context [Floats.Float.eq_dec ?x ?y] =>
              destruct (Floats.Float.eq_dec x y); [ cbn [andb] | right; congruence ]
          | |- context [Z.eqb ?x ?y] =>
              destruct (Z.eqb_spec x y); [ cbn [andb] | right; congruence ]
          | |- context [Pos.eqb ?x ?y] =>
              destruct (Pos.eqb_spec x y); [ cbn [andb] | right; congruence ]
          | |- context [Integers.Ptrofs.eq_dec ?x ?y] =>
              destruct (Integers.Ptrofs.eq_dec x y); [ cbn [andb] | right; congruence ]
          end
        ].
  Qed.

End InitData.

HB.instance Definition _ := hasEqDec.Build _ InitData.eqb InitData.eqb_spec.

Module GlobVar.

  Export AST.

  Definition eqb [V: EqDec.type]
    (x y: globvar V): bool :=
    eqb x.(gvar_info) y.(gvar_info)
    && list_eqb InitData.eqb x.(gvar_init) y.(gvar_init)
    && Bool.eqb x.(gvar_readonly) y.(gvar_readonly)
    && Bool.eqb x.(gvar_volatile) y.(gvar_volatile).

  Lemma eqb_spec {V: EqDec.type}:
    forall x y: globvar V, Bool.reflect (x = y) (eqb x y).
  Proof.
    destruct x, y.
    unfold eqb; cbn -[list_eqb].
    destruct (eqb_spec gvar_info gvar_info0) as [ EQ | NE ]; [ cbn [andb] | right; congruence ].
    destruct (list_eqb_spec _ gvar_init gvar_init0 InitData.eqb_spec);
      [ cbn | right; congruence ].
    destruct (Bool.eqb_spec gvar_readonly gvar_readonly0); [ cbn | right; congruence ].
    destruct (Bool.eqb_spec gvar_volatile gvar_volatile0);
      constructor; congruence.
  Qed.

End GlobVar.

HB.instance Definition _ (V: EqDec.type) := hasEqDec.Build (AST.globvar V) (@GlobVar.eqb V) GlobVar.eqb_spec.

Module FunDef.

  Export AST.

  Definition eqb [F: EqDec.type]
    (x y: fundef F): bool :=
    match x, y with
    | Internal f1, Internal f2 => eqb f1 f2
    | External ef1, External ef2 => ExtFun.eqb ef1 ef2
    | _, _ => false
    end.

  Lemma eqb_spec {F: EqDec.type}:
    forall x y: fundef F, Bool.reflect (x = y) (eqb x y).
  Proof.
    destruct x as [f1|ef1], y as [f2|ef2]; cbn [eqb].
    - destruct (eqb_spec f1 f2); constructor; congruence.
    - right; congruence.
    - right; congruence.
    - destruct (ExtFun.eqb_spec ef1 ef2); constructor; congruence.
  Qed.

End FunDef.

HB.instance Definition _ (F: EqDec.type) := hasEqDec.Build (AST.fundef F) (@FunDef.eqb F) FunDef.eqb_spec.

Module GlobDef.

  Export AST.

  Definition eqb [F V: EqDec.type]
    (x y: AST.globdef F V): bool :=
    match x, y with
    | Gfun x, Gfun y => eqb x y
    | Gvar x, Gvar y => eqb x y
    | _, _ => false
    end.

  Lemma eqb_spec {F V: EqDec.type}:
    forall x y: globdef F V, Bool.reflect (x = y) (eqb x y).
  Proof.
    destruct x as [f1|v1], y as [f2|v2]; cbn [eqb].
    - destruct (eqb_spec f1 f2); constructor; congruence.
    - right; congruence.
    - right; congruence.
    - destruct (eqb_spec v1 v2); constructor; congruence.
  Qed.

End GlobDef.

HB.instance Definition _ (F V: EqDec.type) := hasEqDec.Build (AST.globdef F V) (@GlobDef.eqb F V) GlobDef.eqb_spec.

Module MatchDefs.
  Section MatchDefs.

    Context [C F1 V1 F2 V2: Type].
    Context [LC: Linking.Linker C].
    Context [mf: C -> F1 -> F2 -> Prop] [mv: V1 -> V2 -> Prop].

    Lemma match_defs_map_fst [ctx dl tl]
      (MDEFS: Coqlib.list_forall2
                (Linking.match_ident_globdef mf mv ctx) dl tl):
      List.map fst tl = List.map fst dl.
    Proof using Type.
      induction MDEFS as [ | d1 dl d2 tl M MDEFS IH ]; [ reflexivity | ].
      cbn [List.map]; rewrite IH.
      destruct M as ( EID & _ ); rewrite EID; reflexivity.
    Qed.

    Lemma match_defs_In_fun [ctx dl tl id f]
      (MDEFS: Coqlib.list_forall2
                (Linking.match_ident_globdef mf mv ctx) dl tl)
      (IN: List.In (id, AST.Gfun f) dl):
      exists f', List.In (id, AST.Gfun f') tl.
    Proof using Type.
      induction MDEFS as [ | d1 dl d2 tl M MDEFS IH ]; [ contradiction | ].
      destruct d2 as [ id2 def2 ].
      destruct IN as [ EQ | IN ];
        [ | destruct (IH IN) as ( f' & INf ); exists f'; right; exact INf ].
      destruct M as ( EID & MD ).
      rewrite EQ in EID, MD; cbn [fst snd] in EID, MD.
      subst id2.
      inversion MD as [ ?ctx' ?f1 ?f2 ?ctx'' LO MF | ]; subst.
      exists f2; left; reflexivity.
    Qed.

    Lemma match_defs_norepet [ctx dl tl]
      (MDEFS: Coqlib.list_forall2
                (Linking.match_ident_globdef mf mv ctx) dl tl)
      (SBINDS: SBinds dl):
      SBinds tl.
    Proof using Type.
      apply (proj2 (SBinds_list_norepet _)).
      rewrite (match_defs_map_fst MDEFS).
      exact (proj1 (SBinds_list_norepet _) SBINDS).
    Qed.

  End MatchDefs.
End MatchDefs.

Module Ints.

  Module Ptrofs.

    Lemma bound_int64 (ARCHI: Archi.ptr64 = true) [x: Z]
      (BND: (0 <= x <= Integers.Ptrofs.max_unsigned)%Z)
      : (0 <= x <= Integers.Int64.max_unsigned)%Z.
    Proof using Type.
      specialize (Integers.Ptrofs.modulus_eq64 ARCHI) as PM.
      unfold Integers.Ptrofs.max_unsigned in BND.
      unfold Integers.Int64.max_unsigned; lia.
    Qed.

    Lemma bound_int32 (ARCHI: Archi.ptr64 = false) [x: Z]
      (BND: (0 <= x <= Integers.Ptrofs.max_unsigned)%Z)
      : (0 <= x <= Integers.Int.max_unsigned)%Z.
    Proof using Type.
      specialize (Integers.Ptrofs.modulus_eq32 ARCHI) as PM.
      unfold Integers.Ptrofs.max_unsigned in BND.
      unfold Integers.Int.max_unsigned; lia.
    Qed.

  End Ptrofs.

  Lemma int64_add_repr (x y: Z)
    : Integers.Int64.add (Integers.Int64.repr x) (Integers.Int64.repr y)
      = Integers.Int64.repr (x + y)%Z.
  Proof using Type.
    rewrite Integers.Int64.add_unsigned; apply Integers.Int64.eqm_samerepr.
    apply Integers.Int64.eqm_add;
      apply Integers.Int64.eqm_sym, Integers.Int64.eqm_unsigned_repr.
  Qed.

  Lemma int_add_repr (x y: Z)
    : Integers.Int.add (Integers.Int.repr x) (Integers.Int.repr y)
      = Integers.Int.repr (x + y)%Z.
  Proof using Type.
    rewrite Integers.Int.add_unsigned; apply Integers.Int.eqm_samerepr.
    apply Integers.Int.eqm_add;
      apply Integers.Int.eqm_sym, Integers.Int.eqm_unsigned_repr.
  Qed.

End Ints.

Module CCMem.

  Lemma free_stack_block_perm [m sp lo sz m']
    (FREE: Memory.Mem.free m sp lo sz = Some m')
    [b] (DSJ: b <> sp \/ (sz <= lo)%Z)
    [lo0 hi0 k p] (RP: Memory.Mem.range_perm m b lo0 hi0 k p)
    : Memory.Mem.range_perm m' b lo0 hi0 k p.
  Proof using Type.
    intros ofs RNG.
    refine (Memory.Mem.perm_free_1 _ _ _ _ _ FREE b ofs k p _ (RP ofs RNG)).
    destruct DSJ as [ NE | LE ]; [ now left | ].
    destruct (Z.lt_ge_cases ofs lo) as [ LT | GE ];
      [ right; left; exact LT | right; right; lia ].
  Qed.

  Lemma free_stack_block_load [m sp lo sz m']
    (FREE: Memory.Mem.free m sp lo sz = Some m')
    [b] (DSJ: b <> sp \/ (sz <= lo)%Z) (mc: AST.memory_chunk) (ofs: Z)
    : Memory.Mem.load mc m' b ofs = Memory.Mem.load mc m b ofs.
  Proof using Type.
    refine (Memory.Mem.load_free _ _ _ _ _ FREE mc b ofs _).
    destruct DSJ as [ NE | LE ]; [ now left | right; left; lia ].
  Qed.

  Lemma free_stack_block_contents [m sp lo sz m']
    (FREE: Memory.Mem.free m sp lo sz = Some m')
    : Memory.Mem.mem_contents m' = Memory.Mem.mem_contents m.
  Proof using Type.
    now rewrite (Memory.Mem.free_result _ _ _ _ _ FREE).
  Qed.

  Lemma free_stack_block_access [m sp lo sz m']
    (FREE: Memory.Mem.free m sp lo sz = Some m')
    [b] (DSJ: b <> sp \/ (sz <= lo)%Z)
    : Maps.PMap.get b (Memory.Mem.mem_access m') 0%Z Memtype.Max
      = Maps.PMap.get b (Memory.Mem.mem_access m) 0%Z Memtype.Max.
  Proof using Type.
    rewrite (Memory.Mem.free_result _ _ _ _ _ FREE).
    unfold Memory.Mem.unchecked_free; cbn [Memory.Mem.mem_access].
    rewrite Maps.PMap.gsspec.
    destruct (Coqlib.peq b sp) as [ EB | NEB ]; [ subst b | reflexivity ].
    destruct DSJ as [ NE | LE ]; [ now contradiction NE | ].
    destruct (Coqlib.zle lo 0) as [ LE0 | GT0 ]; [ | reflexivity ].
    destruct (Coqlib.zlt 0 sz) as [ LT0 | GE0 ]; [ lia | reflexivity ].
  Qed.

  Lemma alloc_contents_other [m lo hi m1 bh]
    (CALLOC: Memory.Mem.alloc m lo hi = (m1, bh))
    [b'] (NE: b' <> bh)
    : Maps.PMap.get b' (Memory.Mem.mem_contents m1)
      = Maps.PMap.get b' (Memory.Mem.mem_contents m).
  Proof using Type.
    pose proof (Memory.Mem.alloc_result _ _ _ _ _ CALLOC) as EB.
    subst bh.
    injection CALLOC as EM.
    rewrite <- EM; cbn [Memory.Mem.mem_contents].
    apply Maps.PMap.gso; exact NE.
  Qed.

  Lemma alloc_access_other [m lo hi m1 bh]
    (CALLOC: Memory.Mem.alloc m lo hi = (m1, bh))
    [b'] (NE: b' <> bh)
    : Maps.PMap.get b' (Memory.Mem.mem_access m1)
      = Maps.PMap.get b' (Memory.Mem.mem_access m).
  Proof using Type.
    pose proof (Memory.Mem.alloc_result _ _ _ _ _ CALLOC) as EB.
    subst bh.
    injection CALLOC as EM.
    rewrite <- EM; cbn [Memory.Mem.mem_access].
    apply Maps.PMap.gso; exact NE.
  Qed.

  Lemma bool_of_val_of_bool (b: bool)
    : Values.Val.bool_of_val (Values.Val.of_bool b) b.
  Proof using Type.
    destruct b; cbn.
    - replace true with (negb (Integers.Int.eq Integers.Int.one Integers.Int.zero))
        by reflexivity.
      constructor.
    - replace false with (negb (Integers.Int.eq Integers.Int.zero Integers.Int.zero))
        by (rewrite Integers.Int.eq_true; reflexivity).
      constructor.
  Qed.

  Lemma vptrofs_load_result (x: Integers.Ptrofs.int)
    : Values.Val.load_result AST.Mptr (Values.Vptrofs x) = Values.Vptrofs x.
  Proof using Type.
    unfold AST.Mptr, Values.Vptrofs; destruct Archi.ptr64; reflexivity.
  Qed.

  Lemma mptr_align_neg: (Memdata.align_chunk AST.Mptr | - Memdata.size_chunk AST.Mptr)%Z.
  Proof using Type.
    unfold AST.Mptr; destruct Archi.ptr64; cbn; exists (-1)%Z; reflexivity.
  Qed.

  Lemma load_bool_init [m b ofs n]
    (RANGE: Integers.Int.unsigned n = 0%Z \/ Integers.Int.unsigned n = 1%Z)
    (LD: Memory.Mem.load AST.Mint8unsigned m b ofs
         = Some (Values.Vint (Integers.Int.zero_ext 8 n)))
    : Memory.Mem.load AST.Mbool m b ofs
      = Some (if (Integers.Int.unsigned n =? 1)%Z then Values.Vtrue else Values.Vfalse).
  Proof using Type.
    rewrite Memory.Mem.load_bool_int8_unsigned LD; cbn.
    destruct RANGE as [ E | E ].
    - assert (EN: n = Integers.Int.zero)
        by (apply Integers.Int.same_if_eq; unfold Integers.Int.eq;
            rewrite E Integers.Int.unsigned_zero; reflexivity).
      subst n; rewrite Integers.Int.unsigned_zero; reflexivity.
    - assert (EN: n = Integers.Int.one)
        by (apply Integers.Int.same_if_eq; unfold Integers.Int.eq;
            rewrite E Integers.Int.unsigned_one; reflexivity).
      subst n; rewrite Integers.Int.unsigned_one; reflexivity.
  Qed.

End CCMem.
