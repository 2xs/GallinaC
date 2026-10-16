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

From Stdlib Require Import NArith Arith Psatz.

From HB Require Import structures.
From GallinaC.Utils Require Import ReflectExt.
From GallinaC.Imp Require Import Addr RWMemory Heap.
From Corelib Require Import ssreflect ssrfun ssrbool.

Declare Scope pointer_scope.
Delimit Scope pointer_scope with pointer.

Module Permission.
  Inductive t: Set := Cmp | Read | Write | Free.

  Inductive le: t -> t -> Prop :=
  | le_C: forall x, le Cmp x
  | le_RR: le Read Read
  | le_RW: le Read Write
  | le_RF: le Read Free
  | le_WW: le Write Write
  | le_WF: le Write Free
  | le_FF: le Free Free
  .

  Definition eqb (l r: t): bool :=
    match l, r with
    | Cmp, Cmp => true
    | Read, Read => true
    | Write, Write => true
    | Free, Free => true
    | _,_ => false
    end.

  Definition leb (l r: t): bool :=
    match l, r with
    | Cmp, _ => true
    | Read, (Read | Write | Free) => true
    | Write, (Write | Free) => true
    | Free, Free => true
    | _,_ => false
    end.

  Definition shrink (old new: t): option t :=
    match leb new old with
    | true => Some new
    | false => None
    end.

  Inductive Allows: t -> Operation.t -> Prop :=
  | AllowsCC: Allows Cmp Operation.Cmp
  | AllowsRC: Allows Read Operation.Cmp
  | AllowsRR: Allows Read Operation.Read
  | AllowsWC: Allows Write Operation.Cmp
  | AllowsWR: Allows Write Operation.Read
  | AllowsWW: Allows Write Operation.Write
  | AllowsFX: forall op, Allows Free op
  .
  Definition allows (perm: t) (op: Operation.t): bool :=
    match perm, op with
    | Free, (Operation.Cmp | Operation.Read | Operation.Write | Operation.Free) => true
    | Write, (Operation.Cmp | Operation.Read | Operation.Write) => true
    | Read, (Operation.Cmp | Operation.Read) => true
    | Cmp, Operation.Cmp => true
    | _,_ => false
    end.

  Lemma eq_dec: forall (x y: t), { x = y } + { x <> y }.
  Proof.
    move=> x y; case: x; case: y; by [ left | right ].
  Qed.
  Lemma eqb_refl: forall x, eqb x x = true.
    by move=> x; case: x.
  Qed.
  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
    by move=> x y; case: x; case: y; repeat constructor.
  Qed.
  Lemma eqb_sym: forall x y, eqb x y = eqb y x.
  Proof.
    by move=> x y; case: x; case: y.
  Qed.

  Lemma le_refl: forall x, le x x.
  Proof.
    by move=> x; elim: x; constructor.
  Qed.
  Lemma le_tran: forall x y z, le x y -> le y z -> le x z.
  Proof.
    move=> x y z LExy LEyz.
    by inversion LExy; subst; inversion LEyz; subst; constructor.
  Qed.
  Lemma le_dec: forall x y, { le x y } + { ~ le x y }.
  Proof.
    move=> x y; case: x; case: y;
      by [ repeat constructor | right; move=> LE; inversion LE ].
  Qed.
  Lemma leb_refl: forall x, leb x x = true.
  Proof.
    by move=> x; case: x.
  Qed.
  Lemma leb_spec: forall x y, Bool.reflect (le x y) (leb x y).
  Proof.
    move=> x y; case: x; case: y;
      by [ repeat constructor | right; move=> LE; inversion LE ].
  Qed.
  Lemma eqb_eq: forall x y, eqb x y = true <-> x = y.
  Proof.
    by move=> x y; case: x; case: y; repeat constructor.
  Qed.
  Lemma eqb_neq: forall x y, eqb x y = false <-> x <> y.
  Proof.
    by move=> x y; case: x; case: y; repeat constructor.
  Qed.
  Lemma shrink_spec: forall x y, le y x <-> shrink x y = Some y.
  Proof.
    move=> x y; case: x; case: y; rewrite /shrink /=; split=> H;
      by [ constructor | inversion H ].
  Qed.
  Lemma shrink_antispec: forall x y, ~le y x <-> shrink x y = None.
  Proof.
    move=> x y; case: x; case: y; rewrite /shrink /=; split=> H;
      by [ constructor | inversion H | exfalso; apply: H; constructor
         | move=> LE; inversion LE ].
  Qed.
  Lemma Allows_dec: forall perm op, { Allows perm op } + { ~Allows perm op }.
  Proof.
    move=> perm op; case: perm; case: op;
      try by [ left; constructor ];
      by right; move=> contra; inversion contra.
  Qed.
  Lemma allows_spec: forall perm op, Bool.reflect (Allows perm op) (allows perm op).
  Proof.
    move=> perm op; case: perm; case: op => /=;
      by [ repeat constructor | right; move=> A; inversion A ].
  Qed.

  Lemma allows_tran: forall perm op1 op2, Allows perm op1 -> Operation.le op2 op1 -> Allows perm op2.
  Proof.
    move=> perm op1 op2 ALLOWS LE.
    by inversion ALLOWS; subst; inversion LE; subst; constructor.
  Qed.

End Permission.

Module Addr.
  Record t: Set := mkAddr { block: nat; offset: N.t; }.

  Definition eqb l r :=
    match l, r with
    | mkAddr bl ol, mkAddr br or =>
        (Nat.eqb bl br && N.eqb ol or)%bool
    end.

  Lemma eq_dec: forall (x y: t), { x = y } + { x <> y }.
  Proof.
    move=> [ b_l o_l ] [ b_r o_r ].
    case: (Nat.eq_dec b_l b_r) => [ Heqb | Hneqb ];
      case: (N.eq_dec o_l o_r) => [ Heqo | Hneqo ]; subst;
      by [ left | right; move=> contra; inversion contra; contradiction ].
  Qed.
  Lemma eqb_refl: forall x, eqb x x = true.
  Proof.
    by move=> [ b o ]; rewrite /eqb /= Nat.eqb_refl N.eqb_refl.
  Qed.
  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
  Proof.
    move=> [ b_l o_l ] [ b_r o_r ]; rewrite /eqb /=.
    case: (Nat.eqb_spec b_l b_r) => [ -> | Hneqb ]; last by right; congruence.
    by case: (N.eqb_spec o_l o_r) => Ho; constructor; congruence.
  Qed.
  Lemma eqb_sym: forall x y, eqb x y = eqb y x.
  Proof.
    by move=> [ b_l o_l ] [ b_r o_r ];
      rewrite /eqb /= (Nat.eqb_sym b_l b_r) (N.eqb_sym o_l o_r).
  Qed.

  Lemma eqb_eq: forall x y, eqb x y = true <-> x = y.
  Proof.
    move=> [ b_l o_l ] [ b_r o_r ]; rewrite /eqb /=; split=> H.
    - move: H => /andb_prop [ /Nat.eqb_eq Hb /N.eqb_eq Ho ]; congruence.
    - by inversion H; subst; rewrite Nat.eqb_refl N.eqb_refl.
  Qed.
  Lemma eqb_neq: forall x y, eqb x y = false <-> x <> y.
  Proof.
    move=> [ b_l o_l ] [ b_r o_r ]; split=> H.
    - by move=> /eqb_eq; rewrite H.
    - case E: (eqb (mkAddr b_l o_l) (mkAddr b_r o_r)) => //.
      by exfalso; apply: H; apply eqb_eq; exact: E.
  Qed.

  Inductive Shift: t -> N.t -> t -> Prop :=
    ShiftAddr: forall block offset shift, Shift (mkAddr block offset) shift (mkAddr block (offset + shift)%N).

  Definition shift_fw a shift :=
    match a with
    | mkAddr block offset => mkAddr block (offset + shift)
    end.

  Definition shift_bw a shift :=
    match a with
    | mkAddr block offset =>
        if (shift <=? offset)%N then
          Some (mkAddr block (offset - shift))
        else
          None
    end.

  Lemma shift_fw_spec: forall a s a', Shift a s a' <-> (shift_fw a s) = a'.
  Proof.
    rewrite /shift_fw.
    move=> [ b o ] s [ b' o' ] /=.
    split=> HShiftFW.
    - by inversion HShiftFW; congruence.
    - by inversion HShiftFW; subst; constructor.
  Qed.

  Lemma ShiftFW_dec: forall a s, exists a', Shift a s a'.
  Proof.
    move=> [ b o ] s.
    by exists (shift_fw (mkAddr b o) s); constructor.
  Qed.

  Lemma Shift_fun: forall a s a' a'', Shift a s a' -> Shift a s a'' -> a'' = a'.
  Proof.
    move=> a s a' a'' HShiftFW1 HShiftFW2.
    by case: HShiftFW1 HShiftFW2 => b o sh HShiftFW2; inversion HShiftFW2.
  Qed.

  Lemma Shift_inj: forall a' a'' s a, Shift a' s a -> Shift a'' s a -> a'' = a'.
  Proof.
    move=> a' a'' s a HShift1 HShift2.
    inversion HShift1; subst; inversion HShift2; subst; f_equal;
      by [ congruence | lia ].
  Qed.

  Lemma shift_bw_spec: forall a s a', Shift a' s a <-> (shift_bw a s) = Some a'.
  Proof.
    rewrite /shift_bw.
    move=> [ b o ] s [ b' o' ] /=; split=> HShiftFW.
    - inversion HShiftFW; subst.
      case: (N.leb_spec0 s (o' + s)) => [ _ | ]; last by lia.
      by rewrite N.add_sub.
    - move: HShiftFW; case: (N.leb_spec0 s o) => [ Hle HShiftFW | Hnle ]; last by [].
      inversion HShiftFW; subst.
      have Hrewrite: o = ((o - s) + s)%N by lia.
      by rewrite {2}Hrewrite; constructor.
  Qed.

  Lemma shift_fw_0: forall a, shift_fw a 0 = a.
  Proof.
    by move=> [ b o ]; rewrite /shift_fw; f_equal; eauto using N.add_0_r.
  Qed.

  Lemma shift_fw_twice: forall a n1 n2, (shift_fw (shift_fw a n1) n2) = shift_fw a (n1+n2).
  Proof.
    by move=> [ b o ] n1 n2; rewrite /shift_fw; f_equal; lia.
  Qed.

  Lemma shift_fw_succ: forall b o s, shift_fw (mkAddr b o) (N.succ s) = shift_fw (mkAddr b (N.succ o)) s.
  Proof.
    by move=> b o s; rewrite /shift_fw; f_equal; lia.
  Qed.

  Lemma shift_fw_add: forall b o s, shift_fw (mkAddr b o) s = (mkAddr b (s + o)).
  Proof.
    by move=> b o s; rewrite /shift_fw; f_equal; lia.
  Qed.

  Lemma ShiftFW0: forall a, Shift a 0 a.
  Proof.
    by move=> [ b o ]; rewrite -{2}(N.add_0_r o); constructor.
  Qed.

  Lemma ShiftFW_add: forall b o s, Shift (mkAddr b o) s (mkAddr b (s + o)).
  Proof.
    by move=> b o s; rewrite -(N.add_comm o s); constructor.
  Qed.

End Addr.

Lemma Addr_block_mkAddr: forall b o, Addr.block (Addr.mkAddr b o) = b.
Proof. by []. Qed.
Lemma Addr_offset_mkAddr: forall b o, Addr.offset (Addr.mkAddr b o) = o.
Proof. by []. Qed.
Lemma Addr_mkAddr_ext: forall a, Addr.mkAddr (Addr.block a) (Addr.offset a) = a.
Proof. by move=> [ b o ]. Qed.

HB.instance Definition _ := hasEqDec.Build Addr.t Addr.eqb Addr.eqb_spec.
HB.instance Definition _ :=
  isAddr.Build Addr.t Addr.mkAddr Addr.block Addr.offset
    Addr_block_mkAddr Addr_offset_mkAddr Addr_mkAddr_ext.

Module Provenance.
  Record t: Set :=
    Allocation
      {
        prov_block: nat;
        prov_bofst: N;
        prov_eofst: N;
        prov_mbofst: N;
        prov_meofst: N;
        prov_perm: Permission.t;
      }.

  Inductive WF: t -> Prop :=
    WFProv: forall block bofst eofst mbofst meofst perm,
        (mbofst <= bofst)%N -> (eofst <= meofst)%N ->
        WF (Allocation block bofst eofst mbofst meofst perm).

  Definition wf prov :=
    match prov with
    | Allocation _ bofst eofst mbofst meofst _ =>
        ((mbofst <=? bofst)%N && (eofst <=? meofst)%N)%bool
    end.

  Inductive Within: Addr.t -> t -> Prop :=
    WithinProv: forall block ofst bofst eofst mbofst meofst perm,
        WF (Allocation block bofst eofst mbofst meofst perm) ->
        (bofst <= ofst)%N -> (ofst <= eofst)%N ->
        Within (Addr.mkAddr block ofst) (Allocation block bofst eofst mbofst meofst perm)
  .

  Definition within: Addr.t -> t -> bool :=
    fun addr prov =>
      match addr, prov with
      | Addr.mkAddr b_a ofst, (Allocation b_p bofst eofst mbofst meofst _) as prov =>
          ((b_a =? b_p) && wf prov &&
             (bofst <=? ofst)%N && (ofst <=? eofst)%N
          )%bool
      end
  .

  Inductive Allows: Addr.t -> Operation.t -> t -> Prop :=
  | AllowsCRW: forall block ofst bofst eofst mbofst meofst perm op,
      Within (Addr.mkAddr block ofst) (Allocation block bofst eofst mbofst meofst perm) ->
      (ofst < eofst)%N ->
      Permission.Allows perm op -> Operation.le op Operation.Write ->
      Allows (Addr.mkAddr block ofst) op (Allocation block bofst eofst mbofst meofst perm)
  | AllowsCmp: forall block ofst bofst eofst mbofst meofst perm,
      Within (Addr.mkAddr block ofst) (Allocation block bofst eofst mbofst meofst perm) ->
      Permission.Allows perm Operation.Cmp ->
      Allows (Addr.mkAddr block ofst) Operation.Cmp (Allocation block bofst eofst mbofst meofst perm)
  | AllowsFree: forall block eofst,
      (0 < eofst)%N ->
      Allows (Addr.mkAddr block 0) Operation.Free (Allocation block 0 eofst 0 eofst Permission.Free)
  .

  Definition allows addr op prov :=
    match op, addr, prov with
    | Operation.Cmp, Addr.mkAddr b o,
      Allocation block_p bofst eofst mbofst meofst perm =>
        (within addr prov && Permission.allows perm Operation.Cmp)%bool
    | (Operation.Read | Operation.Write), Addr.mkAddr b o,
      Allocation block_p bofst eofst mbofst meofst perm =>
        (within addr prov && (o <? eofst)%N && Permission.allows perm op)%bool
    | Operation.Free, Addr.mkAddr block_a 0, Allocation block_p 0 eofst 0 meofst Permission.Free =>
        ((block_a =? block_p) && (eofst =? meofst)%N && (0 <? eofst)%N)%bool
    | _, _, _ => false
    end.

  Definition eqb l r :=
    match l, r with
    | Allocation b_l bo_l eo_l mbo_l meo_l perm_l,
      Allocation b_r bo_r eo_r mbo_r meo_r perm_r =>
        (Nat.eqb b_l b_r &&
           N.eqb bo_l bo_r && N.eqb eo_l eo_r &&
           N.eqb mbo_l mbo_r && N.eqb meo_l meo_r &&
           Permission.eqb perm_l perm_r)%bool
    end.

  Lemma eq_dec: forall (x y: t), { x = y } + { x <> y }.
  Proof.
    move=> [ b_l bo_l eo_l mbo_l meo_l perm_l ] [ b_r bo_r eo_r mbo_r meo_r perm_r ];
      case: (Nat.eq_dec b_l b_r);
      case: (N.eq_dec bo_l bo_r);
      case: (N.eq_dec eo_l eo_r);
      case: (N.eq_dec mbo_l mbo_r);
      case: (N.eq_dec meo_l meo_r);
      case: (Permission.eq_dec perm_l perm_r);
      move=> *;
      by [ subst; left | right; move=> contra; inversion contra; contradiction ].
  Qed.
  Lemma eqb_refl: forall x, eqb x x = true.
  Proof.
    move=> [ b bo eo mbo meo perm ];
      by rewrite /eqb /= Nat.eqb_refl !N.eqb_refl Permission.eqb_refl.
  Qed.
  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
  Proof.
    move=> [ b_l bo_l eo_l mbo_l meo_l perm_l ] [ b_r bo_r eo_r mbo_r meo_r perm_r ];
      rewrite /eqb /=.
    case: (Nat.eqb_spec b_l b_r) => [ -> | Hb ]; last by right; congruence.
    case: (N.eqb_spec bo_l bo_r) => [ -> | Hbo ]; last by right; congruence.
    case: (N.eqb_spec eo_l eo_r) => [ -> | Heo ]; last by right; congruence.
    case: (N.eqb_spec mbo_l mbo_r) => [ -> | Hmbo ]; last by right; congruence.
    case: (N.eqb_spec meo_l meo_r) => [ -> | Hmeo ]; last by right; congruence.
    by case: (Permission.eqb_spec perm_l perm_r) => Hperm; constructor; congruence.
  Qed.
  Lemma eqb_sym: forall x y, eqb x y = eqb y x.
  Proof.
    move=> [ b_l bo_l eo_l mbo_l meo_l perm_l ] [ b_r bo_r eo_r mbo_r meo_r perm_r ];
      by rewrite /eqb /= (Nat.eqb_sym b_l) (N.eqb_sym bo_l) (N.eqb_sym eo_l)
                 (N.eqb_sym mbo_l) (N.eqb_sym meo_l) (Permission.eqb_sym perm_l).
  Qed.

  Lemma eqb_eq: forall x y, eqb x y = true <-> x = y.
  Proof.
    move=> [ b_l bo_l eo_l mbo_l meo_l perm_l ] [ b_r bo_r eo_r mbo_r meo_r perm_r ];
      rewrite /eqb /=; split=> H.
    - move: H => /andb_prop [ /andb_prop [ /andb_prop [ /andb_prop
        [ /andb_prop [ /Nat.eqb_eq Hb /N.eqb_eq Hbo ] /N.eqb_eq Heo ]
        /N.eqb_eq Hmbo ] /N.eqb_eq Hmeo ] /Permission.eqb_eq Hperm ].
      congruence.
    - by inversion H; subst;
        rewrite Nat.eqb_refl !N.eqb_refl Permission.eqb_refl.
  Qed.
  Lemma eqb_neq: forall x y, eqb x y = false <-> x <> y.
  Proof.
    move=> [ b_l bo_l eo_l mbo_l meo_l perm_l ] [ b_r bo_r eo_r mbo_r meo_r perm_r ];
      split=> H.
    - by move=> /eqb_eq; rewrite H.
    - case E: (eqb (Allocation b_l bo_l eo_l mbo_l meo_l perm_l)
                   (Allocation b_r bo_r eo_r mbo_r meo_r perm_r)) => //.
      by exfalso; apply: H; apply eqb_eq; exact: E.
  Qed.

  Lemma wf_spec: forall prov, Bool.reflect (WF prov) (wf prov).
  Proof.
    move=> [ block bofst eofst mbofst meofst perm ]; rewrite /wf /=.
    case: (N.leb_spec0 mbofst bofst) => [ Hmb | Hnmb ];
      last by right; move=> contra; inversion contra; lia.
    case: (N.leb_spec0 eofst meofst) => [ Hme | Hnme ];
      last by right; move=> contra; inversion contra; lia.
    by left; constructor.
  Qed.

  Lemma within_spec: forall addr prov, Bool.reflect (Within addr prov) (within addr prov).
  Proof.
    rewrite /within.
    move=> [ b o ] [ block bofst eofst mbofst meofst perm ]; cbn -[wf].
    case: (Nat.eqb_spec b block) => [ -> | Hnb ];
      last by right; move=> contra; inversion contra; lia.
    cbn -[wf].
    case: (wf_spec (Allocation block bofst eofst mbofst meofst perm)) => [ HWF | HNWF ];
      last by right; move=> contra; inversion contra; contradiction.
    rewrite /=.
    case: (N.leb_spec0 bofst o) => [ Hbo | Hnbo ];
      last by right; move=> contra; inversion contra; inversion H3; lia.
    rewrite /=.
    case: (N.leb_spec0 o eofst) => [ Heo | Hneo ];
      last by right; move=> contra; inversion contra; inversion H3; lia.
    by left; constructor.
  Qed.

  Lemma within_eq_block: forall b o prov, Within (Addr.mkAddr b o) prov -> prov_block prov = b.
  Proof.
    by move=> b o prov HWithin; inversion HWithin.
  Qed.
  Lemma within_le_eofst: forall b o prov, Within (Addr.mkAddr b o) prov -> (o <= prov_eofst prov)%N.
  Proof.
    by move=> b o prov HWithin; inversion HWithin; subst; rewrite /=; lia.
  Qed.

  Lemma allows_spec: forall addr op prov, Bool.reflect (Allows addr op prov) (allows addr op prov).
  Proof.
    move=> [ b o ] op [ block bofst eofst mbofst meofst perm ]; rewrite /=.
    case: (Operation.eqb_spec op Operation.Free) => [ Hopfree | Hopneq ];
      [ subst; rewrite /= | ].
    - case: o => [ | o ];
        last by right; move=> contra; inversion contra; subst; inversion H11.
      case: bofst => [ | bofst ];
        last by right; move=> contra; inversion contra; subst; inversion H11.
      case: mbofst => [ | mbofst ];
        last by right; move=> contra; inversion contra; subst; inversion H11.
      case: perm;
        try by right; move=> contra; inversion contra; inversion H11.
      case: (Nat.eqb_spec b block) => [ Heqb | Hneqb ];
        last by right; move=> contra; inversion contra; subst;
                try (inversion H11); contradiction.
      subst; rewrite /=.
      case: (N.eqb_spec eofst meofst) => [ Heqe | Hneqe ];
        last by right; move=> contra; inversion contra; subst; subst;
                try (inversion H10); contradiction.
      subst; rewrite /=.
      case: (N.ltb_spec0 0 meofst) => [ Hlt | Hnlt ];
        [ by left; apply: AllowsFree
        | by right; move=> contra; inversion contra; subst; lia ].
    - case: (Operation.eqb_spec op Operation.Cmp) => [ Hopcmp | Hopncmp ].
      + subst; rewrite /allows.
        case: (within_spec {| Addr.block := b; Addr.offset := o |}
                           (Allocation block bofst eofst mbofst meofst perm))
          => [ HWithin | HNWithin ];
          last by right; move=> contra; apply: HNWithin; inversion contra; subst.
        rewrite /=.
        case: (Permission.allows_spec perm Operation.Cmp) => [ HAllows | HNAllows ];
          last by right; move=> contra; inversion contra; subst; contradiction.
        left.
        have Hrewrite := within_eq_block _ _ _ HWithin; rewrite /= in Hrewrite; subst.
        by apply: AllowsCmp.
      + rewrite /allows.
        case: (within_spec {| Addr.block := b; Addr.offset := o |}
                           (Allocation block bofst eofst mbofst meofst perm))
          => [ HWithin | HNWithin ];
          last by rewrite /=; case: op Hopneq Hopncmp => Hopneq Hopncmp;
                  try (by contradiction);
                  right; move=> contra; inversion contra; congruence.
        rewrite /=.
        case: (N.ltb_spec0 o eofst) => [ Hlt | Hnlt ];
          last by rewrite /=; case: op Hopneq Hopncmp => Hopneq Hopncmp;
                  try (by contradiction);
                  right; move=> contra; inversion contra; lia.
        rewrite /=.
        case: (Permission.allows_spec perm op) => [ HAllows | HNAllows ];
          last by case: op HNAllows Hopneq Hopncmp => HNAllows Hopneq Hopncmp;
                  try (by contradiction);
                  right; move=> contra; inversion contra; subst; contradiction.
        case: op HAllows Hopneq Hopncmp => HAllows Hopneq Hopncmp;
          try (by contradiction).
        all: left; have Hrewrite := within_eq_block _ _ _ HWithin; rewrite /= in Hrewrite;
             subst; by constructor; auto; try lia; constructor.
  Qed.

  Lemma allows_within: forall a op prov, Allows a op prov -> Within a prov.
  Proof.
    move=> a op prov HAllows.
    case: HAllows;
      [ by move=> *; assumption | by move=> *; assumption | move=> block eofst Hlt ].
    by constructor; try lia; constructor; lia.
  Qed.

  Lemma allows_tran: forall a op1 prov op2 , Allows a op1 prov -> Operation.le op2 op1 -> Allows a op2 prov.
  Proof.
    move=> a op1 prov op2 ALLOWS LE.
    move: ALLOWS LE; case: op1; case: op2; move=> ALLOWS LE;
      inversion LE; subst;
      auto;
      inversion ALLOWS; subst;
      constructor; auto;
      try (by eapply Permission.allows_tran; eauto);
      try (by constructor);
      try (constructor;
           (try lia);
           constructor; try lia).
  Qed.

  Lemma allows_shift_within: forall a a' op prov
      (WI: within a' prov) (WIs: within (Addr.shift_fw a' 1) prov)
      (LE: Operation.le op Operation.Write),
      allows a op prov -> allows a' op prov.
  Proof.
    move=> [b o] [b' o'] op [pb bo eo mbo meo perm] WI WIs /Operation.leb_spec.
    have /N.ltb_lt LT: (o' < eo)%N by move/within_spec/within_le_eofst: WIs => /=; lia.
    by case: op => // _; rewrite /allows WI ?LT => /andP [_ ->].
  Qed.

End Provenance.

Module Pointer.
  Definition t := option (Addr.t * Provenance.t).

  Definition NULL: t := None.

  Inductive Allows: t -> Operation.t -> Prop :=
  | AllowsLive: forall addr prov op, Provenance.Allows addr op prov -> Allows (Some (addr, prov)) op
  | AllowsNull: Allows None Operation.Cmp.

  Definition allows ptr op :=
    match ptr with
    | Some (addr, prov) =>
        Provenance.allows addr op prov
    | None => Operation.eqb op Operation.Cmp
    end.

  Inductive References: t -> Addr.t -> Prop := RefPtr: forall addr prov, References (Some (addr, prov)) addr.

  Definition references (ptr: t) addr :=
    match ptr with
    | Some (a', _) => Addr.eqb addr a'
    | None => false
    end.

  Inductive Reaches: t -> Addr.t -> Prop :=
    ReachPtr: forall addr addr' prov, Provenance.Within addr' prov -> Reaches (Some (addr, prov)) addr'.

  Definition reaches (p: t) a :=
    match p with
    | Some (_,prov) => Provenance.within a prov
    | None => false
    end.

  Inductive Shift: t -> N.t -> t -> Prop :=
  | ShiftFWPtr: forall a prov shift a'
                       (HShiftAddr: Addr.Shift a shift a')
                       (HProvWithinsrc: Provenance.Within a prov)
                       (HProvWithindst: Provenance.Within a' prov),
      Shift (Some (a, prov)) shift (Some (a', prov))
  .

  Definition shift_fw p shift: option t :=
    match p with
    | Some (addr, prov) =>
        let addr' := Addr.shift_fw addr shift in
        if (Provenance.within addr prov && Provenance.within addr' prov)%bool then
          Some (Some (addr', prov))
        else
          None
    | None => None
    end.

  Definition shift_bw p shift: option t :=
    match p with
    | Some (addr, prov) =>
        match Addr.shift_bw addr shift with
        | Some addr' =>
            if (Provenance.within addr prov && Provenance.within addr' prov)%bool then
              Some (Some (addr', prov))
            else
              None
        | None => None
        end
    | None => None
    end.

  Definition eqb (p1 p2: t): bool :=
    match p1, p2 with
    | None, None => true
    | Some (a1, p1), Some (a2, p2) =>
        Addr.eqb a1 a2 && Provenance.eqb p1 p2
    | _, _ => false
    end.

  Lemma eq_dec: forall (x y: t), {x = y} + {x <> y}.
  Proof.
    move=> [ [ a1 p1 ] | ] [ [ a2 p2 ] | ];
      [
      |
        by right
      |
        by right
      |
        by left
      ].
    case: (Addr.eq_dec a1 a2) => [ -> | Ha ];
      case: (Provenance.eq_dec p1 p2) => [ -> | Hp ];
      by [ left | right; congruence ].
  Qed.

  Lemma eqb_refl: forall x, eqb x x = true.
  Proof.
    move=> [ [ a p ] | ] //=.
    by rewrite Addr.eqb_refl Provenance.eqb_refl.
  Qed.

  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
  Proof.
    move=> [ [ a1 p1 ] | ] [ [ a2 p2 ] | ]; try by constructor.
    case: (Addr.eqb_spec a1 a2) => [ -> | Hneqa ].
    - case: (Provenance.eqb_spec p1 p2) => [ -> | Hneqp ].
      + by rewrite /= Addr.eqb_refl Provenance.eqb_refl; constructor.
      + have Heqb: Provenance.eqb p1 p2 = false by apply Provenance.eqb_neq.
        rewrite /= Heqb Bool.andb_false_r.
        by right; congruence.
    - have Heqb: Addr.eqb a1 a2 = false by apply Addr.eqb_neq.
      rewrite /= Heqb /=.
      by right; congruence.
  Qed.

  Lemma eqb_sym: forall x y, eqb x y = eqb y x.
  Proof.
    move=> [ [ a1 p1 ] | ] [ [ a2 p2 ] | ] //.
    rewrite /eqb /=; f_equal;
      [ apply: Addr.eqb_sym | apply: Provenance.eqb_sym ].
  Qed.

  Lemma eqb_eq: forall x y, eqb x y = true <-> x = y.
  Proof.
    move=> [ [ a1 p1 ] | ] [ [ a2 p2 ] | ]; split=> H;
      try (by move: H; rewrite /=).
    - case: (Addr.eq_dec a1 a2) => [ -> | Hnea ].
      + case: (Provenance.eq_dec p1 p2) => [ -> | Hnep ]; first by [].
        move: H; rewrite /eqb /= => /Bool.andb_true_iff [ _ /Provenance.eqb_eq Hp ].
        congruence.
      + move: H; rewrite /eqb /= => /Bool.andb_true_iff [ /Addr.eqb_eq Ha _ ].
        congruence.
    - by inversion H; subst; apply: eqb_refl.
  Qed.

  Lemma eqb_neq : forall x y, eqb x y = false <-> x <> y.
  Proof.
    move=> x y; split=> H.
    - by move=> contra; subst; rewrite eqb_refl in H.
    - move: H; case: x => [ [ a1 p1 ] | ]; case: y => [ [ a2 p2 ] | ] H;
        try by []; try by contradiction.
      case: (Addr.eq_dec a1 a2) => [ Heqa | Hnea ].
      + subst.
        case: (Provenance.eq_dec p1 p2) => [ Heqp | Hneq ]; first by subst; congruence.
        have Heqb: Provenance.eqb p1 p2 = false by apply Provenance.eqb_neq.
        by rewrite /eqb /= Heqb Bool.andb_false_r.
      + have Heqb: Addr.eqb a1 a2 = false by apply Addr.eqb_neq.
        by rewrite /eqb /= Heqb.
  Qed.

  Lemma allows_tran: forall ptr op1 op2, Allows ptr op1 -> Operation.le op2 op1 -> Allows ptr op2.
  Proof.
    move=> ptr op1 op2 ALLOWS LE.
    inversion ALLOWS; subst; last by inversion LE; subst; constructor.
    by constructor; eapply Provenance.allows_tran; eauto.
  Qed.

  Lemma allows_spec: forall ptr op, Bool.reflect (Allows ptr op) (allows ptr op).
  Proof.
    move=> [ [ addr prov ] | ] op; last first.
    - by case: op; try by [ left; constructor ];
        right; move=> contra; inversion contra.
    - rewrite /=.
      case: (Provenance.allows_spec addr op prov) => [ HAllows | HNAllows ];
        [ by repeat constructor
        | by right; move=> contra; inversion contra; contradiction ].
  Qed.

  Lemma references_spec: forall ptr addr, Bool.reflect (References ptr addr) (references ptr addr).
  Proof.
    move=> [ [ addr prov ] | ] addr';
      last by right; move=> contra; inversion contra.
    rewrite /=.
    case: (Addr.eqb_spec addr' addr) => [ -> | Hne ];
      [ by repeat constructor
      | by right; move=> contra; inversion contra; congruence ].
  Qed.

  Lemma reaches_spec: forall ptr addr, Bool.reflect (Reaches ptr addr) (reaches ptr addr).
  Proof.
    move=> [ [ addr prov ] | ] addr';
      last by right; move=> contra; inversion contra.
    rewrite /=.
    case: (Provenance.within_spec addr' prov) => [ HWithin | HNWithin ];
      last by right; move=> contra; inversion contra.
    by left; constructor.
  Qed.

  Lemma shift_fw_spec: forall ptr shift ptr', (Shift ptr shift ptr') <-> (shift_fw ptr shift = Some ptr').
  Proof.
    move=> [ [ addr prov ] | ] shift ptr';
      last by split; move=> H; inversion H.
    rewrite /=.
    split=> HShiftFW.
    - inversion HShiftFW; subst.
      move/Addr.shift_fw_spec: HShiftAddr => Heq; subst.
      case: (Provenance.within_spec addr prov) => [ _ | HFalse ];
        last by contradiction.
      case: (Provenance.within_spec (Addr.shift_fw addr shift) prov) => [ _ | HFalse ];
        last by contradiction.
      by [].
    - move: HShiftFW.
      case: (Provenance.within_spec addr prov) => [ HWsrc | HNWsrc ] //=.
      case: (Provenance.within_spec (Addr.shift_fw addr shift) prov) => [ HWdst | HNWdst ] //=.
      move=> HShiftFW; inversion HShiftFW; subst.
      by constructor; auto; apply Addr.shift_fw_spec.
  Qed.

  Lemma Shift_fun: forall ptr shift ptr1 ptr2, Shift ptr shift ptr1 -> Shift ptr shift ptr2 -> ptr2 = ptr1.
  Proof.
    move=> ptr shift ptr1 ptr2 HShiftFW1 HShiftFW2.
    case: HShiftFW1 HShiftFW2 => a prov sh a' HSA HWsrc HWdst H2.
    inversion H2 as [ b prov' sh' a'' HSA' HWsrc' HWdst' ]; subst.
    have Heq: a'' = a' by eapply Addr.Shift_fun; eauto.
    by rewrite Heq.
  Qed.

  Lemma shift_bw_spec: forall ptr shift ptr', (Shift ptr' shift ptr) <-> (shift_bw ptr shift = Some ptr').
  Proof.
    move=> [ [ addr prov ] | ] shift ptr';
      last by split; move=> H; inversion H.
    rewrite /=.
    split=> [ HShiftFW | HShiftBW ].
    - inversion HShiftFW as [ ?a ?prov ?shift ?a' HShiftFWAddr ?HProvWithin ]; subst.
      move/Addr.shift_bw_spec: HShiftFWAddr => ->.
      case: (Provenance.within_spec addr prov) => [ _ | HFalse ];
        last by contradiction.
      case: (Provenance.within_spec a prov) => [ _ | HFalse ];
        last by contradiction.
      by [].
    - move: HShiftBW.
      case Eshift_bw: (Addr.shift_bw addr shift) => [ addr' | ] //=.
      case: (Provenance.within_spec addr prov) => [ HWithinsrc | HNsrc ] //=.
      case: (Provenance.within_spec addr' prov) => [ HWithindst | HNdst ] //=.
      move=> HShiftBW; inversion HShiftBW; subst.
      by constructor; auto; eapply Addr.shift_bw_spec; eauto.
  Qed.

  Lemma Shift_inj: forall ptr1 ptr2 shift ptr, Shift ptr1 shift ptr -> Shift ptr2 shift ptr -> ptr2 = ptr1.
  Proof.
    move=> ptr1 ptr2 shift ptr HShift1 HShift2.
    case: HShift1 HShift2 => a prov sh a' HSA HWsrc HWdst H2.
    inversion H2 as [ b prov' sh' a'' HSA' HWsrc' HWdst' ]; subst.
    have Heq: b = a by eapply Addr.Shift_inj; eauto.
    by rewrite Heq.
  Qed.

  Lemma references_eq ptr addr (HReferences: References ptr addr): { prov | ptr = Some (addr, prov) }.
  Proof.
    have Ereferences: references ptr addr = true
      by case: (references_spec ptr addr) => // HN; contradiction.
    move: Ereferences; rewrite /references.
    case: ptr HReferences => [ [ addr' prov ] | ] // HReferences.
    case: (Addr.eqb_spec addr addr') => [ -> | Hne ] // _.
    by exists prov.
  Qed.

End Pointer.

(* Pointers as references *)

Lemma addr_shift_fw_eq: forall (a: Addr.t) s, shift_fw a s = Addr.shift_fw a s.
Proof.
  by move=> [b o] s.
Qed.

Lemma addr_shift_bw_eq: forall (a: Addr.t) s, shift_bw a s = Addr.shift_bw a s.
Proof.
  by move=> [b o] s.
Qed.

Definition ptr_addr (p: Pointer.t): option Addr.t := option_map fst p.

Lemma ptr_allows_le: forall (r: Pointer.t) op1 op2,
    Operation.le op1 op2 -> is_true (Pointer.allows r op2) -> is_true (Pointer.allows r op1).
Proof.
  move=> r op1 op2 LE H.
  case: (Pointer.allows_spec r op1) => // NA.
  exfalso; apply: NA.
  apply: (Pointer.allows_tran r op2 op1); last exact: LE.
  by move: H; case: (Pointer.allows_spec r op2).
Qed.

HB.instance Definition _ :=
  isRef.Build Addr.t Pointer.t ptr_addr Pointer.allows ptr_allows_le.

Lemma pointer_null_addr: forall r: Pointer.t, ref_addr r = None <-> r = Pointer.NULL.
Proof.
  by move=> [[a prov]|]; split.
Qed.

Lemma pointer_null_cmp: forall op,
    Allows (Pointer.NULL) op <-> op = Operation.Cmp.
Proof.
  move=> op; split; last by move=> ->.
  move=> H; have H2: Operation.eqb op Operation.Cmp = true := H.
  by case: (Operation.eqb_spec op Operation.Cmp) H2.
Qed.

Lemma pointer_null_reaches: forall a: Addr.t, ~ is_true (Pointer.reaches Pointer.NULL a).
Proof.
  by move=> a H.
Qed.

Lemma provenance_within_block: forall (a: Addr.t) prov,
    Provenance.within a prov = true -> block a = Provenance.prov_block prov.
Proof.
  move=> [ba o] [pb bo eo mbo meo perm] /=.
  by move=> /andP [ /andP [ /andP [ /Nat.eqb_eq -> _ ] _ ] _ ].
Qed.

Lemma pointer_reaches_block: forall (p: Pointer.t) (a a': Addr.t),
    is_true (Pointer.reaches p a) -> is_true (Pointer.reaches p a') -> block a = block a'.
Proof.
  move=> [[a0 prov]|] a a' H1 H2 //.
  have W1: Provenance.within a prov = true := H1.
  have W2: Provenance.within a' prov = true := H2.
  by rewrite (provenance_within_block a prov W1) (provenance_within_block a' prov W2).
Qed.

Lemma pointer_shift_fw_references: forall (p: Pointer.t) s p'
    (EQ: Pointer.shift_fw p s = Some p')
    (a: Addr.t) (REF: References p a),
    References p' (shift_fw a s).
Proof.
  move=> [[a0 prov]|] s p' EQ a REF //.
  have REF2: Some a0 = Some a := REF.
  injection REF2 as REF2; subst a0.
  have EQ2: (if (Provenance.within a prov && Provenance.within (Addr.shift_fw a s) prov)%bool
             then Some (Some (Addr.shift_fw a s, prov))
             else None) = Some p' := EQ.
  move: EQ2.
  case C: (Provenance.within a prov && Provenance.within (Addr.shift_fw a s) prov)%bool => //.
  by move=> [<-]; rewrite addr_shift_fw_eq.
Qed.

Lemma pointer_shift_bw_references: forall (p: Pointer.t) s p'
    (EQ: Pointer.shift_bw p s = Some p')
    (a: Addr.t) (REF: References p a),
    exists a', shift_bw a s = Some a' /\ References p' a'.
Proof.
  move=> [[a0 prov]|] s p' EQ a REF //.
  have REF2: Some a0 = Some a := REF.
  injection REF2 as REF2; subst a0.
  have EQ2: match Addr.shift_bw a s with
            | Some addr' =>
                if (Provenance.within a prov && Provenance.within addr' prov)%bool
                then Some (Some (addr', prov))
                else None
            | None => None
            end = Some p' := EQ.
  move: EQ2.
  case ES: (Addr.shift_bw a s) => [addr'|] //.
  case C: (Provenance.within a prov && Provenance.within addr' prov)%bool => //.
  by move=> [<-]; exists addr'; split; [ rewrite addr_shift_bw_eq | ].
Qed.

Lemma pointer_shift_fw_some: forall (p: Pointer.t) s,
    (exists a: Addr.t, References p a
               /\ is_true (Pointer.reaches p a)
               /\ is_true (Pointer.reaches p (shift_fw a s)))
    <-> (exists p', Pointer.shift_fw p s = Some p').
Proof.
  move=> [[a0 prov]|] s; split.
  - move=> [a [REF [R1 R2]]].
    have REF2: Some a0 = Some a := REF.
    injection REF2 as REF2; subst a0.
    have W1: Provenance.within a prov = true := R1.
    have W2: Provenance.within (shift_fw a s) prov = true := R2.
    rewrite addr_shift_fw_eq in W2.
    exists (Some (Addr.shift_fw a s, prov)).
    by rewrite /Pointer.shift_fw W1 W2.
  - move=> [p' EQ].
    have EQ2: (if (Provenance.within a0 prov && Provenance.within (Addr.shift_fw a0 s) prov)%bool
               then Some (Some (Addr.shift_fw a0 s, prov))
               else None) = Some p' := EQ.
    move: EQ2.
    case W1: (Provenance.within a0 prov) => //.
    case W2: (Provenance.within (Addr.shift_fw a0 s) prov) => // _.
    exists a0; split=> //.
    split; first exact: W1.
    by rewrite addr_shift_fw_eq.
  - by move=> [a [REF _]].
  - by move=> [p' EQ].
Qed.

Lemma pointer_shift_bw_some: forall (p: Pointer.t) s,
    (exists (a a': Addr.t), References p a
                  /\ is_true (Pointer.reaches p a)
                  /\ shift_bw a s = Some a'
                  /\ is_true (Pointer.reaches p a'))
    <-> (exists p', Pointer.shift_bw p s = Some p').
Proof.
  move=> [[a0 prov]|] s; split.
  - move=> [a [a' [REF [R1 [ES R2]]]]].
    have REF2: Some a0 = Some a := REF.
    injection REF2 as REF2; subst a0.
    have W1: Provenance.within a prov = true := R1.
    have W2: Provenance.within a' prov = true := R2.
    rewrite addr_shift_bw_eq in ES.
    exists (Some (a', prov)).
    by rewrite /Pointer.shift_bw ES W1 W2.
  - move=> [p' EQ].
    have EQ2: match Addr.shift_bw a0 s with
              | Some addr' =>
                  if (Provenance.within a0 prov && Provenance.within addr' prov)%bool
                  then Some (Some (addr', prov))
                  else None
              | None => None
              end = Some p' := EQ.
    move: EQ2.
    case ES: (Addr.shift_bw a0 s) => [addr'|] //.
    case W1: (Provenance.within a0 prov) => //.
    case W2: (Provenance.within addr' prov) => // _.
    exists a0, addr'; split=> //.
    split; first exact: W1.
    by split; [ rewrite addr_shift_bw_eq | ].
  - by move=> [a [a' [REF _]]].
  - by move=> [p' EQ].
Qed.

Lemma pointer_shift_fw_reaches: forall (p: Pointer.t) s p'
    (EQ: Pointer.shift_fw p s = Some p')
    (a: Addr.t),
    is_true (Pointer.reaches p' a) <-> is_true (Pointer.reaches p a).
Proof.
  move=> [[a0 prov]|] s p' EQ a //.
  have EQ2: (if (Provenance.within a0 prov && Provenance.within (Addr.shift_fw a0 s) prov)%bool
             then Some (Some (Addr.shift_fw a0 s, prov))
             else None) = Some p' := EQ.
  move: EQ2.
  case: (Provenance.within a0 prov && Provenance.within (Addr.shift_fw a0 s) prov)%bool => //.
  by move=> [<-]; split.
Qed.

Lemma pointer_shift_bw_reaches: forall (p: Pointer.t) s p'
    (EQ: Pointer.shift_bw p s = Some p')
    (a: Addr.t),
    is_true (Pointer.reaches p' a) <-> is_true (Pointer.reaches p a).
Proof.
  move=> [[a0 prov]|] s p' EQ a //.
  have EQ2: match Addr.shift_bw a0 s with
            | Some addr' =>
                if (Provenance.within a0 prov && Provenance.within addr' prov)%bool
                then Some (Some (addr', prov))
                else None
            | None => None
            end = Some p' := EQ.
  move: EQ2.
  case: (Addr.shift_bw a0 s) => [addr'|] //.
  case: (Provenance.within a0 prov && Provenance.within addr' prov)%bool => //.
  by move=> [<-]; split.
Qed.

Lemma pointer_shift_fw_allows: forall (p: Pointer.t) s p' (a': Addr.t) op
    (EQ: Pointer.shift_fw p s = Some p')
    (REF: References p' a')
    (REACH: is_true (Pointer.reaches p' (shift_fw a' 1%N)))
    (LE: Operation.le op Operation.Write),
    Allows p op -> Allows p' op.
Proof.
  move=> [[a0 prov]|] s p' a' op //; rewrite /Pointer.shift_fw.
  case: ifP => // /andP [_ WI] [<-] [<-]; rewrite addr_shift_fw_eq => REACH LE.
  exact: Provenance.allows_shift_within WI REACH LE.
Qed.

Lemma pointer_shift_bw_allows: forall (p: Pointer.t) s p' (a': Addr.t) op
    (EQ: Pointer.shift_bw p s = Some p')
    (REF: References p' a')
    (REACH: is_true (Pointer.reaches p' (shift_fw a' 1%N)))
    (LE: Operation.le op Operation.Write),
    Allows p op -> Allows p' op.
Proof.
  move=> [[a0 prov]|] s p' a' op //; rewrite /Pointer.shift_bw.
  case: (Addr.shift_bw a0 s) => [addr'|] //.
  case: ifP => // /andP [_ WI] [<-] [<-]; rewrite addr_shift_fw_eq => REACH LE.
  exact: Provenance.allows_shift_within WI REACH LE.
Qed.

Lemma pointer_allows_free_inv: forall (a: Addr.t) prov,
    Pointer.allows (Some (a, prov)) Operation.Free = true ->
    exists b eo, a = Addr.mkAddr b 0%N
            /\ prov = Provenance.Allocation b 0%N eo 0%N eo Permission.Free
            /\ (0 < eo)%N.
Proof.
  move=> [ba o] [pb bo eo mbo meo perm] H.
  move: H.
  case: o => [|o]; case: bo => [|bo]; case: mbo => [|mbo]; case: perm => //=.
  move=> /andP [/andP [/Nat.eqb_eq H1 /N.eqb_eq H2] H3].
  subst pb meo.
  exists ba, eo.
  split; [ by [] | ].
  split; [ by [] | ].
  by apply/N.ltb_lt.
Qed.

Lemma pointer_allows_reaches: forall (p: Pointer.t) op (a: Addr.t)
    (ALW: Allows p op) (LE: Operation.le Operation.Read op) (REF: References p a),
    is_true (Pointer.reaches p a) /\ is_true (Pointer.reaches p (shift_fw a 1%N)).
Proof.
  move=> [[a0 prov]|] op a ALW LE REF; last by [].
  have Ea: Some a0 = Some a := REF.
  case: Ea => Ea; subst a0.
  have A: Provenance.allows a op prov = true := ALW.
  clear ALW REF.
  rewrite addr_shift_fw_eq.
  case: op A LE => A LE; first by inversion LE.
  - move: a prov A => [b o] [pb bo eo mbo meo perm] /andP [/andP [W /N.ltb_lt LT] _].
    split; first exact: W.
    move/Provenance.within_spec: W => W; inversion W; subst.
    by apply/Provenance.within_spec; constructor => //; lia.
  - move: a prov A => [b o] [pb bo eo mbo meo perm] /andP [/andP [W /N.ltb_lt LT] _].
    split; first exact: W.
    move/Provenance.within_spec: W => W; inversion W; subst.
    by apply/Provenance.within_spec; constructor => //; lia.
  - case: (pointer_allows_free_inv a prov A) => [b [eo [Ea [Ep POS]]]].
    subst a prov.
    by split; apply/Provenance.within_spec; (constructor; [ constructor; lia | lia | lia ]).
Qed.

Lemma pointer_free_base: forall (p: Pointer.t) (a a': Addr.t)
    (AF: Allows p Operation.Free) (REF: References p a) (RCH: is_true (Pointer.reaches p a')),
    (offset a <= offset a')%N.
Proof.
  move=> [[a0 prov]|] a a' AF REF RCH; last by [].
  have Ea: Some a0 = Some a := REF.
  case: Ea => Ea; subst a0.
  have A: Provenance.allows a Operation.Free prov = true := AF.
  clear AF REF.
  case: (pointer_allows_free_inv a prov A) => [b [eo [Ea [Ep POS]]]].
  subst a prov.
  exact: N.le_0_l.
Qed.

HB.instance Definition _ := hasEqDec.Build Pointer.t Pointer.eqb Pointer.eqb_spec.

HB.instance Definition _ :=
  isPtr.Build Addr.t Pointer.t
    Pointer.reaches
    Pointer.NULL
    pointer_null_addr
    pointer_null_cmp
    pointer_null_reaches
    pointer_reaches_block
    pointer_allows_reaches
    pointer_free_base
    Pointer.shift_fw
    Pointer.shift_bw
    pointer_shift_fw_references
    pointer_shift_bw_references
    pointer_shift_fw_some
    pointer_shift_bw_some
    pointer_shift_fw_reaches
    pointer_shift_bw_reaches
    pointer_shift_fw_allows
    pointer_shift_bw_allows.

Module Facts.

  Lemma addr_shift_fw_imm {a n}: Addr.Shift a n (Addr.shift_fw a n).
  Proof.
    by case: a; constructor.
  Qed.
  #[global] Hint Resolve addr_shift_fw_imm: mem.

End Facts.

Add Parametric Relation : Permission.t Permission.le
    reflexivity proved by Permission.le_refl
    transitivity proved by Permission.le_tran
    as perm_le_rel.
