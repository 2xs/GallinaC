From Stdlib Require Import NArith Arith Psatz.

From Utils Require Import ReflectExt.

Declare Scope pointer_scope.
Delimit Scope pointer_scope with pointer.


Module Operation.
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
    | _, _ => false
    end.

  Definition leb (l r: t): bool :=
    match l, r with
    | Cmp, _ => true
    | Read, (Read|Write|Free) => true
    | Write, (Write|Free) => true
    | Free, Free => true
    | _, _ => false
    end.

  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
  Proof.
    destruct x, y;
      now repeat constructor.
  Qed.

  Definition eq_dec: forall x y: t, { x = y } + { x <> y } := eq_dec_of_reflect eqb_spec.

  Definition eqb_refl: forall x, eqb x x = true := reflect_refl eqb_spec.
  Definition eqb_symm: forall x y, (eqb x y) = (eqb y x) := reflect_sym eqb_spec.
  (* Definition eqb_tran: forall x y z, eqb x y = true -> eqb y z = true -> eqb x z = true. *)

  Lemma eqb_eq: forall x y, eqb x y = true <-> x = y.
  Proof.
    destruct x, y; now repeat constructor.
  Qed.
  Lemma eqb_neq: forall x y, eqb x y = false <-> x <> y.
  Proof.
    destruct x, y; now repeat constructor.
  Qed.
End Operation.


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
    destruct x, y;
      (try (left; reflexivity));
      (try (right; discriminate)).
  Qed.
  Lemma eqb_refl: forall x, eqb x x = true.
    destruct x; reflexivity.
  Qed.
  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
    destruct x, y; now repeat constructor.
  Qed.
  Lemma eqb_sym: forall x y, eqb x y = eqb y x.
  Proof.
    destruct x, y; reflexivity.
  Qed.

  Lemma le_refl: forall x, le x x.
  Proof.
    induction x; constructor.
  Qed.
  Lemma le_tran: forall x y z, le x y -> le y z -> le x z.
  Proof.
    intros x y z LExy LEyz;
      inversion LExy; subst;
      inversion LEyz; subst;
      constructor.
  Qed.
  Lemma le_dec: forall x y, { le x y } + { ~ le x y }.
  Proof.
    destruct x, y; now repeat constructor.
  Qed.
  Lemma leb_refl: forall x, leb x x = true.
  Proof.
    destruct x; reflexivity.
  Qed.
  Lemma leb_spec: forall x y, Bool.reflect (le x y) (leb x y).
  Proof.
    destruct x, y; now repeat constructor.
  Qed.
  Lemma eqb_eq: forall x y, eqb x y = true <-> x = y.
  Proof.
    destruct x, y; now repeat constructor.
  Qed.
  Lemma eqb_neq: forall x y, eqb x y = false <-> x <> y.
  Proof.
    destruct x, y; now repeat constructor.
  Qed.
  Lemma shrink_spec: forall x y, le y x <-> shrink x y = Some y.
  Proof.
    destruct x, y; split; intros; now repeat constructor.
  Qed.
  Lemma shrink_antispec: forall x y, ~le y x <-> shrink x y = None.
  Proof.
    destruct x, y; split; intros;
      (try (now repeat constructor));
      (try (exfalso; apply H; now constructor)).
  Qed.
  Lemma Allows_dec: forall perm op, { Allows perm op } + { ~Allows perm op }.
  Proof.
    destruct perm, op;
      try (left; constructor);
      right; intros contra; inversion contra.
  Qed.
  Lemma allows_spec: forall perm op, Bool.reflect (Allows perm op) (allows perm op).
  Proof.
    destruct perm, op; cbn;
      (try (now repeat constructor)).
  Qed.

  Lemma allows_tran: forall perm op1 op2, Allows perm op1 -> Operation.le op2 op1 -> Allows perm op2.
  Proof.
    intros perm op1 op2 ALLOWS LE.
    inversion ALLOWS; subst; inversion LE; subst; constructor.
  Qed.

End Permission.

Module Addr.
  Record t: Set := mkAddr { block: nat; offset: N.t; }.

  Definition forge block offset := mkAddr block offset.

  Definition eqb l r :=
    match l, r with
    | mkAddr bl ol, mkAddr br or =>
        (Nat.eqb bl br && N.eqb ol or)%bool
    end.

  Lemma eq_dec: forall (x y: t), { x = y } + { x <> y }.
  Proof.
    destruct x as [ b_l o_l ], y as [ b_r o_r ].
    (destruct (Nat.eq_dec b_l b_r) as [ Heqb | Hneqb ], (N.eq_dec o_l o_r) as [ Heqo | Hneqo ]; subst);
    [ left; reflexivity
    | right; intros contra; inversion contra; contradiction
    | right; intros contra; inversion contra; contradiction
    | right; intros contra; inversion contra; contradiction
    ].
  Qed.
  Lemma eqb_refl: forall x, eqb x x = true.
  Proof.
    unfold eqb;
      destruct x;
      rewrite Nat.eqb_refl;
      rewrite N.eqb_refl;
      reflexivity.
  Qed.
  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
  Proof.
    unfold eqb;
      destruct x as [ b_l o_l ], y as [ b_r o_r ]; cbn.
    destruct (Nat.eqb_spec b_l b_r); [ subst | right; congruence ].
    destruct (N.eqb_spec o_l o_r); constructor; congruence.
  Qed.
  Lemma eqb_sym: forall x y, eqb x y = eqb y x.
  Proof.
    unfold eqb;
      destruct x as [ b_l o_l ], y as [ b_r o_r ];
      cbn;
      rewrite (Nat.eqb_sym b_l b_r);
      rewrite (N.eqb_sym o_l o_r);
      reflexivity.
  Qed.

  Lemma eqb_eq: forall x y, eqb x y = true <-> x = y.
  Proof.
    unfold eqb;
      (destruct x, y; split; intros H);
        [
          cbn in H; apply andb_prop in H; destruct H as [ Hb Ho ]; apply Nat.eqb_eq in Hb; apply N.eqb_eq in Ho; congruence
        |
          inversion H; subst; cbn; rewrite Nat.eqb_refl; rewrite N.eqb_refl; reflexivity
        ].
  Qed.
  Lemma eqb_neq: forall x y, eqb x y = false <-> x <> y.
  Proof.
    (destruct x, y; split; intros H);
      [
        intros contra; apply eqb_eq in contra; rewrite H in contra; discriminate
      |
        destruct (eqb _ _) eqn:E; [ exfalso; apply H; now apply eqb_eq | reflexivity ]
      ].
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
    unfold shift_fw.
    intros [ b o ] s [ b' o' ]; cbn.
    split; intros HShiftFW.
    - inversion HShiftFW; congruence.
    - inversion HShiftFW; subst. constructor.
  Qed.

  Lemma ShiftFW_dec: forall a s, exists a', Shift a s a'.
  Proof.
    intros [ b o ] s.
    exists (shift_fw (mkAddr b o) s).
    constructor.
  Qed.

  Lemma Shift_fw_fun: forall a s a' a'', Shift a s a' -> Shift a s a'' -> a'' = a'.
  Proof.
    intros a s a' a'' HShiftFW1 HShiftFW2.
    destruct HShiftFW1; inversion HShiftFW2; subst.
    reflexivity.
  Qed.

  Lemma Shift_bw_fun: forall a' a'' s a, Shift a' s a -> Shift a'' s a -> a'' = a'.
  Proof.
    intros a' a'' s a HShift1 HShift2.
    inversion HShift1; subst; inversion HShift2; subst;
      f_equal;
      try (congruence);
      try (lia).
  Qed.

  Lemma shift_bw_spec: forall a s a', Shift a' s a <-> (shift_bw a s) = Some a'.
  Proof.
    unfold shift_bw.
    intros [ b o ] s [ b' o' ]; cbn; split; intros HShiftFW.
    - inversion HShiftFW; subst.
      destruct (N.leb_spec0 s (o' + s)).
      rewrite N.add_sub.
      reflexivity.
      lia.
    - destruct (N.leb_spec0 s o).
      inversion HShiftFW; subst.
      assert (Hrewrite: o = ((o - s) + s)%N) by lia;
        rewrite Hrewrite at 2; clear Hrewrite.
      constructor.
      discriminate.
  Qed.

  Lemma shift_fw_0: forall a, shift_fw a 0 = a.
  Proof.
    intros [ ].
    unfold shift_fw; f_equal; eauto using N.add_0_r.
  Qed.

  Lemma shift_fw_twice: forall a n1 n2, (shift_fw (shift_fw a n1) n2) = shift_fw a (n1+n2).
  Proof.
    intros [] n1 n2.
    unfold shift_fw; f_equal; lia.
  Qed.

  Lemma shift_fw_succ: forall b o s, shift_fw (mkAddr b o) (N.succ s) = shift_fw (mkAddr b (N.succ o)) s.
  Proof.
    intros.
    unfold shift_fw; f_equal; lia.
  Qed.

  Lemma shift_fw_add: forall b o s, shift_fw (mkAddr b o) s = (mkAddr b (s + o)).
  Proof.
    intros b o s.
    unfold shift_fw; f_equal; lia.
  Qed.

  Lemma ShiftFW0: forall a, Shift a 0 a.
  Proof.
    now intros [ ]; rewrite <- N.add_0_r at 2.
  Qed.

  Lemma ShiftFW_add: forall b o s, Shift (mkAddr b o) s (mkAddr b (s + o)).
  Proof.
    now intros; rewrite <- N.add_comm.
  Qed.

End Addr.

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
  | AllowsFree: forall block eofst,
      (0 < eofst)%N ->
      Allows (Addr.mkAddr block 0) Operation.Free (Allocation block 0 eofst 0 eofst Permission.Free)
  .

  Definition allows addr op prov :=
    match op, addr, prov with
    | (Operation.Cmp | Operation.Read | Operation.Write), Addr.mkAddr b o,
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
    destruct x as [ b_l bo_l eo_l mbo_l meo_l perm_l ], y as [ b_r bo_r eo_r mbo_r meo_r perm_r ];
      destruct (Nat.eq_dec b_l b_r);
      destruct (N.eq_dec bo_l bo_r);
      destruct (N.eq_dec eo_l eo_r);
      destruct (N.eq_dec mbo_l mbo_r);
      destruct (N.eq_dec meo_l meo_r);
      destruct (Permission.eq_dec perm_l perm_r);
      (try (subst; left; reflexivity));
      (try (right; intros contra; inversion contra; contradiction)).
  Qed.
  Lemma eqb_refl: forall x, eqb x x = true.
  Proof.
    unfold eqb.
    destruct x; cbn;
      repeat (rewrite Nat.eqb_refl);
      repeat (rewrite N.eqb_refl); rewrite Permission.eqb_refl; reflexivity.
  Qed.
  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
  Proof.
    unfold eqb.
    destruct x as [ b_l bo_l eo_l mbo_l meo_l perm_l ], y as [ b_r bo_r eo_r mbo_r meo_r perm_r ];
      cbn.
    destruct (Nat.eqb_spec b_l b_r); [ subst | right; congruence ].
    destruct (N.eqb_spec bo_l bo_r); [ subst | right; congruence ].
    destruct (N.eqb_spec eo_l eo_r); [ subst | right; congruence ].
    destruct (N.eqb_spec mbo_l mbo_r); [ subst | right; congruence ].
    destruct (N.eqb_spec meo_l meo_r); [ subst | right; congruence ].
    destruct (Permission.eqb_spec perm_l perm_r); constructor; congruence.
  Qed.
  Lemma eqb_sym: forall x y, eqb x y = eqb y x.
  Proof.
    unfold eqb.
    destruct x as [ b_l bo_l eo_l mbo_l meo_l perm_l ], y as [ b_r bo_r eo_r mbo_r meo_r perm_r ];
      cbn;
      rewrite (Nat.eqb_sym b_l _);
      rewrite (N.eqb_sym bo_l _);
      rewrite (N.eqb_sym eo_l _);
      rewrite (N.eqb_sym mbo_l _);
      rewrite (N.eqb_sym meo_l _);
      rewrite (Permission.eqb_sym perm_l _);
      reflexivity.
  Qed.

  Lemma eqb_eq: forall x y, eqb x y = true <-> x = y.
  Proof.
    unfold eqb.
    (destruct x as [ b_l bo_l eo_l mbo_l meo_l perm_l ], y as [ b_r bo_r eo_r mbo_r meo_r perm_r ];
     split; intros H);
      [
        cbn in H;
        apply andb_prop in H; destruct H as [ H HPerm ];
        apply Permission.eqb_eq in HPerm; subst;
        apply andb_prop in H; destruct H as [ H Hmeo ];
        apply N.eqb_eq in Hmeo; subst;
        apply andb_prop in H; destruct H as [ H Hmbo ];
        apply N.eqb_eq in Hmbo; subst;
        apply andb_prop in H; destruct H as [ H Heo ];
        apply N.eqb_eq in Heo; subst;
        apply andb_prop in H; destruct H as [ Hb Hbo ];
        apply N.eqb_eq in Hbo; subst;
        apply Nat.eqb_eq in Hb; subst;
        reflexivity
      |
        inversion H;
        subst;
        cbn;
        repeat (rewrite Nat.eqb_refl);
        repeat (rewrite N.eqb_refl);
        rewrite Permission.eqb_refl;
        reflexivity
      ].
  Qed.
  Lemma eqb_neq: forall x y, eqb x y = false <-> x <> y.
  Proof.
    destruct x as [ b_l bo_l eo_l mbo_l meo_l perm_l ], y as [ b_r bo_r eo_r mbo_r meo_r perm_r ];
     split; intros H;
      [
        intros contra;
        apply eqb_eq in contra;
        rewrite H in contra;
        discriminate
      |
        destruct (eqb _ _) eqn:E; try reflexivity;
        exfalso;
        apply H;
        now apply eqb_eq
      ].
  Qed.

  Lemma wf_spec: forall prov, Bool.reflect (WF prov) (wf prov).
  Proof.
    unfold wf.
    destruct prov as [ block bofst eofst mbofst meofst perm ]; cbn.
    destruct (N.leb_spec0 mbofst bofst); [ cbn | right; intros contra; inversion contra; lia ].
    destruct (N.leb_spec0 eofst meofst); [ left | right; intros contra; inversion contra; lia ].
    now constructor.
  Qed.

  Lemma within_spec: forall addr prov, Bool.reflect (Within addr prov) (within addr prov).
  Proof.
    unfold within.
    intros [ b o ] [ block bofst eofst mbofst meofst perm ]; cbn -[wf].
    destruct (Nat.eqb_spec b block); [ subst; cbn -[wf] | right; intros contra; inversion contra; lia ].
    destruct (wf_spec (Allocation block bofst eofst mbofst meofst perm)); [ cbn | right; intros contra; inversion contra; contradiction ].
    destruct (N.leb_spec0 bofst o) as [ Hbo | ]; [ cbn | right; intros contra; inversion contra; inversion H3; lia ].
    destruct (N.leb_spec0 o eofst) as [ Heo | ]; [ left | right; intros contra; inversion contra; inversion H3; lia ].
    now constructor.
  Qed.

  Lemma within_eq_block: forall b o prov, Within (Addr.mkAddr b o) prov -> prov_block prov = b.
  Proof.
    intros b o prov HWithin; inversion HWithin; cbn; reflexivity.
  Qed.
  Lemma within_le_eofst: forall b o prov, Within (Addr.mkAddr b o) prov -> (o <= prov_eofst prov)%N.
  Proof.
    intros b o prov HWithin.
    inversion HWithin; subst; cbn; lia.
  Qed.

  Lemma allows_spec: forall addr op prov, Bool.reflect (Allows addr op prov) (allows addr op prov).
  Proof.
    intros [ b o ] op [ block bofst eofst mbofst meofst perm ]; cbn.
    destruct (Operation.eqb_spec op Operation.Free) as [ | Hopneq ]; [ subst; cbn | unfold allows ].
    - destruct o; [ cbn | right; intros contra; inversion contra; subst; inversion H11 ].
      destruct bofst; [ cbn | right; intros contra; inversion contra; subst; inversion H11 ].
      destruct mbofst; [ cbn | right; intros contra; inversion contra; subst; inversion H11 ].
      destruct perm;
        try (right; intros contra; inversion contra; inversion H11).
      destruct (Nat.eqb_spec b block); [ subst; cbn | right; intros contra; inversion contra; subst; try (inversion H11); contradiction ].
      destruct (N.eqb_spec eofst meofst); [ subst; cbn | right; intros contra; inversion contra; subst; subst; try (inversion H10); contradiction ].
      destruct (N.ltb_spec0 0 meofst); [ now left; apply AllowsFree | right; intros contra; inversion contra; subst; lia ].
    - destruct (within_spec {| Addr.block := b; Addr.offset := o |} (Allocation block bofst eofst mbofst meofst perm)) as [ HWithin | ]; [ cbn | cbn; destruct op; try (contradiction); right; intros contra; inversion contra; congruence ].
      destruct (N.ltb_spec0 o eofst); [ cbn | cbn; destruct op; (try (contradiction)); right; intros contra; inversion contra; lia ].
      destruct (Permission.allows_spec perm op) as [ HAllows | HNAllows ]; [ | destruct op; try (contradiction); right; intros contra; inversion contra; subst; contradiction ].
      destruct op; try (contradiction); left; assert (Hrewrite := within_eq_block _ _ _ HWithin); cbn in Hrewrite; subst; constructor; auto; try (lia); constructor.
  Qed.

  Lemma allows_within: forall a op prov, Allows a op prov -> Within a prov.
  Proof.
    intros a op prov HAllows.
    destruct HAllows; auto.
    constructor; try (lia).
    constructor; try (lia).
  Qed.

  Lemma allows_tran: forall a op1 prov op2 , Allows a op1 prov -> Operation.le op2 op1 -> Allows a op2 prov.
  Proof.
    intros a op1 prov op2 ALLOWS LE.
    destruct op1, op2; inversion LE; subst;
      auto;
      inversion ALLOWS; subst;
      constructor; auto;
      try (now eapply Permission.allows_tran; eauto);
      try (now constructor);
      try (constructor;
           (try lia);
           constructor; try lia).
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

  Definition cmp (p1 p2: t): option bool :=
    if (allows p1 Operation.Cmp && allows p2 Operation.Cmp)%bool then
      Some (eqb p1 p2)
    else
      None
  .

  Lemma eq_dec: forall (x y: t), {x = y} + {x <> y}.
  Proof.
    destruct x as [ [ a1 p1 ] | ] , y as [ [ a2 p2 ] | ];
      [
      |
        right; discriminate
      |
        right; discriminate
      |
        now constructor
      ].
    destruct (Addr.eq_dec a1 a2), (Provenance.eq_dec p1 p2)
    ;
      [
        left; subst; reflexivity
      |
        right; congruence
      |
        right; congruence
      |
        right; congruence
      ].
  Qed.

  Lemma eqb_refl: forall x, eqb x x = true.
  Proof.
    destruct x as [ [ a p ] | ]; [ | reflexivity ].
    cbn.
    now rewrite Addr.eqb_refl, Provenance.eqb_refl.
  Qed.

  Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
  Proof.
    destruct x as [ [ a1 p1 ] | ], y as [ [ a2 p2 ] | ]; try (now constructor).
    destruct (Addr.eqb_spec a1 a2); subst.
    - destruct (Provenance.eqb_spec p1 p2); subst.
      cbn.
      rewrite Addr.eqb_refl, Provenance.eqb_refl.
      now constructor.
      specialize n as Hneq.
      apply Provenance.eqb_neq in n.
      cbn.
      rewrite n.
      rewrite Bool.andb_false_r.
      right.
      congruence.
    - cbn.
      specialize n as Hneq.
      apply Addr.eqb_neq in n.
      rewrite n; cbn.
      right.
      congruence.
  Qed.

  Lemma eqb_sym: forall x y, eqb x y = eqb y x.
  Proof.
    destruct x as [ [ a1 p1 ] | ], y as [ [ a2 p2 ] | ]; try reflexivity.
    unfold eqb.
    f_equal.
    apply Addr.eqb_sym.
    apply Provenance.eqb_sym.
  Qed.

  Lemma eqb_eq: forall x y, eqb x y = true <-> x = y.
  Proof.
    destruct x as [ [ a1 p1 ] | ], y as [ [ a2 p2 ] | ]; split; intros H;
      (try (cbn in H; discriminate));
      (try reflexivity).
    - destruct (Addr.eq_dec a1 a2); [ subst | ].
      + destruct (Provenance.eq_dec p1 p2); [ congruence | ].
        unfold eqb in H.
        apply Bool.andb_true_iff in H.
        destruct H as [ _ H ].
        apply Provenance.eqb_eq in H.
        congruence.
      + unfold eqb in H.
        apply Bool.andb_true_iff in H.
        destruct H as [ H _ ].
        apply Addr.eqb_eq in H.
        congruence.
    - inversion H; subst; clear H.
      apply eqb_refl.
  Qed.

  Lemma eqb_neq : forall x y, eqb x y = false <-> x <> y.
  Proof.
    intros x y; split; intros H.
    intros contra; subst; rewrite eqb_refl in H; discriminate.
    destruct x as [ [ a1 p1 ] | ], y as [ [ a2 p2 ] | ];
      try reflexivity;
      try (contradiction).
    destruct (Addr.eq_dec a1 a2); [ subst | ].
    - destruct (Provenance.eq_dec p1 p2) as [ | Hneq ]; [ congruence | ].
      apply Provenance.eqb_neq in Hneq.
      unfold eqb.
      rewrite Hneq.
      apply Bool.andb_false_r.
    - unfold eqb.
      apply Addr.eqb_neq in n.
      rewrite n.
      reflexivity.
  Qed.

  Lemma allows_tran: forall ptr op1 op2, Allows ptr op1 -> Operation.le op2 op1 -> Allows ptr op2.
  Proof.
    intros ptr op1 op2 ALLOWS LE.
    inversion ALLOWS; subst; [ | inversion LE; subst; constructor ].
    constructor.
    eapply Provenance.allows_tran; eauto.
  Qed.

  Lemma allows_spec: forall ptr op, Bool.reflect (Allows ptr op) (allows ptr op).
  Proof.
    intros [ [ addr prov ] | ] op; [ cbn | destruct op; try (left; constructor); right; intros contra; now inversion contra ].
    destruct (Provenance.allows_spec addr op prov) as [ HAllows | HNAllows ]; [ now repeat constructor | right; intros contra; inversion contra; contradiction ].
  Qed.

  Lemma references_spec: forall ptr addr, Bool.reflect (References ptr addr) (references ptr addr).
  Proof.
    intros [ [ addr prov ] | ] addr'; [ cbn | right; intros contra; now inversion contra ].
    destruct (Addr.eqb_spec addr' addr); [ subst; now repeat constructor | right; intros contra; inversion contra; congruence ].
  Qed.

  Lemma reaches_spec: forall ptr addr, Bool.reflect (Reaches ptr addr) (reaches ptr addr).
  Proof.
    intros [ [ addr prov ] | ] addr'; [ cbn | right; intros contra; now inversion contra ].
    destruct (Provenance.within_spec addr' prov) as [ HWithin | ]; [ left | right; intros contra; now inversion contra ].
    now constructor.
  Qed.

  Lemma cmp_eqb: forall x y, (Allows x Operation.Cmp /\ Allows y Operation.Cmp) <-> cmp x y = Some (eqb x y).
  Proof.
    intros x y.
    split.
    - intros [ HAllowsx HAllowsy ].
      unfold cmp, eqb.
      destruct (allows_spec x Operation.Cmp) as [ _ | ]; [ | contradiction ].
      destruct (allows_spec y Operation.Cmp) as [ _ | ]; [ | contradiction ].
      reflexivity.
    - unfold cmp, eqb.
      intros Heq.
      destruct (allows_spec x Operation.Cmp) as [ HAllowsx | ]; [ | discriminate ].
      destruct (allows_spec y Operation.Cmp) as [ HAllowsy | ]; [ | discriminate ].
      now split.
  Qed.

  Lemma shift_fw_spec: forall ptr shift ptr', (Shift ptr shift ptr') <-> (shift_fw ptr shift = Some ptr').
  Proof.
    intros [ [ addr prov ] | ] shift ptr'; [ cbn | split; cbn; intros H; now inversion H ].
    split; intros HShiftFW.
    - inversion HShiftFW; subst.
      apply Addr.shift_fw_spec in HShiftAddr; subst.
      destruct (Provenance.within_spec addr prov) as [ _ | HFalse ] in HProvWithinsrc; [ cbn | contradiction ].
      destruct (Provenance.within_spec (Addr.shift_fw addr shift) prov) as [ _ | HFalse ] in HProvWithinsrc; [ cbn | contradiction ].
      reflexivity.
    - destruct (Provenance.within_spec addr prov); [ cbn in HShiftFW | discriminate ].
      destruct (Provenance.within_spec (Addr.shift_fw addr shift) prov); [ | discriminate ].
      inversion HShiftFW; subst.
      constructor; auto.
      now eapply Addr.shift_fw_spec.
  Qed.

  Lemma Shift_fw_fun: forall ptr shift ptr1 ptr2, Shift ptr shift ptr1 -> Shift ptr shift ptr2 -> ptr2 = ptr1.
  Proof.
    intros ptr shift ptr1 ptr2 HShiftFW1 HShiftFW2.
    destruct HShiftFW1; inversion HShiftFW2; subst.
    assert (a'0 = a') by (eapply Addr.Shift_fw_fun; eauto); subst.
    reflexivity.
  Qed.

  Lemma shift_bw_spec: forall ptr shift ptr', (Shift ptr' shift ptr) <-> (shift_bw ptr shift = Some ptr').
  Proof.
    intros [ [ addr prov ] | ] shift ptr'; [ cbn | split; cbn; intros H; now inversion H ].
    split; [ intros HShiftFW | intros HShiftBW ].
    - inversion HShiftFW as [ ?a ?prov ?shift ?a' HShiftFWAddr ?HProvWithin ]; subst.
      apply Addr.shift_bw_spec in HShiftFWAddr; rewrite HShiftFWAddr.
      destruct (Provenance.within_spec addr prov) as [ _ | HFalse ]; [ cbn | contradiction ].
      destruct (Provenance.within_spec a prov) as [ _ | HFalse ]; [ cbn | contradiction ].
      reflexivity.
    - destruct (Addr.shift_bw addr shift) as [ addr' | ] eqn:Eshift_bw; [ cbn in HShiftBW | discriminate ].
      destruct (Provenance.within_spec addr prov) as [ HWithinsrc | ]; [ cbn in HShiftBW | discriminate ].
      destruct (Provenance.within_spec addr' prov) as [ HWithindst | ]; [ cbn in HShiftBW | discriminate ].
      inversion HShiftBW; subst.
      constructor; auto.
      eapply Addr.shift_bw_spec; eauto.
  Qed.

  Lemma Shift_bw_fun: forall ptr1 ptr2 shift ptr, Shift ptr1 shift ptr -> Shift ptr2 shift ptr -> ptr2 = ptr1.
  Proof.
    intros ptr1 ptr2 shift ptr HShift1 HShift2.
    destruct HShift1; inversion HShift2; subst.
    assert (a0 = a) by (eapply Addr.Shift_bw_fun; eauto); subst.
    reflexivity.
  Qed.

  Lemma references_eq ptr addr (HReferences: References ptr addr): { prov | ptr = Some (addr, prov) }.
  Proof.
    destruct (references ptr addr) eqn:Ereferences; [ | destruct (references_spec ptr addr); [ discriminate | contradiction ] ].
    unfold references in Ereferences.
    destruct ptr as [ [ addr' prov ] | ]; [ | discriminate ].
    destruct (Addr.eqb_spec addr addr'); [ subst | discriminate ].
    now exists prov.
  Qed.

End Pointer.

Module Facts.

  Lemma addr_shift_fw_imm {a n}: Addr.Shift a n (Addr.shift_fw a n).
  Proof.
    destruct a; now constructor.
  Qed.
  #[global] Hint Resolve addr_shift_fw_imm: mem.

End Facts.

Add Parametric Relation : Permission.t Permission.le
    reflexivity proved by Permission.le_refl
    transitivity proved by Permission.le_tran
    as perm_le_rel.
