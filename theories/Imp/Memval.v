From Stdlib Require Import Program NArith Arith Bool.
From GallinaC.Imp Require Export Pointer.

Local Obligation Tactic := idtac.

Inductive memval: Set :=
| VUnit: memval
| VBool: bool -> memval
| VInt: nat -> memval
| VOfst: N.t -> memval
| VPtr: Pointer.t -> memval
.

Lemma eq_dec: forall (v w: memval), {v = w } + { v <> w }.
Proof.
  destruct v as [|[ | ]| | |], w as [|[|]| | |];
    try (constructor; congruence).
  destruct (Nat.eq_dec n n0); constructor; congruence.
  destruct (N.eq_dec t t0); constructor; congruence.
  destruct (Pointer.eq_dec t t0); constructor; congruence.
Qed.

Structure MemStorable :=
  {
    obj :> Type;
    encode: obj -> memval;
    decode: memval -> option obj;

    encode_decode: forall o, decode (encode o) = Some o;
    decode_encode: forall v o, decode v = Some o -> encode o = v;
  }.

Arguments obj MS: rename.
Arguments encode {MS} o: rename.
Arguments decode {MS} v: rename.
Arguments encode_decode [MS] o: rename.
Arguments decode_encode [MS] v o Hdecode: rename.

Hint Rewrite encode_decode decode_encode: mem.

Module StorableNat.

  Definition nat_encode := VInt.
  Definition nat_decode (v: memval) :=
    match v with
    | VInt n => Some n
    | VUnit | VOfst _ | VPtr _ | VBool _ => None
    end.

  Program Definition nat_storable :=
    {|
      obj := nat;
      encode := nat_encode;
      decode := nat_decode;
    |}.

  Next Obligation.
    reflexivity.
  Qed.

  Next Obligation.
    destruct v;
      intros o Hdecode; cbn in Hdecode;
      inversion Hdecode; subst.
    reflexivity.
  Qed.

End StorableNat.

Canonical StorableNat.nat_storable.

Module StorablePtr.

  Definition ptr_encode := VPtr.
  Definition ptr_decode (v: memval) :=
    match v with
    | VPtr p => Some p
    | VUnit | VInt _ | VOfst _ | VBool _ => None
    end.

  Program Definition ptr_storable :=
    {|
      obj := Pointer.t;
      encode := ptr_encode;
      decode := ptr_decode;
    |}.

  Next Obligation.
    reflexivity.
  Qed.

  Next Obligation.
    destruct v;
      intros o Hdecode; cbn in Hdecode;
      inversion Hdecode; subst.
    reflexivity.
  Qed.

End StorablePtr.

Canonical StorablePtr.ptr_storable.

Module StorableBool.

  Definition bool_encode := VBool.
  Definition bool_decode (v: memval) :=
    match v with
    | VBool b => Some b
    | VUnit | VInt _ | VOfst _ | VPtr _ => None
    end.

  Program Definition bool_storable :=
    {|
      obj := bool;
      encode := bool_encode;
      decode := bool_decode;
    |}.

  Next Obligation.
    reflexivity.
  Qed.

  Next Obligation.
    destruct v;
      cbn; intros o Hdecode; inversion Hdecode; subst; reflexivity.
  Qed.

End StorableBool.

Canonical StorableBool.bool_storable.

Module StorableUnit.

  Definition unit_encode (_: unit) := VUnit.
  Definition unit_decode (v: memval) :=
    match v with
    | VUnit => Some tt
    | VBool _ | VInt _ | VOfst _ | VPtr _ => None
    end.

  Program Definition unit_storable :=
    {|
      obj := unit;
      encode := unit_encode;
      decode := unit_decode;
    |}.

  Next Obligation.
    destruct o; reflexivity.
  Qed.

  Next Obligation.
    destruct v; destruct o; cbv; intro; congruence.
  Qed.

End StorableUnit.

Canonical StorableUnit.unit_storable.

Module StorableOfst.

  Definition ofst_encode := VOfst.
  Definition ofst_decode (v: memval) :=
    match v with
    | VOfst n => Some n
    | VUnit | VBool _ | VInt _ | VPtr _ => None
    end.

  Program Definition ofst_storable :=
    {|
      obj := N.t;
      encode := ofst_encode;
      decode := ofst_decode;
    |}.

  Next Obligation.
    reflexivity.
  Qed.

  Next Obligation.
    destruct v; cbv; congruence.
  Qed.
End StorableOfst.

Canonical StorableOfst.ofst_storable.
