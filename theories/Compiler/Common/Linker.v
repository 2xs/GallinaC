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

From compcert.common Require Import Linking.

From GallinaC.Compiler.Common Require Import Types Prog.

Local Obligation Tactic := cbn.

Global Program Instance Linker_type : Linker type := {
  link := fun t1 t2 => if type_eqb t1 t2 then Some t1 else None;
  linkorder := eq
}.
Next Obligation.
  reflexivity.
Defined.

Next Obligation.
  congruence.
Defined.

Next Obligation.
  intros x y z.
  destruct (type_eqb_spec x y); [ subst | discriminate ].
  intros EQ. split; congruence.
Defined.

Lemma link_type_eq: forall (t1 t2 t: type), link t1 t2 = Some t -> t1 = t /\ t2 = t.
Proof.
  unfold link; cbn.
  intros t1 t2 t EQ.
  destruct (type_eqb_spec t1 t2); [ | discriminate ].
  split; congruence.
Qed.

Lemma linkorder_type_eq: forall (t1 t2: type), linkorder t1 t2 -> t1 = t2.
Proof.
  auto.
Qed.
Global Opaque Linker_type.

Definition link_vardef (v1 v2: vardef) :=
  match link v1.(var_type) v2.(var_type) with
  | Some vtype => Some (mkvardef vtype)
  | None => None
  end.

Global Program Instance Linker_vardef: Linker vardef :=
  {
    link := link_vardef;
    linkorder := eq;
  }.
Next Obligation.
  auto.
Defined.

Next Obligation.
  intros; congruence.
Defined.

Next Obligation.
  unfold link_vardef.
  intros x y z EQ.
  destruct (link (var_type _) _) eqn:Evtype; [ | discriminate ].
  apply link_linkorder in Evtype.
  destruct Evtype as [ LOTYPEx LOTYPEy ].
  apply linkorder_type_eq in LOTYPEx;
    apply linkorder_type_eq in LOTYPEy.
  destruct x, y, z; cbn in *; split; congruence.
Defined.

Lemma link_vardef_eq (v1 v2 v: vardef): link v1 v2 = Some v -> v1 = v /\ v2 = v.
Proof.
  unfold link; cbn; unfold link_vardef.
  intros EQ.
  destruct (link _ _) eqn:Evtype; [ | discriminate ].
  apply link_type_eq in Evtype.
  destruct Evtype as [ V1T V2T ].
  destruct v1, v2; split; cbn in *; congruence.
Qed.

Lemma linkorder_vardef_eq (v1 v2: vardef): linkorder v1 v2 -> v1 = v2.
Proof.
  auto.
Qed.

Global Opaque Linker_vardef.

Lemma link_match_varinfo_eq (v1 tv1 v2 tv2 v: vardef)
  (LINK: link v1 v2 = Some v) (MV1: v1 = tv1) (MV2: v2 = tv2)
  : exists tv, link tv1 tv2 = Some tv /\ v = tv.
Proof.
  subst tv1 tv2.
  exists v; split; [ exact LINK | reflexivity ].
Qed.
