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

From GallinaC.Utils Require Import ListExt.
From GallinaC.Imp Require Import Store State.
From GallinaC.Seplog Require Import Pred.

Local Open Scope separation_scope.
Local Open Scope mem_scope.

Section Indep.

  Context [Sm: State.type].
  Local Notation Nm := (@var_name Sm).
  Local Notation St := (@m_st Sm).

  Definition indep_store (P: Pred Sm) : Prop :=
    forall s1 s2, heap s1 = heap s2 -> alc s1 = alc s2 -> P s1 -> P s2.

  Definition indep_cnt (P: Pred Sm) : Prop :=
    forall s1 s2, store s1 = store s2 -> heap s1 = heap s2 -> alc s1 = alc s2 -> P s1 -> P s2.

  Lemma indep_cnt_of_indep_store (P: Pred Sm) (INDEP: indep_store P): indep_cnt P.
  Proof using Type. by move=> s1 s2 _ EQhp2 EQalc2 Ps1; exact: (INDEP s1 s2 EQhp2 EQalc2 Ps1). Qed.

  (* Only the variables in nms are guaranteed equal in stores st1 and st2 *)
  Definition store_partial_equal (st1 st2: St) (nms: list Nm): Prop :=
    forall nm v, List.In nm nms -> (nm |~> v @ st1 <-> nm |~> v @ st2).

  (* If P is true for a state, then replacing the store by a partially equal one doesn't invalidate P *)
  Definition indep_store_replace (P: Pred Sm) (nms: list Nm) :=
    forall s1 s2, P s1 -> store_partial_equal (store s1) (store s2) nms ->
                  scnt s2 = scnt s1 -> heap s2 = heap s1 -> alc s2 = alc s1 -> P s2.

  Lemma indep_store_replace_incl (P: Pred Sm) (nms nms': list Nm)
    (SUB: List.incl nms nms') (INDEP: indep_store_replace P nms)
    : indep_store_replace P nms'.
  Proof using Type.
    move=> s1 s2 Ps1 SPE EQsg2 EQhp2 EQalc2.
    apply: (INDEP s1 s2 Ps1) => // nm v INnm; exact: (SPE nm v (SUB nm INnm)).
  Qed.

  Lemma indep_store_replace_of_indep_store (P: Pred Sm) (INDEP: indep_store P):
    indep_store_replace P [].
  Proof using Type.
    by move=> s1 s2 Ps1 _ _ EQhp2 EQalc2; apply: (INDEP s1 s2 _ _ Ps1).
  Qed.

  Definition indep_heap (P: Pred Sm) : Prop :=
    forall s1 s2, store s1 = store s2 -> scnt s1 = scnt s2 -> P s1 -> P s2.

End Indep.

#[global] Hint Resolve indep_cnt_of_indep_store : seplog.
#[global] Hint Resolve indep_store_replace_incl
  indep_store_replace_of_indep_store : seplog_search.
