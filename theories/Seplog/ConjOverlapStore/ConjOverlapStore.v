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

From GallinaC.Imp Require Import State.
From GallinaC.Seplog Require Import Pred.

Local Open Scope separation_scope.

Section ConjOverlapStore.

  Context [Sm: State.type].

  Definition conj_overlap_store (P Q: Pred Sm): Pred Sm :=
    fun s => exists s1 s2,
        store s1 = store s /\ store s2 = store s
        /\ scnt s1 $+ scnt s2 = Some (scnt s)
        /\ heap s1 $+ heap s2 = Some (heap s)
        /\ alc  s1 $+ alc  s2 = Some (alc s)
        /\ P s1 /\ Q s2.

  Local Infix "*&s" := conj_overlap_store (at level 40, left associativity): separation_scope.

  #[global] Instance conj_overlap_store_proper:
    Proper (pointwise_relation Sm iff ==> pointwise_relation Sm iff ==> pointwise_relation Sm iff) conj_overlap_store.
  Proof using Type.
    move=> P P' EQP R R' EQR s.
    by split=> -[ sp [ sr [ EQstp [ EQstr [ EQsg [ EQhp [ EQalc [ /EQP Psp /EQR Rsr ] ] ] ] ] ] ] ];
      exists sp, sr.
  Qed.

  #[global] Instance conj_overlap_store_proper_app:
    Proper (pointwise_relation Sm iff ==> pointwise_relation Sm iff ==> eq ==> iff) conj_overlap_store.
  Proof using Type.
    move=> P P' EQP R R' EQR s _ <-.
    exact: conj_overlap_store_proper P P' EQP R R' EQR s.
  Qed.

  #[global] Instance conj_overlap_store_mono_proper:
    Proper (pointwise_relation Sm Basics.impl ==> pointwise_relation Sm Basics.impl ==> pointwise_relation Sm Basics.impl) conj_overlap_store.
  Proof using Type.
    move=> P P' IMPP R R' IMPR s
      [ sp [ sr [ EQstp [ EQstr [ EQsg [ EQhp [ EQalc [ /IMPP Psp /IMPR Rsr ] ] ] ] ] ] ] ].
    by exists sp, sr.
  Qed.

  #[global] Instance conj_overlap_store_mono_proper_app:
    Proper (pointwise_relation Sm Basics.impl ==> pointwise_relation Sm Basics.impl ==> eq ==> Basics.impl) conj_overlap_store.
  Proof using Type.
    move=> P P' IMPP R R' IMPR s _ <-.
    exact: conj_overlap_store_mono_proper P P' IMPP R R' IMPR s.
  Qed.

End ConjOverlapStore.

Arguments conj_overlap_store_proper {Sm}.
Arguments conj_overlap_store_proper_app {Sm}.
Arguments conj_overlap_store_mono_proper {Sm}.
Arguments conj_overlap_store_mono_proper_app {Sm}.

Infix "*&s" := conj_overlap_store (at level 40, left associativity): separation_scope.
