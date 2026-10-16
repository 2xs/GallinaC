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

From Stdlib Require Export ZArith Psatz.

Local Open Scope Z_scope.

Lemma interval_split:
  forall (P: _ -> Prop) lo mid hi,
    (lo <= mid < hi)%Z ->
    (forall z, (lo <= z < mid)%Z -> P z) ->
    (forall z, (mid <= z < hi)%Z -> P z) ->
    forall z, (lo <= z < hi) -> P z.
Proof.
  intros P lo mid hi [ Hloltmid Hmidlthi ] Hfirst Hsecond z [ Hlolez Hzlthi ].
  destruct (Z.lt_trichotomy z mid) as [ Hlt | [ Heq | Hgt ] ];
    subst.
  - now apply Hfirst.
  - now apply Hsecond.
  - apply Hsecond.
    lia.
Qed.
