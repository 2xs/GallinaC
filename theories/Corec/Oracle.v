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

From Stdlib Require Import Classical IndefiniteDescription.

Lemma cases{A B:Prop}: A \/ B ->  {A} + {B}.
Proof.
  intro Hor.
  assert (Hex :
           let AB := fun (b : bool) =>
                       match b with true => A | false => B end in
           exists b,  AB b);
    [destruct Hor as [HP | HnP]; [   now exists true |   now exists false]|] .
  apply constructive_indefinite_description in Hex.
  destruct Hex as (x & Hex).
  destruct x ; [ now left | now right].
Qed.

Lemma oracle : forall (p:Prop), {p} + {~p}.
Proof.
  intro p.
  assert(Hor := classic p).
  now apply cases.
Qed.
