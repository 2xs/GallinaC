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

(** * Storable

Encoding/decoding types to and from memory words.

A type [T] implementing [isStorable MW T] is encodable to and from the memory word type [MW]
 *)

HB.mixin Record isStorable (MW: Type) T :=
  {
    encode: T -> MW;
    decode: MW -> option T;

    encode_decode: forall x, decode (encode x) = Some x;
    decode_encode: forall v x, decode v = Some x -> encode x = v;
  }.
HB.structure Definition Storable (MW: Type) := { T of isStorable MW T }.

Lemma encode_inj [MW: Type] [So: Storable.type MW] (x y: So)
  (EQ: encode x = encode y)
  : x = y.
Proof.
  have H := encode_decode x.
  rewrite EQ encode_decode in H.
  by move: H => [->].
Qed.
#[global] Hint Resolve encode_inj | 10 : seplog.

