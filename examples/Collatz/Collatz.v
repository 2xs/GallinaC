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

From GallinaC Require Import Programming.

(* Computation of the Collatz series length starting from 17.
 * Should yield 12 (17 52 26 13 40 20 10 5 16 8 4 2 1).
 * *)

Module Collatz.

  Section Collatz.

    Context {Sm: State.type}.

    Definition main: program Sm nat :=
      do var n <- 17%nat;
      do var len <- 0%nat;
      while (do (x : nat) <- read_var n; ret (negb (x =? 1)))
        (
          do (x: nat) <- read_var n;
          (do (old_len: nat) <- read_var len; write_var len (1 + old_len));;
          do even <-
               do b <- x % 2;
               ret (b =? 0);
          if even
          then
            do x <- x / 2;
            write_var n x
          else
            write_var n (3*x+1));;
      do len <- read_var len;
      ret len.

  End Collatz.

End Collatz.
