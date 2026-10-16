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

(* print_ll is not implemented as it performs only I/O *)
(* Instead, it is stubbed and will be excluded from extraction *)
Definition print_ll {Sm: State.type} (ptr: @ptr_t Sm): program Sm unit :=
  ret tt.

Module Reverse.

  Section Reverse.

    Context {Sm: State.type}.
    Local Notation Ad := (@m_ad Sm).
    Local Notation Nm := (@var_name Sm).
    Local Notation Pt := (@ptr_t Sm).
    Local Notation Vl := (value (@ptr_t Sm)).
    Local Notation St := (@m_st Sm).
    Local Notation Hp := (@m_hp Sm).

    Definition allocate: program Sm Pt :=
      do (last: Pt) <- alloc_ptr 2 null;
      write_ptr last 3;;
      do (middle: Pt) <- Primitives.alloc_ptr 2 null;
      write_ptr middle 2;;
      do (ptr_shift: Pt) <- shift_fw_ptr middle 1;
      write_ptr ptr_shift last;;
      do (first: Pt) <- Primitives.alloc_ptr 2 null;
      write_ptr first 1;;
      do (ptr_shift: Pt) <- shift_fw_ptr first 1;
      write_ptr ptr_shift middle;;
      ret first.

    Definition reverse (ptr: Pt) (n_ofst: N.t): program Sm Pt :=
      do var (node: Pt) <- ptr;
      do var (new_next: Pt) <- null;
      write_var node ptr;;
      while (do (curr: Pt) <- read_var node; do c <- eq_ptr curr null; ret (negb c))
        (
          do (nd: Pt) <- read_var node ;
          do (node_next_ptr: Pt) <- nd ~+> n_ofst ;
          do (old_next: Pt) <- read_ptr node_next_ptr ;
          do (new_next_v : Pt) <- read_var new_next ;
          write_ptr node_next_ptr new_next_v ;;
          write_var new_next nd ;;
          write_var node old_next
        );;
      read_var new_next.

    Definition main: program Sm nat :=
      do ptr <- allocate;
      print_ll ptr;;
      do ptr <- reverse ptr 1%N;
      print_ll ptr;;
      ret 0.

  End Reverse.

End Reverse.
