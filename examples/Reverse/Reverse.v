From GallinaC Require Import Programming.

(* print_ll ist not implemented as it performs only I/O *)
(* Instead, it is stubbed and will be excluded from extraction *)
Definition print_ll (ptr : Pointer.t) : program (State ListStore list_heap_carrier) unit :=
  ret tt.

Module Reverse.

  Definition allocate : program (State ListStore list_heap_carrier) Pointer.t :=
    do last <- alloc_ptr 2 Pointer.NULL;
    write_ptr last 3;;
    do middle <- Primitives.alloc_ptr 2 Pointer.NULL;
    write_ptr middle 2;;
    do ptr_shift <- shift_fw_ptr middle 1;
    write_ptr ptr_shift last;;
    do first <- Primitives.alloc_ptr 2 Pointer.NULL;
    write_ptr first 1;;
    do ptr_shift <- shift_fw_ptr first 1;
    write_ptr ptr_shift middle;;
    ret first.

  Definition reverse (ptr: Pointer.t) (n_ofst: N.t): program (State ListStore list_heap_carrier) Pointer.t :=
    do var (node: Pointer.t) <- ptr;
    do var (new_next: Pointer.t) <- Pointer.NULL;
    write_var node ptr;;
    while (do curr <- read_var node; do c <- eq_ptr curr Pointer.NULL; ret (negb c))
      (
        do (nd: Pointer.t) <- read_var node ;
        do node_next_ptr <- nd ~+> n_ofst ;
        do (old_next: Pointer.t) <- read_ptr node_next_ptr ;
        do (new_next_v : Pointer.t) <- read_var new_next ;
        write_ptr node_next_ptr new_next_v ;;
        write_var new_next nd ;;
        write_var node old_next
      );;
    read_var new_next.

  Definition main: program _ nat :=
    do ptr <- allocate;
    print_ll ptr;;
    do ptr <- reverse ptr 1%N;
    print_ll ptr;;
    ret 0.

End Reverse.
