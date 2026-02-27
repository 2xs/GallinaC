From Stdlib Require Import List NArith Arith.
From Utils Require Import Algebra.
From Imp Require Import Monad Heap Pointer Store Memval While.
Import Heap.Facts.

Local Open Scope separation_scope.
Local Open Scope program_scope.

Structure State (St: Store) (Hp: Heap) : Type :=
  mkState
    {
      store: St;
      heap: Hp;
    }.

Arguments mkState {_ _} _ _.
Arguments store {_ _} _.
Arguments heap {_ _} _.

Definition emp {St: Store} {Hp: Heap}: State St Hp :=
  {| store := Store.emp; heap := $0; |}.

Definition with_var {A} {St: Store} {Hp: Heap} {MS: MemStorable} (e_var: obj MS) (p_cont: name -> program (State _ _) A): program (State St Hp) A :=
  do s <- get;
  let (st, n) := push s.(store) (encode e_var) in
  put {| store := st; heap := s.(heap); |};;
  do v <- p_cont n;
  do s <- get;
  match pop s.(store) with
  | Some st =>
      put {| store := st; heap := s.(heap); |};;
      ret v
  | None => fail
  end.

Notation "'do' 'var' x <- m1 ; m2" := (@with_var _ _ _ _ m1 (fun x => m2))
                                  (at level 100, x name, m1 at level 90, m2 at level 100):
    program_scope.

Notation "'do' 'var' ( x : t )  <- m1 ; m2" := (@with_var _ _ _ _ (m1: t) (fun x => m2))
                                       (at level 100, x name, m1 at level 90, m2 at level 100):
    program_scope.

Definition read_var {St: Store} {Hp: Heap} {MS: MemStorable} varname: program (State St Hp) (obj MS) :=
  do s <- get;
  match Store.lookup s.(store) varname with
  | Some val =>
      match decode val with
      | Some v => ret v
      | None => fail
      end
  | None => fail
  end.

Definition write_var {St: Store} {Hp: Heap} {MS: MemStorable} varname (val: obj MS) : program (State St Hp) unit :=
  do s <- get;
  match Store.mutate s.(store) varname (encode val) with
  | Some st =>
      put {|
          store := st;
          heap := s.(heap);
        |}
  | None => fail
  end.

Definition read_ptr {St: Store} {Hp: Heap} {MS: MemStorable} (p : Pointer.t) : program (State St Hp) (obj MS) :=
  do s <- get;
  match (Heap.lookup s.(heap) p) with
  | Some val =>
      match decode val with
      | Some v => ret v
      | None => fail
      end
  | None => fail
  end.

Definition write_ptr {St: Store} {Hp: Heap} {MS: MemStorable} (p: Pointer.t) (val: obj MS)  : program (State St Hp) unit :=
  do s <- get;
  match Heap.mutate s.(heap) p (encode val) with
  | Some h => put {|
                  store := s.(store);
                  heap := h;
                |}
  | None => fail
  end.

Definition alloc_ptr {St: Store} {Hp: Heap} {MS: MemStorable} (n: N.t) (val: obj MS): program (State St Hp) Pointer.t :=
  do s <- get;
  match Heap.alloc s.(heap) n (encode val) with
  | Some (hp, ptr) => put {| store := s.(store); heap := hp |};;
                      ret ptr
  | None => fail
  end.
Arguments alloc_ptr {St Hp MS} n%_N_scope val.

Definition free_ptr {St: Store} {Hp: Heap} (p: Pointer.t): program (State St Hp) unit :=
  do s <- get;
  match Heap.free s.(heap) p with
  | Some h => put {| store := s.(store); heap := h; |}
  | None => fail
  end.

Definition shift_fw_ptr {St: Store} {Hp: Heap} (ptr: Pointer.t) (shift: N.t): program (State St Hp) Pointer.t :=
  do s <- get;
  match weakly_valid s.(heap) ptr, Pointer.shift_fw ptr shift with
  | true, Some p =>
      match weakly_valid s.(heap) p with
      | true => ret p
      | false => fail
      end
  | false,_ | _, None => fail
  end.
Arguments shift_fw_ptr {St Hp} ptr shift%_N_scope.
Notation "ptr ~+> shift" := (@shift_fw_ptr _ _ ptr shift) (at level 50, left associativity): program_scope.

Definition shift_bw_ptr {St: Store} {Hp: Heap} (ptr: Pointer.t) (shift: N.t): program (State St Hp) Pointer.t :=
  do s <- get;
  match weakly_valid s.(heap) ptr, Pointer.shift_bw ptr shift with
  | true, Some p =>
      match weakly_valid s.(heap) p with
      | true => ret p
      | false => fail
      end
  | false,_ | _, None => fail
  end.
Arguments shift_bw_ptr {St Hp} ptr shift%_N_scope.
Notation "ptr ~-> shift" := (@shift_bw_ptr _ _ ptr shift) (at level 50, left associativity): program_scope.

Definition eq_ptr {St: Store} {Hp: Heap} (ptr_l: Pointer.t) (ptr_r: Pointer.t): program (State St Hp) bool :=
  do s <- get;
  match weakly_valid s.(heap) ptr_l, weakly_valid s.(heap) ptr_r,
    Pointer.allows ptr_l Operation.Cmp, Pointer.allows ptr_r Operation.Cmp,
    Pointer.cmp ptr_l ptr_r with
  | true, true, true, true, Some b => ret b
  | _, _, _, _, _ => fail
  end.

Definition while {S: Type} := @While.while S.

(* Notation "{ m }" := (m: program _ _): program_scope. *)
