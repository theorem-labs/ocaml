(* Machine.v - [TRUSTED] ZINC machine state definition. *)

From Stdlib Require Import ZArith Strings.String.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST.

Record trap_frame : Type := mk_trap_frame {
  trap_pc         : Z;
  trap_sp_offset  : nat;
  trap_env        : value;
  trap_extra_args : nat;
}.

(* Heap: maps addresses (nat) to (tag, fields) pairs.
   Used for mutable blocks (refs, arrays). Closures and immutable
   blocks remain as inline Val_block values. *)
Definition heap := list (nat * (nat * list value)).  (* addr -> (tag, fields) *)

Record state : Type := mk_state {
  pc         : Z;
  accu       : value;
  stack      : list value;
  env        : value;
  extra_args : nat;
  global     : list value;
  trap_stack : list trap_frame;
  hp         : heap;           (* mutable heap *)
  next_addr  : nat;            (* next free heap address *)
}.

Inductive step_result : Type :=
  | Step      : state -> step_result
  | Halt      : value -> step_result
  | Error     : string -> step_result
  | CCall_request : nat -> list value -> state -> step_result.

Inductive run_result : Type :=
  | Finished    : value -> run_result
  | Run_error   : string -> run_result
  | Out_of_fuel : state -> run_result.

Definition set_accu (s : state) (v : value) : state :=
  mk_state s.(pc) v s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack) s.(hp) s.(next_addr).

(* Heap operations *)
Fixpoint heap_lookup (h : heap) (addr : nat) : option (nat * list value) :=
  match h with
  | [] => None
  | (a, (t, fs)) :: rest =>
    if Nat.eqb a addr then Some (t, fs) else heap_lookup rest addr
  end.

Definition heap_alloc (s : state) (tag : nat) (fields : list value) : state * value :=
  let addr := s.(next_addr) in
  let s' := mk_state s.(pc) s.(accu) s.(stack) s.(env) s.(extra_args) s.(global)
              s.(trap_stack) ((addr, (tag, fields)) :: s.(hp)) (S addr) in
  (s', Val_ptr addr).

Fixpoint heap_update (h : heap) (addr : nat) (fields : list value) : heap :=
  match h with
  | [] => []
  | (a, (t, fs)) :: rest =>
    if Nat.eqb a addr then (a, (t, fields)) :: rest
    else (a, (t, fs)) :: heap_update rest addr fields
  end.

(* Get field from either inline block or heap pointer *)
Definition field_or_heap (s : state) (v : value) (n : nat) : option value :=
  match v with
  | Val_block _ fields => nth_error fields n
  | Val_ptr addr =>
    match heap_lookup s.(hp) addr with
    | Some (_, fields) => nth_error fields n
    | None => None
    end
  | Val_closure addr ofs =>
    match heap_lookup s.(hp) addr with
    | Some (_, fields) => nth_error fields (ofs + n)
    | None => None
    end
  | _ => None
  end.

(* Get tag from either inline block or heap pointer *)
Definition tag_or_heap (s : state) (v : value) : option nat :=
  match v with
  | Val_block t _ => Some t
  | Val_ptr addr | Val_closure addr _ =>
    match heap_lookup s.(hp) addr with
    | Some (t, _) => Some t
    | None => None
    end
  | _ => None
  end.

(* Get block size from either inline block or heap pointer *)
Definition size_or_heap (s : state) (v : value) : option nat :=
  match v with
  | Val_block _ fields => Some (length fields)
  | Val_ptr addr =>
    match heap_lookup s.(hp) addr with
    | Some (_, fields) => Some (length fields)
    | None => None
    end
  | _ => None
  end.

Definition initial_state (global_data : list value) : state :=
  mk_state 0%Z val_unit [] val_unit 0 global_data [] [] 0.
