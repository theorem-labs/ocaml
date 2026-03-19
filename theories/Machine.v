(* Machine.v - [TRUSTED] ZINC machine state definition. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp Require Import Value Bytecode.
Import ListNotations.

Record trap_frame : Type := mk_trap_frame {
  trap_pc         : Z;
  trap_sp_offset  : nat;
  trap_env        : value;
  trap_extra_args : nat;
}.

Record state : Type := mk_state {
  pc         : Z;
  accu       : value;
  stack      : list value;
  env        : value;
  extra_args : nat;
  global     : list value;
  trap_stack : list trap_frame;
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

Definition set_pc (s : state) (v : Z) : state :=
  mk_state v s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack).

Definition set_accu (s : state) (v : value) : state :=
  mk_state s.(pc) v s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack).

Definition set_stack (s : state) (v : list value) : state :=
  mk_state s.(pc) s.(accu) v s.(env) s.(extra_args) s.(global) s.(trap_stack).

Definition set_env (s : state) (v : value) : state :=
  mk_state s.(pc) s.(accu) s.(stack) v s.(extra_args) s.(global) s.(trap_stack).

Definition set_extra_args (s : state) (v : nat) : state :=
  mk_state s.(pc) s.(accu) s.(stack) s.(env) v s.(global) s.(trap_stack).

Definition set_global (s : state) (v : list value) : state :=
  mk_state s.(pc) s.(accu) s.(stack) s.(env) s.(extra_args) v s.(trap_stack).

Definition set_trap_stack (s : state) (v : list trap_frame) : state :=
  mk_state s.(pc) s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) v.

Definition advance_pc (s : state) : state :=
  set_pc s (s.(pc) + 1)%Z.

Definition push_stack (s : state) (v : value) : state :=
  set_stack s (v :: s.(stack)).

Definition pop_stack (s : state) (n : nat) : state :=
  set_stack s (skipn n s.(stack)).

Definition stack_nth (s : state) (n : nat) : option value :=
  nth_error s.(stack) n.

Definition initial_state (global_data : list value) : state :=
  mk_state 0%Z val_unit [] val_unit 0 global_data [].
