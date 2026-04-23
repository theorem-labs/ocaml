(* Machine.v - [TRUSTED] ZINC machine state definition. *)

From Stdlib Require Import ZArith Strings.String.
From Stdlib Require Import List. Import ListNotations.
From Stdlib.FSets Require Import FMapPositive.
From Stdlib.PArith Require Import BinPosDef.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST.
From RecordUpdate Require Import RecordUpdate.

(* Heap: maps addresses (nat) to (tag, fields) pairs.
   Uses PositiveMap for O(log n) lookup instead of O(n) linear scan.
   Keys are Pos.of_succ_nat addr, mapping nat 0→1, 1→2, etc. *)
Definition heap := PositiveMap.t (nat * list value).

(* Machine state.
   trap_sp : nat — stack depth (length of stack) at the time the current
   outermost active PUSHTRAP pushed its trap frame.  Zero means no handler.
   The trap frame lives on the main stack at positions
     (length stack - trap_sp) .. (length stack - trap_sp + 3)
   from the top. *)
Record state : Type := mk_state {
  pc         : Z;
  accu       : value;
  stack      : list value;
  env        : value;
  extra_args : nat;
  global     : list value;
  trap_sp    : nat;            (* trap-stack pointer: stack depth at last PUSHTRAP *)
  hp         : heap;           (* mutable heap *)
  next_addr  : nat;            (* next free heap address *)
}.

#[export] Instance eta_state : Settable state :=
  settable! mk_state <pc; accu; stack; env; extra_args; global; trap_sp; hp; next_addr>.

Inductive step_result_gen (S : Type) : Type :=
  | Step      : S -> step_result_gen S
  | Halt      : value -> step_result_gen S
  | Error     : string -> step_result_gen S
  | CCall_request : nat -> list value -> S -> step_result_gen S.

Arguments step_result_gen : clear implicits.
Arguments Step {S}.
Arguments Halt {S}.
Arguments Error {S}.
Arguments CCall_request {S}.

Definition step_result := step_result_gen state.

Inductive run_result : Type :=
  | Finished    : value -> run_result
  | Run_error   : string -> run_result
  | Out_of_fuel : state -> run_result.

(* Heap operations *)
Definition heap_lookup (h : heap) (addr : nat) : option (nat * list value) :=
  PositiveMap.find (Pos.of_succ_nat addr) h.

Definition heap_alloc (s : state) (tag : nat) (fields : list value) : state * value :=
  let addr := s.(next_addr) in
  let h' := PositiveMap.add (Pos.of_succ_nat addr) (tag, fields) s.(hp) in
  (s <|hp := h'|> <|next_addr := S addr|>, Val_ptr addr).

Definition heap_update (h : heap) (addr : nat) (fields : list value) : heap :=
  match PositiveMap.find (Pos.of_succ_nat addr) h with
  | Some (tag, _) => PositiveMap.add (Pos.of_succ_nat addr) (tag, fields) h
  | None => h
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

(* Micro monad for bytecode computations.
   Inspired by the Osiris micro monad (Seassau et al. 2025).
   Simplified: no exceptions, handlers, parallelism, or effects —
   just return, error, fuel exhaustion, and C-call requests. *)
Inductive bcmicro : Type :=
  | MRet  : value -> bcmicro
  | MErr  : string -> bcmicro
  | MFuel : state -> bcmicro
  | MVis  : nat -> list value -> (option value -> bcmicro) -> bcmicro.

Definition initial_state (global_data : list value) : state :=
  mk_state 0%Z val_unit [] val_unit 0 global_data 0 (PositiveMap.empty _) 0.
