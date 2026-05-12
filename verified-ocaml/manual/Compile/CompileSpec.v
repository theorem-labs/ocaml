(* CompileSpec.v - [TRUSTED] Module Type specifying what the compiler
   correctness proof must deliver. The compiler and source interpreter are
   declared as Parameters (provided by Untrusted code); the theorem states
   that compilation preserves observable behavior.

   Trust model: this file defines the CONCRETE correctness statement using
   only trusted components (step, initial_state, etc.). The untrusted code
   must provide compile_program and interpret that satisfy this statement.

   This file has NO dependencies outside manual/ — it is fully self-contained.
   The concrete compile_program and interpret are supplied by the checker
   module in checker/Compile/CompileChecker.v. *)

From Stdlib Require Import ZArith PeanoNat Strings.String.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Value.
From RecordUpdate Require Import RecordUpdate.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import Run HandleInstrSpec.
From OCamlInterp.Manual.Utils Require Import Observable.
From OCamlInterp.Manual.Utils Require Import Syntax.
Open Scope list_scope.

(* === Trusted definitions for running compiled bytecode === *)

(* Convert a C call to output events.
   Current Compile.v builtins map:
     0 = print_int, 1 = print_newline, 2 = print_string.
   The trusted observable mapping also reserves/requires:
     3 = print_char.
   print_string is intentionally still a no-op here because strings are
   stubbed end-to-end. Uses z_to_events from Observable.v as the single
   source of truth for print_int. *)
Definition ccall_to_events (prim_idx : nat) (args : list value) : list event :=
  match prim_idx, args with
  | 0%nat, [Val_int n] => z_to_events n
  | 1%nat, _ => [Out_char 10]
  | 3%nat, [Val_int c] => [Out_char c]
  | _, _ => []
  end.

(* List-based wrapper parameterized over a step function.
   The step function takes a code array and a state, returning a step_result.
   This allows run_collecting/bytecode_behavior to be used with any
   HandleInstrSpec instantiation. *)
Fixpoint run_collecting
    (step_fn : list instruction -> state -> step_result)
    (fuel : nat) (code : list instruction) (s : state)
    (out : list event) : behavior :=
  match fuel with
  | O => mk_behavior (rev out) Term_timeout
  | S fuel' =>
    match step_fn code s with
    | Step s' => run_collecting step_fn fuel' code s' out
    | Halt v => mk_behavior (rev out) (Term_normal v)
    | Error msg => mk_behavior (rev out) (Term_error msg)
    | CCall_request prim_idx args cont =>
      let new_events := ccall_to_events prim_idx args in
      let out' := rev new_events ++ out in
      run_collecting step_fn fuel' code (cont <|accu := Val_int 0|>) out'
    end
  end.

Definition bytecode_behavior
    (step_fn : list instruction -> state -> step_result)
    (fuel : nat) (code : list instruction)
    (globals : list value) : behavior :=
  run_collecting step_fn fuel code (initial_state globals) [].

(* === The Spec === *)

Definition behavior_equiv (b1 b2 : behavior) :=
  let t1 := b1.(trace)  in let t2 := b2.(trace)  in
  let r1 := b1.(result) in let r2 := b2.(result) in
  let n := Nat.min (List.length t1) (List.length t2) in
  List.firstn n t1 = List.firstn n t2
  /\
  match r1, r2 with
  | Term_timeout, _ | _, Term_timeout => True
  | Term_normal _, Term_normal _
  | Term_error _, Term_error _
     => List.length t1 = List.length t2
  | (Term_normal _ | Term_error _), _ => False
  end.

(* Build a list-based step function from a HandleInstrSpec instance.
   Uses fetch_instr and list_to_code_array from Run.v. *)
Definition step_list_of (handle_instr : instruction -> Z -> state -> step_result)
    (code : list instruction) (s : state) : step_result :=
  let code_arr := list_to_code_array code in
  match fetch_instr code_arr s.(pc) with
  | None => Error "pc out of bounds"
  | Some instr => handle_instr instr (s.(pc) + 1) s
  end.

Module Type CompileSpec (Import HI : HandleInstrSpec).

  (* The step function derived from this HandleInstrSpec instance *)
  Definition step_fn : list instruction -> state -> step_result :=
    step_list_of HI.handle_instr.

  (* Compiler (provided by Untrusted) *)
  Parameter compile_program : program -> list instruction.

  (* Source interpreter (provided by semi-auto, checked by Untrusted) *)
  Parameter interpret : nat -> program -> behavior.

  (* Correctness: the traces always match up to the end of the shortest
     trace; the interpreter terminates if and only if the compiled bytecode
     terminates, in which case the length of the traces match as well and
     the interpreter errors if and only if the compiled bytecode also
     errors. *)
  Axiom compiler_correctness :
    forall (prog : program) (src_fuel bc_fuel : nat),
      behavior_equiv (interpret src_fuel prog)
                     (bytecode_behavior step_fn bc_fuel (compile_program prog) []).

End CompileSpec.
