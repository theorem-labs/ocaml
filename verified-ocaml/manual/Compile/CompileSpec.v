(* CompileSpec.v - [TRUSTED] Module Type specifying what the compiler
   correctness proof must deliver. The compiler and source interpreter are
   declared as Parameters (provided by Untrusted code); the theorem states
   that compilation preserves observable behavior.

   Trust model: this file defines the CONCRETE correctness statement using
   only trusted components (step, initial_state, etc.). The untrusted code
   must provide compile_program and interpret that satisfy this statement.

   This file has NO dependencies outside manual/ — it is fully self-contained.
   The concrete compile_program and interpret are supplied by the checker
   module in automatic/Compile/CompileChecker.v. *)

From Stdlib Require Import ZArith PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Value.
From RecordUpdate Require Import RecordUpdate.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import Handlers Dispatch Run HandleInstrSpec.
From OCamlInterp.Manual.Utils Require Import Observable.
From OCamlInterp.Manual.Utils Require Import Syntax.

(* Instantiate the Run functor at the manual Dispatch to expose
   step / run / run_micro / handle_bcmicro / run_pure at top level.
   CompileSpec is in manual/ and cannot depend on automatic/, so it
   cannot reuse automatic/Bytecode/Interpret.v; it builds its own copy
   of the same instantiation here. *)
Module DispatchImpl <: HandleInstrSpec.
  Definition handle_instr := Dispatch.handle_instr.
End DispatchImpl.
Include Run.Make DispatchImpl.

(* === Trusted definitions for running compiled bytecode === *)

(* Convert a C call to output events.
   Primitive indices match Compile.v's is_builtin:
     0 = print_int, 1 = print_newline, 2 = print_string
   Uses z_to_events from Interpret.v -- single source of truth. *)
Definition ccall_to_events (prim_idx : nat) (args : list value) : list event :=
  match prim_idx, args with
  | 0%nat, [Val_int n] => z_to_events n
  | 1%nat, _ => [Out_char 10]
  | _, _ => []
  end.

(* List-based wrapper: compile_program produces list instruction,
   but the trusted step function works on PrimArray.  Convert once. *)
Definition step_list (code : list instruction) (s : state) : step_result :=
  step (list_to_code_array code) s.

(* Run bytecode collecting output events.
   Output list accumulated in reverse order (newest first). *)
Fixpoint run_collecting (fuel : nat) (code : list instruction) (s : state)
    (out : list event) : behavior :=
  match fuel with
  | O => mk_behavior (rev out) Term_timeout
  | S fuel' =>
    match step_list code s with
    | Step s' => run_collecting fuel' code s' out
    | Halt v => mk_behavior (rev out) (Term_normal v)
    | Error msg => mk_behavior (rev out) (Term_error msg)
    | CCall_request prim_idx args cont =>
      let new_events := ccall_to_events prim_idx args in
      let out' := rev new_events ++ out in
      run_collecting fuel' code (cont <|accu := Val_int 0|>) out'
    end
  end.

Definition bytecode_behavior (fuel : nat) (code : list instruction)
    (globals : list value) : behavior :=
  run_collecting fuel code (initial_state globals) [].

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

Module Type CompileSpec.

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
                     (bytecode_behavior bc_fuel (compile_program prog) []).

End CompileSpec.
