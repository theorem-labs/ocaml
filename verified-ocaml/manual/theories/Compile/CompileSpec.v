(* CompileSpec.v - [TRUSTED] Module Type specifying what the compiler
   correctness proof must deliver. The compiler and source interpreter are
   declared as Parameters (provided by Untrusted code); the theorem states
   that compilation preserves observable behavior.

   Trust model: this file defines the CONCRETE correctness statement using
   only trusted components (step, initial_state, etc.). The untrusted code
   must provide compile_program and interpret that satisfy this statement.
   The correctness predicate is NOT a Parameter -- it is fully spelled out
   here so it cannot be trivialized. *)

From Stdlib Require Import ZArith PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode Require Import Interpret.
From OCamlInterp.Manual.Utils Require Import Observable.
From OCamlInterp.Manual.Utils Require Import Syntax.
From OCamlInterp.SemiAutomatic.Interpret Require Import Interpret.

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
      run_collecting fuel' code (set_accu cont (Val_int 0)) out'
    end
  end.

Definition bytecode_behavior (fuel : nat) (code : list instruction)
    (globals : list value) : behavior :=
  run_collecting fuel code (initial_state globals) [].

(* === The Spec === *)

Module Type CompileSpec.

  (* Compiler and source interpreter (provided by Untrusted) *)
  Parameter compile_program : program -> list instruction.

  (* Correctness: if the source interpreter terminates normally with some
     output trace, then there exists enough bytecode fuel such that the
     compiled code also terminates normally with the same trace.

     The statement is FULLY CONCRETE -- only compile_program is opaque.
     The source interpreter (interpret) is imported directly from its
     module, not parameterized, so it cannot be trivialized. *)
  Axiom compiler_correctness :
    forall (prog : program) (src_fuel : nat),
      match interpret src_fuel prog with
      | {| trace := src_trace; result := Term_normal _ |} =>
        exists (bc_fuel : nat),
          let bc := bytecode_behavior bc_fuel (compile_program prog) [] in
          bc.(trace) = src_trace /\
          match bc.(result) with
          | Term_normal _ => True
          | _ => False
          end
      | _ => True
      end.

End CompileSpec.

(* Check that the untrusted proof satisfies the spec *)
From OCamlInterp.Automatic.Compile Require Import Compile.
From OCamlInterp.Automatic.Compile Require Import CompileProof.

Module Check <: CompileSpec.
  Definition compile_program := compile_program.
  Definition compiler_correctness := compiler_correctness.
End Check.
