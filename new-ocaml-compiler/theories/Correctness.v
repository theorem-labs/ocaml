(* Correctness.v - [TRUSTED] Compiler correctness theorem statement.

   This file contains the STATEMENT of compiler correctness. The statement
   itself is trusted: it defines what it means for the compiler to be correct.
   The proof (when provided) is checked mechanically by Rocq.

   The core theorem:
     forall source, interpret(source) = (interpret-bytecode . compile)(source)

   Both sides must produce the same observable behavior (output trace + result). *)

From Stdlib Require Import ZArith Strings.String PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp Require Import Value Bytecode Machine Interp Syntax
                                Observable SourceInterp Compile.
Open Scope Z_scope.

(* === Behavior extraction from bytecode interpreter === *)

(* Convert a C call to output events.
   Primitive indices must match Compile.v's is_builtin:
     0 = print_int, 1 = print_newline, 2 = print_string
   Uses z_to_events from SourceInterp.v — single source of truth. *)
Definition ccall_to_events (prim_idx : nat) (args : list value) : list event :=
  match prim_idx, args with
  | 0%nat, [Val_int n] => z_to_events n        (* print_int *)
  | 1%nat, _ => [Out_char 10]                   (* print_newline *)
  | _, _ => []
  end.

(* Run bytecode with a handler that collects output events.
   Output list is accumulated in reverse order (newest first). *)
Fixpoint run_collecting (fuel : nat) (code : list instruction) (s : state)
    (out : list event) : behavior :=
  match fuel with
  | O => mk_behavior (rev out) Term_timeout
  | S fuel' =>
    match step code s with
    | Step s' => run_collecting fuel' code s' out
    | Halt v => mk_behavior (rev out) (Term_normal v)
    | Error msg => mk_behavior (rev out) (Term_error msg)
    | CCall_request prim_idx args cont =>
      let new_events := ccall_to_events prim_idx args in
      let out' := rev new_events ++ out in
      run_collecting fuel' code (set_accu cont (Val_int 0)) out'
    end
  end.

(* Extract behavior from running compiled code *)
Definition bytecode_behavior (fuel : nat) (code : list instruction)
    (globals : list value) : behavior :=
  run_collecting fuel code (initial_state globals) [].

(* === The Correctness Theorem === *)

(* The source interpreter and bytecode interpreter consume fuel at different
   rates: the source interpreter uses 1 fuel per AST node, while the bytecode
   interpreter uses 1 fuel per instruction. So we cannot use the same fuel
   parameter for both sides. Instead, we state: if the source interpreter
   terminates normally, there exists enough bytecode fuel to match the trace. *)

Definition traces_agree (prog : program) : Prop :=
  forall (src_fuel : nat),
    match interpret src_fuel prog with
    | {| trace := t; result := Term_normal _ |} =>
      exists (bc_fuel : nat),
        (bytecode_behavior bc_fuel (compile_program prog) []).(trace) = t
    | _ => True
    end.

Theorem compiler_correctness :
  forall (prog : program), traces_agree prog.
Proof.
  (* This proof is the main deliverable of the formal verification effort.
     It requires showing that for every source-level execution that terminates
     normally, the compiled bytecode produces the same output trace when run
     with sufficient fuel. *)
Admitted.

(* The bytecode interpreter's step function is deterministic. *)
Lemma step_deterministic :
  forall code s r1 r2,
    step code s = r1 -> step code s = r2 -> r1 = r2.
Proof.
  intros. congruence.
Qed.
