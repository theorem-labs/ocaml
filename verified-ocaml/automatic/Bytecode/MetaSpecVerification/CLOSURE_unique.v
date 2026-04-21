(* CLOSURE_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for CLOSURE.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_CLOSURE : forall nvars code_ofs, 
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of (CLOSURE nvars code_ofs))
      (pre_of (CLOSURE nvars code_ofs)) (P_error_of (CLOSURE nvars code_ofs)) (P_halt_of (CLOSURE nvars code_ofs)) (P_ccall_of (CLOSURE nvars code_ofs)) ->
    handler_correct h2 (clight_of (CLOSURE nvars code_ofs))
      (pre_of (CLOSURE nvars code_ofs)) (P_error_of (CLOSURE nvars code_ofs)) (P_halt_of (CLOSURE nvars code_ofs)) (P_ccall_of (CLOSURE nvars code_ofs)) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
