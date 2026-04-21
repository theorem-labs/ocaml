(* MAKEBLOCK1_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for MAKEBLOCK1.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_MAKEBLOCK1 : forall n, 
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of (MAKEBLOCK1 n))
      (pre_of (MAKEBLOCK1 n)) (P_error_of (MAKEBLOCK1 n)) (P_halt_of (MAKEBLOCK1 n)) (P_ccall_of (MAKEBLOCK1 n)) ->
    handler_correct h2 (clight_of (MAKEBLOCK1 n))
      (pre_of (MAKEBLOCK1 n)) (P_error_of (MAKEBLOCK1 n)) (P_halt_of (MAKEBLOCK1 n)) (P_ccall_of (MAKEBLOCK1 n)) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
