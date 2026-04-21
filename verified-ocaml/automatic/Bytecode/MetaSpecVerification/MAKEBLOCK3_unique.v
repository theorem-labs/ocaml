(* MAKEBLOCK3_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for MAKEBLOCK3.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_MAKEBLOCK3 : forall n, 
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of (MAKEBLOCK3 n))
      (pre_of (MAKEBLOCK3 n)) (P_error_of (MAKEBLOCK3 n)) (P_halt_of (MAKEBLOCK3 n)) (P_ccall_of (MAKEBLOCK3 n)) ->
    handler_correct h2 (clight_of (MAKEBLOCK3 n))
      (pre_of (MAKEBLOCK3 n)) (P_error_of (MAKEBLOCK3 n)) (P_halt_of (MAKEBLOCK3 n)) (P_ccall_of (MAKEBLOCK3 n)) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
