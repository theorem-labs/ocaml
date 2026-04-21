(* CONSTINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for CONSTINT.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_CONSTINT : forall z, 
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of (CONSTINT z))
      (pre_of (CONSTINT z)) (P_error_of (CONSTINT z)) (P_halt_of (CONSTINT z)) (P_ccall_of (CONSTINT z)) ->
    handler_correct h2 (clight_of (CONSTINT z))
      (pre_of (CONSTINT z)) (P_error_of (CONSTINT z)) (P_halt_of (CONSTINT z)) (P_ccall_of (CONSTINT z)) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
