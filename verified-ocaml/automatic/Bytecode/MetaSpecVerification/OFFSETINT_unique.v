(* OFFSETINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for OFFSETINT.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_OFFSETINT : forall z, 
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of (OFFSETINT z))
      (pre_of (OFFSETINT z)) (P_error_of (OFFSETINT z)) (P_halt_of (OFFSETINT z)) (P_ccall_of (OFFSETINT z)) ->
    handler_correct h2 (clight_of (OFFSETINT z))
      (pre_of (OFFSETINT z)) (P_error_of (OFFSETINT z)) (P_halt_of (OFFSETINT z)) (P_ccall_of (OFFSETINT z)) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
