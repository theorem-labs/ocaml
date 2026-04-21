(* BRANCH_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for BRANCH.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_BRANCH : forall z, 
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of (BRANCH z))
      (pre_of (BRANCH z)) (P_error_of (BRANCH z)) (P_halt_of (BRANCH z)) (P_ccall_of (BRANCH z)) ->
    handler_correct h2 (clight_of (BRANCH z))
      (pre_of (BRANCH z)) (P_error_of (BRANCH z)) (P_halt_of (BRANCH z)) (P_ccall_of (BRANCH z)) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
