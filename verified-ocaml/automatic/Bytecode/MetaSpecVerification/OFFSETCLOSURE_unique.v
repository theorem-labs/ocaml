(* OFFSETCLOSURE_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for OFFSETCLOSURE.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_OFFSETCLOSURE : forall z, 
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of (OFFSETCLOSURE z))
      (pre_of (OFFSETCLOSURE z)) (P_error_of (OFFSETCLOSURE z)) (P_halt_of (OFFSETCLOSURE z)) (P_ccall_of (OFFSETCLOSURE z)) ->
    handler_correct h2 (clight_of (OFFSETCLOSURE z))
      (pre_of (OFFSETCLOSURE z)) (P_error_of (OFFSETCLOSURE z)) (P_halt_of (OFFSETCLOSURE z)) (P_ccall_of (OFFSETCLOSURE z)) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
