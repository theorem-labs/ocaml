(* BLEINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for BLEINT.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_BLEINT : forall z1 z2, 
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of (BLEINT z1 z2))
      (pre_of (BLEINT z1 z2)) (P_error_of (BLEINT z1 z2)) (P_halt_of (BLEINT z1 z2)) (P_ccall_of (BLEINT z1 z2)) ->
    handler_correct h2 (clight_of (BLEINT z1 z2))
      (pre_of (BLEINT z1 z2)) (P_error_of (BLEINT z1 z2)) (P_halt_of (BLEINT z1 z2)) (P_ccall_of (BLEINT z1 z2)) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
