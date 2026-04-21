(* GETGLOBALFIELD_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for GETGLOBALFIELD.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_GETGLOBALFIELD : forall n p, 
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of (GETGLOBALFIELD n p))
      (pre_of (GETGLOBALFIELD n p)) (P_error_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)) ->
    handler_correct h2 (clight_of (GETGLOBALFIELD n p))
      (pre_of (GETGLOBALFIELD n p)) (P_error_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
