(* GETGLOBAL_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for GETGLOBAL.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_GETGLOBAL : forall n, 
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of (GETGLOBAL n))
      (pre_of (GETGLOBAL n)) (P_error_of (GETGLOBAL n)) (P_halt_of (GETGLOBAL n)) (P_ccall_of (GETGLOBAL n)) ->
    handler_correct h2 (clight_of (GETGLOBAL n))
      (pre_of (GETGLOBAL n)) (P_error_of (GETGLOBAL n)) (P_halt_of (GETGLOBAL n)) (P_ccall_of (GETGLOBAL n)) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
