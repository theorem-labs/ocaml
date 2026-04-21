(* SETFLOATFIELD_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for SETFLOATFIELD.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_SETFLOATFIELD : forall n, 
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of (SETFLOATFIELD n))
      (pre_of (SETFLOATFIELD n)) (P_error_of (SETFLOATFIELD n)) (P_halt_of (SETFLOATFIELD n)) (P_ccall_of (SETFLOATFIELD n)) ->
    handler_correct h2 (clight_of (SETFLOATFIELD n))
      (pre_of (SETFLOATFIELD n)) (P_error_of (SETFLOATFIELD n)) (P_halt_of (SETFLOATFIELD n)) (P_ccall_of (SETFLOATFIELD n)) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
