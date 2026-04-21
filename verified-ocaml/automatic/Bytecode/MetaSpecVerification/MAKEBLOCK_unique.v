(* MAKEBLOCK_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for MAKEBLOCK.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_MAKEBLOCK : forall t size, 
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of (MAKEBLOCK t size))
      (pre_of (MAKEBLOCK t size)) (P_error_of (MAKEBLOCK t size)) (P_halt_of (MAKEBLOCK t size)) (P_ccall_of (MAKEBLOCK t size)) ->
    handler_correct h2 (clight_of (MAKEBLOCK t size))
      (pre_of (MAKEBLOCK t size)) (P_error_of (MAKEBLOCK t size)) (P_halt_of (MAKEBLOCK t size)) (P_ccall_of (MAKEBLOCK t size)) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
