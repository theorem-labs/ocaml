(* DIVINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for DIVINT.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_DIVINT :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of DIVINT)
      (pre_of DIVINT) (P_error_of DIVINT) (P_halt_of DIVINT) (P_ccall_of DIVINT) ->
    handler_correct h2 (clight_of DIVINT)
      (pre_of DIVINT) (P_error_of DIVINT) (P_halt_of DIVINT) (P_ccall_of DIVINT) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
