(* APPLY1_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for APPLY1.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_APPLY1 :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of APPLY1)
      (pre_of APPLY1) (P_error_of APPLY1) (P_halt_of APPLY1) (P_ccall_of APPLY1) ->
    handler_correct h2 (clight_of APPLY1)
      (pre_of APPLY1) (P_error_of APPLY1) (P_halt_of APPLY1) (P_ccall_of APPLY1) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
