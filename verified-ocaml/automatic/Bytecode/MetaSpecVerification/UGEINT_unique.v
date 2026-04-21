(* UGEINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for UGEINT.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_UGEINT :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of UGEINT)
      (pre_of UGEINT) (P_error_of UGEINT) (P_halt_of UGEINT) (P_ccall_of UGEINT) ->
    handler_correct h2 (clight_of UGEINT)
      (pre_of UGEINT) (P_error_of UGEINT) (P_halt_of UGEINT) (P_ccall_of UGEINT) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
