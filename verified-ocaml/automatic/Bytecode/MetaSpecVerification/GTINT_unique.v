(* GTINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for GTINT.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_GTINT :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of GTINT)
      (pre_of GTINT) (P_error_of GTINT) (P_halt_of GTINT) (P_ccall_of GTINT) ->
    handler_correct h2 (clight_of GTINT)
      (pre_of GTINT) (P_error_of GTINT) (P_halt_of GTINT) (P_ccall_of GTINT) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
