(* ULTINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for ULTINT.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_ULTINT :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of ULTINT)
      (pre_of ULTINT) (P_error_of ULTINT) (P_halt_of ULTINT) (P_ccall_of ULTINT) ->
    handler_correct h2 (clight_of ULTINT)
      (pre_of ULTINT) (P_error_of ULTINT) (P_halt_of ULTINT) (P_ccall_of ULTINT) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
