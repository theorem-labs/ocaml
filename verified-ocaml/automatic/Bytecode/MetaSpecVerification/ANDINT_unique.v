(* ANDINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for ANDINT.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_ANDINT :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of ANDINT)
      (pre_of ANDINT) (P_error_of ANDINT) (P_halt_of ANDINT) (P_ccall_of ANDINT) ->
    handler_correct h2 (clight_of ANDINT)
      (pre_of ANDINT) (P_error_of ANDINT) (P_halt_of ANDINT) (P_ccall_of ANDINT) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
