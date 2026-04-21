(* EQ_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for EQ.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_EQ :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of EQ)
      (pre_of EQ) (P_error_of EQ) (P_halt_of EQ) (P_ccall_of EQ) ->
    handler_correct h2 (clight_of EQ)
      (pre_of EQ) (P_error_of EQ) (P_halt_of EQ) (P_ccall_of EQ) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
