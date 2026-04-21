(* CHECK_SIGNALS_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for CHECK_SIGNALS.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_CHECK_SIGNALS :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of CHECK_SIGNALS)
      (pre_of CHECK_SIGNALS) (P_error_of CHECK_SIGNALS) (P_halt_of CHECK_SIGNALS) (P_ccall_of CHECK_SIGNALS) ->
    handler_correct h2 (clight_of CHECK_SIGNALS)
      (pre_of CHECK_SIGNALS) (P_error_of CHECK_SIGNALS) (P_halt_of CHECK_SIGNALS) (P_ccall_of CHECK_SIGNALS) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
