(* PUSH_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for PUSH.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_PUSH :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of PUSH)
      (pre_of PUSH) (P_error_of PUSH) (P_halt_of PUSH) (P_ccall_of PUSH) ->
    handler_correct h2 (clight_of PUSH)
      (pre_of PUSH) (P_error_of PUSH) (P_halt_of PUSH) (P_ccall_of PUSH) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
