(* RERAISE_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for RERAISE.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_RERAISE :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of RERAISE)
      (pre_of RERAISE) (P_error_of RERAISE) (P_halt_of RERAISE) (P_ccall_of RERAISE) ->
    handler_correct h2 (clight_of RERAISE)
      (pre_of RERAISE) (P_error_of RERAISE) (P_halt_of RERAISE) (P_ccall_of RERAISE) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
