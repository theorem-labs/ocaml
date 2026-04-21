(* RAISE_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for RAISE.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_RAISE :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of RAISE)
      (pre_of RAISE) (P_error_of RAISE) (P_halt_of RAISE) (P_ccall_of RAISE) ->
    handler_correct h2 (clight_of RAISE)
      (pre_of RAISE) (P_error_of RAISE) (P_halt_of RAISE) (P_ccall_of RAISE) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
