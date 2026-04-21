(* POPTRAP_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for POPTRAP.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_POPTRAP :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of POPTRAP)
      (pre_of POPTRAP) (P_error_of POPTRAP) (P_halt_of POPTRAP) (P_ccall_of POPTRAP) ->
    handler_correct h2 (clight_of POPTRAP)
      (pre_of POPTRAP) (P_error_of POPTRAP) (P_halt_of POPTRAP) (P_ccall_of POPTRAP) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
