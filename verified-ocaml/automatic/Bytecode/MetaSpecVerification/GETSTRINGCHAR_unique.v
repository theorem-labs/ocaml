(* GETSTRINGCHAR_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for GETSTRINGCHAR.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_GETSTRINGCHAR :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of GETSTRINGCHAR)
      (pre_of GETSTRINGCHAR) (P_error_of GETSTRINGCHAR) (P_halt_of GETSTRINGCHAR) (P_ccall_of GETSTRINGCHAR) ->
    handler_correct h2 (clight_of GETSTRINGCHAR)
      (pre_of GETSTRINGCHAR) (P_error_of GETSTRINGCHAR) (P_halt_of GETSTRINGCHAR) (P_ccall_of GETSTRINGCHAR) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
