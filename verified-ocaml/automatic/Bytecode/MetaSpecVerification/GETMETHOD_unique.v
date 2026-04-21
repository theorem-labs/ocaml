(* GETMETHOD_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for GETMETHOD.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_GETMETHOD :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of GETMETHOD)
      (pre_of GETMETHOD) (P_error_of GETMETHOD) (P_halt_of GETMETHOD) (P_ccall_of GETMETHOD) ->
    handler_correct h2 (clight_of GETMETHOD)
      (pre_of GETMETHOD) (P_error_of GETMETHOD) (P_halt_of GETMETHOD) (P_ccall_of GETMETHOD) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
