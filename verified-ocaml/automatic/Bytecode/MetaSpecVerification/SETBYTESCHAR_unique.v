(* SETBYTESCHAR_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for SETBYTESCHAR.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_SETBYTESCHAR :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of SETBYTESCHAR)
      (pre_of SETBYTESCHAR) (P_error_of SETBYTESCHAR) (P_halt_of SETBYTESCHAR) (P_ccall_of SETBYTESCHAR) ->
    handler_correct h2 (clight_of SETBYTESCHAR)
      (pre_of SETBYTESCHAR) (P_error_of SETBYTESCHAR) (P_halt_of SETBYTESCHAR) (P_ccall_of SETBYTESCHAR) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
