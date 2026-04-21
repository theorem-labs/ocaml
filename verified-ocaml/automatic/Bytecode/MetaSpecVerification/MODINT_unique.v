(* MODINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for MODINT.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_MODINT :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of MODINT)
      (pre_of MODINT) (P_error_of MODINT) (P_halt_of MODINT) (P_ccall_of MODINT) ->
    handler_correct h2 (clight_of MODINT)
      (pre_of MODINT) (P_error_of MODINT) (P_halt_of MODINT) (P_ccall_of MODINT) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
