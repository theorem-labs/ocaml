(* C_CALL_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for C_CALL.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_C_CALL : forall nargs prim_idx, 
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of (C_CALL nargs prim_idx))
      (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
    handler_correct h2 (clight_of (C_CALL nargs prim_idx))
      (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
