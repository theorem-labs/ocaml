(* PUSHTRAP_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for PUSHTRAP. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.

Lemma unique_PUSHTRAP :
  forall z,
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (PUSHTRAP z))
        (error_message_of (PUSHTRAP z))
        (pre_of (PUSHTRAP z)) (P_halt_of (PUSHTRAP z)) (P_ccall_of (PUSHTRAP z)) ->
      handler_correct h2 (clight_of (PUSHTRAP z))
        (error_message_of (PUSHTRAP z))
        (pre_of (PUSHTRAP z)) (P_halt_of (PUSHTRAP z)) (P_ccall_of (PUSHTRAP z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof. Admitted.
