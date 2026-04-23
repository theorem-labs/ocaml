(* RETURN_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for RETURN. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.

Lemma unique_RETURN :
  forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (RETURN n))
        (error_message_of (RETURN n))
        (pre_of (RETURN n)) (P_halt_of (RETURN n)) (P_ccall_of (RETURN n)) ->
      handler_correct h2 (clight_of (RETURN n))
        (error_message_of (RETURN n))
        (pre_of (RETURN n)) (P_halt_of (RETURN n)) (P_ccall_of (RETURN n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof. Admitted.
