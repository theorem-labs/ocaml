(* APPLY_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for APPLY. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.

Lemma unique_APPLY :
  forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (APPLY n))
        (error_message_of (APPLY n))
        (pre_of (APPLY n)) (P_halt_of (APPLY n)) (P_ccall_of (APPLY n)) ->
      handler_correct h2 (clight_of (APPLY n))
        (error_message_of (APPLY n))
        (pre_of (APPLY n)) (P_halt_of (APPLY n)) (P_ccall_of (APPLY n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof. Admitted.
