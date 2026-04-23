(* PUSHCONSTINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for PUSHCONSTINT. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.

Lemma unique_PUSHCONSTINT :
  forall z,
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (PUSHCONSTINT z))
        (pre_of (PUSHCONSTINT z)) (P_error_of (PUSHCONSTINT z)) (P_halt_of (PUSHCONSTINT z)) (P_ccall_of (PUSHCONSTINT z)) ->
      handler_correct h2 (clight_of (PUSHCONSTINT z))
        (pre_of (PUSHCONSTINT z)) (P_error_of (PUSHCONSTINT z)) (P_halt_of (PUSHCONSTINT z)) (P_ccall_of (PUSHCONSTINT z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros z h1 h2 Hcorr1 Hcorr2 s.
  exact (unique_from_handler_correct
    (clight_of (PUSHCONSTINT z)) (pre_of (PUSHCONSTINT z))
    (P_error_of (PUSHCONSTINT z)) (P_halt_of (PUSHCONSTINT z)) (P_ccall_of (PUSHCONSTINT z))
    h1 h2 Hcorr1 Hcorr2 s).
Qed.
