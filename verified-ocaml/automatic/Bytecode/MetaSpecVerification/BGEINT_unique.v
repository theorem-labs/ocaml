(* BGEINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for BGEINT. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.

Lemma unique_BGEINT :
  forall z1 z2,
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (BGEINT z1 z2))
        (pre_of (BGEINT z1 z2)) (P_error_of (BGEINT z1 z2)) (P_halt_of (BGEINT z1 z2)) (P_ccall_of (BGEINT z1 z2)) ->
      handler_correct h2 (clight_of (BGEINT z1 z2))
        (pre_of (BGEINT z1 z2)) (P_error_of (BGEINT z1 z2)) (P_halt_of (BGEINT z1 z2)) (P_ccall_of (BGEINT z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros z1 z2 h1 h2 Hcorr1 Hcorr2 s.
  exact (unique_from_handler_correct
    (clight_of (BGEINT z1 z2)) (pre_of (BGEINT z1 z2))
    (P_error_of (BGEINT z1 z2)) (P_halt_of (BGEINT z1 z2)) (P_ccall_of (BGEINT z1 z2))
    h1 h2 Hcorr1 Hcorr2 s).
Qed.
