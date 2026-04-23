(* GETGLOBAL_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for GETGLOBAL. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.

Lemma unique_GETGLOBAL :
  forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (GETGLOBAL n))
        (pre_of (GETGLOBAL n)) (P_error_of (GETGLOBAL n)) (P_halt_of (GETGLOBAL n)) (P_ccall_of (GETGLOBAL n)) ->
      handler_correct h2 (clight_of (GETGLOBAL n))
        (pre_of (GETGLOBAL n)) (P_error_of (GETGLOBAL n)) (P_halt_of (GETGLOBAL n)) (P_ccall_of (GETGLOBAL n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros n h1 h2 Hcorr1 Hcorr2 s.
  exact (unique_from_handler_correct
    (clight_of (GETGLOBAL n)) (pre_of (GETGLOBAL n))
    (P_error_of (GETGLOBAL n)) (P_halt_of (GETGLOBAL n)) (P_ccall_of (GETGLOBAL n))
    h1 h2 Hcorr1 Hcorr2 s).
Qed.
