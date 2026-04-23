(* MAKEBLOCK3_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for MAKEBLOCK3. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.

Lemma unique_MAKEBLOCK3 :
  forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (MAKEBLOCK3 n))
        (error_message_of (MAKEBLOCK3 n))
        (pre_of (MAKEBLOCK3 n)) (P_halt_of (MAKEBLOCK3 n)) (P_ccall_of (MAKEBLOCK3 n)) ->
      handler_correct h2 (clight_of (MAKEBLOCK3 n))
        (error_message_of (MAKEBLOCK3 n))
        (pre_of (MAKEBLOCK3 n)) (P_halt_of (MAKEBLOCK3 n)) (P_ccall_of (MAKEBLOCK3 n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros.
  eapply unique_non_halt_ccall_from_handler_correct; eauto;
    unfold P_halt_of, P_ccall_of; simpl; intros; tauto.
Qed.
