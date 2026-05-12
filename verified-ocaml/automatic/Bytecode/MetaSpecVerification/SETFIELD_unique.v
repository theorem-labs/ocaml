(* SETFIELD_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for SETFIELD. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.

Lemma unique_SETFIELD :
  forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (SETFIELD n) ->
      handler_correct h1 (clight_of (SETFIELD n))
        (error_message_of (SETFIELD n))
        (pre_of (SETFIELD n)) (P_halt_of (SETFIELD n)) (P_ccall_of (SETFIELD n)) ->
      handler_correct h2 (clight_of (SETFIELD n))
        (error_message_of (SETFIELD n))
        (pre_of (SETFIELD n)) (P_halt_of (SETFIELD n)) (P_ccall_of (SETFIELD n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros.
  eapply unique_from_handler_unique_hyps; eauto.
Qed.
