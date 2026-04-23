(* SUBINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for SUBINT. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.

Lemma unique_SUBINT :
  forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of SUBINT)
        (error_message_of SUBINT)
        (pre_of SUBINT) (P_halt_of SUBINT) (P_ccall_of SUBINT) ->
      handler_correct h2 (clight_of SUBINT)
        (error_message_of SUBINT)
        (pre_of SUBINT) (P_halt_of SUBINT) (P_ccall_of SUBINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros.
  eapply unique_non_halt_ccall_from_handler_correct; eauto;
    unfold P_halt_of, P_ccall_of; simpl; intros; tauto.
Qed.
