(* ADDINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for ADDINT. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.

Lemma unique_ADDINT :
  forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps ADDINT ->
      handler_correct h1 (clight_of ADDINT)
        (error_message_of ADDINT)
        (pre_of ADDINT) (P_halt_of ADDINT) (P_ccall_of ADDINT) ->
      handler_correct h2 (clight_of ADDINT)
        (error_message_of ADDINT)
        (pre_of ADDINT) (P_halt_of ADDINT) (P_ccall_of ADDINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros.
  eapply unique_from_handler_unique_hyps; eauto.
Qed.
