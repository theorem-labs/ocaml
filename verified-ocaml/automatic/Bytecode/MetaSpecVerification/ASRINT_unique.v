(* ASRINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for ASRINT. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.

Lemma unique_ASRINT :
  forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of ASRINT)
        (pre_of ASRINT) (P_error_of ASRINT) (P_halt_of ASRINT) (P_ccall_of ASRINT) ->
      handler_correct h2 (clight_of ASRINT)
        (pre_of ASRINT) (P_error_of ASRINT) (P_halt_of ASRINT) (P_ccall_of ASRINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros h1 h2 Hcorr1 Hcorr2 s.
  exact (unique_from_handler_correct
    (clight_of ASRINT) (pre_of ASRINT)
    (P_error_of ASRINT) (P_halt_of ASRINT) (P_ccall_of ASRINT)
    h1 h2 Hcorr1 Hcorr2 s).
Qed.
