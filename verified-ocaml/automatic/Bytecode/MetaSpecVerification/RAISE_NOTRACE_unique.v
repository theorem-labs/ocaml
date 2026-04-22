(* RAISE_NOTRACE_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for RAISE_NOTRACE. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.

Lemma unique_RAISE_NOTRACE :
  forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of RAISE_NOTRACE)
        (pre_of RAISE_NOTRACE) (P_error_of RAISE_NOTRACE) (P_halt_of RAISE_NOTRACE) (P_ccall_of RAISE_NOTRACE) ->
      handler_correct h2 (clight_of RAISE_NOTRACE)
        (pre_of RAISE_NOTRACE) (P_error_of RAISE_NOTRACE) (P_halt_of RAISE_NOTRACE) (P_ccall_of RAISE_NOTRACE) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros h1 h2 Hcorr1 Hcorr2 s.
  exact (unique_from_handler_correct
    (clight_of RAISE_NOTRACE) (pre_of RAISE_NOTRACE)
    (P_error_of RAISE_NOTRACE) (P_halt_of RAISE_NOTRACE) (P_ccall_of RAISE_NOTRACE)
    h1 h2 Hcorr1 Hcorr2 s).
Qed.
