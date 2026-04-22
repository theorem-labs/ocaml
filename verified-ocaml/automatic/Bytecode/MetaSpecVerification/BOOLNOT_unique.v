(* BOOLNOT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for BOOLNOT. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.

Lemma unique_BOOLNOT :
  forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of BOOLNOT)
        (pre_of BOOLNOT) (P_error_of BOOLNOT) (P_halt_of BOOLNOT) (P_ccall_of BOOLNOT) ->
      handler_correct h2 (clight_of BOOLNOT)
        (pre_of BOOLNOT) (P_error_of BOOLNOT) (P_halt_of BOOLNOT) (P_ccall_of BOOLNOT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros h1 h2 Hcorr1 Hcorr2 s.
  exact (unique_from_handler_correct
    (clight_of BOOLNOT) (pre_of BOOLNOT)
    (P_error_of BOOLNOT) (P_halt_of BOOLNOT) (P_ccall_of BOOLNOT)
    h1 h2 Hcorr1 Hcorr2 s).
Qed.
