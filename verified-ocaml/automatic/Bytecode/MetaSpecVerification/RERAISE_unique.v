(* RERAISE_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for RERAISE. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.

Lemma unique_RERAISE :
  forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of RERAISE)
        (pre_of RERAISE) (P_error_of RERAISE) (P_halt_of RERAISE) (P_ccall_of RERAISE) ->
      handler_correct h2 (clight_of RERAISE)
        (pre_of RERAISE) (P_error_of RERAISE) (P_halt_of RERAISE) (P_ccall_of RERAISE) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros h1 h2 Hcorr1 Hcorr2 s.
  exact (unique_from_handler_correct
    (clight_of RERAISE) (pre_of RERAISE)
    (P_error_of RERAISE) (P_halt_of RERAISE) (P_ccall_of RERAISE)
    h1 h2 Hcorr1 Hcorr2 s).
Qed.
