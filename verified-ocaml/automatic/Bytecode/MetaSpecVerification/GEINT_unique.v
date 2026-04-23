(* GEINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for GEINT. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.

Lemma unique_GEINT :
  forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of GEINT)
        (error_message_of GEINT)
        (pre_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT) ->
      handler_correct h2 (clight_of GEINT)
        (error_message_of GEINT)
        (pre_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof. Admitted.
