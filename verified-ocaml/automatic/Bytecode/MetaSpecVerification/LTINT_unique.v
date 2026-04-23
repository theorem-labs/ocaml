(* LTINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for LTINT. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.

Lemma unique_LTINT :
  forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of LTINT)
        (error_message_of LTINT)
        (pre_of LTINT) (P_halt_of LTINT) (P_ccall_of LTINT) ->
      handler_correct h2 (clight_of LTINT)
        (error_message_of LTINT)
        (pre_of LTINT) (P_halt_of LTINT) (P_ccall_of LTINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof. Admitted.
