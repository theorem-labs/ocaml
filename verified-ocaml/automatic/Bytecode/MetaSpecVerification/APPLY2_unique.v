(* APPLY2_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for APPLY2. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.

Lemma unique_APPLY2 :
  forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of APPLY2)
        (error_message_of APPLY2)
        (pre_of APPLY2) (P_halt_of APPLY2) (P_ccall_of APPLY2) ->
      handler_correct h2 (clight_of APPLY2)
        (error_message_of APPLY2)
        (pre_of APPLY2) (P_halt_of APPLY2) (P_ccall_of APPLY2) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof. Admitted.
