(* ORINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for ORINT. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.

Lemma unique_ORINT :
  forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of ORINT)
        (error_message_of ORINT)
        (pre_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT) ->
      handler_correct h2 (clight_of ORINT)
        (error_message_of ORINT)
        (pre_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof. Admitted.
