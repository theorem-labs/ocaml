(* ATOM_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for ATOM. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.

Lemma unique_ATOM :
  forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (ATOM n))
        (error_message_of (ATOM n))
        (pre_of (ATOM n)) (P_halt_of (ATOM n)) (P_ccall_of (ATOM n)) ->
      handler_correct h2 (clight_of (ATOM n))
        (error_message_of (ATOM n))
        (pre_of (ATOM n)) (P_halt_of (ATOM n)) (P_ccall_of (ATOM n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof. Admitted.
