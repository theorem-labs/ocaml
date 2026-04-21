(* APPTERM_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for APPTERM.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_APPTERM : forall nargs slotsize, 
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of (APPTERM nargs slotsize))
      (pre_of (APPTERM nargs slotsize)) (P_error_of (APPTERM nargs slotsize)) (P_halt_of (APPTERM nargs slotsize)) (P_ccall_of (APPTERM nargs slotsize)) ->
    handler_correct h2 (clight_of (APPTERM nargs slotsize))
      (pre_of (APPTERM nargs slotsize)) (P_error_of (APPTERM nargs slotsize)) (P_halt_of (APPTERM nargs slotsize)) (P_ccall_of (APPTERM nargs slotsize)) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
