(* SETVECTITEM_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for SETVECTITEM.
   Stub file; proof to be filled in by subagent. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma unique_SETVECTITEM :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of SETVECTITEM)
      (pre_of SETVECTITEM) (P_error_of SETVECTITEM) (P_halt_of SETVECTITEM) (P_ccall_of SETVECTITEM) ->
    handler_correct h2 (clight_of SETVECTITEM)
      (pre_of SETVECTITEM) (P_error_of SETVECTITEM) (P_halt_of SETVECTITEM) (P_ccall_of SETVECTITEM) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
