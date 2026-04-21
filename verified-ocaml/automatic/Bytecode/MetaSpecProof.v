(* MetaSpecProof.v - [UNTRUSTED] Phase-1 implementation of the handler
   uniqueness meta-specification.

   The theorem is intentionally admitted here, in automatic/, so checker/
   can remain a module-type ascription layer plus Print Assumptions probes. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine InstructSpec.
From OCamlInterp.Manual.Bytecode.Interpret Require Import MetaSpec.

Lemma handler_unique_mod_errors :
  forall (i : instruction)
         (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of i)
      (fun e m s ard => instr_wfb i = true /\ pre_of i e m s ard)
      (P_error_of i) (P_halt_of i) (P_ccall_of i) ->
    handler_correct h2 (clight_of i)
      (fun e m s ard => instr_wfb i = true /\ pre_of i e m s ard)
      (P_error_of i) (P_halt_of i) (P_ccall_of i) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.
