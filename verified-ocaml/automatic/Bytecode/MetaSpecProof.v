(* MetaSpecProof.v - [UNTRUSTED] Phase-1 implementation of the handler
   uniqueness meta-specification.

   The theorem is intentionally admitted here, in automatic/, so checker/
   can remain a module-type ascription layer plus Print Assumptions probes. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine InstructSpec.
From OCamlInterp.Manual.Bytecode.Interpret Require Import MetaSpec.

Lemma handler_unique_mod_errors :
  forall (i : instruction) (pc' : Z)
         (h1 h2 : Z -> state -> step_result),
    handler_matches h1 (spec_of i pc') ->
    handler_matches h2 (spec_of i pc') ->
    forall s, em_eq (h1 pc' s) (h2 pc' s).
Proof.
Admitted.
