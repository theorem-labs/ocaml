(* MetaSpecChecker.v - Ascribes a Module satisfying MetaSpec.MetaSpec,
   admitting the uniqueness meta-theorem.

   Phase 1 of META_SPEC_PLAN.md: the meta-theorem is Admitted so the
   whole-tree build stays green and the interface is in place.  Phase
   2/3 will prove [handler_unique_mod_errors] by discharging the four
   obligations (A: step_pre totality, B: abs_rel functional, C: P_error
   characterises error states, D: outcome kinds mutually exclusive)
   described in the plan. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine InstructSpec.
From OCamlInterp.Manual.Bytecode.Interpret Require MetaSpec.

Module Check <: MetaSpec.MetaSpec.

  Lemma handler_unique_mod_errors :
    forall (i : instruction) (pc' : Z)
           (h1 h2 : Z -> state -> step_result),
      MetaSpec.handler_matches h1 (spec_of i pc') ->
      MetaSpec.handler_matches h2 (spec_of i pc') ->
      forall s, MetaSpec.em_eq (h1 pc' s) (h2 pc' s).
  Proof.
  Admitted.

  Section __.
  Set Printing All.
  Set Printing Fully Qualified.
  Set Printing Depth 10000000000.
  Set Printing Width 2000.
  Goal True.
    idtac "<handler_unique_mod_errors>".
    idtac "<PrintAssumptions>".
    Print Assumptions handler_unique_mod_errors.
    idtac "</PrintAssumptions>".
    idtac "</handler_unique_mod_errors>".
  Abort.
  End __.

End Check.
