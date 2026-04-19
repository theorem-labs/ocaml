(* MetaSpec.v - [TRUSTED] Module Type stating the uniqueness meta-theorem
   for bytecode instruction handlers.

   The meta-theorem says: any two handlers satisfying the handler_correct
   obligation packaged by [spec_of i pc'] agree on every input state up
   to error-message strings.  See
   manual/Bytecode/generator/META_SPEC_PLAN.md for the full design and
   Phase 2/3 obligations that discharge this theorem.

   This Phase 1 file declares the interface only.  The ascription in
   checker/Bytecode/MetaSpecChecker.v admits the meta-theorem so the
   rest of the tree can build against a stable surface. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine InstructSpec.

(* Error-message equivalence on step_result.

   Two outcomes are [em_eq] iff they agree on the non-error projections
   (Step post-state, Halt value, CCall_request triple) or both are Error
   with arbitrary messages. *)
Inductive em_eq : step_result -> step_result -> Prop :=
  | em_Step  : forall s, em_eq (Step s) (Step s)
  | em_Halt  : forall v, em_eq (Halt v) (Halt v)
  | em_CCall : forall n args s',
      em_eq (CCall_request n args s') (CCall_request n args s')
  | em_Error : forall msg msg', em_eq (Error msg) (Error msg').

(* A handler [h] "matches" a spec bundle [b] iff it satisfies the same
   handler_correct obligation as [b.(hs_handler)].  This is the shape
   the meta-theorem quantifies over. *)
Definition handler_matches
    (h : Z -> state -> step_result) (b : HandlerSpecBundle) : Prop :=
  handler_correct h b.(hs_clight) b.(hs_step_pre)
                  b.(hs_P_error) b.(hs_P_halt) b.(hs_P_ccall).

Module Type MetaSpec.

  (* Uniqueness mod error-message strings.

     For every instruction [i] and successor PC [pc'], any two handlers
     that independently satisfy the spec bundle [spec_of i pc'] produce
     observationally-equivalent results on every input state (agreeing
     on the Step post-state, Halt value, and CCall_request triple;
     potentially disagreeing only on the contents of Error messages). *)
  Parameter handler_unique_mod_errors :
    forall (i : instruction) (pc' : Z)
           (h1 h2 : Z -> state -> step_result),
      handler_matches h1 (spec_of i pc') ->
      handler_matches h2 (spec_of i pc') ->
      forall s, em_eq (h1 pc' s) (h2 pc' s).

End MetaSpec.
