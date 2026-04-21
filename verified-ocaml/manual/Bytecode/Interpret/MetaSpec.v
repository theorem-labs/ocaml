(* MetaSpec.v - [TRUSTED] Module Type stating the uniqueness meta-theorem
   for bytecode instruction handlers.

   The meta-theorem says: any two handlers satisfying the per-instruction
   correctness obligation (packaged by the dispatch functions clight_of,
   pre_of, P_error_of, P_halt_of, P_ccall_of) agree on every input state
   up to error-message strings.

   This Phase 1 file declares the interface only.  The ascription in
   checker/Bytecode/MetaSpecChecker.v admits the meta-theorem so the
   rest of the tree can build against a stable surface. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec.

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

Module Type MetaSpec.

  (* Uniqueness mod error-message strings.

     For every instruction [i], any two handlers that independently
     satisfy the spec dispatch functions produce observationally-
     equivalent results on every input state (agreeing on the Step
     post-state, Halt value, and CCall_request triple; potentially
     disagreeing only on the contents of Error messages). *)
  Parameter handler_unique_mod_errors :
    forall (i : instruction)
           (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of i)
        (fun e m s ard => instr_wfb i = true /\ pre_of i e m s ard)
        (P_error_of i) (P_halt_of i) (P_ccall_of i) ->
      handler_correct h2 (clight_of i)
        (fun e m s ard => instr_wfb i = true /\ pre_of i e m s ard)
        (P_error_of i) (P_halt_of i) (P_ccall_of i) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

End MetaSpec.
