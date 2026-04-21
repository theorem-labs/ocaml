(* C_CALL_correct.v -- C_CALL handler correctness wrapper.

   handle_C_CALL always returns CCall_request, so handler_correct
   reduces to proving P_ccall_of (C_CALL nargs prim_idx), which is
   instr_wfb (C_CALL nargs prim_idx) = true /\ True — trivially true. *)

From Stdlib Require Import ZArith List.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.

Theorem correct_C_CALL : forall nargs prim_idx,
  handler_correct (handle_instr (C_CALL nargs prim_idx)) (clight_of (C_CALL nargs prim_idx))
    (pre_of (C_CALL nargs prim_idx))
    (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)).
Proof.
  intros nargs prim_idx.
  unfold handler_correct.
  intros e le m s.
  (* handle_instr (C_CALL nargs prim_idx) reduces to
     handle_C_CALL nargs prim_idx, which always returns CCall_request.
     The obligation is P_ccall_of (C_CALL nargs prim_idx) prim_idx args cont,
     i.e. instr_wfb (C_CALL nargs prim_idx) = true /\ True. *)
  simpl.
  split; reflexivity.
Qed.
