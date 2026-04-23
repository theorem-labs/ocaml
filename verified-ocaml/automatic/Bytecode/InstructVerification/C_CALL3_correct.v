(* C_CALL3_correct.v -- C_CALL3 handler completeness proof.

   The C body advances pc by 1 and returns 3 (CCall_request signal).
   The Rocq handler is: handle_C_CALL 3 prim_idx pc' s = CCall_request ...
   Since handler_correct matches on the step_result and the CCall_request
   case requires P_ccall = (fun _ _ _ => True), the proof is immediate. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Import Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.

Theorem verify_C_CALL3_correct : forall prim_idx,
  handler_correct (handle_C_CALL 3 prim_idx) f_instr_C_CALL3
    (fun _ _ _ _ => True)
    (fun _ _ => False) (fun _ => False) (fun _ _ _ => True).
Proof.
  intros prim_idx e le m s.
  unfold handle_C_CALL. simpl. exact I.
Qed.
