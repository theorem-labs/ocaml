(* C_CALLN_correct.v -- C_CALLN handler completeness proof.

   The C body reads nargs and prim_idx from the code buffer, advances pc
   by 2, and returns 3 (CCall_request signal).
   The Rocq handler is: handle_C_CALL nargs prim_idx pc' s = CCall_request ...
   Since handler_correct matches on the step_result and the CCall_request
   case requires P_ccall = (fun _ _ _ => True), the proof is immediate. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.InstructSpec.

Theorem verify_C_CALLN_correct : forall nargs prim_idx,
  handler_correct (handle_C_CALL nargs prim_idx) f_instr_C_CALLN
    (fun _ _ _ _ => True)
    (fun _ _ => False) (fun _ => False) (fun _ _ _ => True).
Proof.
  intros nargs prim_idx e le m s.
  unfold handle_C_CALL. simpl. exact I.
Qed.
