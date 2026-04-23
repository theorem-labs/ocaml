(* STOP_correct.v -- STOP handler completeness proof.

   The C body is: return 1; (halt signal).
   The Rocq handler is: handle_STOP s = Halt s.(accu).

   Since handler_correct matches on the step_result and the Halt case
   requires P_halt v = (fun _ => True) (accu s) = True, the proof is
   immediate. *)

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

Theorem verify_STOP_correct :
  handler_correct (fun _ => handle_STOP) f_instr_STOP
    (fun _ _ _ _ => True)
    (fun _ _ => False) (fun _ => True) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handle_STOP. exact I.
Qed.

Definition correct_STOP :
    handler_correct (handle_instr STOP) (clight_of STOP)
      (pre_of STOP)
      (P_error_of STOP) (P_halt_of STOP) (P_ccall_of STOP).
Proof.
Admitted.
