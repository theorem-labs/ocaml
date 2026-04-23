(* STOP_correct.v -- STOP handler correctness proof.

   The C body is: return 1; (halt signal).
   The Rocq handler is: handle_STOP s = Halt s.(accu).

   Since handler_correct matches on the step_result and the Halt case
   requires P_halt_of STOP v = (instr_wfb STOP = true /\ True), the
   proof reduces to showing that the Clight body `return 1` executes
   to Out_return (Some (Vint (Int.repr 1), tint)). *)

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

Definition correct_STOP :
    handler_correct (handle_instr STOP) (clight_of STOP)
      (error_message_of STOP)
      (pre_of STOP) (P_halt_of STOP) (P_ccall_of STOP).
Proof.
  unfold handler_correct, handler_correct_gen.
  intros e le m s.
  (* error_message_of STOP s = None, handle_instr STOP _ s = Halt s.(accu) *)
  simpl error_message_of.
  simpl handle_instr.
  (* Now in the Halt branch: need P_halt_of STOP (accu s) /\ forall w, ... *)
  split.
  - (* P_halt_of STOP (accu s) = instr_wfb STOP = true /\ True *)
    simpl. split; [reflexivity | exact I].
  - (* forall w, abs_rel_with_ard e le m s w ->
       step_pre e m s w ->
       exists le' m', clight_returns f_instr_STOP 1 e le m le' m' *)
    intros w Hrel Hpre.
    exists le, m.
    (* clight_returns f_instr_STOP 1 e le m le m =
       exec_stmt function_entry1 clight_ge e le m
         (Sreturn (Some (Econst_int (Int.repr 1) tint))) E0 le m
         (Out_return (Some (Vint (Int.repr 1), tint))) *)
    unfold clight_returns. simpl fn_body.
    apply exec_Sreturn_some.
    apply eval_Econst_int.
Qed.
