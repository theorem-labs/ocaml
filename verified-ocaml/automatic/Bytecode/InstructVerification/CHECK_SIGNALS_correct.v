(* CHECK_SIGNALS_correct.v -- trivial: C body is just return 0. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
From OCamlInterp.Manual Require Bytecode.AST.
Import Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

Theorem verify_CHECK_SIGNALS_correct :
    handler_correct handle_CHECK_SIGNALS f_instr_CHECK_SIGNALS
      (fun _ => None)
      (fun _ _ _ _ => True)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with the exact type expected by InstructVerificationProof.v.
   handle_instr CHECK_SIGNALS = handle_CHECK_SIGNALS and
   clight_of CHECK_SIGNALS = f_instr_CHECK_SIGNALS by computation.
   pre_of CHECK_SIGNALS = no_pre = fun _ _ _ _ => True. *)
Definition correct_CHECK_SIGNALS :
  handler_correct (handle_instr CHECK_SIGNALS) (clight_of CHECK_SIGNALS)
    (error_message_of CHECK_SIGNALS)
    (pre_of CHECK_SIGNALS) (P_halt_of CHECK_SIGNALS) (P_ccall_of CHECK_SIGNALS).
Proof.
Admitted.
