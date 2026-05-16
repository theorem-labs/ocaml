(* PUSHACC1_correct.v -- PUSHACC1 = PUSH then ACC1.
   The C handler: decrement sp, store accu to *new_sp, load old stack[0]
   (= *(new_sp + 8)) into accu.
   Rocq: handle_PUSHACC 1 pc' s =
     let new_stack := accu :: stack in
     Step {pc := pc'; accu := stack[0]; stack := new_stack}. *)
From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Import Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr sem_binary_operation sem_cast
        Mem.load Mem.store Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int field_offset PTree.get PTree.set].

Theorem verify_PUSHACC1_correct :
    handler_correct (handle_instr (PUSHACC 1)) (clight_of (PUSHACC 1))
      (error_message_of (PUSHACC 1))
      (pre_of (PUSHACC 1)) (P_halt_of (PUSHACC 1)) (P_ccall_of (PUSHACC 1)).
Proof.
Admitted.

Definition correct_PUSHACC1 :
    handler_correct (handle_instr (PUSHACC 1)) (clight_of (PUSHACC 1))
      (error_message_of (PUSHACC 1))
      (pre_of (PUSHACC 1)) (P_halt_of (PUSHACC 1)) (P_ccall_of (PUSHACC 1)).
Proof. exact verify_PUSHACC1_correct. Qed.
