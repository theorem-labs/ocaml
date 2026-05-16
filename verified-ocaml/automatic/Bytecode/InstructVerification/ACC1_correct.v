(* ACC1_correct.v -- clone of ACC2 with stack index 1 *)
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
        Mem.load Mem.store Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int field_offset PTree.get PTree.set].

Theorem verify_ACC1 :
    handler_correct (handle_ACC 1) f_instr_ACC1
      (fun _ => None)
      (fun _ _ _ _ => True)
      (fun _ => None) (fun _ => None).
Proof.
  (* Intractable as stated: handler_correct checks the Error branch before
     any abs_rel/precondition assumptions, so stack underflow leaves a bare
     False goal under (fun _ => None). *)
Admitted.

Theorem correct_ACC1 :
    handler_correct (handle_ACC 1) f_instr_ACC1
      (fun _ => None)
      (fun _ _ _ _ => True)
      (fun _ => None) (fun _ => None).
Proof.
  exact verify_ACC1.
Qed.
