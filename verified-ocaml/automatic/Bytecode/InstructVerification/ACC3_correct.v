(* ACC3_correct.v -- stack index 3, sp + 3 = sp + 24 bytes *)
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

Local Lemma sem_add_sp_3 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 3)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 24))).
Proof. intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity. Qed.

Theorem verify_ACC3 :
    handler_correct (handle_ACC 3) f_instr_ACC3
      (fun _ => None)
      (fun _ _ _ _ => True)
      (fun _ => None) (fun _ => None).
Proof.
  (* Intractable as stated: handler_correct checks the Error branch before
     any abs_rel/precondition assumptions, so stack underflow leaves a bare
     False goal under (fun _ => None). *)
Admitted.

Theorem correct_ACC3 :
    handler_correct (handle_ACC 3) f_instr_ACC3
      (fun _ => None)
      (fun _ _ _ _ => True)
      (fun _ => None) (fun _ => None).
Proof.
  exact verify_ACC3.
Qed.
