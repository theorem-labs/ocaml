(* PUSHACC4_correct.v -- PUSHACC4 = PUSH then ACC4.
   The C handler: decrement sp, store accu to *new_sp, load old stack[3]
   (= *(new_sp + 32)) into accu.
   Rocq: handle_PUSHACC 4 pc' s =
     let new_stack := accu :: stack in
     Step {pc := pc'; accu := stack[3]; stack := new_stack}. *)
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

(* sp + 4 = sp + 32 bytes *)
Local Lemma sem_add_sp_4 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 4)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 32))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Theorem verify_PUSHACC4_correct :
    handler_correct (handle_instr (PUSHACC 4)) (clight_of (PUSHACC 4))
      (error_message_of (PUSHACC 4))
      (pre_of (PUSHACC 4)) (P_halt_of (PUSHACC 4)) (P_ccall_of (PUSHACC 4)).
Proof.
Admitted.

Definition correct_PUSHACC4 :
    handler_correct (handle_instr (PUSHACC 4)) (clight_of (PUSHACC 4))
      (error_message_of (PUSHACC 4))
      (pre_of (PUSHACC 4)) (P_halt_of (PUSHACC 4)) (P_ccall_of (PUSHACC 4)).
Proof. exact verify_PUSHACC4_correct. Qed.
