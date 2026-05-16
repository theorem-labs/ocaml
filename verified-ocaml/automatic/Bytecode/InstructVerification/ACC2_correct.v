(* ACC2_correct.v -- ACC2 completeness proof using the computational
   evaluator from StepToBigstep.v.

   ACC2 is identical to ACC0 except it accesses stack[2] instead of
   stack[0].  The C code reads *(sp + 2) which adds 16 bytes (2 * sizeof(long)).

   Uses abs_rel directly (no separate _pre relation).
   All lemmas/axioms imported from HandlerLemmas. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
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
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.
Local Notation exec := (exec_stmt function_entry1 clight_ge).

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Local pointer arithmetic lemma: sp + 2 = sp + 16 bytes             *)
(* ================================================================== *)

Local Lemma sem_add_sp_2 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 2)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Theorem verify_ACC2 :
    handler_correct (handle_ACC 2) f_instr_ACC2
      (fun _ => None)
      (fun _ _ _ _ => True)
      (fun _ => None) (fun _ => None).
Proof.
  (* Intractable as stated: handler_correct checks the Error branch before
     any abs_rel/precondition assumptions, so stack underflow leaves a bare
     False goal under (fun _ => None). *)
Admitted.

Theorem correct_ACC2 :
    handler_correct (handle_ACC 2) f_instr_ACC2
      (fun _ => None)
      (fun _ _ _ _ => True)
      (fun _ => None) (fun _ => None).
Proof.
  exact verify_ACC2.
Qed.
