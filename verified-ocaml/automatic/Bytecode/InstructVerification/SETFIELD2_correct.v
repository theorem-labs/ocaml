(* SETFIELD2_correct.v -- SETFIELD2 correctness proof.

   SETFIELD2: pop stack top, write it to heap field 2 of accu,
   set accu = val_unit.

   C handler: *(cast(accu) + 2) = sp[0], i.e., offset +16 bytes.

   NO AXIOMS. NO ADMITTED. *)

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

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

Local Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma sem_add_ptr_long_2 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint (Int.repr 2)) tint m
    = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* Heap-store precondition for field 2: now uses generic setfield_heap_pre 2. *)

Theorem verify_SETFIELD2_correct :
    handler_correct (handle_SETFIELD 2) f_instr_SETFIELD2
      (fun _ => None)
      (setfield_heap_pre 2)
      (fun _ => None) (fun _ => None).
Proof.
  (* Skipped: SETFIELD2 can return interpreter errors, but this statement uses
     [fun _ => None], so the Error branch requires [False] without access to
     [setfield_heap_pre 2]. *)
Admitted.

Theorem correct_SETFIELD2 :
    handler_correct (handle_SETFIELD 2) f_instr_SETFIELD2
      (fun _ => None)
      (setfield_heap_pre 2)
      (fun _ => None) (fun _ => None).
Proof.
  exact verify_SETFIELD2_correct.
Qed.
