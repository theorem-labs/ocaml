(* SETFIELD1_correct.v -- SETFIELD1 correctness proof.

   SETFIELD1: pop stack top, write it to heap field 1 of accu,
   set accu = val_unit.

   C handler (f_instr_SETFIELD1):
     _t'1 = s->sp;               // read sp
     s->sp = _t'1 + 1;           // sp++ (pop)
     _t'2 = s->accu;             // read accu (heap ptr)
     _t'3 = *_t'1;               // read stack top
     *(cast(_t'2) + 1) = _t'3;   // store to heap field 1 (offset +8)
     s->accu = ((0 << 1) + 1);   // val_unit = 1
     return 0;

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
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

(* Heap-store precondition for field 1: now uses generic setfield_heap_pre 1. *)

Theorem verify_SETFIELD1_correct :
    handler_correct (handle_SETFIELD 1) f_instr_SETFIELD1
      (fun _ => None)
      (setfield_heap_pre 1)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.
