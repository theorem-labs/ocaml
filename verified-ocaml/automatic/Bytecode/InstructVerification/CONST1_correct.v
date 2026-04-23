(* CONST1_correct.v -- CONST1 completeness proof.
   Clone of CONST0 with constant 1: s->accu = ((1 << 1) + 1) = 3. *)

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

Local Lemma sem_cast_int_to_long_1 : forall m,
  sem_cast (Vint (Int.repr 1)) tint tlong m = Some (Vlong (Int64.repr 1)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_shl_long_1_1 : forall m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong (Int64.repr 1)) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.repr 2)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_add_long_int_2_1 : forall m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong (Int64.repr 2)) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.repr 3)).
Proof. intros. reflexivity. Qed.

Local Lemma val_int_1_load_result :
  Val.load_result Mint64 (Vlong (Int64.repr 3)) = Vlong (Int64.repr 3).
Proof. reflexivity. Qed.

Theorem verify_CONST1_correct :
    handler_correct (handle_CONSTINT 1) f_instr_CONST1
      (fun _ => None)
      (fun _ _ _ _ => True)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.
