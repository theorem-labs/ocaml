(* CONST2_correct.v -- constant 2: s->accu = ((2 << 1) + 1) = 5. *)
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
Local Lemma sem_cast_int_to_long_2 : forall m, sem_cast (Vint (Int.repr 2)) tint tlong m = Some (Vlong (Int64.repr 2)). Proof. intros. reflexivity. Qed.
Local Lemma sem_shl_long_2_1 : forall m, sem_binary_operation (genv_cenv clight_ge) Oshl (Vlong (Int64.repr 2)) tlong (Vint (Int.repr 1)) tint m = Some (Vlong (Int64.repr 4)). Proof. intros. reflexivity. Qed.
Local Lemma sem_add_long_int_4_1 : forall m, sem_binary_operation (genv_cenv clight_ge) Oadd (Vlong (Int64.repr 4)) tlong (Vint (Int.repr 1)) tint m = Some (Vlong (Int64.repr 5)). Proof. intros. reflexivity. Qed.
Local Lemma val_int_2_load_result : Val.load_result Mint64 (Vlong (Int64.repr 5)) = Vlong (Int64.repr 5). Proof. reflexivity. Qed.
