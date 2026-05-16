(* XORINT_correct.v -- clone of SUBINT adapted for bitwise XOR with retag.
   C: s->accu = (long)(((long)_t'2 ^ (long)_t'3) | 1); sp++.
   Tagged: ((2a+1) XOR (2b+1)) | 1 = 2*(a XOR b) + 1 (retag after XOR). *)
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

Local Lemma sem_xor_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Oxor
    (Vlong n1) tlong (Vlong n2) tlong m = Some (Vlong (Int64.xor n1 n2)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_or_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oor
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.or n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

Local Lemma tagged_xorint_arith : forall a b,
  Int64.or (Int64.xor (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1))) (Int64.repr 1)
  = Int64.repr ((Z.lxor a b) * 2 + 1).
Proof.
  intros a b.
  apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_or, Int64.bits_xor, !Int64.testbit_repr by lia.
  replace (a * 2 + 1) with (2 * a + 1) by lia.
  replace (b * 2 + 1) with (2 * b + 1) by lia.
  replace (Z.lxor a b * 2 + 1) with (2 * Z.lxor a b + 1) by lia.
  change 1%Z with (2 * 0 + 1)%Z.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - (* i = 0: XOR of two odd numbers gives 0, OR with 1 gives 1 *)
    rewrite !Z.testbit_odd_0. simpl. reflexivity.
  - (* i > 0: OR with 1 doesn't affect higher bits *)
    replace i with (Z.succ (i - 1)) by lia.
    rewrite !Z.testbit_odd_succ by lia.
    rewrite Z.testbit_0_l. rewrite Bool.orb_false_r.
    rewrite Z.lxor_spec. reflexivity.
Qed.

(* Wrapper with the canonical type expected by InstructVerificationProof.v *)
Theorem correct_XORINT :
  handler_correct (handle_instr Bytecode.AST.XORINT) (clight_of Bytecode.AST.XORINT)
    (error_message_of Bytecode.AST.XORINT)
    (pre_of Bytecode.AST.XORINT) (P_halt_of Bytecode.AST.XORINT) (P_ccall_of Bytecode.AST.XORINT).
Proof.
Admitted.
