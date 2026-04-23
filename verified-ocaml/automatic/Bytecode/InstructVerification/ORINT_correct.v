(* ORINT_correct.v -- clone of ANDINT with bitwise OR.
   C: s->accu = (long)((long)_t'2 | (long)_t'3); sp++.
   Tagged: (2a+1) | (2b+1) = 2(a lor b)+1 (tag bit preserved by OR). *)
From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.
Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr sem_binary_operation sem_cast
        Mem.load Mem.store Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int field_offset PTree.get PTree.set].

Local Lemma sem_or_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Oor
    (Vlong n1) tlong (Vlong n2) tlong m = Some (Vlong (Int64.or n1 n2)).
Proof. intros. reflexivity. Qed.

Local Lemma tagged_orint_arith : forall a b,
  Int64.or (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1))
  = Int64.repr ((Z.lor a b) * 2 + 1).
Proof.
  intros a b.
  apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_or, !Int64.testbit_repr by lia.
  replace (a * 2 + 1) with (2 * a + 1) by lia.
  replace (b * 2 + 1) with (2 * b + 1) by lia.
  replace (Z.lor a b * 2 + 1) with (2 * Z.lor a b + 1) by lia.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - rewrite !Z.testbit_odd_0. reflexivity.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite !Z.testbit_odd_succ by lia.
    rewrite Z.lor_spec. reflexivity.
Qed.

Theorem verify_ORINT_correct :
    handler_correct handle_ORINT f_instr_ORINT
      (fun _ => None)
      (pre_and accu_is_long stack_head_is_long)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with the exact type expected by InstructVerificationProof.v *)
Theorem correct_ORINT :
    handler_correct (handle_instr ORINT) (clight_of ORINT)
      (error_message_of ORINT)
      (pre_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT).
Proof.
Admitted.
