(* ANDINT_correct.v -- clone of SUBINT with bitwise AND.
   C: s->accu = (long)((long)_t'2 & (long)_t'3); sp++.
   Tagged: (2a+1) & (2b+1) = 2(a land b)+1 (tag bit preserved by AND). *)
From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.
Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr sem_binary_operation sem_cast
        Mem.load Mem.store Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int field_offset PTree.get PTree.set].

Local Lemma sem_and_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Oand
    (Vlong n1) tlong (Vlong n2) tlong m = Some (Vlong (Int64.and n1 n2)).
Proof. intros. reflexivity. Qed.

Local Lemma tagged_andint_arith : forall a b,
  Int64.and (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1))
  = Int64.repr ((Z.land a b) * 2 + 1).
Proof.
  intros a b.
  apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_and, !Int64.testbit_repr by lia.
  replace (a * 2 + 1) with (2 * a + 1) by lia.
  replace (b * 2 + 1) with (2 * b + 1) by lia.
  replace (Z.land a b * 2 + 1) with (2 * Z.land a b + 1) by lia.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - rewrite !Z.testbit_odd_0. reflexivity.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite !Z.testbit_odd_succ by lia.
    rewrite Z.land_spec. reflexivity.
Qed.

Local Theorem verify_ANDINT_correct :
    handler_correct handle_ANDINT f_instr_ANDINT
      (fun _ => None)
      (pre_and accu_is_long stack_head_is_long)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

Import Bytecode.AST.

(* Wrapper: lift verify_ANDINT_correct to the dispatch-level type
   expected by InstructVerificationFineGrainedSpec. *)
Theorem correct_ANDINT :
    handler_correct (handle_instr ANDINT) (clight_of ANDINT)
      (error_message_of ANDINT)
      (pre_of ANDINT) (P_halt_of ANDINT) (P_ccall_of ANDINT).
Proof.
Admitted.
