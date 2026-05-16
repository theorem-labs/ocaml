(* SUBINT_correct.v -- clone of ADDINT with subtraction.
   C: (long)_t'2 - (long)_t'3 + 1. Tagged: (a*2+1) - (b*2+1) + 1 = (a-b)*2+1. *)
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

Local Lemma sem_sub_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vlong n1) tlong (Vlong n2) tlong m = Some (Vlong (Int64.sub n1 n2)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

Local Lemma eqm64_sub : forall x x' y y',
  Int64.eqm x x' -> Int64.eqm y y' -> Int64.eqm (x - y) (x' - y').
Proof. intros x x' y y' [kx Hx] [ky Hy]. exists (kx - ky)%Z. lia. Qed.

Local Lemma tagged_subint_arith : forall a b,
  Int64.add (Int64.sub (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1))) (Int64.repr 1)
  = Int64.repr ((a - b) * 2 + 1).
Proof.
  intros a b.
  unfold Int64.add, Int64.sub.
  apply Int64.eqm_samerepr.
  replace ((a - b) * 2 + 1)%Z with ((a * 2 + 1) - (b * 2 + 1) + 1)%Z by lia.
  apply Int64.eqm_add.
  - apply Int64.eqm_unsigned_repr_l.
    apply eqm64_sub; apply Int64.eqm_unsigned_repr_l; apply Int64.eqm_refl.
  - apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_refl.
Qed.

(* Wrapper with the canonical type expected by InstructVerificationProof.v *)
Theorem correct_SUBINT :
  handler_correct (handle_instr Bytecode.AST.SUBINT) (clight_of Bytecode.AST.SUBINT)
    (error_message_of Bytecode.AST.SUBINT)
    (pre_of Bytecode.AST.SUBINT) (P_halt_of Bytecode.AST.SUBINT) (P_ccall_of Bytecode.AST.SUBINT).
Proof.
Admitted.

