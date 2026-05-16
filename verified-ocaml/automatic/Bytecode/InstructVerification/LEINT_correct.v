(* LEINT_correct.v -- Verification of the LEINT bytecode handler.
   C: s->accu = ((long)((long)_t'2 <= (long)_t'3) << 1) + 1; sp++.
   If le: ((long)1 << 1) + 1 = 3 = tagged 1 = val_true.
   If not le: ((long)0 << 1) + 1 = 1 = tagged 0 = val_false.

   The Rocq handler uses val_bool (a <=? b) which produces
   Val_int 1 (val_true) or Val_int 0 (val_false).
   The Clight code compares as signed longs via Ole. *)
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
        ptrofs_of_int field_offset PTree.get PTree.set
        Int64.cmp Int64.lt Int64.eq].

Local Lemma sem_le_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Ole
    (Vlong n1) tlong (Vlong n2) tlong m
    = Some (Val.of_bool (Int64.cmp Cle n1 n2)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_cast_bool_int_to_long : forall (cond : bool) m,
  sem_cast (Val.of_bool cond) tint tlong m
    = Some (Vlong (Int64.repr (if cond then 1 else 0))).
Proof. intros. destruct cond; reflexivity. Qed.

Local Lemma sem_shl_bool_long_1 : forall (cond : bool) m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong (Int64.repr (if cond then 1 else 0))) tlong
    (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.repr (if cond then 2 else 0))).
Proof. intros. destruct cond; reflexivity. Qed.

Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

Local Lemma tagged_bool_result : forall (cond : bool),
  Int64.add (Int64.repr (if cond then 2 else 0)) (Int64.repr 1)
    = Int64.repr (if cond then 3 else 1).
Proof. intros. destruct cond; reflexivity. Qed.

(* tagged_le_arith: Cle on tagged integers matches Z.leb under signed range.
   Int64.cmp Cle x y = negb (Int64.lt y x).
   Int64.lt compares signed representations.
   Under signed range, Int64.signed (repr (a*2+1)) = a*2+1. *)
Local Lemma tagged_le_arith : forall a b,
  Int64.min_signed <= a * 2 + 1 <= Int64.max_signed ->
  Int64.min_signed <= b * 2 + 1 <= Int64.max_signed ->
  Int64.cmp Cle (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1)) = Z.leb a b.
Proof.
  intros a b Ha Hb.
  unfold Int64.cmp, Int64.lt.
  rewrite !Int64.signed_repr by lia.
  destruct (Z.leb a b) eqn:Hleb.
  - apply Z.leb_le in Hleb.
    destruct (zlt (b * 2 + 1) (a * 2 + 1)); [lia | reflexivity].
  - apply Z.leb_gt in Hleb.
    destruct (zlt (b * 2 + 1) (a * 2 + 1)); [reflexivity | lia].
Qed.

Definition le_int_range_pre (m : mem) (s : state) (ard : abs_rel_data) : Prop :=
  match s.(Machine.accu), s.(Machine.stack) with
  | Val_int a, Val_int b :: _ =>
      Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
      Int64.min_signed <= b * 2 + 1 <= Int64.max_signed /\
      int_vlong ard a /\
      int_vlong ard b
  | _, _ => False
  end.

Theorem verify_LEINT_correct :
    handler_correct handle_LEINT f_instr_LEINT
      (fun _ => None)
      (fun _ => le_int_range_pre)
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

(* ================================================================== *)
(* Wrapper with canonical InstructSpec predicates                       *)
(* Abandoned for this pass: [verify_LEINT_correct] is still admitted, and
   canonical [pre_of LEINT] is not enough for [handler_correct_weaken]'s
   unconditional [signed_int_op_safe] obligation.  Successful Clight execution
   can establish Vlong operands, but not that the abstract operands are both
   [Val_int] with the required signed tagged bounds. *)
(* ================================================================== *)

Import Bytecode.AST.

Theorem correct_LEINT :
    handler_correct (handle_instr LEINT) (clight_of LEINT)
      (error_message_of LEINT)
      (pre_of LEINT) (P_halt_of LEINT) (P_ccall_of LEINT).
Proof.
Admitted.
