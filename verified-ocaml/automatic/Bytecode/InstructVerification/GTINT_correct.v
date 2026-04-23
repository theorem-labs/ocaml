(* GTINT_correct.v -- Verification of the GTINT bytecode handler.
   C: s->accu = ((long)((long)_t'2 > (long)_t'3) << 1) + 1; sp++.
   If a > b: ((long)1 << 1) + 1 = 3 = tagged 1 = val_true.
   If not:   ((long)0 << 1) + 1 = 1 = tagged 0 = val_false.

   The Rocq handler uses val_bool (a >? b) which is Val_int 1 when
   a > b, Val_int 0 otherwise.
   The Clight code compares as longs via Ogt (signed greater-than).
   CompCert implements Ogt as Int64.cmp Cgt n1 n2 = Int64.lt n2 n1. *)
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

(* sem_binary_operation for Ogt on two Vlong values.
   CompCert: Ogt -> sem_cmp Cgt -> cmp_default path ->
   sem_binarith with bin_case_l Signed ->
   Int64.cmp Cgt n1 n2 = Int64.lt n2 n1 (swap operands). *)
Local Lemma sem_gt_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Ogt
    (Vlong n1) tlong (Vlong n2) tlong m
    = Some (Val.of_bool (Int64.lt n2 n1)).
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

Local Lemma tagged_gt_result : forall (cond : bool),
  Int64.add (Int64.repr (if cond then 2 else 0)) (Int64.repr 1)
    = Int64.repr (if cond then 3 else 1).
Proof. intros. destruct cond; reflexivity. Qed.

(* Key arithmetic lemma: signed comparison of tagged integers
   preserves the Z ordering.
   Int64.lt (repr (b*2+1)) (repr (a*2+1)) = Z.ltb b a

   Int64.lt uses signed comparison.  Under the range precondition
   Int64.min_signed <= x*2+1 <= Int64.max_signed, Int64.signed_repr
   gives signed(repr(x*2+1)) = x*2+1, and the comparison reduces
   to a simple Z inequality. *)
Local Lemma tagged_gt_arith : forall a b,
  Int64.min_signed <= a * 2 + 1 <= Int64.max_signed ->
  Int64.min_signed <= b * 2 + 1 <= Int64.max_signed ->
  Int64.lt (Int64.repr (b * 2 + 1)) (Int64.repr (a * 2 + 1)) = Z.ltb b a.
Proof.
  intros a b Ha Hb.
  unfold Int64.lt.
  rewrite !Int64.signed_repr by lia.
  destruct (Z.ltb b a) eqn:Hltb.
  - apply Z.ltb_lt in Hltb.
    destruct (zlt (b * 2 + 1) (a * 2 + 1)); [reflexivity | lia].
  - apply Z.ltb_ge in Hltb.
    destruct (zlt (b * 2 + 1) (a * 2 + 1)); [lia | reflexivity].
Qed.

(* Z.gtb a b = Z.ltb b a *)
Local Lemma Z_gtb_ltb : forall a b, (a >? b)%Z = (b <? a)%Z.
Proof. intros. apply Z.gtb_ltb. Qed.

Definition gtint_range_pre (m : mem) (s : state) (ard : abs_rel_data) : Prop :=
  match s.(Machine.accu), s.(Machine.stack) with
  | Val_int a, Val_int b :: _ =>
      Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
      Int64.min_signed <= b * 2 + 1 <= Int64.max_signed /\
      int_vlong ard a /\
      int_vlong ard b
  | _, _ => False
  end.

Theorem verify_GTINT_correct :
    handler_correct handle_GTINT f_instr_GTINT
      (fun _ => None)
      (fun _ => gtint_range_pre)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

Theorem verify_GTINT_handler_correct :
    handler_correct handle_GTINT f_instr_GTINT
      (fun _ => None)
      signed_int_op_safe
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* ================================================================== *)
(* Wrapper with canonical InstructSpec predicates                       *)
(* ================================================================== *)

Theorem correct_GTINT :
    handler_correct (handle_instr Bytecode.AST.GTINT) (clight_of Bytecode.AST.GTINT)
      (error_message_of Bytecode.AST.GTINT)
      (pre_of Bytecode.AST.GTINT) (P_halt_of Bytecode.AST.GTINT) (P_ccall_of Bytecode.AST.GTINT).
Proof.
Admitted.

