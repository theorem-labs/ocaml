(* LTINT_correct.v -- Verification of the LTINT bytecode handler.
   C: s->accu = ((long)((long)_t'2 < (long)_t'3) << 1) + 1; sp++.
   If a < b: ((long)1 << 1) + 1 = 3 = tagged 1 = val_true.
   If a >= b: ((long)0 << 1) + 1 = 1 = tagged 0 = val_false.

   The Rocq handler uses val_bool (a <? b) which produces Val_int 1
   when a < b and Val_int 0 otherwise. The Clight code compares as
   longs via Olt (signed less-than). *)
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

Local Lemma sem_lt_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Olt
    (Vlong n1) tlong (Vlong n2) tlong m
    = Some (Val.of_bool (Int64.lt n1 n2)).
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

Local Lemma tagged_lt_result : forall (cond : bool),
  Int64.add (Int64.repr (if cond then 2 else 0)) (Int64.repr 1)
    = Int64.repr (if cond then 3 else 1).
Proof. intros. destruct cond; reflexivity. Qed.

(* tagged_lt_arith: signed less-than on tagged integers corresponds
   to Z.ltb on the untagged values.
   Int64.lt compares signed representations. When a*2+1 and b*2+1
   are in the Int64 signed range, signed(repr(x*2+1)) = x*2+1, and
   (a*2+1) < (b*2+1) iff a < b.  This holds for all values that
   fit in the OCaml value range (63-bit signed integers).
   Proved following the pattern of tagged_eq_arith in EQ_correct.v,
   using Int64.signed_repr under a signed-range precondition. *)
Local Lemma tagged_lt_arith : forall a b,
  Int64.min_signed <= a * 2 + 1 <= Int64.max_signed ->
  Int64.min_signed <= b * 2 + 1 <= Int64.max_signed ->
  Int64.lt (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1)) = Z.ltb a b.
Proof.
  intros a b Ha Hb.
  unfold Int64.lt.
  rewrite !Int64.signed_repr by lia.
  destruct (zlt (a * 2 + 1) (b * 2 + 1)); destruct (Z.ltb a b) eqn:Hlt.
  - reflexivity.
  - apply Z.ltb_nlt in Hlt. lia.
  - apply Z.ltb_lt in Hlt. lia.
  - reflexivity.
Qed.

Definition lt_int_range_pre (m : mem) (s : state) (ard : abs_rel_data) : Prop :=
  match s.(Machine.accu), s.(Machine.stack) with
  | Val_int a, Val_int b :: _ =>
      Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
      Int64.min_signed <= b * 2 + 1 <= Int64.max_signed /\
      int_vlong ard a /\
      int_vlong ard b
  | _, _ => False
  end.

Theorem verify_LTINT_correct :
    handler_correct handle_LTINT f_instr_LTINT
      (fun _ => None)
      (fun _ => lt_int_range_pre)
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

(* ================================================================== *)
(* Wrapper with canonical InstructSpec predicates                       *)
(* Abandoned for this pass: [verify_LTINT_correct] is still admitted, and
   weakening from canonical [pre_of LTINT] would require [signed_int_op_safe]
   for every state whose Clight body executes.  Clight execution only proves
   Vlong-representability, not the stronger [Val_int] shape and signed tagged
   range facts required by [signed_int_op_safe]. *)
(* ================================================================== *)

Import Bytecode.AST.

Theorem correct_LTINT :
    handler_correct (handle_instr LTINT) (clight_of LTINT)
      (error_message_of LTINT)
      (pre_of LTINT) (P_halt_of LTINT) (P_ccall_of LTINT).
Proof.
Admitted.
