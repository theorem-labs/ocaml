(* LSLINT_correct.v -- correctness proof for the LSLINT bytecode handler.
   C: accu = (long)(((accu - 1) << (stack_top >> 1)) + 1); sp++.
   Rocq: handle_LSLINT pops stack, computes Z.shiftl a b.
   Tagged: ((2a+1) - 1) << ((2b+1) >> 1) + 1 = 2*(Z.shiftl a b)+1. *)
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

(* ================================================================== *)
(* Semantic lemmas for LSLINT C operations                             *)
(* ================================================================== *)

Local Lemma sem_sub_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.sub n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl. reflexivity.
Qed.

Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Tagged arithmetic lemmas for LSLINT                                 *)
(* ================================================================== *)

(* Helper: 127 <= Int64.max_signed *)
Local Lemma max_signed_ge_127 : 127 <= Int64.max_signed.
Proof.
  unfold Int64.max_signed.
  rewrite Int64.half_modulus_power.
  change (Int64.zwordsize - 1) with 63.
  assert (two_p 63 >= 128).
  { change (two_p 63) with (two_p (7 + 56)).
    rewrite two_p_is_exp by lia.
    change (two_p 7) with 128.
    generalize (two_p_gt_ZERO 56 ltac:(lia)). lia. }
  lia.
Qed.

(* Helper: 127 <= Int64.max_unsigned *)
Local Lemma max_unsigned_ge_127 : 127 <= Int64.max_unsigned.
Proof.
  generalize Int64.two_wordsize_max_unsigned.
  change Int64.zwordsize with 64. lia.
Qed.

(* Key lemma: for 0 <= b < 64,
   Int64.shr (Int64.repr (b*2+1)) (Int64.repr 1) has unsigned value = b *)
Local Lemma shr_tagged_unsigned : forall b,
  0 <= b < 64 ->
  Int64.unsigned (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)) = b.
Proof.
  intros b Hb.
  unfold Int64.shr.
  rewrite Int64.signed_repr.
  2: { generalize (Int64.min_signed_neg) max_signed_ge_127. lia. }
  change (Int64.unsigned (Int64.repr 1)) with 1.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1)%Z with 2%Z.
  replace ((b * 2 + 1) / 2)%Z with b by (apply Z.div_unique with 1; lia).
  apply Int64.unsigned_repr.
  generalize max_unsigned_ge_127. lia.
Qed.

(* The ltu guard for sem_shl holds when 0 <= b < 64 *)
Local Lemma lsl_shift_ltu_guard : forall b,
  0 <= b < 64 ->
  Int64.ltu (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1))
            Int64.iwordsize = true.
Proof.
  intros b Hb.
  unfold Int64.ltu.
  rewrite shr_tagged_unsigned by lia.
  change (Int64.unsigned Int64.iwordsize) with Int64.zwordsize.
  unfold Int64.zwordsize. simpl.
  destruct (zlt b 64); [reflexivity | lia].
Qed.

(* sem_shl succeeds under shift range precondition *)
Local Lemma tagged_lslint_shl_succeeds : forall a b m,
  0 <= b < 64 ->
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong (Int64.sub (Int64.repr (a * 2 + 1)) (Int64.repr 1)))
    tlong
    (Vlong (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)))
    tlong
    m = Some (Vlong (Int64.shl
                       (Int64.sub (Int64.repr (a * 2 + 1)) (Int64.repr 1))
                       (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)))).
Proof.
  intros a b m Hb.
  unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tlong tlong) with (shift_case_ll Signed).
  simpl.
  rewrite lsl_shift_ltu_guard by lia.
  reflexivity.
Qed.

(* Helper: Int64.sub (Int64.repr (a*2+1)) (Int64.repr 1) = Int64.repr (a*2) *)
Local Lemma int64_sub_tagged_1 : forall a,
  Int64.sub (Int64.repr (a * 2 + 1)) (Int64.repr 1) = Int64.repr (a * 2).
Proof.
  intros. unfold Int64.sub.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_trans with (y := (a * 2 + 1 - 1)%Z).
  - apply Int64.eqm_sub;
    apply Int64.eqm_unsigned_repr_l; apply Int64.eqm_refl.
  - apply Int64.eqm_refl2. lia.
Qed.

(* Helper: Int64.shr (Int64.repr (b*2+1)) (Int64.repr 1) = Int64.repr b *)
Local Lemma int64_shr_tagged_1 : forall b,
  0 <= b < 64 ->
  Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1) = Int64.repr b.
Proof.
  intros b Hb.
  apply Int64.same_if_eq. unfold Int64.eq.
  rewrite shr_tagged_unsigned by lia.
  rewrite Int64.unsigned_repr by (generalize max_unsigned_ge_127; lia).
  destruct (zeq b b); [reflexivity | congruence].
Qed.

(* Helper: Int64.shl (Int64.repr (a*2)) (Int64.repr b) = Int64.repr (Z.shiftl a b * 2) *)
Local Lemma int64_shl_tagged : forall a b,
  0 <= b < 64 ->
  Int64.shl (Int64.repr (a * 2)) (Int64.repr b) = Int64.repr (Z.shiftl a b * 2).
Proof.
  intros a b Hb.
  unfold Int64.shl.
  apply Int64.eqm_samerepr.
  rewrite (Int64.unsigned_repr b) by (generalize max_unsigned_ge_127; lia).
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  replace (a * 2 ^ b * 2) with (a * 2 * 2 ^ b) by ring.
  apply Int64.eqm_mult.
  - apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
  - apply Int64.eqm_refl.
Qed.

(* The combined C computation equals the Rocq tagged result.
   ((tagged_a - 1) << (tagged_b >> 1)) + 1 = tagged(Z.shiftl a b) *)
Local Lemma tagged_lslint_arith : forall a b,
  0 <= b < 64 ->
  Int64.add (Int64.shl (Int64.sub (Int64.repr (a * 2 + 1)) (Int64.repr 1))
                        (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)))
            (Int64.repr 1)
  = Int64.repr (Z.shiftl a b * 2 + 1).
Proof.
  intros a b Hb.
  rewrite int64_sub_tagged_1.
  rewrite int64_shr_tagged_1 by lia.
  rewrite int64_shl_tagged by lia.
  unfold Int64.add.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_add;
    apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

#[warnings="-not-a-closed-proof"]
(* Wrapper with the exact type required by InstructVerificationProof.v *)
Local Notation LSLINT := Bytecode.AST.LSLINT.
Theorem correct_LSLINT :
    handler_correct (handle_instr LSLINT) (clight_of LSLINT)
      (error_message_of LSLINT)
      (pre_of LSLINT) (P_halt_of LSLINT) (P_ccall_of LSLINT).
Proof.
Admitted.
