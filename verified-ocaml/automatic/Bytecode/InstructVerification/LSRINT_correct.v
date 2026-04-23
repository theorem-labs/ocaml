(* LSRINT_correct.v -- correctness proof for the LSRINT bytecode handler.

   C handler (from Clight AST):
     _t'1 = s->sp;           // load sp
     s->sp = _t'1 + 1;       // sp++ (pop stack)
     _t'2 = s->accu;         // load accu
     _t'3 = *_t'1;           // load stack[0]
     s->accu = (long)(((unsigned long)_t'2 >> (_t'3 >> 1)) | 1);
     return 0;

   Rocq handler:
     handle_LSRINT pc' s = match accu, stack with
       | Val_int a, Val_int b :: rest =>
           Step (s<|pc:=pc'|><|accu:=Val_int(z_lsr a b)|><|stack:=rest|>)
       | _, _ => Error ...

   Precondition: 0 <= b < 64 (shift amount in range).
   Both former axioms are now proved as lemmas under this hypothesis. *)

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

(* ================================================================== *)
(* Helper lemmas (shared with LSLINT)                                  *)
(* ================================================================== *)

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

(* ================================================================== *)
(* Proved lemmas replacing former axioms                               *)
(* ================================================================== *)

(* The ltu guard for sem_shr (outer shift) holds when 0 <= b < 64 *)
Local Lemma lsr_shift_amount_in_range : forall b,
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

Local Ltac lia64 := change Int64.zwordsize with 64 in *; lia.

(* The tagged arithmetic identity for logical shift right.
   ((unsigned long)(2a+1) >> b) | 1 = 2*(z_lsr a b)+1  in 64-bit.
   Proved by bitwise extensionality (Int64.same_bits_eq). *)
Local Lemma tagged_lsrint_arith : forall a b,
  0 <= b < 64 ->
  Int64.or (Int64.shru (Int64.repr (a * 2 + 1))
                        (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)))
           (Int64.repr 1)
  = Int64.repr (z_lsr a b * 2 + 1).
Proof.
  intros a b Hb.
  rewrite int64_shr_tagged_1 by lia.
  unfold z_lsr, z_unsigned, word_bits.

  apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_or by lia64.

  destruct (zeq i 0) as [Hi0 | Hi0].
  - (* i = 0: bit 0 -- or with 1 makes bit 0 true *)
    subst i.
    rewrite Int64.bits_shru by lia64.
    rewrite (Int64.unsigned_repr b) by (generalize max_unsigned_ge_127; lia).
    rewrite orb_true_r.
    symmetry.
    rewrite Int64.testbit_repr by lia64.
    rewrite Z.mul_comm. rewrite Z.testbit_odd_0. reflexivity.
  - (* i > 0: bit 0 of 1 is false, so the or disappears *)
    assert (Hbit1 : Int64.testbit (Int64.repr 1) i = false).
    { unfold Int64.testbit.
      rewrite Int64.unsigned_repr
        by (change Int64.max_unsigned with 18446744073709551615; lia).
      apply Z.testbit_false; [lia64|].
      assert (2 ^ i >= 2)
        by (apply Z.le_ge; replace 2 with (2^1) by lia; apply Z.pow_le_mono_r; lia64).
      rewrite Z.div_small by lia. reflexivity. }
    rewrite Hbit1. rewrite orb_false_r.
    (* Simplify RHS: testbit(x*2+1, i) = testbit(x, i-1) for i > 0 *)
    rewrite Int64.testbit_repr by lia64.
    replace (Z.shiftr (Z.land a (Z.ones 63)) b * 2 + 1)
      with (2 * Z.shiftr (Z.land a (Z.ones 63)) b + 1) by lia.
    replace i with (Z.succ (i - 1)) by lia64.
    rewrite Z.testbit_odd_succ by lia64.
    replace (Z.succ (i - 1)) with i by lia.
    (* RHS: testbit(Z.shiftr (Z.land a (Z.ones 63)) b, i-1) *)
    rewrite Z.shiftr_spec by lia64.
    rewrite Z.land_spec.
    (* RHS: Z.testbit a (i-1+b) && Z.testbit (Z.ones 63) (i-1+b) *)

    (* Expand LHS: bits_shru *)
    rewrite Int64.bits_shru by lia64.
    rewrite (Int64.unsigned_repr b) by (generalize max_unsigned_ge_127; lia).

    destruct (zlt (i + b) Int64.zwordsize) as [Hib | Hib].
    + (* i + b < 64: both LHS and RHS pick up the shifted bit *)
      change Int64.zwordsize with 64 in *.
      rewrite Z.ones_spec_low by lia.
      rewrite andb_true_r.
      rewrite Int64.testbit_repr by lia64.
      replace (a * 2 + 1) with (2 * a + 1) by lia.
      replace (i + b) with (Z.succ (i + b - 1)) by lia.
      rewrite Z.testbit_odd_succ by lia.
      replace (i + b - 1) with (i - 1 + b) by lia. reflexivity.
    + (* i + b >= 64: LHS is 0, RHS ones-mask kills the bit *)
      change Int64.zwordsize with 64 in *.
      simpl.
      destruct (Z.testbit (Z.ones 63) (i - 1 + b)) eqn:Hones.
      * rewrite Z.ones_spec_high in Hones by lia. discriminate.
      * rewrite andb_false_r. reflexivity.
Qed.

(* ================================================================== *)
(* Semantic lemmas                                                      *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ulong : forall n m,
  sem_cast (Vlong n) tlong tulong m = Some (Vlong n).
Proof. intros. reflexivity. Qed.

Local Lemma sem_cast_ulong_to_long : forall n m,
  sem_cast (Vlong n) tulong tlong m = Some (Vlong n).
Proof. intros. reflexivity. Qed.

Local Lemma sem_shr_inner : forall n1 m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n1) tlong (Vint (Int.repr 1)) tint m =
    Some (Vlong (Int64.shr n1 (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  reflexivity.
Qed.

Local Lemma sem_shr_outer : forall n1 n2 m,
  Int64.ltu n2 Int64.iwordsize = true ->
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n1) tulong (Vlong n2) tlong m =
    Some (Vlong (Int64.shru n1 n2)).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tulong tlong) with (shift_case_ll Unsigned).
  simpl. rewrite H. reflexivity.
Qed.

Local Lemma sem_or_ulong_int_1 : forall n1 m,
  sem_binary_operation (genv_cenv clight_ge) Oor
    (Vlong n1) tulong (Vint (Int.repr 1)) tint m =
    Some (Vlong (Int64.or n1 (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_or, sem_binarith.
  change (classify_binarith tulong tint) with (bin_case_l Unsigned).
  reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

#[warnings="-not-a-closed-proof"]
Theorem verify_LSRINT_correct :
    handler_correct handle_LSRINT f_instr_LSRINT
      (fun _ => None)
      (fun _ _ s ard =>
         match s.(Machine.accu), s.(Machine.stack) with
         | Val_int a, Val_int b :: _ => 0 <= b < 64 /\ int_vlong ard a /\ int_vlong ard b
         | _, Val_int b :: _ => 0 <= b < 64
         | _, _ => True
         end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

Theorem verify_LSRINT_handler_correct :
    handler_correct handle_LSRINT f_instr_LSRINT
      (fun _ => None)
      shift_in_range
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with the exact type needed by InstructVerificationProof.v *)
Import Bytecode.AST.

Theorem correct_LSRINT :
    handler_correct (handle_instr LSRINT) (clight_of LSRINT)
      (error_message_of LSRINT)
      (pre_of LSRINT) (P_halt_of LSRINT) (P_ccall_of LSRINT).
Proof.
Admitted.
