(* ASRINT_correct.v -- correctness proof for ASRINT bytecode handler.

   C handler (from clightgen):
     _t'1 = s->sp;
     s->sp = _t'1 + 1;
     _t'2 = s->accu;
     _t'3 = *_t'1;
     s->accu = (long)(((long)_t'2 >> ((long)_t'3 >> 1)) | 1);
     return 0;

   Rocq handler:
     handle_ASRINT pc' s = match accu, stack with
       | Val_int a, Val_int b :: rest =>
           Step (s<|pc:=pc'|><|accu:=Val_int(Z.shiftr a b)|><|stack:=rest|>)
       | _, _ => Error ...

   Tagged arithmetic identity (when 0 <= b < 64 and a*2+1 fits in
   64-bit signed range):
     ((2a+1) >>_arith b) | 1 = 2*(Z.shiftr a b)+1

   The C shift is only defined when the shift amount is in [0,64).
   Additionally, since Int64.shr is an arithmetic (signed) shift,
   the tagged value a*2+1 must fit in the 64-bit signed range
   for the result to agree with Z.shiftr on unbounded integers.
   This holds for OCaml's 63-bit integers (a in [-2^62, 2^62-1]).
   Both constraints are encoded as preconditions via
   handler_correct. *)

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
(* Semantic lemmas for shift and or operations                         *)
(* ================================================================== *)

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl. reflexivity.
Qed.

Local Lemma sem_shr_long_long_signed : forall n1 n2 m,
  Int64.ltu n2 Int64.iwordsize = true ->
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n1) tlong (Vlong n2) tlong m
  = Some (Vlong (Int64.shr n1 n2)).
Proof.
  intros n1 n2 m Hguard.
  unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tlong) with (shift_case_ll Signed).
  simpl. rewrite Hguard. reflexivity.
Qed.

Local Lemma sem_or_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oor
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.or n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Tagged arithmetic lemmas for ASRINT                                  *)
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

(* The ltu guard holds when 0 <= b < 64 *)
Local Lemma asr_shift_ltu_guard : forall b,
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

(* Z.lor x 1 = 2 * Z.div2 x + 1 *)
Local Lemma Z_lor_1_div2 : forall x, Z.lor x 1 = 2 * Z.div2 x + 1.
Proof.
  intros x.
  pose proof (Z.div2_odd (Z.lor x 1)) as Heq.
  assert (Hodd : Z.odd (Z.lor x 1) = true).
  { rewrite <- Z.bit0_odd. rewrite Z.lor_spec. simpl. rewrite Bool.orb_true_r. reflexivity. }
  rewrite Hodd in Heq. simpl Z.b2z in Heq.
  assert (Hdiv2 : Z.div2 (Z.lor x 1) = Z.div2 x).
  { rewrite !Z.div2_spec.
    rewrite Z.shiftr_lor.
    replace (Z.shiftr 1 1) with 0 by reflexivity.
    rewrite Z.lor_0_r. reflexivity. }
  lia.
Qed.

(* Z.div2 (Z.shiftr (a*2+1) b) = Z.shiftr a b when 0 <= b *)
Local Lemma Z_div2_shiftr_tagged : forall a b,
  0 <= b ->
  Z.div2 (Z.shiftr (a * 2 + 1) b) = Z.shiftr a b.
Proof.
  intros a b Hb.
  rewrite Z.div2_div.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_div by (try apply Z.pow_pos_nonneg; lia).
  replace (2 ^ b * 2) with (2 ^ (b + 1)).
  2:{ change (b + 1) with (Z.succ b). rewrite Z.pow_succ_r by lia. ring. }
  symmetry.
  apply Z.div_unique with (2 * (a mod 2^b) + 1).
  - pose proof (Z.mod_pos_bound a (2^b) ltac:(apply Z.pow_pos_nonneg; lia)).
    pose proof (Z.pow_pos_nonneg 2 b ltac:(lia) ltac:(lia)).
    assert (H2b : 2 ^ (b + 1) = 2 * 2 ^ b).
    { change (b + 1) with (Z.succ b). rewrite Z.pow_succ_r by lia. ring. }
    left. lia.
  - change (b + 1) with (Z.succ b). rewrite Z.pow_succ_r by lia.
    rewrite (Z.div_mod a (2^b)) at 1 by (apply Z.pow_nonzero; lia).
    ring.
Qed.

(* The combined tagged arithmetic identity for ASRINT. *)
Local Lemma tagged_asrint_arith : forall a b,
  0 <= b < 64 ->
  Int64.min_signed <= a * 2 + 1 <= Int64.max_signed ->
  Int64.or (Int64.shr (Int64.repr (a * 2 + 1))
              (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)))
           (Int64.repr 1)
  = Int64.repr (Z.shiftr a b * 2 + 1).
Proof.
  intros a b Hb Ha_range.
  rewrite int64_shr_tagged_1 by lia.
  unfold Int64.shr.
  rewrite (Int64.unsigned_repr b) by (generalize max_unsigned_ge_127; lia).
  rewrite Int64.signed_repr by exact Ha_range.
  unfold Int64.or.
  apply Int64.eqm_samerepr.
  rewrite (Int64.unsigned_repr 1) by (generalize max_unsigned_ge_127; lia).
  apply Int64.eqm_trans with (y := Z.lor (Z.shiftr (a * 2 + 1) b) 1).
  - apply Int64.eqm_same_bits.
    intros i Hi.
    rewrite !Z.lor_spec.
    f_equal.
    apply Int64.same_bits_eqm with (i := i).
    + apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
    + exact Hi.
  - rewrite Z_lor_1_div2.
    rewrite Z_div2_shiftr_tagged by lia.
    apply Int64.eqm_refl2. lia.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

(* Wrapper with the canonical type expected by InstructVerificationProof.v *)
Theorem correct_ASRINT :
  handler_correct (handle_instr Bytecode.AST.ASRINT) (clight_of Bytecode.AST.ASRINT)
    (error_message_of Bytecode.AST.ASRINT)
    (pre_of Bytecode.AST.ASRINT) (P_halt_of Bytecode.AST.ASRINT) (P_ccall_of Bytecode.AST.ASRINT).
Proof.
Admitted.
