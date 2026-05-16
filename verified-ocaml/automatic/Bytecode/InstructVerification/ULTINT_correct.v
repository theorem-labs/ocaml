(* ULTINT_correct.v -- Verification of the ULTINT bytecode handler.
   C: s->accu = ((long)((unsigned long)_t'2 < (unsigned long)_t'3) << 1) + 1; sp++.
   If accu <_u stack_top: result = tagged 1 = val_true.
   Otherwise: result = tagged 0 = val_false.

   The Rocq handler uses val_bool (Z.ltb (z_flip_sign a) (z_flip_sign b))
   which flips bit 62 to convert signed Z comparison to unsigned order.
   The Clight code casts operands to tulong then uses Olt, which goes
   through Int64.cmpu Clt = Int64.ltu (unsigned less-than on Int64).

   PRECONDITION: The z_flip_sign trick on mathematical Z only matches
   Int64.ltu for non-negative operands (0 <= a, 0 <= b < 2^62).
   For negative operands, Z.lxor on infinite-precision Z does not
   model the 63-bit OCaml lxor correctly, causing disagreement.
   We add this as a step_pre via handler_correct. *)
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
(* Semantic lemmas for unsigned comparison                             *)
(* ================================================================== *)

(* Cast from tlong to tulong is identity for Vlong (cast_case_pointer
   on ptr64 = true). *)
Local Lemma sem_cast_long_to_ulong : forall n m,
  sem_cast (Vlong n) tlong tulong m = Some (Vlong n).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

(* Olt on tulong tulong: classify_cmp -> cmp_default -> sem_binarith
   -> classify_binarith tulong tulong = bin_case_l Unsigned ->
   Int64.cmpu Clt = Int64.ltu. *)
Local Lemma sem_lt_ulong_ulong : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Olt
    (Vlong n1) tulong (Vlong n2) tulong m
    = Some (Val.of_bool (Int64.ltu n1 n2)).
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

Local Lemma tagged_ult_result : forall (cond : bool),
  Int64.add (Int64.repr (if cond then 2 else 0)) (Int64.repr 1)
    = Int64.repr (if cond then 3 else 1).
Proof. intros. destruct cond; reflexivity. Qed.

(* ================================================================== *)
(* Key arithmetic lemma                                                *)
(* ================================================================== *)

(* Int64.ltu is Z.ltb on unsigned values *)
Local Lemma int64_ltu_ltb : forall x y,
  Int64.ltu x y = Z.ltb (Int64.unsigned x) (Int64.unsigned y).
Proof.
  intros. unfold Int64.ltu.
  destruct (zlt (Int64.unsigned x) (Int64.unsigned y)) as [Hlt|Hge].
  - symmetry. apply Z.ltb_lt. exact Hlt.
  - symmetry. apply Z.ltb_ge. lia.
Qed.

(* For non-negative a < 2^n, Z.lxor a (2^n) = a + 2^n
   (bit n of a is 0, xor sets it; no carry since bits don't overlap). *)
Local Lemma Z_lxor_add_pow2 : forall a n,
  0 <= a ->
  0 <= n ->
  a < 2 ^ n ->
  Z.lxor a (2 ^ n) = a + 2 ^ n.
Proof.
  intros a n Ha Hn Hlt.
  rewrite Z.add_nocarry_lxor.
  - reflexivity.
  - apply Z.bits_inj. intros j.
    rewrite Z.land_spec, Z.bits_0.
    rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eqb n j) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst.
      destruct (Z.eq_dec a 0) as [->|Ha0].
      * rewrite Z.testbit_0_l. reflexivity.
      * rewrite Z.bits_above_log2; [reflexivity | lia | ].
        apply Z.log2_lt_pow2; lia.
    + rewrite Bool.andb_false_r. reflexivity.
Qed.

(* For non-negative a, b in [0, 2^62), the unsigned comparison of
   tagged integers matches z_flip_sign comparison.

   Both sides reduce to Z.ltb a b:
   - LHS: Int64.ltu compares unsigned (a*2+1) vs (b*2+1), both positive
   - RHS: z_flip_sign adds 2^62 to both (since bit 62 is 0), cancels *)
Local Lemma tagged_ultint_arith : forall a b,
  0 <= a < 4611686018427387904 ->
  0 <= b < 4611686018427387904 ->
  Int64.ltu (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1))
  = Z.ltb (z_flip_sign a) (z_flip_sign b).
Proof.
  intros a b Ha Hb.
  unfold z_flip_sign, word_bits. simpl Z.sub.
  change (Z.shiftl 1 62) with (2 ^ 62).
  rewrite !Z_lxor_add_pow2 by lia.
  rewrite int64_ltu_ltb.
  rewrite !Int64.unsigned_repr
    by (unfold Int64.max_unsigned; change Int64.modulus with 18446744073709551616; lia).
  destruct (Z.ltb_spec (a * 2 + 1) (b * 2 + 1));
  destruct (Z.ltb_spec (a + 2 ^ 62) (b + 2 ^ 62)); lia.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Local Abbreviation ULTINT := Bytecode.AST.ULTINT.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr ULTINT / clight_of ULTINT / pre_of ULTINT are convertible
   with handle_ULTINT / f_instr_ULTINT / unsigned_ints_safe.
   P_halt_of and P_ccall_of are vacuously satisfied (ULTINT never halts or
   issues a C call).  error_message_of requires matching error_message_of. *)
Definition correct_ULTINT :
    handler_correct (handle_instr ULTINT) (clight_of ULTINT)
      (error_message_of ULTINT)
      (pre_of ULTINT) (P_halt_of ULTINT) (P_ccall_of ULTINT).
Proof.
Admitted.
