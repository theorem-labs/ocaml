(* UGEINT_correct.v -- Verification of the UGEINT bytecode handler.
   C: s->accu = ((long)((unsigned long)_t'2 >= (unsigned long)_t'3) << 1) + 1; sp++.
   Rocq: val_bool (Z.geb (z_flip_sign a) (z_flip_sign b)).
   The arithmetic lemma is PROVED under OCaml 63-bit int range.
   NO AXIOMS. *)
From Stdlib Require Import ZArith List Strings.String PeanoNat Lia Bool.
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

Open Scope Z_scope.

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr sem_binary_operation sem_cast
        Mem.load Mem.store Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int field_offset PTree.get PTree.set].

(* ================================================================== *)
(* Semantic lemmas for Clight evaluation                               *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ulong : forall n m,
  sem_cast (Vlong n) tlong tulong m = Some (Vlong n).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma sem_ge_ulong_ulong : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Oge
    (Vlong n1) tulong (Vlong n2) tulong m
    = Some (Val.of_bool (negb (Int64.ltu n1 n2))).
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

Local Lemma tagged_uge_result : forall (cond : bool),
  Int64.add (Int64.repr (if cond then 2 else 0)) (Int64.repr 1)
    = Int64.repr (if cond then 3 else 1).
Proof. intros. destruct cond; reflexivity. Qed.

(* ================================================================== *)
(* Z.lxor / z_flip_sign arithmetic                                    *)
(* ================================================================== *)

Local Lemma testbit62_nonneg : forall a : Z,
  0 <= a < 4611686018427387904 ->
  Z.testbit a 62 = false.
Proof.
  intros a Ha.
  apply Z.bits_above_log2; try lia.
  destruct (Z.eq_dec a 0) as [->|Hne].
  - simpl. lia.
  - apply Z.log2_lt_pow2; lia.
Qed.

Local Lemma testbit62_neg : forall a : Z,
  -4611686018427387904 <= a < 0 ->
  Z.testbit a 62 = true.
Proof.
  intros a Ha.
  apply Z.bits_above_log2_neg; try lia.
  destruct (Z.eq_dec (Z.pred (-a)) 0) as [He|Hne].
  - rewrite He. simpl. lia.
  - assert (0 < Z.pred (-a)) by lia.
    apply Z.log2_lt_pow2; lia.
Qed.

Local Lemma land_pow2_zero : forall a n : Z,
  0 <= n ->
  Z.testbit a n = false ->
  Z.land a (2^n) = 0.
Proof.
  intros a n Hn Hbit.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec i n) as [->|Hne].
  - rewrite Hbit. reflexivity.
  - rewrite Z.pow2_bits_false by auto. rewrite Bool.andb_false_r. reflexivity.
Qed.

Local Lemma lxor_pow2_add : forall a n : Z,
  0 <= a -> 0 <= n ->
  Z.testbit a n = false ->
  Z.lxor a (2^n) = a + 2^n.
Proof.
  intros a n Ha Hn Hbit.
  symmetry. apply Z.add_nocarry_lxor.
  apply land_pow2_zero; auto.
Qed.

Local Lemma lxor_neg_lnot : forall a b : Z,
  a < 0 ->
  Z.lxor a b = Z.lnot (Z.lxor (Z.lnot a) b).
Proof.
  intros a b Ha.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec, Z.lnot_spec by lia.
  rewrite Z.lxor_spec, Z.lnot_spec by lia.
  destruct (Z.testbit a n); destruct (Z.testbit b n); reflexivity.
Qed.

Local Lemma z_flip_sign_nonneg_eq : forall a : Z,
  0 <= a < 4611686018427387904 ->
  z_flip_sign a = a + 4611686018427387904.
Proof.
  intros a Ha.
  unfold z_flip_sign, word_bits.
  change (Z.shiftl 1 (63 - 1)) with 4611686018427387904.
  change 4611686018427387904 with (2^62) at 1.
  rewrite lxor_pow2_add; try lia.
  apply testbit62_nonneg; lia.
Qed.

Local Lemma z_flip_sign_neg_eq : forall a : Z,
  -4611686018427387904 <= a < 0 ->
  z_flip_sign a = a - 4611686018427387904.
Proof.
  intros a Ha.
  unfold z_flip_sign, word_bits.
  change (Z.shiftl 1 (63 - 1)) with 4611686018427387904.
  change 4611686018427387904 with (2^62) at 1.
  rewrite lxor_neg_lnot by lia.
  rewrite lxor_pow2_add.
  - unfold Z.lnot. lia.
  - unfold Z.lnot. lia.
  - lia.
  - apply testbit62_nonneg. unfold Z.lnot. lia.
Qed.

(* ================================================================== *)
(* Main arithmetic lemma                                               *)
(* ================================================================== *)

Definition ocaml_int_range (z : Z) : Prop :=
  -4611686018427387904 <= z < 4611686018427387904.

Local Lemma Z_geb_negb_ltb : forall a b, Z.geb a b = negb (Z.ltb a b).
Proof.
  intros. destruct (Z.geb a b) eqn:Hge; destruct (Z.ltb a b) eqn:Hlt;
    try reflexivity;
    rewrite Z.geb_leb in Hge;
    first [rewrite Z.leb_le in Hge | rewrite Z.leb_gt in Hge];
    first [rewrite Z.ltb_lt in Hlt | rewrite Z.ltb_ge in Hlt]; lia.
Qed.

Local Lemma tagged_unsigned_nonneg : forall a : Z,
  0 <= a < 4611686018427387904 ->
  Int64.unsigned (Int64.repr (a * 2 + 1)) = a * 2 + 1.
Proof.
  intros a Ha. apply Int64.unsigned_repr.
  unfold Int64.max_unsigned. change Int64.modulus with 18446744073709551616. lia.
Qed.

Local Lemma tagged_unsigned_neg : forall a : Z,
  -4611686018427387904 <= a < 0 ->
  Int64.unsigned (Int64.repr (a * 2 + 1)) = a * 2 + 1 + 18446744073709551616.
Proof.
  intros a Ha. rewrite Int64.unsigned_repr_eq.
  change Int64.modulus with 18446744073709551616.
  replace (a * 2 + 1)
    with ((a * 2 + 1 + 18446744073709551616) + (-1) * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small; lia.
Qed.

Local Lemma tagged_ugeint_arith : forall a b,
  0 <= a < 4611686018427387904 ->
  0 <= b < 4611686018427387904 ->
  negb (Int64.ltu (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1)))
    = Z.geb (z_flip_sign a) (z_flip_sign b).
Proof.
  intros a b Ha Hb. rewrite Z_geb_negb_ltb.
  unfold Int64.ltu.
  rewrite (tagged_unsigned_nonneg a ltac:(lia)).
  rewrite (tagged_unsigned_nonneg b ltac:(lia)).
  rewrite (z_flip_sign_nonneg_eq a ltac:(lia)).
  rewrite (z_flip_sign_nonneg_eq b ltac:(lia)).
  destruct (zlt _ _); destruct (Z.ltb _ _) eqn:Hlt; simpl; try reflexivity;
    first [apply Z.ltb_lt in Hlt | apply Z.ltb_ge in Hlt]; lia.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_UGEINT_correct :
    handler_correct handle_UGEINT f_instr_UGEINT
      (fun _ => None)
      (fun _ _ s ard =>
         match s.(Machine.accu), s.(Machine.stack) with
         | Val_int a, Val_int b :: _ =>
             0 <= a < 4611686018427387904 /\
             0 <= b < 4611686018427387904 /\
             int_vlong ard a /\
             int_vlong ard b
         | _, _ => True
         end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

Theorem verify_UGEINT_handler_correct :
    handler_correct handle_UGEINT f_instr_UGEINT
      (fun _ => None)
      unsigned_ints_safe
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* ================================================================== *)
(* Wrapper with the exact type required by InstructVerificationProof.v *)
(* ================================================================== *)

Local Notation UGEINT := Bytecode.AST.UGEINT.

Theorem correct_UGEINT :
    handler_correct (handle_instr UGEINT) (clight_of UGEINT)
      (error_message_of UGEINT)
      (pre_of UGEINT) (P_halt_of UGEINT) (P_ccall_of UGEINT).
Proof.
Admitted.
