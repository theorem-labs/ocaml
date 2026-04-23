(* GEINT_correct.v -- Verification of the GEINT bytecode handler.
   C: s->accu = ((long)((long)_t'2 >= (long)_t'3) << 1) + 1; sp++.
   If a >= b: ((long)1 << 1) + 1 = 3 = tagged 1 = val_true.
   If a < b:  ((long)0 << 1) + 1 = 1 = tagged 0 = val_false.

   The Clight code uses Oge (signed >=), which CompCert implements as
   negb (Int64.lt n1 n2), where Int64.lt uses signed comparison.
   The Rocq handler uses val_bool (a >=? b) where >=? is Z.geb.

   The tagged_ge_arith lemma requires a range precondition:
   both integer operands must satisfy
     Int64.min_signed <= a*2+1 <= Int64.max_signed
   so that Int64.signed_repr is injective (no modular wrapping).

   For non-(Val_int, Val_int) value combinations, the precondition is
   False, making those obligations vacuously true. *)
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

(* sem_binary_operation Oge on two longs: Oge -> sem_cmp Cge ->
   cmp_default -> sem_binarith -> bin_case_l Signed ->
   Int64.cmp Cge n1 n2 = negb (Int64.lt n1 n2). *)
Local Lemma sem_ge_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Oge
    (Vlong n1) tlong (Vlong n2) tlong m
    = Some (Val.of_bool (negb (Int64.lt n1 n2))).
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

Local Lemma tagged_ge_result : forall (cond : bool),
  Int64.add (Int64.repr (if cond then 2 else 0)) (Int64.repr 1)
    = Int64.repr (if cond then 3 else 1).
Proof. intros. destruct cond; reflexivity. Qed.

Local Lemma tagged_ge_arith : forall a b,
  Int64.min_signed <= a * 2 + 1 <= Int64.max_signed ->
  Int64.min_signed <= b * 2 + 1 <= Int64.max_signed ->
  negb (Int64.lt (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1)))
    = Z.geb a b.
Proof.
  intros a b Ha Hb.
  unfold Int64.lt.
  rewrite !Int64.signed_repr by lia.
  rewrite Z.geb_leb.
  destruct (Coqlib.zlt (a * 2 + 1) (b * 2 + 1)); simpl.
  - (* a * 2 + 1 < b * 2 + 1, so a < b, so (b <=? a) = false *)
    symmetry. apply Z.leb_gt. lia.
  - (* a * 2 + 1 >= b * 2 + 1, so a >= b, so (b <=? a) = true *)
    symmetry. apply Z.leb_le. lia.
Qed.

Definition geint_range_pre (m : mem) (s : state) (ard : abs_rel_data) : Prop :=
  match s.(Machine.accu), s.(Machine.stack) with
  | Val_int a, Val_int b :: _ =>
      Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
      Int64.min_signed <= b * 2 + 1 <= Int64.max_signed /\
      int_vlong ard a /\
      int_vlong ard b
  | _, _ => False
  end.

Theorem verify_GEINT_correct :
    handler_correct handle_GEINT f_instr_GEINT
      (fun _ => None)
      (fun _ => geint_range_pre)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

Theorem verify_GEINT_handler_correct :
    handler_correct handle_GEINT f_instr_GEINT
      (fun _ => None)
      signed_int_op_safe
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* ================================================================== *)
(* Wrapper with canonical InstructSpec predicates                       *)
(* ================================================================== *)

Import Bytecode.AST.

Theorem correct_GEINT :
    handler_correct (handle_instr GEINT) (clight_of GEINT)
      (error_message_of GEINT)
      (pre_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT).
Proof.
Admitted.
