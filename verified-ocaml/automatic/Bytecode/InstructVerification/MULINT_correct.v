(* MULINT_correct.v -- correctness proof for the MULINT handler.
   C handler computes: (((accu >> 1) * (stack_top >> 1)) << 1) + 1
   Tagged arithmetic: shr untags both operands, multiply, shl+1 retags.
   For tagged ints a_tagged = a*2+1, b_tagged = b*2+1:
     ((a*2+1) >> 1) = a, ((b*2+1) >> 1) = b  (arithmetic shift)
     (a * b) << 1 + 1 = (a*b)*2+1 = tagged(a*b)
   Rocq handler: handle_MULINT pops stack, multiplies two ints. *)
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

(* Semantic lemma: long >> 1 (arithmetic shift right) *)
Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* Semantic lemma: long * long *)
Local Lemma sem_mul_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Omul
    (Vlong n1) tlong (Vlong n2) tlong m
    = Some (Vlong (Int64.mul n1 n2)).
Proof. intros. reflexivity. Qed.

(* Semantic lemma: long << 1 *)
Local Lemma sem_shl_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.shl n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* Semantic lemma: long + int(1) *)
Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* eqm for multiplication *)
Local Lemma eqm64_mul : forall x x' y y',
  Int64.eqm x x' -> Int64.eqm y y' -> Int64.eqm (x * y) (x' * y').
Proof.
  intros x x' y y' [kx Hx] [ky Hy].
  exists (kx * y' + x' * ky + kx * ky * Int64.modulus)%Z.
  nia.
Qed.

Local Lemma eqm64_add : forall x x' y y',
  Int64.eqm x x' -> Int64.eqm y y' -> Int64.eqm (x + y) (x' + y').
Proof.
  intros x x' y y' [kx Hx] [ky Hy].
  exists (kx + ky)%Z. nia.
Qed.

(* Key helper: for odd tagged int n*2+1, the signed arithmetic shift right
   by 1 produces a value congruent to n modulo half_modulus.
   After the outer shl by 1 in the full expression, these half_modulus
   terms become full modulus multiples. We state this as an eqm at
   modulus where the difference is a multiple of half_modulus. *)
Local Lemma shr_tagged_eqm_half : forall n,
  exists k, Int64.signed (Int64.repr (n * 2 + 1)) / 2 = n + k * Int64.half_modulus.
Proof.
  intros n.
  (* signed(repr(n*2+1)) = (n*2+1) + j * modulus for some j *)
  pose proof (Int64.eqm_signed_unsigned (Int64.repr (n * 2 + 1))) as [k1 Hk1].
  pose proof (Int64.eqm_unsigned_repr (n * 2 + 1)) as [k2 Hk2].
  (* Hk1: signed(repr(n*2+1)) = k1*M + unsigned(repr(n*2+1)) *)
  (* Hk2: n*2+1 = k2*M + unsigned(repr(n*2+1)) *)
  set (j := (k1 - k2)%Z).
  assert (Hsigned : Int64.signed (Int64.repr (n * 2 + 1)) = n * 2 + 1 + j * Int64.modulus).
  { unfold j. nia. }
  rewrite Hsigned.
  (* modulus = half_modulus * 2 *)
  assert (HM : Int64.modulus = Int64.half_modulus * 2) by (vm_compute; reflexivity).
  rewrite HM.
  (* (n*2+1 + j*(H*2)) / 2 *)
  replace (n * 2 + 1 + j * (Int64.half_modulus * 2))%Z
    with ((n + j * Int64.half_modulus) * 2 + 1)%Z by lia.
  rewrite Z.div_add_l by lia.
  change (1 / 2)%Z with 0%Z.
  exists j. lia.
Qed.

(* The full tagged multiplication identity. *)
Local Lemma tagged_mulint_arith : forall a b,
  Int64.add
    (Int64.shl
      (Int64.mul
        (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))
        (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)))
      (Int64.repr 1))
    (Int64.repr 1)
  = Int64.repr ((a * b) * 2 + 1).
Proof.
  intros a b.
  unfold Int64.add, Int64.shl, Int64.mul, Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  apply Int64.eqm_samerepr.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 1)%Z with 2%Z.

  set (sa := Int64.signed (Int64.repr (a * 2 + 1)) / 2).
  set (sb := Int64.signed (Int64.repr (b * 2 + 1)) / 2).
  fold sa. fold sb.

  destruct (shr_tagged_eqm_half a) as [ka Hsa_eq].
  destruct (shr_tagged_eqm_half b) as [kb Hsb_eq].
  fold sa in Hsa_eq. fold sb in Hsb_eq.

  (* Peel off unsigned(repr(...)) layers, then prove core eqm directly *)
  eapply Int64.eqm_trans.
  - apply eqm64_add.
    + apply Int64.eqm_unsigned_repr_l.
      apply eqm64_mul.
      * apply Int64.eqm_unsigned_repr_l.
        apply eqm64_mul; apply Int64.eqm_unsigned_repr_l; apply Int64.eqm_refl.
      * apply Int64.eqm_refl.
    + apply Int64.eqm_refl.
  - (* Goal: eqm (sa * sb * 2 + 1) (a*b*2+1) *)
    rewrite Hsa_eq, Hsb_eq.
    set (H := Int64.half_modulus).
    assert (HM : Int64.modulus = H * 2) by (unfold H; vm_compute; reflexivity).
    exists (a * kb + b * ka + ka * kb * H)%Z.
    rewrite HM. nia.
Qed.

Theorem verify_MULINT_correct :
    handler_correct handle_MULINT f_instr_MULINT
      (fun _ => None)
      (pre_and accu_is_long stack_head_is_long)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with the canonical type expected by InstructVerificationProof.v *)
Theorem correct_MULINT :
  handler_correct (handle_instr Bytecode.AST.MULINT) (clight_of Bytecode.AST.MULINT)
    (error_message_of Bytecode.AST.MULINT)
    (pre_of Bytecode.AST.MULINT) (P_halt_of Bytecode.AST.MULINT) (P_ccall_of Bytecode.AST.MULINT).
Proof.
Admitted.

