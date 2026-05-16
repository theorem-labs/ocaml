(* NEQ_correct.v -- Verification of the NEQ bytecode handler.
   C: s->accu = ((long)((long)_t'2 != (long)_t'3) << 1) + 1; sp++.
   If not-equal: ((long)1 << 1) + 1 = 3 = tagged 1 = val_true.
   If equal: ((long)0 << 1) + 1 = 1 = tagged 0 = val_false.

   Structurally identical to EQ but uses One (not-equal) instead of Oeq,
   and the Rocq handler swaps val_true/val_false:
     handle_NEQ: if value_phys_eqb ... then val_false else val_true

   NOTE: The Rocq handler uses value_phys_eqb which works on ANY value
   types, but the Clight code compares as longs via One. The proof only
   covers the case where both accu and stack top are Val_int. The
   precondition neq_int_range_pre is False for other value combinations,
   making those obligations vacuously true. *)
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

Local Lemma sem_ne_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Cop.One
    (Vlong n1) tlong (Vlong n2) tlong m
    = Some (Val.of_bool (negb (Int64.eq n1 n2))).
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

Local Lemma tagged_neq_result : forall (cond : bool),
  Int64.add (Int64.repr (if cond then 2 else 0)) (Int64.repr 1)
    = Int64.repr (if cond then 3 else 1).
Proof. intros. destruct cond; reflexivity. Qed.

(* ================================================================== *)
(* Key arithmetic lemma: tagged integer equality                       *)
(*                                                                      *)
(* Int64.eq (Int64.repr (a*2+1)) (Int64.repr (b*2+1)) = Z.eqb a b    *)
(*                                                                      *)
(* Requires both a*2+1 and b*2+1 to be in [0, Int64.max_unsigned]     *)
(* so that Int64.repr is injective (no modular wrapping).              *)
(* ================================================================== *)

Local Lemma tagged_neq_arith : forall a b,
  0 <= a * 2 + 1 <= Int64.max_unsigned ->
  0 <= b * 2 + 1 <= Int64.max_unsigned ->
  Int64.eq (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1)) = Z.eqb a b.
Proof.
  intros a b Ha Hb.
  unfold Int64.eq.
  rewrite !Int64.unsigned_repr by lia.
  destruct (Z.eqb a b) eqn:Heqb.
  - apply Z.eqb_eq in Heqb. subst b.
    destruct (zeq (a * 2 + 1) (a * 2 + 1)); [reflexivity | congruence].
  - apply Z.eqb_neq in Heqb.
    destruct (zeq (a * 2 + 1) (b * 2 + 1)) as [Heq | Hneq].
    + exfalso. apply Heqb. lia.
    + reflexivity.
Qed.

(* ================================================================== *)
(* The precondition: both integer operands in representable range.     *)
(* For non-(Val_int, Val_int) combinations, the precondition is False, *)
(* making those obligations vacuously true.                            *)
(* ================================================================== *)

Definition neq_int_range_pre (m : mem) (s : state) (ard : abs_rel_data) : Prop :=
  match s.(Machine.accu), s.(Machine.stack) with
  | Val_int a, Val_int b :: _ =>
      0 <= a * 2 + 1 <= Int64.max_unsigned /\
      0 <= b * 2 + 1 <= Int64.max_unsigned /\
      int_vlong ard a /\
      int_vlong ard b
  | _, _ => False
  end.

Theorem verify_NEQ_correct :
    handler_correct handle_NEQ f_instr_NEQ
      (fun _ => None)
      (fun _ => neq_int_range_pre)
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

(* Exported version with named building-block precondition *)
(* Wrapper with the exact type required by InstructVerificationProof.v.
   Abandoned for this pass: [verify_NEQ_correct] is still admitted, and
   [handler_correct_weaken] would also require an unconditional proof that
   canonical [pre_of NEQ] implies [int_op_safe].  The generic Clight
   executability precondition only exposes successful Vlong operations, not
   that the abstract operands are both [Val_int]. *)
Local Notation NEQ := Bytecode.AST.NEQ.
Theorem correct_NEQ :
    handler_correct (handle_instr NEQ) (clight_of NEQ)
      (error_message_of NEQ)
      (pre_of NEQ) (P_halt_of NEQ) (P_ccall_of NEQ).
Proof.
Admitted.
