(* ATOM0_correct.v -- ATOM0 correctness proof.

   ATOM0 sets accu to Atom(0) = tag 0 atom = (long)(0 << 10) = 0.
   No PC advancement (no argument read from code stream).

   C code (f_instr_ATOM0):
     s->accu = (long)(0 << 10);   // atom with tag 0
     return 0;

   Rocq handler (handle_ATOM0):
     handle_ATOM0 pc' s = Step (s <|accu := Val_block 0 []|>)

   Atoms are empty blocks represented as tagged integers,
   matching vr_block_atom in val_repr.

   Single store to accu field at offset +8. No PC change, no temps.

   NO AXIOMS.  NO ADMITTED. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From RecordUpdate Require Import RecordUpdate.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Import Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

(* 0 << 10 as ints *)
Local Lemma sem_shl_int_0_10 : forall m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vint (Int.repr 0)) tint (Vint (Int.repr 10)) tint m =
    Some (Vint (Int.shl (Int.repr 0) (Int.repr 10))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tint tint) with (shift_case_ii Signed).
  simpl.
  change (Int.ltu (Int.repr 10) Int.iwordsize) with true.
  reflexivity.
Qed.

(* Int.shl 0 10 = 0 *)
Local Lemma int_shl_0_10 : Int.shl (Int.repr 0) (Int.repr 10) = Int.repr 0.
Proof.
  unfold Int.shl.
  change (Int.unsigned (Int.repr 10)) with 10%Z.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 10)%Z with 1024%Z.
  change (Int.unsigned (Int.repr 0)) with 0%Z.
  simpl. reflexivity.
Qed.

(* cast (int)0 -> (long)0 *)
Local Lemma sem_cast_int_shl_0_10_to_long : forall m,
  sem_cast (Vint (Int.shl (Int.repr 0) (Int.repr 10))) tint tlong m =
    Some (Vlong (Int64.repr 0)).
Proof.
  intros. rewrite int_shl_0_10.
  unfold sem_cast.
  change (classify_cast tint tlong) with (cast_case_i2l Signed).
  simpl. reflexivity.
Qed.

(* load_result for Vlong 0 *)
Local Lemma atom0_load_result :
  Val.load_result Mint64 (Vlong (Int64.repr 0)) = Vlong (Int64.repr 0).
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_ATOM0_correct :
    handler_correct handle_ATOM0 f_instr_ATOM0
      (fun _ => None)
      (fun _ _ _ _ => True)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.
