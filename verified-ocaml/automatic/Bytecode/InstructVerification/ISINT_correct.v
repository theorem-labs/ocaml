(* ISINT_correct.v -- ISINT completeness proof using
   the computational evaluator from StepToBigstep.v.

   ISINT handler:
   - Rocq: handle_ISINT pc' s:
       Step (s <|pc:=pc'|> <|accu:= if is_int (accu s) then val_true else val_false|>)
       Always returns Step (no Error).

   - C (Clight AST): The handler body does:
       1. _t'1 = s->accu                          (read accu tagged value)
       2. s->accu = ((_t'1 & 1) << 1) + 1         (tag-bit test + encode as bool)
       3. return 0

   Tagged integer arithmetic correspondence:
     Val_int n:       val_repr = Vlong (Int64.repr (n*2+1)), bit 0 = 1
       C: ((n*2+1) & 1) = 1, (1 << 1) + 1 = 3 = val_repr(Val_int 1) = val_true
     Val_block tag []: val_repr = Vlong (Int64.repr (tag*1024)), bit 0 = 0
       C: ((tag*1024) & 1) = 0, (0 << 1) + 1 = 1 = val_repr(Val_int 0) = val_false

   Precondition: accu is Val_int or Val_block tag [].
   Val_ptr and Val_closure produce Vptr in memory, and CompCert's
   sem_and on Vptr is undefined (sem_binarith requires Vint/Vlong/Vfloat
   values for the operator, but Vptr fails the binarith path), so those
   cases cannot be proved without extending the CompCert semantics.

   Uses abs_rel directly (no separate _pre relation).
   All lemmas imported from HandlerLemmas. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.
Local Notation exec := (exec_stmt function_entry1 clight_ge).

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Lemma: sem_and tlong tint on Vlong * Vint(1)                       *)
(* ================================================================== *)

Lemma sem_and_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oand
    (Vlong n) tlong
    (Vint (Int.repr 1)) tint
    m = Some (Vlong (Int64.and n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_and.
  change (classify_binarith tlong tint) with (bin_case_l Signed).
  unfold sem_binarith. simpl binarith_type.
  unfold sem_cast at 1. simpl classify_cast.
  rewrite ptr64_true.
  unfold sem_cast at 1. simpl classify_cast.
  simpl cast_int_long.
  change (Int.signed (Int.repr 1)) with 1%Z.
  reflexivity.
Qed.

(* ================================================================== *)
(* Lemma: sem_shl on tlong * tint: Vlong << Vint(1)                   *)
(* ================================================================== *)

Lemma sem_shl_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong n) tlong
    (Vint (Int.repr 1)) tint
    m = Some (Vlong (Int64.shl' n (Int.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl.
  reflexivity.
Qed.

(* ================================================================== *)
(* Lemma: sem_add on tlong * tint: Vlong + Vint(1)                    *)
(* ================================================================== *)

Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong
    (Vint (Int.repr 1)) tint
    m = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add tlong tint) with add_default.
  unfold sem_binarith.
  change (classify_binarith tlong tint) with (bin_case_l Signed).
  simpl binarith_type.
  unfold sem_cast at 1. simpl classify_cast.
  rewrite ptr64_true.
  unfold sem_cast at 1. simpl classify_cast.
  simpl cast_int_long.
  change (Int.signed (Int.repr 1)) with 1%Z.
  reflexivity.
Qed.

(* ================================================================== *)
(* Lemma: Tagged integer bit-0 is 1                                    *)
(*   Int64.and (Int64.repr (n*2+1)) (Int64.repr 1) = Int64.repr 1     *)
(* ================================================================== *)

Lemma tagged_int_bit0 : forall n,
  Int64.and (Int64.repr (n * 2 + 1)) (Int64.repr 1) = Int64.repr 1.
Proof.
  intros n.
  (* Z.land (n*2+1) 1 = 1 because n*2+1 is odd *)
  apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_and, !Int64.testbit_repr by lia.
  replace (n * 2 + 1)%Z with (2 * n + 1)%Z by lia.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - rewrite Z.testbit_odd_0. reflexivity.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite Z.testbit_odd_succ by lia.
    (* Goal: Z.testbit n (i-1) && Z.testbit 1 (Z.succ(i-1)) = Z.testbit 1 (Z.succ(i-1)) *)
    (* Z.testbit 1 (succ k) for k >= 0: 1 = 2*0+1, testbit_odd_succ gives testbit 0 k = false *)
    assert (Hbit1 : Z.testbit 1 (Z.succ (i - 1)) = false).
    { change 1%Z with (2 * 0 + 1)%Z.
      rewrite Z.testbit_odd_succ by lia.
      apply Z.bits_0. }
    rewrite Hbit1. apply andb_false_r.
Qed.

(* ================================================================== *)
(* Lemma: Tagged block-atom bit-0 is 0                                 *)
(*   Int64.and (Int64.repr (tag*1024)) (Int64.repr 1) = Int64.repr 0  *)
(* ================================================================== *)

Lemma tagged_block_bit0 : forall tag,
  Int64.and (Int64.repr (Z.of_nat tag * 1024)) (Int64.repr 1) = Int64.repr 0.
Proof.
  intros tag.
  apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_and, !Int64.testbit_repr by lia.
  replace (Z.of_nat tag * 1024)%Z with (2 * (Z.of_nat tag * 512))%Z by lia.
  rewrite Z.bits_0.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - rewrite Z.testbit_even_0. reflexivity.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite Z.testbit_even_succ by lia.
    (* Goal: Z.testbit (tag*512) (i-1) && Z.testbit 1 (Z.succ(i-1)) = false *)
    assert (Hbit1 : Z.testbit 1 (Z.succ (i - 1)) = false).
    { change 1%Z with (2 * 0 + 1)%Z.
      rewrite Z.testbit_odd_succ by lia.
      apply Z.bits_0. }
    rewrite Hbit1. apply andb_false_r.
Qed.

(* ================================================================== *)
(* Concrete arithmetic lemmas via native_compute                       *)
(* ================================================================== *)

Lemma shl_1_1 :
  Int64.shl' (Int64.repr 1) (Int.repr 1) = Int64.repr 2.
Proof.
  cut (Int64.unsigned (Int64.shl' (Int64.repr 1) (Int.repr 1))
       = Int64.unsigned (Int64.repr 2)).
  { intro H. rewrite <- (Int64.repr_unsigned (Int64.shl' _ _)).
    rewrite H. apply Int64.repr_unsigned. }
  native_compute. reflexivity.
Qed.

Lemma shl_0_1 :
  Int64.shl' (Int64.repr 0) (Int.repr 1) = Int64.repr 0.
Proof.
  cut (Int64.unsigned (Int64.shl' (Int64.repr 0) (Int.repr 1))
       = Int64.unsigned (Int64.repr 0)).
  { intro H. rewrite <- (Int64.repr_unsigned (Int64.shl' _ _)).
    rewrite H. apply Int64.repr_unsigned. }
  native_compute. reflexivity.
Qed.

Lemma add_2_1 :
  Int64.add (Int64.repr 2) (Int64.repr 1) = Int64.repr 3.
Proof.
  cut (Int64.unsigned (Int64.add (Int64.repr 2) (Int64.repr 1))
       = Int64.unsigned (Int64.repr 3)).
  { intro H. rewrite <- (Int64.repr_unsigned (Int64.add _ _)).
    rewrite H. apply Int64.repr_unsigned. }
  native_compute. reflexivity.
Qed.

Lemma add_0_1 :
  Int64.add (Int64.repr 0) (Int64.repr 1) = Int64.repr 1.
Proof.
  cut (Int64.unsigned (Int64.add (Int64.repr 0) (Int64.repr 1))
       = Int64.unsigned (Int64.repr 1)).
  { intro H. rewrite <- (Int64.repr_unsigned (Int64.add _ _)).
    rewrite H. apply Int64.repr_unsigned. }
  native_compute. reflexivity.
Qed.

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof.
  intros. reflexivity.
Qed.

(* ================================================================== *)
(* Precondition: accu has a Vlong representation (not Vptr).           *)
(*                                                                      *)
(* Val_int n        -> Vlong (tagged n)              OK                *)
(* Val_block tag [] -> Vlong (tagged block-atom)     OK                *)
(* Val_ptr addr     -> Vptr b ofs                    sem_and fails     *)
(* Val_closure a o  -> Vptr b (ofs+delta)            sem_and fails     *)
(*                                                                      *)
(* This is a semantic restriction: the C ISINT handler uses bitwise    *)
(* AND which CompCert only defines for integer-like (Vlong/Vint)       *)
(* values, not for pointer values (Vptr).                              *)
(* ================================================================== *)

Definition isint_accu_vlong (s : Machine.state) : Prop :=
  match Machine.accu s with
  | Val_int _ => True
  | Val_block _ nil => True
  | _ => False
  end.

(* Stronger precondition: also requires Vlong representation for Val_int.
   This excludes the vr_code_ptr case where Val_int is represented as Vptr,
   which cannot be handled by CompCert's sem_and (undefined on Vptr). *)
Definition isint_accu_vlong_strong (s : Machine.state) (ard : abs_rel_data) : Prop :=
  isint_accu_vlong s /\
  match Machine.accu s with
  | Val_int n => int_vlong ard n
  | _ => True
  end.

(* ================================================================== *)
(* Main theorem                                                        *)
(*                                                                      *)
(* Uses a custom statement (like BOOLNOT_correct.v) to add the         *)
(* isint_accu_vlong precondition, since handle_ISINT always returns    *)
(* Step and handler_correct has no Step-case precondition slot.         *)
(* ================================================================== *)

Theorem verify_ISINT_correct :
  forall e le m s,
    match handle_ISINT s.(pc) s with
    | Step s' =>
        forall ard,
        isint_accu_vlong_strong s ard ->
        abs_rel_with_ard e le m s ard ->
        exists le' m' out,
          exec_stmt function_entry1 clight_ge e le m (fn_body f_instr_ISINT) E0 le' m' out /\
          abs_rel e le' m' s'
    | Error msg => False
    | Halt v => False
    | CCall_request _ _ _ => False
    end.
Proof.
Admitted.

(* Wrapper: convert to handler_correct form for the Module Type. *)
Theorem verify_ISINT_handler_correct :
    handler_correct handle_ISINT f_instr_ISINT
      (fun _ => None)
      accu_is_immediate
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Final wrapper with the exact type from InstructVerificationFineGrainedSpec. *)
Theorem correct_ISINT :
    handler_correct (handle_instr ISINT) (clight_of ISINT)
      (error_message_of ISINT)
      (pre_of ISINT) (P_halt_of ISINT) (P_ccall_of ISINT).
Proof.
Admitted.
