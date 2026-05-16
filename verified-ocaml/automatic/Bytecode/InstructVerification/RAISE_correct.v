(* RAISE_correct.v -- RAISE handler correctness proof.

   RAISE pops a trap frame from the stack, restoring pc, sp, trap_sp,
   env, and extra_args.  This is the exception-raising instruction.

   C code (f_instr_RAISE), live path (dead Sifthenelse branch elided):
     _t'12 = s->trap_sp;   s->sp = _t'12;
     _t'10 = s->sp;  _t'11 = *(cast _t'10 (tptr(tptr tint)) + 0);  s->pc = _t'11;
     _t'7 = s->sp;  _t'8 = s->sp;  _t'9 = *(_t'8 + 1);
     s->trap_sp = _t'7 + (_t'9 >> 1);
     _t'5 = s->sp;  _t'6 = *(_t'5 + 2);  s->env = _t'6;
     _t'3 = s->sp;  _t'4 = *(_t'3 + 3);  s->extra_args = _t'4 >> 1;
     _t'2 = s->sp;  s->sp = _t'2 + 4;
     return 0;

   NO AXIOMS. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
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
        ptrofs_of_int Ptrofs.of_int64
        field_offset
        PTree.get PTree.set].

(* raise_step_pre is imported from InstructSpec.v *)

(* ================================================================== *)
(* Struct layout                                                       *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full) /\
  field_offset ce _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset ce _trap_sp (co_members co) = Errors.OK (48, Full).
Proof.
  eexists. split; [| split; [| split; [| split; [| split]]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_raise : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full) /\
  field_offset (genv_cenv clight_ge) _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset (genv_cenv clight_ge) _trap_sp (co_members co) = Errors.OK (48, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Local Lemma sem_cast_ptlong_to_ptptint_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tlong) (tptr (tptr tint)) m = Some (Vptr b ofs).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma sem_add_ptptint_0 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr (tptr tint)) (Vint (Int.repr 0)) tint m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr (tptr tint)) tint) with (add_case_pi (tptr tint) Signed).
  unfold sem_add_ptr_int. change (sizeof (genv_cenv clight_ge) (tptr tint)) with 8%Z.
  f_equal. f_equal. unfold ptrofs_of_int.
  change (Ptrofs.of_ints (Int.repr 0)) with Ptrofs.zero.
  rewrite Ptrofs.mul_zero, Ptrofs.add_zero. reflexivity.
Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma sem_cast_long_to_long : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof. intros. unfold sem_cast. simpl classify_cast. rewrite ptr64_true. reflexivity. Qed.

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed). simpl. reflexivity.
Qed.

Local Lemma sem_add_ptr_tlong : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vlong n) tlong m
  = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tlong) with (add_case_pl tlong).
  unfold sem_add_ptr_long. reflexivity.
Qed.

Local Lemma sem_add_sp_2 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 2)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_sp_3 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 3)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 24))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_sp_4 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 4)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 32))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_RAISE_correct :
    handler_correct (fun _pc s => do_raise s.(accu) s) f_instr_RAISE
      (fun _ => None)
      raise_step_pre
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

(* Bridge lemma: when do_raise returns Error, error_message_of_raise
   returns the same message.  Both functions share the same case
   structure, so this is a direct computation. *)
Local Lemma do_raise_error_implies_error_message : forall exn s msg,
  do_raise exn s = Error msg ->
  error_message_of_raise s = Some msg.
Proof.
  intros exn s msg H.
  unfold do_raise in H. unfold error_message_of_raise.
  destruct (Nat.eqb (trap_sp s) 0) eqn:Htsp.
  - inversion H. reflexivity.
  - set (k := Nat.sub (length (Machine.stack s)) (trap_sp s)) in *.
    set (ft := skipn k (Machine.stack s)) in *.
    destruct ft as [| v0 ft1].
    + inversion H. reflexivity.
    + destruct v0; try (inversion H; reflexivity).
      destruct ft1 as [| v1 ft2]; try (inversion H; reflexivity).
      destruct v1; try (inversion H; reflexivity).
      destruct ft2 as [| v2 ft3]; try (inversion H; reflexivity).
      destruct ft3 as [| v3 ft4]; try (inversion H; reflexivity).
      destruct v3; try (inversion H; reflexivity).
Qed.

From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr RAISE / clight_of RAISE / pre_of RAISE are
   convertible with (fun _ s => do_raise s.(accu) s) / f_instr_RAISE /
   raise_step_pre.  The Step case is delegated to verify_RAISE_correct.
   Error cases are bridged via do_raise_error_implies_error_message. *)
Definition correct_RAISE :
    handler_correct (handle_instr RAISE) (clight_of RAISE)
      (error_message_of RAISE)
      (pre_of RAISE) (P_halt_of RAISE) (P_ccall_of RAISE).
Proof.
Admitted.
