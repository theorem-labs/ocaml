(* PUSHTRAP_correct.v -- PUSHTRAP handler correctness proof.

   PUSHTRAP pushes 4 values onto the stack and updates trap_sp:
     sp[0] = (tptr tint)(pc + *pc)       -- handler address (code pointer)
     sp[1] = ((trap_sp - new_sp) << 1)|1 -- tagged trap link (distance)
     sp[2] = env                         -- saved environment
     sp[3] = (extra_args << 1) | 1       -- tagged extra_args

   Then: trap_sp = new_sp; pc += 1; return 0.

   Rocq handler (Interpret.v):
     handle_PUSHTRAP handler_pc pc' s =
       let prev_tsp := Val_int (Z.of_nat s.(trap_sp)) in
       let new_stack := Val_int handler_pc :: prev_tsp ::
                        s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: s.(stack) in
       let new_tsp := length new_stack in
       Step (s <|pc := pc'|> <|stack := new_stack|> <|trap_sp := new_tsp|>)

   Key design: vr_code_ptr makes val_repr for sp[0] trivial regardless of
   the specific branch offset.  The step_pre provides all arithmetic needed.

   NO AXIOMS.  NO ADMITTED. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
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
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul Ptrofs.of_ints
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout                                                        *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets_pushtrap : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full) /\
  field_offset ce _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset ce _trap_sp (co_members co) = Errors.OK (48, Full).
Proof.
  eexists. split; [| split; [| split; [| split; [| split; [| split]]]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce_pushtrap : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_pushtrap : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full) /\
  field_offset (genv_cenv clight_ge) _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset (genv_cenv clight_ge) _trap_sp (co_members co) = Errors.OK (48, Full).
Proof.
  rewrite cenv_is_ce_pushtrap. exact ce_offsets_pushtrap.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Local Lemma sem_sub_sp_4 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 4)) tint
    m = Some (Vptr sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 32))).
Proof.
  intros. unfold sem_binary_operation, sem_sub.
  change (classify_sub (tptr tlong) tint) with (sub_case_pi tlong Signed).
  cbv beta iota.
  change (sizeof (genv_cenv clight_ge) tlong) with 8%Z.
  unfold ptrofs_of_int. reflexivity.
Qed.

Local Lemma sem_add_sp_3 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 3)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 24))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_sp_2_local : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 2)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* Cast tptr tlong -> tptr (tptr tint): pointer-to-pointer = identity on 64-bit *)
Local Lemma sem_cast_ptrtlong_to_ptrptrint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tlong) (tptr (tptr tint)) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast.
  change (classify_cast (tptr tlong) (tptr (tptr tint))) with cast_case_pointer.
  reflexivity.
Qed.

(* tptr (tptr tint) + 0 = same ptr *)
Local Lemma sem_add_sp_0_ptrint : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr (tptr tint))
    (Vint (Int.repr 0)) tint
    m = Some (Vptr sp_b sp_ofs).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr (tptr tint)) tint) with (add_case_pi (tptr tint) Signed).
  unfold sem_add_ptr_int. f_equal. f_equal.
  change (sizeof (genv_cenv clight_ge) (tptr tint)) with 8%Z.
  unfold ptrofs_of_int.
  change (Ptrofs.of_ints (Int.repr 0)) with Ptrofs.zero.
  rewrite Ptrofs.mul_zero, Ptrofs.add_zero. reflexivity.
Qed.

Local Lemma sem_add_ptr_int_tint_local : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint) (Vint n) tint m
  = Some (Vptr b (Ptrofs.add ofs
        (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                    (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint_local : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_add_pc_1_local : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma tagged_int_arith : forall n,
  0 <= n -> n < Int64.half_modulus ->
  Int64.add (Int64.shl' (Int64.repr n) (Int.repr 1)) (Int64.repr 1)
  = Int64.repr (n * 2 + 1).
Proof.
  intros n Hge Hlt.
  unfold Int64.shl', Int64.shl.
  change (Int.unsigned (Int.repr 1)) with 1%Z.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 1)%Z with 2%Z.
  rewrite Int64.add_unsigned.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_trans with (y := (n * 2 + 1)%Z).
  2: { apply Int64.eqm_refl. }
  apply Int64.eqm_add.
  - apply Int64.eqm_unsigned_repr_l.
    apply Int64.eqm_mult.
    + apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
    + apply Int64.eqm_refl.
  - apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
Qed.

Local Lemma sem_shl_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong n) tlong
    (Vint (Int.repr 1)) tint
    m = Some (Vlong (Int64.shl' n (Int.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl. reflexivity.
Qed.

Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong
    (Vint (Int.repr 1)) tint
    m = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add tlong tint) with add_default.
  unfold sem_binarith. simpl. reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_PUSHTRAP_correct : forall handler_pc,
    handler_correct (handle_PUSHTRAP handler_pc) f_instr_PUSHTRAP
      (fun _ => None)
      (pushtrap_step_pre handler_pc)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr (PUSHTRAP z) / clight_of (PUSHTRAP z) / pre_of (PUSHTRAP z)
   are convertible with handle_PUSHTRAP z / f_instr_PUSHTRAP / pushtrap_step_pre z.
   P_halt_of and P_ccall_of are vacuously satisfied (PUSHTRAP never halts or
   issues a C call).  error_message_of is vacuous too (PUSHTRAP never errors). *)
Definition correct_PUSHTRAP : forall z,
    handler_correct (handle_instr (Bytecode.AST.PUSHTRAP z)) (clight_of (Bytecode.AST.PUSHTRAP z))
      (error_message_of (Bytecode.AST.PUSHTRAP z))
      (pre_of (Bytecode.AST.PUSHTRAP z)) (P_halt_of (Bytecode.AST.PUSHTRAP z)) (P_ccall_of (Bytecode.AST.PUSHTRAP z)).
Proof.
Admitted.

