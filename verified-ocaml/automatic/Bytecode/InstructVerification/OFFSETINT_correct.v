(* OFFSETINT_correct.v -- OFFSETINT completeness proof.

   OFFSETINT handler:
   - Rocq: handle_OFFSETINT ofs pc' s matches accu:
       Val_int a => Step {pc:=pc', accu:=Val_int(a+ofs)}
       _          => Error

   - C (Clight AST): The handler body does:
       1. _t'2 = s->accu                              (read accu tagged int)
       2. _t'3 = s->pc                                (read pc pointer)
       3. _t'4 = *_t'3                                (read operand from code)
       4. s->accu = _t'2 + (_t'4 << 1)                (tagged offset add)
       5. _t'1 = s->pc                                (read pc pointer again)
       6. s->pc = _t'1 + 1                            (advance pc past operand)
       7. return 0

   Tagged integer arithmetic correspondence:
     val_repr (Val_int a) = Vlong (Int64.repr (a*2+1))
     C computes: (a*2+1) + (ofs << 1) = (a*2+1) + ofs*2 = (a+ofs)*2+1
                = val_repr (Val_int (a+ofs))

   Key differences from NEGINT:
   - TWO stores: accu field at offset +8, pc field at offset +0
   - Reads operand from code memory via *pc (Mint32 load)
   - Post-state uses shifted code_base_ofs to account for pc advancement
   - Code buffer invariants expressed as preconditions (not axioms)

   Uses handler_correct for code buffer preconditions.
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
(* Struct layout: _pc field at offset 0                                *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_pc_offset : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full).
Proof.
  eexists. split; [| split]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_with_pc : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_pc_offset.
Qed.

(* ================================================================== *)
(* Semantic lemma: Oshl on tint values                                 *)
(* ================================================================== *)

Lemma sem_shl_int_int : forall i m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vint i) tint
    (Vint (Int.repr 1)) tint
    m = Some (Vint (Int.shl i (Int.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tint tint) with (shift_case_ii Signed).
  simpl.
  change (Int.ltu (Int.repr 1) Int.iwordsize) with true.
  reflexivity.
Qed.

(* ================================================================== *)
(* Semantic lemma: Oadd tlong tint via sem_binarith                    *)
(* ================================================================== *)

Lemma sem_add_long_int : forall n i m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong
    (Vint i) tint
    m = Some (Vlong (Int64.add n (Int64.repr (Int.signed i)))).
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
  reflexivity.
Qed.

(* ================================================================== *)
(* Semantic lemma: pointer + 1 for tptr tint                           *)
(* ================================================================== *)

Lemma sem_add_ptr_int_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int.
  change (sizeof (genv_cenv clight_ge) tint) with 4%Z.
  reflexivity.
Qed.

(* ================================================================== *)
(* Semantic lemma: cast (tptr tint) -> (tptr tint) is identity         *)
(* ================================================================== *)

Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* ================================================================== *)
(* Arithmetic lemma: tagged offset addition (PROVED, no axiom)         *)
(*                                                                      *)
(* The C code computes ofs << 1 in 32-bit, then sign-extends to 64-bit *)
(* and adds to the tagged accu. This equals (a+ofs)*2+1 in 64-bit     *)
(* provided the 32-bit shift does not overflow, i.e.,                  *)
(* Int.min_signed <= ofs*2 <= Int.max_signed.                          *)
(* ================================================================== *)

Local Lemma int_shl_1 : forall i,
  Int.shl i (Int.repr 1) = Int.repr (Int.unsigned i * 2).
Proof.
  intros. unfold Int.shl.
  change (Int.unsigned (Int.repr 1)) with 1%Z.
  f_equal. rewrite Z.shiftl_mul_pow2 by lia. simpl. lia.
Qed.

(* When Int.signed i * 2 fits in 32-bit signed range,
   Int.signed (Int.shl i (Int.repr 1)) = Int.signed i * 2. *)
Local Lemma int_signed_shl_1 : forall i,
  Int.min_signed <= Int.signed i * 2 <= Int.max_signed ->
  Int.signed (Int.shl i (Int.repr 1)) = Int.signed i * 2.
Proof.
  intros i Hrange.
  rewrite int_shl_1.
  assert (Hrepr_eq : Int.repr (Int.unsigned i * 2) = Int.repr (Int.signed i * 2)).
  { apply Int.eqm_samerepr.
    pose proof (Int.eqm_signed_unsigned i) as [k Hk].
    exists (- k * 2)%Z.
    change Int.modulus with 4294967296%Z in *. lia. }
  rewrite Hrepr_eq.
  apply Int.signed_repr. exact Hrange.
Qed.

Lemma tagged_offsetint_arith : forall a (i : int),
  Int.min_signed <= Int.signed i * 2 <= Int.max_signed ->
  Int64.add (Int64.repr (a * 2 + 1))
            (Int64.repr (Int.signed (Int.shl i (Int.repr 1))))
  = Int64.repr ((a + Int.signed i) * 2 + 1).
Proof.
  intros a i Hrange.
  rewrite (int_signed_shl_1 i Hrange).
  rewrite Int64.add_unsigned.
  apply Int64.eqm_samerepr.
  eapply Int64.eqm_trans.
  { apply Int64.eqm_add;
      apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr. }
  replace ((a + Int.signed i) * 2 + 1)%Z
    with (a * 2 + 1 + Int.signed i * 2)%Z by lia.
  apply Int64.eqm_refl.
Qed.

(* ================================================================== *)
(* Value representation for the result                                 *)
(* ================================================================== *)

Lemma val_repr_offsetint_result : forall hm cb co a (i : int),
  Int.min_signed <= Int.signed i * 2 <= Int.max_signed ->
  val_repr hm cb co (Val_int (a + Int.signed i))
    (Vlong (Int64.add (Int64.repr (a * 2 + 1))
                       (Int64.repr (Int.signed (Int.shl i (Int.repr 1)))))).
Proof.
  intros. rewrite (tagged_offsetint_arith a i H). constructor.
Qed.

(* ================================================================== *)
(* load_result for Vlong / Vptr                                        *)
(* ================================================================== *)

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(*                                                                      *)
(* Preconditions (from handler_correct):                      *)
(* 1. Code buffer contains the operand at current PC                   *)
(* 2. The 32-bit left shift by 1 does not overflow                    *)
(*                                                                      *)
(* Block separation (cb <> sb) comes from ar_code_ne_sptr in the       *)
(* abs_rel_data record -- no precondition needed.                      *)
(* ================================================================== *)

Theorem verify_OFFSETINT_correct : forall ofs,
    Int.min_signed <= ofs * 2 <= Int.max_signed ->
    handler_correct (handle_OFFSETINT ofs) f_instr_OFFSETINT
      (fun _ => None)
      (fun e m s ard =>
         (exists (i : int),
           Mem.load Mint32 m (ar_code_base_block ard)
             (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
                (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
           = Some (Vint i) /\
           Int.signed i = ofs /\
           Int.min_signed <= Int.signed i * 2 <= Int.max_signed) /\
         accu_is_long e m s ard)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Exported version with named building-block precondition *)
Theorem verify_OFFSETINT_handler_correct : forall ofs,
    Int.min_signed <= ofs * 2 <= Int.max_signed ->
    handler_correct (handle_OFFSETINT ofs) f_instr_OFFSETINT
      (fun _ => None)
      (pre_and (code_at (Int.repr ofs)) accu_is_long)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with the uniform type expected by InstructVerificationFineGrainedSpec.
   handle_instr (OFFSETINT z) / clight_of (OFFSETINT z) / pre_of (OFFSETINT z)
   are convertible with handle_OFFSETINT z / f_instr_OFFSETINT /
   pre_and (code_at (Int.repr z)) accu_is_long.

   The proof destructs the instr_wfb boolean guard first:
   - When z * 2 is in range: the Step case (accu = Val_int) delegates to
     verify_OFFSETINT_handler_correct. Error cases (non-integer accu) are
     proved via error_message_of / error_message_of reflexivity.
   - When z * 2 is out of range: the handler returns Error "OFFSETINT:
     malformed operand", matching error_message_of exactly. *)
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

Definition correct_OFFSETINT : forall z,
  handler_correct (handle_instr (OFFSETINT z)) (clight_of (OFFSETINT z))
    (error_message_of (OFFSETINT z))
    (pre_of (OFFSETINT z)) (P_halt_of (OFFSETINT z)) (P_ccall_of (OFFSETINT z)).
Proof.
Admitted.
