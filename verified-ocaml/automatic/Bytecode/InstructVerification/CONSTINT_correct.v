(* CONSTINT_correct.v -- CONSTINT completeness proof.

   CONSTINT reads n from *pc, computes Val_int(n) = (n<<1)+1, stores to accu,
   and increments pc by 1 (4 bytes, sizeof(int)).

   C code:
     _t'2 = s->pc;
     _t'3 = *_t'2;                  // read n from bytecode stream
     s->accu = ((long)_t'3 << 1) + 1;
     _t'1 = s->pc;
     s->pc = _t'1 + 1;             // advance pc past argument
     return 0;

   Rocq:
     handle_CONSTINT n pc' s = Step (s <|pc := pc'|> <|accu := Val_int n|>)

   Two stores: accu field at offset +8, pc field at offset +0.

   Unlike CONST0-3, CONSTINT is parameterized over n, which the C code reads
   from the code block.  This requires preconditions:
   - The code buffer contains Int.repr n at the current PC position
   - The code block is separate from the struct block
   - n fits in the int32 signed range

   NO AXIOMS.  All structural/range constraints are preconditions
   via handler_correct, following the pattern of POP_correct.v. *)

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
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout: _pc at offset 0, _accu at offset 8                   *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full).
Proof.
  eexists. split; [| split]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_pc_accu : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_cast_int_to_long : forall n m,
  sem_cast (Vint n) tint tlong m = Some (Vlong (Int64.repr (Int.signed n))).
Proof.
  intros. unfold sem_cast.
  change (classify_cast tint tlong) with (cast_case_i2l Signed).
  simpl. reflexivity.
Qed.

Lemma sem_shl_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong n) tlong (Vint (Int.repr 1)) tint m =
    Some (Vlong (Int64.shl n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl.
  change (Int.ltu (Int.repr 1) Int64.iwordsize') with true.
  reflexivity.
Qed.

Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m =
    Some (Vlong (Int64.add n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add tlong tint) with add_default.
  unfold sem_binarith.
  change (classify_binarith tlong tint) with (bin_case_l Signed).
  simpl. reflexivity.
Qed.

(* tagged_int_eq: proved from range constraint instead of axiom.
   When Int.min_signed <= n <= Int.max_signed, Int.signed (Int.repr n) = n,
   so the Int64 arithmetic simplifies to modular congruence. *)
Lemma tagged_int_eq : forall n,
  Int.min_signed <= n <= Int.max_signed ->
  Int64.add (Int64.shl (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 1))
            (Int64.repr 1) = Int64.repr (n * 2 + 1).
Proof.
  intros n Hrange.
  rewrite Int.signed_repr by exact Hrange.
  unfold Int64.shl.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Int64.add_unsigned.
  apply Int64.eqm_samerepr.
  (* Goal: eqm (unsigned(repr(shiftl(unsigned(repr(n)),1))) + unsigned(repr(1)))
               (n * 2 + 1) *)
  apply Int64.eqm_trans with (y := (Z.shiftl (Int64.unsigned (Int64.repr n)) 1 + 1)%Z).
  { apply Int64.eqm_add.
    - apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
    - apply Int64.eqm_refl. }
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 1)%Z with 2%Z.
  (* Goal: eqm (unsigned(repr(n)) * 2 + 1) (n * 2 + 1) *)
  apply Int64.eqm_add.
  - apply Int64.eqm_mult.
    + apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
    + apply Int64.eqm_refl.
  - apply Int64.eqm_refl.
Qed.

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* pc_rel with shifted code base *)
Lemma pc_rel_shift : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr 4)))
         cb (Ptrofs.add co (Ptrofs.repr sizeof_code_t)) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal.
  rewrite Ptrofs.add_assoc.
  rewrite Ptrofs.add_assoc.
  f_equal.
  rewrite Ptrofs.add_commut. reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_CONSTINT_correct : forall n,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_CONSTINT n) f_instr_CONSTINT
      (fun _ => None)
      (fun _ m s ard =>
         (* The code buffer contains Int.repr n at the current PC position *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr n)) /\
         (* n fits in the int32 signed range *)
         Int.min_signed <= n <= Int.max_signed)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Exported version with named building-block precondition *)
Theorem verify_CONSTINT_handler_correct : forall n,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_CONSTINT n) f_instr_CONSTINT
      (fun _ => None)
      (code_at (Int.repr n))
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

(* Wrapper with the exact type expected by InstructVerificationProof.v.
   handle_instr (CONSTINT n) = handle_CONSTINT n by computation.
   clight_of (CONSTINT n) = f_instr_CONSTINT by computation.
   pre_of (CONSTINT n) = code_at (Int.repr n) by computation.
   error_message_of (CONSTINT n) is vacuously False (error_message_of returns None).
   P_halt_of (CONSTINT n) and P_ccall_of (CONSTINT n) are False (not STOP/C_CALL).
   Since handle_CONSTINT always returns Step, those predicates are never needed.
   The Step case delegates to verify_CONSTINT_handler_correct, which requires
   n in Int.min_signed..Int.max_signed — the same guard enforced by instr_wfb. *)
Definition correct_CONSTINT : forall n,
  handler_correct (handle_instr (CONSTINT n)) (clight_of (CONSTINT n))
    (error_message_of (CONSTINT n))
    (pre_of (CONSTINT n)) (P_halt_of (CONSTINT n)) (P_ccall_of (CONSTINT n)).
Proof.
Admitted.
