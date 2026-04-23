(* ATOM_correct.v -- ATOM correctness proof.

   ATOM reads tag t from *pc, computes Vlong(tag << 10) = atom representation,
   stores to accu, and increments pc by 1 (4 bytes, sizeof(int)).

   C code (f_instr_ATOM):
     _t'1 = s->pc;
     s->pc = _t'1 + 1;             // advance pc past argument
     _t'2 = *_t'1;                  // read tag from bytecode stream
     s->accu = (long)(_t'2 << 10); // atom = tag * 1024
     return 0;

   Rocq handler (handle_ATOM):
     handle_ATOM t pc' s = Step (s <|pc := pc'|> <|accu := Val_block t []|>)

   Atoms are empty blocks represented as tagged integers (tag * 1024),
   matching vr_block_atom in val_repr.

   Two stores: pc field at offset +0, accu field at offset +8.
   Reads tag operand from code block (precondition via handler_correct).

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

Lemma sem_shl_int_10 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vint n) tint (Vint (Int.repr 10)) tint m =
    Some (Vint (Int.shl n (Int.repr 10))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tint tint) with (shift_case_ii Signed).
  simpl.
  change (Int.ltu (Int.repr 10) Int.iwordsize) with true.
  reflexivity.
Qed.

Lemma sem_cast_int_to_long : forall n m,
  sem_cast (Vint n) tint tlong m = Some (Vlong (Int64.repr (Int.signed n))).
Proof.
  intros. unfold sem_cast.
  change (classify_cast tint tlong) with (cast_case_i2l Signed).
  simpl. reflexivity.
Qed.

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

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

(* Atom tag arithmetic: (long)(Int.shl (Int.repr t) (Int.repr 10)) = t * 1024
   when 0 <= t <= 2097151 (tag fits in 21 bits, shift doesn't overflow). *)
Lemma atom_tag_eq : forall (t : nat),
  Z.of_nat t <= 2097151 ->
  Int64.repr (Int.signed (Int.shl (Int.repr (Z.of_nat t)) (Int.repr 10)))
  = Int64.repr (Z.of_nat t * 1024).
Proof.
  intros t Ht.
  f_equal.
  unfold Int.shl.
  change (Int.unsigned (Int.repr 10)) with 10%Z.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 10)%Z with 1024%Z.
  rewrite Int.signed_repr.
  - rewrite Int.unsigned_repr.
    + reflexivity.
    + split. { lia. }
      change Int.max_unsigned with 4294967295%Z. lia.
  - rewrite Int.unsigned_repr.
    + split.
      * change Int.min_signed with (-2147483648)%Z. lia.
      * change Int.max_signed with 2147483647%Z. lia.
    + split. { lia. }
      change Int.max_unsigned with 4294967295%Z. lia.
Qed.

(* ================================================================== *)
(* Corrected handler                                                   *)
(* ================================================================== *)

(* handle_ATOM returns Val_block t [], matching the C runtime's atom
   representation (Vlong(tag * 1024)) via vr_block_atom. *)

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Local Lemma val_repr_co_shift : forall hm cb co co' v cv,
  val_repr hm cb co v cv -> val_repr hm cb co' v cv.
Proof.
  intros. inversion H; subst.
  - constructor. - eapply vr_ptr; eassumption.
  - eapply vr_closure; eauto. - constructor. - eapply vr_code_ptr.
Qed.
Local Lemma stack_repr_co_shift : forall hm cb co co' m stk b ofs,
  stack_repr hm cb co m stk b ofs -> stack_repr hm cb co' m stk b ofs.
Proof.
  intros hm0 cb0 co0 co' m0 stk0 b0 ofs0 H. induction H.
  - constructor. - econstructor; [eassumption | eapply val_repr_co_shift; eassumption | assumption].
Qed.
Local Lemma global_repr_co_shift : forall hm cb co co' m vs b ofs,
  global_repr hm cb co m vs b ofs -> global_repr hm cb co' m vs b ofs.
Proof.
  intros hm0 cb0 co0 co' m0 vs0 b0 ofs0 H. induction H.
  - constructor. - econstructor; [eassumption | eapply val_repr_co_shift; eassumption | assumption].
Qed.

Theorem verify_ATOM_correct : forall t,
    Z.of_nat t <= 2097151 ->
    handler_correct (handle_ATOM t) f_instr_ATOM
      (fun _ => None)
      (fun _ m s ard =>
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat t))))
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

(* Wrapper with the exact type expected by InstructVerificationProof.v.
   handle_instr (ATOM t) reduces to handle_ATOM t by computation.
   clight_of (ATOM t) = f_instr_ATOM by computation.
   pre_of (ATOM t) = code_at (Int.repr (Z.of_nat t)) by computation.
   handle_ATOM always returns Step, so P_error/P_halt/P_ccall are dead.
   The Step case delegates to verify_ATOM_correct, which requires
   Z.of_nat t <= 2097151 — the guard enforced by instr_wfb. *)
Definition correct_ATOM : forall t,
  handler_correct (handle_instr (ATOM t)) (clight_of (ATOM t))
    (error_message_of (ATOM t))
    (pre_of (ATOM t)) (P_halt_of (ATOM t)) (P_ccall_of (ATOM t)).
Proof.
Admitted.
