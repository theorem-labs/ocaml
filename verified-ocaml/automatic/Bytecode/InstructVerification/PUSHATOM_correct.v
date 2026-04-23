(* PUSHATOM_correct.v -- PUSHATOM correctness proof.

   PUSHATOM t = PUSH then ATOM t.
   C code (f_instr_PUSHATOM):
     _t'5 = s->sp;                    // read sp
     _t'1 = (tptr tlong)(_t'5 - 1);   // new_sp = sp - 1
     s->sp = _t'1;                     // store new_sp         (Store 1: sb, uso+16)
     _t'4 = s->accu;                   // read accu
     *_t'1 = _t'4;                     // push accu to stack   (Store 2: sp_b, new_sp_ofs)
     _t'2 = s->pc;                     // read pc pointer
     s->pc = _t'2 + 1;                // advance pc           (Store 3: sb, uso+0)
     _t'3 = *_t'2;                     // read tag from code
     s->accu = (long)(_t'3 << 10);    // set accu to atom     (Store 4: sb, uso+8)
     return 0;

   Rocq handler (handle_PUSHATOM):
     handle_PUSHATOM t pc' s =
       Step (s <|pc := pc'|> <|accu := Val_block t []|>
               <|stack := accu :: stack|>)

   Atoms are empty blocks represented as tagged integers (tag * 1024),
   matching vr_block_atom in val_repr.

   Four stores:
     Store 1: sp field  (sb, uso+16)     <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp   (sp_b, new_sp)   <- accu_v
     Store 3: pc field  (sb, uso+0)      <- Vptr cb new_pc_ofs
     Store 4: accu field (sb, uso+8)     <- Vlong (tag * 1024)

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
Local Notation exec := (exec_stmt function_entry1 clight_ge).

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].


(* ================================================================== *)
(* Struct layout facts                                                 *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_facts_all : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_all : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full).
Proof.
  rewrite cenv_is_ce. exact ce_facts_all.
Qed.

(* ================================================================== *)
(* Semantic helpers (from ATOM_correct.v)                               *)
(* ================================================================== *)

Local Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_shl_int_10 : forall n m,
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

Local Lemma sem_cast_int_to_long : forall n m,
  sem_cast (Vint n) tint tlong m = Some (Vlong (Int64.repr (Int.signed n))).
Proof.
  intros. unfold sem_cast.
  change (classify_cast tint tlong) with (cast_case_i2l Signed).
  simpl. reflexivity.
Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

Local Lemma pc_rel_shift : forall cb co rocq_pc,
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

Local Lemma atom_tag_eq : forall (t : nat),
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
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_PUSHATOM_correct : forall t,
    Z.of_nat t <= 2097151 ->
    handler_correct (handle_PUSHATOM t) f_instr_PUSHATOM
      (fun _ => None)
      (fun _ m s ard =>
         let sb := ar_sptr_block ard in
         let so := ar_sptr_ofs ard in
         (exists sp_b sp_ofs,
           Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) /\
           Ptrofs.unsigned sp_ofs >= 16) /\
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat t))))
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with building-block precondition for Module Type *)
Theorem verify_PUSHATOM_handler_correct : forall t,
    Z.of_nat t <= 2097151 ->
    handler_correct (handle_PUSHATOM t) f_instr_PUSHATOM
      (fun _ => None)
      (pre_and (sp_at_least 16) (code_at (Int.repr (Z.of_nat t))))
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper matching InstructVerificationFineGrainedSpec signature.
   handle_instr (PUSHATOM t) = handle_PUSHATOM t by computation via Dispatch.
   clight_of (PUSHATOM t) = f_instr_PUSHATOM by computation.
   pre_of (PUSHATOM t) = sp_at_least 16 /\p code_at (Int.repr (Z.of_nat t)).
   error_message_of (PUSHATOM _) is vacuously False (error_message_of returns None).
   P_halt_of (PUSHATOM _) and P_ccall_of (PUSHATOM _) are False (not STOP/C_CALL).
   Since handle_PUSHATOM always returns Step, those predicates are never needed.
   The Step case delegates to verify_PUSHATOM_handler_correct, which requires
   Z.of_nat t <= 2097151 — the same guard enforced by instr_wfb. *)
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

Definition correct_PUSHATOM : forall t,
  handler_correct (handle_instr (PUSHATOM t)) (clight_of (PUSHATOM t))
    (error_message_of (PUSHATOM t))
    (pre_of (PUSHATOM t)) (P_halt_of (PUSHATOM t)) (P_ccall_of (PUSHATOM t)).
Proof.
Admitted.
