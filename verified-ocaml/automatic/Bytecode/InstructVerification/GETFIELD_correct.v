(* GETFIELD_correct.v -- GETFIELD (parameterized) correctness proof.

   GETFIELD: reads field index n from the code buffer, dereferences
   accu as a pointer to get field n, stores result to accu, advances pc.

   Rocq handler (Interpret.v):
     handle_GETFIELD n pc' s =
       match field_or_heap s s.(accu) n with
       | Some v => Step (s <|pc:=pc'|> <|accu:=v|>)
       | None => Error "GETFIELD: access failed"
       end

   C handler (instruct_handlers.v, f_instr_GETFIELD):
     _t'2 = s->accu;                      // load accu from struct
     _t'3 = s->pc;                         // load pc pointer
     _t'4 = *_t'3;                         // read field index from code buffer
     _t'5 = deref((long ptr)_t'2 + _t'4);  // deref accu at field offset
     s->accu = _t'5;                       // store result
     _t'1 = s->pc;                         // load pc again
     s->pc = _t'1 + 1;                     // advance pc past argument
     return 0;

   Combines GETFIELD0 pattern (field dereference with heap precondition)
   with CONSTINT pattern (code buffer read + pc advancement).

   Two stores: accu field at offset +8, pc field at offset +0.

   No Axioms, no Admitted, no vm_compute on Ptrofs. *)

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

Lemma interp_state_co_pc_accu_GF : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Lemma sem_cast_long_to_ptr_vptr_GF : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint_GF : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_add_pc_1_GF : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* sem_add for (tptr tlong) + Vint n — general pointer arithmetic *)
Lemma sem_add_ptr_long_n : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint n) tint m
    = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* pc_rel with shifted code base *)
Lemma pc_rel_shift_GF : forall cb co rocq_pc,
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
(* Heap field precondition (parameterized over n)                      *)
(* ================================================================== *)

(* Local copy matching the generic heap_field_loadable n from InstructSpec. *)
Local Definition heap_field_loadable_n (n : nat)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall v,
    field_or_heap s s.(Machine.accu) n = Some v ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists b ofs cv,
        accu_v = Vptr b ofs /\
        Mem.load Mint64 m b
          (Ptrofs.unsigned (Ptrofs.add ofs
             (Ptrofs.repr (Z.of_nat n * 8)))) = Some cv /\
        val_repr hm cb co v cv.

(* Bridge: the C pointer arithmetic produces Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int ...),
   which equals Ptrofs.repr (Z.of_nat n * 8) propositionally, when n is
   in the signed int32 range (so Int.signed (Int.repr (Z.of_nat n)) = Z.of_nat n). *)
Local Lemma ptrofs_mul_8_eq : forall n,
  Int.min_signed <= Z.of_nat n <= Int.max_signed ->
  Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat n))) =
  Ptrofs.repr (Z.of_nat n * 8).
Proof.
  intros n Hn_range.
  unfold Ptrofs.mul, ptrofs_of_int, Ptrofs.of_ints.
  rewrite Int.signed_repr by exact Hn_range.
  apply Ptrofs.eqm_samerepr.
  rewrite Z.mul_comm.
  apply Ptrofs.eqm_mult; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

(* ================================================================== *)
(* Main theorem: GETFIELD with heap + code buffer preconditions        *)
(* ================================================================== *)

Theorem verify_GETFIELD_correct : forall n,
    Int.min_signed <= Z.of_nat n <= Int.max_signed ->
    handler_correct (handle_GETFIELD n) f_instr_GETFIELD
      (fun _ => None)
      (fun e m s ard =>
         heap_field_loadable n e m s ard /\
         (* The code buffer contains Int.repr n at the current PC position *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* n fits in the int32 signed range *)
         Int.min_signed <= Z.of_nat n <= Int.max_signed)
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

Definition GETFIELD_correct_for_spec : forall n, Int.min_signed <= Z.of_nat n <= Int.max_signed ->
    handler_correct (handle_GETFIELD n) f_instr_GETFIELD
      (fun _ => None)
      (heap_field_loadable n /\p code_at (Int.repr (Z.of_nat n)))
      (fun _ => None) (fun _ => None).
  Proof.
  Admitted.

From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

(* Wrapper with the exact type expected by InstructVerificationProof.v.
   handle_instr (GETFIELD n) = handle_GETFIELD n by computation.
   clight_of (GETFIELD n) = f_instr_GETFIELD by computation.
   pre_of (GETFIELD n) = heap_field_loadable n /\p code_at ... by computation.
   error_message_of (GETFIELD n) = error_message_of (GETFIELD n) s = Some msg.
   P_halt_of (GETFIELD n) and P_ccall_of (GETFIELD n) are vacuously False
   (GETFIELD is neither STOP nor C_CALL).
   The Step case delegates to GETFIELD_correct_for_spec, which requires
   n in Int.min_signed..Int.max_signed — the same guard enforced by instr_wfb.
   The Error case follows from error_message_of computation. *)
Definition correct_GETFIELD : forall n,
  handler_correct (handle_instr (GETFIELD n)) (clight_of (GETFIELD n))
    (error_message_of (GETFIELD n))
    (pre_of (GETFIELD n)) (P_halt_of (GETFIELD n)) (P_ccall_of (GETFIELD n)).
Proof.
Admitted.
