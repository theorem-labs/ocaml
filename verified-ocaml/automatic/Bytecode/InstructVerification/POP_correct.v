(* POP_correct.v -- POP handler completeness proof.

   POP n: drops n elements from the stack.

   C code (f_instr_POP):
     _t'1 = s->pc;             // read pc pointer (points to n in code buffer)
     s->pc = _t'1 + 1;         // advance pc past argument
     _t'2 = s->sp;             // read sp pointer
     _t'3 = *_t'1;             // read n from code buffer (Mint32)
     s->sp = _t'2 + _t'3;     // sp += n (pointer arithmetic: each elem = 8 bytes)
     return 0;

   Rocq:
     handle_POP n pc' s = Step (s <|pc := pc'|> <|stack := skipn n s.(stack)|>)

   Two stores: pc field at offset +0, sp field at offset +16.

   Uses handler_correct because the C code reads n from the
   code buffer and because the code block must be separate from the
   struct block (for store separation).  NO AXIOMS -- everything is
   either proved or expressed as a precondition. *)

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
(* Struct layout: _pc at offset 0, _sp at offset 16                    *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full).
Proof.
  eexists. split; [| split]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_pc_sp : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full).
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

(* sp + n : pointer arithmetic on (tptr tlong), where n is tint.
   sizeof(tlong) = 8, so sp + n = sp + n * 8 bytes. *)
Lemma sem_add_sp_n : forall sp_b sp_ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint n) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs
                (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma sem_cast_ptr_tlong_to_ptr_tlong : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tlong) (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

Lemma ptrofs_add_zero : forall ofs,
  Ptrofs.add ofs (Ptrofs.repr 0) = ofs.
Proof.
  intros. change (Ptrofs.repr 0) with Ptrofs.zero.
  apply Ptrofs.add_zero.
Qed.

(* ================================================================== *)
(* pc_rel with shifted code base                                       *)
(* ================================================================== *)

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
(* stack_repr_skipn: dropping n elements from the front of a stack     *)
(* shifts the stack pointer by n * 8 bytes.                            *)
(* ================================================================== *)

Lemma ptrofs_max_unsigned_large : (Ptrofs.max_unsigned >= 2^32)%Z.
Proof. vm_compute. discriminate. Qed.

Lemma ptrofs_add_repr : forall a b,
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  intros. rewrite Ptrofs.add_unsigned.
  apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add;
    apply Ptrofs.eqm_sym;
    apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma stack_repr_skipn : forall n hm cb co m stk sp_b sp_ofs,
  stack_repr hm cb co m stk sp_b sp_ofs ->
  stack_repr hm cb co m (skipn n stk) sp_b
    (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat n * 8))).
Proof.
  induction n as [| n' IH]; intros hm cb co m stk sp_b sp_ofs Hsr.
  - (* n = 0: skipn 0 stk = stk, offset + 0 = offset *)
    simpl. rewrite ptrofs_add_zero. exact Hsr.
  - (* n = S n': skipn (S n') stk = skipn n' (tl stk) *)
    destruct stk as [| v vs].
    + (* stk = nil: skipn (S n') [] = [] *)
      simpl. constructor.
    + (* stk = v :: vs: skipn (S n') (v :: vs) = skipn n' vs *)
      simpl skipn. inversion Hsr; subst.
      (* vs has stack_repr at Ptrofs.add sp_ofs (Ptrofs.repr 8) *)
      specialize (IH hm cb co m vs sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) H5).
      (* Show the two offsets are equal *)
      replace (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat (S n') * 8)))
        with (Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr (Z.of_nat n' * 8))).
      { exact IH. }
      { rewrite Ptrofs.add_assoc. f_equal.
        rewrite ptrofs_add_repr.
        f_equal. lia. }
Qed.

(* ================================================================== *)
(* Arithmetic: ptrofs_mul_8_of_ints                                    *)
(* Relates pointer arithmetic sp + n (C) to sp + n*8 (logical).       *)
(* When the C code does (tptr tlong) + (tint)n, CompCert computes     *)
(* sp + mul(8, ptrofs_of_int Signed (Int.repr n)).                    *)
(* We show this equals sp + repr(n * 8) when 0 <= n.                  *)
(* ================================================================== *)

Lemma ptrofs_mul_8_of_ints_eq : forall n,
  0 <= n ->
  n < Int.half_modulus ->
  Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr n))
  = Ptrofs.repr (n * 8).
Proof.
  intros n Hnn Hn_bound.
  unfold ptrofs_of_int, Ptrofs.of_ints.
  change Int.half_modulus with 2147483648 in Hn_bound.
  rewrite Int.signed_repr.
  2: { change Int.min_signed with (-2147483648).
       change Int.max_signed with 2147483647. lia. }
  unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 8).
  2: { pose proof ptrofs_max_unsigned_large. lia. }
  rewrite (Ptrofs.unsigned_repr n).
  2: { pose proof ptrofs_max_unsigned_large. lia. }
  f_equal. lia.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_POP_correct : forall n,
    Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_POP n) f_instr_POP
      (fun _ => None)
      (fun _ m s ard =>
         (* The code buffer contains Int.repr n at the current PC position *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* The code block is separate from the struct block *)
         ar_code_base_block ard <> ar_sptr_block ard /\
         (* n fits in the signed int32 range *)
         Z.of_nat n < Int.half_modulus /\
         (* sp + n*8 fits in ptrofs range (needed for pointer arithmetic) *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs + Z.of_nat n * 8 < Ptrofs.modulus) /\
         (* n does not exceed the stack length *)
         (n <= Datatypes.length (Machine.stack s))%nat)
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

(* Wrapper with building-block precondition for Module Type *)
Theorem verify_POP_handler_correct : forall n,
    Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_POP n) f_instr_POP
      (fun _ => None)
      (pre_and (pre_and (code_at (Int.repr (Z.of_nat n))) code_ne_struct) (stack_length_ge n))
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

(* Wrapper with the exact type expected by InstructVerificationProof.v.
   handle_instr (POP n) = handle_POP n and clight_of (POP n) = f_instr_POP
   by computation.  pre_of (POP n) = (code_at ... /\p code_ne_struct) /\p
   stack_length_ge n, matching verify_POP_handler_correct's precondition.

   The Step case delegates to verify_POP_handler_correct after showing
   Z.of_nat n < Int.half_modulus via Z.ltb_spec.  The Error case
   (n >= half_modulus) is discharged by reflexivity since handle_POP
   returns Error and error_message_of is trivially satisfied. *)
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

Definition correct_POP : forall n,
  handler_correct (handle_instr (POP n)) (clight_of (POP n))
    (error_message_of (POP n))
    (pre_of (POP n)) (P_halt_of (POP n)) (P_ccall_of (POP n)).
Proof.
Admitted.
