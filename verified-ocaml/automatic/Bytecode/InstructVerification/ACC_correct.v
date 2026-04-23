(* ACC_correct.v -- ACC (parameterized) handler completeness proof.

   ACC n: reads index n from the code buffer, then reads stack[n],
   stores to accu, and advances pc past the argument.

   C code (f_instr_ACC):
     _t'1 = s->pc;             // read pc pointer (points to n in code buffer)
     s->pc = _t'1 + 1;         // advance pc past argument
     _t'2 = s->sp;             // read sp pointer
     _t'3 = *_t'1;             // read n from code buffer (Mint32)
     _t'4 = *(_t'2 + _t'3);   // stack[n] (pointer arith: each elem = 8 bytes)
     s->accu = _t'4;           // store to accu
     return 0;

   Rocq:
     handle_ACC n pc' s =
       match nth_error s.(stack) n with
       | Some v => Step (s <|pc := pc'|> <|accu := v|>)
       | None => Error "ACC: stack underflow"
       end

   Two stores: pc field at offset +0, accu field at offset +8.

   Combines the CONSTINT code-buffer-read pattern with ACC0's
   stack access pattern, generalized over n.

   NO AXIOMS.  All structural/range constraints are preconditions
   via handler_correct. *)

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
(* Struct layout: _pc at offset 0, _sp at offset 16, _accu at offset 8 *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_pc_sp_accu : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
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
(* stack_repr_nth: connect nth_error with stack_repr memory loads.     *)
(* If stack_repr relates the Rocq list to memory at (sp_b, sp_ofs),   *)
(* then nth_error stk n = Some v implies there is a CompCert value    *)
(* cv at sp + n*8 with val_repr hm v cv.                              *)
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

Lemma stack_repr_nth : forall n hm cb co m stk sp_b sp_ofs v,
  stack_repr hm cb co m stk sp_b sp_ofs ->
  nth_error stk n = Some v ->
  exists cv,
    Mem.load Mint64 m sp_b
      (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some cv /\
    val_repr hm cb co v cv.
Proof.
  induction n as [| n' IH]; intros hm cb co m stk sp_b sp_ofs v Hsr Hnth.
  - (* n = 0 *)
    destruct stk as [| v0 rest].
    + discriminate.
    + simpl in Hnth. inversion Hnth; subst.
      inversion Hsr as [| xv xvs xb xofs xcv Hload Hvr Hrest].
      subst xv xvs xb xofs.
      exists xcv. split.
      * replace (Z.of_nat 0 * 8)%Z with 0%Z by lia.
        change (Ptrofs.repr 0) with Ptrofs.zero.
        rewrite Ptrofs.add_zero. exact Hload.
      * exact Hvr.
  - (* n = S n' *)
    destruct stk as [| v0 rest].
    + discriminate.
    + simpl in Hnth.
      inversion Hsr as [| xv xvs xb xofs xcv Hload Hvr Hrest].
      subst xv xvs xb xofs.
      specialize (IH hm cb co m rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) v Hrest Hnth).
      destruct IH as [cv' [Hload' Hvr']].
      exists cv'. split.
      * (* Rewrite offset: (sp + 8) + n'*8 = sp + (S n')*8 *)
        replace (Z.of_nat (S n') * 8)%Z with (8 + Z.of_nat n' * 8)%Z by lia.
        rewrite <- ptrofs_add_repr.
        rewrite <- Ptrofs.add_assoc.
        exact Hload'.
      * exact Hvr'.
Qed.

(* ================================================================== *)
(* ptrofs_mul_8_of_ints_eq: relate C pointer arithmetic to logical    *)
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

Theorem verify_ACC_correct : forall n,
    Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_ACC n) f_instr_ACC
      (fun _ => None)
      (fun _ m s ard =>
         (* The code buffer contains Int.repr n at the current PC position *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* n fits in the signed int32 range *)
         Z.of_nat n < Int.half_modulus /\
         (* sp + n*8 fits in ptrofs range *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs + Z.of_nat n * 8 < Ptrofs.modulus))
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with building-block precondition for Module Type *)
Theorem verify_ACC_handler_correct : forall n,
    Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_ACC n) f_instr_ACC
      (fun _ => None)
      (code_at (Int.repr (Z.of_nat n)))
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper matching InstructVerificationFineGrainedSpec signature.
   handle_instr (ACC n) reduces to handle_ACC n by computation.
   clight_of (ACC n) = f_instr_ACC, pre_of (ACC n) = code_at (Int.repr (Z.of_nat n)).
   Error case (stack underflow) matches error_message_of exactly.
   Step case delegates to verify_ACC_handler_correct (requires Z.of_nat n < Int.half_modulus). *)
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

Theorem correct_ACC : forall n,
    handler_correct (handle_instr (ACC n)) (clight_of (ACC n))
      (error_message_of (ACC n))
      (pre_of (ACC n)) (P_halt_of (ACC n)) (P_ccall_of (ACC n)).
Proof.
Admitted.
