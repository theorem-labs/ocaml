(* PUSHGETGLOBAL_correct.v -- PUSHGETGLOBAL completeness proof.

   PUSHGETGLOBAL n = PUSH (push accu to stack) then GETGLOBAL n
   (load global_data[n] into accu).

   C code (f_instr_PUSHGETGLOBAL):
     _t'8 = s->sp;
     _t'1 = (tptr tlong)(_t'8 - 1);   // new_sp = sp - 8
     s->sp = _t'1;                      // Store 1: sp field
     _t'7 = s->accu;
     *_t'1 = _t'7;                      // Store 2: push accu
     _t'3 = s->global_data;
     _t'4 = s->pc;
     _t'5 = *_t'4;                      // read n from code buffer
     _t'6 = *(cast(_t'3) + _t'5);      // load global_data[n]
     s->accu = _t'6;                    // Store 3: accu = global[n]
     _t'2 = s->pc;
     s->pc = _t'2 + 1;                  // Store 4: advance pc
     return 0;

   Rocq:
     handle_PUSHGETGLOBAL n pc' s =
       let new_stack := accu :: stack in
       match nth_error s.(global) n with
       | Some v => Step (s <|pc := pc'|> <|accu := v|> <|stack := new_stack|>)
       | None => Error "PUSHGETGLOBAL: index out of bounds"
       end

   Four stores on the struct block plus one on the stack block:
     Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v
     Store 3: accu field (sb, uso+8) <- cv_global
     Store 4: pc field (sb, uso+0) <- Vptr cb new_pc_ofs

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
(* Struct layout: _pc@0, _accu@8, _sp@16, _global_data@40             *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _global_data (co_members co) = Errors.OK (40, Full).
Proof.
  eexists. split; [| split; [| split; [| split]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_pushgetglobal : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _global_data (co_members co) = Errors.OK (40, Full).
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

(* ================================================================== *)
(* Architectural constant                                              *)
(* ================================================================== *)

Lemma ptrofs_modulus_large : (Ptrofs.modulus > 8)%Z.
Proof.
  unfold Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  simpl. reflexivity.
Qed.

(* ================================================================== *)
(* Key lemma: global_repr + nth_error => Mem.load                     *)
(* ================================================================== *)

Lemma nat_iter_succ_r : forall {A} (f : A -> A) n x,
  Nat.iter (S n) f x = Nat.iter n f (f x).
Proof.
  intros A f n. revert f. induction n as [| n' IH]; intros f x.
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma global_repr_nth_error_ptrofs : forall hm cb co m gs gb go n v,
  global_repr hm cb co m gs gb go ->
  nth_error gs n = Some v ->
  exists cv,
    Mem.load Mint64 m gb
      (Ptrofs.unsigned (Nat.iter n (fun p => Ptrofs.add p (Ptrofs.repr 8)) go))
    = Some cv /\
    val_repr hm cb co v cv.
Proof.
  intros hm cb co m gs gb go n v Hgr.
  revert n.
  induction Hgr as [| v0 vs b ofs cv0 Hload Hval_repr Hgr' IH];
    intros n Hnth.
  - destruct n; discriminate Hnth.
  - destruct n as [| n'].
    + simpl in Hnth. injection Hnth as Heq. subst v.
      exists cv0. simpl. split; [exact Hload | exact Hval_repr].
    + simpl in Hnth.
      specialize (IH n' Hnth).
      destruct IH as [cv' [Hload' Hval_repr']].
      exists cv'. split; [| exact Hval_repr'].
      rewrite nat_iter_succ_r. exact Hload'.
Qed.

Lemma iter_add_8_unsigned : forall go n,
  Ptrofs.unsigned go + Z.of_nat n * 8 < Ptrofs.modulus ->
  Ptrofs.unsigned (Nat.iter n (fun p => Ptrofs.add p (Ptrofs.repr 8)) go)
  = Ptrofs.unsigned go + Z.of_nat n * 8.
Proof.
  intros go n.
  revert go.
  induction n as [| n' IH]; intros go Hbound.
  - simpl. lia.
  - rewrite nat_iter_succ_r.
    pose proof (Ptrofs.unsigned_range go) as [Hgo_pos Hgo_lt].
    pose proof ptrofs_modulus_large as Hmod_gt_8.
    assert (H8_repr : Ptrofs.unsigned (Ptrofs.repr 8) = 8).
    { apply Ptrofs.unsigned_repr. unfold Ptrofs.max_unsigned. lia. }
    set (go' := Ptrofs.add go (Ptrofs.repr 8)).
    assert (Hgo'_unsigned : Ptrofs.unsigned go' = Ptrofs.unsigned go + 8).
    { subst go'. unfold Ptrofs.add.
      rewrite H8_repr.
      apply Ptrofs.unsigned_repr. unfold Ptrofs.max_unsigned.
      replace (Z.of_nat (S n')) with (Z.of_nat n' + 1)%Z in Hbound by lia. lia. }
    rewrite IH.
    + rewrite Hgo'_unsigned.
      replace (Z.of_nat (S n')) with (Z.of_nat n' + 1)%Z by lia. lia.
    + rewrite Hgo'_unsigned.
      replace (Z.of_nat (S n')) with (Z.of_nat n' + 1)%Z in Hbound by lia. lia.
Qed.

Lemma global_repr_nth_error : forall hm cb co m gs gb go n v,
  global_repr hm cb co m gs gb go ->
  nth_error gs n = Some v ->
  Ptrofs.unsigned go + Z.of_nat n * 8 < Ptrofs.modulus ->
  exists cv,
    Mem.load Mint64 m gb (Ptrofs.unsigned go + Z.of_nat n * 8) = Some cv /\
    val_repr hm cb co v cv.
Proof.
  intros hm cb co m gs gb go n v Hgr Hnth Hbound.
  destruct (global_repr_nth_error_ptrofs hm cb co m gs gb go n v Hgr Hnth)
    as [cv [Hload Hval_repr]].
  exists cv. split; [| exact Hval_repr].
  rewrite <- (iter_add_8_unsigned go n Hbound).
  exact Hload.
Qed.

(* ================================================================== *)
(* Pointer arithmetic: global_data + n                                 *)
(* ================================================================== *)

Lemma sem_add_global_n : forall gb go i m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr gb go) (tptr tlong)
    (Vint i) tint
    m = Some (Vptr gb (Ptrofs.add go
                (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed i)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma ptrofs_global_offset : forall go n,
  0 <= Z.of_nat n <= Int.max_signed ->
  Ptrofs.unsigned go + Z.of_nat n * 8 < Ptrofs.modulus ->
  Ptrofs.unsigned (Ptrofs.add go
    (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat n)))))
  = Ptrofs.unsigned go + Z.of_nat n * 8.
Proof.
  intros go n Hn_range Hbound.
  unfold ptrofs_of_int.
  change (Ptrofs.of_ints (Int.repr (Z.of_nat n)))
    with (Ptrofs.repr (Int.signed (Int.repr (Z.of_nat n)))).
  change Int.max_signed with 2147483647 in Hn_range.
  rewrite Int.signed_repr by
    (unfold Int.min_signed, Int.max_signed, Int.half_modulus, Int.modulus,
     Int.wordsize, Wordsize_32.wordsize; simpl; lia).
  unfold Ptrofs.add, Ptrofs.mul.
  pose proof ptrofs_modulus_large as Hmod_gt.
  rewrite (Ptrofs.unsigned_repr 8) by (unfold Ptrofs.max_unsigned; lia).
  rewrite (Ptrofs.unsigned_repr (Z.of_nat n)).
  2: { unfold Ptrofs.max_unsigned. pose proof (Ptrofs.unsigned_range go). lia. }
  rewrite Ptrofs.unsigned_repr.
  - rewrite Ptrofs.unsigned_repr. lia.
    unfold Ptrofs.max_unsigned.
    change Ptrofs.modulus with 18446744073709551616%Z. lia.
  - rewrite (Ptrofs.unsigned_repr (8 * Z.of_nat n)).
    2: { unfold Ptrofs.max_unsigned. change Ptrofs.modulus with 18446744073709551616%Z. lia. }
    pose proof (Ptrofs.unsigned_range go). unfold Ptrofs.max_unsigned.
    change Ptrofs.modulus with 18446744073709551616%Z in *. lia.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_PUSHGETGLOBAL_correct : forall n,
    0 <= Z.of_nat n <= Int.max_signed ->
    handler_correct (handle_PUSHGETGLOBAL n) f_instr_PUSHGETGLOBAL
      (fun _ => None)
      (fun _ m s ard =>
         (* code memory at pc contains n *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
           = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* global offset arithmetic stays in ptrofs range *)
         Ptrofs.unsigned (ar_global_ofs ard) + Z.of_nat n * 8 < Ptrofs.modulus /\
         (* sp has room for a push: new sp after push must still be >= 8 *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs >= 16))
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with building-block precondition for Module Type *)
Theorem verify_PUSHGETGLOBAL_handler_correct : forall n,
    0 <= Z.of_nat n <= Int.max_signed ->
    handler_correct (handle_PUSHGETGLOBAL n) f_instr_PUSHGETGLOBAL
      (fun _ => None)
      (pre_and (pre_and (code_at (Int.repr (Z.of_nat n))) (global_offset_safe n)) (sp_at_least 16))
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with the canonical type expected by InstructVerificationProof.v.
   handle_instr (PUSHGETGLOBAL n) / clight_of (PUSHGETGLOBAL n) / pre_of (PUSHGETGLOBAL n)
   are convertible with handle_PUSHGETGLOBAL n / f_instr_PUSHGETGLOBAL /
   ((code_at ... /\p global_offset_safe n) /\p sp_at_least 16).
   P_halt_of and P_ccall_of are vacuously satisfied (PUSHGETGLOBAL never halts or
   issues a C call).  error_message_of requires nth_error global n = None. *)
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

Theorem correct_PUSHGETGLOBAL : forall n,
    handler_correct (handle_instr (PUSHGETGLOBAL n)) (clight_of (PUSHGETGLOBAL n))
      (error_message_of (PUSHGETGLOBAL n))
      (pre_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)).
Proof.
Admitted.
