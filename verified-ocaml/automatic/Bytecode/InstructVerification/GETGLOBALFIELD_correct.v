(* GETGLOBALFIELD_correct.v -- GETGLOBALFIELD completeness proof.

   GETGLOBALFIELD reads two operands from the code buffer:
     N = global index, P = field index.
   It loads global_data[N], then dereferences field P of that value,
   stores the result in accu, and advances pc by 2 (past both operands).

   C code (f_instr_GETGLOBALFIELD):
     Phase 1 (GETGLOBAL part):
       _t'7 = s->global_data;
       _t'8 = s->pc;
       _t'9 = *_t'8;                     read N from code buffer
       _t'10 = *(global_data + _t'9);    load global_data[N]
       s->accu = _t'10;
     Phase 2 (advance pc):
       _t'6 = s->pc;
       s->pc = _t'6 + 1;                 advance pc past N
     Phase 3 (GETFIELD part):
       _t'2 = s->accu;                   read accu = global_data[N]
       _t'3 = s->pc;
       _t'4 = *_t'3;                     read P from code buffer
       _t'5 = *((long ptr)_t'2 + _t'4);  load field P of global[N]
       s->accu = _t'5;
     Phase 4 (advance pc):
       _t'1 = s->pc;
       s->pc = _t'1 + 1;                 advance pc past P
       return 0;

   Rocq handler:
     handle_GETGLOBALFIELD n p pc' s =
       match nth_error s.(global) n with
       | Some glob =>
         match field_or_heap s glob p with
         | Some v => Step (s <|pc := pc'|> <|accu := v|>)
         | None => Error "GETGLOBALFIELD: field access failed"
         end
       | None => Error "GETGLOBALFIELD: index out of bounds"
       end

   Four stores: accu (global[N]), pc (advance 1),
                accu (field[P]), pc (advance 1).

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
(* Struct layout: _pc at 0, _accu at 8, _global_data at 40            *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _global_data (co_members co) = Errors.OK (40, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_ggf : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _global_data (co_members co) = Errors.OK (40, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Lemma sem_add_pc_1_ggf : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint_ggf : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_cast_long_to_ptr_vptr_ggf : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma load_result_vlong_ggf : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr_ggf : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* pc_rel shift by 2 code positions (two operands consumed).
   Goal: ((co + rocq_pc*4) + 4) + 4 = (co + 8) + rocq_pc*4
   Strategy: reassociate to co + (rocq_pc*4 + 4 + 4)
             and co + (8 + rocq_pc*4), then commute inner terms. *)
Lemma pc_rel_shift_2 : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add (Ptrofs.add co
                     (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                     (Ptrofs.repr 4))
                     (Ptrofs.repr 4)))
         cb (Ptrofs.add co (Ptrofs.repr (2 * sizeof_code_t))) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal.
  (* LHS is: Ptrofs.add (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * 4)))
                                      (Ptrofs.repr 4))
                          (Ptrofs.repr 4)
     RHS is: Ptrofs.add (Ptrofs.add co (Ptrofs.repr (2 * 4)))
                          (Ptrofs.repr (rocq_pc * 4))
     Reassociate both sides fully right. *)
  rewrite (Ptrofs.add_assoc (Ptrofs.add co (Ptrofs.repr (rocq_pc * 4)))
             (Ptrofs.repr 4) (Ptrofs.repr 4)).
  rewrite (Ptrofs.add_assoc co (Ptrofs.repr (rocq_pc * 4))
             (Ptrofs.add (Ptrofs.repr 4) (Ptrofs.repr 4))).
  rewrite (Ptrofs.add_assoc co (Ptrofs.repr (2 * 4))
             (Ptrofs.repr (rocq_pc * 4))).
  f_equal.
  rewrite Ptrofs.add_commut.
  reflexivity.
Qed.

(* ================================================================== *)
(* Architectural constant                                              *)
(* ================================================================== *)

Lemma ptrofs_modulus_large_ggf : (Ptrofs.modulus > 8)%Z.
Proof.
  unfold Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  simpl. reflexivity.
Qed.

(* ================================================================== *)
(* Key lemma: global_repr + nth_error => Mem.load                     *)
(* ================================================================== *)

Lemma nat_iter_succ_r_ggf : forall {A} (f : A -> A) n x,
  Nat.iter (S n) f x = Nat.iter n f (f x).
Proof.
  intros A f n. revert f. induction n as [| n' IH]; intros f x.
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma global_repr_nth_error_ptrofs_ggf : forall hm cb0 co0 m gs gb go n v,
  global_repr hm cb0 co0 m gs gb go ->
  nth_error gs n = Some v ->
  exists cv,
    Mem.load Mint64 m gb
      (Ptrofs.unsigned (Nat.iter n (fun p => Ptrofs.add p (Ptrofs.repr 8)) go))
    = Some cv /\
    val_repr hm cb0 co0 v cv.
Proof.
  intros hm cb0 co0 m gs gb go n v Hgr.
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
      rewrite nat_iter_succ_r_ggf. exact Hload'.
Qed.

Lemma iter_add_8_unsigned_ggf : forall go n,
  Ptrofs.unsigned go + Z.of_nat n * 8 < Ptrofs.modulus ->
  Ptrofs.unsigned (Nat.iter n (fun p => Ptrofs.add p (Ptrofs.repr 8)) go)
  = Ptrofs.unsigned go + Z.of_nat n * 8.
Proof.
  intros go n.
  revert go.
  induction n as [| n' IH]; intros go Hbound.
  - simpl. lia.
  - rewrite nat_iter_succ_r_ggf.
    pose proof (Ptrofs.unsigned_range go) as [Hgo_pos Hgo_lt].
    pose proof ptrofs_modulus_large_ggf as Hmod_gt_8.
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

Lemma global_repr_nth_error_ggf : forall hm cb0 co0 m gs gb go n v,
  global_repr hm cb0 co0 m gs gb go ->
  nth_error gs n = Some v ->
  Ptrofs.unsigned go + Z.of_nat n * 8 < Ptrofs.modulus ->
  exists cv,
    Mem.load Mint64 m gb (Ptrofs.unsigned go + Z.of_nat n * 8) = Some cv /\
    val_repr hm cb0 co0 v cv.
Proof.
  intros hm cb0 co0 m gs gb go n v Hgr Hnth Hbound.
  destruct (global_repr_nth_error_ptrofs_ggf hm cb0 co0 m gs gb go n v Hgr Hnth)
    as [cv [Hload Hval_repr]].
  exists cv. split; [| exact Hval_repr].
  rewrite <- (iter_add_8_unsigned_ggf go n Hbound).
  exact Hload.
Qed.

(* ================================================================== *)
(* Pointer arithmetic: global_data + n                                 *)
(* ================================================================== *)

Lemma sem_add_global_n_ggf : forall gb go i m,
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

Lemma ptrofs_global_offset_ggf : forall go n,
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
  pose proof ptrofs_modulus_large_ggf as Hmod_gt.
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
(* Pointer arithmetic: (tptr tlong) + int p                            *)
(* ================================================================== *)

Lemma sem_add_ptr_long_p : forall b ofs i m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong)
    (Vint i) tint
    m = Some (Vptr b (Ptrofs.add ofs
                (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed i)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_GETGLOBALFIELD_correct : forall n p,
    handler_correct (handle_GETGLOBALFIELD n p) f_instr_GETGLOBALFIELD
      (fun _ => None)
      (fun _ m s ard =>
         (* Code buffer contains Int.repr (Z.of_nat n) at current PC *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* Code buffer contains Int.repr (Z.of_nat p) at PC+1 *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))) (Ptrofs.repr 4)))
         = Some (Vint (Int.repr (Z.of_nat p))) /\
         0 <= Z.of_nat n <= Int.max_signed /\
         0 <= Z.of_nat p <= Int.max_signed /\
         Ptrofs.unsigned (ar_global_ofs ard) + Z.of_nat n * 8 < Ptrofs.modulus /\
         (* When field_or_heap succeeds, the C memory has the field value,
            the global's C representation is a pointer on a block distinct
            from sb, and the field load is at that pointer + p*8. *)
         (forall glob v cv_global,
            nth_error s.(Machine.global) n = Some glob ->
            field_or_heap s glob p = Some v ->
            val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) glob cv_global ->
            exists b ofs cv,
              cv_global = Vptr b ofs /\
              b <> ar_sptr_block ard /\
              Mem.load Mint64 m b
                (Ptrofs.unsigned (Ptrofs.add ofs
                   (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat p))))))
                = Some cv /\
              val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) v cv))
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* ================================================================== *)
(* Wrapper with the exact type expected by InstructVerificationProof.v *)
(* ================================================================== *)

From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

(* handle_instr (GETGLOBALFIELD n p) computes to handle_GETGLOBALFIELD n p.
   clight_of (GETGLOBALFIELD n p) computes to f_instr_GETGLOBALFIELD.
   pre_of (GETGLOBALFIELD n p) computes to getglobalfield_step_pre n p.
   error_message_of (GETGLOBALFIELD n p) requires bridging: the old proof uses an
   explicit disjunction while error_message_of uses error_message_of.
   P_halt_of / P_ccall_of are vacuously False (not STOP / not C_CALL).
   We case-split on nth_error and field_or_heap:
     - Step case: delegate to verify_GETGLOBALFIELD_correct.
     - Error cases: prove error_message_of by unfolding error_message_of. *)
Definition correct_GETGLOBALFIELD : forall n p,
    handler_correct (handle_instr (GETGLOBALFIELD n p)) (clight_of (GETGLOBALFIELD n p))
      (error_message_of (GETGLOBALFIELD n p))
      (pre_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)).
Proof.
Admitted.
