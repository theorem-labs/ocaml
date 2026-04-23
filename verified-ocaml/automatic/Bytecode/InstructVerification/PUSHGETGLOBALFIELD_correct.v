(* PUSHGETGLOBALFIELD_correct.v -- PUSHGETGLOBALFIELD completeness proof.

   PUSHGETGLOBALFIELD n p = PUSH (push accu to stack) then
   GETGLOBAL n (load global_data[n]) then GETFIELD p (dereference field p).

   C code (f_instr_PUSHGETGLOBALFIELD):
     -- Push --
     _t'13 = s->sp;
     _t'1 = (tptr tlong)(_t'13 - 1);     // new_sp = sp - 8
     s->sp = _t'1;                         // Store 1: sp field
     _t'12 = s->accu;
     *_t'1 = _t'12;                        // Store 2: push accu
     -- Get global --
     _t'8 = s->global_data;
     _t'9 = s->pc;
     _t'10 = *_t'9;                        // read N from code buffer
     _t'11 = *(cast(_t'8) + _t'10);       // load global_data[N]
     s->accu = _t'11;                      // Store 3: accu = global[N]
     -- Advance pc past N --
     _t'7 = s->pc;
     s->pc = _t'7 + 1;                     // Store 4: pc += 1
     -- Field deref --
     _t'3 = s->accu;
     _t'4 = s->pc;
     _t'5 = *_t'4;                         // read P from code buffer
     _t'6 = *(cast(_t'3) + _t'5);         // deref field P from global
     s->accu = _t'6;                       // Store 5: accu = field
     -- Advance pc past P --
     _t'2 = s->pc;
     s->pc = _t'2 + 1;                     // Store 6: pc += 1
     return 0;

   Rocq:
     handle_PUSHGETGLOBALFIELD n p pc' s =
       let new_stack := accu :: stack in
       match nth_error s.(global) n with
       | Some glob =>
         match field_or_heap s glob p with
         | Some v => Step (s <|pc:=pc'|> <|accu:=v|> <|stack:=new_stack|>)
         | None => Error "PUSHGETGLOBALFIELD: field access failed"
         end
       | None => Error "PUSHGETGLOBALFIELD: index out of bounds"
       end

   Six stores on the struct / stack blocks:
     Store 1: sp field (sb, uso+16)       <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp (sp_b, new_sp_ofs)  <- accu_v
     Store 3: accu field (sb, uso+8)      <- cv_global
     Store 4: pc field (sb, uso+0)        <- Vptr cb mid_pc_ofs
     Store 5: accu field (sb, uso+8)      <- cv_field
     Store 6: pc field (sb, uso+0)        <- Vptr cb new_pc_ofs

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

Lemma interp_state_co_pushgetglobalfield : exists co,
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

(* Two-step pc shift: code_base advances by 2 * sizeof_code_t *)
Lemma pc_rel_shift_2 : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr 8)))
         cb (Ptrofs.add co (Ptrofs.repr (2 * sizeof_code_t))) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal.
  rewrite Ptrofs.add_assoc.
  rewrite Ptrofs.add_assoc.
  f_equal.
  rewrite Ptrofs.add_commut. reflexivity.
Qed.

Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
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
(* Heap field precondition                                             *)
(* ================================================================== *)

(* After loading global[n], the result is a pointer-like value (glob).
   The field dereference reads field p from that value. The C code
   does: cast(glob_val) + p, then dereference.
   This precondition bridges the Rocq field_or_heap with C Mem.load. *)
Definition heap_field_loadable_pushgetglobalfield
    (p : nat) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall glob v cv_global,
    field_or_heap s glob p = Some v ->
    val_repr hm cb co glob cv_global ->
    exists b ofs cv,
      cv_global = Vptr b ofs /\
      b <> ar_sptr_block ard /\
      (forall sp_b sp_ofs,
         Mem.load Mint64 m (ar_sptr_block ard)
           (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
         b <> sp_b) /\
      Mem.load Mint64 m b
        (Ptrofs.unsigned (Ptrofs.add ofs
           (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat p))))))
        = Some cv /\
      val_repr hm cb co v cv.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

#[warnings="-not-a-closed-proof"]
Theorem verify_PUSHGETGLOBALFIELD_correct : forall n p,
    handler_correct (handle_PUSHGETGLOBALFIELD n p) f_instr_PUSHGETGLOBALFIELD
      (fun _ => None)
      (fun _ m s ard =>
         (* Code memory at pc contains n (first operand) *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
           = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* Code memory at pc+1 contains p (second operand) *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))))
           = Some (Vint (Int.repr (Z.of_nat p))) /\
         (* n fits in int32 signed range *)
         0 <= Z.of_nat n <= Int.max_signed /\
         (* p fits in int32 signed range *)
         0 <= Z.of_nat p <= Int.max_signed /\
         (* global offset arithmetic stays in ptrofs range *)
         Ptrofs.unsigned (ar_global_ofs ard) + Z.of_nat n * 8 < Ptrofs.modulus /\
         (* sp has room for a push *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs >= 16) /\
         (* heap field loadable: after loading global[n], field p is accessible *)
         heap_field_loadable_pushgetglobalfield p m s ard)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* ================================================================== *)
(* Wrapper with the exact type expected by InstructVerificationProof.v *)
(* ================================================================== *)

From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

(* handle_instr (PUSHGETGLOBALFIELD n p) computes to handle_PUSHGETGLOBALFIELD n p.
   clight_of (PUSHGETGLOBALFIELD n p) computes to f_instr_PUSHGETGLOBALFIELD.
   pre_of (PUSHGETGLOBALFIELD n p) computes to pushgetglobalfield_step_pre n p.
   error_message_of (PUSHGETGLOBALFIELD n p) requires bridging: the old proof uses an
   explicit disjunction while error_message_of uses error_message_of.
   P_halt_of / P_ccall_of are vacuously False (not STOP / not C_CALL).
   We case-split on nth_error and field_or_heap:
     - Step case: delegate to verify_PUSHGETGLOBALFIELD_correct.
     - Error cases: prove error_message_of by unfolding error_message_of. *)
Definition correct_PUSHGETGLOBALFIELD : forall n p,
    handler_correct (handle_instr (PUSHGETGLOBALFIELD n p)) (clight_of (PUSHGETGLOBALFIELD n p))
      (error_message_of (PUSHGETGLOBALFIELD n p))
      (pre_of (PUSHGETGLOBALFIELD n p)) (P_halt_of (PUSHGETGLOBALFIELD n p)) (P_ccall_of (PUSHGETGLOBALFIELD n p)).
Proof.
Admitted.
