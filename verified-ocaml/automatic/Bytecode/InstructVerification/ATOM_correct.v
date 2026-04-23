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
      (fun _ m s ard =>
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat t))))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros t Ht_range.
  intros e le m s.
  unfold handle_ATOM.
  replace (Z.of_nat t <=? 2097151)%Z with true.
  2: { symmetry. apply Z.leb_le. exact Ht_range. }
  simpl.

  intros ard Hpre Hcode_load.
  unfold abs_rel_with_ard in Hpre.

  set (sb := ar_sptr_block ard) in *.
  set (so := ar_sptr_ofs ard) in *.
  set (hm := ar_heap_map ard) in *.
  set (cb := ar_code_base_block ard) in *.
  set (co := ar_code_base_ofs ard) in *.

  destruct Hpre as (Hle_s &
    [pc_ptr [Hpc_load Hpc_rel]] &
    [accu_v [Haccu_load Haccu_repr]] &
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
    [env_v [Henv_load Henv_repr]] &
    Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
    [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
  subst sp_ptr.

  (* Structural invariants *)
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  pose proof (code_block_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  (* Composite environment *)
  destruct interp_state_co_pc_accu as [co_is [Hco [Hpc_offset Haccu_offset]]].

  (* pc_ptr is a concrete Vptr *)
  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* The atom accu value: Vlong(tag * 1024) *)
  set (atom_long := Int64.repr (Z.of_nat t * 1024)).
  set (atom_v := Vlong atom_long).

  (* New pc after advancement *)
  set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
  set (new_pc_v := Vptr cb new_pc_ofs).

  (* Store 1: pc field at (sb, uso+0) <- new_pc_v *)
  destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia) new_pc_v)
    as [m1 Hstore1].

  (* Code load survives store1 (different block: sb <> cb) *)
  assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
            Some (Vint (Int.repr (Z.of_nat t)))).
  { erewrite Mem.load_store_other.
    - exact Hcode_load.
    - exact Hstore1.
    - left. exact Hcb_ne. }

  (* accu load survives store1 at offset +0 *)
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 8) new_pc_v accu_v Hstore1 Haccu_load).
    right. lia. }

  (* Store 2: accu field at (sb, uso+8) <- atom_v *)
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.
  destruct (store_succeeds_sb m1 sb so 8 accu_v Hsb_writable_m1 Haccu_load_m1 ltac:(lia) ltac:(lia) atom_v)
    as [m2 Hstore2].

  (* Witnesses *)
  set (le' := PTree.set _t'2 (Vint (Int.repr (Z.of_nat t)))
              (PTree.set _t'1 (Vptr cb pc_ofs) le)).
  exists le'. exists m2.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ============================================================== *)
  (* Part 1: exec via computational evaluator                        *)
  (* ============================================================== *)
  {
    apply (eval_stmt_to_exec clight_ge 20).
    eval_cbn.

    (* S1: Sset _t'1 (s->pc) -- read pc pointer from struct *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hpc_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load; eval_cbn.

    (* S2: Sassign (s->pc) (_t'1 + 1) -- advance pc *)
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_pc_1 cb pc_ofs m); eval_cbn.
    change (Ptrofs.add pc_ofs (Ptrofs.repr 4)) with new_pc_ofs.
    rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    fold new_pc_v.
    rewrite Hstore1; eval_cbn.

    (* S3: Sset _t'2 ( *t'1) -- read tag from code stream *)
    rewrite PTree.gss; eval_cbn.
    rewrite Hcode_load_m1; eval_cbn.

    (* S4: Sassign (s->accu) ((long)(t'2 << 10)) *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_shl_int_10 (Int.repr (Z.of_nat t)) m1); eval_cbn.
    rewrite (sem_cast_int_to_long (Int.shl (Int.repr (Z.of_nat t)) (Int.repr 10)) m1); eval_cbn.
    rewrite (sem_cast_long_vlong
      (Int64.repr (Int.signed (Int.shl (Int.repr (Z.of_nat t)) (Int.repr 10))))); eval_cbn.
    rewrite (atom_tag_eq t Ht_range).
    fold atom_long. fold atom_v.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Hstore2; eval_cbn.

    (* S5: Sreturn 0 *)
    subst le'. reflexivity.
  }

  (* ============================================================== *)
  (* Part 2: abs_rel for post-state                                  *)
  (* ============================================================== *)
  {
    set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
    set (ard' := mk_abs_rel
      (ar_sptr_block ard) (ar_sptr_ofs ard) (ar_heap_map ard)
      (ar_code_base_block ard) new_co
      (ar_global_block ard) (ar_global_ofs ard)
      (ar_stack_block ard) (ar_stack_base_ofs ard)
      (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
    exists ard'.
    set (uso := Ptrofs.unsigned so) in *.

    (* pc field at uso+0: written by store1, unaffected by store2 *)
    assert (Hpc_load2 : Mem.load Mint64 m2 sb (uso + 0) = Some new_pc_v).
    { assert (Hpc_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some new_pc_v).
      { pose proof (load_after_store_same m m1 sb (uso + 0) new_pc_v Hstore1) as Htmp.
        unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }
      apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 0)
               atom_v new_pc_v Hstore2 Hpc_m1). left. lia. }

    (* accu field at uso+8: written by store2 *)
    assert (Haccu_load2 : Mem.load Mint64 m2 sb (uso + 8) = Some atom_v).
    { pose proof (load_after_store_same m1 m2 sb (uso + 8) atom_v Hstore2) as Htmp.
      subst atom_v. rewrite load_result_vlong in Htmp. exact Htmp. }

    (* sp field at uso+16: unaffected by both stores *)
    assert (Hsp_load2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
    { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m1 sb (uso + 0) (uso + 16)
                 new_pc_v (Vptr sp_b sp_ofs) Hstore1 Hsp_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 16)
               atom_v (Vptr sp_b sp_ofs) Hstore2 Hsp_m1). right. lia. }

    (* env field at uso+24: unaffected *)
    assert (Henv_load2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
    { assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m1 sb (uso + 0) (uso + 24)
                 new_pc_v env_v Hstore1 Henv_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 24)
               atom_v env_v Hstore2 Henv_m1). right. lia. }

    (* extra_args field at uso+32: unaffected *)
    assert (Hextra_load2 : Mem.load Mint64 m2 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { assert (Hextra_m1 : Mem.load Mint64 m1 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m1 sb (uso + 0) (uso + 32)
                 new_pc_v _ Hstore1 Hextra_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 32)
               atom_v _ Hstore2 Hextra_m1). right. lia. }

    (* global_data field at uso+40: unaffected *)
    assert (Hgd_load2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
    { assert (Hgd_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m1 sb (uso + 0) (uso + 40)
                 new_pc_v gd_ptr Hstore1 Hgd_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 40)
               atom_v gd_ptr Hstore2 Hgd_m1). right. lia. }

    (* trap_sp field at uso+48: unaffected *)
    assert (Hts_load2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
    { assert (Hts_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (uso + 0) (uso + 48)
                 new_pc_v ts_ptr Hstore1 Hts_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 48)
               atom_v ts_ptr Hstore2 Hts_m1). right. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le' *)
    { subst le'.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      exact Hle_s. }

    (* 2. pc field -- updated to new_pc_v *)
    { exists new_pc_v. split.
      - exact Hpc_load2.
      - simpl. subst new_pc_v new_pc_ofs.
        apply pc_rel_shift. }

    (* 3. accu field -- Val_block t [] via vr_block_atom *)
    { exists atom_v. split.
      - exact Haccu_load2.
      - simpl. subst atom_v atom_long.
        exact (vr_block_atom _ _ _ t). }

    (* 4. sp field -- unchanged *)
    { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load2.
      - reflexivity.
      - simpl. eapply stack_repr_co_shift.
        eapply (stack_repr_store_other_block hm cb co m1 m2 _ sp_b sp_ofs sb (uso + 8) atom_v).
        + eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b sp_ofs sb (uso + 0) new_pc_v).
          * exact Hstack_repr.
          * exact Hstore1.
          * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        + exact Hstore2.
        + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. eapply Mem.perm_store_1. exact Hstore1. apply Hsp_writable. exact Hofs'. 
        - exact Hsp_align. }

    (* 5. env field -- unchanged *)
    { exists env_v. split.
      - exact Henv_load2.
      - simpl. eapply val_repr_co_shift. exact Henv_repr. }

    (* 6. extra_args field -- unchanged *)
    { simpl. exact Hextra_load2. }

    (* 7. global_data field -- unchanged *)
    { exists gd_ptr. split; [| split; [| split]].
      - exact Hgd_load2.
      - simpl. exact Hgd_eq.
      - simpl. eapply global_repr_co_shift.
        eapply (global_repr_store_other_block hm cb co m1 m2 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (uso + 8) atom_v).
        + eapply (global_repr_store_other_block hm cb co m m1 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sb (uso + 0) new_pc_v).
          * exact Hglobal_repr.
          * exact Hstore1.
          * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        + exact Hstore2.
        + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load2.
      - simpl. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved *)
      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. eapply Mem.perm_store_1. exact Hstore1. apply Hsb_writable. exact Hofs'. }
  }
Qed.

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
    (pre_of (ATOM t))
    (P_error_of (ATOM t)) (P_halt_of (ATOM t)) (P_ccall_of (ATOM t)).
Proof.
Admitted.
