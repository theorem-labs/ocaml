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
From OCamlInterp.Manual Require Import Bytecode.InstructSpec.
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
    handler_correct (handle_CONSTINT n) f_instr_CONSTINT
      (fun _ m s ard =>
         (* The code buffer contains Int.repr n at the current PC position *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr n)) /\
         (* n fits in the int32 signed range *)
         Int.min_signed <= n <= Int.max_signed)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intro n.
  intros e le m s.
  unfold handler_correct, handle_CONSTINT. simpl.

  intros ard Hpre Hstep_pre.
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

  destruct Hstep_pre as (Hcode_load & Hn_range).

  (* Structural invariants *)
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  (* Block separation from abs_rel inline facts *)
  pose proof Hsp_ne_sb as Hsp_ne_sb. fold sb in Hsp_ne_sb.
  pose proof Hgb_ne_sb as Hgb_ne. fold sb in Hgb_ne.
  pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  (* Composite environment: co_is with _pc@0, _accu@8 *)
  destruct interp_state_co_pc_accu as [co_is [Hco [Hpc_offset Haccu_offset]]].

  (* pc_ptr is a concrete Vptr *)
  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* Tagged value *)
  set (tagged_n := Int64.repr (n * 2 + 1)).
  set (tagged_v := Vlong tagged_n).

  (* Store 1: accu field at (sb, uso+8) <- tagged_v *)
  destruct (store_succeeds_sb m sb so 8 accu_v Hsb_writable Haccu_load ltac:(lia) ltac:(lia) tagged_v)
    as [m1 Hstore1].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

  (* New pc after advancement *)
  set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
  set (new_pc_v := Vptr cb new_pc_ofs).

  (* pc field in m1: unaffected by store1 at offset +8 *)
  assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 8)
             (Ptrofs.unsigned so + 0) tagged_v (Vptr cb pc_ofs)
             Hstore1 Hpc_load).
    left. lia. }

  (* Store 2: pc field at (sb, uso+0) <- new_pc_v *)
  destruct (store_succeeds_sb m1 sb so 0 (Vptr cb pc_ofs) Hsb_writable_m1 Hpc_load_m1 ltac:(lia) ltac:(lia) new_pc_v)
    as [m2 Hstore2].

  (* Code load survives store1 (different block) *)
  assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
            Some (Vint (Int.repr n))).
  { erewrite Mem.load_store_other.
    - exact Hcode_load.
    - exact Hstore1.
    - left. exact Hcb_ne. }

  (* Witnesses *)
  set (le' := PTree.set _t'1 (Vptr cb pc_ofs)
              (PTree.set _t'3 (Vint (Int.repr n))
              (PTree.set _t'2 (Vptr cb pc_ofs) le))).
  exists le'. exists m2.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ============================================================== *)
  (* Part 1: exec via computational evaluator                        *)
  (* ============================================================== *)
  {
    apply (eval_stmt_to_exec clight_ge 20).
    eval_cbn.

    (* ============================================================ *)
    (* S1: Sset _t'2 (s->pc) -- read pc pointer from struct         *)
    (* ============================================================ *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hpc_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load; eval_cbn.

    (* ============================================================ *)
    (* S2: Sset _t'3 (deref _t'2) -- read [*]pc = Vint (Int.repr n) *)
    (* ============================================================ *)
    rewrite PTree.gss; eval_cbn.
    rewrite Hcode_load; eval_cbn.

    (* ============================================================ *)
    (* S3: Sassign (s->accu) (((long)_t'3 << 1) + 1)               *)
    (*                                                                *)
    (* Lvalue: Efield (Ederef _s ...) _accu tlong                    *)
    (* Rvalue: Ebinop Oadd (Ebinop Oshl (Ecast _t'3 tlong) 1) 1    *)
    (* ============================================================ *)
    (* Lvalue resolution *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.

    (* Rvalue: _t'3 *)
    rewrite PTree.gss; eval_cbn.
    (* Ecast _t'3 tint -> tlong *)
    rewrite (sem_cast_int_to_long (Int.repr n) m); eval_cbn.
    (* Oshl (cast result) 1 *)
    rewrite (sem_shl_long_int_1 (Int64.repr (Int.signed (Int.repr n))) m); eval_cbn.
    (* Oadd (shift result) 1 *)
    rewrite (sem_add_long_int_1
      (Int64.shl (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 1)) m); eval_cbn.
    (* sem_cast tlong -> tlong for assign *)
    rewrite (sem_cast_long_vlong
      (Int64.add (Int64.shl (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 1))
                 (Int64.repr 1))); eval_cbn.

    (* Try store: first ptrofs *)
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    (* Replace tagged value *)
    replace (Int64.add (Int64.shl (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 1))
                       (Int64.repr 1))
      with tagged_n by (subst tagged_n; symmetry; apply tagged_int_eq; exact Hn_range).
    fold tagged_v.
    rewrite Hstore1; eval_cbn.

    (* S4: Sset _t'1 (s->pc) -- read pc pointer again from m1
       le is: set _t'3 ... (set _t'2 ... le), need to skip 2
       Hco and Hpc_offset already resolved all composite/field_offset *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m1; eval_cbn.

    (* S5: Sassign (s->pc) (_t'1 + 1) -- advance pc
       le is: set _t'1 ... (set _t'3 ... (set _t'2 ... le)), need to skip 3 *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.

    (* Rvalue: _t'1 + 1 *)
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_pc_1 cb pc_ofs m1); eval_cbn.
    rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.

    (* Store to pc field *)
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    fold new_pc_v.
    rewrite Hstore2; eval_cbn.

    (* S6: Sreturn 0 *)
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

    (* pc field at uso+0: written by store2 *)
    assert (Hpc_load2 : Mem.load Mint64 m2 sb (uso + 0) = Some new_pc_v).
    { pose proof (load_after_store_same m1 m2 sb (uso + 0) new_pc_v Hstore2) as Htmp.
      unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }

    (* accu field at uso+8: written by store1, unaffected by store2 *)
    assert (Haccu_load2 : Mem.load Mint64 m2 sb (uso + 8) = Some tagged_v).
    { assert (Haccu_m1 : Mem.load Mint64 m1 sb (uso + 8) = Some tagged_v).
      { pose proof (load_after_store_same m m1 sb (uso + 8) tagged_v Hstore1) as Htmp.
        subst tagged_v. rewrite load_result_vlong in Htmp. exact Htmp. }
      apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 8)
               new_pc_v tagged_v Hstore2 Haccu_m1). right. lia. }

    (* sp field at uso+16: unaffected by both stores *)
    assert (Hsp_load2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
    { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m1 sb (uso + 8) (uso + 16)
                 tagged_v (Vptr sp_b sp_ofs) Hstore1 Hsp_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 16)
               new_pc_v (Vptr sp_b sp_ofs) Hstore2 Hsp_m1). right. lia. }

    (* env field at uso+24: unaffected *)
    assert (Henv_load2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
    { assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m1 sb (uso + 8) (uso + 24)
                 tagged_v env_v Hstore1 Henv_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 24)
               new_pc_v env_v Hstore2 Henv_m1). right. lia. }

    (* extra_args field at uso+32: unaffected *)
    assert (Hextra_load2 : Mem.load Mint64 m2 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { assert (Hextra_m1 : Mem.load Mint64 m1 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m1 sb (uso + 8) (uso + 32)
                 tagged_v _ Hstore1 Hextra_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 32)
               new_pc_v _ Hstore2 Hextra_m1). right. lia. }

    (* global_data field at uso+40: unaffected *)
    assert (Hgd_load2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
    { assert (Hgd_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m1 sb (uso + 8) (uso + 40)
                 tagged_v gd_ptr Hstore1 Hgd_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 40)
               new_pc_v gd_ptr Hstore2 Hgd_m1). right. lia. }

    (* trap_sp field at uso+48: unaffected *)
    assert (Hts_load2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
    { assert (Hts_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (uso + 8) (uso + 48)
                 tagged_v ts_ptr Hstore1 Hts_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 48)
               new_pc_v ts_ptr Hstore2 Hts_m1). right. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le' *)
    { subst le'.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      exact Hle_s. }

    (* 2. pc field -- updated to new_pc_v *)
    { exists new_pc_v. split.
      - exact Hpc_load2.
      - simpl. subst new_pc_v new_pc_ofs.
        apply pc_rel_shift. }

    (* 3. accu field -- updated to Val_int n *)
    { exists tagged_v. split.
      - exact Haccu_load2.
      - simpl. subst tagged_v tagged_n.
        exact (vr_int _ _ _ n). }

    (* 4. sp field -- unchanged *)
    { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load2.
      - reflexivity.
      - simpl.
        eapply stack_repr_co_shift.
        eapply (stack_repr_store_other_block hm cb co m1 m2 _ sp_b sp_ofs sb (uso + 0) new_pc_v).
        + eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b sp_ofs sb (uso + 8) tagged_v).
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
      - simpl.
        eapply global_repr_co_shift.
        eapply (global_repr_store_other_block hm cb co m1 m2 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (uso + 0) new_pc_v).
        + eapply (global_repr_store_other_block hm cb co m m1 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sb (uso + 8) tagged_v).
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

(* Exported version with named building-block precondition *)
Theorem verify_CONSTINT_handler_correct : forall n,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_CONSTINT n) f_instr_CONSTINT
      (code_at (Int.repr n))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros n Hn.
  apply handler_correct_weaken with
    (sp := fun _ m s ard =>
       Mem.load Mint32 m (ar_code_base_block ard)
         (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
            (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
       = Some (Vint (Int.repr n)) /\
       Int.min_signed <= n <= Int.max_signed).
  - exact (verify_CONSTINT_correct n).
  - intros e le m s ard _ Hca.
    unfold code_at in Hca.
    exact (conj Hca Hn).
Qed.
