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
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.InstructSpec.
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
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros t Ht_range.
  intros e le m s. unfold handler_correct, handle_PUSHATOM. simpl.
  intros ard Hpre Hstep_pre. unfold abs_rel_with_ard in Hpre.
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

  (* Extract preconditions *)
  destruct Hstep_pre as [[sp_b' [sp_ofs' [Hsp_load' Hsp_ge16]]] Hcode_load].
  simpl in Hsp_load'. fold sb so in Hsp_load'.
  assert (sp_b' = sp_b /\ sp_ofs' = sp_ofs) as [-> ->]
    by (rewrite Hsp_load in Hsp_load'; injection Hsp_load'; auto).

  (* Structural invariants *)
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  pose proof (code_block_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  (* Composite environment facts *)
  destruct interp_state_co_all as [co_is [Hco [Hpc_offset [Haccu_offset Hsp_offset]]]].

  (* pc_ptr is a concrete Vptr *)
  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* New sp after push *)
  set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
  assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 8).
  { subst new_sp_ofs. unfold Ptrofs.sub.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
    apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range sp_ofs).
    unfold Ptrofs.max_unsigned. lia. }

  (* New pc after advancement *)
  set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
  set (new_pc_v := Vptr cb new_pc_ofs).

  (* Atom value *)
  set (atom_long := Int64.repr (Z.of_nat t * 1024)).
  set (atom_v := Vlong atom_long).

  (* Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs *)
  destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) (Vptr sp_b new_sp_ofs)) as [m1 Hstore1].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

  (* Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v (push accu to stack) *)
  assert (Halign_new : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs)).
  { rewrite Hnew_sp_unsigned. simpl align_chunk.
    apply Z.divide_sub_r. exact Hsp_align. exists 1; lia. }
  destruct (store_to_sp_after_sb_store m m1 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)
              sp_b (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s)))
              (Ptrofs.unsigned new_sp_ofs)
              Hstore1 Hsp_writable
              ltac:(rewrite Hnew_sp_unsigned; lia)
              ltac:(rewrite Hnew_sp_unsigned; lia)
              Halign_new accu_v) as [m2 Hstore2].

  (* Store 3: pc field (sb, uso+0) <- new_pc_v *)
  (* First show pc field survived stores 1 and 2 *)
  assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) = Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
             (Ptrofs.unsigned so + 0) (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs)
             Hstore1 Hpc_load). left. lia. }
  assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) = Some (Vptr cb pc_ofs)).
  { erewrite Mem.load_store_other; [exact Hpc_load_m1 | exact Hstore2 |].
    left. exact (not_eq_sym Hsp_ne_sb). }
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore2 Hsb_writable_m1) as Hsb_writable_m2.
  destruct (store_succeeds_sb m2 sb so 0 (Vptr cb pc_ofs) Hsb_writable_m2 Hpc_load_m2 ltac:(lia) ltac:(lia) new_pc_v) as [m3 Hstore3].

  (* Code load survives stores 1-3 (different block: cb <> sb, cb <> sp_b) *)
  assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
            Some (Vint (Int.repr (Z.of_nat t)))).
  { erewrite Mem.load_store_other; [exact Hcode_load | exact Hstore1 |].
    left. exact Hcb_ne. }
  assert (Hcode_load_m2 : Mem.load Mint32 m2 cb (Ptrofs.unsigned pc_ofs) =
            Some (Vint (Int.repr (Z.of_nat t)))).
  { erewrite Mem.load_store_other; [exact Hcode_load_m1 | exact Hstore2 |].
    left. exact Hcb_ne_sp. }
  assert (Hcode_load_m3 : Mem.load Mint32 m3 cb (Ptrofs.unsigned pc_ofs) =
            Some (Vint (Int.repr (Z.of_nat t)))).
  { erewrite Mem.load_store_other; [exact Hcode_load_m2 | exact Hstore3 |].
    left. exact Hcb_ne. }

  (* Store 4: accu field (sb, uso+8) <- atom_v *)
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
             (Ptrofs.unsigned so + 8) (Vptr sp_b new_sp_ofs) accu_v
             Hstore1 Haccu_load). left. lia. }
  assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { erewrite Mem.load_store_other; [exact Haccu_load_m1 | exact Hstore2 |].
    left. exact (not_eq_sym Hsp_ne_sb). }
  assert (Haccu_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 8) new_pc_v accu_v
             Hstore3 Haccu_load_m2). right. lia. }
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore3 Hsb_writable_m2) as Hsb_writable_m3.
  destruct (store_succeeds_sb m3 sb so 8 accu_v Hsb_writable_m3 Haccu_load_m3 ltac:(lia) ltac:(lia) atom_v) as [m4 Hstore4].

  (* Witnesses *)
  set (le' := PTree.set _t'3 (Vint (Int.repr (Z.of_nat t)))
              (PTree.set _t'2 (Vptr cb pc_ofs)
              (PTree.set _t'4 accu_v
              (PTree.set _t'1 (Vptr sp_b new_sp_ofs)
              (PTree.set _t'5 (Vptr sp_b sp_ofs) le))))).
  exists le'. exists m4.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ============================================================== *)
  (* Part 1: exec via computational evaluator                        *)
  (* ============================================================== *)
  {
    apply (eval_stmt_to_exec clight_ge 20).
    eval_cbn.

    (* S1: Sset _t'5 (s->sp) -- read sp pointer from struct *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* S2: Sset _t'1 (cast (sub _t'5 1) (tptr tlong)) *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_sub_sp_1; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.

    (* S3: Sassign (s->sp) _t'1 -- store new sp *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    fold new_sp_ofs.
    rewrite Hstore1; eval_cbn.

    (* S4: Sset _t'4 (s->accu) -- read accu *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m1; eval_cbn.

    (* S5: Sassign (deref _t'1) _t'4 -- push accu to *new_sp *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Haccu_repr); eval_cbn.
    fold new_sp_ofs.
    rewrite Hstore2; eval_cbn.

    (* S6: Sset _t'2 (s->pc) -- read pc pointer *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Hpc_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m2; eval_cbn.

    (* S7: Sassign (s->pc) (_t'2 + 1) -- advance pc *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_pc_1 cb pc_ofs m2); eval_cbn.
    change (Ptrofs.add pc_ofs (Ptrofs.repr 4)) with new_pc_ofs.
    rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    fold new_pc_v.
    rewrite Hstore3; eval_cbn.

    (* S8: Sset _t'3 (deref _t'2) -- read tag from code stream *)
    rewrite PTree.gss; eval_cbn.
    rewrite Hcode_load_m3; eval_cbn.

    (* S9: Sassign (s->accu) ((long)(_t'3 << 10)) -- compute and store atom *)
    (* Haccu_offset was already applied globally by S4, so eval_cbn resolves the lvalue *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_shl_int_10 (Int.repr (Z.of_nat t)) m3); eval_cbn.
    rewrite (sem_cast_int_to_long (Int.shl (Int.repr (Z.of_nat t)) (Int.repr 10)) m3); eval_cbn.
    rewrite (sem_cast_long_vlong
      (Int64.repr (Int.signed (Int.shl (Int.repr (Z.of_nat t)) (Int.repr 10))))); eval_cbn.
    rewrite (atom_tag_eq t Ht_range).
    fold atom_long. fold atom_v.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Hstore4; eval_cbn.

    (* S10: Sreturn 0 *)
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

    (* Helper: loads on sb survive store 2 (different block: sp_b vs sb) *)
    assert (Hload_sb_m2 : forall ofs v,
      Mem.load Mint64 m1 sb ofs = Some v ->
      Mem.load Mint64 m2 sb ofs = Some v).
    { intros ofs v Hload1.
      erewrite Mem.load_store_other; [exact Hload1 | exact Hstore2 |].
      left. exact (not_eq_sym Hsp_ne_sb). }

    (* Helper: loads on sp_b survive store 3 (different block: sb vs sp_b) *)
    assert (Hload_spb_m3 : forall ofs v,
      Mem.load Mint64 m2 sp_b ofs = Some v ->
      Mem.load Mint64 m3 sp_b ofs = Some v).
    { intros ofs v Hload2.
      erewrite Mem.load_store_other; [exact Hload2 | exact Hstore3 |].
      left. exact Hsp_ne_sb. }

    (* Helper: loads on sp_b survive store 4 (different block: sb vs sp_b) *)
    assert (Hload_spb_m4 : forall ofs v,
      Mem.load Mint64 m3 sp_b ofs = Some v ->
      Mem.load Mint64 m4 sp_b ofs = Some v).
    { intros ofs v Hload3.
      erewrite Mem.load_store_other; [exact Hload3 | exact Hstore4 |].
      left. exact Hsp_ne_sb. }

    (* pc field at uso+0: written by store 3, survives store 4 *)
    assert (Hpc_load4 : Mem.load Mint64 m4 sb (uso + 0) = Some new_pc_v).
    { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 0)
               atom_v new_pc_v Hstore4).
      - pose proof (load_after_store_same m2 m3 sb (uso + 0) new_pc_v Hstore3) as Htmp.
        unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp.
      - left. lia. }

    (* accu field at uso+8: written by store 4 *)
    assert (Haccu_load4 : Mem.load Mint64 m4 sb (uso + 8) = Some atom_v).
    { pose proof (load_after_store_same m3 m4 sb (uso + 8) atom_v Hstore4) as Htmp.
      subst atom_v. rewrite load_result_vlong in Htmp. exact Htmp. }

    (* sp field at uso+16: written by store 1, survives stores 2-4 *)
    assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { pose proof (load_after_store_same m m1 sb (uso + 16) (Vptr sp_b new_sp_ofs) Hstore1) as Htmp.
      simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
    assert (Hsp_load4 : Mem.load Mint64 m4 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 16)
               atom_v (Vptr sp_b new_sp_ofs) Hstore4).
      - apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 16)
                 new_pc_v (Vptr sp_b new_sp_ofs) Hstore3).
        + apply Hload_sb_m2. exact Hsp_load_m1.
        + right. lia.
      - right. lia. }

    (* env field at uso+24: unaffected by all 4 stores *)
    assert (Henv_load4 : Mem.load Mint64 m4 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 24)
               atom_v env_v Hstore4).
      - apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 24)
                 new_pc_v env_v Hstore3).
        + apply Hload_sb_m2.
          apply (load_after_store_other m m1 sb (uso + 16) (uso + 24)
                   (Vptr sp_b new_sp_ofs) env_v Hstore1 Henv_load).
          right. lia.
        + right. lia.
      - right. lia. }

    (* extra_args field at uso+32: unaffected *)
    assert (Hextra_load4 : Mem.load Mint64 m4 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 32)
               atom_v _ Hstore4).
      - apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 32)
                 new_pc_v _ Hstore3).
        + apply Hload_sb_m2.
          apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
                   (Vptr sp_b new_sp_ofs) _ Hstore1 Hextra_load).
          right. lia.
        + right. lia.
      - right. lia. }

    (* global_data field at uso+40: unaffected *)
    assert (Hgd_load4 : Mem.load Mint64 m4 sb (uso + 40) = Some gd_ptr).
    { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 40)
               atom_v gd_ptr Hstore4).
      - apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 40)
                 new_pc_v gd_ptr Hstore3).
        + apply Hload_sb_m2.
          apply (load_after_store_other m m1 sb (uso + 16) (uso + 40)
                   (Vptr sp_b new_sp_ofs) gd_ptr Hstore1 Hgd_load).
          right. lia.
        + right. lia.
      - right. lia. }

    (* trap_sp field at uso+48: unaffected *)
    assert (Hts_load4 : Mem.load Mint64 m4 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 48)
               atom_v ts_ptr Hstore4).
      - apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 48)
                 new_pc_v ts_ptr Hstore3).
        + apply Hload_sb_m2.
          apply (load_after_store_other m m1 sb (uso + 16) (uso + 48)
                   (Vptr sp_b new_sp_ofs) ts_ptr Hstore1 Hts_load).
          right. lia.
        + right. lia.
      - right. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le' *)
    { subst le'.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      exact Hle_s. }

    (* 2. pc field -- updated to new_pc_v, ard' has advanced code_base_ofs *)
    { exists new_pc_v. split.
      - exact Hpc_load4.
      - simpl. subst new_pc_v new_pc_ofs.
        apply pc_rel_shift. }

    (* 3. accu field -- Val_block t [] via vr_block_atom *)
    { exists atom_v. split.
      - exact Haccu_load4.
      - simpl. subst atom_v atom_long.
        exact (vr_block_atom _ _ _ t). }

    (* 4. sp field -- updated to new_sp_ofs; stack gets accu prepended *)
    { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load4.
      - reflexivity.
      - eapply stack_repr_co_shift.
        eapply (stack_repr_store_other_block hm cb co m3 m4 _ sp_b new_sp_ofs sb (uso + 8) atom_v).
        + eapply (stack_repr_store_other_block hm cb co m2 m3 _ sp_b new_sp_ofs sb (uso + 0) new_pc_v).
          * eapply stack_repr_cons_after_store.
            -- eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b sp_ofs sb (uso + 16) (Vptr sp_b new_sp_ofs)).
               exact Hstack_repr. exact Hstore1. exact (not_eq_sym Hsp_ne_sb).
            -- eapply val_repr_co_shift. exact Haccu_repr.
            -- exact Hstore2.
            -- exact Hsp_ge8.
            -- exact Hsp_rep.
          * exact Hstore3.
          * exact (not_eq_sym Hsp_ne_sb).
        + exact Hstore4.
        + exact (not_eq_sym Hsp_ne_sb).
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - (* sp_ofs_ge8 for new sp *)
        rewrite Hnew_sp_unsigned. lia.
      - (* sp_rep *)
        simpl length. rewrite Nat2Z.inj_succ. rewrite Hnew_sp_unsigned. lia.
      - (* sp_writable *)
        simpl length. rewrite Nat2Z.inj_succ. rewrite Hnew_sp_unsigned.
        replace (Ptrofs.unsigned sp_ofs - 8 + 8 * Z.succ (Z.of_nat (length (Machine.stack s))))
          with (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) by lia.
        intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore4.
        eapply Mem.perm_store_1. exact Hstore3.
        eapply Mem.perm_store_1. exact Hstore2.
        eapply Mem.perm_store_1. exact Hstore1.
        apply Hsp_writable. exact Hofs'.
      - (* sp_aligned *)
        exact Halign_new. }

    (* 5. env field -- unchanged *)
    { exists env_v. split.
      - exact Henv_load4.
      - eapply val_repr_co_shift. exact Henv_repr. }

    (* 6. extra_args field -- unchanged *)
    { simpl. exact Hextra_load4. }

    (* 7. global_data field -- unchanged *)
    { exists gd_ptr. split; [| split; [| split]].
      - exact Hgd_load4.
      - simpl. exact Hgd_eq.
      - simpl.
        eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m3 m4 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (uso + 8) atom_v).
        + apply (global_repr_store_other_block hm cb co m2 m3 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sb (uso + 0) new_pc_v).
          * apply (global_repr_store_other_block hm cb co m1 m2 _
                     (ar_global_block ard) (ar_global_ofs ard)
                     sp_b (Ptrofs.unsigned new_sp_ofs) accu_v).
            { apply (global_repr_store_other_block hm cb co m m1 _
                       (ar_global_block ard) (ar_global_ofs ard)
                       sb (uso + 16) (Vptr sp_b new_sp_ofs)
                       Hglobal_repr Hstore1).
              intro Heq2; exact (Hgb_ne (eq_sym Heq2)). }
            { exact Hstore2. }
            { exact Hsp_ne_gb. }
          * exact Hstore3.
          * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        + exact Hstore4.
        + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load4.
      - simpl. exact Htrap_rel. }

    (* 9. sb_writable *)
    { intros ofs' Hofs'.
      eapply Mem.perm_store_1. exact Hstore4.
      eapply Mem.perm_store_1. exact Hstore3.
      eapply Mem.perm_store_1. exact Hstore2.
      eapply Mem.perm_store_1. exact Hstore1.
      apply Hsb_writable. exact Hofs'. }
  }
Qed.

(* Wrapper with building-block precondition for Module Type *)
Theorem verify_PUSHATOM_handler_correct : forall t,
    Z.of_nat t <= 2097151 ->
    handler_correct (handle_PUSHATOM t) f_instr_PUSHATOM
      (pre_and (sp_at_least 16) (code_at (Int.repr (Z.of_nat t))))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros t Ht.
  eapply handler_correct_weaken.
  - exact (verify_PUSHATOM_correct t Ht).
  - intros e le m s ard _ [Hsp Hca]. exact (conj Hsp Hca).
Qed.
