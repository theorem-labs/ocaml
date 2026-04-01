(* PUSHCONSTINT_correct.v -- PUSHCONSTINT completeness proof.

   PUSHCONSTINT n = PUSH then CONSTINT n.
   C code:
     _t'6 = s->sp;
     _t'1 = (tptr tlong)(_t'6 - 1);   // new_sp = sp - 8
     s->sp = _t'1;                      // store 1: sp field
     _t'5 = s->accu;
     *_t'1 = _t'5;                      // store 2: push accu
     _t'3 = s->pc;
     _t'4 = *_t'3;                      // read n from code
     s->accu = ((long)_t'4 << 1) + 1;   // store 3: accu = tagged n
     _t'2 = s->pc;
     s->pc = _t'2 + 1;                  // store 4: advance pc
     return 0;

   Rocq:
     handle_PUSHCONSTINT n pc' s =
       Step (s <|pc := pc'|> <|accu := Val_int n|>
               <|stack := accu :: stack|>)

   Four stores on the struct block:
     Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v
     Store 3: accu field (sb, uso+8) <- Vlong tagged_n
     Store 4: pc field (sb, uso+0) <- Vptr cb new_pc_ofs

   NO AXIOMS.  All invariants that CONSTINT_correct.v took as axioms
   (code_block_ne_sptr, code_contains_n, tagged_int_eq) are turned
   into preconditions via handler_correct_with_pre. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
Require Import instruct_handlers.
Require Import InstructSpec.
Require Import StepToBigstep.
Require Import HandlerLemmas.

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
(* Struct layout: _sp@16, _accu@8, _pc@0                              *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
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
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers (reused from CONSTINT_correct)                     *)
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

(* Preconditions (replacing the axioms from CONSTINT_correct.v):
   1. code_block_ne_sptr: code base block distinct from struct block
   2. code_contains_n: code memory at pc contains Vint (Int.repr n)
   3. tagged_int_eq: tagged integer arithmetic identity
   4. code_block_ne_sp: code block distinct from stack block *)
Theorem verify_PUSHCONSTINT_correct : forall n,
    handler_correct_with_pre (handle_PUSHCONSTINT n) f_instr_PUSHCONSTINT
      (fun m s ard =>
         (* code block separate from struct block *)
         ar_code_base_block ard <> ar_sptr_block ard /\
         (* code block separate from stack block -- needed for store survival *)
         (forall sp_b sp_ofs sp_ptr,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some sp_ptr ->
            sp_ptr = Vptr sp_b sp_ofs ->
            ar_code_base_block ard <> sp_b) /\
         (* code memory at pc contains n *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
           = Some (Vint (Int.repr n)) /\
         (* tagged integer identity *)
         Int64.add (Int64.shl (Int64.repr (Int.signed (Int.repr n)))
                              (Int64.repr 1))
                   (Int64.repr 1) = Int64.repr (n * 2 + 1))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intro n.
  intros e le m s.
  unfold handler_correct_with_pre, handle_PUSHCONSTINT. simpl.

  intros ard Hpre Hextra_pre.
  destruct Hextra_pre as (Hcb_ne & Hcb_ne_sp & Hcode_load & Htagged_eq).

  (* Unpack abs_rel_with_ard *)
  set (sb := ar_sptr_block ard) in *.
  set (so := ar_sptr_ofs ard) in *.
  set (hm := ar_heap_map ard) in *.
  set (cb := ar_code_base_block ard) in *.
  set (co := ar_code_base_ofs ard) in *.
  destruct Hpre as (Hle_s &
    [pc_ptr [Hpc_load Hpc_rel]] &
    [accu_v [Haccu_load Haccu_repr]] &
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb Hcb_ne_sp2]]]]]]]] &
    [env_v [Henv_load Henv_repr]] &
    Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
    [ts_ptr [Hts_load Htrap_rel]]).
  subst sp_ptr.

  (* Code block separate from stack block *)
  assert (Hcb_ne_spb : cb <> sp_b).
  { exact Hcb_ne_sp2. }

  (* Structural invariants *)
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep. fold sb in Hblock_sep.
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  pose proof (sp_ofs_ge_8 hm m (Machine.stack s) sp_b sp_ofs Hstack_repr) as Hsp_ge8.

  (* Composite environment facts *)
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
  (* pc field offset -- from interp_state_co_all, projecting just the pc offset *)
  assert (Hpc_offset : field_offset (genv_cenv clight_ge) _pc (co_members co_is) = Errors.OK (0, Full)).
  { destruct interp_state_co_all as [co_is2 [Hco2 [Hpc2 _]]].
    rewrite Hco in Hco2. injection Hco2 as <-. exact Hpc2. }

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

  (* Tagged value *)
  set (tagged_n := Int64.repr (n * 2 + 1)).
  set (tagged_v := Vlong tagged_n).

  (* New pc after advancement *)
  set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
  set (new_pc_v := Vptr cb new_pc_ofs).

  (* ================================================================ *)
  (* Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs           *)
  (* ================================================================ *)
  destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 16)
              (Vptr sp_b sp_ofs) (Vptr sp_b new_sp_ofs) Hsp_load) as [m1 Hstore1].

  (* ================================================================ *)
  (* Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v                    *)
  (* ================================================================ *)
  destruct (store_to_other_block m m1 sb (Ptrofs.unsigned so + 16)
              (Vptr sp_b new_sp_ofs) sp_b (Ptrofs.unsigned new_sp_ofs) accu_v
              Hstore1 (not_eq_sym Hblock_sep)
              ltac:(rewrite Hnew_sp_unsigned; lia)) as [m2 Hstore2].

  (* ================================================================ *)
  (* Store 3: accu field (sb, uso+8) <- tagged_v                       *)
  (* ================================================================ *)
  (* First show accu field survived stores 1 and 2 *)
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
             (Ptrofs.unsigned so + 8) (Vptr sp_b new_sp_ofs) accu_v
             Hstore1 Haccu_load). left. lia. }
  assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { erewrite Mem.load_store_other; [exact Haccu_load_m1 | exact Hstore2 |].
    left. exact (not_eq_sym Hblock_sep). }
  destruct (store_succeeds_from_load m2 sb (Ptrofs.unsigned so + 8)
              accu_v tagged_v Haccu_load_m2) as [m3 Hstore3].

  (* ================================================================ *)
  (* Store 4: pc field (sb, uso+0) <- new_pc_v                        *)
  (* ================================================================ *)
  (* pc field survived stores 1, 2, 3 *)
  assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
             (Ptrofs.unsigned so + 0) (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs)
             Hstore1 Hpc_load). left. lia. }
  assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { erewrite Mem.load_store_other; [exact Hpc_load_m1 | exact Hstore2 |].
    left. exact (not_eq_sym Hblock_sep). }
  assert (Hpc_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 8)
             (Ptrofs.unsigned so + 0) tagged_v (Vptr cb pc_ofs)
             Hstore3 Hpc_load_m2). left. lia. }
  destruct (store_succeeds_from_load m3 sb (Ptrofs.unsigned so + 0)
              (Vptr cb pc_ofs) new_pc_v Hpc_load_m3)
    as [m4 Hstore4].

  (* ================================================================ *)
  (* Code memory survives all 4 stores                                 *)
  (* ================================================================ *)
  (* Store 1 at sb, store 2 at sp_b, store 3 at sb, store 4 at sb.
     Code load is at cb which is != sb and != sp_b. *)
  assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs)
            = Some (Vint (Int.repr n))).
  { erewrite Mem.load_store_other; [exact Hcode_load | exact Hstore1 |].
    left. exact Hcb_ne. }
  assert (Hcode_load_m2 : Mem.load Mint32 m2 cb (Ptrofs.unsigned pc_ofs)
            = Some (Vint (Int.repr n))).
  { erewrite Mem.load_store_other; [exact Hcode_load_m1 | exact Hstore2 |].
    left. exact Hcb_ne_spb. }

  (* pc field in m3: needed for the second s->pc read *)
  (* Already have Hpc_load_m3 above *)

  (* ================================================================ *)
  (* Witnesses                                                         *)
  (* ================================================================ *)
  set (le' := PTree.set _t'2 (Vptr cb pc_ofs)
              (PTree.set _t'4 (Vint (Int.repr n))
              (PTree.set _t'3 (Vptr cb pc_ofs)
              (PTree.set _t'5 accu_v
              (PTree.set _t'1 (Vptr sp_b new_sp_ofs)
              (PTree.set _t'6 (Vptr sp_b sp_ofs) le)))))).
  exists le'. exists m4.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ============================================================== *)
  (* Part 1: exec via rewriting                                      *)
  (* ============================================================== *)
  {
    (* Unfold set abbreviations so hypotheses and goal stay in sync
       after eval_cbn (which unfolds set definitions). *)
    unfold so, sb in *.

    apply (eval_stmt_to_exec clight_ge 20).
    eval_cbn.

    (* ============================================================ *)
    (* S1: Sset _t'6 (s->sp) -- read sp from struct                 *)
    (* ============================================================ *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* ============================================================ *)
    (* S2: Sset _t'1 (cast (_t'6 - 1) (tptr tlong))                 *)
    (* ============================================================ *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_sub_sp_1; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.

    (* ============================================================ *)
    (* S3: Sassign (s->sp) _t'1  -- Store 1: sp field               *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 16 ltac:(lia) ltac:(lia)).
    fold new_sp_ofs.
    rewrite Hstore1; eval_cbn.

    (* ============================================================ *)
    (* S4: Sset _t'5 (s->accu) -- read accu                         *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 8 ltac:(lia) ltac:(lia)).
    rewrite (load_after_store_other m m1 (ar_sptr_block ard)
               (Ptrofs.unsigned (ar_sptr_ofs ard) + 16)
               (Ptrofs.unsigned (ar_sptr_ofs ard) + 8) (Vptr sp_b new_sp_ofs) accu_v
               Hstore1 Haccu_load ltac:(left; lia)).
    eval_cbn.

    (* ============================================================ *)
    (* S5: Sassign (deref _t'1) _t'5 -- Store 2: push accu          *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ Haccu_repr); eval_cbn.
    fold new_sp_ofs.
    rewrite Hstore2; eval_cbn.

    (* ============================================================ *)
    (* S6: Sset _t'3 (s->pc) -- read pc pointer                     *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Hpc_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m2; eval_cbn.

    (* ============================================================ *)
    (* S7: Sset _t'4 (deref _t'3) -- read n from code               *)
    (* ============================================================ *)
    rewrite PTree.gss; eval_cbn.
    rewrite Hcode_load_m2; eval_cbn.

    (* ============================================================ *)
    (* S8: Sassign (s->accu) (((long)_t'4 << 1) + 1) -- Store 3     *)
    (* ============================================================ *)
    (* Lvalue: s->accu *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.

    (* Rvalue: _t'4 -> cast -> shl -> add *)
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_int_to_long (Int.repr n) m2); eval_cbn.
    rewrite (sem_shl_long_int_1 (Int64.repr (Int.signed (Int.repr n))) m2); eval_cbn.
    rewrite (sem_add_long_int_1
      (Int64.shl (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 1)) m2); eval_cbn.
    rewrite (sem_cast_long_vlong
      (Int64.add (Int64.shl (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 1))
                 (Int64.repr 1))); eval_cbn.

    (* Store *)
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 8 ltac:(lia) ltac:(lia)).
    replace (Int64.add (Int64.shl (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 1))
                       (Int64.repr 1))
      with tagged_n by (subst tagged_n; symmetry; exact Htagged_eq).
    fold tagged_v.
    rewrite Hstore3; eval_cbn.

    (* ============================================================ *)
    (* S9: Sset _t'2 (s->pc) -- read pc pointer again from m3       *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m3; eval_cbn.

    (* ============================================================ *)
    (* S10: Sassign (s->pc) (_t'2 + 1) -- Store 4: advance pc       *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.

    (* Rvalue: _t'2 + 1 *)
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_pc_1 cb pc_ofs m3); eval_cbn.
    rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.

    (* Store to pc field *)
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
    fold new_pc_v.
    rewrite Hstore4; eval_cbn.

    (* ============================================================ *)
    (* S11: Sreturn 0                                                *)
    (* ============================================================ *)
    subst le'. reflexivity.
  }

  (* ============================================================== *)
  (* Part 2: abs_rel for post-state                                  *)
  (* ============================================================== *)
  {
    (* Shift code_base_ofs for the post-state *)
    set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
    set (ard' := mk_abs_rel
      (ar_sptr_block ard) (ar_sptr_ofs ard) (ar_heap_map ard)
      (ar_code_base_block ard) new_co
      (ar_global_block ard) (ar_global_ofs ard)
      (ar_stack_block ard) (ar_stack_base_ofs ard)
      (ar_code_ne_sptr ard) (ar_code_ne_global ard)
      (ar_sptr_ofs_bound ard)).
    exists ard'.
    set (uso := Ptrofs.unsigned so) in *.

    (* Helper: loads on sb survive store 2 (different block: sp_b vs sb) *)
    assert (Hload_sb_m2 : forall ofs v,
      Mem.load Mint64 m1 sb ofs = Some v ->
      Mem.load Mint64 m2 sb ofs = Some v).
    { intros ofs v Hload1.
      erewrite Mem.load_store_other; [exact Hload1 | exact Hstore2 |].
      left. exact (not_eq_sym Hblock_sep). }

    (* Helper: loads on sp_b survive store 3 (different block: sb vs sp_b) *)
    assert (Hload_spb_m3 : forall ofs v,
      Mem.load Mint64 m2 sp_b ofs = Some v ->
      Mem.load Mint64 m3 sp_b ofs = Some v).
    { intros ofs v Hload2.
      erewrite Mem.load_store_other; [exact Hload2 | exact Hstore3 |].
      left. exact Hblock_sep. }

    (* Helper: loads on sp_b survive store 4 (different block: sb vs sp_b) *)
    assert (Hload_spb_m4 : forall ofs v,
      Mem.load Mint64 m3 sp_b ofs = Some v ->
      Mem.load Mint64 m4 sp_b ofs = Some v).
    { intros ofs v Hload3.
      erewrite Mem.load_store_other; [exact Hload3 | exact Hstore4 |].
      left. exact Hblock_sep. }

    (* pc field at uso+0: survived stores 1,2,3; written by store 4 *)
    assert (Hpc_load4 : Mem.load Mint64 m4 sb (uso + 0) = Some new_pc_v).
    { pose proof (load_after_store_same m3 m4 sb (uso + 0) new_pc_v Hstore4) as Htmp.
      unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }

    (* accu field at uso+8: written by store 3, survives store 4 *)
    assert (Haccu_load_m3 : Mem.load Mint64 m3 sb (uso + 8) = Some tagged_v).
    { pose proof (load_after_store_same m2 m3 sb (uso + 8) tagged_v Hstore3) as Htmp.
      subst tagged_v. rewrite load_result_vlong in Htmp. exact Htmp. }
    assert (Haccu_load4 : Mem.load Mint64 m4 sb (uso + 8) = Some tagged_v).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 8)
               new_pc_v tagged_v Hstore4 Haccu_load_m3). right. lia. }

    (* sp field at uso+16: written by store 1, survives stores 2, 3, 4 *)
    assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { pose proof (load_after_store_same m m1 sb (uso + 16)
                    (Vptr sp_b new_sp_ofs) Hstore1) as Htmp.
      simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
    assert (Hsp_load_m2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { exact (Hload_sb_m2 _ _ Hsp_load_m1). }
    assert (Hsp_load_m3 : Mem.load Mint64 m3 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 16)
               tagged_v (Vptr sp_b new_sp_ofs) Hstore3 Hsp_load_m2). right. lia. }
    assert (Hsp_load4 : Mem.load Mint64 m4 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 16)
               new_pc_v (Vptr sp_b new_sp_ofs) Hstore4 Hsp_load_m3). right. lia. }

    (* env field at uso+24: unaffected by all 4 stores *)
    assert (Henv_load_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 24)
               (Vptr sp_b new_sp_ofs) env_v Hstore1 Henv_load). right. lia. }
    assert (Henv_load_m2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
    { exact (Hload_sb_m2 _ _ Henv_load_m1). }
    assert (Henv_load_m3 : Mem.load Mint64 m3 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 24)
               tagged_v env_v Hstore3 Henv_load_m2). right. lia. }
    assert (Henv_load4 : Mem.load Mint64 m4 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 24)
               new_pc_v env_v Hstore4 Henv_load_m3). right. lia. }

    (* extra_args field at uso+32: unaffected *)
    assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
               (Vptr sp_b new_sp_ofs) _ Hstore1 Hextra_load). right. lia. }
    assert (Hextra_load_m2 : Mem.load Mint64 m2 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { exact (Hload_sb_m2 _ _ Hextra_load_m1). }
    assert (Hextra_load_m3 : Mem.load Mint64 m3 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 32)
               tagged_v _ Hstore3 Hextra_load_m2). right. lia. }
    assert (Hextra_load4 : Mem.load Mint64 m4 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 32)
               new_pc_v _ Hstore4 Hextra_load_m3). right. lia. }

    (* global_data field at uso+40: unaffected *)
    assert (Hgd_load_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 40)
               (Vptr sp_b new_sp_ofs) gd_ptr Hstore1 Hgd_load). right. lia. }
    assert (Hgd_load_m2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
    { exact (Hload_sb_m2 _ _ Hgd_load_m1). }
    assert (Hgd_load_m3 : Mem.load Mint64 m3 sb (uso + 40) = Some gd_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 40)
               tagged_v gd_ptr Hstore3 Hgd_load_m2). right. lia. }
    assert (Hgd_load4 : Mem.load Mint64 m4 sb (uso + 40) = Some gd_ptr).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 40)
               new_pc_v gd_ptr Hstore4 Hgd_load_m3). right. lia. }

    (* trap_sp field at uso+48: unaffected *)
    assert (Hts_load_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 48)
               (Vptr sp_b new_sp_ofs) ts_ptr Hstore1 Hts_load). right. lia. }
    assert (Hts_load_m2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
    { exact (Hload_sb_m2 _ _ Hts_load_m1). }
    assert (Hts_load_m3 : Mem.load Mint64 m3 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 48)
               tagged_v ts_ptr Hstore3 Hts_load_m2). right. lia. }
    assert (Hts_load4 : Mem.load Mint64 m4 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 48)
               new_pc_v ts_ptr Hstore4 Hts_load_m3). right. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].

    (* 1. _s is in le' *)
    { subst le'.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      exact Hle_s. }

    (* 2. pc field -- updated to new_pc_v, with shifted code_base *)
    { exists new_pc_v. split.
      - exact Hpc_load4.
      - simpl. subst new_pc_v new_pc_ofs.
        apply pc_rel_shift. }

    (* 3. accu field -- updated to Val_int n *)
    { exists tagged_v. split.
      - exact Haccu_load4.
      - simpl. subst tagged_v tagged_n.
        exact (vr_int _ n). }

    (* 4. sp field -- updated to new_sp_ofs; stack gets accu prepended *)
    { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
      split; [| split; [| split; [| split; [| split]]]].
      - exact Hsp_load4.
      - reflexivity.
      - simpl.
        (* Build stack_repr through all 4 stores *)
        assert (Hstack_m1 : stack_repr hm m1 (Machine.stack s) sp_b sp_ofs).
        { apply (stack_repr_store_other_block hm m m1 _ sp_b sp_ofs sb
                   (uso + 16) (Vptr sp_b new_sp_ofs)
                   Hstack_repr Hstore1).
          intro Heq; exact (Hblock_sep (eq_sym Heq)). }
        assert (Hstack_cons_m2 : stack_repr hm m2 (Machine.accu s :: Machine.stack s) sp_b new_sp_ofs).
        { exact (stack_repr_cons_after_store hm m1 m2
                   (Machine.stack s) sp_b sp_ofs (Machine.accu s) accu_v
                   Hstack_m1 Haccu_repr Hstore2 Hsp_ge8). }
        assert (Hstack_cons_m3 : stack_repr hm m3 (Machine.accu s :: Machine.stack s) sp_b new_sp_ofs).
        { apply (stack_repr_store_other_block hm m2 m3 _ sp_b new_sp_ofs sb
                   (uso + 8) tagged_v
                   Hstack_cons_m2 Hstore3).
          intro Heq; exact (Hblock_sep (eq_sym Heq)). }
        apply (stack_repr_store_other_block hm m3 m4 _ sp_b new_sp_ofs sb
                 (uso + 0) new_pc_v
                 Hstack_cons_m3 Hstore4).
                intro Heq; exact (Hblock_sep (eq_sym Heq)).
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp2. }

    (* 5. env field -- unchanged *)
    { exists env_v. split.
      - exact Henv_load4.
      - simpl. exact Henv_repr. }

    (* 6. extra_args field -- unchanged *)
    { simpl. exact Hextra_load4. }

    (* 7. global_data field -- unchanged *)
    { exists gd_ptr. split; [| split; [| split]].
      - exact Hgd_load4.
      - simpl. exact Hgd_eq.
      - simpl.
        (* global_repr survives all 4 stores (different blocks) *)
        apply (global_repr_store_other_block hm m3 m4 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (uso + 0) new_pc_v).
        + apply (global_repr_store_other_block hm m2 m3 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sb (uso + 8) tagged_v).
          * apply (global_repr_store_other_block hm m1 m2 _
                     (ar_global_block ard) (ar_global_ofs ard)
                     sp_b (Ptrofs.unsigned new_sp_ofs) accu_v).
            -- apply (global_repr_store_other_block hm m m1 _
                       (ar_global_block ard) (ar_global_ofs ard)
                       sb (uso + 16) (Vptr sp_b new_sp_ofs)
                       Hglobal_repr Hstore1).
               intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
            -- exact Hstore2.
            -- exact Hsp_ne_gb.
          * exact Hstore3.
          * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        + exact Hstore4.
        + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load4.
      - simpl. exact Htrap_rel. }
  }
Qed.
