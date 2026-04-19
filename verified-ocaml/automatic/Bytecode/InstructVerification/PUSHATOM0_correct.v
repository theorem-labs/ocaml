(* PUSHATOM0_correct.v -- PUSHATOM0 completeness proof.

   PUSHATOM0 = PUSH then ATOM0.
   C code:
     sp = sp - 1;          // decrement sp
     *sp = accu;            // push old accu onto stack
     accu = (long)(0 << 10); // set accu to atom0 = 0
   Rocq:
     handle_PUSHATOM0 pc' s =
       Step (s <|accu := Val_block 0 []|> <|stack := accu :: stack|>)

   Three stores:
     Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v
     Store 3: accu field (sb, uso+8) <- Vlong (Int64.repr 0)

   Combines patterns of PUSHCONST0_correct.v (push + store) and
   ATOM0_correct.v (atom semantics with vr_block_atom).

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

(* handle_PUSHATOM0 returns Val_block 0 [], matching the C runtime's
   atom representation (Vlong 0) via vr_block_atom. *)

(* ================================================================== *)
(* Semantic helpers for (0 << 10) computation                          *)
(* ================================================================== *)

(* 0 << 10 as ints *)
Local Lemma sem_shl_int_0_10 : forall m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vint (Int.repr 0)) tint (Vint (Int.repr 10)) tint m =
    Some (Vint (Int.shl (Int.repr 0) (Int.repr 10))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tint tint) with (shift_case_ii Signed).
  simpl.
  change (Int.ltu (Int.repr 10) Int.iwordsize) with true.
  reflexivity.
Qed.

(* Int.shl 0 10 = 0 *)
Local Lemma int_shl_0_10 : Int.shl (Int.repr 0) (Int.repr 10) = Int.repr 0.
Proof.
  unfold Int.shl.
  change (Int.unsigned (Int.repr 10)) with 10%Z.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 10)%Z with 1024%Z.
  change (Int.unsigned (Int.repr 0)) with 0%Z.
  simpl. reflexivity.
Qed.

(* cast (int)(0 << 10) -> (long)0 *)
Local Lemma sem_cast_int_shl_0_10_to_long : forall m,
  sem_cast (Vint (Int.shl (Int.repr 0) (Int.repr 10))) tint tlong m =
    Some (Vlong (Int64.repr 0)).
Proof.
  intros. rewrite int_shl_0_10.
  unfold sem_cast.
  change (classify_cast tint tlong) with (cast_case_i2l Signed).
  simpl. reflexivity.
Qed.

(* load_result for Vlong 0 *)
Local Lemma atom0_load_result :
  Val.load_result Mint64 (Vlong (Int64.repr 0)) = Vlong (Int64.repr 0).
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_PUSHATOM0_correct :
    handler_correct handle_PUSHATOM0 f_instr_PUSHATOM0
      (fun _ m _ ard =>
         let sb := ar_sptr_block ard in
         let so := ar_sptr_ofs ard in
         exists sp_b sp_ofs,
           Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) /\
           Ptrofs.unsigned sp_ofs >= 16)
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handler_correct, handle_PUSHATOM0. simpl.
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
  (* Extract sp_ofs >= 16 from step_pre *)
  destruct Hstep_pre as [sp_b' [sp_ofs' [Hsp_load' Hsp_ge16]]].
  simpl in Hsp_load'. fold sb so in Hsp_load'.
  assert (sp_b' = sp_b /\ sp_ofs' = sp_ofs) as [-> ->]
    by (rewrite Hsp_load in Hsp_load'; injection Hsp_load'; auto).

  (* Structural invariants *)
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  (* Composite environment facts *)
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

  (* New sp after push *)
  set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
  assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 8).
  { subst new_sp_ofs. unfold Ptrofs.sub.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
    apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range sp_ofs).
    unfold Ptrofs.max_unsigned. lia. }

  (* Store 1: sp field <- new_sp *)
  destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) (Vptr sp_b new_sp_ofs)) as [m1 Hstore_sp].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore_sp Hsb_writable) as Hsb_writable_m1.

  (* Store 2: *new_sp <- accu_v (different block from sb) *)
  assert (Halign_new : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs)).
  { rewrite Hnew_sp_unsigned. simpl align_chunk.
    apply Z.divide_sub_r. exact Hsp_align. exists 1; lia. }
  destruct (store_to_sp_after_sb_store m m1 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)
              sp_b (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s)))
              (Ptrofs.unsigned new_sp_ofs)
              Hstore_sp Hsp_writable
              ltac:(rewrite Hnew_sp_unsigned; lia)
              ltac:(rewrite Hnew_sp_unsigned; lia)
              Halign_new accu_v) as [m2 Hstore_accu].

  (* Store 3: accu field <- Vlong (Int64.repr 0) -- atom0 value *)
  (* First show accu field survived stores 1 and 2 *)
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
             (Ptrofs.unsigned so + 8) (Vptr sp_b new_sp_ofs) accu_v
             Hstore_sp Haccu_load). left. lia. }
  assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { erewrite Mem.load_store_other; [exact Haccu_load_m1 | exact Hstore_accu |].
    left. exact (not_eq_sym Hsp_ne_sb). }
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore_accu Hsb_writable_m1) as Hsb_writable_m2.
  destruct (store_succeeds_sb m2 sb so 8 accu_v Hsb_writable_m2 Haccu_load_m2 ltac:(lia) ltac:(lia) (Vlong (Int64.repr 0))) as [m3 Hstore_atom].

  (* Witnesses *)
  set (le' := PTree.set _t'2 accu_v
              (PTree.set _t'1 (Vptr sp_b new_sp_ofs)
              (PTree.set _t'3 (Vptr sp_b sp_ofs) le))).
  exists le'. exists m3.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ============================================================== *)
  (* Part 1: exec via computational evaluator                        *)
  (* ============================================================== *)
  {
    apply (eval_stmt_to_exec clight_ge 10).
    eval_cbn.

    (* Statement 1: Sset _t'3 (s->sp) *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* Statement 2: Sset _t'1 (cast (sub _t'3 1) (tptr tlong)) *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_sub_sp_1; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.

    (* Statement 3: Sassign (s->sp) _t'1 *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    fold new_sp_ofs.
    rewrite Hstore_sp; eval_cbn.

    (* Statement 4: Sset _t'2 (s->accu) *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
               (Ptrofs.unsigned so + 8) (Vptr sp_b new_sp_ofs) accu_v
               Hstore_sp Haccu_load ltac:(left; lia)).
    eval_cbn.

    (* Statement 5: Sassign (deref _t'1) _t'2 *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Haccu_repr); eval_cbn.
    fold new_sp_ofs.
    rewrite Hstore_accu; eval_cbn.

    (* Statement 6: Sassign (s->accu) (cast (0 << 10) tlong) *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.

    (* rvalue: cast (0 << 10) tlong *)
    rewrite (sem_shl_int_0_10 m2); eval_cbn.
    rewrite (sem_cast_int_shl_0_10_to_long m2); eval_cbn.

    (* assignment sem_cast: tlong -> tlong *)
    rewrite (sem_cast_long_vlong (Int64.repr 0)); eval_cbn.

    (* store to accu field *)
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Hstore_atom; eval_cbn.

    (* Statement 7: Sreturn 0 *)
    subst le'. reflexivity.
  }

  (* ============================================================== *)
  (* Part 2: abs_rel for post-state                                  *)
  (* ============================================================== *)
  {
    exists ard.
    set (uso := Ptrofs.unsigned so) in *.

    (* Helper: loads on sb survive store 2 (different block: sp_b vs sb) *)
    assert (Hload_sb_m2 : forall ofs v,
      Mem.load Mint64 m1 sb ofs = Some v ->
      Mem.load Mint64 m2 sb ofs = Some v).
    { intros ofs v Hload1.
      erewrite Mem.load_store_other; [exact Hload1 | exact Hstore_accu |].
      left. exact (not_eq_sym Hsp_ne_sb). }

    (* Helper: loads on sp_b survive store 3 (different block: sb vs sp_b) *)
    assert (Hload_spb_m3 : forall ofs v,
      Mem.load Mint64 m2 sp_b ofs = Some v ->
      Mem.load Mint64 m3 sp_b ofs = Some v).
    { intros ofs v Hload2.
      erewrite Mem.load_store_other; [exact Hload2 | exact Hstore_atom |].
      left. exact Hsp_ne_sb. }

    (* pc field: uso + 0, unaffected by all 3 stores *)
    assert (Hpc_load3 : Mem.load Mint64 m3 sb (uso + 0) = Some pc_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 0)
               (Vlong (Int64.repr 0)) pc_ptr Hstore_atom).
      - apply Hload_sb_m2.
        apply (load_after_store_other m m1 sb (uso + 16) (uso + 0)
                 (Vptr sp_b new_sp_ofs) pc_ptr Hstore_sp Hpc_load).
        left. lia.
      - left. lia. }

    (* accu field: uso + 8, overwritten by store 3 *)
    assert (Haccu_load3 : Mem.load Mint64 m3 sb (uso + 8) = Some (Vlong (Int64.repr 0))).
    { pose proof (load_after_store_same m2 m3 sb (uso + 8)
                    (Vlong (Int64.repr 0)) Hstore_atom) as Htmp.
      rewrite atom0_load_result in Htmp.
      exact Htmp. }

    (* sp field: uso + 16, overwritten by store 1, survives stores 2 and 3 *)
    assert (Hsp_load3 : Mem.load Mint64 m3 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 16)
               (Vlong (Int64.repr 0)) (Vptr sp_b new_sp_ofs) Hstore_atom).
      - apply Hload_sb_m2.
        pose proof (load_after_store_same m m1 sb (uso + 16)
                      (Vptr sp_b new_sp_ofs) Hstore_sp) as Htmp.
        simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp.
      - right. lia. }

    (* env field: uso + 24, unaffected by all 3 stores *)
    assert (Henv_load3 : Mem.load Mint64 m3 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 24)
               (Vlong (Int64.repr 0)) env_v Hstore_atom).
      - apply Hload_sb_m2.
        apply (load_after_store_other m m1 sb (uso + 16) (uso + 24)
                 (Vptr sp_b new_sp_ofs) env_v Hstore_sp Henv_load).
        right. lia.
      - right. lia. }

    (* extra_args field: uso + 32 *)
    assert (Hextra_load3 : Mem.load Mint64 m3 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 32)
               (Vlong (Int64.repr 0)) _ Hstore_atom).
      - apply Hload_sb_m2.
        apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
                 (Vptr sp_b new_sp_ofs) _ Hstore_sp Hextra_load).
        right. lia.
      - right. lia. }

    (* global_data field: uso + 40 *)
    assert (Hgd_load3 : Mem.load Mint64 m3 sb (uso + 40) = Some gd_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 40)
               (Vlong (Int64.repr 0)) gd_ptr Hstore_atom).
      - apply Hload_sb_m2.
        apply (load_after_store_other m m1 sb (uso + 16) (uso + 40)
                 (Vptr sp_b new_sp_ofs) gd_ptr Hstore_sp Hgd_load).
        right. lia.
      - right. lia. }

    (* trap_sp field: uso + 48 *)
    assert (Hts_load3 : Mem.load Mint64 m3 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 48)
               (Vlong (Int64.repr 0)) ts_ptr Hstore_atom).
      - apply Hload_sb_m2.
        apply (load_after_store_other m m1 sb (uso + 16) (uso + 48)
                 (Vptr sp_b new_sp_ofs) ts_ptr Hstore_sp Hts_load).
        right. lia.
      - right. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le' *)
    { subst le'.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      exact Hle_s. }

    (* 2. pc field -- unchanged by handler *)
    { exists pc_ptr. split.
      - exact Hpc_load3.
      - simpl. exact Hpc_rel. }

    (* 3. accu field -- updated to Val_block 0 [] via vr_block_atom *)
    { exists (Vlong (Int64.repr 0)). split.
      - exact Haccu_load3.
      - simpl. exact (vr_block_atom _ _ _ 0). }

    (* 4. sp field -- updated to new_sp_ofs; stack gets accu prepended *)
    { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load3.
      - reflexivity.
      - simpl.
        assert (Hstack_m1 : stack_repr hm cb co m1 (Machine.stack s) sp_b sp_ofs).
        { apply (stack_repr_store_other_block hm cb co m m1 _ sp_b sp_ofs sb
                   (uso + 16) (Vptr sp_b new_sp_ofs)
                   Hstack_repr Hstore_sp).
          intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
        assert (Hstack_cons_m2 : stack_repr hm cb co m2 (Machine.accu s :: Machine.stack s) sp_b new_sp_ofs).
        { exact (stack_repr_cons_after_store hm cb co m1 m2
                   (Machine.stack s) sp_b sp_ofs (Machine.accu s) accu_v
                   Hstack_m1 Haccu_repr Hstore_accu Hsp_ge8 Hsp_rep). }
        apply (stack_repr_store_other_block hm cb co m2 m3 _ sp_b new_sp_ofs sb
                 (uso + 8) (Vlong (Int64.repr 0))
                 Hstack_cons_m2 Hstore_atom).
                intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
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
        eapply Mem.perm_store_1. exact Hstore_atom.
        eapply Mem.perm_store_1. exact Hstore_accu.
        eapply Mem.perm_store_1. exact Hstore_sp.
        apply Hsp_writable. exact Hofs'.
      - (* sp_aligned *)
        exact Halign_new. }

    (* 5. env field -- unchanged *)
    { exists env_v. split.
      - exact Henv_load3.
      - simpl. exact Henv_repr. }

    (* 6. extra_args field -- unchanged *)
    { simpl. exact Hextra_load3. }

    (* 7. global_data field -- unchanged *)
    { exists gd_ptr. split; [| split; [| split]].
      - exact Hgd_load3.
      - simpl. exact Hgd_eq.
      - simpl.
        apply (global_repr_store_other_block hm cb co m2 m3 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (uso + 8) (Vlong (Int64.repr 0))).
        + apply (global_repr_store_other_block hm cb co m1 m2 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sp_b (Ptrofs.unsigned new_sp_ofs) accu_v).
          * apply (global_repr_store_other_block hm cb co m m1 _
                     (ar_global_block ard) (ar_global_ofs ard)
                     sb (uso + 16) (Vptr sp_b new_sp_ofs)
                     Hglobal_repr Hstore_sp).
            intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          * exact Hstore_accu.
          * exact Hsp_ne_gb.
        + exact Hstore_atom.
        + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load3.
      - simpl. exact Htrap_rel. }

    (* 9. sb_writable *)
    { intros ofs' Hofs'.
      eapply Mem.perm_store_1. exact Hstore_atom.
      eapply Mem.perm_store_1. exact Hstore_accu.
      eapply Mem.perm_store_1. exact Hstore_sp.
      apply Hsb_writable. exact Hofs'. }
  }
Qed.
