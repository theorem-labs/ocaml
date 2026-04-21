(* PUSH_bigstep_compl_computational.v -- PUSH completeness proof *)

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

Theorem verify_PUSH_correct :
    handler_correct handle_PUSH f_instr_PUSH
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
  intros e le m s. unfold handler_correct, handle_PUSH. intros ard Hpre Hstep_pre. unfold abs_rel_with_ard in Hpre.
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
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
  set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
  assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 8).
  { subst new_sp_ofs. unfold Ptrofs.sub.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
    apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range sp_ofs).
    unfold Ptrofs.max_unsigned. lia. }
  destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) (Vptr sp_b new_sp_ofs)) as [m1 Hstore_sp].
  assert (Halign_new : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs)).
  { rewrite Hnew_sp_unsigned. simpl.
    apply Z.divide_sub_r; [exact Hsp_align | exists 1; lia]. }
  destruct (store_to_sp_after_sb_store m m1 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)
              sp_b (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s)))
              (Ptrofs.unsigned new_sp_ofs)
              Hstore_sp Hsp_writable
              ltac:(rewrite Hnew_sp_unsigned; lia)
              ltac:(rewrite Hnew_sp_unsigned; lia)
              Halign_new
              accu_v) as [m2 Hstore_accu].
  set (le' := PTree.set _t'2 accu_v
              (PTree.set _t'1 (Vptr sp_b new_sp_ofs)
              (PTree.set _t'3 (Vptr sp_b sp_ofs) le))).
  exists le'. exists m2.
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
    (* eval_cbn resolves composite lookup (co_is already bound) but
       stops at field_offset (protected). Unlike Statement 1, no
       rewrite Hco needed. *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    (* access_mode tlong = By_value Mint64 (no Mptr), so eval_cbn
       reduces to Mem.load Mint64 m1 sb (Ptrofs.unsigned (Ptrofs.add so (Ptrofs.repr 8))) *)
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

    (* Statement 6: Sreturn 0 *)
    subst le'. reflexivity.
  }

  (* ============================================================== *)
  (* Part 2: abs_rel for post-state                                  *)
  (* ============================================================== *)
  {
    exists ard.
    set (uso := Ptrofs.unsigned so) in *.

    (* Preservation of loads through two stores: m -> m1 -> m2.
       Store 1: Mem.store Mint64 m sb (uso + 16) (Vptr sp_b new_sp_ofs) = Some m1
       Store 2: Mem.store Mint64 m1 sp_b (Ptrofs.unsigned new_sp_ofs) accu_v = Some m2
       Store 2 is on sp_b which is different from sb, so for fields in sb,
       store 2 just preserves the load from m1. *)

    (* Helper: loads on sb survive store 2 (different block) *)
    assert (Hload_m2 : forall ofs v,
      Mem.load Mint64 m1 sb ofs = Some v ->
      Mem.load Mint64 m2 sb ofs = Some v).
    { intros ofs v Hload1.
      erewrite Mem.load_store_other; [exact Hload1 | exact Hstore_accu |].
      left. exact (not_eq_sym Hsp_ne_sb). }

    (* pc field: uso + 0, unaffected by store 1 (ofs 16), unaffected by store 2 *)
    assert (Hpc_load2 : Mem.load Mint64 m2 sb (uso + 0) = Some pc_ptr).
    { apply Hload_m2.
      apply (load_after_store_other m m1 sb (uso + 16) (uso + 0)
               (Vptr sp_b new_sp_ofs) pc_ptr Hstore_sp Hpc_load).
      left. lia. }

    (* accu field: uso + 8, unaffected by store 1 (ofs 16), unaffected by store 2 *)
    assert (Haccu_load2 : Mem.load Mint64 m2 sb (uso + 8) = Some accu_v).
    { apply Hload_m2.
      apply (load_after_store_other m m1 sb (uso + 16) (uso + 8)
               (Vptr sp_b new_sp_ofs) accu_v Hstore_sp Haccu_load).
      left. lia. }

    (* sp field: uso + 16, overwritten by store 1, unaffected by store 2 *)
    assert (Hsp_load2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { apply Hload_m2.
      pose proof (load_after_store_same m m1 sb (uso + 16)
                    (Vptr sp_b new_sp_ofs) Hstore_sp) as Htmp.
      simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }

    (* env field: uso + 24, unaffected by store 1 (ofs 16), unaffected by store 2 *)
    assert (Henv_load2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
    { apply Hload_m2.
      apply (load_after_store_other m m1 sb (uso + 16) (uso + 24)
               (Vptr sp_b new_sp_ofs) env_v Hstore_sp Henv_load).
      right. lia. }

    (* extra_args field: uso + 32 *)
    assert (Hextra_load2 : Mem.load Mint64 m2 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply Hload_m2.
      apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
               (Vptr sp_b new_sp_ofs) _ Hstore_sp Hextra_load).
      right. lia. }

    (* global_data field: uso + 40 *)
    assert (Hgd_load2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
    { apply Hload_m2.
      apply (load_after_store_other m m1 sb (uso + 16) (uso + 40)
               (Vptr sp_b new_sp_ofs) gd_ptr Hstore_sp Hgd_load).
      right. lia. }

    (* trap_sp field: uso + 48 *)
    assert (Hts_load2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
    { apply Hload_m2.
      apply (load_after_store_other m m1 sb (uso + 16) (uso + 48)
               (Vptr sp_b new_sp_ofs) ts_ptr Hstore_sp Hts_load).
      right. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le' *)
    { subst le'.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      exact Hle_s. }

    (* 2. pc field -- unchanged by handler *)
    { exists pc_ptr. split.
      - exact Hpc_load2.
      - simpl. exact Hpc_rel. }

    (* 3. accu field -- unchanged (PUSH does not modify accu) *)
    { exists accu_v. split.
      - exact Haccu_load2.
      - simpl. exact Haccu_repr. }

    (* 4. sp field -- updated to new_sp_ofs; stack gets accu prepended *)
    { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load2.
      - reflexivity.
      - simpl.
        (* First establish stack_repr in m1 (after sp store, before accu store) *)
        assert (Hstack_m1 : stack_repr hm cb co m1 (Machine.stack s) sp_b sp_ofs).
        { apply (stack_repr_store_other_block hm cb co m m1 _ sp_b sp_ofs sb
                   (uso + 16) (Vptr sp_b new_sp_ofs)
                   Hstack_repr Hstore_sp).
          intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
        (* Now apply stack_repr_cons_after_store *)
        exact (stack_repr_cons_after_store hm cb co m1 m2
                 (Machine.stack s) sp_b sp_ofs (Machine.accu s) accu_v
                                  Hstack_m1 Haccu_repr Hstore_accu Hsp_ge8 Hsp_rep).
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - (* sp_ofs_ge8: Ptrofs.unsigned new_sp_ofs >= 8, from Hsp_ge16. *)
        rewrite Hnew_sp_unsigned. lia.
      - (* sp_rep: Ptrofs.unsigned new_sp_ofs + 8 * length (accu :: stack) < modulus.
           new_sp_ofs = sp_ofs - 8, length (accu :: stack) = 1 + length stack,
           so this equals sp_ofs + 8 * length stack, same as Hsp_rep. *)
        simpl length. rewrite Nat2Z.inj_succ. rewrite Hnew_sp_unsigned. lia.
      - (* sp_writable: range_perm on [0, new_sp_ofs + 8 * length (accu :: stack)) *)
        simpl length. rewrite Nat2Z.inj_succ. rewrite Hnew_sp_unsigned.
        replace (Ptrofs.unsigned sp_ofs - 8 + 8 * Z.succ (Z.of_nat (length (Machine.stack s))))
          with (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) by lia.
        intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore_accu.
        eapply Mem.perm_store_1. exact Hstore_sp.
        apply Hsp_writable. exact Hofs'.
      - (* sp_aligned: new_sp_ofs is 8-aligned *)
        rewrite Hnew_sp_unsigned. simpl.
        apply Z.divide_sub_r; [exact Hsp_align | exists 1; lia]. }

    (* 5. env field -- unchanged *)
    { exists env_v. split.
      - exact Henv_load2.
      - simpl. exact Henv_repr. }

    (* 6. extra_args field -- unchanged *)
    { simpl. exact Hextra_load2. }

    (* 7. global_data field -- unchanged *)
    { exists gd_ptr. split; [| split; [| split]].
      - exact Hgd_load2.
      - simpl. exact Hgd_eq.
      - simpl.
        (* global_repr must survive both stores. Store 1 is on sb, store 2 on sp_b.
           gb is different from both. *)
        apply (global_repr_store_other_block hm cb co m1 m2 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sp_b (Ptrofs.unsigned new_sp_ofs) accu_v).
        + apply (global_repr_store_other_block hm cb co m m1 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sb (uso + 16) (Vptr sp_b new_sp_ofs)
                   Hglobal_repr Hstore_sp).
          intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        + exact Hstore_accu.
        + exact Hsp_ne_gb.
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load2.
      - simpl. exact Htrap_rel. }

    (* 9. sb_writable -- permission preserved through both stores *)
    { intros ofs' Hofs'.
      eapply Mem.perm_store_1. exact Hstore_accu.
      eapply Mem.perm_store_1. exact Hstore_sp.
      apply Hsb_writable. exact Hofs'. }
  }
Qed.

(* Wrapper with the exact type expected by InstructVerificationProof.v.
   handle_instr PUSH = handle_PUSH and clight_of PUSH = f_instr_PUSH
   by computation.  pre_of PUSH = sp_at_least 16 which is convertible
   with the lambda above.  Since handle_PUSH always returns Step, the
   P_error/P_halt/P_ccall predicates are dead code in the match. *)
Definition correct_PUSH :
  handler_correct (Dispatch.handle_instr PUSH) (clight_of PUSH)
    (pre_of PUSH)
    (P_error_of PUSH) (P_halt_of PUSH) (P_ccall_of PUSH).
Proof.
  exact verify_PUSH_correct.
Qed.
