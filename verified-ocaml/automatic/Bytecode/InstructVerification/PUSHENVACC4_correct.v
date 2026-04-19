(* PUSHENVACC4_correct.v -- PUSHENVACC4 = PUSH then ENVACC2.

   C handler (f_instr_PUSHENVACC4):
     t5 = s->sp; t1 = (long ptr)(t5 - 1); s->sp = t1;
     t4 = s->accu; *t1 = t4;
     t2 = s->env; t3 = *((long ptr)t2 + 2); s->accu = t3; return 0;

   Rocq (handle_PUSHENVACC 4):
     let new_stack := accu :: stack in
     match field_or_heap s s.(env) 4 with
     | Some v => Step (s <|pc:=pc'|> <|accu:=v|> <|stack:=new_stack|>)
     | None => Error "PUSHENVACC: env access out of bounds"
     end

   No Axioms, no Admitted. *)

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

Lemma sem_cast_long_to_ptr_vptr_PEA4 : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_add_ptr_long_PEA4 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint (Int.repr 4)) tint m
    = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 32))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* Step precondition for PUSHENVACC4: now uses generic pushenvacc_step_pre 4. *)

Theorem verify_PUSHENVACC4_correct :
    handler_correct (handle_PUSHENVACC 4) f_instr_PUSHENVACC4
      (pushenvacc_step_pre 4)
      (fun _ s => field_or_heap s s.(Machine.env) 4 = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_PUSHENVACC.

  destruct (field_or_heap s s.(Machine.env) 4) as [v|] eqn:Hfoh.

  2: { reflexivity. }
  {
    intros ard Hpre Hstep_pre.
    destruct Hpre as (Hle_s &
      [pc_ptr [Hpc_load Hpc_rel]] &
      [accu_v [Haccu_load Haccu_repr]] &
      [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
      [env_v [Henv_load Henv_repr]] &
      Hextra_load &
      [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
      [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
    subst sp_ptr.

    set (sb := ar_sptr_block ard) in *.
    set (so := ar_sptr_ofs ard) in *.
    set (hm := ar_heap_map ard) in *.
    set (cb := ar_code_base_block ard) in *.
    set (co := ar_code_base_ofs ard) in *.

    unfold pushenvacc_step_pre in Hstep_pre. fold sb so hm in Hstep_pre.
    destruct Hstep_pre as [sp_b' [sp_ofs' [Hsp_load' [Hsp_ge16 Hefl]]]].
    assert (sp_b' = sp_b /\ sp_ofs' = sp_ofs) as [-> ->]
      by (rewrite Hsp_load in Hsp_load'; injection Hsp_load'; auto).

    pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.

    destruct (Hefl v Hfoh env_v Henv_repr)
      as [env_b [env_ofs [cv [Henv_is_ptr [Hfield_load [Hfield_repr [Henv_ne_sb Henv_ne_spb]]]]]]].
    subst env_v.

    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
    destruct interp_state_co_env as [co_is2 [Hco2 [Henv_offset Haccu_offset2]]].
    assert (co_is = co_is2) as Hco_eq by (rewrite Hco in Hco2; injection Hco2; auto).
    subst co_is2.

    set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
    assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 8).
    { subst new_sp_ofs. unfold Ptrofs.sub.
      change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
      apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range sp_ofs).
      unfold Ptrofs.max_unsigned. lia. }

    destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) (Vptr sp_b new_sp_ofs)) as [m1 Hstore_sp].

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

    assert (Hfield_load_m1 : Mem.load Mint64 m1 env_b (Ptrofs.unsigned (Ptrofs.add env_ofs (Ptrofs.repr 32))) = Some cv).
    { erewrite Mem.load_store_other. exact Hfield_load. exact Hstore_sp.
      left. exact Henv_ne_sb. }
    assert (Hfield_load_m2 : Mem.load Mint64 m2 env_b (Ptrofs.unsigned (Ptrofs.add env_ofs (Ptrofs.repr 32))) = Some cv).
    { erewrite Mem.load_store_other. exact Hfield_load_m1. exact Hstore_accu.
      left. exact Henv_ne_spb. }

    assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
               (Ptrofs.unsigned so + 8) (Vptr sp_b new_sp_ofs) accu_v
               Hstore_sp Haccu_load). left. lia. }
    assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { erewrite Mem.load_store_other. exact Haccu_load_m1. exact Hstore_accu.
      left. exact (not_eq_sym Hsp_ne_sb). }

    assert (Hsb_writable_m2 : Mem.range_perm m2 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore_accu.
      eapply Mem.perm_store_1. exact Hstore_sp. apply Hsb_writable. exact Hofs'. }
    destruct (store_succeeds_sb m2 sb so 8 accu_v Hsb_writable_m2 Haccu_load_m2 ltac:(lia) ltac:(lia) cv)
      as [m3 Hstore_env_field].

    assert (Henv_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some (Vptr env_b env_ofs)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
               (Ptrofs.unsigned so + 24) (Vptr sp_b new_sp_ofs) (Vptr env_b env_ofs)
               Hstore_sp Henv_load). right. lia. }
    assert (Henv_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 24) = Some (Vptr env_b env_ofs)).
    { erewrite Mem.load_store_other. exact Henv_load_m1. exact Hstore_accu.
      left. exact (not_eq_sym Hsp_ne_sb). }

    assert (Hsp_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 16) =
              Some (Vptr sp_b new_sp_ofs)).
    { assert (Hsp_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
                Some (Vptr sp_b new_sp_ofs)).
      { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 16)
                      (Vptr sp_b new_sp_ofs) Hstore_sp) as Htmp.
        simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
      erewrite Mem.load_store_other. exact Hsp_m1. exact Hstore_accu.
      left. exact (not_eq_sym Hsp_ne_sb). }

    set (le' := PTree.set _t'3 cv
                (PTree.set _t'2 (Vptr env_b env_ofs)
                (PTree.set _t'4 accu_v
                (PTree.set _t'1 (Vptr sp_b new_sp_ofs)
                (PTree.set _t'5 (Vptr sp_b sp_ofs) le))))).
    exists le'. exists m3.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    {
      apply (eval_stmt_to_exec clight_ge 15).
      eval_cbn.

      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hsp_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      rewrite Hsp_load; eval_cbn.

      rewrite PTree.gss; eval_cbn.
      rewrite sem_sub_sp_1; eval_cbn.
      rewrite sem_cast_ptr_to_ptr; eval_cbn.

      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite sem_cast_ptr_to_ptr; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      fold new_sp_ofs.
      rewrite Hstore_sp; eval_cbn.

      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Haccu_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Haccu_load_m1.
      eval_cbn.

      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Haccu_repr); eval_cbn.
      fold new_sp_ofs.
      rewrite Hstore_accu; eval_cbn.

      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      try rewrite Hco; eval_cbn.
      try rewrite Henv_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
      rewrite Henv_load_m2; eval_cbn.

      rewrite PTree.gss; eval_cbn.
      rewrite sem_cast_long_to_ptr_vptr_PEA4; eval_cbn.
      rewrite (sem_add_ptr_long_PEA4 env_b env_ofs m2); eval_cbn.
      rewrite Hfield_load_m2; eval_cbn.

      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      try rewrite Haccu_offset; eval_cbn.
      try rewrite PTree.gss; eval_cbn.
      try rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hfield_repr); eval_cbn.
      try rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Hstore_env_field; eval_cbn.

      subst le'. reflexivity.
    }

    {
      exists ard.
      set (uso := Ptrofs.unsigned so) in *.

      assert (Hload_sb_m2 : forall ofs v0,
        Mem.load Mint64 m1 sb ofs = Some v0 ->
        Mem.load Mint64 m2 sb ofs = Some v0).
      { intros ofs v0 Hload1.
        erewrite Mem.load_store_other; [exact Hload1 | exact Hstore_accu |].
        left. exact (not_eq_sym Hsp_ne_sb). }

      assert (Hpc_load3 : Mem.load Mint64 m3 sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 0)
                 cv pc_ptr Hstore_env_field).
        - apply Hload_sb_m2.
          apply (load_after_store_other m m1 sb (uso + 16) (uso + 0)
                   (Vptr sp_b new_sp_ofs) pc_ptr Hstore_sp Hpc_load).
          left. lia.
        - left. lia. }

      assert (Haccu_load3 : Mem.load Mint64 m3 sb (uso + 8) = Some cv).
      { pose proof (load_after_store_same m2 m3 sb (uso + 8) cv Hstore_env_field) as Htmp.
        rewrite (val_repr_load_result hm cb co v cv Hfield_repr) in Htmp.
        exact Htmp. }

      assert (Hsp_load3 : Mem.load Mint64 m3 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 16)
                 cv (Vptr sp_b new_sp_ofs) Hstore_env_field).
        exact Hsp_load_m2. right. lia. }

      assert (Henv_load3 : Mem.load Mint64 m3 sb (uso + 24) = Some (Vptr env_b env_ofs)).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 24)
                 cv (Vptr env_b env_ofs) Hstore_env_field).
        exact Henv_load_m2. right. lia. }

      assert (Hextra_load3 : Mem.load Mint64 m3 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 32)
                 cv _ Hstore_env_field).
        - apply Hload_sb_m2.
          apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
                   (Vptr sp_b new_sp_ofs) _ Hstore_sp Hextra_load).
          right. lia.
        - right. lia. }

      assert (Hgd_load3 : Mem.load Mint64 m3 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 40)
                 cv gd_ptr Hstore_env_field).
        - apply Hload_sb_m2.
          apply (load_after_store_other m m1 sb (uso + 16) (uso + 40)
                   (Vptr sp_b new_sp_ofs) gd_ptr Hstore_sp Hgd_load).
          right. lia.
        - right. lia. }

      assert (Hts_load3 : Mem.load Mint64 m3 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 48)
                 cv ts_ptr Hstore_env_field).
        - apply Hload_sb_m2.
          apply (load_after_store_other m m1 sb (uso + 16) (uso + 48)
                   (Vptr sp_b new_sp_ofs) ts_ptr Hstore_sp Hts_load).
          right. lia.
        - right. lia. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      { exists pc_ptr. split. exact Hpc_load3. simpl. exact Hpc_rel. }
      { exists cv. split. exact Haccu_load3. simpl. exact Hfield_repr. }

      { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load3.
        - reflexivity.
        - simpl.
          assert (Hstack_m1 : stack_repr hm cb co m1 (Machine.stack s) sp_b sp_ofs).
          { apply (stack_repr_store_other_block hm cb co m m1 _ sp_b sp_ofs sb
                     (uso + 16) (Vptr sp_b new_sp_ofs) Hstack_repr Hstore_sp).
            intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
          assert (Hstack_cons_m2 : stack_repr hm cb co m2 (Machine.accu s :: Machine.stack s) sp_b new_sp_ofs).
          { exact (stack_repr_cons_after_store hm cb co m1 m2
                     (Machine.stack s) sp_b sp_ofs (Machine.accu s) accu_v
                     Hstack_m1 Haccu_repr Hstore_accu Hsp_ge8 Hsp_rep). }
          apply (stack_repr_store_other_block hm cb co m2 m3
                   (Machine.accu s :: Machine.stack s) sp_b new_sp_ofs sb
                   (uso + 8) cv Hstack_cons_m2 Hstore_env_field).
          intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - rewrite Hnew_sp_unsigned. lia.
        - simpl length. rewrite Nat2Z.inj_succ. rewrite Hnew_sp_unsigned. lia.
        - simpl length. rewrite Nat2Z.inj_succ. rewrite Hnew_sp_unsigned.
          replace (Ptrofs.unsigned sp_ofs - 8 + 8 * Z.succ (Z.of_nat (length (Machine.stack s))))
            with (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) by lia.
          intros ofs' Hofs'.
          eapply Mem.perm_store_1. exact Hstore_env_field.
          eapply Mem.perm_store_1. exact Hstore_accu.
          eapply Mem.perm_store_1. exact Hstore_sp.
          apply Hsp_writable. exact Hofs'.
        - exact Halign_new. }

      { exists (Vptr env_b env_ofs). split. exact Henv_load3. simpl. exact Henv_repr. }
      { simpl. exact Hextra_load3. }

      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load3.
        - simpl. exact Hgd_eq.
        - simpl.
          apply (global_repr_store_other_block hm cb co m2 m3 _
                   (ar_global_block ard) (ar_global_ofs ard) sb (uso + 8) cv).
          + apply (global_repr_store_other_block hm cb co m1 m2 _
                     (ar_global_block ard) (ar_global_ofs ard)
                     sp_b (Ptrofs.unsigned new_sp_ofs) accu_v).
            * apply (global_repr_store_other_block hm cb co m m1 _
                       (ar_global_block ard) (ar_global_ofs ard)
                       sb (uso + 16) (Vptr sp_b new_sp_ofs) Hglobal_repr Hstore_sp).
              intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
            * exact Hstore_accu.
            * exact Hsp_ne_gb.
          + exact Hstore_env_field.
          + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      { exists ts_ptr. split. exact Hts_load3. simpl. exact Htrap_rel. }

      { intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore_env_field.
        eapply Mem.perm_store_1. exact Hstore_accu.
        eapply Mem.perm_store_1. exact Hstore_sp.
        apply Hsb_writable. exact Hofs'. }
    }
  }
Qed.
