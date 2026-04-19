(* SETFIELD3_correct.v -- SETFIELD3 correctness proof.

   SETFIELD3: pop stack top, write it to heap field 3 of accu,
   set accu = val_unit.

   C handler: *(cast(accu) + 3) = sp[0], i.e., offset +24 bytes.

   NO AXIOMS. NO ADMITTED. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
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
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

Local Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma sem_add_ptr_long_3 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint (Int.repr 3)) tint m
    = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 24))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* Heap-store precondition for field 3: now uses generic setfield_heap_pre 3. *)

Theorem verify_SETFIELD3_correct :
    handler_correct (handle_SETFIELD 3) f_instr_SETFIELD3
      (setfield_heap_pre 3)
      (fun _ s => match s.(Machine.stack) with
                  | _ :: _ =>
                    match s.(Machine.accu) with
                    | Val_ptr addr =>
                      match heap_lookup s.(Machine.hp) addr with
                      | Some (_, fields) => set_nth fields 3 (hd (Val_int 0) s.(Machine.stack)) = None
                      | None => True
                      end
                    | _ => True
                    end
                  | _ => True end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handler_correct, handle_SETFIELD.

  destruct (Machine.stack s) as [|newval rest] eqn:Hstk. { reflexivity. }
  destruct (Machine.accu s) as [z_val|blk_tag blk_flds|addr|clo_addr clo_ofs] eqn:Haccu_eq; try exact I.
  destruct (heap_lookup (Machine.hp s) addr) as [[tag fields]|] eqn:Hlookup. 2: { exact I. }
  destruct (set_nth fields 3 newval) as [new_fields|] eqn:Hset. 2: { simpl. exact Hset. }

  {
    intros ard Hpre Hhpre. unfold abs_rel_with_ard in Hpre.
    set (sb := ar_sptr_block ard) in *. set (so := ar_sptr_ofs ard) in *. set (hm := ar_heap_map ard) in *.
    set (cb := ar_code_base_block ard) in *.
    set (co := ar_code_base_ofs ard) in *.

    destruct Hpre as (Hle_s & [pc_ptr [Hpc_load Hpc_rel]] & [accu_v [Haccu_load Haccu_repr]] &
      [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
      [env_v [Henv_load Henv_repr]] & Hextra_load &
      [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] & [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
    subst sp_ptr.

    pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    rewrite Hstk in Hstack_repr.
    inversion Hstack_repr as [| ? ? ? ? stk_top_cv Hload_sp0 Hval_repr_top Hstack_repr_rest].
    revert Hgd_load Hgd_eq Hglobal_repr. subst. intros Hgd_load Hgd_eq Hglobal_repr.

    assert (Hsp_mod_orig : Ptrofs.unsigned sp_ofs + 8 < Ptrofs.modulus).
    { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }
    assert (Hsp_rep_tail : Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length rest) < Ptrofs.modulus).
    { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }
    assert (Hsp_writable_tail : Mem.range_perm m sp_b 0 (Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length rest)) Cur Writable).
    { intros ofs' Hofs'. apply Hsp_writable. rewrite Hstk. simpl length. pose proof (Nat2Z.is_nonneg (length rest)). lia. }

    unfold setfield_heap_pre in Hhpre.
    specialize (Hhpre newval rest Hstk accu_v Haccu_repr sp_b sp_ofs Hsp_load stk_top_cv Hval_repr_top).
    destruct Hhpre as [hb [hofs [Haccu_is_ptr [Hhb_ne_sb [Hhb_ne_sp [Hhb_ne_gb Hheap_store_ok]]]]]]. subst accu_v.

    set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
    destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) new_sp_v) as [m1 Hstore1].

    assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vptr hb hofs)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8) new_sp_v (Vptr hb hofs) Hstore1 Haccu_load). left. lia. }
    assert (Hload_sp0_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) = Some stk_top_cv).
    { erewrite Mem.load_store_other. exact Hload_sp0. exact Hstore1. left. exact Hsp_ne_sb. }

    destruct (Hheap_store_ok m1 Hstore1) as [m2 Hstore2].
    change (Z.of_nat 3 * 8) with 24 in Hstore2.

    set (unit_v := Vlong (Int64.repr 1)).
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.
    assert (Hsb_writable_m2 : Mem.range_perm m2 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. apply Hsb_writable_m1. exact Hofs'. }
    assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some (Vptr hb hofs)).
    { erewrite Mem.load_store_other. exact Haccu_load_m1. exact Hstore2. left. intro Heq. exact (Hhb_ne_sb (eq_sym Heq)). }
    destruct (store_succeeds_sb m2 sb so 8 (Vptr hb hofs) Hsb_writable_m2 Haccu_load_m2 ltac:(lia) ltac:(lia) unit_v) as [m3 Hstore3].

    set (le' := PTree.set _t'3 stk_top_cv (PTree.set _t'2 (Vptr hb hofs) (PTree.set _t'1 (Vptr sp_b sp_ofs) le))).
    exists le'. exists m3. exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.
    {
      apply (eval_stmt_to_exec clight_ge 15). eval_cbn.
      rewrite Hle_s; eval_cbn. rewrite Hco; eval_cbn. rewrite Hsp_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn. rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)). rewrite Hsp_load; eval_cbn.

      rewrite PTree.gso by (compute; congruence). rewrite Hle_s; eval_cbn. rewrite Mptr_Mint64; eval_cbn.
      rewrite PTree.gss; eval_cbn. rewrite sem_add_sp_1; eval_cbn. rewrite sem_cast_ptr_to_ptr; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)). unfold new_sp_v in Hstore1. rewrite Hstore1; eval_cbn.

      rewrite PTree.gso by (compute; congruence). rewrite Hle_s; eval_cbn. rewrite Haccu_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)). rewrite Haccu_load_m1; eval_cbn.

      rewrite PTree.gso by (compute; congruence). rewrite PTree.gss; eval_cbn. rewrite Hload_sp0_m1; eval_cbn.

      (* *(cast(_t'2) + 3) = _t'3 -- field 3, offset +24 *)
      rewrite PTree.gso by (compute; congruence). rewrite PTree.gss; eval_cbn.
      rewrite sem_cast_long_to_ptr_vptr; eval_cbn.
      rewrite (sem_add_ptr_long_3 hb hofs m1); eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hval_repr_top); eval_cbn.
      rewrite Hstore2; eval_cbn.

      rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence). rewrite Hle_s; eval_cbn.
      rewrite (sem_cast_int_to_long_0 m2); eval_cbn. rewrite (sem_shl_long_0_1 m2); eval_cbn.
      rewrite (sem_add_long_int_0_1 m2); eval_cbn. rewrite (sem_cast_long_vlong (Int64.repr 1)); eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)). fold unit_v. rewrite Hstore3; eval_cbn.
      subst le'. reflexivity.
    }
    {
      exists ard. set (uso := Ptrofs.unsigned so) in *.
      assert (Hload_m2_sb : forall ofs0 v0, Mem.load Mint64 m1 sb ofs0 = Some v0 -> Mem.load Mint64 m2 sb ofs0 = Some v0).
      { intros ofs0 v0 Hld. erewrite Mem.load_store_other; [exact Hld | exact Hstore2 |]. left. intro Heq. exact (Hhb_ne_sb (eq_sym Heq)). }

      assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 0) new_sp_v pc_ptr Hstore1 Hpc_load). left. lia. }
      assert (Hpc_load3 : Mem.load Mint64 m3 sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 0) unit_v pc_ptr Hstore3). apply Hload_m2_sb. exact Hpc_load_m1. left. lia. }
      assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some new_sp_v).
      { pose proof (load_after_store_same m m1 sb (uso + 16) new_sp_v Hstore1) as Htmp. unfold new_sp_v in Htmp |- *. simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
      assert (Hsp_load3 : Mem.load Mint64 m3 sb (uso + 16) = Some new_sp_v).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 16) unit_v new_sp_v Hstore3). apply Hload_m2_sb. exact Hsp_load_m1. right. lia. }
      assert (Haccu_load3 : Mem.load Mint64 m3 sb (uso + 8) = Some unit_v).
      { pose proof (load_after_store_same m2 m3 sb (uso + 8) unit_v Hstore3) as Htmp. subst unit_v. rewrite load_result_vlong in Htmp. exact Htmp. }
      assert (Henv_load_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 24) new_sp_v env_v Hstore1 Henv_load). right. lia. }
      assert (Henv_load3 : Mem.load Mint64 m3 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 24) unit_v env_v Hstore3). apply Hload_m2_sb. exact Henv_load_m1. right. lia. }
      assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 32) new_sp_v _ Hstore1 Hextra_load). right. lia. }
      assert (Hextra_load3 : Mem.load Mint64 m3 sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 32) unit_v _ Hstore3). apply Hload_m2_sb. exact Hextra_load_m1. right. lia. }
      assert (Hgd_load_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 40) new_sp_v gd_ptr Hstore1 Hgd_load). right. lia. }
      assert (Hgd_load3 : Mem.load Mint64 m3 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 40) unit_v gd_ptr Hstore3). apply Hload_m2_sb. exact Hgd_load_m1. right. lia. }
      assert (Hts_load_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 48) new_sp_v ts_ptr Hstore1 Hts_load). right. lia. }
      assert (Hts_load3 : Mem.load Mint64 m3 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 48) unit_v ts_ptr Hstore3). apply Hload_m2_sb. exact Hts_load_m1. right. lia. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
      { subst le'. rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence). exact Hle_s. }
      { exists pc_ptr. split. exact Hpc_load3. simpl. exact Hpc_rel. }
      { exists unit_v. split. exact Haccu_load3. simpl. subst unit_v. exact (vr_int _ _ _ 0). }
      { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)).
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load3. - reflexivity.
        - simpl.
          eapply (stack_repr_store_other_block hm cb co m2 m3 _ sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) unit_v).
          + eapply (stack_repr_store_other_block hm cb co m1 m2 _ sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) hb (Ptrofs.unsigned (Ptrofs.add hofs (Ptrofs.repr 24))) stk_top_cv).
            * eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16) new_sp_v).
              -- exact Hstack_repr_rest. -- exact Hstore1. -- intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
            * exact Hstore2. * intro Heq. exact (Hhb_ne_sp Heq).
          + exact Hstore3. + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb. - exact Hsp_ne_gb. - exact Hcb_ne_sp.
        - rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)). lia.
        - rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)). exact Hsp_rep_tail.
        - intros ofs' Hofs'. rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)) in Hofs'.
          eapply Mem.perm_store_1. exact Hstore3. eapply Mem.perm_store_1. exact Hstore2.
          eapply Mem.perm_store_1. exact Hstore1. apply Hsp_writable_tail. exact Hofs'.
        - simpl. rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)).
          apply Z.divide_add_r. exact Hsp_align. exists 1. lia. }
      { exists env_v. split. exact Henv_load3. simpl. exact Henv_repr. }
      { simpl. exact Hextra_load3. }
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load3. - simpl. exact Hgd_eq.
        - simpl.
          apply (global_repr_store_other_block hm cb co m2 m3 _ (ar_global_block ard) (ar_global_ofs ard) sb (uso + 8) unit_v).
          + apply (global_repr_store_other_block hm cb co m1 m2 _ (ar_global_block ard) (ar_global_ofs ard) hb (Ptrofs.unsigned (Ptrofs.add hofs (Ptrofs.repr 24))) stk_top_cv).
            * apply (global_repr_store_other_block hm cb co m m1 _ (ar_global_block ard) (ar_global_ofs ard) sb (uso + 16) new_sp_v Hglobal_repr Hstore1).
              intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
            * exact Hstore2. * intro Heq2. exact (Hhb_ne_gb Heq2).
          + exact Hstore3. + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        - exact Hgb_ne_sb. }
      { exists ts_ptr. split. exact Hts_load3. simpl. exact Htrap_rel. }
      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore3. eapply Mem.perm_store_1. exact Hstore2.
        eapply Mem.perm_store_1. exact Hstore1. apply Hsb_writable. exact Hofs'. }
    }
  }
Qed.
