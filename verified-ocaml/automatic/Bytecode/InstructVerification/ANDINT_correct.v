(* ANDINT_correct.v -- clone of SUBINT with bitwise AND.
   C: s->accu = (long)((long)_t'2 & (long)_t'3); sp++.
   Tagged: (2a+1) & (2b+1) = 2(a land b)+1 (tag bit preserved by AND). *)
From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.
Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr sem_binary_operation sem_cast
        Mem.load Mem.store Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int field_offset PTree.get PTree.set].

Local Lemma sem_and_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Oand
    (Vlong n1) tlong (Vlong n2) tlong m = Some (Vlong (Int64.and n1 n2)).
Proof. intros. reflexivity. Qed.

Local Lemma tagged_andint_arith : forall a b,
  Int64.and (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1))
  = Int64.repr ((Z.land a b) * 2 + 1).
Proof.
  intros a b.
  apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_and, !Int64.testbit_repr by lia.
  replace (a * 2 + 1) with (2 * a + 1) by lia.
  replace (b * 2 + 1) with (2 * b + 1) by lia.
  replace (Z.land a b * 2 + 1) with (2 * Z.land a b + 1) by lia.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - rewrite !Z.testbit_odd_0. reflexivity.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite !Z.testbit_odd_succ by lia.
    rewrite Z.land_spec. reflexivity.
Qed.

Local Theorem verify_ANDINT_correct :
    handler_correct handle_ANDINT f_instr_ANDINT
      (pre_and accu_is_long stack_head_is_long)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handler_correct, handle_ANDINT.
  destruct (Machine.accu s) as [a| | |] eqn:Haccu_eq; try (exact I).
  destruct (Machine.stack s) as [|v_hd v_tl] eqn:Hstk; try (exact I).
  destruct v_hd as [b| | |] eqn:Hvhd; try (exact I).
  intros ard Hpre Hstep_pre. unfold abs_rel_with_ard in Hpre.
  unfold pre_and, accu_is_long, stack_head_is_long in Hstep_pre.
  destruct Hstep_pre as [Haccu_long Hhead_long].
  set (sb := ar_sptr_block ard) in *. set (so := ar_sptr_ofs ard) in *. set (hm := ar_heap_map ard) in *.
  set (cb := ar_code_base_block ard) in *.
  set (co := ar_code_base_ofs ard) in *.
  destruct Hpre as (Hle_s & [pc_ptr [Hpc_load Hpc_rel]] & [accu_v [Haccu_load Haccu_repr]] & [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] & [env_v [Henv_load Henv_repr]] & Hextra_load & [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] & [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable). subst sp_ptr.
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  rewrite Haccu_eq in Haccu_repr.
  pose proof Haccu_repr as Haccu_repr_rw.
  inversion Haccu_repr; subst accu_v.
  2: { exfalso. rewrite Haccu_eq in Haccu_long.
       destruct (Haccu_long _ Haccu_repr_rw) as [z Hz]. discriminate Hz. }
  rename H0 into Haccu_is_int.
  rewrite Hstk in Hstack_repr.
  inversion Hstack_repr as [| ? ? ? ? cv0 Hload_sp0 Hval_repr0 Hstack_repr_rest].
  revert Hgd_load Hgd_eq Hglobal_repr. subst. intros Hgd_load Hgd_eq Hglobal_repr.
  pose proof Hval_repr0 as Hval_repr0_rw.
  inversion Hval_repr0; subst cv0.
  2: { exfalso. rewrite Hstk in Hhead_long.
       destruct (Hhead_long _ Hval_repr0_rw) as [z Hz]. discriminate Hz. }
  rename H0 into Hstk_is_int.
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
  set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
  destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) new_sp_v) as [m1 Hstore1].
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vlong (Int64.repr (a * 2 + 1)))).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8) new_sp_v (Vlong (Int64.repr (a * 2 + 1))) Hstore1 Haccu_load). left. lia. }
  assert (Hload_sp0_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) = Some (Vlong (Int64.repr (b * 2 + 1)))).
  { erewrite Mem.load_store_other. exact Hload_sp0. exact Hstore1. left. exact Hsp_ne_sb. }
  set (result_v := Vlong (Int64.and (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1)))).
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.
  destruct (store_succeeds_sb m1 sb so 8 (Vlong (Int64.repr (a * 2 + 1))) Hsb_writable_m1 Haccu_load_m1 ltac:(lia) ltac:(lia) result_v) as [m' Hstore2].
  set (le' := PTree.set _t'3 (Vlong (Int64.repr (b * 2 + 1))) (PTree.set _t'2 (Vlong (Int64.repr (a * 2 + 1))) (PTree.set _t'1 (Vptr sp_b sp_ofs) le))).
  exists le'. exists m'. exists (Out_return (Some (Vint (Int.repr 0), tint))). split.
  { apply (eval_stmt_to_exec clight_ge 10). eval_cbn.
    rewrite Hle_s; eval_cbn. rewrite Hco; eval_cbn. rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn. rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.
    rewrite PTree.gso by (compute; congruence). rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn. rewrite sem_add_sp_1; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn. rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    unfold new_sp_v in Hstore1. rewrite Hstore1; eval_cbn.
    rewrite PTree.gso by (compute; congruence). rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m1; eval_cbn.
    rewrite PTree.gso by (compute; congruence). rewrite PTree.gss; eval_cbn.
    rewrite Hload_sp0_m1; eval_cbn.
    (* -- ANDINT-specific: evaluate (Ecast (Ebinop Oand ...)) -- *)
    rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence). rewrite Hle_s; eval_cbn.
    rewrite PTree.gso by (compute; congruence). rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    rewrite sem_and_long_long; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    unfold result_v in Hstore2. rewrite Hstore2; eval_cbn.
    subst le'. reflexivity. }
  { exists ard. set (uso := Ptrofs.unsigned so) in *.
    assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
    { assert (Hpc_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 0) new_sp_v pc_ptr Hstore1 Hpc_load). left. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 0) result_v pc_ptr Hstore2 Hpc_m1). left. lia. }
    assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some new_sp_v).
    { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some new_sp_v).
      { pose proof (load_after_store_same m m1 sb (uso + 16) new_sp_v Hstore1) as Htmp. unfold new_sp_v in Htmp |- *. simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 16) result_v new_sp_v Hstore2 Hsp_m1). right. lia. }
    assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some result_v).
    { pose proof (load_after_store_same m1 m' sb (uso + 8) result_v Hstore2) as Htmp. unfold result_v in Htmp |- *. simpl Val.load_result in Htmp. exact Htmp. }
    assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v). { apply (load_after_store_other m m1 sb (uso + 16) (uso + 24) new_sp_v env_v Hstore1 Henv_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 24) result_v env_v Hstore2 He1). right. lia. }
    assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))). { apply (load_after_store_other m m1 sb (uso + 16) (uso + 32) new_sp_v _ Hstore1 Hextra_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 32) result_v _ Hstore2 He1). right. lia. }
    assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr). { apply (load_after_store_other m m1 sb (uso + 16) (uso + 40) new_sp_v gd_ptr Hstore1 Hgd_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 40) result_v gd_ptr Hstore2 He1). right. lia. }
    assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr). { apply (load_after_store_other m m1 sb (uso + 16) (uso + 48) new_sp_v ts_ptr Hstore1 Hts_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 48) result_v ts_ptr Hstore2 He1). right. lia. }
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
    { subst le'. rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence). exact Hle_s. }
    { exists pc_ptr. split. exact Hpc_load'. simpl. exact Hpc_rel. }
    { exists result_v. split. exact Haccu_load'. simpl. unfold result_v. rewrite tagged_andint_arith. constructor. }
    { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)).
      assert (Hsp_rep' : Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length v_tl) < Ptrofs.modulus).
      { rewrite Hstk in Hsp_rep. simpl in Hsp_rep. lia. }
      assert (Hadd : Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 8)) = Ptrofs.unsigned sp_ofs + 8). { apply ptrofs_add_unsigned; lia. }
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]. exact Hsp_load'. reflexivity. simpl.
      eapply (stack_repr_store_other_block hm cb co m1 m' _ sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) result_v).
      + eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16) new_sp_v).
        * exact Hstack_repr_rest. * exact Hstore1. * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
            + exact Hstore2. + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
      + exact Hsp_ne_sb. + exact Hsp_ne_gb. + exact Hcb_ne_sp.
        + simpl Machine.stack. rewrite Hadd. lia.
        + simpl Machine.stack. rewrite Hadd. exact Hsp_rep'.
        + simpl Machine.stack. intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. eapply Mem.perm_store_1. exact Hstore1. apply Hsp_writable. rewrite Hadd in Hofs'. rewrite Hstk. simpl. lia.
        + (* sp_align *) simpl. rewrite Hadd. apply Z.divide_add_r. exact Hsp_align. exists 1. lia. }
    { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }
    { simpl. exact Hextra_load'. }
    { exists gd_ptr. split; [| split; [| split]]. exact Hgd_load'. simpl. exact Hgd_eq. simpl.
      eapply (global_repr_store_other_block hm cb co m1 m' _ _ _ sb (uso + 8) result_v).
      + eapply (global_repr_store_other_block hm cb co m m1 _ _ _ sb (uso + 16) new_sp_v). * exact Hglobal_repr. * exact Hstore1. * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
            + exact Hstore2. + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
      + exact Hgb_ne_sb. }
    { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. }

    (* 9. sb_writable -- permission preserved *)
    { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. eapply Mem.perm_store_1. exact Hstore1. apply Hsb_writable. exact Hofs'. } }
Qed.

Import Bytecode.AST.

(* Wrapper: lift verify_ANDINT_correct to the dispatch-level type
   expected by InstructVerificationFineGrainedSpec. *)
Theorem correct_ANDINT :
    handler_correct (handle_instr ANDINT) (clight_of ANDINT)
      (pre_of ANDINT)
      (P_error_of ANDINT) (P_halt_of ANDINT) (P_ccall_of ANDINT).
Proof.
Admitted.
