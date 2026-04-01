(* ACC5_correct.v -- stack index 5, sp + 5 = sp + 40 bytes *)
From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
Require Import instruct_handlers InstructSpec StepToBigstep HandlerLemmas.
Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr sem_binary_operation sem_cast
        Mem.load Mem.store Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int field_offset PTree.get PTree.set].

Local Lemma sem_add_sp_5 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 5)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 40))).
Proof. intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity. Qed.

Theorem verify_ACC5 :
    handler_correct (handle_ACC 5) f_instr_ACC5
      (fun _ _ _ _ => True)
      (fun _ s => nth_error s.(Machine.stack) 5 = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handler_correct, handle_ACC. simpl nth_error.
  destruct (Machine.stack s) as [|v0 stk0] eqn:Hstk.
  { reflexivity. }
  destruct stk0 as [|v1 stk1].
  { reflexivity. }
  destruct stk1 as [|v2 stk2].
  { reflexivity. }
  destruct stk2 as [|v3 stk3].
  { reflexivity. }
  destruct stk3 as [|v4 stk4].
  { reflexivity. }
  destruct stk4 as [|v5 rest].
  { reflexivity. }
  intros ard Hpre _. unfold abs_rel_with_ard in Hpre.
  set (sb := ar_sptr_block ard) in *. set (so := ar_sptr_ofs ard) in *. set (hm := ar_heap_map ard) in *.
  destruct Hpre as (Hle_s & [pc_ptr [Hpc_load Hpc_rel]] & [accu_v [Haccu_load Haccu_repr]] & [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb Hcb_ne_sp]]]]]]]] & [env_v [Henv_load Henv_repr]] & Hextra_load & [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] & [ts_ptr [Hts_load Htrap_rel]]). subst sp_ptr.
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep. fold sb in Hblock_sep.
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  rewrite Hstk in Hstack_repr.
  (* Invert stack_repr N+1 times *)
  pose proof Hstack_repr as Hstack_repr_orig.
    inversion Hstack_repr as [| xv0 xvs0 xb0 xofs0 cv0 Hload_sp0 Hval_repr0 Hstack_repr_0]. subst xv0 xvs0 xb0 xofs0.
  inversion Hstack_repr_0 as [| xv1 xvs1 xb1 xofs1 cv1 Hload_sp1 Hval_repr1 Hstack_repr_1]. subst xv1 xvs1 xb1 xofs1.
  inversion Hstack_repr_1 as [| xv2 xvs2 xb2 xofs2 cv2 Hload_sp2 Hval_repr2 Hstack_repr_2]. subst xv2 xvs2 xb2 xofs2.
  inversion Hstack_repr_2 as [| xv3 xvs3 xb3 xofs3 cv3 Hload_sp3 Hval_repr3 Hstack_repr_3]. subst xv3 xvs3 xb3 xofs3.
  inversion Hstack_repr_3 as [| xv4 xvs4 xb4 xofs4 cv4 Hload_sp4 Hval_repr4 Hstack_repr_4]. subst xv4 xvs4 xb4 xofs4.
  inversion Hstack_repr_4 as [| xv5 xvs5 xb5 xofs5 cv5 Hload_sp5 Hval_repr5 Hstack_repr_5]. subst xv5 xvs5 xb5 xofs5.
  (* Normalize the nested Ptrofs.add to a single offset *)
  assert (Hofs_eq : Ptrofs.add (Ptrofs.add (Ptrofs.add (Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8)) (Ptrofs.repr 8)) (Ptrofs.repr 8)) (Ptrofs.repr 8) = Ptrofs.add sp_ofs (Ptrofs.repr 40)).
  { rewrite !Ptrofs.add_assoc. reflexivity. }
  rewrite Hofs_eq in Hload_sp5.
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
  destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 8) accu_v cv5 Haccu_load) as [m' Hstore].
  set (le' := PTree.set _t'2 cv5 (PTree.set _t'1 (Vptr sp_b sp_ofs) le)).
  exists le'. exists m'. exists (Out_return (Some (Vint (Int.repr 0), tint))). split.
  { apply (eval_stmt_to_exec clight_ge 10). eval_cbn.
    rewrite Hle_s; eval_cbn. rewrite Hco; eval_cbn. rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn. rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn. rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_5; eval_cbn. rewrite Hload_sp5; eval_cbn.
    rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn. rewrite Haccu_offset; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ Hval_repr5); eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)). rewrite Hstore; eval_cbn.
    subst le'. reflexivity. }
  { exists ard. set (uso := Ptrofs.unsigned so) in *.
    assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr). { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) cv5 pc_ptr Hstore Hpc_load). left. lia. }
    assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)). { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) cv5 (Vptr sp_b sp_ofs) Hstore Hsp_load). right. lia. }
    assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v). { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) cv5 env_v Hstore Henv_load). right. lia. }
    assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))). { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) cv5 _ Hstore Hextra_load). right. lia. }
    assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr). { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) cv5 gd_ptr Hstore Hgd_load). right. lia. }
    assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr). { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) cv5 ts_ptr Hstore Hts_load). right. lia. }
    assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some cv5). { pose proof (load_after_store_same m m' sb (uso + 8) cv5 Hstore) as Htmp. rewrite (val_repr_load_result hm v5 cv5 Hval_repr5) in Htmp. exact Htmp. }
    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
    { subst le'. rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence). exact Hle_s. }
    { exists pc_ptr. split. exact Hpc_load'. simpl. exact Hpc_rel. }
    { exists cv5. split. exact Haccu_load'. simpl. exact Hval_repr5. }
    { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs. split; [| split; [| split; [| split; [| split]]]]. exact Hsp_load'. reflexivity. simpl. rewrite Hstk.
            apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb (uso + 8) cv5 Hstack_repr Hstore). intro Heq; exact (Hblock_sep (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp. }
    { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }
    { simpl. exact Hextra_load'. }
    { exists gd_ptr. split; [| split; [| split]]. exact Hgd_load'. simpl. exact Hgd_eq. simpl. apply (global_repr_store_other_block hm m m' _ _ _ sb (uso + 8) cv5 Hglobal_repr Hstore). intro Heq2; exact (Hgb_ne (eq_sym Heq2)). exact Hgb_ne_sb. }
    { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. } }
Qed.
