(* ACC1_correct.v -- clone of ACC2 with stack index 1 *)
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

Theorem verify_ACC1 :
    handler_correct (handle_ACC 1) f_instr_ACC1
      (fun _ _ _ _ => True)
      (fun _ s => nth_error s.(Machine.stack) 1 = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handler_correct, handle_ACC. simpl nth_error.
  destruct (Machine.stack s) as [|v0 stk0] eqn:Hstk.
  { reflexivity. }
  destruct stk0 as [|v1 rest].
  { reflexivity. }
  intros ard Hpre _. unfold abs_rel_with_ard in Hpre.
  set (sb := ar_sptr_block ard) in *. set (so := ar_sptr_ofs ard) in *. set (hm := ar_heap_map ard) in *.
  destruct Hpre as (Hle_s & [pc_ptr [Hpc_load Hpc_rel]] & [accu_v [Haccu_load Haccu_repr]] & [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] & [env_v [Henv_load Henv_repr]] & Hextra_load & [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] & [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable). subst sp_ptr.
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  rewrite Hstk in Hstack_repr.
  inversion Hstack_repr as [| xv0 xvs0 xb0 xofs0 cv0 Hload_sp0 Hval_repr0 Hstack_repr1]. subst xv0 xvs0 xb0 xofs0.
  inversion Hstack_repr1 as [| xv1 xvs1 xb1 xofs1 cv1 Hload_sp1 Hval_repr1 Hstack_repr_rest]. subst xv1 xvs1 xb1 xofs1.
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
  destruct (store_succeeds_sb m sb so 8 accu_v Hsb_writable Haccu_load ltac:(lia) ltac:(lia) cv1) as [m' Hstore].
  set (le' := PTree.set _t'2 cv1 (PTree.set _t'1 (Vptr sp_b sp_ofs) le)).
  exists le'. exists m'. exists (Out_return (Some (Vint (Int.repr 0), tint))). split.
  { apply (eval_stmt_to_exec clight_ge 10). eval_cbn.
    rewrite Hle_s; eval_cbn. rewrite Hco; eval_cbn. rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn. rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn. rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_1; eval_cbn. rewrite Hload_sp1; eval_cbn.
    rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn. rewrite Haccu_offset; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ Hval_repr1); eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)). rewrite Hstore; eval_cbn.
    subst le'. reflexivity. }
  { exists ard. set (uso := Ptrofs.unsigned so) in *.
    assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr). { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) cv1 pc_ptr Hstore Hpc_load). left. lia. }
    assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)). { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) cv1 (Vptr sp_b sp_ofs) Hstore Hsp_load). right. lia. }
    assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v). { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) cv1 env_v Hstore Henv_load). right. lia. }
    assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))). { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) cv1 _ Hstore Hextra_load). right. lia. }
    assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr). { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) cv1 gd_ptr Hstore Hgd_load). right. lia. }
    assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr). { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) cv1 ts_ptr Hstore Hts_load). right. lia. }
    assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some cv1). { pose proof (load_after_store_same m m' sb (uso + 8) cv1 Hstore) as Htmp. rewrite (val_repr_load_result hm v1 cv1 Hval_repr1) in Htmp. exact Htmp. }
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
    { subst le'. rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence). exact Hle_s. }
    { exists pc_ptr. split. exact Hpc_load'. simpl. exact Hpc_rel. }
    { exists cv1. split. exact Haccu_load'. simpl. exact Hval_repr1. }
    { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]. exact Hsp_load'. reflexivity. simpl. rewrite Hstk.
            apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb (uso + 8) cv1 Hstack_repr Hstore). intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsp_writable. exact Hofs'. 
        - exact Hsp_align. }
    { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }
    { simpl. exact Hextra_load'. }
    { exists gd_ptr. split; [| split; [| split]]. exact Hgd_load'. simpl. exact Hgd_eq. simpl. apply (global_repr_store_other_block hm m m' _ _ _ sb (uso + 8) cv1 Hglobal_repr Hstore). intro Heq2; exact (Hgb_ne (eq_sym Heq2)). exact Hgb_ne_sb. }
    { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. }

    (* 9. sb_writable -- permission preserved *)
    { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsb_writable. exact Hofs'. } }
Qed.
