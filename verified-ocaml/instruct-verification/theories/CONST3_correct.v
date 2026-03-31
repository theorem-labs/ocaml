(* CONST3_correct.v -- constant 3: s->accu = ((3 << 1) + 1) = 7. *)
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
Local Lemma sem_cast_int_to_long_3 : forall m, sem_cast (Vint (Int.repr 3)) tint tlong m = Some (Vlong (Int64.repr 3)). Proof. intros. reflexivity. Qed.
Local Lemma sem_shl_long_3_1 : forall m, sem_binary_operation (genv_cenv clight_ge) Oshl (Vlong (Int64.repr 3)) tlong (Vint (Int.repr 1)) tint m = Some (Vlong (Int64.repr 6)). Proof. intros. reflexivity. Qed.
Local Lemma sem_add_long_int_6_1 : forall m, sem_binary_operation (genv_cenv clight_ge) Oadd (Vlong (Int64.repr 6)) tlong (Vint (Int.repr 1)) tint m = Some (Vlong (Int64.repr 7)). Proof. intros. reflexivity. Qed.
Local Lemma val_int_3_load_result : Val.load_result Mint64 (Vlong (Int64.repr 7)) = Vlong (Int64.repr 7). Proof. reflexivity. Qed.
Theorem verify_CONST3_correct :
    handler_correct (handle_CONSTINT 3) f_instr_CONST3 (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handler_correct, handle_CONSTINT. simpl. intro Hpre.
  destruct Hpre as [ard Hpre]. set (sb := ar_sptr_block ard) in *. set (so := ar_sptr_ofs ard) in *. set (hm := ar_heap_map ard) in *.
  destruct Hpre as (Hle_s & [pc_ptr [Hpc_load Hpc_rel]] & [accu_v [Haccu_load Haccu_repr]] & [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq Hstack_repr]]]]] & [env_v [Henv_load Henv_repr]] & Hextra_load & [gd_ptr [Hgd_load [Hgd_eq Hglobal_repr]]] & [ts_ptr [Hts_load Htrap_rel]]). subst sp_ptr.
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound. pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep. fold sb in Hblock_sep. pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
  destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 8) accu_v (Vlong (Int64.repr 7)) Haccu_load) as [m' Hstore].
  exists le. exists m'. exists (Out_return (Some (Vint (Int.repr 0), tint))). split.
  { apply (eval_stmt_to_exec clight_ge 10). eval_cbn. rewrite Hle_s; eval_cbn. rewrite Hco; eval_cbn. rewrite Haccu_offset; eval_cbn.
    rewrite (sem_cast_int_to_long_3 m); eval_cbn. rewrite (sem_shl_long_3_1 m); eval_cbn. rewrite (sem_add_long_int_6_1 m); eval_cbn.
    rewrite (sem_cast_long_vlong (Int64.repr 7)); eval_cbn. rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)). rewrite Hstore; eval_cbn. reflexivity. }
  { exists ard. set (uso := Ptrofs.unsigned so) in *.
    assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr). { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) (Vlong (Int64.repr 7)) pc_ptr Hstore Hpc_load). left. lia. }
    assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)). { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) (Vlong (Int64.repr 7)) (Vptr sp_b sp_ofs) Hstore Hsp_load). right. lia. }
    assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v). { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) (Vlong (Int64.repr 7)) env_v Hstore Henv_load). right. lia. }
    assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))). { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) (Vlong (Int64.repr 7)) _ Hstore Hextra_load). right. lia. }
    assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr). { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) (Vlong (Int64.repr 7)) gd_ptr Hstore Hgd_load). right. lia. }
    assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr). { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) (Vlong (Int64.repr 7)) ts_ptr Hstore Hts_load). right. lia. }
    assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some (Vlong (Int64.repr 7))). { pose proof (load_after_store_same m m' sb (uso + 8) (Vlong (Int64.repr 7)) Hstore) as Htmp. rewrite val_int_3_load_result in Htmp. exact Htmp. }
    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
    { exact Hle_s. }
    { exists pc_ptr. split. exact Hpc_load'. simpl. exact Hpc_rel. }
    { exists (Vlong (Int64.repr 7)). split. exact Haccu_load'. simpl. exact (vr_int _ 3). }
    { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs. split; [| split]. exact Hsp_load'. reflexivity. simpl. apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb (uso + 8) (Vlong (Int64.repr 7)) Hstack_repr Hstore). intro Heq; exact (Hblock_sep (eq_sym Heq)). }
    { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }
    { simpl. exact Hextra_load'. }
    { exists gd_ptr. split; [| split]. exact Hgd_load'. simpl. exact Hgd_eq. simpl. apply (global_repr_store_other_block hm m m' _ _ _ sb (uso + 8) (Vlong (Int64.repr 7)) Hglobal_repr Hstore). intro Heq2; exact (Hgb_ne (eq_sym Heq2)). }
    { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. } }
Qed.
