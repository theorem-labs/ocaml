(* PUSH_bigstep_compl_computational.v -- PUSH completeness proof *)

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
      (fun _ _ _ _ => True)
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handler_correct, handle_PUSH. intros ard Hpre _. unfold abs_rel_with_ard in Hpre.
  set (sb := ar_sptr_block ard) in *.
  set (so := ar_sptr_ofs ard) in *.
  set (hm := ar_heap_map ard) in *.
  destruct Hpre as (Hle_s &
    [pc_ptr [Hpc_load Hpc_rel]] &
    [accu_v [Haccu_load Haccu_repr]] &
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb Hcb_ne_sp]]]]]]]] &
    [env_v [Henv_load Henv_repr]] &
    Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
    [ts_ptr [Hts_load Htrap_rel]]).
  subst sp_ptr.
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep. fold sb in Hblock_sep.
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  pose proof (sp_block_ne_global ard sp_b) as Hsp_ne_gb_legacy.
  pose proof (sp_ofs_ge_8 hm m (Machine.stack s) sp_b sp_ofs Hstack_repr) as Hsp_ge8.
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
  set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
  assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 8).
  { subst new_sp_ofs. unfold Ptrofs.sub.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
    apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range sp_ofs).
    unfold Ptrofs.max_unsigned. lia. }
  destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 16)
              (Vptr sp_b sp_ofs) (Vptr sp_b new_sp_ofs) Hsp_load) as [m1 Hstore_sp].
  destruct (store_to_other_block m m1 sb (Ptrofs.unsigned so + 16)
              (Vptr sp_b new_sp_ofs) sp_b (Ptrofs.unsigned new_sp_ofs) accu_v
              Hstore_sp (not_eq_sym Hblock_sep)
              ltac:(rewrite Hnew_sp_unsigned; lia)) as [m2 Hstore_accu].
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
    rewrite (sem_cast_long_val_repr _ _ _ _ Haccu_repr); eval_cbn.
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
      left. exact (not_eq_sym Hblock_sep). }

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

    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].

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
      split; [| split; [| split; [| split; [| split]]]].
      - exact Hsp_load2.
      - reflexivity.
      - simpl.
        (* First establish stack_repr in m1 (after sp store, before accu store) *)
        assert (Hstack_m1 : stack_repr hm m1 (Machine.stack s) sp_b sp_ofs).
        { apply (stack_repr_store_other_block hm m m1 _ sp_b sp_ofs sb
                   (uso + 16) (Vptr sp_b new_sp_ofs)
                   Hstack_repr Hstore_sp).
          intro Heq; exact (Hblock_sep (eq_sym Heq)). }
        (* Now apply stack_repr_cons_after_store *)
        exact (stack_repr_cons_after_store hm m1 m2
                 (Machine.stack s) sp_b sp_ofs (Machine.accu s) accu_v
                                  Hstack_m1 Haccu_repr Hstore_accu Hsp_ge8).
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp. }

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
        apply (global_repr_store_other_block hm m1 m2 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sp_b (Ptrofs.unsigned new_sp_ofs) accu_v).
        + apply (global_repr_store_other_block hm m m1 _
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
  }
Qed.
