(* PUSHACC7_correct.v -- PUSHACC7 = PUSH then ACC7.
   The C handler: decrement sp, store accu to *new_sp, load old stack[6]
   (= *(new_sp + 56)) into accu.
   Rocq: handle_PUSHACC 7 pc' s =
     let new_stack := accu :: stack in
     Step {pc := pc'; accu := stack[6]; stack := new_stack}. *)
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
        Mem.load Mem.store Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int field_offset PTree.get PTree.set].

Local Lemma sem_add_sp_7 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 7)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 56))).
Proof. intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity. Qed.

Theorem verify_PUSHACC7_correct :
    handler_correct (handle_PUSHACC 7) f_instr_PUSHACC7
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 7 = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handler_correct, handle_PUSHACC. simpl nth_error.
  (* Need 7 elements in original stack for Step. *)
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
  destruct stk4 as [|v5 stk5].
  { reflexivity. }
  destruct stk5 as [|v6 rest].
  { reflexivity. }
  intro Hpre.
  destruct Hpre as [ard Hpre].
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

  (* Structural facts *)
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep. fold sb in Hblock_sep.
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.

  (* sp_ofs >= 8 (room to push) *)
  pose proof (sp_ofs_ge_8 hm m (Machine.stack s) sp_b sp_ofs Hstack_repr) as Hsp_ge8.

  (* Invert stack_repr 7 times to get load for v6 *)
  rewrite Hstk in Hstack_repr.
  pose proof (sp_ofs_stack_representable hm m _ sp_b sp_ofs Hstack_repr) as Hsp_rep.
  simpl length in Hsp_rep.
  inversion Hstack_repr as [| xv0 xvs0 xb0 xofs0 cv0 Hload_sp0 Hval_repr0 Hstack_repr_0].
  subst xv0 xvs0 xb0 xofs0.
  inversion Hstack_repr_0 as [| xv1 xvs1 xb1 xofs1 cv1 Hload_sp1 Hval_repr1 Hstack_repr_1].
  subst xv1 xvs1 xb1 xofs1.
  inversion Hstack_repr_1 as [| xv2 xvs2 xb2 xofs2 cv2 Hload_sp2 Hval_repr2 Hstack_repr_2].
  subst xv2 xvs2 xb2 xofs2.
  inversion Hstack_repr_2 as [| xv3 xvs3 xb3 xofs3 cv3 Hload_sp3 Hval_repr3 Hstack_repr_3].
  subst xv3 xvs3 xb3 xofs3.
  inversion Hstack_repr_3 as [| xv4 xvs4 xb4 xofs4 cv4 Hload_sp4 Hval_repr4 Hstack_repr_4].
  subst xv4 xvs4 xb4 xofs4.
  inversion Hstack_repr_4 as [| xv5 xvs5 xb5 xofs5 cv5 Hload_sp5 Hval_repr5 Hstack_repr_5].
  subst xv5 xvs5 xb5 xofs5.
  inversion Hstack_repr_5 as [| xv6 xvs6 xb6 xofs6 cv6 Hload_sp6 Hval_repr6 Hstack_repr_6].
  subst xv6 xvs6 xb6 xofs6.

  (* Normalize nested Ptrofs.add: sp + 8*6 = sp + 48 *)
  assert (Hofs_eq : Ptrofs.add (Ptrofs.add (Ptrofs.add (Ptrofs.add (Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8)) (Ptrofs.repr 8)) (Ptrofs.repr 8)) (Ptrofs.repr 8)) (Ptrofs.repr 8) = Ptrofs.add sp_ofs (Ptrofs.repr 48)).
  { rewrite !Ptrofs.add_assoc. reflexivity. }
  rewrite Hofs_eq in Hload_sp6.

  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

  (* Compute new_sp *)
  set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
  assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 8).
  { subst new_sp_ofs. unfold Ptrofs.sub.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
    apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range sp_ofs).
    unfold Ptrofs.max_unsigned. lia. }

  (* Store 1: sp field <- new_sp *)
  destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 16)
              (Vptr sp_b sp_ofs) (Vptr sp_b new_sp_ofs) Hsp_load) as [m1 Hstore_sp].

  (* Store 2: *new_sp <- accu_v (on sp_b, different block from sb) *)
  destruct (store_to_other_block m m1 sb (Ptrofs.unsigned so + 16)
              (Vptr sp_b new_sp_ofs) sp_b (Ptrofs.unsigned new_sp_ofs) accu_v
              Hstore_sp (not_eq_sym Hblock_sep)
              ltac:(rewrite Hnew_sp_unsigned; lia)) as [m2 Hstore_accu].

  (* After stores 1 and 2, load v6's repr from the stack.
     The load at sp+48 (= new_sp+56) survives both stores. *)
  assert (Hload_sp6_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 48))) = Some cv6).
  { erewrite Mem.load_store_other. exact Hload_sp6. exact Hstore_sp.
    left. exact Hblock_sep. }
  assert (Hload_sp6_m2 : Mem.load Mint64 m2 sp_b (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 48))) = Some cv6).
  { erewrite Mem.load_store_other. exact Hload_sp6_m1. exact Hstore_accu.
    right. right. rewrite Hnew_sp_unsigned. simpl size_chunk.
    rewrite (ptrofs_add_unsigned sp_ofs 48 ltac:(lia) ltac:(lia)). lia. }

  (* new_sp + 56 = sp + 48. *)
  assert (Hadd_back : Ptrofs.add new_sp_ofs (Ptrofs.repr 56) = Ptrofs.add sp_ofs (Ptrofs.repr 48)).
  { subst new_sp_ofs. rewrite Ptrofs.sub_add_opp.
    rewrite Ptrofs.add_assoc. f_equal.
    cut (Ptrofs.unsigned (Ptrofs.add (Ptrofs.neg (Ptrofs.repr 8)) (Ptrofs.repr 56))
         = Ptrofs.unsigned (Ptrofs.repr 48)).
    { intro H. rewrite <- (Ptrofs.repr_unsigned (Ptrofs.add _ _)).
      rewrite H. apply Ptrofs.repr_unsigned. }
    native_compute. reflexivity. }

  (* Store 3: accu field <- cv6 *)
  assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { assert (Haccu_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
               (Ptrofs.unsigned so + 8) (Vptr sp_b new_sp_ofs) accu_v
               Hstore_sp Haccu_load). left. lia. }
    erewrite Mem.load_store_other. exact Haccu_m1. exact Hstore_accu.
    left. exact (not_eq_sym Hblock_sep). }

  destruct (store_succeeds_from_load m2 sb (Ptrofs.unsigned so + 8) accu_v cv6
              Haccu_load_m2) as [m3 Hstore_accu_field].

  (* Define le' with all the temps. *)
  set (le' := PTree.set _t'3 cv6
              (PTree.set _t'2 (Vptr sp_b new_sp_ofs)
              (PTree.set _t'4 accu_v
              (PTree.set _t'1 (Vptr sp_b new_sp_ofs)
              (PTree.set _t'5 (Vptr sp_b sp_ofs) le))))).

  exists le'. exists m3.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ============================================================== *)
  (* Part 1: exec via computational evaluator                        *)
  (* ============================================================== *)
  {
    apply (eval_stmt_to_exec clight_ge 15).
    eval_cbn.

    (* Statement 1: Sset _t'5 (s->sp) *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* Statement 2: Sset _t'1 (cast (sub _t'5 1) (tptr tlong)) *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_sub_sp_1; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.

    (* Statement 3: Sassign (s->sp) _t'1 -- store new_sp to sp field *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    fold new_sp_ofs.
    rewrite Hstore_sp; eval_cbn.

    (* Statement 4: Sset _t'4 (s->accu) -- load accu *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
               (Ptrofs.unsigned so + 8) (Vptr sp_b new_sp_ofs) accu_v
               Hstore_sp Haccu_load ltac:(left; lia)).
    eval_cbn.

    (* Statement 5: Sassign (deref _t'1) _t'4 -- store accu to *new_sp *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ Haccu_repr); eval_cbn.
    fold new_sp_ofs.
    rewrite Hstore_accu; eval_cbn.

    (* Statement 6: Sset _t'2 (s->sp) -- reload sp (now new_sp) *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    try rewrite Mptr_Mint64; eval_cbn.
    try rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    assert (Hsp_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 16) =
              Some (Vptr sp_b new_sp_ofs)).
    { assert (Hsp_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
                Some (Vptr sp_b new_sp_ofs)).
      { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 16)
                      (Vptr sp_b new_sp_ofs) Hstore_sp) as Htmp.
        simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
      erewrite Mem.load_store_other. exact Hsp_m1. exact Hstore_accu.
      left. exact (not_eq_sym Hblock_sep). }
    rewrite Hsp_load_m2; eval_cbn.

    (* Statement 7: Sset _t'3 (deref (_t'2 + 7)) -- load *(new_sp + 7) = stack[6] *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_7; eval_cbn.
    rewrite Hadd_back.
    rewrite Hload_sp6_m2; eval_cbn.

    (* Statement 8: Sassign (s->accu) _t'3 -- store v6 to accu field *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    try rewrite Haccu_offset; eval_cbn.
    try rewrite PTree.gss; eval_cbn.
    try rewrite (sem_cast_long_val_repr _ _ _ _ Hval_repr6); eval_cbn.
    try rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Hstore_accu_field; eval_cbn.

    (* Statement 9: Sreturn 0 *)
    subst le'. reflexivity.
  }

  (* ============================================================== *)
  (* Part 2: abs_rel for post-state                                  *)
  (* ============================================================== *)
  {
    exists ard.
    set (uso := Ptrofs.unsigned so) in *.

    (* Helper: loads on sb survive store 2 (different block) *)
    assert (Hload_sb_m2 : forall ofs v,
      Mem.load Mint64 m1 sb ofs = Some v ->
      Mem.load Mint64 m2 sb ofs = Some v).
    { intros ofs v Hload1.
      erewrite Mem.load_store_other; [exact Hload1 | exact Hstore_accu |].
      left. exact (not_eq_sym Hblock_sep). }

    (* pc field: uso + 0 *)
    assert (Hpc_load3 : Mem.load Mint64 m3 sb (uso + 0) = Some pc_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 0)
               cv6 pc_ptr Hstore_accu_field).
      - apply Hload_sb_m2.
        apply (load_after_store_other m m1 sb (uso + 16) (uso + 0)
                 (Vptr sp_b new_sp_ofs) pc_ptr Hstore_sp Hpc_load).
        left. lia.
      - left. lia. }

    (* accu field: uso + 8, overwritten by store 3 *)
    assert (Haccu_load3 : Mem.load Mint64 m3 sb (uso + 8) = Some cv6).
    { pose proof (load_after_store_same m2 m3 sb (uso + 8) cv6 Hstore_accu_field) as Htmp.
      rewrite (val_repr_load_result hm v6 cv6 Hval_repr6) in Htmp.
      exact Htmp. }

    (* sp field: uso + 16 *)
    assert (Hsp_load3 : Mem.load Mint64 m3 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 16)
               cv6 (Vptr sp_b new_sp_ofs) Hstore_accu_field).
      - assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) =
                  Some (Vptr sp_b new_sp_ofs)).
        { pose proof (load_after_store_same m m1 sb (uso + 16)
                        (Vptr sp_b new_sp_ofs) Hstore_sp) as Htmp.
          simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
        apply Hload_sb_m2. exact Hsp_m1.
      - right. lia. }

    (* env field: uso + 24 *)
    assert (Henv_load3 : Mem.load Mint64 m3 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 24)
               cv6 env_v Hstore_accu_field).
      - apply Hload_sb_m2.
        apply (load_after_store_other m m1 sb (uso + 16) (uso + 24)
                 (Vptr sp_b new_sp_ofs) env_v Hstore_sp Henv_load).
        right. lia.
      - right. lia. }

    (* extra_args field: uso + 32 *)
    assert (Hextra_load3 : Mem.load Mint64 m3 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 32)
               cv6 _ Hstore_accu_field).
      - apply Hload_sb_m2.
        apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
                 (Vptr sp_b new_sp_ofs) _ Hstore_sp Hextra_load).
        right. lia.
      - right. lia. }

    (* global_data field: uso + 40 *)
    assert (Hgd_load3 : Mem.load Mint64 m3 sb (uso + 40) = Some gd_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 40)
               cv6 gd_ptr Hstore_accu_field).
      - apply Hload_sb_m2.
        apply (load_after_store_other m m1 sb (uso + 16) (uso + 40)
                 (Vptr sp_b new_sp_ofs) gd_ptr Hstore_sp Hgd_load).
        right. lia.
      - right. lia. }

    (* trap_sp field: uso + 48 *)
    assert (Hts_load3 : Mem.load Mint64 m3 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 48)
               cv6 ts_ptr Hstore_accu_field).
      - apply Hload_sb_m2.
        apply (load_after_store_other m m1 sb (uso + 16) (uso + 48)
                 (Vptr sp_b new_sp_ofs) ts_ptr Hstore_sp Hts_load).
        right. lia.
      - right. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].

    (* 1. _s is in le' *)
    { subst le'.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      exact Hle_s. }

    (* 2. pc field -- unchanged *)
    { exists pc_ptr. split.
      - exact Hpc_load3.
      - simpl. exact Hpc_rel. }

    (* 3. accu field -- now v6 *)
    { exists cv6. split.
      - exact Haccu_load3.
      - simpl. exact Hval_repr6. }

    (* 4. sp field -- updated to new_sp; stack gets accu prepended *)
    { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
      split; [| split; [| split; [| split; [| split]]]].
      - exact Hsp_load3.
      - reflexivity.
      - simpl.
        assert (Hstack_m1 : stack_repr hm m1 (v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: rest) sp_b sp_ofs).
        { apply (stack_repr_store_other_block hm m m1 _ sp_b sp_ofs sb
                   (uso + 16) (Vptr sp_b new_sp_ofs)
                   Hstack_repr Hstore_sp).
          intro Heq; exact (Hblock_sep (eq_sym Heq)). }
        assert (Hstack_m2 : stack_repr hm m2 (Machine.accu s :: v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: rest) sp_b new_sp_ofs).
        { exact (stack_repr_cons_after_store hm m1 m2
                   (v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: rest) sp_b sp_ofs (Machine.accu s) accu_v
                   Hstack_m1 Haccu_repr Hstore_accu Hsp_ge8). }
        apply (stack_repr_store_other_block hm m2 m3
                 (Machine.accu s :: v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: rest) sp_b new_sp_ofs sb
                 (uso + 8) cv6
                 Hstack_m2 Hstore_accu_field).
                intro Heq; exact (Hblock_sep (eq_sym Heq)).
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp. }

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
        apply (global_repr_store_other_block hm m2 m3 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (uso + 8) cv6).
        + apply (global_repr_store_other_block hm m1 m2 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sp_b (Ptrofs.unsigned new_sp_ofs) accu_v).
          * apply (global_repr_store_other_block hm m m1 _
                     (ar_global_block ard) (ar_global_ofs ard)
                     sb (uso + 16) (Vptr sp_b new_sp_ofs)
                     Hglobal_repr Hstore_sp).
            intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          * exact Hstore_accu.
          * exact Hsp_ne_gb.
        + exact Hstore_accu_field.
                + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load3.
      - simpl. exact Htrap_rel. }
  }
Qed.
