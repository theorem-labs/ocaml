(* PUSHCONST2_correct.v -- PUSHCONST2 completeness proof.

   PUSHCONST2 = PUSH then CONST2.
   C code:
     sp = sp - 1;          // decrement sp
     *sp = accu;            // push old accu onto stack
     accu = Val_int(2);     // set accu to tagged 2 = (2<<1)+1 = 5
   Rocq:
     handle_PUSHCONSTINT 2 pc' s =
       Step (s <|pc := pc'|> <|accu := Val_int 2|> <|stack := accu :: stack|>)

   Three stores:
     Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v
     Store 3: accu field (sb, uso+8) <- Vlong (Int64.repr 5)

   Follows the patterns of PUSH_correct.v and CONST2_correct.v. *)

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

(* Arithmetic lemmas for constant 2: (2 << 1) + 1 = 5 *)
Local Lemma sem_cast_int_to_long_2 : forall m,
  sem_cast (Vint (Int.repr 2)) tint tlong m = Some (Vlong (Int64.repr 2)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_shl_long_2_1 : forall m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong (Int64.repr 2)) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.repr 4)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_add_long_int_4_1 : forall m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong (Int64.repr 4)) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.repr 5)).
Proof. intros. reflexivity. Qed.

Local Lemma val_int_2_load_result :
  Val.load_result Mint64 (Vlong (Int64.repr 5)) = Vlong (Int64.repr 5).
Proof. reflexivity. Qed.

Theorem verify_PUSHCONST2_correct :
    handler_correct (handle_PUSHCONSTINT 2) f_instr_PUSHCONST2
      (fun _ _ => True)
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handler_correct, handle_PUSHCONSTINT. simpl.
  intro Hpre.

  (* Unpack abs_rel *)
  destruct Hpre as [ard Hpre].
  set (sb := ar_sptr_block ard) in *.
  set (so := ar_sptr_ofs ard) in *.
  set (hm := ar_heap_map ard) in *.
  destruct Hpre as (Hle_s &
    [pc_ptr [Hpc_load Hpc_rel]] &
    [accu_v [Haccu_load Haccu_repr]] &
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq Hstack_repr]]]]] &
    [env_v [Henv_load Henv_repr]] &
    Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq Hglobal_repr]]] &
    [ts_ptr [Hts_load Htrap_rel]]).
  subst sp_ptr.

  (* Structural invariants *)
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep. fold sb in Hblock_sep.
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  pose proof (sp_block_ne_global ard sp_b) as Hsp_ne_gb.
  pose proof (sp_ofs_ge_8 hm m (Machine.stack s) sp_b sp_ofs Hstack_repr) as Hsp_ge8.

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
  destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 16)
              (Vptr sp_b sp_ofs) (Vptr sp_b new_sp_ofs) Hsp_load) as [m1 Hstore_sp].

  (* Store 2: *new_sp <- accu_v (different block from sb) *)
  destruct (store_to_other_block m m1 sb (Ptrofs.unsigned so + 16)
              (Vptr sp_b new_sp_ofs) sp_b (Ptrofs.unsigned new_sp_ofs) accu_v
              Hstore_sp (not_eq_sym Hblock_sep)
              ltac:(rewrite Hnew_sp_unsigned; lia)) as [m2 Hstore_accu].

  (* Store 3: accu field <- Vlong (Int64.repr 5) *)
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
             (Ptrofs.unsigned so + 8) (Vptr sp_b new_sp_ofs) accu_v
             Hstore_sp Haccu_load). left. lia. }
  assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { erewrite Mem.load_store_other; [exact Haccu_load_m1 | exact Hstore_accu |].
    left. exact (not_eq_sym Hblock_sep). }
  destruct (store_succeeds_from_load m2 sb (Ptrofs.unsigned so + 8)
              accu_v (Vlong (Int64.repr 5)) Haccu_load_m2) as [m3 Hstore_const].

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
    rewrite (sem_cast_long_val_repr _ _ _ _ Haccu_repr); eval_cbn.
    fold new_sp_ofs.
    rewrite Hstore_accu; eval_cbn.

    (* Statement 6: Sassign (s->accu) ((2 << 1) + 1) *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.

    (* rvalue: ((cast 2 tlong) << 1) + 1 *)
    rewrite (sem_cast_int_to_long_2 m2); eval_cbn.
    rewrite (sem_shl_long_2_1 m2); eval_cbn.
    rewrite (sem_add_long_int_4_1 m2); eval_cbn.
    rewrite (sem_cast_long_vlong (Int64.repr 5)); eval_cbn.

    (* store to accu field *)
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Hstore_const; eval_cbn.

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
      left. exact (not_eq_sym Hblock_sep). }

    (* Helper: loads on sp_b survive store 3 (different block: sb vs sp_b) *)
    assert (Hload_spb_m3 : forall ofs v,
      Mem.load Mint64 m2 sp_b ofs = Some v ->
      Mem.load Mint64 m3 sp_b ofs = Some v).
    { intros ofs v Hload2.
      erewrite Mem.load_store_other; [exact Hload2 | exact Hstore_const |].
      left. exact Hblock_sep. }

    (* pc field: uso + 0, unaffected by all 3 stores *)
    assert (Hpc_load3 : Mem.load Mint64 m3 sb (uso + 0) = Some pc_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 0)
               (Vlong (Int64.repr 5)) pc_ptr Hstore_const).
      - apply Hload_sb_m2.
        apply (load_after_store_other m m1 sb (uso + 16) (uso + 0)
                 (Vptr sp_b new_sp_ofs) pc_ptr Hstore_sp Hpc_load).
        left. lia.
      - left. lia. }

    (* accu field: uso + 8, overwritten by store 3 *)
    assert (Haccu_load3 : Mem.load Mint64 m3 sb (uso + 8) = Some (Vlong (Int64.repr 5))).
    { pose proof (load_after_store_same m2 m3 sb (uso + 8)
                    (Vlong (Int64.repr 5)) Hstore_const) as Htmp.
      rewrite val_int_2_load_result in Htmp.
      exact Htmp. }

    (* sp field: uso + 16, overwritten by store 1, survives stores 2 and 3 *)
    assert (Hsp_load3 : Mem.load Mint64 m3 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 16)
               (Vlong (Int64.repr 5)) (Vptr sp_b new_sp_ofs) Hstore_const).
      - apply Hload_sb_m2.
        pose proof (load_after_store_same m m1 sb (uso + 16)
                      (Vptr sp_b new_sp_ofs) Hstore_sp) as Htmp.
        simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp.
      - right. lia. }

    (* env field: uso + 24, unaffected by all 3 stores *)
    assert (Henv_load3 : Mem.load Mint64 m3 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 24)
               (Vlong (Int64.repr 5)) env_v Hstore_const).
      - apply Hload_sb_m2.
        apply (load_after_store_other m m1 sb (uso + 16) (uso + 24)
                 (Vptr sp_b new_sp_ofs) env_v Hstore_sp Henv_load).
        right. lia.
      - right. lia. }

    (* extra_args field: uso + 32 *)
    assert (Hextra_load3 : Mem.load Mint64 m3 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 32)
               (Vlong (Int64.repr 5)) _ Hstore_const).
      - apply Hload_sb_m2.
        apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
                 (Vptr sp_b new_sp_ofs) _ Hstore_sp Hextra_load).
        right. lia.
      - right. lia. }

    (* global_data field: uso + 40 *)
    assert (Hgd_load3 : Mem.load Mint64 m3 sb (uso + 40) = Some gd_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 40)
               (Vlong (Int64.repr 5)) gd_ptr Hstore_const).
      - apply Hload_sb_m2.
        apply (load_after_store_other m m1 sb (uso + 16) (uso + 40)
                 (Vptr sp_b new_sp_ofs) gd_ptr Hstore_sp Hgd_load).
        right. lia.
      - right. lia. }

    (* trap_sp field: uso + 48 *)
    assert (Hts_load3 : Mem.load Mint64 m3 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 48)
               (Vlong (Int64.repr 5)) ts_ptr Hstore_const).
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
      exact Hle_s. }

    (* 2. pc field -- unchanged by handler *)
    { exists pc_ptr. split.
      - exact Hpc_load3.
      - simpl. exact Hpc_rel. }

    (* 3. accu field -- updated to Val_int 2 *)
    { exists (Vlong (Int64.repr 5)). split.
      - exact Haccu_load3.
      - simpl. exact (vr_int _ 2). }

    (* 4. sp field -- updated to new_sp_ofs; stack gets accu prepended *)
    { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
      split; [| split].
      - exact Hsp_load3.
      - reflexivity.
      - simpl.
        assert (Hstack_m1 : stack_repr hm m1 (Machine.stack s) sp_b sp_ofs).
        { apply (stack_repr_store_other_block hm m m1 _ sp_b sp_ofs sb
                   (uso + 16) (Vptr sp_b new_sp_ofs)
                   Hstack_repr Hstore_sp).
          intro Heq; exact (Hblock_sep (eq_sym Heq)). }
        assert (Hstack_cons_m2 : stack_repr hm m2 (Machine.accu s :: Machine.stack s) sp_b new_sp_ofs).
        { exact (stack_repr_cons_after_store hm m1 m2
                   (Machine.stack s) sp_b sp_ofs (Machine.accu s) accu_v
                   Hstack_m1 Haccu_repr Hstore_accu Hsp_ge8). }
        apply (stack_repr_store_other_block hm m2 m3 _ sp_b new_sp_ofs sb
                 (uso + 8) (Vlong (Int64.repr 5))
                 Hstack_cons_m2 Hstore_const).
        intro Heq; exact (Hblock_sep (eq_sym Heq)). }

    (* 5. env field -- unchanged *)
    { exists env_v. split.
      - exact Henv_load3.
      - simpl. exact Henv_repr. }

    (* 6. extra_args field -- unchanged *)
    { simpl. exact Hextra_load3. }

    (* 7. global_data field -- unchanged *)
    { exists gd_ptr. split; [| split].
      - exact Hgd_load3.
      - simpl. exact Hgd_eq.
      - simpl.
        apply (global_repr_store_other_block hm m2 m3 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (uso + 8) (Vlong (Int64.repr 5))).
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
        + exact Hstore_const.
        + intro Heq2; exact (Hgb_ne (eq_sym Heq2)). }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load3.
      - simpl. exact Htrap_rel. }
  }
Qed.
