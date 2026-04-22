(* ADDINT_bigstep_compl_computational.v -- ADDINT completeness proof using
   the computational evaluator from StepToBigstep.v.

   ADDINT handler in C:
     _t'1 = s->sp;           // load sp
     s->sp = _t'1 + 1;       // sp++ (pop stack)
     _t'2 = s->accu;         // load accu
     _t'3 = *_t'1;           // load stack[0] (old sp)
     s->accu = (long)((long)_t'2 + (long)_t'3 - 1);  // tagged add
     return 0;

   Rocq handler:
     handle_ADDINT pc' s = match accu, stack with
       | Val_int a, Val_int b :: rest =>
           Step (s<|pc:=pc'|><|accu:=Val_int(a+b)|><|stack:=rest|>)
       | _, _ => Error ...

   This proof handles TWO stores (sp field, accu field) and the tagged
   integer arithmetic identity: (2a+1) + (2b+1) - 1 = 2(a+b) + 1.

   Uses abs_rel directly (no separate _pre relation). *)

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
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

Theorem verify_ADDINT_compl_comp :
    handler_correct handle_ADDINT f_instr_ADDINT
      (pre_and accu_is_long stack_head_is_long)
      (fun _ s => forall a b rest,
         s.(Machine.accu) = Val_int a ->
         s.(Machine.stack) = Val_int b :: rest -> False)
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_ADDINT.

  (* Case split on accu *)
  destruct (Machine.accu s) as [a| | |] eqn:Haccu_eq;
    try (intros; congruence).
  destruct (Machine.stack s) as [|v_hd v_tl] eqn:Hstk;
    try (intros; congruence).
  destruct v_hd as [b| | |] eqn:Hvhd;
    try (intros; congruence).

  (* ================================================================ *)
  (* Step case: accu = Val_int a, stack = Val_int b :: v_tl           *)
  (* ================================================================ *)
  {
    intros ard Hpre Hstep_pre. unfold abs_rel_with_ard in Hpre.
    unfold pre_and, accu_is_long, stack_head_is_long in Hstep_pre.
    destruct Hstep_pre as [Haccu_long Hhead_long].
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

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound.
    fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne.
    fold sb in Hgb_ne.

    (* Accu is Val_int a *)
    rewrite Haccu_eq in Haccu_repr.
    pose proof Haccu_repr as Haccu_repr_rw.
    inversion Haccu_repr; subst accu_v.
    2: { exfalso. rewrite Haccu_eq in Haccu_long.
         destruct (Haccu_long _ Haccu_repr_rw) as [z Hz]. discriminate Hz. }
    rename H0 into Haccu_is_int.

    (* Pre-compute modulus bounds for sp + 8 BEFORE inversion/subst *)
    assert (Hsp_mod_orig : Ptrofs.unsigned sp_ofs + 8 < Ptrofs.modulus).
    { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }
    assert (Hsp_rep_tail : Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length v_tl) < Ptrofs.modulus).
    { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }
    (* Pre-compute writable inclusion for the tail range *)
    assert (Hsp_writable_tail : Mem.range_perm m sp_b 0
              (Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length v_tl)) Cur Writable).
    { intros ofs' Hofs'. apply Hsp_writable. rewrite Hstk. simpl length.
      pose proof (Nat2Z.is_nonneg (length v_tl)). lia. }

    (* Extract stack head *)
    rewrite Hstk in Hstack_repr.
    inversion Hstack_repr as [| ? ? ? ? cv0 Hload_sp0 Hval_repr0 Hstack_repr_rest].
    (* Protect gd_ptr from bare subst by reverting it *)
    revert Hgd_load Hgd_eq Hglobal_repr.
    subst.
    intros Hgd_load Hgd_eq Hglobal_repr.

    (* Stack head is Val_int b *)
    pose proof Hval_repr0 as Hval_repr0_rw.
    inversion Hval_repr0; subst cv0.
    2: { exfalso. rewrite Hstk in Hhead_long.
         destruct (Hhead_long _ Hval_repr0_rw) as [z Hz]. discriminate Hz. }
    rename H0 into Hstk_is_int.

    (* Composite environment facts *)
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    (* --- Store 1: sp field (so+16) gets sp+1 = Vptr sp_b (sp_ofs + 8) --- *)
    set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
    destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) new_sp_v)
      as [m1 Hstore1].

    (* --- After store 1: load accu from m1 --- *)
    assert (Haccu_load_m1 :
      Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) =
        Some (Vlong (Int64.repr (a * 2 + 1)))).
    { apply (load_after_store_other m m1 sb
               (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8)
               new_sp_v (Vlong (Int64.repr (a * 2 + 1)))
               Hstore1 Haccu_load). left. lia. }

    (* --- After store 1: load *sp from m1 (different block) --- *)
    assert (Hload_sp0_m1 :
      Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) =
        Some (Vlong (Int64.repr (b * 2 + 1)))).
    { erewrite Mem.load_store_other.
      - exact Hload_sp0.
      - exact Hstore1.
      - left. exact Hsp_ne_sb. }

    (* --- Store 2: accu field (so+8) gets the tagged add result --- *)
    set (result_v := Vlong (Int64.sub (Int64.add (Int64.repr (a * 2 + 1))
                                                  (Int64.repr (b * 2 + 1)))
                                       (Int64.repr 1))).
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.
    destruct (store_succeeds_sb m1 sb so 8 (Vlong (Int64.repr (a * 2 + 1))) Hsb_writable_m1 Haccu_load_m1 ltac:(lia) ltac:(lia) result_v)
      as [m' Hstore2].

    (* Witnesses *)
    set (le' := PTree.set _t'3 (Vlong (Int64.repr (b * 2 + 1)))
                  (PTree.set _t'2 (Vlong (Int64.repr (a * 2 + 1)))
                    (PTree.set _t'1 (Vptr sp_b sp_ofs) le))).
    exists le'. exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (* ============================================================== *)
    {
      apply (eval_stmt_to_exec clight_ge 10).

      (* --- Initial reduction --- *)
      eval_cbn.

      (* === Sset _t'1 (s->sp) === *)
      rewrite Hle_s; eval_cbn.                                       (* le ! _s *)
      rewrite Hco; eval_cbn.                                         (* composite lookup *)
      rewrite Hsp_offset; eval_cbn.                                  (* field_offset _sp *)
      rewrite Mptr_Mint64; eval_cbn.                                 (* Mptr -> Mint64 *)
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).     (* sp ptrofs *)
      rewrite Hsp_load; eval_cbn.                                    (* sp field load *)

      (* === Sassign (s->sp = _t'1 + 1) : lvalue + rhs + store === *)
      rewrite PTree.gso by (compute; congruence).                    (* le1 ! _s: skip _t'1 *)
      rewrite Hle_s; eval_cbn.                                       (* le ! _s => lvalue resolved *)
      rewrite PTree.gss; eval_cbn.                                   (* le1 ! _t'1 *)
      rewrite sem_add_sp_1; eval_cbn.                                (* sp + 1 = sp + 8 *)
      rewrite sem_cast_ptr_to_ptr; eval_cbn.                         (* cast (tptr tlong)->(tptr tlong) *)
      rewrite Mptr_Mint64; eval_cbn.                                   (* Mptr -> Mint64 *)
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).     (* sp field ptrofs *)
      unfold new_sp_v in Hstore1.
      rewrite Hstore1; eval_cbn.                                     (* sp store *)

      (* === Sset _t'2 (s->accu) -- reads from m1 === *)
      rewrite PTree.gso by (compute; congruence).                    (* le2 ! _s: skip _t'1 *)
      rewrite Hle_s; eval_cbn.                                       (* le ! _s + eval *)
      rewrite Haccu_offset; eval_cbn.                                (* field_offset _accu *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).      (* accu ptrofs *)
      rewrite Haccu_load_m1; eval_cbn.                               (* accu field load from m1 *)

      (* === Sset _t'3 [deref _t'1] -- deref old sp === *)
      (* _t'1 was set first, then _t'2. le now has _t'2 on top, _t'1 below.
         gso skips _t'2, gss hits _t'1. *)
      rewrite PTree.gso by (compute; congruence).                    (* skip _t'2 *)
      rewrite PTree.gss; eval_cbn.                                   (* get _t'1 + deref *)
      rewrite Hload_sp0_m1; eval_cbn.                                (* load from sp in m1 *)

      (* === Sassign (s->accu = (long)((long)_t'2 + (long)_t'3 - 1)) : lvalue === *)
      rewrite PTree.gso by (compute; congruence).                    (* le4 ! _s: skip _t'3 *)
      rewrite PTree.gso by (compute; congruence).                    (* le4 ! _s: skip _t'2 *)
      rewrite PTree.gso by (compute; congruence).                    (* le4 ! _s: skip _t'1 *)
      rewrite Hle_s; eval_cbn.                                       (* le ! _s => lvalue resolved *)

      (* === Sassign rhs: evaluate (long)((long)_t'2 + (long)_t'3 - 1) === *)
      (* _t'2 *)
      rewrite PTree.gso by (compute; congruence).                    (* le4 ! _t'2: skip _t'3 *)
      rewrite PTree.gss; eval_cbn.                                   (* le3 ! _t'2 *)
      (* sem_cast _t'2 tlong tlong *)
      rewrite sem_cast_long_vlong; eval_cbn.

      (* _t'3 *)
      rewrite PTree.gss; eval_cbn.                                   (* le4 ! _t'3 *)
      (* sem_cast _t'3 tlong tlong *)
      rewrite sem_cast_long_vlong; eval_cbn.

      (* sem_binary_operation Oadd (Vlong ...) tlong (Vlong ...) tlong m1 *)
      rewrite sem_add_long_long; eval_cbn.

      (* sem_binary_operation Osub (Vlong (add ...)) tlong (Vint 1) tint m1 *)
      rewrite sem_sub_long_int; eval_cbn.

      (* Final sem_cast of result *)
      rewrite sem_cast_long_vlong; eval_cbn.

      (* Sassign cast: sem_cast of result from tlong to tlong *)
      rewrite sem_cast_long_vlong; eval_cbn.

      (* Store to accu field *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      unfold result_v in Hstore2.
      rewrite Hstore2; eval_cbn.

      (* === Sreturn 0 === *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      exists ard.
      set (uso := Ptrofs.unsigned so) in *.

      (* --- Loads from m' (after store2 at so+8, store1 at so+16 in m1) --- *)

      (* pc field at so+0: unaffected by both stores *)
      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
      { assert (Hpc_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some pc_ptr).
        { apply (load_after_store_other m m1 sb
                   (uso + 16) (uso + 0) new_sp_v pc_ptr
                   Hstore1 Hpc_load). left. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 8) (uso + 0) result_v pc_ptr
                 Hstore2 Hpc_m1). left. lia. }

      (* sp field at so+16: written by store1, unaffected by store2 *)
      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some new_sp_v).
      { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some new_sp_v).
        { pose proof (load_after_store_same m m1 sb (uso + 16) new_sp_v Hstore1) as Htmp.
          unfold new_sp_v in Htmp |- *. simpl Val.load_result in Htmp.
          rewrite ptr64_true in Htmp.
          exact Htmp. }
        apply (load_after_store_other m1 m' sb
                 (uso + 8) (uso + 16) result_v new_sp_v
                 Hstore2 Hsp_m1). right. lia. }

      (* accu field at so+8: written by store2 *)
      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some result_v).
      { pose proof (load_after_store_same m1 m' sb (uso + 8) result_v Hstore2) as Htmp.
        unfold result_v in Htmp |- *. simpl Val.load_result in Htmp.
        exact Htmp. }

      (* env field at so+24: unaffected by both stores *)
      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
      { assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m1 sb
                   (uso + 16) (uso + 24) new_sp_v env_v
                   Hstore1 Henv_load). right. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 8) (uso + 24) result_v env_v
                 Hstore2 Henv_m1). right. lia. }

      (* extra_args field at so+32: unaffected by both stores *)
      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { assert (Hextra_m1 : Mem.load Mint64 m1 sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m1 sb
                   (uso + 16) (uso + 32) new_sp_v _
                   Hstore1 Hextra_load). right. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 8) (uso + 32) result_v _
                 Hstore2 Hextra_m1). right. lia. }

      (* global_data field at so+40: unaffected by both stores *)
      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { assert (Hgd_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m1 sb
                   (uso + 16) (uso + 40) new_sp_v gd_ptr
                   Hstore1 Hgd_load). right. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 8) (uso + 40) result_v gd_ptr
                 Hstore2 Hgd_m1). right. lia. }

      (* trap_sp field at so+48: unaffected by both stores *)
      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { assert (Hts_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m1 sb
                   (uso + 16) (uso + 48) new_sp_v ts_ptr
                   Hstore1 Hts_load). right. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 8) (uso + 48) result_v ts_ptr
                 Hstore2 Hts_m1). right. lia. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field -- unchanged by handler *)
      { exists pc_ptr. split.
        - exact Hpc_load'.
        - simpl. exact Hpc_rel. }

      (* 3. accu field -- updated to Val_int (a + b) *)
      { exists result_v. split.
        - exact Haccu_load'.
        - simpl.
          (* Goal: val_repr hm cb co (Val_int (a + b)) result_v *)
          unfold result_v.
          rewrite tagged_addint_arith.
          constructor. }

      (* 4. sp field -- updated to sp + 8 (stack tail) *)
      { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)).
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load'.
        - reflexivity.
        - simpl.
          (* Goal: stack_repr hm cb co m' <tail> sp_b (sp_ofs + 8) *)
          (* Hstack_repr_rest: stack_repr hm cb co m <tail> sp_b (sp_ofs + 8) *)
          (* m -> m1 (store to sb at so+16) -> m' (store to sb at so+8) *)
          (* Both stores to sb, stack in sp_b. sb <> sp_b. *)
          eapply (stack_repr_store_other_block hm cb co m1 m' _ sp_b
                   (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) result_v).
          + eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b
                     (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16) new_sp_v).
            * exact Hstack_repr_rest.
            * exact Hstore1.
            * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          + exact Hstore2.
                    + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - (* sp_ge8 *)
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)). lia.
        - (* sp_rep *)
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)). exact Hsp_rep_tail.
        - (* sp_writable *)
          intros ofs' Hofs'.
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)) in Hofs'.
          eapply Mem.perm_store_1. exact Hstore2.
          eapply Mem.perm_store_1. exact Hstore1.
          apply Hsp_writable_tail. exact Hofs'.
        - (* sp_align *)
          simpl.
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)).
          apply Z.divide_add_r. exact Hsp_align. exists 1. lia. }

      (* 5. env field -- unchanged *)
      { exists env_v. split.
        - exact Henv_load'.
        - simpl. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { simpl. exact Hextra_load'. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load'.
        - simpl. exact Hgd_eq.
        - simpl.
          (* global_repr through two stores to sb *)
          eapply (global_repr_store_other_block hm cb co m1 m' _ _ _ sb (uso + 8) result_v).
          + eapply (global_repr_store_other_block hm cb co m m1 _ _ _ sb (uso + 16) new_sp_v).
            * exact Hglobal_repr.
            * exact Hstore1.
            * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          + exact Hstore2.
                    + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load'.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved *)
      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. eapply Mem.perm_store_1. exact Hstore1. apply Hsb_writable. exact Hofs'. }
    }
  }
Qed.

(* ================================================================== *)
(* Wrapper with canonical InstructSpec predicates                       *)
(* ================================================================== *)

Import Bytecode.AST.

Theorem correct_ADDINT :
    handler_correct (handle_instr ADDINT) (clight_of ADDINT)
      (pre_of ADDINT)
      (P_error_of ADDINT) (P_halt_of ADDINT) (P_ccall_of ADDINT).
Proof.
Admitted.
