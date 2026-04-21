(* SETFIELD0_correct.v -- SETFIELD0 correctness proof.

   SETFIELD0: pop stack top, write it to heap field 0 of accu,
   set accu = val_unit.

   Rocq handler:
     handle_SETFIELD 0 pc' s =
       match stack with
       | newval :: rest =>
         match accu with
         | Val_ptr addr =>
           match heap_lookup hp addr with
           | Some (_, fields) =>
             match set_nth fields 0 newval with
             | Some new_fields => Step (s <|pc:=pc'|> <|accu:=val_unit|>
                                          <|stack:=rest|> <|hp:=heap_update ...|>)
             | None => Error "index out of bounds"
             end
           | None => Error "dangling pointer"
           end
         | _ => Error "not a mutable block"
         end
       | _ => Error "stack underflow"
       end

   C handler (f_instr_SETFIELD0):
     _t'1 = s->sp;               // read sp
     s->sp = _t'1 + 1;           // sp++ (pop)
     _t'2 = s->accu;             // read accu (heap ptr)
     _t'3 = *_t'1;               // read stack top
     *(cast(_t'2) + 0) = _t'3;   // store to heap field 0
     s->accu = ((0 << 1) + 1);   // val_unit = 1
     return 0;

   Three stores: sp field (so+16), heap block, accu field (so+8).
   The heap write is to a block separate from sb and sp_b (precondition).

   NO AXIOMS. NO ADMITTED. *)

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

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Semantic lemma: cast tlong -> (tptr tlong) for Vptr                 *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* sem_add for (tptr tlong) + 0 *)
Local Lemma sem_add_ptr_long_0 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint (Int.repr 0)) tint m
    = Some (Vptr b ofs).
Proof. exact sem_add_sp_0. Qed.

(* ================================================================== *)
(* Load result for Vlong                                               *)
(* ================================================================== *)

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Heap-store precondition                                             *)
(* ================================================================== *)

(* Heap-store precondition for field 0: now uses generic setfield_heap_pre 0. *)

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_SETFIELD0_correct :
    handler_correct (handle_SETFIELD 0) f_instr_SETFIELD0
      (setfield_heap_pre 0)
      (fun _ s => match s.(Machine.stack) with
                  | _ :: _ =>
                    match s.(Machine.accu) with
                    | Val_ptr addr =>
                      match heap_lookup s.(Machine.hp) addr with
                      | Some (_, fields) => set_nth fields 0 (hd (Val_int 0) s.(Machine.stack)) = None
                      | None => True
                      end
                    | _ => True
                    end
                  | _ => True end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_SETFIELD.

  (* Case split on stack *)
  destruct (Machine.stack s) as [|newval rest] eqn:Hstk.
  { (* stack = [] => Error "stack underflow" *)
    reflexivity. }

  (* Case split on accu *)
  destruct (Machine.accu s) as [z_val|blk_tag blk_flds|addr|clo_addr clo_ofs] eqn:Haccu_eq;
    try exact I.

  (* Main case: accu = Val_ptr addr *)
  destruct (heap_lookup (Machine.hp s) addr) as [[tag fields]|] eqn:Hlookup.
  2: { (* heap_lookup = None => Error "dangling pointer" *)
    exact I. }

  destruct (set_nth fields 0 newval) as [new_fields|] eqn:Hset.
  2: { (* set_nth = None => Error "index out of bounds" *)
    simpl. exact Hset. }

  (* ================================================================ *)
  (* Step case: stack = newval :: rest, accu = Val_ptr addr,           *)
  (*            heap_lookup = Some (tag, fields), set_nth = Some       *)
  (* ================================================================ *)
  {
    intros ard Hpre Hhpre.
    unfold abs_rel_with_ard in Hpre.

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
    pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.

    (* Composite environment facts *)
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    (* Stack repr: extract head *)
    rewrite Hstk in Hstack_repr.
    inversion Hstack_repr as [| ? ? ? ? stk_top_cv Hload_sp0 Hval_repr_top Hstack_repr_rest].
    (* Protect gd_ptr from bare subst *)
    revert Hgd_load Hgd_eq Hglobal_repr.
    subst.
    intros Hgd_load Hgd_eq Hglobal_repr.

    (* Stack bounds *)
    assert (Hsp_mod_orig : Ptrofs.unsigned sp_ofs + 8 < Ptrofs.modulus).
    { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }
    assert (Hsp_rep_tail : Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length rest) < Ptrofs.modulus).
    { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }
    assert (Hsp_writable_tail : Mem.range_perm m sp_b 0
              (Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length rest)) Cur Writable).
    { intros ofs' Hofs'. apply Hsp_writable. rewrite Hstk. simpl length.
      pose proof (Nat2Z.is_nonneg (length rest)). lia. }

    (* Use heap precondition *)
    unfold setfield_heap_pre in Hhpre.
    specialize (Hhpre newval rest Hstk accu_v Haccu_repr sp_b sp_ofs Hsp_load stk_top_cv Hval_repr_top).
    destruct Hhpre as [hb [hofs [Haccu_is_ptr [Hhb_ne_sb [Hhb_ne_sp [Hhb_ne_gb Hheap_store_ok]]]]]].
    subst accu_v.

    (* Simplify Ptrofs.add hofs (Ptrofs.repr 0) = hofs *)
    assert (Hofs_eq : Ptrofs.add hofs (Ptrofs.repr 0) = hofs).
    { change (Ptrofs.repr 0) with Ptrofs.zero. apply Ptrofs.add_zero. }

    (* ============================================================ *)
    (* Store 1: sp field (so+16) <- Vptr sp_b (sp_ofs + 8)          *)
    (* ============================================================ *)
    set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
    destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) new_sp_v)
      as [m1 Hstore1].

    (* Accu load survives store 1 *)
    assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) =
              Some (Vptr hb hofs)).
    { apply (load_after_store_other m m1 sb
               (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8)
               new_sp_v (Vptr hb hofs)
               Hstore1 Haccu_load). left. lia. }

    (* Stack top load survives store 1 (different block) *)
    assert (Hload_sp0_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) =
              Some stk_top_cv).
    { erewrite Mem.load_store_other.
      - exact Hload_sp0.
      - exact Hstore1.
      - left. exact Hsp_ne_sb. }

    (* ============================================================ *)
    (* Store 2: heap write at (hb, hofs) <- stk_top_cv              *)
    (* ============================================================ *)
    change (Z.of_nat 0 * 8) with 0 in Hheap_store_ok.
    rewrite Hofs_eq in Hheap_store_ok.
    destruct (Hheap_store_ok m1 Hstore1) as [m2 Hstore2].

    (* ============================================================ *)
    (* Store 3: accu field (so+8) <- val_unit = Vlong 1              *)
    (* ============================================================ *)
    set (unit_v := Vlong (Int64.repr 1)).

    (* sb_writable through stores 1 and 2 *)
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.
    assert (Hsb_writable_m2 : Mem.range_perm m2 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2.
      apply Hsb_writable_m1. exact Hofs'. }

    (* Accu load survives store 2 (different block) *)
    assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) =
              Some (Vptr hb hofs)).
    { erewrite Mem.load_store_other.
      - exact Haccu_load_m1.
      - exact Hstore2.
      - left. intro Heq. exact (Hhb_ne_sb (eq_sym Heq)). }

    destruct (store_succeeds_sb m2 sb so 8 (Vptr hb hofs) Hsb_writable_m2 Haccu_load_m2 ltac:(lia) ltac:(lia) unit_v)
      as [m3 Hstore3].

    (* ============================================================ *)
    (* Witnesses                                                     *)
    (* ============================================================ *)
    set (le' := PTree.set _t'3 stk_top_cv
                  (PTree.set _t'2 (Vptr hb hofs)
                    (PTree.set _t'1 (Vptr sp_b sp_ofs) le))).
    exists le'. exists m3.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (* ============================================================== *)
    {
      apply (eval_stmt_to_exec clight_ge 15).
      eval_cbn.

      (* S1: Sset _t'1 (s->sp) *)
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hsp_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      rewrite Hsp_load; eval_cbn.

      (* S2: Sassign (s->sp = _t'1 + 1) -- store 1 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite sem_add_sp_1; eval_cbn.
      rewrite sem_cast_ptr_to_ptr; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      unfold new_sp_v in Hstore1.
      rewrite Hstore1; eval_cbn.

      (* S3: Sset _t'2 (s->accu) -- read accu from m1 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Haccu_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Haccu_load_m1; eval_cbn.

      (* S4: Sset _t'3 (deref _t'1) -- read stack top from m1 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite Hload_sp0_m1; eval_cbn.

      (* S5: Sassign *(cast(_t'2) + 0) = _t'3 -- heap store *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite sem_cast_long_to_ptr_vptr; eval_cbn.
      rewrite (sem_add_ptr_long_0 hb hofs m1); eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hval_repr_top); eval_cbn.
      rewrite Hstore2; eval_cbn.

      (* S6: Sassign (s->accu = ((0 << 1) + 1)) -- val_unit store *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite (sem_cast_int_to_long_0 m2); eval_cbn.
      rewrite (sem_shl_long_0_1 m2); eval_cbn.
      rewrite (sem_add_long_int_0_1 m2); eval_cbn.
      rewrite (sem_cast_long_vlong (Int64.repr 1)); eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      fold unit_v. rewrite Hstore3; eval_cbn.

      (* S7: Sreturn 0 *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      exists ard.
      set (uso := Ptrofs.unsigned so) in *.

      (* --- Loads from m3 --- *)

      (* Helper: loads on sb from m1 survive store 2 (hb <> sb) *)
      assert (Hload_m2_sb : forall ofs0 v0,
        Mem.load Mint64 m1 sb ofs0 = Some v0 ->
        Mem.load Mint64 m2 sb ofs0 = Some v0).
      { intros ofs0 v0 Hld.
        erewrite Mem.load_store_other; [exact Hld | exact Hstore2 |].
        left. intro Heq. exact (Hhb_ne_sb (eq_sym Heq)). }

      (* pc field at uso+0 *)
      assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 0)
                 new_sp_v pc_ptr Hstore1 Hpc_load). left. lia. }
      assert (Hpc_load3 : Mem.load Mint64 m3 sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 0)
                 unit_v pc_ptr Hstore3). apply Hload_m2_sb. exact Hpc_load_m1. left. lia. }

      (* sp field at uso+16: written by store 1 *)
      assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some new_sp_v).
      { pose proof (load_after_store_same m m1 sb (uso + 16) new_sp_v Hstore1) as Htmp.
        unfold new_sp_v in Htmp |- *. simpl Val.load_result in Htmp.
        rewrite ptr64_true in Htmp. exact Htmp. }
      assert (Hsp_load3 : Mem.load Mint64 m3 sb (uso + 16) = Some new_sp_v).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 16)
                 unit_v new_sp_v Hstore3). apply Hload_m2_sb. exact Hsp_load_m1. right. lia. }

      (* accu field at uso+8: written by store 3 *)
      assert (Haccu_load3 : Mem.load Mint64 m3 sb (uso + 8) = Some unit_v).
      { pose proof (load_after_store_same m2 m3 sb (uso + 8) unit_v Hstore3) as Htmp.
        subst unit_v. rewrite load_result_vlong in Htmp. exact Htmp. }

      (* env field at uso+24 *)
      assert (Henv_load_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 24)
                 new_sp_v env_v Hstore1 Henv_load). right. lia. }
      assert (Henv_load3 : Mem.load Mint64 m3 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 24)
                 unit_v env_v Hstore3). apply Hload_m2_sb. exact Henv_load_m1. right. lia. }

      (* extra_args field at uso+32 *)
      assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
                 new_sp_v _ Hstore1 Hextra_load). right. lia. }
      assert (Hextra_load3 : Mem.load Mint64 m3 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 32)
                 unit_v _ Hstore3). apply Hload_m2_sb. exact Hextra_load_m1. right. lia. }

      (* global_data field at uso+40 *)
      assert (Hgd_load_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 40)
                 new_sp_v gd_ptr Hstore1 Hgd_load). right. lia. }
      assert (Hgd_load3 : Mem.load Mint64 m3 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 40)
                 unit_v gd_ptr Hstore3). apply Hload_m2_sb. exact Hgd_load_m1. right. lia. }

      (* trap_sp field at uso+48 *)
      assert (Hts_load_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 48)
                 new_sp_v ts_ptr Hstore1 Hts_load). right. lia. }
      assert (Hts_load3 : Mem.load Mint64 m3 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 48)
                 unit_v ts_ptr Hstore3). apply Hload_m2_sb. exact Hts_load_m1. right. lia. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field -- unchanged *)
      { exists pc_ptr. split.
        - exact Hpc_load3.
        - simpl. exact Hpc_rel. }

      (* 3. accu field -- updated to val_unit = Val_int 0 *)
      { exists unit_v. split.
        - exact Haccu_load3.
        - simpl. subst unit_v. exact (vr_int _ _ _ 0). }

      (* 4. sp field -- updated to sp + 8 (stack tail) *)
      { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)).
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load3.
        - reflexivity.
        - simpl.
          (* stack_repr through stores: m -> m1 (sb store), m1 -> m2 (hb store), m2 -> m3 (sb store) *)
          eapply (stack_repr_store_other_block hm cb co m2 m3 _ sp_b
                   (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) unit_v).
          + eapply (stack_repr_store_other_block hm cb co m1 m2 _ sp_b
                     (Ptrofs.add sp_ofs (Ptrofs.repr 8)) hb (Ptrofs.unsigned hofs) stk_top_cv).
            * eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b
                       (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16) new_sp_v).
              -- exact Hstack_repr_rest.
              -- exact Hstore1.
              -- intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
            * exact Hstore2.
            * intro Heq. exact (Hhb_ne_sp Heq).
          + exact Hstore3.
          + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)). lia.
        - rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)). exact Hsp_rep_tail.
        - intros ofs' Hofs'.
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)) in Hofs'.
          eapply Mem.perm_store_1. exact Hstore3.
          eapply Mem.perm_store_1. exact Hstore2.
          eapply Mem.perm_store_1. exact Hstore1.
          apply Hsp_writable_tail. exact Hofs'.
        - simpl.
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)).
          apply Z.divide_add_r. exact Hsp_align. exists 1. lia. }

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
          apply (global_repr_store_other_block hm cb co m2 m3 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sb (uso + 8) unit_v).
          + apply (global_repr_store_other_block hm cb co m1 m2 _
                     (ar_global_block ard) (ar_global_ofs ard)
                     hb (Ptrofs.unsigned hofs) stk_top_cv).
            * apply (global_repr_store_other_block hm cb co m m1 _
                       (ar_global_block ard) (ar_global_ofs ard)
                       sb (uso + 16) new_sp_v
                       Hglobal_repr Hstore1).
              intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
            * exact Hstore2.
            * intro Heq2. exact (Hhb_ne_gb Heq2).
          + exact Hstore3.
          + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load3.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved through 3 stores *)
      { intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore3.
        eapply Mem.perm_store_1. exact Hstore2.
        eapply Mem.perm_store_1. exact Hstore1.
        apply Hsb_writable. exact Hofs'. }
    }
  }

Qed.
