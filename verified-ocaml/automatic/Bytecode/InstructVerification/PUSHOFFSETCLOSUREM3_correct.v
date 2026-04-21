(* PUSHOFFSETCLOSUREM3_correct.v -- PUSHOFFSETCLOSUREM3 = PUSH then OFFSETCLOSUREM3.

   C handler (f_instr_PUSHOFFSETCLOSUREM3):
     _t'4 = s->sp;                    // load sp
     _t'1 = (tptr tlong)(_t'4 - 1);   // new_sp = sp - 1
     s->sp = _t'1;                     // store 1: update sp field
     _t'3 = s->accu;                   // load accu
     *_t'1 = _t'3;                     // store 2: push accu onto stack
     _t'2 = s->env;                    // load env
     s->accu = _t'2 - 3*sizeof(long);  // store 3: set accu = env - 24
     return 0;

   Rocq (handle_PUSHOFFSETCLOSURE (-2)):
     let new_stack := accu :: stack in
     match env with
     | Val_closure addr base_ofs =>
         Step (accu := Val_closure addr (Z.to_nat (Z.of_nat base_ofs + (-2))),
               stack := new_stack)
     | Val_block t _ => Error  (* Z.eqb (-2) 0 = false *)
     | _ => Error
     end

   Three stores:
     Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v
     Store 3: accu field (sb, uso+8) <- result_v  (= env_long - 24)

   step_pre: sp_ofs >= 16 (room for push) + offsetclosurem2 precondition
     (env is Vlong, subtraction result has valid val_repr).
   No Axioms, no Admitted. *)

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
From OCamlInterp.Manual Require Import Bytecode.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

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

(* ================================================================== *)
(* Semantic lemmas for the env - 3*sizeof(long) computation            *)
(* ================================================================== *)

(* Inner Omul: 3 * sizeof(long) = 24, using Vptrofs form *)
Local Lemma sem_mul_3_sizeof : forall m,
  sem_binary_operation (genv_cenv ge) Omul
    (Vint (Int.repr 3)) tint
    (Vptrofs (Ptrofs.repr 8)) tulong m
  = Some (Vlong (Int64.repr 24)).
Proof. intros. reflexivity. Qed.

(* Outer Osub: Vlong - Vlong(24) *)
Local Lemma sem_sub_long_24 : forall n m,
  sem_binary_operation (genv_cenv ge) Osub
    (Vlong n) tlong (Vlong (Int64.repr 24)) tulong m
  = Some (Vlong (Int64.sub n (Int64.repr 24))).
Proof. intros. reflexivity. Qed.

(* Cast: tulong -> tlong for Vlong *)
Local Lemma sem_cast_tulong_tlong : forall n m,
  sem_cast (Vlong n) tulong tlong m = Some (Vlong n).
Proof. intros. reflexivity. Qed.

(* Bridge: Int64.sub x (repr 24) = Int64.add x (repr (-24)) *)
Local Lemma sub_24_eq_add_neg24 : forall x,
  Int64.sub x (Int64.repr 24) = Int64.add x (Int64.repr (-24)).
Proof.
  intros. rewrite Int64.sub_add_opp. f_equal.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_PUSHOFFSETCLOSUREM3_correct :
    handler_correct (handle_PUSHOFFSETCLOSURE (-2)) f_instr_PUSHOFFSETCLOSUREM3
      (sp_at_least 16 /\p closure_offset_pre (-2) (-24))
      (fun msg s =>
        (msg = "PUSHOFFSETCLOSURE: non-zero offset on non-closure env"%string /\
         match Machine.env s with Val_block _ _ => True | _ => False end) \/
        (msg = "PUSHOFFSETCLOSURE: invalid env"%string /\
         match Machine.env s with Val_closure _ _ | Val_block _ _ => False | _ => True end))
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_PUSHOFFSETCLOSURE.

  (* Case split on s.(env) *)
  destruct (Machine.env s) eqn:Henv_eq.

  (* ================================================================ *)
  (* Case 1: env = Val_int z => Error "invalid env"                    *)
  (* ================================================================ *)
  - right; exact (conj eq_refl I).

  (* ================================================================ *)
  (* Case 2: env = Val_block n l => Error "non-zero offset" (Z.eqb (-2) 0 = false) *)
  (* ================================================================ *)
  - left; exact (conj eq_refl I).

  (* ================================================================ *)
  (* Case 3: env = Val_ptr n => Error "invalid env"                    *)
  (* ================================================================ *)
  - right; exact (conj eq_refl I).

  (* ================================================================ *)
  (* Case 4: env = Val_closure n n0 => Step                            *)
  (* ================================================================ *)
  - simpl.
    intros ard Hpre Hstep_pre. unfold abs_rel_with_ard in Hpre.
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

    (* Extract preconditions *)
    unfold pre_and, sp_at_least, closure_offset_pre in Hstep_pre.
    rewrite Henv_eq in Hstep_pre.
    fold sb so hm in Hstep_pre.
    destruct Hstep_pre as [[sp_b' [sp_ofs' [Hsp_load' Hsp_ge16]]] [env_long [Henv_long_load Hresult_repr]]].
    simpl in Hsp_load'. fold sb so in Hsp_load'.

    (* Bridge: the generic precondition uses Int64.add with (-24),
       but C semantics produce Int64.sub with 24. *)
    rewrite <- sub_24_eq_add_neg24 in Hresult_repr.
    assert (sp_b' = sp_b /\ sp_ofs' = sp_ofs) as [-> ->]
      by (rewrite Hsp_load in Hsp_load'; injection Hsp_load'; auto).

    (* env_v = Vlong env_long (both load from same offset) *)
    assert (Henv_v_long : env_v = Vlong env_long).
    { rewrite Henv_long_load in Henv_load. congruence. }
    subst env_v.

    (* Rewrite env in Henv_repr *)
    rewrite Henv_eq in Henv_repr.

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.

    (* Composite environment facts *)
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
    destruct interp_state_co_env as [co_env [Hco_env [Henv_offset _]]].
    assert (co_env = co_is) as -> by congruence.

    (* New sp after push *)
    set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
    assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 8).
    { subst new_sp_ofs. unfold Ptrofs.sub.
      change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
      apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range sp_ofs).
      unfold Ptrofs.max_unsigned. lia. }

    (* Compute result value *)
    set (result_v := Vlong (Int64.sub env_long (Int64.repr 24))).

    (* Store 1: sp field <- new_sp *)
    destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) (Vptr sp_b new_sp_ofs)) as [m1 Hstore_sp].
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore_sp Hsb_writable) as Hsb_writable_m1.

    (* Store 2: *new_sp <- accu_v (different block from sb) *)
    assert (Halign_new : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs)).
    { rewrite Hnew_sp_unsigned. simpl align_chunk.
      apply Z.divide_sub_r. exact Hsp_align. exists 1; lia. }
    destruct (store_to_sp_after_sb_store m m1 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)
                sp_b (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s)))
                (Ptrofs.unsigned new_sp_ofs)
                Hstore_sp Hsp_writable
                ltac:(rewrite Hnew_sp_unsigned; lia)
                ltac:(rewrite Hnew_sp_unsigned; lia)
                Halign_new accu_v) as [m2 Hstore_accu].

    (* Store 3: accu field <- result_v *)
    assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
               (Ptrofs.unsigned so + 8) (Vptr sp_b new_sp_ofs) accu_v
               Hstore_sp Haccu_load). left. lia. }
    assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { erewrite Mem.load_store_other; [exact Haccu_load_m1 | exact Hstore_accu |].
      left. exact (not_eq_sym Hsp_ne_sb). }
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore_accu Hsb_writable_m1) as Hsb_writable_m2.

    (* env_v survives stores 1 and 2 *)
    assert (Henv_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
               (Ptrofs.unsigned so + 24) (Vptr sp_b new_sp_ofs) (Vlong env_long)
               Hstore_sp Henv_long_load). right. lia. }
    assert (Henv_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long)).
    { erewrite Mem.load_store_other; [exact Henv_load_m1 | exact Hstore_accu |].
      left. exact (not_eq_sym Hsp_ne_sb). }

    destruct (store_succeeds_sb m2 sb so 8 accu_v Hsb_writable_m2 Haccu_load_m2 ltac:(lia) ltac:(lia) result_v) as [m3 Hstore_result].

    (* Witnesses *)
    set (le' := PTree.set _t'2 (Vlong env_long)
                (PTree.set _t'3 accu_v
                (PTree.set _t'1 (Vptr sp_b new_sp_ofs)
                (PTree.set _t'4 (Vptr sp_b sp_ofs) le)))).
    exists le'. exists m3.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (* ============================================================== *)
    {
      apply (eval_stmt_to_exec clight_ge 15).
      eval_cbn.

      (* Statement 1: Sset _t'4 (s->sp) *)
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hsp_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      rewrite Hsp_load; eval_cbn.

      (* Statement 2: Sset _t'1 (cast (sub _t'4 1) (tptr tlong)) *)
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

      (* Statement 4: Sset _t'3 (s->accu) -- load accu from m1 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Haccu_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Haccu_load_m1; eval_cbn.

      (* Statement 5: Sassign (deref _t'1) _t'3 -- store accu to *new_sp *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Haccu_repr); eval_cbn.
      fold new_sp_ofs.
      rewrite Hstore_accu; eval_cbn.

      (* Statement 6: Sset _t'2 (s->env) -- load env from m2 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      eval_cbn.
      rewrite Henv_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
      rewrite Henv_load_m2; eval_cbn.

      (* Statement 7: Sassign (s->accu) (_t'2 - 3*sizeof(long)) *)
      (* Need to read _s for s->accu lvalue: gso past _t'2, _t'3, _t'1, _t'4 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      try rewrite Haccu_offset; eval_cbn.

      (* Evaluate _t'2 - 3*sizeof(long): read _t'2 *)
      try rewrite PTree.gss; eval_cbn.

      (* Inner mul: 3 * sizeof(long) = 24 *)
      rewrite sem_mul_3_sizeof; eval_cbn.

      (* Outer sub: env_long - 24 *)
      rewrite sem_sub_long_24; eval_cbn.

      (* Cast: tulong -> tlong *)
      rewrite sem_cast_tulong_tlong; eval_cbn.

      (* Store result to accu field *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      unfold result_v in Hstore_result.
      rewrite Hstore_result; eval_cbn.

      (* Statement 8: Sreturn 0 *)
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
        left. exact (not_eq_sym Hsp_ne_sb). }

      (* pc field: uso + 0 *)
      assert (Hpc_load3 : Mem.load Mint64 m3 sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 0)
                 result_v pc_ptr Hstore_result).
        - apply Hload_sb_m2.
          apply (load_after_store_other m m1 sb (uso + 16) (uso + 0)
                   (Vptr sp_b new_sp_ofs) pc_ptr Hstore_sp Hpc_load).
          left. lia.
        - left. lia. }

      (* accu field: uso + 8, overwritten by store 3 *)
      assert (Haccu_load3 : Mem.load Mint64 m3 sb (uso + 8) = Some result_v).
      { pose proof (load_after_store_same m2 m3 sb (uso + 8) result_v Hstore_result) as Htmp.
        unfold result_v in Htmp |- *.
        change (Val.load_result Mint64 (Vlong (Int64.sub env_long (Int64.repr 24))))
          with (Vlong (Int64.sub env_long (Int64.repr 24))) in Htmp.
        exact Htmp. }

      (* sp field: uso + 16, overwritten by store 1, survives stores 2 and 3 *)
      assert (Hsp_load3 : Mem.load Mint64 m3 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 16)
                 result_v (Vptr sp_b new_sp_ofs) Hstore_result).
        - apply Hload_sb_m2.
          pose proof (load_after_store_same m m1 sb (uso + 16)
                        (Vptr sp_b new_sp_ofs) Hstore_sp) as Htmp.
          simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp.
        - right. lia. }

      (* env field: uso + 24, unaffected by all 3 stores *)
      assert (Henv_load3 : Mem.load Mint64 m3 sb (uso + 24) = Some (Vlong env_long)).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 24)
                 result_v (Vlong env_long) Hstore_result).
        - apply Hload_sb_m2. exact Henv_load_m1.
        - right. lia. }

      (* extra_args field: uso + 32 *)
      assert (Hextra_load3 : Mem.load Mint64 m3 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 32)
                 result_v _ Hstore_result).
        - apply Hload_sb_m2.
          apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
                   (Vptr sp_b new_sp_ofs) _ Hstore_sp Hextra_load).
          right. lia.
        - right. lia. }

      (* global_data field: uso + 40 *)
      assert (Hgd_load3 : Mem.load Mint64 m3 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 40)
                 result_v gd_ptr Hstore_result).
        - apply Hload_sb_m2.
          apply (load_after_store_other m m1 sb (uso + 16) (uso + 40)
                   (Vptr sp_b new_sp_ofs) gd_ptr Hstore_sp Hgd_load).
          right. lia.
        - right. lia. }

      (* trap_sp field: uso + 48 *)
      assert (Hts_load3 : Mem.load Mint64 m3 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 48)
                 result_v ts_ptr Hstore_result).
        - apply Hload_sb_m2.
          apply (load_after_store_other m m1 sb (uso + 16) (uso + 48)
                   (Vptr sp_b new_sp_ofs) ts_ptr Hstore_sp Hts_load).
          right. lia.
        - right. lia. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field -- unchanged *)
      { exists pc_ptr. split.
        - exact Hpc_load3.
        - simpl. exact Hpc_rel. }

      (* 3. accu field -- updated to result_v (env - 24) *)
      { exists result_v. split.
        - exact Haccu_load3.
        - simpl. exact Hresult_repr. }

      (* 4. sp field -- updated to new_sp; stack gets accu prepended *)
      { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load3.
        - reflexivity.
        - simpl.
          assert (Hstack_m1 : stack_repr hm cb co m1 (Machine.stack s) sp_b sp_ofs).
          { apply (stack_repr_store_other_block hm cb co m m1 _ sp_b sp_ofs sb
                     (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)
                     Hstack_repr Hstore_sp).
            intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
          assert (Hstack_cons_m2 : stack_repr hm cb co m2 (Machine.accu s :: Machine.stack s) sp_b new_sp_ofs).
          { exact (stack_repr_cons_after_store hm cb co m1 m2
                     (Machine.stack s) sp_b sp_ofs (Machine.accu s) accu_v
                     Hstack_m1 Haccu_repr Hstore_accu Hsp_ge8 Hsp_rep). }
          apply (stack_repr_store_other_block hm cb co m2 m3 _ sp_b new_sp_ofs sb
                   (Ptrofs.unsigned so + 8) result_v
                   Hstack_cons_m2 Hstore_result).
                  intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - (* sp_ofs_ge8 for new sp *)
          rewrite Hnew_sp_unsigned. lia.
        - (* sp_rep *)
          simpl length. rewrite Nat2Z.inj_succ. rewrite Hnew_sp_unsigned. lia.
        - (* sp_writable *)
          simpl length. rewrite Nat2Z.inj_succ. rewrite Hnew_sp_unsigned.
          replace (Ptrofs.unsigned sp_ofs - 8 + 8 * Z.succ (Z.of_nat (length (Machine.stack s))))
            with (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) by lia.
          intros ofs' Hofs'.
          eapply Mem.perm_store_1. exact Hstore_result.
          eapply Mem.perm_store_1. exact Hstore_accu.
          eapply Mem.perm_store_1. exact Hstore_sp.
          apply Hsp_writable. exact Hofs'.
        - (* sp_aligned *)
          exact Halign_new. }

      (* 5. env field -- unchanged *)
      { exists (Vlong env_long). split.
        - exact Henv_load3.
        - simpl. rewrite Henv_eq. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { simpl. exact Hextra_load3. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load3.
        - simpl. exact Hgd_eq.
        - simpl.
          apply (global_repr_store_other_block hm cb co m2 m3 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sb (Ptrofs.unsigned so + 8) result_v).
          + apply (global_repr_store_other_block hm cb co m1 m2 _
                     (ar_global_block ard) (ar_global_ofs ard)
                     sp_b (Ptrofs.unsigned new_sp_ofs) accu_v).
            * apply (global_repr_store_other_block hm cb co m m1 _
                       (ar_global_block ard) (ar_global_ofs ard)
                       sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)
                       Hglobal_repr Hstore_sp).
              intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
            * exact Hstore_accu.
            * exact Hsp_ne_gb.
          + exact Hstore_result.
          + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load3.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable *)
      { intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore_result.
        eapply Mem.perm_store_1. exact Hstore_accu.
        eapply Mem.perm_store_1. exact Hstore_sp.
        apply Hsb_writable. exact Hofs'. }
    }
Qed.
