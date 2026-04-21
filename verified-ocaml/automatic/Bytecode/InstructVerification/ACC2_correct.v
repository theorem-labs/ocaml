(* ACC2_correct.v -- ACC2 completeness proof using the computational
   evaluator from StepToBigstep.v.

   ACC2 is identical to ACC0 except it accesses stack[2] instead of
   stack[0].  The C code reads *(sp + 2) which adds 16 bytes (2 * sizeof(long)).

   Uses abs_rel directly (no separate _pre relation).
   All lemmas/axioms imported from HandlerLemmas. *)

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

(* ================================================================== *)
(* Local pointer arithmetic lemma: sp + 2 = sp + 16 bytes             *)
(* ================================================================== *)

Local Lemma sem_add_sp_2 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 2)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Theorem verify_ACC2 :
    handler_correct (handle_ACC 2) f_instr_ACC2
      (fun _ _ _ _ => True)
      (fun _ s => nth_error s.(Machine.stack) 2 = None) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_ACC. simpl nth_error.

  (* Destruct stack to depth 3 *)
  destruct (Machine.stack s) as [|v0 stk0] eqn:Hstk.

  (* ================================================================ *)
  (* Case 1: stack = nil => Error                                      *)
  (* ================================================================ *)
  { reflexivity. }

  destruct stk0 as [|v1 stk1].

  (* ================================================================ *)
  (* Case 2: stack = v0 :: nil => Error                                *)
  (* ================================================================ *)
  { reflexivity. }

  destruct stk1 as [|v2 rest].

  (* ================================================================ *)
  (* Case 3: stack = v0 :: v1 :: nil => Error                          *)
  (* ================================================================ *)
  { reflexivity. }

  (* ================================================================ *)
  (* Case 4: stack = v0 :: v1 :: v2 :: rest => Step                    *)
  (* ================================================================ *)
  {
    intros ard Hpre _. unfold abs_rel_with_ard in Hpre.
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

    (* Invert stack_repr three times to get the third element.
       Use targeted subst to avoid clobbering gd_ptr etc. *)
    rewrite Hstk in Hstack_repr.
    inversion Hstack_repr as [| xv0 xvs0 xb0 xofs0 cv0 Hload_sp0 Hval_repr0 Hstack_repr1].
    subst xv0 xvs0 xb0 xofs0.
    inversion Hstack_repr1 as [| xv1 xvs1 xb1 xofs1 cv1 Hload_sp1 Hval_repr1 Hstack_repr2].
    subst xv1 xvs1 xb1 xofs1.
    inversion Hstack_repr2 as [| xv2 xvs2 xb2 xofs2 cv2 Hload_sp2 Hval_repr2 Hstack_repr_rest].
    subst xv2 xvs2 xb2 xofs2.

    (* Relate the twice-advanced sp offset to sp_ofs + 16.
       stack_repr inversions produce:
         Hload_sp2 : Mem.load ... sp_b (Ptrofs.unsigned (Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8))) = Some cv2
       We need it in terms of Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 16)). *)
    assert (Hofs_eq : Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8)
                    = Ptrofs.add sp_ofs (Ptrofs.repr 16)).
    { rewrite Ptrofs.add_assoc. reflexivity. }
    rewrite Hofs_eq in Hload_sp2.

    (* Composite environment facts *)
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    (* Accu store must succeed *)
    destruct (store_succeeds_sb m sb so 8 accu_v Hsb_writable Haccu_load ltac:(lia) ltac:(lia) cv2)
      as [m' Hstore].

    (* Witnesses *)
    set (le' := PTree.set _t'2 cv2 (PTree.set _t'1 (Vptr sp_b sp_ofs) le)).
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

      (* === Sset _t'2 : deref (sp + 2) === *)
      rewrite PTree.gss; eval_cbn.                                   (* le1 ! _t'1 *)
      rewrite sem_add_sp_2; eval_cbn.                                (* sp + 2 = sp + 16 bytes *)
      rewrite Hload_sp2; eval_cbn.                                   (* stack[2] load *)

      (* === Sassign (s->accu = _t'2): lvalue === *)
      rewrite PTree.gso by (compute; congruence).                    (* le2 ! _s: skip _t'2 *)
      rewrite PTree.gso by (compute; congruence).                    (* le2 ! _s: skip _t'1 *)
      rewrite Hle_s; eval_cbn.                                       (* le ! _s *)
      rewrite Haccu_offset; eval_cbn.                                (* field_offset _accu *)

      (* === Sassign rvalue + sem_cast + store === *)
      rewrite PTree.gss; eval_cbn.                                   (* le2 ! _t'2 *)
      rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hval_repr2); eval_cbn. (* sem_cast *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).      (* accu ptrofs *)
      rewrite Hstore; eval_cbn.                                      (* accu store *)

      (* === Sreturn 0 -- reduces automatically === *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      exists ard.
      set (uso := Ptrofs.unsigned so) in *.

      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) cv2 pc_ptr
                 Hstore Hpc_load). left. lia. }

      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) cv2 (Vptr sp_b sp_ofs)
                 Hstore Hsp_load). right. lia. }

      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) cv2 env_v
                 Hstore Henv_load). right. lia. }

      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) cv2 _
                 Hstore Hextra_load). right. lia. }

      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) cv2 gd_ptr
                 Hstore Hgd_load). right. lia. }

      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) cv2 ts_ptr
                 Hstore Hts_load). right. lia. }

      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some cv2).
      { pose proof (load_after_store_same m m' sb (uso + 8) cv2 Hstore) as Htmp.
        rewrite (val_repr_load_result hm cb co v2 cv2 Hval_repr2) in Htmp.
        exact Htmp. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field -- unchanged by handler *)
      { exists pc_ptr. split.
        - exact Hpc_load'.
        - simpl. exact Hpc_rel. }

      (* 3. accu field -- updated to stack[2] *)
      { exists cv2. split.
        - exact Haccu_load'.
        - simpl. exact Hval_repr2. }

      (* 4. sp field -- unchanged *)
      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load'.
        - reflexivity.
        - simpl. rewrite Hstk.
          apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) cv2
                   Hstack_repr Hstore).
                    intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsp_writable. exact Hofs'. 
        - exact Hsp_align. }

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
          apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) cv2
                   Hglobal_repr Hstore).
                    intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load'.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved *)
      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsb_writable. exact Hofs'. }
    }
  }
Qed.
