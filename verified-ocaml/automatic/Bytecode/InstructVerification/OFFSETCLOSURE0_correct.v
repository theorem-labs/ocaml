(* OFFSETCLOSURE0_correct.v -- OFFSETCLOSURE0 completeness proof using
   the computational evaluator from StepToBigstep.v.

   Proves that the C handler f_instr_OFFSETCLOSURE0 computes the same state
   transition as the Rocq handle_OFFSETCLOSURE 0 handler.

   OFFSETCLOSURE0 C code: _t'1 = s->env; s->accu = _t'1; return 0
   Rocq: handle_OFFSETCLOSURE 0 pc' s matches on s.(env):
     - Val_closure addr base_ofs => Step (accu := Val_closure addr base_ofs)
     - Val_block t _ => Step (accu := s.(env))
     - _ => Error

   In both Step cases the new accu is s.(env), which is represented by
   env_v in memory.  The C code simply copies env_v to the accu field.

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

(* Tactic for controlled reduction of the evaluator. *)
Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* Helper: in the Val_closure case, Z.to_nat (Z.of_nat n + 0) = n *)
Local Lemma offset_closure_0 : forall n,
  Z.to_nat (Z.of_nat n + 0) = n.
Proof. intros. rewrite Z.add_0_r. apply Nat2Z.id. Qed.

Theorem verify_OFFSETCLOSURE0_compl_comp :
    handler_correct (handle_OFFSETCLOSURE 0) f_instr_OFFSETCLOSURE0
      (fun _ _ _ _ => True)
      (fun msg s => msg = "OFFSETCLOSURE: invalid env"%string /\
        match Machine.env s with Val_closure _ _ | Val_block _ _ => False | _ => True end)
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_OFFSETCLOSURE.

  (* Case split on s.(env) *)
  destruct (Machine.env s) eqn:Henv_eq.

  (* ================================================================ *)
  (* Case: env = Val_int z => Error                                    *)
  (* ================================================================ *)
  - exact (conj eq_refl I).

  (* ================================================================ *)
  (* Case: env = Val_block n l => Step (Z.eqb 0 0 = true)            *)
  (* ================================================================ *)
  - simpl.
    (* The Step case *)
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

      (* Composite environment facts *)
      destruct interp_state_co_env as [co_is [Hco [Henv_offset Haccu_offset]]].

      (* Accu store must succeed *)
      destruct (store_succeeds_sb m sb so 8 accu_v Hsb_writable Haccu_load ltac:(lia) ltac:(lia) env_v)
        as [m' Hstore].

      (* Witnesses *)
      set (le' := PTree.set _t'1 env_v le).
      exists le'. exists m'.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* ============================================================== *)
      (* Part 1: exec via computational evaluator                        *)
      (*                                                                  *)
      (* OFFSETCLOSURE0 body:                                            *)
      (*   _t'1 = s->env                                                 *)
      (*   s->accu = _t'1                                                *)
      (*   return 0                                                       *)
      (* ============================================================== *)
      {
        apply (eval_stmt_to_exec clight_ge 10).

        (* --- Initial reduction --- *)
        eval_cbn.

        (* === Sset _t'1 (s->env) === *)
        rewrite Hle_s; eval_cbn.                                       (* le ! _s *)
        rewrite Hco; eval_cbn.                                         (* composite lookup *)
        rewrite Henv_offset; eval_cbn.                                 (* field_offset _env *)
        rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).     (* env ptrofs *)
        rewrite Henv_load; eval_cbn.                                   (* env field load *)

        (* === Sassign (s->accu = _t'1): lvalue === *)
        rewrite PTree.gso by (compute; congruence).                    (* le1 ! _s: skip _t'1 *)
        rewrite Hle_s; eval_cbn.                                       (* le ! _s *)

        (* For tlong env field, composite lookup and field_offset _env already reduced.
           Now evaluating Sassign lvalue for _accu field: *)
        rewrite Haccu_offset; eval_cbn.                                (* field_offset _accu *)

        (* === Sassign rvalue + sem_cast + store === *)
        rewrite PTree.gss; eval_cbn.                                   (* le1 ! _t'1 *)
        rewrite Henv_eq in Henv_repr.
        rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Henv_repr); eval_cbn.  (* sem_cast *)
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
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) env_v pc_ptr
                   Hstore Hpc_load). left. lia. }

        assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) env_v (Vptr sp_b sp_ofs)
                   Hstore Hsp_load). right. lia. }

        assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) env_v env_v
                   Hstore Henv_load). right. lia. }

        assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) env_v _
                   Hstore Hextra_load). right. lia. }

        assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) env_v gd_ptr
                   Hstore Hgd_load). right. lia. }

        assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) env_v ts_ptr
                   Hstore Hts_load). right. lia. }

        (* Rewrite Henv_repr for use in Part 2 *)
        rewrite Henv_eq in Henv_repr.

        assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some env_v).
        { pose proof (load_after_store_same m m' sb (uso + 8) env_v Hstore) as Htmp.
          rewrite (val_repr_load_result hm cb co _ env_v Henv_repr) in Htmp.
          exact Htmp. }

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

        (* 1. _s is in le' *)
        { subst le'.
          rewrite PTree.gso by (compute; congruence).
          exact Hle_s. }

        (* 2. pc field -- unchanged by handler *)
        { exists pc_ptr. split.
          - exact Hpc_load'.
          - simpl. exact Hpc_rel. }

        (* 3. accu field -- updated to env *)
        { exists env_v. split.
          - exact Haccu_load'.
          - simpl. exact Henv_repr. }

        (* 4. sp field -- unchanged *)
        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
          - exact Hsp_load'.
          - reflexivity.
          - simpl.
            apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) env_v
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
          - simpl. rewrite Henv_eq. exact Henv_repr. }

        (* 6. extra_args field -- unchanged *)
        { simpl. exact Hextra_load'. }

        (* 7. global_data field -- unchanged *)
        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd_load'.
          - simpl. exact Hgd_eq.
          - simpl.
            apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) env_v
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

  (* ================================================================ *)
  (* Case: env = Val_ptr n => Error                                    *)
  (* ================================================================ *)
  - exact (conj eq_refl I).

  (* ================================================================ *)
  (* Case: env = Val_closure n n0 => Step                              *)
  (* ================================================================ *)
  - simpl.
    (* The Step case *)
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

      (* Rewrite env in Henv_repr once up front *)
      rewrite Henv_eq in Henv_repr.

      (* Structural invariants *)
      pose proof (sptr_ofs_representable ard) as Hso_bound.
      fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
      pose proof (global_block_ne_sptr ard) as Hgb_ne.
      fold sb in Hgb_ne.

      (* Composite environment facts *)
      destruct interp_state_co_env as [co_is [Hco [Henv_offset Haccu_offset]]].

      (* Accu store must succeed *)
      destruct (store_succeeds_sb m sb so 8 accu_v Hsb_writable Haccu_load ltac:(lia) ltac:(lia) env_v)
        as [m' Hstore].

      (* Witnesses *)
      set (le' := PTree.set _t'1 env_v le).
      exists le'. exists m'.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      (* The post-state accu: Val_closure n (Z.to_nat (Z.of_nat n0 + 0)) = Val_closure n n0 *)
      rewrite offset_closure_0.

      split.

      (* ============================================================== *)
      (* Part 1: exec via computational evaluator                        *)
      (* ============================================================== *)
      {
        apply (eval_stmt_to_exec clight_ge 10).

        (* --- Initial reduction --- *)
        eval_cbn.

        (* === Sset _t'1 (s->env) === *)
        rewrite Hle_s; eval_cbn.                                       (* le ! _s *)
        rewrite Hco; eval_cbn.                                         (* composite lookup *)
        rewrite Henv_offset; eval_cbn.                                 (* field_offset _env *)
        rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).     (* env ptrofs *)
        rewrite Henv_load; eval_cbn.                                   (* env field load *)

        (* === Sassign (s->accu = _t'1): lvalue === *)
        rewrite PTree.gso by (compute; congruence).                    (* le1 ! _s: skip _t'1 *)
        rewrite Hle_s; eval_cbn.                                       (* le ! _s *)

        (* For tlong env field, composite lookup already resolved in first Efield.
           The Sassign lvalue introduces a new composite lookup: *)
        rewrite Haccu_offset; eval_cbn.                                (* field_offset _accu *)

        (* === Sassign rvalue + sem_cast + store === *)
        rewrite PTree.gss; eval_cbn.                                   (* le1 ! _t'1 *)
        rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Henv_repr); eval_cbn.  (* sem_cast *)
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
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) env_v pc_ptr
                   Hstore Hpc_load). left. lia. }

        assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) env_v (Vptr sp_b sp_ofs)
                   Hstore Hsp_load). right. lia. }

        assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) env_v env_v
                   Hstore Henv_load). right. lia. }

        assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) env_v _
                   Hstore Hextra_load). right. lia. }

        assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) env_v gd_ptr
                   Hstore Hgd_load). right. lia. }

        assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) env_v ts_ptr
                   Hstore Hts_load). right. lia. }

        assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some env_v).
        { pose proof (load_after_store_same m m' sb (uso + 8) env_v Hstore) as Htmp.
          rewrite (val_repr_load_result hm cb co _ env_v Henv_repr) in Htmp.
          exact Htmp. }

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

        (* 1. _s is in le' *)
        { subst le'.
          rewrite PTree.gso by (compute; congruence).
          exact Hle_s. }

        (* 2. pc field -- unchanged by handler *)
        { exists pc_ptr. split.
          - exact Hpc_load'.
          - simpl. exact Hpc_rel. }

        (* 3. accu field -- updated to env (Val_closure n n0) *)
        { exists env_v. split.
          - exact Haccu_load'.
          - simpl. exact Henv_repr. }

        (* 4. sp field -- unchanged *)
        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
          - exact Hsp_load'.
          - reflexivity.
          - simpl.
            apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) env_v
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
          - simpl. rewrite Henv_eq. exact Henv_repr. }

        (* 6. extra_args field -- unchanged *)
        { simpl. exact Hextra_load'. }

        (* 7. global_data field -- unchanged *)
        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd_load'.
          - simpl. exact Hgd_eq.
          - simpl.
            apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) env_v
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
