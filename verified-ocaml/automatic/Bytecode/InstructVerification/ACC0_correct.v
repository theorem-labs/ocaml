(* ACC0_bigstep_compl_computational.v -- ACC0 completeness proof using
   the computational evaluator from StepToBigstep.v.

   Same theorem as ACC0_bigstep_compl_allresults.v, but Part 1
   (constructing the exec_stmt derivation) uses comp_eval_stmt +
   eval_stmt_to_exec instead of manual tactic construction.

   APPROACH:
   1. Prove comp_eval_stmt clight_ge 10 e le m body = Some (...)
      by interleaving [cbn -[...]] (reduces evaluator control flow) and
      [rewrite] (resolves abstract PTree lookups, memory loads, composite
      lookups, semantic operations, etc.)
   2. Apply eval_stmt_to_exec to obtain exec_stmt.
   3. Part 2 (abs_rel preservation) is identical to the allresults version.

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
From OCamlInterp.Manual Require Import Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.
Local Notation exec := (exec_stmt function_entry1 clight_ge).

(* Tactic for controlled reduction of the evaluator.
   cbn reduces: comp_eval_stmt/expr/lvalue, fn_body, typeof, access_mode,
   Mem.loadv/storev (Vptr dispatch), Eapp, match on option/outcome.
   cbn leaves alone (via -[...]): clight_ge (prevents expanding the 9000-line
   prog AST), genv_cenv (record projection), Mptr (opaque Archi.ptr64),
   sem_binary_operation/sem_cast (depend on ge or ptr64),
   Mem.load/store (abstract memory), Ptrofs arith (abstract offsets),
   field_offset (depends on ge), PTree.get/set (abstract temp_env). *)
Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

Theorem verify_ACC0_compl_comp :
    handler_correct (handle_ACC 0) f_instr_ACC0
      (fun _ _ _ _ => True)
      (fun _ s => s.(Machine.stack) = nil)
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_ACC. simpl nth_error.
  destruct (Machine.stack s) as [|v_hd v_tl] eqn:Hstk.

  (* ================================================================ *)
  (* Case 1: stack = nil => Error                                      *)
  (* ================================================================ *)
  { reflexivity. }

  (* ================================================================ *)
  (* Case 2: stack = v_hd :: v_tl => Step                              *)
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

    (* Extract stack head *)
    rewrite Hstk in Hstack_repr.
    inversion Hstack_repr as [| ? ? ? ? cv0 Hload_sp0 Hval_repr0 Hstack_repr_rest].

    (* Composite environment facts *)
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    (* Accu store must succeed *)
    destruct (store_succeeds_sb m sb so 8 accu_v Hsb_writable Haccu_load ltac:(lia) ltac:(lia) cv0)
      as [m' Hstore].

    (* Witnesses *)
    set (le' := PTree.set _t'2 cv0 (PTree.set _t'1 (Vptr sp_b sp_ofs) le)).
    exists le'. exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (*                                                                  *)
    (* Instead of manually constructing the exec_stmt derivation tree  *)
    (* with eapply, we prove comp_eval_stmt = Some (...) and apply     *)
    (* the soundness bridge eval_stmt_to_exec.                         *)
    (*                                                                  *)
    (* The rewrite chain mirrors the evaluator's execution path:       *)
    (* each [rewrite] resolves a stuck abstract term, and [eval_cbn]   *)
    (* reduces the evaluator until the next stuck point.               *)
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

      (* === Sset _t'2 : deref (sp + 0) === *)
      rewrite PTree.gss; eval_cbn.                                   (* le1 ! _t'1 *)
      rewrite sem_add_sp_0; eval_cbn.                                (* sp + 0 *)
      rewrite Hload_sp0; eval_cbn.                                   (* stack[0] load *)

      (* === Sassign (s->accu = _t'2): lvalue === *)
      rewrite PTree.gso by (compute; congruence).                    (* le2 ! _s: skip _t'2 *)
      rewrite PTree.gso by (compute; congruence).                    (* le2 ! _s: skip _t'1 *)
      rewrite Hle_s; eval_cbn.                                       (* le ! _s *)
      rewrite Haccu_offset; eval_cbn.                                (* field_offset _accu *)

      (* === Sassign rvalue + sem_cast + store === *)
      rewrite PTree.gss; eval_cbn.                                   (* le2 ! _t'2 *)
      rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hval_repr0); eval_cbn. (* sem_cast *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).      (* accu ptrofs *)
      rewrite Hstore; eval_cbn.                                      (* accu store *)

      (* === Sreturn 0 -- reduces automatically === *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* (identical to ACC0_bigstep_compl_allresults.v)                  *)
    (* ============================================================== *)
    {
      exists ard.
      set (uso := Ptrofs.unsigned so) in *.

      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) cv0 pc_ptr
                 Hstore Hpc_load). left. lia. }

      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) cv0 (Vptr sp_b sp_ofs)
                 Hstore Hsp_load). right. lia. }

      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) cv0 env_v
                 Hstore Henv_load). right. lia. }

      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) cv0 _
                 Hstore Hextra_load). right. lia. }

      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) cv0 gd_ptr
                 Hstore Hgd_load). right. lia. }

      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) cv0 ts_ptr
                 Hstore Hts_load). right. lia. }

      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some cv0).
      { pose proof (load_after_store_same m m' sb (uso + 8) cv0 Hstore) as Htmp.
        rewrite (val_repr_load_result hm cb co v_hd cv0 Hval_repr0) in Htmp.
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

      (* 3. accu field -- updated to stack head *)
      { exists cv0. split.
        - exact Haccu_load'.
        - simpl. exact Hval_repr0. }

      (* 4. sp field -- unchanged *)
      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load'.
        - reflexivity.
        - simpl. rewrite Hstk.
          apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) cv0
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
          apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) cv0
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
