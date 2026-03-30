(* ACC0_bigstep_compl_allresults.v -- Completeness for ACC0, all outcomes.
   Matches on handle_ACC 0 result:
   - Step s' => C code executes and abs_rel holds
   - Error _ => stack was nil (unconditional)
   - Halt _ / CCall_request _ _ _ => impossible (False)

   Uses abs_rel directly (no separate _pre relation).
   All lemmas/axioms imported from HandlerLemmas. *)

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
Require Import HandlerLemmas.

Local Notation ge := clight_ge.
Local Notation exec := (exec_stmt function_entry1 clight_ge).

(* ================================================================== *)
(* Access mode lemmas (trivially provable, not in HandlerLemmas)       *)
(* ================================================================== *)

Local Lemma access_mode_tlong : access_mode tlong = By_value Mint64.
Proof. reflexivity. Qed.

Local Lemma access_mode_tptr_tlong : access_mode (tptr tlong) = By_value Mint64.
Proof. simpl. rewrite Mptr_Mint64. reflexivity. Qed.

Local Lemma access_mode_tstruct : forall id a, access_mode (Tstruct id a) = By_copy.
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Main theorem: all outcomes                                          *)
(* ================================================================== *)

Theorem verify_ACC0_compl : forall e le m s,
    match handle_ACC 0 s.(pc) s with
    | Step s' =>
        abs_rel e le m s ->
        exists le' m' out,
          exec e le m f_instr_ACC0.(fn_body) E0 le' m' out /\
          abs_rel e le' m' s'
    | Error _ => s.(Machine.stack) = nil
    | Halt _ => False
    | CCall_request _ _ _ => False
    end.
Proof.
  intros e le m s.

  (* Case split on handle_ACC 0 *)
  unfold handle_ACC. simpl nth_error.
  destruct (Machine.stack s) as [|v_hd v_tl] eqn:Hstk.

  (* ================================================================ *)
  (* Case 1: stack = nil => Error "ACC: stack underflow"               *)
  (* ================================================================ *)
  { reflexivity. }

  (* ================================================================ *)
  (* Case 2: stack = v_hd :: v_tl => Step                              *)
  (* ================================================================ *)
  {
    (* Introduce the precondition now that we're in the Step case *)
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

    (* Get structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound.
    fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep.
    fold sb in Hblock_sep.
    pose proof (global_block_ne_sptr ard) as Hgb_ne.
    fold sb in Hgb_ne.

    (* Extract the head value from stack_repr *)
    rewrite Hstk in Hstack_repr.
    inversion Hstack_repr as [| ? ? ? ? cv0 Hload_sp0 Hval_repr0 Hstack_repr_rest].

    (* Get the composite for _interp_state *)
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    (* The accu store must succeed *)
    destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 8) accu_v cv0 Haccu_load)
      as [m' Hstore].

    (* Build the witnesses *)
    exists (PTree.set _t'2 cv0 (PTree.set _t'1 (Vptr sp_b sp_ofs) le)).
    exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: Construct exec derivation                               *)
    (* ============================================================== *)
    {
      simpl fn_body.

      (* E0 = E0 ** E0 for Ssequence traces *)
      change E0 with (E0 ** E0) at 1.

      (* Top Ssequence: inner_block ; return 0 *)
      eapply exec_Sseq_1.

      (* --- Inner block: Sset _t'1; (Sset _t'2; Sassign) --- *)
      change E0 with (E0 ** E0) at 1.
      eapply exec_Sseq_1.

      (* Statement 1: _t'1 = s->sp *)
      { eapply exec_Sset.
        eapply eval_Elvalue.
        - eapply eval_Efield_struct.
          + eapply eval_Elvalue.
            * eapply eval_Ederef. eapply eval_Etempvar. exact Hle_s.
            * eapply deref_loc_copy. apply access_mode_tstruct.
          + reflexivity.
          + exact Hco.
          + exact Hsp_offset.
        - eapply deref_loc_value.
          + exact access_mode_tptr_tlong.
          + simpl.
            rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
            exact Hsp_load.
      }

      (* Statements 2+3: Sset _t'2; Sassign *)
      change E0 with (E0 ** E0) at 1.
      eapply exec_Sseq_1.

      (* Statement 2: _t'2 = *(_t'1 + 0) *)
      { eapply exec_Sset.
        eapply eval_Elvalue.
        - eapply eval_Ederef.
          eapply eval_Ebinop.
          + eapply eval_Etempvar. apply PTree.gss.
          + eapply eval_Econst_int.
          + apply sem_add_sp_0.
        - eapply deref_loc_value.
          + exact access_mode_tlong.
          + simpl. exact Hload_sp0.
      }

      (* Statement 3: s->accu = _t'2 *)
      { eapply exec_Sassign.
        - eapply eval_Efield_struct.
          + eapply eval_Elvalue.
            * eapply eval_Ederef. eapply eval_Etempvar.
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gso by (compute; congruence).
              exact Hle_s.
            * eapply deref_loc_copy. apply access_mode_tstruct.
          + reflexivity.
          + exact Hco.
          + exact Haccu_offset.
        - eapply eval_Etempvar. apply PTree.gss.
        - apply (sem_cast_long_val_repr _ _ _ m Hval_repr0).
        - eapply assign_loc_value.
          + exact access_mode_tlong.
          + simpl.
            rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
            exact Hstore.
      }

      (* Statement 4: return 0 *)
      { eapply exec_Sreturn_some. eapply eval_Econst_int. }
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      exists ard.

      (* Prove field loads are preserved by the accu store *)
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
        rewrite (val_repr_load_result hm v_hd cv0 Hval_repr0) in Htmp.
        exact Htmp. }

      split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].

      (* 1. _s is in le' *)
      { rewrite PTree.gso by (compute; congruence).
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
        split; [| split].
        - exact Hsp_load'.
        - reflexivity.
        - simpl. rewrite Hstk.
          apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb (uso + 8) cv0
                   Hstack_repr Hstore).
          intro Heq; exact (Hblock_sep (eq_sym Heq)). }

      (* 5. env field -- unchanged *)
      { exists env_v. split.
        - exact Henv_load'.
        - simpl. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { simpl. exact Hextra_load'. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split].
        - exact Hgd_load'.
        - simpl. exact Hgd_eq.
        - simpl.
          apply (global_repr_store_other_block hm m m' _ _ _ sb (uso + 8) cv0
                   Hglobal_repr Hstore).
          intro Heq2; exact (Hgb_ne (eq_sym Heq2)). }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load'.
        - simpl. exact Htrap_rel. }
    }
  }
Qed.
