(* OFFSETCLOSURE2_correct.v -- OFFSETCLOSURE2 completeness proof.

   Proves that the C handler f_instr_OFFSETCLOSURE2 computes the same state
   transition as the Rocq handle_OFFSETCLOSURE 2 handler.

   OFFSETCLOSURE2 C code:
     _t'1 = s->env;
     s->accu = _t'1 + 3 * sizeof(long);   // env + 24 bytes
     return 0

   Rocq: handle_OFFSETCLOSURE 2 pc' s matches on s.(env):
     - Val_int z => Error
     - Val_block t _ => Error  (Z.eqb 2 0 = false)
     - Val_ptr n => Error
     - Val_closure addr base_ofs => Step (accu := Val_closure addr (base_ofs + 2))

   The C code performs integer addition (tlong + tulong) on the env value.
   CompCert's sem_binarith does not support Vptr for integer addition, so
   we require a step_pre asserting the env value is represented as Vlong
   (a flat integer encoding of the closure pointer) rather than Vptr.
   The precondition also requires that the result of addition gives a
   valid val_repr for the new closure.

   No Axioms, no Admitted. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.InstructSpec.
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

(* ================================================================== *)
(* Semantic lemmas for the OFFSETCLOSURE2 body                         *)
(* ================================================================== *)

(* Inner Omul: 3 * sizeof(long) = 24, using Vptrofs form *)
Local Lemma sem_mul_3_sizeof : forall m,
  sem_binary_operation (genv_cenv ge) Omul
    (Vint (Int.repr 3)) tint
    (Vptrofs (Ptrofs.repr 8)) tulong m
  = Some (Vlong (Int64.repr 24)).
Proof. intros. reflexivity. Qed.

(* Outer Oadd: Vlong + Vlong(24) *)
Local Lemma sem_add_long_24 : forall n m,
  sem_binary_operation (genv_cenv ge) Oadd
    (Vlong n) tlong (Vlong (Int64.repr 24)) tulong m
  = Some (Vlong (Int64.add n (Int64.repr 24))).
Proof. intros. reflexivity. Qed.

(* Cast: tulong -> tlong for Vlong *)
Local Lemma sem_cast_tulong_tlong : forall n m,
  sem_cast (Vlong n) tulong tlong m = Some (Vlong n).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_OFFSETCLOSURE2_compl_comp :
    handler_correct (handle_OFFSETCLOSURE 2) f_instr_OFFSETCLOSURE2
      (closure_offset_pre 2 24)
      (fun msg s =>
        (msg = "OFFSETCLOSURE: non-zero offset on non-closure env"%string /\
         match Machine.env s with Val_block _ _ => True | _ => False end) \/
        (msg = "OFFSETCLOSURE: invalid env"%string /\
         match Machine.env s with Val_closure _ _ | Val_block _ _ => False | _ => True end))
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_OFFSETCLOSURE.

  (* Case split on s.(env) — value has 4 constructors *)
  destruct (Machine.env s) eqn:Henv_eq.

  (* ================================================================ *)
  (* Case 1: env = Val_int z => Error "invalid env"                    *)
  (* ================================================================ *)
  - right; exact (conj eq_refl I).

  (* ================================================================ *)
  (* Case 2: env = Val_block n l => Error "non-zero offset" (Z.eqb 2 0 = false) *)
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
    {
      intros ard Hpre Hstep_pre.
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

      (* Extract the closure precondition *)
      unfold closure_offset_pre in Hstep_pre.
      rewrite Henv_eq in Hstep_pre.
      fold sb so hm in Hstep_pre.
      destruct Hstep_pre as [env_long [Henv_long_load Hresult_repr]].

      (* env_v = Vlong env_long (both load from same offset) *)
      assert (Henv_v_long : env_v = Vlong env_long).
      { rewrite Henv_long_load in Henv_load. congruence. }
      subst env_v.

      (* Structural invariants *)
      pose proof (sptr_ofs_representable ard) as Hso_bound.
      fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
      pose proof (global_block_ne_sptr ard) as Hgb_ne.
      fold sb in Hgb_ne.

      (* Composite environment facts *)
      destruct interp_state_co_env as [co_is [Hco [Henv_offset Haccu_offset]]].

      (* Compute result value *)
      set (result_v := Vlong (Int64.add env_long (Int64.repr 24))).

      (* Accu store must succeed *)
      destruct (store_succeeds_sb m sb so 8 accu_v Hsb_writable Haccu_load ltac:(lia) ltac:(lia) result_v)
        as [m' Hstore].

      (* Witnesses *)
      set (le' := PTree.set _t'1 (Vlong env_long) le).
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

        (* === Sset _t'1 (s->env) === *)
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Henv_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
        rewrite Henv_long_load; eval_cbn.

        (* === Sassign lvalue: s->accu === *)
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Haccu_offset; eval_cbn.

        (* === Sassign rvalue: _t'1 + 3*sizeof(long) === *)
        rewrite PTree.gss; eval_cbn.

        (* Inner mul: 3 * sizeof(long) = 24 *)
        rewrite sem_mul_3_sizeof; eval_cbn.

        (* Outer add: env_long + 24 *)
        rewrite sem_add_long_24; eval_cbn.

        (* Cast: tulong -> tlong *)
        rewrite sem_cast_tulong_tlong; eval_cbn.

        (* Store result to accu *)
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        unfold result_v in Hstore.
        rewrite Hstore; eval_cbn.

        (* === Sreturn 0 === *)
        subst le'. reflexivity.
      }

      (* ============================================================== *)
      (* Part 2: abs_rel for post-state                                  *)
      (* ============================================================== *)
      {
        exists ard.
        set (uso := Ptrofs.unsigned so) in *.

        assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) result_v pc_ptr
                   Hstore Hpc_load). left. lia. }

        assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) result_v (Vptr sp_b sp_ofs)
                   Hstore Hsp_load). right. lia. }

        assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some (Vlong env_long)).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) result_v (Vlong env_long)
                   Hstore Henv_long_load). right. lia. }

        assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) result_v _
                   Hstore Hextra_load). right. lia. }

        assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) result_v gd_ptr
                   Hstore Hgd_load). right. lia. }

        assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) result_v ts_ptr
                   Hstore Hts_load). right. lia. }

        assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some result_v).
        { pose proof (load_after_store_same m m' sb (uso + 8) result_v Hstore) as Htmp.
          unfold result_v in Htmp |- *.
          change (Val.load_result Mint64 (Vlong (Int64.add env_long (Int64.repr 24))))
            with (Vlong (Int64.add env_long (Int64.repr 24))) in Htmp.
          exact Htmp. }

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

        (* 1. _s is in le' *)
        { subst le'.
          rewrite PTree.gso by (compute; congruence).
          exact Hle_s. }

        (* 2. pc field -- unchanged *)
        { exists pc_ptr. split.
          - exact Hpc_load'.
          - simpl. exact Hpc_rel. }

        (* 3. accu field -- updated to result *)
        { exists result_v. split.
          - exact Haccu_load'.
          - simpl. exact Hresult_repr. }

        (* 4. sp field -- unchanged *)
        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
          - exact Hsp_load'.
          - reflexivity.
          - simpl.
            apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) result_v
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
        { exists (Vlong env_long). split.
          - exact Henv_load'.
          - simpl. rewrite Henv_eq. rewrite Henv_eq in Henv_repr. exact Henv_repr. }

        (* 6. extra_args field -- unchanged *)
        { simpl. exact Hextra_load'. }

        (* 7. global_data field -- unchanged *)
        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd_load'.
          - simpl. exact Hgd_eq.
          - simpl.
            apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) result_v
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
