(* BOOLNOT_correct.v -- BOOLNOT completeness proof using
   the computational evaluator from StepToBigstep.v.

   BOOLNOT handler:
   - Rocq: handle_BOOLNOT pc' s matches accu:
       Val_int 0 => Step {pc:=pc', accu:=val_true}   (val_true = Val_int 1)
       _         => Step {pc:=pc', accu:=val_false}   (val_false = Val_int 0)

   - C (Clight AST): The handler body does:
       1. _t'1 = s->accu                          (read accu tagged int)
       2. s->accu = 4 - _t'1                      (tagged boolean negation)
       3. return 0

   Tagged integer arithmetic correspondence:
     val_repr (Val_int 0) = Vlong (Int64.repr 1)     -- tagged false
     val_repr (Val_int 1) = Vlong (Int64.repr 3)     -- tagged true
     C computes: 4 - 1 = 3 = val_repr (Val_int 1)   -- boolnot(false) = true
     C computes: 4 - 3 = 1 = val_repr (Val_int 0)   -- boolnot(true) = false

   Key differences from NEGINT:
   - Case split on accu = Val_int 0 vs Val_int 1 (boolean values only)
   - Arithmetic: 4 - tagged(n) rather than 2 - tagged(n)
   - The C handler is only correct for boolean inputs (Val_int 0 or Val_int 1)
   - The Rocq handler is defined for ALL inputs (maps non-zero to val_false)
     but C code 4 - (n*2+1) only equals tagged 0 when n=1.
   - Therefore we add a boolean precondition restricting accu to {0, 1}.

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
Require Import StepToBigstep.
Require Import HandlerLemmas.

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
(* Lemma: sem_sub on tint(4) - tlong = Int64.sub with sign extension  *)
(* ================================================================== *)

Lemma sem_sub_int_long_4 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vint (Int.repr 4)) tint
    (Vlong n) tlong
    m = Some (Vlong (Int64.sub (Int64.repr 4) n)).
Proof.
  intros. unfold sem_binary_operation, sem_sub.
  change (classify_sub tint tlong) with sub_default.
  unfold sem_binarith.
  change (classify_binarith tint tlong) with (bin_case_l Signed).
  simpl binarith_type.
  unfold sem_cast at 1. simpl classify_cast.
  simpl cast_int_long.
  change (Int.signed (Int.repr 4)) with 4%Z.
  unfold sem_cast at 1. simpl classify_cast.
  rewrite ptr64_true.
  reflexivity.
Qed.

(* ================================================================== *)
(* Lemma: tagged boolnot arithmetic for Val_int 0                      *)
(*   4 - 1 = 3 (tagged: Int64.sub (repr 4) (repr 1) = repr 3)        *)
(* ================================================================== *)

Lemma tagged_boolnot_arith_0 :
  Int64.sub (Int64.repr 4) (Int64.repr 1)
  = Int64.repr 3.
Proof.
  cut (Int64.unsigned (Int64.sub (Int64.repr 4) (Int64.repr 1))
       = Int64.unsigned (Int64.repr 3)).
  { intro H. rewrite <- (Int64.repr_unsigned (Int64.sub _ _)).
    rewrite H. apply Int64.repr_unsigned. }
  native_compute. reflexivity.
Qed.

(* ================================================================== *)
(* Lemma: tagged boolnot arithmetic for Val_int 1                      *)
(*   4 - 3 = 1 (tagged: Int64.sub (repr 4) (repr 3) = repr 1)        *)
(* ================================================================== *)

Lemma tagged_boolnot_arith_1 :
  Int64.sub (Int64.repr 4) (Int64.repr 3)
  = Int64.repr 1.
Proof.
  cut (Int64.unsigned (Int64.sub (Int64.repr 4) (Int64.repr 3))
       = Int64.unsigned (Int64.repr 1)).
  { intro H. rewrite <- (Int64.repr_unsigned (Int64.sub _ _)).
    rewrite H. apply Int64.repr_unsigned. }
  native_compute. reflexivity.
Qed.

(* ================================================================== *)
(* Lemma: load_result for Vlong is identity                            *)
(* ================================================================== *)

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof.
  intros. reflexivity.
Qed.

(* ================================================================== *)
(* Boolean precondition: accu is Val_int 0 or Val_int 1               *)
(* ================================================================== *)

Definition boolnot_precond (s : Machine.state) : Prop :=
  Machine.accu s = Val_int 0 \/ Machine.accu s = Val_int 1.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_BOOLNOT_correct :
  forall e le m s,
    match handle_BOOLNOT s.(pc) s with
    | Step s' =>
        boolnot_precond s ->
        abs_rel e le m s ->
        exists le' m' out,
          exec_stmt function_entry1 clight_ge e le m (fn_body f_instr_BOOLNOT) E0 le' m' out /\
          abs_rel e le' m' s'
    | Error msg => True
    | Halt v => False
    | CCall_request _ _ _ => False
    end.
Proof.
  intros e le m s.
  unfold handle_BOOLNOT.

  (* Case split on accu *)
  destruct (Machine.accu s) as [n | | | ] eqn:Haccu_eq.

  (* ================================================================ *)
  (* Case 1: accu = Val_int n                                          *)
  (* ================================================================ *)
  {
    destruct n as [| p | p] eqn:Hn.

    (* ============================================================== *)
    (* Case 1a: accu = Val_int 0 => Step with val_true = Val_int 1    *)
    (* ============================================================== *)
    {
      intros _Hbool Hpre.

      destruct Hpre as [ard Hpre]. unfold abs_rel_with_ard in Hpre.
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

      pose proof (sptr_ofs_representable ard) as Hso_bound.
      fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
      pose proof (global_block_ne_sptr ard) as Hgb_ne.
      fold sb in Hgb_ne.

      (* accu = Val_int 0, val_repr gives Vlong (Int64.repr 1) *)
      rewrite Haccu_eq in Haccu_repr.
      inversion Haccu_repr; subst accu_v.

      destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

      (* C result: 4 - 1 = 3 *)
      set (cv_result := Vlong (Int64.sub (Int64.repr 4) (Int64.repr 1))) in *.

      destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 8)
                  (Vlong (Int64.repr 1)) cv_result Haccu_load)
        as [m' Hstore].

      set (le' := PTree.set _t'1 (Vlong (Int64.repr 1)) le).
      exists le'. exists m'.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* Part 1: exec *)
      {
        apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.

        (* S1: Sset _t'1 = s->accu *)
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_load; eval_cbn.

        (* S2: s->accu = 4 - _t'1 *)
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite PTree.gss; eval_cbn.
        rewrite sem_sub_int_long_4; eval_cbn.
        rewrite sem_cast_long_vlong; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        fold cv_result.
        rewrite Hstore; eval_cbn.

        (* S3: return 0 *)
        subst le'. reflexivity.
      }

      (* Part 2: abs_rel for post-state *)
      {
        exists ard.
        set (uso := Ptrofs.unsigned so) in *.

        assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) cv_result pc_ptr
                   Hstore Hpc_load). left. lia. }

        assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) cv_result (Vptr sp_b sp_ofs)
                   Hstore Hsp_load). right. lia. }

        assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) cv_result env_v
                   Hstore Henv_load). right. lia. }

        assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) cv_result _
                   Hstore Hextra_load). right. lia. }

        assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) cv_result gd_ptr
                   Hstore Hgd_load). right. lia. }

        assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) cv_result ts_ptr
                   Hstore Hts_load). right. lia. }

        assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some cv_result).
        { pose proof (load_after_store_same m m' sb (uso + 8) cv_result Hstore) as Htmp.
          subst cv_result.
          rewrite load_result_vlong in Htmp.
          exact Htmp. }

        split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].

        { subst le'.
          rewrite PTree.gso by (compute; congruence).
          exact Hle_s. }

        { exists pc_ptr. split.
          - exact Hpc_load'.
          - simpl. exact Hpc_rel. }

        (* accu: cv_result = Vlong(4-1) = Vlong(3) = val_repr(Val_int 1) *)
        { exists cv_result. split.
          - exact Haccu_load'.
          - simpl. subst cv_result.
            rewrite tagged_boolnot_arith_0.
            constructor. }

        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
          split; [| split; [| split; [| split; [| split]]]].
          - exact Hsp_load'.
          - reflexivity.
          - simpl.
            apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb (uso + 8) cv_result
                     Hstack_repr Hstore).
                        intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          - exact Hsp_ne_sb.
          - exact Hsp_ne_gb.
          - exact Hcb_ne_sp. }

        { exists env_v. split.
          - exact Henv_load'.
          - simpl. exact Henv_repr. }

        { simpl. exact Hextra_load'. }

        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd_load'.
          - simpl. exact Hgd_eq.
          - simpl.
            apply (global_repr_store_other_block hm m m' _ _ _ sb (uso + 8) cv_result
                     Hglobal_repr Hstore).
                        intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          - exact Hgb_ne_sb. }

        { exists ts_ptr. split.
          - exact Hts_load'.
          - simpl. exact Htrap_rel. }
      }
    }

    (* ============================================================== *)
    (* Case 1b: accu = Val_int (Z.pos p) => Step with val_false       *)
    (* ============================================================== *)
    {
      intros Hbool Hpre.

      (* From boolnot_precond + accu = Val_int (Z.pos p): must be Val_int 1 *)
      destruct Hbool as [Hbool | Hbool];
        [rewrite Haccu_eq in Hbool; discriminate |].
      rewrite Haccu_eq in Hbool. injection Hbool as Hp.
      assert (Hp1 : p = xH) by lia. subst p.

      destruct Hpre as [ard Hpre]. unfold abs_rel_with_ard in Hpre.
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

      pose proof (sptr_ofs_representable ard) as Hso_bound.
      fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
      pose proof (global_block_ne_sptr ard) as Hgb_ne.
      fold sb in Hgb_ne.

      (* accu = Val_int 1, val_repr gives Vlong (Int64.repr 3) *)
      rewrite Haccu_eq in Haccu_repr.
      inversion Haccu_repr; subst accu_v.

      destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

      (* C result: 4 - 3 = 1 *)
      set (cv_result := Vlong (Int64.sub (Int64.repr 4) (Int64.repr 3))) in *.

      destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 8)
                  (Vlong (Int64.repr 3)) cv_result Haccu_load)
        as [m' Hstore].

      set (le' := PTree.set _t'1 (Vlong (Int64.repr 3)) le).
      exists le'. exists m'.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* Part 1: exec *)
      {
        apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.

        (* S1: Sset _t'1 = s->accu *)
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_load; eval_cbn.

        (* S2: s->accu = 4 - _t'1 *)
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite PTree.gss; eval_cbn.
        rewrite sem_sub_int_long_4; eval_cbn.
        rewrite sem_cast_long_vlong; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        fold cv_result.
        rewrite Hstore; eval_cbn.

        (* S3: return 0 *)
        subst le'. reflexivity.
      }

      (* Part 2: abs_rel for post-state *)
      {
        exists ard.
        set (uso := Ptrofs.unsigned so) in *.

        assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) cv_result pc_ptr
                   Hstore Hpc_load). left. lia. }

        assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) cv_result (Vptr sp_b sp_ofs)
                   Hstore Hsp_load). right. lia. }

        assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) cv_result env_v
                   Hstore Henv_load). right. lia. }

        assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) cv_result _
                   Hstore Hextra_load). right. lia. }

        assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) cv_result gd_ptr
                   Hstore Hgd_load). right. lia. }

        assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) cv_result ts_ptr
                   Hstore Hts_load). right. lia. }

        assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some cv_result).
        { pose proof (load_after_store_same m m' sb (uso + 8) cv_result Hstore) as Htmp.
          subst cv_result.
          rewrite load_result_vlong in Htmp.
          exact Htmp. }

        split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].

        { subst le'.
          rewrite PTree.gso by (compute; congruence).
          exact Hle_s. }

        { exists pc_ptr. split.
          - exact Hpc_load'.
          - simpl. exact Hpc_rel. }

        (* accu: cv_result = Vlong(4-3) = Vlong(1) = val_repr(Val_int 0) *)
        { exists cv_result. split.
          - exact Haccu_load'.
          - simpl. subst cv_result.
            rewrite tagged_boolnot_arith_1.
            constructor. }

        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
          split; [| split; [| split; [| split; [| split]]]].
          - exact Hsp_load'.
          - reflexivity.
          - simpl.
            apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb (uso + 8) cv_result
                     Hstack_repr Hstore).
                        intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          - exact Hsp_ne_sb.
          - exact Hsp_ne_gb.
          - exact Hcb_ne_sp. }

        { exists env_v. split.
          - exact Henv_load'.
          - simpl. exact Henv_repr. }

        { simpl. exact Hextra_load'. }

        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd_load'.
          - simpl. exact Hgd_eq.
          - simpl.
            apply (global_repr_store_other_block hm m m' _ _ _ sb (uso + 8) cv_result
                     Hglobal_repr Hstore).
                        intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          - exact Hgb_ne_sb. }

        { exists ts_ptr. split.
          - exact Hts_load'.
          - simpl. exact Htrap_rel. }
      }
    }

    (* ============================================================== *)
    (* Case 1c: accu = Val_int (Z.neg p) => excluded by precondition  *)
    (* ============================================================== *)
    {
      intros Hbool _Hpre.
      destruct Hbool as [Hbool | Hbool];
        rewrite Haccu_eq in Hbool; discriminate.
    }
  }

  (* ================================================================ *)
  (* Cases 2-4: non-integer accu => excluded by boolean precondition   *)
  (* ================================================================ *)
  all: intros Hbool _Hpre;
       destruct Hbool as [Hbool | Hbool];
       rewrite Haccu_eq in Hbool; discriminate.
Qed.
