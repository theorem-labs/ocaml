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

#[warnings="-not-a-closed-proof"]
Theorem verify_BOOLNOT_correct :
  forall e le m s,
    match handle_BOOLNOT s.(pc) s with
    | Step s' =>
        boolnot_precond s ->
        forall ard,
        abs_rel_with_ard e le m s ard ->
        accu_is_long e m s ard ->
        exists le' m' out,
          exec_stmt function_entry1 clight_ge e le m (fn_body f_instr_BOOLNOT) E0 le' m' out /\
          abs_rel e le' m' s'
    | Error msg => False
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
      intros _Hbool ard Hpre Haccu_long.

      unfold accu_is_long in Haccu_long.
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

      pose proof (sptr_ofs_representable ard) as Hso_bound.
      fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
      pose proof (global_block_ne_sptr ard) as Hgb_ne.
      fold sb in Hgb_ne.

      (* accu = Val_int 0, val_repr gives Vlong (Int64.repr 1) *)
      pose proof Haccu_repr as Haccu_repr_rw.
      rewrite Haccu_eq in Haccu_repr.
      inversion Haccu_repr; subst accu_v.
      2: { exfalso.
           destruct (Haccu_long _ Haccu_repr_rw) as [z Hz]. discriminate Hz. }

      destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

      (* C result: 4 - 1 = 3 *)
      set (cv_result := Vlong (Int64.sub (Int64.repr 4) (Int64.repr 1))) in *.

      destruct (store_succeeds_sb m sb so 8 (Vlong (Int64.repr 1)) Hsb_writable Haccu_load ltac:(lia) ltac:(lia) cv_result)
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

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

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
            apply vr_int. }

        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
          - exact Hsp_load'.
          - reflexivity.
          - simpl.
            apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) cv_result
                     Hstack_repr Hstore).
                        intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          - exact Hsp_ne_sb.
          - exact Hsp_ne_gb.
          - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsp_writable. exact Hofs'. 
        - exact Hsp_align. }

        { exists env_v. split.
          - exact Henv_load'.
          - simpl. exact Henv_repr. }

        { simpl. exact Hextra_load'. }

        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd_load'.
          - simpl. exact Hgd_eq.
          - simpl.
            apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) cv_result
                     Hglobal_repr Hstore).
                        intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          - exact Hgb_ne_sb. }

        { exists ts_ptr. split.
          - exact Hts_load'.
          - simpl. exact Htrap_rel. }

        (* 9. sb_writable -- permission preserved *)
        { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsb_writable. exact Hofs'. }
      }
    }

    (* ============================================================== *)
    (* Case 1b: accu = Val_int (Z.pos p) => Step with val_false       *)
    (* ============================================================== *)
    {
      intros Hbool ard Hpre Haccu_long.

      (* From boolnot_precond + accu = Val_int (Z.pos p): must be Val_int 1 *)
      destruct Hbool as [Hbool | Hbool];
        [rewrite Haccu_eq in Hbool; discriminate |].
      rewrite Haccu_eq in Hbool. injection Hbool as Hp.
      assert (Hp1 : p = xH) by lia. subst p.

      unfold accu_is_long in Haccu_long.
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

      pose proof (sptr_ofs_representable ard) as Hso_bound.
      fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
      pose proof (global_block_ne_sptr ard) as Hgb_ne.
      fold sb in Hgb_ne.

      (* accu = Val_int 1, val_repr gives Vlong (Int64.repr 3) *)
      pose proof Haccu_repr as Haccu_repr_rw.
      rewrite Haccu_eq in Haccu_repr.
      inversion Haccu_repr; subst accu_v.
      2: { exfalso.
           destruct (Haccu_long _ Haccu_repr_rw) as [z Hz]. discriminate Hz. }

      destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

      (* C result: 4 - 3 = 1 *)
      set (cv_result := Vlong (Int64.sub (Int64.repr 4) (Int64.repr 3))) in *.

      destruct (store_succeeds_sb m sb so 8 (Vlong (Int64.repr 3)) Hsb_writable Haccu_load ltac:(lia) ltac:(lia) cv_result)
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

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

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
            apply vr_int. }

        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
          - exact Hsp_load'.
          - reflexivity.
          - simpl.
            apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) cv_result
                     Hstack_repr Hstore).
                        intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          - exact Hsp_ne_sb.
          - exact Hsp_ne_gb.
          - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsp_writable. exact Hofs'. 
        - exact Hsp_align. }

        { exists env_v. split.
          - exact Henv_load'.
          - simpl. exact Henv_repr. }

        { simpl. exact Hextra_load'. }

        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd_load'.
          - simpl. exact Hgd_eq.
          - simpl.
            apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) cv_result
                     Hglobal_repr Hstore).
                        intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          - exact Hgb_ne_sb. }

        { exists ts_ptr. split.
          - exact Hts_load'.
          - simpl. exact Htrap_rel. }

        (* 9. sb_writable -- permission preserved *)
        { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsb_writable. exact Hofs'. }
      }
    }

    (* ============================================================== *)
    (* Case 1c: accu = Val_int (Z.neg p) => excluded by precondition  *)
    (* ============================================================== *)
    {
      intros Hbool _ _ _.
      destruct Hbool as [Hbool | Hbool];
        rewrite Haccu_eq in Hbool; discriminate.
    }
  }

  (* ================================================================ *)
  (* Cases 2-4: non-integer accu => excluded by boolean precondition   *)
  (* ================================================================ *)
  all: intros Hbool _ _ _;
       destruct Hbool as [Hbool | Hbool];
       rewrite Haccu_eq in Hbool; discriminate.
Qed.

Local Lemma exec_Sset_is_normal : forall e le m id a t le' m' out,
  exec_stmt function_entry1 clight_ge e le m (Sset id a) t le' m' out ->
  out = Out_normal.
Proof. intros. inversion H; subst; reflexivity. Qed.

Local Lemma exec_Sassign_is_normal : forall e le m a1 a2 t le' m' out,
  exec_stmt function_entry1 clight_ge e le m (Sassign a1 a2) t le' m' out ->
  out = Out_normal.
Proof. intros. inversion H; subst; reflexivity. Qed.

Local Lemma eval_expr_Econst_int_inv : forall e le m n ty v,
  eval_expr clight_ge e le m (Econst_int n ty) v ->
  v = Vint n.
Proof.
  intros e le m n ty v Hev.
  inversion Hev; subst; [reflexivity|].
  match goal with H : eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ =>
    inversion H
  end.
Qed.

Local Lemma exec_Sreturn_const_int : forall e le m n t le' m' out,
  exec_stmt function_entry1 clight_ge e le m
    (Sreturn (Some (Econst_int n tint))) t le' m' out ->
  out = Out_return (Some (Vint n, tint)).
Proof.
  intros. inversion H; subst.
  match goal with He : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply eval_expr_Econst_int_inv in He
  end.
  subst. reflexivity.
Qed.

Local Lemma exec_Sseq_normal_first : forall e le m s1 s2 t le' m' out,
  exec_stmt function_entry1 clight_ge e le m (Ssequence s1 s2) t le' m' out ->
  (forall t' le0 m0 out0,
    exec_stmt function_entry1 clight_ge e le m s1 t' le0 m0 out0 ->
    out0 = Out_normal) ->
  exists t1 le1 m1 t2,
    exec_stmt function_entry1 clight_ge e le m s1 t1 le1 m1 Out_normal /\
    exec_stmt function_entry1 clight_ge e le1 m1 s2 t2 le' m' out.
Proof.
  intros e le m s1 s2 t le' m' out Hseq Hs1_normal.
  remember (Ssequence s1 s2) as stmt eqn:Hstmt.
  destruct Hseq; try (inversion Hstmt; fail).
  - inversion Hstmt; subst. eauto 8.
  - inversion Hstmt; subst.
    specialize (Hs1_normal _ _ _ _ Hseq).
    contradiction.
Qed.

Local Lemma BOOLNOT_body_outcome : forall e le m t le' m' out,
  exec_stmt function_entry1 clight_ge e le m (fn_body f_instr_BOOLNOT)
    t le' m' out ->
  out = Out_return (Some (Vint (Int.repr 0), tint)).
Proof.
  intros e le m t le' m' out Hexec.
  cbn [fn_body f_instr_BOOLNOT] in Hexec.
  apply exec_Sseq_normal_first in Hexec.
  2:{ intros t' le0 m0 out0 HA.
      apply exec_Sseq_normal_first in HA.
      2:{ intros. eapply exec_Sset_is_normal; eauto. }
      destruct HA as [? [? [? [? [_ HAssign]]]]].
      eapply exec_Sassign_is_normal; eauto. }
  destruct Hexec as [? [? [? [? [_ HRet]]]]].
  eapply exec_Sreturn_const_int; eauto.
Qed.

(* Wrapper: convert to handler_correct form for the Module Type. *)
Theorem verify_BOOLNOT_handler_correct :
    handler_correct handle_BOOLNOT f_instr_BOOLNOT
      (fun _ => None)
      (pre_and accu_is_bool accu_is_long)
      (fun _ => None) (fun _ => None).
Proof.
  unfold handler_correct, handler_correct_gen.
  intros e le m s.
  specialize (verify_BOOLNOT_correct e le m s) as H.
  unfold handle_BOOLNOT in H |- *.
  destruct (Machine.accu s) as [n| | |] eqn:Haccu; try solve
    [ intros ard Hrel Hpre;
      destruct Hpre as [Hbool Hlong];
      destruct (H Hbool ard Hrel Hlong) as [le' [m' [out [Hexec Habs]]]];
      exists le', m'; split;
      [ unfold clight_returns; rewrite (BOOLNOT_body_outcome _ _ _ _ _ _ _ Hexec) in Hexec; exact Hexec
      | unfold R_ex; exact Habs ] ].
  destruct n;
    (intros ard Hrel Hpre;
     destruct Hpre as [Hbool Hlong];
     destruct (H Hbool ard Hrel Hlong) as [le' [m' [out [Hexec Habs]]]];
     exists le', m'; split;
     [ unfold clight_returns; rewrite (BOOLNOT_body_outcome _ _ _ _ _ _ _ Hexec) in Hexec; exact Hexec
     | unfold R_ex; exact Habs ]).
Qed.

(* Final wrapper with the exact type expected by InstructVerificationProof.v. *)
Definition correct_BOOLNOT :
    handler_correct (handle_instr Bytecode.AST.BOOLNOT) (clight_of Bytecode.AST.BOOLNOT)
      (error_message_of Bytecode.AST.BOOLNOT)
      (pre_of Bytecode.AST.BOOLNOT) (P_halt_of Bytecode.AST.BOOLNOT) (P_ccall_of Bytecode.AST.BOOLNOT).
Proof.
(* Abandoned for this pass: [verify_BOOLNOT_handler_correct] is closed under
   the semantic precondition [pre_and accu_is_bool accu_is_long].  The canonical
   [pre_of BOOLNOT] is the generic Clight-body executability condition and is
   not convertible to that boolean accumulator precondition, so this wrapper
   needs a separate weakening/strengthening argument. *)
Admitted.
