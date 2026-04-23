(* ENVACC4_correct.v -- ENVACC4 correctness proof.

   ENVACC4: accu = Field(env, 4), i.e., load field 4 from the closure
   environment pointed to by env.

   C handler: t1 = s->env; t2 = deref((long ptr)t1 + 4); s->accu = t2; return 0;

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
From OCamlInterp.Manual Require Import Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
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

Lemma sem_cast_long_to_ptr_vptr_EA4 : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_add_ptr_long_4 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint (Int.repr 4)) tint m
    = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 32))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Definition env_field_loadable_4
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  forall v,
    field_or_heap s s.(Machine.env) 4 = Some v ->
    forall env_v,
      val_repr hm cb co s.(Machine.env) env_v ->
      exists b ofs cv,
        env_v = Vptr b ofs /\
        b <> sb /\
        Mem.load Mint64 m b
          (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat 4 * 8)))) = Some cv /\
        val_repr hm cb co v cv.

Theorem verify_ENVACC4_with_pre :
    handler_correct (handle_ENVACC 4) f_instr_ENVACC4
      env_field_loadable_4
      (fun _ s => field_or_heap s s.(Machine.env) 4 = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_ENVACC.
  destruct (field_or_heap s s.(Machine.env) 4) as [v|] eqn:Hfoh.

  2: { reflexivity. }
  {
    intros ard Hpre Hefl.

    destruct Hpre as (Hle_s &
      [pc_ptr [Hpc_load Hpc_rel]] &
      [accu_v [Haccu_load Haccu_repr]] &
      [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
      [env_v [Henv_load Henv_repr]] &
      Hextra_load &
      [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
      [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
    subst sp_ptr.

    set (sb := ar_sptr_block ard) in *.
    set (so := ar_sptr_ofs ard) in *.
    set (hm := ar_heap_map ard) in *.
    set (cb := ar_code_base_block ard) in *.
    set (co := ar_code_base_ofs ard) in *.

    pose proof (sptr_ofs_representable ard) as Hso_bound.
    fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].

    unfold env_field_loadable_4 in Hefl.
    destruct (Hefl v Hfoh env_v Henv_repr)
      as [b [ofs [cv [Henv_is_ptr [Hb_ne_sb [Hfield_load Hfield_repr]]]]]].
    change (Z.of_nat 4 * 8) with 32 in Hfield_load.
    subst env_v.

    destruct interp_state_co_env as [co_is [Hco [Henv_offset Haccu_offset]]].

    destruct (store_succeeds_sb m sb so 8 accu_v Hsb_writable Haccu_load ltac:(lia) ltac:(lia) cv) as [m' Hstore].

    set (le' := PTree.set _t'2 cv (PTree.set _t'1 (Vptr b ofs) le)).
    exists le'. exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* Part 1: exec *)
    {
      apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.

      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Henv_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
      rewrite Henv_load; eval_cbn.

      rewrite PTree.gss; eval_cbn.
      rewrite sem_cast_long_to_ptr_vptr_EA4; eval_cbn.
      rewrite (sem_add_ptr_long_4 b ofs m); eval_cbn.
      rewrite Hfield_load; eval_cbn.

      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Haccu_offset; eval_cbn.

      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hfield_repr); eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Hstore; eval_cbn.

      subst le'. reflexivity.
    }

    (* Part 2: abs_rel *)
    {
      exists ard.
      set (uso := Ptrofs.unsigned so) in *.

      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) cv pc_ptr
                 Hstore Hpc_load). left. lia. }

      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) cv (Vptr sp_b sp_ofs)
                 Hstore Hsp_load). right. lia. }

      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some (Vptr b ofs)).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) cv (Vptr b ofs)
                 Hstore Henv_load). right. lia. }

      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) cv _
                 Hstore Hextra_load). right. lia. }

      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) cv gd_ptr
                 Hstore Hgd_load). right. lia. }

      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) cv ts_ptr
                 Hstore Hts_load). right. lia. }

      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some cv).
      { pose proof (load_after_store_same m m' sb (uso + 8) cv Hstore) as Htmp.
        rewrite (val_repr_load_result hm cb co v cv Hfield_repr) in Htmp.
        exact Htmp. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      { exists pc_ptr. split. exact Hpc_load'. simpl. exact Hpc_rel. }

      { exists cv. split. exact Haccu_load'. simpl. exact Hfield_repr. }

      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load'.
        - reflexivity.
        - simpl.
          apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) cv
                   Hstack_repr Hstore).
          intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsp_writable. exact Hofs'.
        - exact Hsp_align. }

      { exists (Vptr b ofs). split. exact Henv_load'. simpl. exact Henv_repr. }

      { simpl. exact Hextra_load'. }

      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load'.
        - simpl. exact Hgd_eq.
        - simpl.
          apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) cv
                   Hglobal_repr Hstore).
          intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. }

      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsb_writable. exact Hofs'. }
    }
  }
Qed.
