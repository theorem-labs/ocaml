(* BRANCHIF_correct.v -- BRANCHIF handler completeness proof.

   BRANCHIF handler:
   - Rocq: handle_BRANCHIF target pc' s matches accu:
       Val_int 0 => Step {pc := pc'}        (fall through; pc' = s.pc)
       _         => Step {pc := target}      (branch taken)

   - C (Clight AST): The handler body does:
       1. _t'1 = s->accu                   (read accu, tlong)
       2. if (_t'1 != ((0 << 1) + 1))      (test accu != tagged(0) = 1)
          THEN (branch taken):
            _t'3 = s->pc
            _t'4 = s->pc
            _t'5 = *_t'4                    (read offset from code stream)
            s->pc = _t'3 + _t'5            (ptr + int arithmetic)
          ELSE (fall through):
            _t'2 = s->pc
            s->pc = _t'2 + 1               (advance past operand)
       3. return 0

   Two cases:
   - accu = Val_int 0: C takes else branch, stores pc + 1.
   - accu != Val_int 0: C takes then branch, reads offset, stores
     pc + offset.

   Preconditions (via handler_correct):
   - code_base_block != sptr_block (code buffer separate from struct)
   - code buffer at pc contains the branch offset as Vint
   - comparison well-definedness: for non-zero accu, the C ne-comparison
     against tagged(0) succeeds.  This holds when val_repr produces a
     Vlong (Val_int with in-range n, or Val_block tag nil), but not for
     Vptr (CompCert's sem_binarith on tlong/tlong returns None for Vptr).
     The precondition pushes this obligation to the caller. *)

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
(* Struct layout: _pc at offset 0, _accu at offset 8                   *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full).
Proof.
  eexists. split; [| split]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_branchif : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Memory helpers                                                      *)
(* ================================================================== *)

Lemma store_pc_succeeds : forall m sb so_ptrofs v_new,
  Mem.range_perm m sb (Ptrofs.unsigned so_ptrofs) (Ptrofs.unsigned so_ptrofs + 56) Cur Writable ->
  (exists v_old, Mem.load Mint64 m sb (Ptrofs.unsigned so_ptrofs + 0) = Some v_old) ->
  exists m', Mem.store Mint64 m sb (Ptrofs.unsigned so_ptrofs + 0) v_new = Some m'.
Proof.
  intros m sb so_ptrofs v_new Hrp [v_old Hload].
  exact (store_succeeds_sb m sb so_ptrofs 0 v_old Hrp Hload ltac:(lia) ltac:(lia) v_new).
Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* ================================================================== *)
(* Pointer / casting helpers                                           *)
(* ================================================================== *)

Lemma ptrofs_add_zero : forall ofs,
  Ptrofs.add ofs (Ptrofs.repr 0) = ofs.
Proof.
  intros. change (Ptrofs.repr 0) with Ptrofs.zero.
  apply Ptrofs.add_zero.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma sem_add_ptr_int_tint : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint n) tint
    m = Some (Vptr b (Ptrofs.add ofs
                (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                            (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* ================================================================== *)
(* Comparison semantics for Val_int 0 case                             *)
(* ================================================================== *)

Lemma sem_one_long_eq : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Cop.One
    (Vlong n) tlong (Vlong (Int64.repr 1)) tlong m
    = Some (Val.of_bool (negb (Int64.eq n (Int64.repr 1)))).
Proof.
  intros. reflexivity.
Qed.

Lemma bool_val_of_bool : forall b m,
  bool_val (Val.of_bool b) tint m = Some b.
Proof.
  intros [] m; simpl; reflexivity.
Qed.

Lemma int64_eq_1_1 : Int64.eq (Int64.repr 1) (Int64.repr 1) = true.
Proof.
  unfold Int64.eq.
  rewrite Coqlib.zeq_true.
  reflexivity.
Qed.

(* bool_val for Vint Int.one on tint gives true *)
Lemma bool_val_vint_one : forall m,
  bool_val (Vint Int.one) tint m = Some true.
Proof.
  intros. simpl. reflexivity.
Qed.

(* ================================================================== *)
(* pc_rel helpers                                                      *)
(* ================================================================== *)

(* For the fall-through case: new code base is co + sizeof_code_t *)
Lemma pc_rel_shift_1 : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr 4)))
         cb (Ptrofs.add co (Ptrofs.repr sizeof_code_t)) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal.
  rewrite Ptrofs.add_assoc.
  rewrite Ptrofs.add_assoc.
  f_equal.
  rewrite Ptrofs.add_commut. reflexivity.
Qed.

(* ================================================================== *)
(* Tactic for the "branch taken" abs_rel postcondition.                *)
(* ================================================================== *)

Local Ltac prove_field_survives Hstore Hload :=
  apply (load_after_store_other _ _ _ _ _ _ _ Hstore Hload); right; lia.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_BRANCHIF_correct : forall target,
    handler_correct (handle_BRANCHIF target) f_instr_BRANCHIF
      (fun _ m s ard =>
         (* Code block is separate from struct block *)
         ar_code_base_block ard <> ar_sptr_block ard /\
         (* Code buffer at pc contains the branch offset *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
           = Some (Vint (Int.repr (target - Machine.pc s))) /\
         (* Comparison well-definedness for non-zero accu *)
         (Machine.accu s <> Val_int 0 ->
            forall cv,
            val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Machine.accu s) cv ->
            sem_binary_operation (genv_cenv clight_ge) Cop.One
              cv tlong (Vlong (Int64.repr 1)) tlong m
              = Some (Vint Int.one)) /\
         (* Zero accu must be tagged int (not code pointer) *)
         (Machine.accu s = Val_int 0 ->
            forall cv,
            val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Machine.accu s) cv ->
            exists z, cv = Vlong z))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intro target.
  intros e le m s.
  unfold handler_correct, handle_BRANCHIF.

  (* Case split on accu *)
  destruct (Machine.accu s) as [n | tag fields | addr | addr ofs_cl] eqn:Haccu_eq.

  (* ================================================================ *)
  (* Case 1: accu = Val_int n                                          *)
  (* ================================================================ *)
  {
    destruct (Z.eq_dec n 0) as [Hn0 | Hn0].

    (* ============================================================== *)
    (* Case 1a: accu = Val_int 0 => fall through (C else branch)      *)
    (* ============================================================== *)
    {
      subst n. simpl.
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
        Hsp_data &
        [env_v [Henv_load Henv_repr]] &
        Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne]]]] &
        [ts_ptr [Hts_load Htrap_rel]] &
        Hsb_writable).
      destruct Hsp_data as [sp_ptr [sp_b [sp_ofs (Hsp_load & Hsp_eq & Hstack_repr
        & Hblock_sep & Hsp_ne_gb & Hcb_ne_sp & Hsp_ge8 & Hsp_bound & Hsp_writable & Hsp_align)]]].
      subst sp_ptr.

      destruct Hstep_pre as [Hcb_ne_sb [Hcode_load [Hcmp_pre Hzero_tagged]]].

      pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].

      (* accu = Val_int 0, val_repr gives Vlong (Int64.repr 1) *)
      pose proof Haccu_repr as Haccu_repr'.
      rewrite Haccu_eq in Haccu_repr.
      inversion Haccu_repr; subst accu_v.
      2: { exfalso. rewrite Haccu_eq in Haccu_repr'.
           destruct (Hzero_tagged eq_refl _ Haccu_repr') as [z Hz].
           discriminate Hz. }

      destruct interp_state_co_branchif as [co_is [Hco [Hpc_offset Haccu_offset]]].

      (* pc_ptr is a concrete Vptr *)
      unfold pc_rel in Hpc_rel. subst pc_ptr.
      set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

      assert (Hpc_load_uso : Mem.load Mint64 m sb (Ptrofs.unsigned so) =
                Some (Vptr cb pc_ofs)).
      { replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia.
        exact Hpc_load. }

      set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
      set (new_pc_v := Vptr cb new_pc_ofs).

      assert (Hpc_load_uso0 : Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) =
                Some (Vptr cb pc_ofs)).
      { replace (Ptrofs.unsigned so + 0)%Z with (Ptrofs.unsigned so) by lia.
        exact Hpc_load_uso. }
      destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load_uso0 ltac:(lia) ltac:(lia) new_pc_v) as [m' Hstore0].
      assert (Hstore : Mem.store Mint64 m sb (Ptrofs.unsigned so) new_pc_v = Some m').
      { replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia.
        exact Hstore0. }

      set (le' := PTree.set _t'2 (Vptr cb pc_ofs)
                    (PTree.set _t'1 (Vlong (Int64.repr 1)) le)).
      exists le'. exists m'.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* Part 1: manual bigstep construction *)
      {
        set (le1 := PTree.set _t'1 (Vlong (Int64.repr 1)) le).

        (* Outer: (Sset + Sifthenelse) ; Sreturn *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le') (m1 := m').

        (* Inner: Sset _t'1 ; Sifthenelse *)
        { apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m).

          (* Sset _t'1 = s->accu *)
          { apply exec_Sset.
            eapply eval_Elvalue.
            - eapply eval_Efield_struct.
              + eapply eval_Elvalue.
                * eapply eval_Ederef. eapply eval_Etempvar. exact Hle_s.
                * apply deref_loc_copy. reflexivity.
              + reflexivity.
              + exact Hco.
              + exact Haccu_offset.
            - apply deref_loc_value with (chunk := Mint64).
              + reflexivity.
              + simpl. fold so.
                rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
                exact Haccu_load. }

          (* Sifthenelse: condition is false => else branch *)
          { eapply exec_Sifthenelse.
            - (* eval condition: _t'1 != ((0 << 1) + 1) *)
              eapply eval_Ebinop.
              + eapply eval_Etempvar. subst le1. rewrite PTree.gss. reflexivity.
              + eapply eval_Ebinop.
                * eapply eval_Ebinop.
                  { eapply eval_Ecast. eapply eval_Econst_int. exact (sem_cast_int_to_long_0 m). }
                  { eapply eval_Econst_int. }
                  { exact (sem_shl_long_0_1 m). }
                * eapply eval_Econst_int.
                * exact (sem_add_long_int_0_1 m).
              + rewrite sem_one_long_eq. rewrite int64_eq_1_1. reflexivity.
            - (* bool_val: Val.of_bool false = Vint Int.zero => Some false *)
              simpl. reflexivity.
            - (* Execute else branch *)
              simpl.
              (* Else: Ssequence (Sset _t'2 = s->pc) (Sassign s->pc = _t'2+1) *)
              apply exec_Sseq_1 with (t1 := E0)
                (le1 := PTree.set _t'2 (Vptr cb pc_ofs) le1) (m1 := m).

              (* Sset _t'2 = s->pc *)
              { apply exec_Sset.
                eapply eval_Elvalue.
                - eapply eval_Efield_struct.
                  + eapply eval_Elvalue.
                    * eapply eval_Ederef. eapply eval_Etempvar.
                      subst le1. rewrite PTree.gso by (compute; congruence). exact Hle_s.
                    * apply deref_loc_copy. reflexivity.
                  + reflexivity.
                  + exact Hco.
                  + exact Hpc_offset.
                - apply deref_loc_value with (chunk := Mptr).
                  + reflexivity.
                  + simpl. rewrite Mptr_Mint64. fold so.
                    rewrite (ptrofs_add_zero so).
                    exact Hpc_load_uso. }

              (* Sassign s->pc = _t'2 + 1 *)
              { eapply exec_Sassign.
                - eapply eval_Efield_struct.
                  + eapply eval_Elvalue.
                    * eapply eval_Ederef. eapply eval_Etempvar.
                      unfold le'.
                      rewrite PTree.gso by (compute; congruence).
                      rewrite PTree.gso by (compute; congruence). exact Hle_s.
                    * apply deref_loc_copy. reflexivity.
                  + reflexivity.
                  + exact Hco.
                  + exact Hpc_offset.
                - eapply eval_Ebinop.
                  + eapply eval_Etempvar. unfold le'. rewrite PTree.gss. reflexivity.
                  + eapply eval_Econst_int.
                  + apply sem_add_pc_1.
                - apply sem_cast_ptr_tint_to_ptr_tint.
                - apply assign_loc_value with (chunk := Mptr).
                  + reflexivity.
                  + simpl. rewrite Mptr_Mint64. fold so.
                    rewrite (ptrofs_add_zero so).
                    fold new_pc_v. exact Hstore. } } }

        (* Sreturn 0 *)
        { apply exec_Sreturn_some. eapply eval_Econst_int. }
      }

      (* Part 2: abs_rel *)
      {
        set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
        set (ard' := mk_abs_rel sb so hm cb new_co
                       (ar_global_block ard) (ar_global_ofs ard)
                       (ar_stack_block ard) (ar_stack_base_ofs ard)
                       (ar_code_ne_sptr ard) (ar_code_ne_global ard)
                       (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
        exists ard'.
        set (uso := Ptrofs.unsigned so) in *.

        assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some new_pc_v).
        { pose proof (load_after_store_same m m' sb uso new_pc_v Hstore) as Htmp.
          unfold new_pc_v in Htmp |- *.
          rewrite load_result_vptr in Htmp.
          replace (uso + 0)%Z with uso by lia.
          exact Htmp. }

        assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some (Vlong (Int64.repr 1))).
        { prove_field_survives Hstore Haccu_load. }

        assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { prove_field_survives Hstore Hsp_load. }

        assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
        { prove_field_survives Hstore Henv_load. }

        assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { prove_field_survives Hstore Hextra_load. }

        assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
        { prove_field_survives Hstore Hgd_load. }

        assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
        { prove_field_survives Hstore Hts_load. }

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

        { unfold le'.
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          exact Hle_s. }

        { exists new_pc_v. split.
          - exact Hpc_load'.
          - simpl. subst new_pc_v new_pc_ofs.
            apply pc_rel_shift_1. }

        { exists (Vlong (Int64.repr 1)). split.
          - exact Haccu_load'.
          - simpl. rewrite Haccu_eq. apply vr_int. }

        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
          split. { exact Hsp_load'. }
          split. { reflexivity. }
          split. { simpl.
            eapply stack_repr_co_shift.
            apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb uso new_pc_v
                     Hstack_repr Hstore).
            intro Heq; exact (Hblock_sep (eq_sym Heq)). }
          split. { exact Hblock_sep. }
          split. { exact Hsp_ne_gb. }
          split. { exact Hcb_ne_sp. }
          split. { exact Hsp_ge8. }
          split. { exact Hsp_bound. }
          split. { intros ofs' Hofs'.
          eapply Mem.perm_store_1. exact Hstore.
          apply Hsp_writable. exact Hofs'. }
          exact Hsp_align. }

        { exists env_v. split.
          - exact Henv_load'.
          - simpl. eapply val_repr_co_shift. exact Henv_repr. }

        { simpl. exact Hextra_load'. }

        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd_load'.
          - simpl. exact Hgd_eq.
          - simpl.
            eapply global_repr_co_shift.
            apply (global_repr_store_other_block hm cb co m m' _ _ _ sb uso new_pc_v
                     Hglobal_repr Hstore).
            intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          - exact Hgb_ne. }

        { exists ts_ptr. split.
          - exact Hts_load'.
          - simpl. exact Htrap_rel. }

        { intros ofs' Hofs'.
          eapply Mem.perm_store_1. exact Hstore.
          apply Hsb_writable. exact Hofs'. }
      }
    }

    (* ============================================================== *)
    (* Case 1b: accu = Val_int n, n <> 0 => branch taken              *)
    (* ============================================================== *)
    {
      (* n <> 0, so the match gives the wildcard: Step {pc := target} *)
      destruct n as [| p | p]; [contradiction | |]; simpl;
      intros ard Hpre Hstep_pre;

      (unfold abs_rel_with_ard in Hpre;
      set (sb := ar_sptr_block ard) in *;
      set (so := ar_sptr_ofs ard) in *;
      set (hm := ar_heap_map ard) in *;
      set (cb := ar_code_base_block ard) in *;
      set (co := ar_code_base_ofs ard) in *;
      destruct Hpre as (Hle_s &
        [pc_ptr [Hpc_load Hpc_rel]] &
        [accu_v [Haccu_load Haccu_repr]] &
        Hsp_data &
        [env_v [Henv_load Henv_repr]] &
        Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne]]]] &
        [ts_ptr [Hts_load Htrap_rel]] &
        Hsb_writable);
      destruct Hsp_data as [sp_ptr [sp_b [sp_ofs (Hsp_load & Hsp_eq & Hstack_repr
        & Hblock_sep & Hsp_ne_gb & Hcb_ne_sp & Hsp_ge8 & Hsp_bound & Hsp_writable & Hsp_align)]]];
      subst sp_ptr;

      destruct Hstep_pre as [Hcb_ne_sb [Hcode_load [Hcmp_pre _]]];

      pose proof (sptr_ofs_representable ard) as Hso_bound; fold so in Hso_bound;
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _];

      rewrite Haccu_eq in Haccu_repr;

      destruct interp_state_co_branchif as [co_is [Hco [Hpc_offset Haccu_offset]]];

      unfold pc_rel in Hpc_rel; subst pc_ptr;
      set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *;

      assert (Hpc_load_uso : Mem.load Mint64 m sb (Ptrofs.unsigned so) =
                Some (Vptr cb pc_ofs))
        by (replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia;
            exact Hpc_load);

      set (branch_ofs := Int.repr (target - Machine.pc s));
      fold pc_ofs in Hcode_load;
      fold branch_ofs in Hcode_load;

      set (new_pc_ofs := Ptrofs.add pc_ofs
             (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                         (ptrofs_of_int Signed branch_ofs)));
      set (new_pc_v := Vptr cb new_pc_ofs);

      assert (Hpc_load_uso0 : Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) =
                Some (Vptr cb pc_ofs))
        by (replace (Ptrofs.unsigned so + 0)%Z with (Ptrofs.unsigned so) by lia;
            exact Hpc_load_uso);
      destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load_uso0 ltac:(lia) ltac:(lia) new_pc_v) as [m' Hstore0];
      assert (Hstore : Mem.store Mint64 m sb (Ptrofs.unsigned so) new_pc_v = Some m')
        by (replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia;
            exact Hstore0);

      (* Use the precondition for the comparison *)
      pose proof (Hcmp_pre ltac:(congruence) accu_v
                    Haccu_repr) as Hcmp;

      set (le' := PTree.set _t'5 (Vint branch_ofs)
                    (PTree.set _t'4 (Vptr cb pc_ofs)
                      (PTree.set _t'3 (Vptr cb pc_ofs)
                        (PTree.set _t'1 accu_v le))));
      exists le'; exists m';
      exists (Out_return (Some (Vint (Int.repr 0), tint)));

      split;

      [ (* Part 1: manual bigstep construction *)

        set (le1 := PTree.set _t'1 accu_v le);
        set (le2 := PTree.set _t'3 (Vptr cb pc_ofs) le1);
        set (le3 := PTree.set _t'4 (Vptr cb pc_ofs) le2);
        set (le4 := PTree.set _t'5 (Vint branch_ofs) le3);

        (* Outer: (Sset _t'1 + Sifthenelse) ; Sreturn *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m');

        [ (* Inner: Sset _t'1 ; Sifthenelse *)
          apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m);

          [ (* Sset _t'1 = s->accu *)
            apply exec_Sset;
            eapply eval_Elvalue;
            [ eapply eval_Efield_struct;
              [ eapply eval_Elvalue;
                [ eapply eval_Ederef; eapply eval_Etempvar; exact Hle_s
                | apply deref_loc_copy; reflexivity ]
              | reflexivity
              | exact Hco
              | exact Haccu_offset ]
            | apply deref_loc_value with (chunk := Mint64);
              [ reflexivity
              | simpl; fold so;
                rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia));
                exact Haccu_load ] ]

          | (* Sifthenelse: condition true => then branch *)
            eapply exec_Sifthenelse;
            [ (* eval condition *)
              eapply eval_Ebinop;
              [ eapply eval_Etempvar; subst le1; rewrite PTree.gss; reflexivity
              | eapply eval_Ebinop;
                [ eapply eval_Ebinop;
                  [ eapply eval_Ecast; [ eapply eval_Econst_int | exact (sem_cast_int_to_long_0 m) ]
                  | eapply eval_Econst_int
                  | exact (sem_shl_long_0_1 m) ]
                | eapply eval_Econst_int
                | exact (sem_add_long_int_0_1 m) ]
              | exact Hcmp ]
            | (* bool_val: Vint Int.one => Some true *)
              exact (bool_val_vint_one m)
            | (* Execute then branch *)
              simpl;
              (* Then: Sseq (Sset _t'3) (Sseq (Sset _t'4) (Sseq (Sset _t'5) (Sassign s->pc))) *)
              apply exec_Sseq_1 with (t1 := E0) (le1 := le2) (m1 := m);
              [ (* Sset _t'3 = s->pc *)
                apply exec_Sset;
                eapply eval_Elvalue;
                [ eapply eval_Efield_struct;
                  [ eapply eval_Elvalue;
                    [ eapply eval_Ederef; eapply eval_Etempvar;
                      subst le1; rewrite PTree.gso by (compute; congruence); exact Hle_s
                    | apply deref_loc_copy; reflexivity ]
                  | reflexivity
                  | exact Hco
                  | exact Hpc_offset ]
                | apply deref_loc_value with (chunk := Mptr);
                  [ reflexivity
                  | simpl; rewrite Mptr_Mint64; fold so;
                    rewrite (ptrofs_add_zero so);
                    exact Hpc_load_uso ] ]

              | apply exec_Sseq_1 with (t1 := E0) (le1 := le3) (m1 := m);
                [ (* Sset _t'4 = s->pc *)
                  apply exec_Sset;
                  eapply eval_Elvalue;
                  [ eapply eval_Efield_struct;
                    [ eapply eval_Elvalue;
                      [ eapply eval_Ederef; eapply eval_Etempvar;
                        subst le2 le1;
                        rewrite PTree.gso by (compute; congruence);
                        rewrite PTree.gso by (compute; congruence); exact Hle_s
                      | apply deref_loc_copy; reflexivity ]
                    | reflexivity
                    | exact Hco
                    | exact Hpc_offset ]
                  | apply deref_loc_value with (chunk := Mptr);
                    [ reflexivity
                    | simpl; rewrite Mptr_Mint64; fold so;
                      rewrite (ptrofs_add_zero so);
                      exact Hpc_load_uso ] ]

                | apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m);
                  [ (* Sset _t'5 = deref _t'4 (read branch offset from code) *)
                    apply exec_Sset;
                    eapply eval_Elvalue;
                    [ eapply eval_Ederef; eapply eval_Etempvar;
                      subst le3; rewrite PTree.gss; reflexivity
                    | apply deref_loc_value with (chunk := Mint32);
                      [ reflexivity
                      | simpl; exact Hcode_load ] ]

                  | (* Sassign s->pc = _t'3 + _t'5 *)
                    eapply exec_Sassign;
                    [ (* lvalue: s->pc *)
                      eapply eval_Efield_struct;
                      [ eapply eval_Elvalue;
                        [ eapply eval_Ederef; eapply eval_Etempvar;
                          subst le4 le3 le2 le1;
                          rewrite PTree.gso by (compute; congruence);
                          rewrite PTree.gso by (compute; congruence);
                          rewrite PTree.gso by (compute; congruence);
                          rewrite PTree.gso by (compute; congruence); exact Hle_s
                        | apply deref_loc_copy; reflexivity ]
                      | reflexivity
                      | exact Hco
                      | exact Hpc_offset ]
                    | (* rvalue: _t'3 + _t'5 *)
                      eapply eval_Ebinop;
                      [ eapply eval_Etempvar;
                        subst le4 le3 le2;
                        rewrite PTree.gso by (compute; congruence);
                        rewrite PTree.gso by (compute; congruence);
                        rewrite PTree.gss; reflexivity
                      | eapply eval_Etempvar;
                        subst le4; rewrite PTree.gss; reflexivity
                      | apply sem_add_ptr_int_tint ]
                    | (* sem_cast *)
                      apply sem_cast_ptr_tint_to_ptr_tint
                    | (* assign_loc *)
                      apply assign_loc_value with (chunk := Mptr);
                      [ reflexivity
                      | simpl; rewrite Mptr_Mint64; fold so;
                        rewrite (ptrofs_add_zero so);
                        fold new_pc_v; exact Hstore ] ] ] ] ] ] ]

        | (* Sreturn 0 *)
          apply exec_Sreturn_some; eapply eval_Econst_int ]

      | (* Part 2: abs_rel *)
        (set (new_co := Ptrofs.sub new_pc_ofs (Ptrofs.repr (target * sizeof_code_t)));
        set (ard' := mk_abs_rel sb so hm cb new_co
                       (ar_global_block ard) (ar_global_ofs ard)
                       (ar_stack_block ard) (ar_stack_base_ofs ard)
                       (ar_code_ne_sptr ard) (ar_code_ne_global ard)
                       (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard));
        exists ard';
        set (uso := Ptrofs.unsigned so) in *;

        assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some new_pc_v)
          by (pose proof (load_after_store_same m m' sb uso new_pc_v Hstore) as Htmp;
              unfold new_pc_v in Htmp |- *;
              rewrite load_result_vptr in Htmp;
              replace (uso + 0)%Z with uso by lia;
              exact Htmp);

        assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some accu_v)
          by (prove_field_survives Hstore Haccu_load);

        assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs))
          by (prove_field_survives Hstore Hsp_load);

        assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v)
          by (prove_field_survives Hstore Henv_load);

        assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s)))))
          by (prove_field_survives Hstore Hextra_load);

        assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr)
          by (prove_field_survives Hstore Hgd_load);

        assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr)
          by (prove_field_survives Hstore Hts_load);

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]];

        [ unfold le';
          rewrite PTree.gso by (compute; congruence);
          rewrite PTree.gso by (compute; congruence);
          rewrite PTree.gso by (compute; congruence);
          rewrite PTree.gso by (compute; congruence);
          exact Hle_s

        | exists new_pc_v; split;
          [ exact Hpc_load'
          | simpl; unfold pc_rel; unfold new_pc_v;
            f_equal;
            unfold new_co;
            rewrite Ptrofs.sub_add_opp;
            rewrite Ptrofs.add_assoc;
            rewrite (Ptrofs.add_commut (Ptrofs.neg _) _);
            rewrite <- Ptrofs.sub_add_opp;
            rewrite Ptrofs.sub_idem;
            symmetry; apply Ptrofs.add_zero ]

        | exists accu_v; split;
          [ exact Haccu_load'
          | simpl; rewrite Haccu_eq; eapply val_repr_co_shift; exact Haccu_repr ]

        | exists (Vptr sp_b sp_ofs), sp_b, sp_ofs;
          (split; [ exact Hsp_load'
          | split; [ reflexivity
          | split; [ simpl;
            eapply stack_repr_co_shift;
            apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb uso new_pc_v
                     Hstack_repr Hstore);
            intro Heq; exact (Hblock_sep (eq_sym Heq))
          | split; [ exact Hblock_sep
          | split; [ exact Hsp_ne_gb
          | split; [ exact Hcb_ne_sp
          | split; [ exact Hsp_ge8
          | split; [ exact Hsp_bound
          | split; [ intros ofs' Hofs';
            eapply Mem.perm_store_1; [ exact Hstore | ];
            apply Hsp_writable; exact Hofs'
          | exact Hsp_align ]]]]]]]]])

        | exists env_v; split;
          [ exact Henv_load'
          | simpl; eapply val_repr_co_shift; exact Henv_repr ]

        | simpl; exact Hextra_load'

        | exists gd_ptr; split; [| split; [| split]];
          [ exact Hgd_load'
          | simpl; exact Hgd_eq
          | simpl;
            eapply global_repr_co_shift;
            apply (global_repr_store_other_block hm cb co m m' _ _ _ sb uso new_pc_v
                     Hglobal_repr Hstore);
            intro Heq2; exact (Hgb_ne (eq_sym Heq2))
          | exact Hgb_ne ]

        | exists ts_ptr; split;
          [ exact Hts_load'
          | simpl; exact Htrap_rel ]

        | intros ofs' Hofs';
          eapply Mem.perm_store_1; [ exact Hstore | ];
          apply Hsb_writable; exact Hofs' ])
      ]).
    }
  }

  (* ================================================================ *)
  (* Case 2: accu = Val_block tag fields => branch taken               *)
  (* ================================================================ *)
  (* Val_block tag fields: handle_BRANCHIF gives Step {pc := target}.
     val_repr can only produce a witness for Val_block tag nil
     (vr_block_atom), so Val_block tag (h::t) is vacuously true.
     For Val_block tag nil, val_repr gives Vlong, so the comparison
     precondition is usable. *)

  (* ================================================================ *)
  (* Cases 2-4: non-integer accu => branch taken                       *)
  (*                                                                    *)
  (* These use the comparison precondition.                            *)
  (* The proof structure is identical to Case 1b.                      *)
  (* ================================================================ *)

  all: simpl;
    intros ard Hpre Hstep_pre;

    (unfold abs_rel_with_ard in Hpre;
    set (sb := ar_sptr_block ard) in *;
    set (so := ar_sptr_ofs ard) in *;
    set (hm := ar_heap_map ard) in *;
    set (cb := ar_code_base_block ard) in *;
    set (co := ar_code_base_ofs ard) in *;
    destruct Hpre as (Hle_s &
      [pc_ptr [Hpc_load Hpc_rel]] &
      [accu_v [Haccu_load Haccu_repr]] &
      Hsp_data &
      [env_v [Henv_load Henv_repr]] &
      Hextra_load &
      [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne]]]] &
      [ts_ptr [Hts_load Htrap_rel]] &
      Hsb_writable);
    destruct Hsp_data as [sp_ptr [sp_b [sp_ofs (Hsp_load & Hsp_eq & Hstack_repr
      & Hblock_sep & Hsp_ne_gb & Hcb_ne_sp & Hsp_ge8 & Hsp_bound & Hsp_writable & Hsp_align)]]];
    subst sp_ptr;

    destruct Hstep_pre as [Hcb_ne_sb [Hcode_load [Hcmp_pre _]]];

    pose proof (sptr_ofs_representable ard) as Hso_bound; fold so in Hso_bound;
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _];

    destruct interp_state_co_branchif as [co_is [Hco [Hpc_offset Haccu_offset]]];

    unfold pc_rel in Hpc_rel; subst pc_ptr;
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *;

    assert (Hpc_load_uso : Mem.load Mint64 m sb (Ptrofs.unsigned so) =
              Some (Vptr cb pc_ofs))
      by (replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia;
          exact Hpc_load);

    set (branch_ofs := Int.repr (target - Machine.pc s));
    fold pc_ofs in Hcode_load;
    fold branch_ofs in Hcode_load;

    set (new_pc_ofs := Ptrofs.add pc_ofs
           (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                       (ptrofs_of_int Signed branch_ofs)));
    set (new_pc_v := Vptr cb new_pc_ofs);

    assert (Hpc_load_uso0 : Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs))
      by (replace (Ptrofs.unsigned so + 0)%Z with (Ptrofs.unsigned so) by lia;
          exact Hpc_load_uso);
    destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load_uso0 ltac:(lia) ltac:(lia) new_pc_v) as [m' Hstore0];
    assert (Hstore : Mem.store Mint64 m sb (Ptrofs.unsigned so) new_pc_v = Some m')
      by (replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia;
          exact Hstore0);

    rewrite Haccu_eq in Haccu_repr;

    pose proof (Hcmp_pre ltac:(congruence) accu_v
                  Haccu_repr) as Hcmp;

    set (le' := PTree.set _t'5 (Vint branch_ofs)
                  (PTree.set _t'4 (Vptr cb pc_ofs)
                    (PTree.set _t'3 (Vptr cb pc_ofs)
                      (PTree.set _t'1 accu_v le))));
    exists le'; exists m';
    exists (Out_return (Some (Vint (Int.repr 0), tint)));

    split;

    [ (* Part 1: manual bigstep construction *)

      set (le1 := PTree.set _t'1 accu_v le);
      set (le2 := PTree.set _t'3 (Vptr cb pc_ofs) le1);
      set (le3 := PTree.set _t'4 (Vptr cb pc_ofs) le2);
      set (le4 := PTree.set _t'5 (Vint branch_ofs) le3);

      apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m');

      [ apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m);

        [ apply exec_Sset;
          eapply eval_Elvalue;
          [ eapply eval_Efield_struct;
            [ eapply eval_Elvalue;
              [ eapply eval_Ederef; eapply eval_Etempvar; exact Hle_s
              | apply deref_loc_copy; reflexivity ]
            | reflexivity
            | exact Hco
            | exact Haccu_offset ]
          | apply deref_loc_value with (chunk := Mint64);
            [ reflexivity
            | simpl; fold so;
              rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia));
              exact Haccu_load ] ]

        | eapply exec_Sifthenelse;
          [ eapply eval_Ebinop;
            [ eapply eval_Etempvar; subst le1; rewrite PTree.gss; reflexivity
            | eapply eval_Ebinop;
              [ eapply eval_Ebinop;
                [ eapply eval_Ecast; [ eapply eval_Econst_int | exact (sem_cast_int_to_long_0 m) ]
                | eapply eval_Econst_int
                | exact (sem_shl_long_0_1 m) ]
              | eapply eval_Econst_int
              | exact (sem_add_long_int_0_1 m) ]
            | exact Hcmp ]
          | exact (bool_val_vint_one m)
          | simpl;
            apply exec_Sseq_1 with (t1 := E0) (le1 := le2) (m1 := m);
            [ apply exec_Sset;
              eapply eval_Elvalue;
              [ eapply eval_Efield_struct;
                [ eapply eval_Elvalue;
                  [ eapply eval_Ederef; eapply eval_Etempvar;
                    subst le1; rewrite PTree.gso by (compute; congruence); exact Hle_s
                  | apply deref_loc_copy; reflexivity ]
                | reflexivity
                | exact Hco
                | exact Hpc_offset ]
              | apply deref_loc_value with (chunk := Mptr);
                [ reflexivity
                | simpl; rewrite Mptr_Mint64; fold so;
                  rewrite (ptrofs_add_zero so);
                  exact Hpc_load_uso ] ]

            | apply exec_Sseq_1 with (t1 := E0) (le1 := le3) (m1 := m);
              [ apply exec_Sset;
                eapply eval_Elvalue;
                [ eapply eval_Efield_struct;
                  [ eapply eval_Elvalue;
                    [ eapply eval_Ederef; eapply eval_Etempvar;
                      subst le2 le1;
                      rewrite PTree.gso by (compute; congruence);
                      rewrite PTree.gso by (compute; congruence); exact Hle_s
                    | apply deref_loc_copy; reflexivity ]
                  | reflexivity
                  | exact Hco
                  | exact Hpc_offset ]
                | apply deref_loc_value with (chunk := Mptr);
                  [ reflexivity
                  | simpl; rewrite Mptr_Mint64; fold so;
                    rewrite (ptrofs_add_zero so);
                    exact Hpc_load_uso ] ]

              | apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m);
                [ apply exec_Sset;
                  eapply eval_Elvalue;
                  [ eapply eval_Ederef; eapply eval_Etempvar;
                    subst le3; rewrite PTree.gss; reflexivity
                  | apply deref_loc_value with (chunk := Mint32);
                    [ reflexivity
                    | simpl; exact Hcode_load ] ]

                | eapply exec_Sassign;
                  [ eapply eval_Efield_struct;
                    [ eapply eval_Elvalue;
                      [ eapply eval_Ederef; eapply eval_Etempvar;
                        subst le4 le3 le2 le1;
                        rewrite PTree.gso by (compute; congruence);
                        rewrite PTree.gso by (compute; congruence);
                        rewrite PTree.gso by (compute; congruence);
                        rewrite PTree.gso by (compute; congruence); exact Hle_s
                      | apply deref_loc_copy; reflexivity ]
                    | reflexivity
                    | exact Hco
                    | exact Hpc_offset ]
                  | eapply eval_Ebinop;
                    [ eapply eval_Etempvar;
                      subst le4 le3 le2;
                      rewrite PTree.gso by (compute; congruence);
                      rewrite PTree.gso by (compute; congruence);
                      rewrite PTree.gss; reflexivity
                    | eapply eval_Etempvar;
                      subst le4; rewrite PTree.gss; reflexivity
                    | apply sem_add_ptr_int_tint ]
                  | apply sem_cast_ptr_tint_to_ptr_tint
                  | apply assign_loc_value with (chunk := Mptr);
                    [ reflexivity
                    | simpl; rewrite Mptr_Mint64; fold so;
                      rewrite (ptrofs_add_zero so);
                      fold new_pc_v; exact Hstore ] ] ] ] ] ] ]

      | apply exec_Sreturn_some; eapply eval_Econst_int ]

    | (* Part 2: abs_rel *)
      (set (new_co := Ptrofs.sub new_pc_ofs (Ptrofs.repr (target * sizeof_code_t)));
      set (ard' := mk_abs_rel sb so hm cb new_co
                     (ar_global_block ard) (ar_global_ofs ard)
                     (ar_stack_block ard) (ar_stack_base_ofs ard)
                     (ar_code_ne_sptr ard) (ar_code_ne_global ard)
                     (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard));
      exists ard';
      set (uso := Ptrofs.unsigned so) in *;

      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some new_pc_v)
        by (pose proof (load_after_store_same m m' sb uso new_pc_v Hstore) as Htmp;
            unfold new_pc_v in Htmp |- *;
            rewrite load_result_vptr in Htmp;
            replace (uso + 0)%Z with uso by lia;
            exact Htmp);

      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some accu_v)
        by (prove_field_survives Hstore Haccu_load);

      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs))
        by (prove_field_survives Hstore Hsp_load);

      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v)
        by (prove_field_survives Hstore Henv_load);

      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s)))))
        by (prove_field_survives Hstore Hextra_load);

      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr)
        by (prove_field_survives Hstore Hgd_load);

      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr)
        by (prove_field_survives Hstore Hts_load);

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]];

      [ unfold le';
        rewrite PTree.gso by (compute; congruence);
        rewrite PTree.gso by (compute; congruence);
        rewrite PTree.gso by (compute; congruence);
        rewrite PTree.gso by (compute; congruence);
        exact Hle_s

      | exists new_pc_v; split;
        [ exact Hpc_load'
        | simpl; unfold pc_rel; unfold new_pc_v;
          f_equal;
          unfold new_co;
          rewrite Ptrofs.sub_add_opp;
          rewrite Ptrofs.add_assoc;
          rewrite (Ptrofs.add_commut (Ptrofs.neg _) _);
          rewrite <- Ptrofs.sub_add_opp;
          rewrite Ptrofs.sub_idem;
          symmetry; apply Ptrofs.add_zero ]

      | exists accu_v; split;
        [ exact Haccu_load'
        | simpl; rewrite Haccu_eq; eapply val_repr_co_shift; exact Haccu_repr ]

      | exists (Vptr sp_b sp_ofs), sp_b, sp_ofs;
        (split; [ exact Hsp_load'
        | split; [ reflexivity
        | split; [ simpl;
          eapply stack_repr_co_shift;
          apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb uso new_pc_v
                   Hstack_repr Hstore);
          intro Heq; exact (Hblock_sep (eq_sym Heq))
        | split; [ exact Hblock_sep
        | split; [ exact Hsp_ne_gb
        | split; [ exact Hcb_ne_sp
        | split; [ exact Hsp_ge8
        | split; [ exact Hsp_bound
        | split; [ intros ofs' Hofs';
          eapply Mem.perm_store_1; [ exact Hstore | ];
          apply Hsp_writable; exact Hofs'
        | exact Hsp_align ]]]]]]]]])

      | exists env_v; split;
        [ exact Henv_load'
        | simpl; eapply val_repr_co_shift; exact Henv_repr ]

      | simpl; exact Hextra_load'

      | exists gd_ptr; split; [| split; [| split]];
        [ exact Hgd_load'
        | simpl; exact Hgd_eq
        | simpl;
          eapply global_repr_co_shift;
          apply (global_repr_store_other_block hm cb co m m' _ _ _ sb uso new_pc_v
                   Hglobal_repr Hstore);
          intro Heq2; exact (Hgb_ne (eq_sym Heq2))
        | exact Hgb_ne ]

      | exists ts_ptr; split;
        [ exact Hts_load'
        | simpl; exact Htrap_rel ]

      | intros ofs' Hofs';
        eapply Mem.perm_store_1; [ exact Hstore | ];
        apply Hsb_writable; exact Hofs' ])
    ]).
Qed.
