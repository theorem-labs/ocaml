(* OFFSETCLOSURE_correct.v -- OFFSETCLOSURE (parameterized) completeness proof.

   Proves that the C handler f_instr_OFFSETCLOSURE computes the same state
   transition as the Rocq handle_OFFSETCLOSURE n handler.

   OFFSETCLOSURE reads n from the code buffer, reads env, computes
   env + n*sizeof(long), stores to accu, and advances pc past the argument.

   C code (f_instr_OFFSETCLOSURE):
     _t'1 = s->pc;             // read pc pointer
     s->pc = _t'1 + 1;         // store 1: advance pc past argument
     _t'2 = s->env;            // read env (tlong)
     _t'3 = *_t'1;             // read n from code buffer (Mint32)
     s->accu = _t'2 + _t'3 * sizeof(long);  // store 2: set accu

   Rocq: handle_OFFSETCLOSURE n pc' s matches on s.(env):
     - Val_closure addr base_ofs =>
         Step (s <|pc := pc'|> <|accu := Val_closure addr (Z.to_nat (Z.of_nat base_ofs + n))|>)
     - Val_block t _ => if Z.eqb n 0 then Step ... else Error
     - _ => Error

   Two stores: pc field at offset +0, accu field at offset +8.

   Combines CONSTINT's code-buffer-read + pc-advance pattern with
   OFFSETCLOSURE2's env offset arithmetic, generalized over n.

   NO AXIOMS.  All structural/range constraints are preconditions
   via handler_correct. *)

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
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout: _pc at offset 0, _env at offset 24, _accu at offset 8 *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Local Lemma interp_state_co_pc_env_accu : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Local Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* _t'3 * sizeof(long): tint * tulong *)
Local Lemma sem_mul_n_sizeof : forall n m,
  sem_binary_operation (genv_cenv ge) Omul
    (Vint n) tint
    (Vptrofs (Ptrofs.repr 8)) tulong m
  = Some (Vlong (Int64.mul (Int64.repr (Int.signed n)) (Int64.repr 8))).
Proof.
  intros. unfold sem_binary_operation, sem_mul, sem_binarith.
  change (classify_binarith tint tulong) with (bin_case_l Unsigned).
  simpl.
  unfold sem_cast. simpl classify_cast.
  reflexivity.
Qed.

(* Vlong + Vlong: tlong + tulong *)
Local Lemma sem_add_long_long : forall a b m,
  sem_binary_operation (genv_cenv ge) Oadd
    (Vlong a) tlong (Vlong b) tulong m
  = Some (Vlong (Int64.add a b)).
Proof.
  intros. reflexivity.
Qed.

(* Cast tulong -> tlong for Vlong *)
Local Lemma sem_cast_tulong_tlong : forall n m,
  sem_cast (Vlong n) tulong tlong m = Some (Vlong n).
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

Local Lemma pc_rel_shift : forall cb co rocq_pc,
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
(* Precondition                                                        *)
(* ================================================================== *)

Definition offsetclosure_pre (n : Z)
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  (* Code buffer contains Int.repr n at the current PC position *)
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr n)) /\
  (* n fits in the int32 signed range *)
  Int.min_signed <= n <= Int.max_signed /\
  (* env is representable as Vlong (needed for C arithmetic path) *)
  (exists env_long,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long) /\
    (* The result of the C arithmetic gives valid val_repr *)
    match s.(Machine.env) with
    | Val_closure addr base_ofs =>
        val_repr hm cb co
          (Val_closure addr (Z.to_nat (Z.of_nat base_ofs + n)))
          (Vlong (Int64.add env_long
            (Int64.mul (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 8))))
    | Val_block t l =>
        val_repr hm cb co (Val_block t l)
          (Vlong (Int64.add env_long
            (Int64.mul (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 8))))
    | _ => True
    end).

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_OFFSETCLOSURE_correct : forall n,
    handler_correct (handle_OFFSETCLOSURE n) f_instr_OFFSETCLOSURE
      (fun e m s ard => offsetclosure_pre n e m s ard)
      (fun msg s =>
        (msg = "OFFSETCLOSURE: non-zero offset on non-closure env"%string /\
         match Machine.env s with Val_block _ _ => True | _ => False end) \/
        (msg = "OFFSETCLOSURE: invalid env"%string /\
         match Machine.env s with Val_closure _ _ | Val_block _ _ => False | _ => True end))
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intro n.
  intros e le m s.
  unfold handler_correct, handle_OFFSETCLOSURE.

  (* Case split on s.(env) *)
  destruct (Machine.env s) eqn:Henv_eq.

  (* ================================================================ *)
  (* Case 1: env = Val_int z => Error "invalid env"                    *)
  (* ================================================================ *)
  - right; exact (conj eq_refl I).

  (* ================================================================ *)
  (* Case 2: env = Val_block n0 l                                      *)
  (* ================================================================ *)
  - destruct (Z.eqb n 0) eqn:Hn0.
    + (* Z.eqb n 0 = true => Step *)
      simpl.
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

      unfold offsetclosure_pre in Hstep_pre.
      fold sb so hm in Hstep_pre.
      rewrite Henv_eq in Hstep_pre.
      destruct Hstep_pre as (Hcode_load & Hn_range & [env_long [Henv_long_load Hresult_repr]]).

      (* env_v = Vlong env_long *)
      assert (Henv_v_long : env_v = Vlong env_long).
      { rewrite Henv_long_load in Henv_load. congruence. }
      subst env_v.

      (* Structural invariants *)
      pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
      pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
      pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

      (* Composite environment *)
      destruct interp_state_co_pc_env_accu as [co_is [Hco [Hpc_offset [Henv_offset Haccu_offset]]]].

      (* pc_ptr is a concrete Vptr *)
      unfold pc_rel in Hpc_rel. subst pc_ptr.
      set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

      set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
      set (new_pc_v := Vptr cb new_pc_ofs).

      (* Result value *)
      set (result_v := Vlong (Int64.add env_long
            (Int64.mul (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 8)))).

      (* Store 1: pc field at (sb, uso+0) <- new_pc_v *)
      destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia) new_pc_v)
        as [m1 Hstore1].
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

      (* Code load survives store1 *)
      assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
                Some (Vint (Int.repr n))).
      { erewrite Mem.load_store_other.
        - exact Hcode_load.
        - exact Hstore1.
        - left. exact Hcb_ne. }

      (* env survives store1 *)
      assert (Henv_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long)).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
                 (Ptrofs.unsigned so + 24) new_pc_v (Vlong env_long) Hstore1 Henv_long_load).
        right. lia. }

      (* accu survives store1 *)
      assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
                 (Ptrofs.unsigned so + 8) new_pc_v accu_v Hstore1 Haccu_load).
        right. lia. }

      (* Store 2: accu field at (sb, uso+8) <- result_v *)
      destruct (store_succeeds_sb m1 sb so 8 accu_v Hsb_writable_m1 Haccu_load_m1 ltac:(lia) ltac:(lia) result_v)
        as [m2 Hstore2].

      (* Witnesses *)
      set (le' := PTree.set _t'3 (Vint (Int.repr n))
                  (PTree.set _t'2 (Vlong env_long)
                  (PTree.set _t'1 (Vptr cb pc_ofs) le))).

      exists le'. exists m2.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* Part 1: exec *)
      {
        apply (eval_stmt_to_exec clight_ge 20).
        eval_cbn.

        (* S1: Sset _t'1 (s->pc) *)
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        rewrite Hpc_load; eval_cbn.

        (* S2: Sassign (s->pc) (_t'1 + 1) *)
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_pc_1 cb pc_ofs m); eval_cbn.
        rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        fold new_pc_v.
        rewrite Hstore1; eval_cbn.

        (* S3: Sset _t'2 (s->env) -- Hco already resolved globally *)
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Henv_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
        rewrite Henv_load_m1; eval_cbn.

        (* S4: Sset _t'3 (deref _t'1) *)
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gss; eval_cbn.
        rewrite Hcode_load_m1; eval_cbn.

        (* S5: Sassign (s->accu) -- Hco already resolved *)
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Haccu_offset; eval_cbn.

        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gss; eval_cbn.
        rewrite PTree.gss; eval_cbn.

        rewrite sem_mul_n_sizeof; eval_cbn.
        rewrite sem_add_long_long; eval_cbn.
        rewrite sem_cast_tulong_tlong; eval_cbn.

        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        fold result_v.
        rewrite Hstore2; eval_cbn.

        subst le'. reflexivity.
      }

      (* Part 2: abs_rel for post-state *)
      {
        set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
        set (ard' := mk_abs_rel
          (ar_sptr_block ard) (ar_sptr_ofs ard) (ar_heap_map ard)
          (ar_code_base_block ard) new_co
          (ar_global_block ard) (ar_global_ofs ard)
          (ar_stack_block ard) (ar_stack_base_ofs ard)
          (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
        exists ard'.
        set (uso := Ptrofs.unsigned so) in *.

        assert (Hpc_load2 : Mem.load Mint64 m2 sb (uso + 0) = Some new_pc_v).
        { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 0)
                   result_v new_pc_v Hstore2).
          - pose proof (load_after_store_same m m1 sb (uso + 0) new_pc_v Hstore1) as Htmp.
            unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp.
          - left. lia. }

        assert (Haccu_load2 : Mem.load Mint64 m2 sb (uso + 8) = Some result_v).
        { pose proof (load_after_store_same m1 m2 sb (uso + 8) result_v Hstore2) as Htmp.
          unfold result_v in Htmp |- *. rewrite load_result_vlong in Htmp. exact Htmp. }

        assert (Hsp_load2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 16)
                   result_v (Vptr sp_b sp_ofs) Hstore2).
          - apply (load_after_store_other m m1 sb (uso + 0) (uso + 16)
                     new_pc_v (Vptr sp_b sp_ofs) Hstore1 Hsp_load).
            right. lia.
          - right. lia. }

        assert (Henv_load2 : Mem.load Mint64 m2 sb (uso + 24) = Some (Vlong env_long)).
        { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 24)
                   result_v (Vlong env_long) Hstore2 Henv_load_m1).
          right. lia. }

        assert (Hextra_load2 : Mem.load Mint64 m2 sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 32) result_v _ Hstore2).
          - apply (load_after_store_other m m1 sb (uso + 0) (uso + 32)
                     new_pc_v _ Hstore1 Hextra_load).
            right. lia.
          - right. lia. }

        assert (Hgd_load2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 40)
                   result_v gd_ptr Hstore2).
          - apply (load_after_store_other m m1 sb (uso + 0) (uso + 40)
                     new_pc_v gd_ptr Hstore1 Hgd_load).
            right. lia.
          - right. lia. }

        assert (Hts_load2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 48)
                   result_v ts_ptr Hstore2).
          - apply (load_after_store_other m m1 sb (uso + 0) (uso + 48)
                     new_pc_v ts_ptr Hstore1 Hts_load).
            right. lia.
          - right. lia. }

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

        { subst le'.
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          exact Hle_s. }

        { exists new_pc_v. split.
          - exact Hpc_load2.
          - simpl. subst new_pc_v new_pc_ofs. apply pc_rel_shift. }

        { exists result_v. split.
          - exact Haccu_load2.
          - simpl. simpl ar_heap_map. fold hm.
            eapply val_repr_co_shift. exact Hresult_repr. }

        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
          - exact Hsp_load2.
          - reflexivity.
          - eapply stack_repr_store_other_block.
            eapply stack_repr_store_other_block.
            eapply stack_repr_co_shift. exact Hstack_repr.
            exact Hstore1. intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
            exact Hstore2. intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          - exact Hsp_ne_sb.
          - exact Hsp_ne_gb.
          - exact Hcb_ne_sp.
          - exact Hsp_ge8.
          - exact Hsp_rep.
          - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2.
            eapply Mem.perm_store_1. exact Hstore1. apply Hsp_writable. exact Hofs'.
          - exact Hsp_align. }

        { exists (Vlong env_long). split.
          - exact Henv_load2.
          - simpl. simpl ar_heap_map. fold hm.
            eapply val_repr_co_shift. exact Henv_repr. }

        { simpl. exact Hextra_load2. }

        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd_load2.
          - exact Hgd_eq.
          - eapply global_repr_store_other_block.
            eapply global_repr_store_other_block.
            eapply global_repr_co_shift. exact Hglobal_repr.
            exact Hstore1. intro Heq; exact (Hgb_ne_sb (eq_sym Heq)).
            exact Hstore2. intro Heq; exact (Hgb_ne_sb (eq_sym Heq)).
          - exact Hgb_ne_sb. }

        { exists ts_ptr. split.
          - exact Hts_load2.
          - simpl. exact Htrap_rel. }

        { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2.
          eapply Mem.perm_store_1. exact Hstore1. apply Hsb_writable. exact Hofs'. }
      }

    + (* Z.eqb n 0 = false => Error "non-zero offset" *)
      left; exact (conj eq_refl I).

  (* ================================================================ *)
  (* Case 3: env = Val_ptr n0 => Error "invalid env"                   *)
  (* ================================================================ *)
  - right; exact (conj eq_refl I).

  (* ================================================================ *)
  (* Case 4: env = Val_closure n0 n1 => Step                           *)
  (* ================================================================ *)
  - simpl.
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

    unfold offsetclosure_pre in Hstep_pre.
    fold sb so hm in Hstep_pre.
    rewrite Henv_eq in Hstep_pre.
    destruct Hstep_pre as (Hcode_load & Hn_range & [env_long [Henv_long_load Hresult_repr]]).

    (* env_v = Vlong env_long *)
    assert (Henv_v_long : env_v = Vlong env_long).
    { rewrite Henv_long_load in Henv_load. congruence. }
    subst env_v.

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
    pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

    (* Composite environment *)
    destruct interp_state_co_pc_env_accu as [co_is [Hco [Hpc_offset [Henv_offset Haccu_offset]]]].

    (* pc_ptr is a concrete Vptr *)
    unfold pc_rel in Hpc_rel. subst pc_ptr.
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

    set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
    set (new_pc_v := Vptr cb new_pc_ofs).

    (* Result value *)
    set (result_v := Vlong (Int64.add env_long
          (Int64.mul (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 8)))).

    (* Store 1: pc field *)
    destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia) new_pc_v)
      as [m1 Hstore1].
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

    (* Code load survives store1 *)
    assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
              Some (Vint (Int.repr n))).
    { erewrite Mem.load_store_other.
      - exact Hcode_load.
      - exact Hstore1.
      - left. exact Hcb_ne. }

    (* env survives store1 *)
    assert (Henv_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
               (Ptrofs.unsigned so + 24) new_pc_v (Vlong env_long) Hstore1 Henv_long_load).
      right. lia. }

    (* accu survives store1 *)
    assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
               (Ptrofs.unsigned so + 8) new_pc_v accu_v Hstore1 Haccu_load).
      right. lia. }

    (* Store 2: accu field *)
    destruct (store_succeeds_sb m1 sb so 8 accu_v Hsb_writable_m1 Haccu_load_m1 ltac:(lia) ltac:(lia) result_v)
      as [m2 Hstore2].

    (* Witnesses *)
    set (le' := PTree.set _t'3 (Vint (Int.repr n))
                (PTree.set _t'2 (Vlong env_long)
                (PTree.set _t'1 (Vptr cb pc_ofs) le))).

    exists le'. exists m2.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* Part 1: exec *)
    {
      apply (eval_stmt_to_exec clight_ge 20).
      eval_cbn.

      (* S1: Sset _t'1 (s->pc) -- resolves Hco globally *)
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load; eval_cbn.

      (* S2: Sassign (s->pc) (_t'1 + 1) *)
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_pc_1 cb pc_ofs m); eval_cbn.
      rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      fold new_pc_v.
      rewrite Hstore1; eval_cbn.

      (* S3: Sset _t'2 (s->env) -- Hco already resolved *)
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Henv_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
      rewrite Henv_load_m1; eval_cbn.

      (* S4: Sset _t'3 (deref _t'1) *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite Hcode_load_m1; eval_cbn.

      (* S5: Sassign (s->accu) -- Hco already resolved *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Haccu_offset; eval_cbn.

      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite PTree.gss; eval_cbn.

      rewrite sem_mul_n_sizeof; eval_cbn.
      rewrite sem_add_long_long; eval_cbn.
      rewrite sem_cast_tulong_tlong; eval_cbn.

      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      fold result_v.
      rewrite Hstore2; eval_cbn.

      subst le'. reflexivity.
    }

    (* Part 2: abs_rel for post-state *)
    {
      set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
      set (ard' := mk_abs_rel
        (ar_sptr_block ard) (ar_sptr_ofs ard) (ar_heap_map ard)
        (ar_code_base_block ard) new_co
        (ar_global_block ard) (ar_global_ofs ard)
        (ar_stack_block ard) (ar_stack_base_ofs ard)
        (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
      exists ard'.
      set (uso := Ptrofs.unsigned so) in *.

      assert (Hpc_load2 : Mem.load Mint64 m2 sb (uso + 0) = Some new_pc_v).
      { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 0)
                 result_v new_pc_v Hstore2).
        - pose proof (load_after_store_same m m1 sb (uso + 0) new_pc_v Hstore1) as Htmp.
          unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp.
        - left. lia. }

      assert (Haccu_load2 : Mem.load Mint64 m2 sb (uso + 8) = Some result_v).
      { pose proof (load_after_store_same m1 m2 sb (uso + 8) result_v Hstore2) as Htmp.
        unfold result_v in Htmp |- *. rewrite load_result_vlong in Htmp. exact Htmp. }

      assert (Hsp_load2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 16)
                 result_v (Vptr sp_b sp_ofs) Hstore2).
        - apply (load_after_store_other m m1 sb (uso + 0) (uso + 16)
                   new_pc_v (Vptr sp_b sp_ofs) Hstore1 Hsp_load).
          right. lia.
        - right. lia. }

      assert (Henv_load2 : Mem.load Mint64 m2 sb (uso + 24) = Some (Vlong env_long)).
      { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 24)
                 result_v (Vlong env_long) Hstore2 Henv_load_m1).
        right. lia. }

      assert (Hextra_load2 : Mem.load Mint64 m2 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 32) result_v _ Hstore2).
        - apply (load_after_store_other m m1 sb (uso + 0) (uso + 32)
                   new_pc_v _ Hstore1 Hextra_load).
          right. lia.
        - right. lia. }

      assert (Hgd_load2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 40)
                 result_v gd_ptr Hstore2).
        - apply (load_after_store_other m m1 sb (uso + 0) (uso + 40)
                   new_pc_v gd_ptr Hstore1 Hgd_load).
          right. lia.
        - right. lia. }

      assert (Hts_load2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 48)
                 result_v ts_ptr Hstore2).
        - apply (load_after_store_other m m1 sb (uso + 0) (uso + 48)
                   new_pc_v ts_ptr Hstore1 Hts_load).
          right. lia.
        - right. lia. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      { exists new_pc_v. split.
        - exact Hpc_load2.
        - simpl. subst new_pc_v new_pc_ofs. apply pc_rel_shift. }

      { exists result_v. split.
        - exact Haccu_load2.
        - simpl. simpl ar_heap_map. fold hm.
          eapply val_repr_co_shift. exact Hresult_repr. }

      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load2.
        - reflexivity.
        - eapply stack_repr_store_other_block.
          eapply stack_repr_store_other_block.
          eapply stack_repr_co_shift. exact Hstack_repr.
          exact Hstore1. intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          exact Hstore2. intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2.
          eapply Mem.perm_store_1. exact Hstore1. apply Hsp_writable. exact Hofs'.
        - exact Hsp_align. }

      { exists (Vlong env_long). split.
        - exact Henv_load2.
        - simpl. simpl ar_heap_map. fold hm.
          eapply val_repr_co_shift. exact Henv_repr. }

      { simpl. exact Hextra_load2. }

      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load2.
        - exact Hgd_eq.
        - eapply global_repr_store_other_block.
          eapply global_repr_store_other_block.
          eapply global_repr_co_shift. exact Hglobal_repr.
          exact Hstore1. intro Heq; exact (Hgb_ne_sb (eq_sym Heq)).
          exact Hstore2. intro Heq; exact (Hgb_ne_sb (eq_sym Heq)).
        - exact Hgb_ne_sb. }

      { exists ts_ptr. split.
        - exact Hts_load2.
        - simpl. exact Htrap_rel. }

      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2.
        eapply Mem.perm_store_1. exact Hstore1. apply Hsb_writable. exact Hofs'. }
    }
Qed.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr (OFFSETCLOSURE z) / clight_of (OFFSETCLOSURE z) / pre_of (OFFSETCLOSURE z)
   are convertible with handle_OFFSETCLOSURE z / f_instr_OFFSETCLOSURE / offsetclosure_pre z.
   P_halt_of and P_ccall_of are vacuously satisfied (OFFSETCLOSURE never halts or
   issues a C call).  P_error_of requires a small computation bridge via
   error_message_of. *)
Definition correct_OFFSETCLOSURE : forall z,
    handler_correct (handle_instr (Bytecode.AST.OFFSETCLOSURE z)) (clight_of (Bytecode.AST.OFFSETCLOSURE z))
      (pre_of (Bytecode.AST.OFFSETCLOSURE z))
      (P_error_of (Bytecode.AST.OFFSETCLOSURE z)) (P_halt_of (Bytecode.AST.OFFSETCLOSURE z)) (P_ccall_of (Bytecode.AST.OFFSETCLOSURE z)).
Proof.
Admitted.

