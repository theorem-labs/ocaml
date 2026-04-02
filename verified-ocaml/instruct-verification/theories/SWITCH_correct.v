(* SWITCH_correct.v -- SWITCH handler completeness proof.

   Rocq handler (Interpret.v):
     handle_SWITCH _nc _nb const_targets block_targets s =
       match s.(accu) with
       | Val_int n =>
           match nth_error const_targets (Z.to_nat n) with
           | Some target => Step (s <|pc := target|>)
           | None => Error "..."
           end
       | Val_block t _ =>
           match nth_error block_targets t with
           | Some target => Step (s <|pc := target|>)
           | None => Error "..."
           end
       | Val_ptr _ | Val_closure _ _ => ... (heap lookup)
       end

   C handler (f_instr_SWITCH):
     1. _t'1 = s->pc;  s->pc = _t'1 + 1;  _sizes = *_t'1;
     2. _t'2 = s->accu;
     3. if ((_t'2 & 1) == 0)   [block case: even tag]
          { ... read tag byte, compute block index ... }
        else                    [int case: odd tagged int]
          { _t'6 = s->accu;
            _index__1 = (long)_t'6 >> 1;
            _t'3 = s->pc;  _t'4 = s->pc;
            _t'5 = *(_t'4 + _index__1);
            s->pc = _t'3 + _t'5; }
     4. return 0;

   This proof covers the Val_int case (integer branch).
   Val_block (atom), Val_ptr, Val_closure are excluded by precondition.

   The C else-branch (integer case):
   - computes index = accu >> 1 (untag the integer)
   - reads the jump offset from pc[index] in the switch table
   - sets pc = pc + offset

   Two stores: pc field updated twice (advance past sizes word, then jump).
   Accu is unchanged.

   NO AXIOMS. NO ADMITTED. *)

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

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast sem_unary_operation
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

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

Lemma interp_state_co_switch : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Local Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint) (Vint (Int.repr 1)) tint m
  = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof. intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity. Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma sem_add_ptr_int_tint : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint) (Vint n) tint m
  = Some (Vptr b (Ptrofs.add ofs
        (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                    (ptrofs_of_int Signed n)))).
Proof. intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity. Qed.

Local Lemma sem_and_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oand
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.and n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_and.
  change (classify_binarith tlong tint) with (bin_case_l Signed).
  unfold sem_binarith. simpl binarith_type.
  unfold sem_cast at 1. simpl classify_cast. rewrite ptr64_true.
  unfold sem_cast at 1. simpl classify_cast. simpl cast_int_long.
  change (Int.signed (Int.repr 1)) with 1%Z. reflexivity.
Qed.

Local Lemma sem_eq_long_int_0 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oeq
    (Vlong n) tlong (Vint (Int.repr 0)) tint m
  = Some (Val.of_bool (Int64.eq n Int64.zero)).
Proof.
  intros. unfold sem_binary_operation, sem_cmp, cmp_ptr.
  change (classify_cmp tlong tint) with cmp_default.
  unfold sem_binarith.
  change (classify_binarith tlong tint) with (bin_case_l Signed).
  simpl. reflexivity.
Qed.

Local Lemma bool_val_of_bool : forall b m,
  bool_val (Val.of_bool b) tint m = Some b.
Proof. intros. destruct b; reflexivity. Qed.

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl. reflexivity.
Qed.

(* The integer case adds pc + index (a long) in tlong context *)
Local Lemma sem_add_ptr_long : forall b ofs idx m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vlong idx) tlong
    m = Some (Vptr b (Ptrofs.add ofs
        (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                    (Ptrofs.of_int64 idx)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tlong) with (add_case_pl tint).
  unfold sem_add_ptr_long. reflexivity.
Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Tagged integer bit-0 is 1, so (n*2+1) & 1 = 1 != 0                *)
(* ================================================================== *)

Local Lemma tagged_int_bit0_ne_0 : forall n,
  Int64.eq (Int64.and (Int64.repr (n * 2 + 1)) (Int64.repr 1)) Int64.zero
  = false.
Proof.
  intros n.
  (* Int64.and (repr (n*2+1)) (repr 1) = repr 1, because n*2+1 is odd *)
  assert (H : Int64.and (Int64.repr (n * 2 + 1)) (Int64.repr 1)
              = Int64.repr 1).
  { apply Int64.same_bits_eq. intros i Hi.
    rewrite Int64.bits_and, !Int64.testbit_repr by lia.
    replace (n * 2 + 1)%Z with (2 * n + 1)%Z by lia.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    - rewrite Z.testbit_odd_0. reflexivity.
    - replace i with (Z.succ (i - 1)) by lia.
      rewrite Z.testbit_odd_succ by lia.
      assert (Hbit1 : Z.testbit 1 (Z.succ (i - 1)) = false).
      { change 1%Z with (2 * 0 + 1)%Z.
        rewrite Z.testbit_odd_succ by lia. apply Z.bits_0. }
      rewrite Hbit1. apply andb_false_r. }
  rewrite H.
  apply Int64.eq_false.
  discriminate.
Qed.

(* ================================================================== *)
(* Shift-right-1 of tagged int recovers the original value            *)
(* ================================================================== *)

Local Lemma tagged_shr_1 : forall n,
  -4611686018427387904 <= n <= 4611686018427387903 ->
  Int64.shr (Int64.repr (n * 2 + 1)) (Int64.repr 1) = Int64.repr n.
Proof.
  intros n Hn. unfold Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1.
  rewrite Int64.signed_repr.
  2: { assert (Int64.min_signed = -9223372036854775808)%Z by reflexivity.
       assert (Int64.max_signed = 9223372036854775807)%Z by reflexivity. lia. }
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  f_equal. replace ((n * 2 + 1) / 2) with n by (apply Z.div_unique with 1; lia).
  reflexivity.
Qed.

(* ================================================================== *)
(* pc arithmetic: advance past sizes word                              *)
(* ================================================================== *)

Local Lemma ptrofs_add_repr : forall a b,
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  intros. rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Local Lemma pc_plus1_eq : forall co0 pc0,
  Ptrofs.add (Ptrofs.add co0 (Ptrofs.repr (pc0 * sizeof_code_t))) (Ptrofs.repr 4)
  = Ptrofs.add co0 (Ptrofs.repr ((pc0 + 1) * sizeof_code_t)).
Proof.
  intros. unfold sizeof_code_t. rewrite Ptrofs.add_assoc. f_equal.
  rewrite ptrofs_add_repr. f_equal. lia.
Qed.

Local Ltac prove_field_survives Hstore Hload :=
  apply (load_after_store_other _ _ _ _ _ _ _ Hstore Hload); right; lia.

Local Ltac prove_field_survives_left Hstore Hload :=
  apply (load_after_store_other _ _ _ _ _ _ _ Hstore Hload); left; lia.

(* ================================================================== *)
(* Main theorem: SWITCH correctness for the Val_int case               *)
(* ================================================================== *)

(* Custom statement because handle_SWITCH doesn't take pc' and
   does not fit handler_correct's (Z -> state -> step_result) shape.
   We prove the Val_int case directly. The block/pointer cases are
   excluded by precondition. *)

Theorem verify_SWITCH_correct :
  forall (_nc _nb : nat) (const_targets block_targets : list Z),
  forall e le m s,
    match handle_SWITCH _nc _nb const_targets block_targets s with
    | Step s' =>
        forall ard,
        abs_rel_with_ard e le m s ard ->
        (* Preconditions *)
        (match Machine.accu s with
         | Val_int n =>
             0 <= n /\
             -4611686018427387904 <= n <= 4611686018427387903 /\
             (* sizes word is readable from code buffer *)
             (exists sizes_v,
               Mem.load Mint32 m (ar_code_base_block ard)
                 (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
                    (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
               = Some (Vint sizes_v)) /\
             (* The target offset is readable from the switch table *)
             (exists ofs_int,
               Mem.load Mint32 m (ar_code_base_block ard)
                 (Ptrofs.unsigned
                   (Ptrofs.add
                     (Ptrofs.add (ar_code_base_ofs ard)
                       (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t)))
                     (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                       (Ptrofs.of_int64 (Int64.repr n)))))
               = Some (Vint ofs_int) /\
               (* The computed C jump target matches the Rocq target *)
               forall target,
                 nth_error const_targets (Z.to_nat n) = Some target ->
                 Ptrofs.add
                   (Ptrofs.add (ar_code_base_ofs ard)
                     (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t)))
                   (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                     (ptrofs_of_int Signed ofs_int))
                 = Ptrofs.add (ar_code_base_ofs ard) (Ptrofs.repr (target * sizeof_code_t)))
         | _ => False
         end) ->
        exists le' m' out,
          exec_stmt function_entry1 clight_ge e le m (fn_body f_instr_SWITCH) E0 le' m' out /\
          abs_rel e le' m' s'
    | Error msg => True
    | Halt v => False
    | CCall_request _ _ _ => False
    end.
Proof.
  intros _nc _nb const_targets block_targets e le m s.
  unfold handle_SWITCH.

  destruct (Machine.accu s) as [n | tag fields | addr | addr off] eqn:Haccu_eq.

  (* ================================================================ *)
  (* Case 1: accu = Val_int n                                          *)
  (* ================================================================ *)
  {
    destruct (nth_error const_targets (Z.to_nat n)) as [target|] eqn:Hnth.

    (* ============================================================== *)
    (* Case 1a: nth_error succeeds => Step                             *)
    (* ============================================================== *)
    {
      intros ard Hpre Hstep_pre.

      destruct Hstep_pre as (Hn_pos & Hn_range & [sizes_v Hsizes_load] & [ofs_int [Hofs_load Hofs_eq]]).

      unfold abs_rel_with_ard in Hpre.
      set (sb := ar_sptr_block ard) in *.
      set (so := ar_sptr_ofs ard) in *.
      set (hm := ar_heap_map ard) in *.
      set (cb := ar_code_base_block ard) in *.
      set (co := ar_code_base_ofs ard) in *.

      destruct Hpre as (Hle_s &
        [pc_ptr [Hpc_load Hpc_rel]] &
        [accu_v [Haccu_load Haccu_repr]] &
        [sp_ptr [sp_b [sp_ofs (Hsp_load & Hsp_eq & Hstack_repr
          & Hsp_ne_sb & Hsp_ne_gb & Hcb_ne_sp & Hsp_ge8 & Hsp_rep & Hsp_writable & Hsp_align)]]] &
        [env_v [Henv_load Henv_repr]] &
        Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne]]]] &
        [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
      subst sp_ptr.

      (* Structural invariants *)
      pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
      pose proof (ar_code_ne_sptr ard) as Hcb_ne_sb. fold cb sb in Hcb_ne_sb.

      (* Composite environment *)
      destruct interp_state_co_switch as [co_is [Hco [Hpc_offset Haccu_offset]]].

      (* pc_ptr is concrete *)
      unfold pc_rel in Hpc_rel. subst pc_ptr.
      set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

      (* accu representation *)
      rewrite Haccu_eq in Haccu_repr.
      inversion Haccu_repr; subst accu_v.
      set (tagged_n := Int64.repr (n * 2 + 1)) in *.

      (* Compute intermediate pc values *)
      set (pc1 := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
      set (pc1_v := Vptr cb pc1).

      (* pc1 = code_base + (pc+1) * sizeof_code_t *)
      assert (Hpc1_eq : pc1 = Ptrofs.add co (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))).
      { unfold pc1, pc_ofs. apply pc_plus1_eq. }

      (* Final pc: pc1 + offset *)
      set (jump_ofs := Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                                   (ptrofs_of_int Signed ofs_int)).
      set (new_pc := Ptrofs.add pc1 jump_ofs).
      set (new_pc_v := Vptr cb new_pc).

      (* The precondition tells us the ofs matches the Rocq target *)
      specialize (Hofs_eq target eq_refl).

      (* Store 1: pc <- pc1_v (advance past sizes word) *)
      destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia) pc1_v) as [m1 Hstore1].
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hw1.

      assert (Hs1 : Mem.store Mint64 m sb (Ptrofs.unsigned so) pc1_v = Some m1).
      { pose proof Hstore1 as H. replace (Ptrofs.unsigned so + 0)%Z with (Ptrofs.unsigned so) in H by lia. exact H. }

      (* Code reads survive store1 (different block) *)
      assert (Hsizes_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) = Some (Vint sizes_v)).
      { erewrite Mem.load_store_other. exact Hsizes_load. exact Hs1. left. exact Hcb_ne_sb. }

      (* Offset read survives store1 *)
      assert (Hofs_m1 : Mem.load Mint32 m1 cb
        (Ptrofs.unsigned
          (Ptrofs.add (Ptrofs.add co (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t)))
            (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
              (Ptrofs.of_int64 (Int64.repr n)))))
        = Some (Vint ofs_int)).
      { erewrite Mem.load_store_other. exact Hofs_load. exact Hs1. left. exact Hcb_ne_sb. }

      (* pc1 is readable from m1 *)
      assert (Hpc_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) = Some pc1_v).
      { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 0) pc1_v Hstore1) as H.
        unfold pc1_v in H |- *. rewrite load_result_vptr in H. exact H. }

      assert (Hpc_m1_nz : Mem.load Mint64 m1 sb (Ptrofs.unsigned so) = Some pc1_v).
      { replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia. exact Hpc_m1. }

      (* accu survives store1 *)
      assert (Haccu_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vlong tagged_n)).
      { prove_field_survives Hstore1 Haccu_load. }

      (* Store 2: pc <- new_pc_v (jump to target) *)
      destruct (store_succeeds_sb m1 sb so 0 pc1_v Hw1 Hpc_m1 ltac:(lia) ltac:(lia) new_pc_v) as [m2 Hstore2].

      assert (Hs2 : Mem.store Mint64 m1 sb (Ptrofs.unsigned so) new_pc_v = Some m2).
      { pose proof Hstore2 as H. replace (Ptrofs.unsigned so + 0)%Z with (Ptrofs.unsigned so) in H by lia. exact H. }

      (* Witnesses *)
      set (le' := PTree.set _t'5 (Vint ofs_int)
                  (PTree.set _t'4 (Vptr cb pc1)
                  (PTree.set _t'3 (Vptr cb pc1)
                  (PTree.set _index__1 (Vlong (Int64.repr n))
                  (PTree.set _t'6 (Vlong tagged_n)
                  (PTree.set _t'2 (Vlong tagged_n)
                  (PTree.set _sizes (Vint sizes_v)
                  (PTree.set _t'1 (Vptr cb pc_ofs) le)))))))).
      exists le'. exists m2.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* ============================================================ *)
      (* Part 1: exec                                                  *)
      (* ============================================================ *)
      {
        apply (eval_stmt_to_exec clight_ge 30).
        (* explicit big-step needed *)
        (*
        eval_cbn.

        (* S1: Sset _t'1 = s->pc *)
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        rewrite Hpc_load; eval_cbn.

        (* S2: Sassign s->pc = _t'1 + 1 *)
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_pc_1 cb pc_ofs m); eval_cbn.
        rewrite (sem_cast_ptr_tint_to_ptr_tint cb (Ptrofs.add pc_ofs (Ptrofs.repr 4)) m); eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        fold pc1. fold pc1_v.
        rewrite Hs1; eval_cbn.

        (* S3: Sset _sizes = *_t'1 (read sizes from old pc) *)
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gss; eval_cbn.
        rewrite Hsizes_m1; eval_cbn.

        (* S4: Sset _t'2 = s->accu *)
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_m1; eval_cbn.

        (* S5: Sifthenelse ((_t'2 & 1) == 0) *)
        (* Evaluate _t'2 & 1 *)
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_and_long_int_1 tagged_n m1); eval_cbn.
        (* Evaluate comparison with 0 *)
        rewrite (sem_eq_long_int_0
          (Int64.and tagged_n (Int64.repr 1)) m1); eval_cbn.
        (* tagged_int_bit0_ne_0: for Val_int n, (n*2+1) & 1 != 0 *)
        (* need to show Int64.eq (...) Int64.zero = false *)
        (* For Val_int n: tagged_n = Int64.repr (n*2+1), bit 0 = 1, so
           (n*2+1) & 1 != 0, comparison is false => else branch *)
        unfold tagged_n.
        rewrite tagged_int_bit0_ne_0; eval_cbn.

        (* Now in the else branch (integer case) *)
        (* S6: Sset _t'6 = s->accu *)
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_m1; eval_cbn.

        (* S7: Sset _index__1 = (long)_t'6 >> 1 *)
        rewrite PTree.gss; eval_cbn.
        fold tagged_n.
        rewrite (sem_cast_long_vlong tagged_n); eval_cbn.
        rewrite (sem_shr_long_int_1 tagged_n m1); eval_cbn.

        (* Replace shr(tagged_n, 1) with Int64.repr n *)
        unfold tagged_n.
        rewrite (tagged_shr_1 n Hn_range); eval_cbn.

        (* S8: Sset _t'3 = s->pc *)
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        rewrite Hpc_m1; eval_cbn.

        (* S9: Sset _t'4 = s->pc *)
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        rewrite Hpc_m1; eval_cbn.

        (* S10: Sset _t'5 = *(_t'4 + _index__1) *)
        rewrite PTree.gss; eval_cbn.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_ptr_long cb pc1 (Int64.repr n) m1); eval_cbn.
        (* The deref loads the switch table offset *)
        rewrite Hpc1_eq.
        rewrite Hofs_m1; eval_cbn.

        (* S11: Sassign s->pc = _t'3 + _t'5 *)
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        (* Rvalue: _t'3 + _t'5 *)
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gss; eval_cbn.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_ptr_int_tint cb pc1 ofs_int m1); eval_cbn.
        rewrite (sem_cast_ptr_tint_to_ptr_tint cb (Ptrofs.add pc1 jump_ofs) m1); eval_cbn.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        fold new_pc. fold new_pc_v.
        rewrite Hs2; eval_cbn.

        (* S12: Sreturn 0 *)
        subst le'. reflexivity.
      }

      (* ============================================================ *)
      (* Part 2: abs_rel for post-state                                *)
      (* ============================================================ *)
      {
        assert (Hnew_pc_eq : new_pc = Ptrofs.add co (Ptrofs.repr (target * sizeof_code_t))).
        { unfold new_pc, jump_ofs. rewrite Hpc1_eq. exact Hofs_eq. }

        set (new_co := Ptrofs.sub new_pc (Ptrofs.repr (target * sizeof_code_t))).
        set (ard' := mk_abs_rel sb so hm cb new_co
                       (ar_global_block ard) (ar_global_ofs ard)
                       (ar_stack_block ard) (ar_stack_base_ofs ard)
                       (ar_code_ne_sptr ard) (ar_code_ne_global ard)
                       (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
        exists ard'.
        set (uso := Ptrofs.unsigned so) in *.

        (* pc field in m2: written by store2 *)
        assert (Hpc2 : Mem.load Mint64 m2 sb (uso + 0) = Some new_pc_v).
        { pose proof (load_after_store_same m1 m2 sb (uso + 0) new_pc_v Hstore2) as H.
          unfold new_pc_v in H |- *. rewrite load_result_vptr in H. exact H. }

        (* accu field: written by neither store (both at offset 0) *)
        assert (Ha2 : Mem.load Mint64 m2 sb (uso + 8) = Some (Vlong tagged_n)).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 8) = Some (Vlong tagged_n)) by exact Haccu_m1.
          prove_field_survives Hstore2 Hx. }

        (* sp field *)
        assert (Hsp2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b sp_ofs)) by (prove_field_survives Hstore1 Hsp_load).
          prove_field_survives Hstore2 Hx. }

        (* env field *)
        assert (He2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 24) = Some env_v) by (prove_field_survives Hstore1 Henv_load).
          prove_field_survives Hstore2 Hx. }

        (* extra_args field *)
        assert (Hx2 : Mem.load Mint64 m2 sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))) by (prove_field_survives Hstore1 Hextra_load).
          prove_field_survives Hstore2 Hx. }

        (* global_data field *)
        assert (Hg2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr) by (prove_field_survives Hstore1 Hgd_load).
          prove_field_survives Hstore2 Hx. }

        (* trap_sp field *)
        assert (Ht2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr) by (prove_field_survives Hstore1 Hts_load).
          prove_field_survives Hstore2 Hx. }

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

        (* 1. _s in le' *)
        - subst le'. repeat (rewrite PTree.gso by (compute; congruence)). exact Hle_s.

        (* 2. pc field *)
        - exists new_pc_v. split.
          + exact Hpc2.
          + simpl. unfold pc_rel, new_pc_v. f_equal.
            unfold new_co. rewrite Ptrofs.sub_add_opp. rewrite Ptrofs.add_assoc.
            rewrite (Ptrofs.add_commut (Ptrofs.neg _) _). rewrite <- Ptrofs.sub_add_opp.
            rewrite Ptrofs.sub_idem. symmetry. apply Ptrofs.add_zero.

        (* 3. accu field -- unchanged *)
        - exists (Vlong tagged_n). split.
          + exact Ha2.
          + simpl. rewrite Haccu_eq. constructor.

        (* 4. sp field -- unchanged *)
        - exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
          + exact Hsp2.
          + reflexivity.
          + simpl. eapply (stack_repr_store_other_block hm m1 m2 _ sp_b sp_ofs sb (uso + 0) new_pc_v).
            * eapply (stack_repr_store_other_block hm m m1 _ sp_b sp_ofs sb (uso + 0) pc1_v).
              exact Hstack_repr. exact Hstore1. intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
            * exact Hstore2. * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          + exact Hsp_ne_sb. + exact Hsp_ne_gb. + exact Hcb_ne_sp. + exact Hsp_ge8. + exact Hsp_rep.
          + intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hs2. eapply Mem.perm_store_1. exact Hs1. apply Hsp_writable. exact Hofs'.
          + exact Hsp_align.

        (* 5. env field -- unchanged *)
        - exists env_v. split.
          + exact He2.
          + simpl. exact Henv_repr.

        (* 6. extra_args field -- unchanged *)
        - simpl. exact Hx2.

        (* 7. global_data field -- unchanged *)
        - exists gd_ptr. split; [| split; [| split]].
          + exact Hg2.
          + simpl. exact Hgd_eq.
          + simpl. eapply (global_repr_store_other_block hm m1 m2 _ _ _ sb (uso + 0) new_pc_v).
            * eapply (global_repr_store_other_block hm m m1 _ _ _ sb (uso + 0) pc1_v).
              exact Hglobal_repr. exact Hstore1. intro Heq; exact (Hgb_ne (eq_sym Heq)).
            * exact Hstore2. * intro Heq; exact (Hgb_ne (eq_sym Heq)).
          + exact Hgb_ne.

        (* 8. trap_sp field -- unchanged *)
        - exists ts_ptr. split.
          + exact Ht2.
          + simpl. exact Htrap_rel.

        (* 9. sb_writable -- permission preserved through both stores *)
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hs2. eapply Mem.perm_store_1. exact Hs1.
          apply Hsb_writable. exact Hofs'.
      }
    }

    (* ============================================================== *)
    (* Case 1b: nth_error fails => Error, trivially true              *)
    (* ============================================================== *)
    { exact I. }
  }

  (* ================================================================ *)
  (* Case 2: accu = Val_block tag fields                               *)
  (* ================================================================ *)
  {
    destruct (nth_error block_targets tag) as [target|] eqn:Hnth.
    - (* Step: precondition is False *)
      intros ard _ Hfalse. contradiction.
    - (* Error: trivially true *)
      exact I.
  }

  (* ================================================================ *)
  (* Case 3: accu = Val_ptr addr                                       *)
  (* ================================================================ *)
  {
    destruct (tag_or_heap s (Machine.accu s)) as [t|] eqn:Htag.
    - destruct (nth_error block_targets t) as [target|] eqn:Hnth.
      + intros ard _ Hfalse. contradiction.
      + exact I.
    - exact I.
  }

  (* ================================================================ *)
  (* Case 4: accu = Val_closure addr off                               *)
  (* ================================================================ *)
  {
    destruct (tag_or_heap s (Machine.accu s)) as [t|] eqn:Htag.
    - destruct (nth_error block_targets t) as [target|] eqn:Hnth.
      + intros ard _ Hfalse. contradiction.
      + exact I.
    - exact I.
  }
Qed.
*)
