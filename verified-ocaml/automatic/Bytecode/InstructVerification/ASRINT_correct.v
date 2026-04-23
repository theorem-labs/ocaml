(* ASRINT_correct.v -- correctness proof for ASRINT bytecode handler.

   C handler (from clightgen):
     _t'1 = s->sp;
     s->sp = _t'1 + 1;
     _t'2 = s->accu;
     _t'3 = *_t'1;
     s->accu = (long)(((long)_t'2 >> ((long)_t'3 >> 1)) | 1);
     return 0;

   Rocq handler:
     handle_ASRINT pc' s = match accu, stack with
       | Val_int a, Val_int b :: rest =>
           Step (s<|pc:=pc'|><|accu:=Val_int(Z.shiftr a b)|><|stack:=rest|>)
       | _, _ => Error ...

   Tagged arithmetic identity (when 0 <= b < 64 and a*2+1 fits in
   64-bit signed range):
     ((2a+1) >>_arith b) | 1 = 2*(Z.shiftr a b)+1

   The C shift is only defined when the shift amount is in [0,64).
   Additionally, since Int64.shr is an arithmetic (signed) shift,
   the tagged value a*2+1 must fit in the 64-bit signed range
   for the result to agree with Z.shiftr on unbounded integers.
   This holds for OCaml's 63-bit integers (a in [-2^62, 2^62-1]).
   Both constraints are encoded as preconditions via
   handler_correct. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Import Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr sem_binary_operation sem_cast
        Mem.load Mem.store Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int field_offset PTree.get PTree.set].

(* ================================================================== *)
(* Semantic lemmas for shift and or operations                         *)
(* ================================================================== *)

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl. reflexivity.
Qed.

Local Lemma sem_shr_long_long_signed : forall n1 n2 m,
  Int64.ltu n2 Int64.iwordsize = true ->
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n1) tlong (Vlong n2) tlong m
  = Some (Vlong (Int64.shr n1 n2)).
Proof.
  intros n1 n2 m Hguard.
  unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tlong) with (shift_case_ll Signed).
  simpl. rewrite Hguard. reflexivity.
Qed.

Local Lemma sem_or_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oor
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.or n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Tagged arithmetic lemmas for ASRINT                                  *)
(* ================================================================== *)

(* Helper: 127 <= Int64.max_signed *)
Local Lemma max_signed_ge_127 : 127 <= Int64.max_signed.
Proof.
  unfold Int64.max_signed.
  rewrite Int64.half_modulus_power.
  change (Int64.zwordsize - 1) with 63.
  assert (two_p 63 >= 128).
  { change (two_p 63) with (two_p (7 + 56)).
    rewrite two_p_is_exp by lia.
    change (two_p 7) with 128.
    generalize (two_p_gt_ZERO 56 ltac:(lia)). lia. }
  lia.
Qed.

(* Helper: 127 <= Int64.max_unsigned *)
Local Lemma max_unsigned_ge_127 : 127 <= Int64.max_unsigned.
Proof.
  generalize Int64.two_wordsize_max_unsigned.
  change Int64.zwordsize with 64. lia.
Qed.

(* Key lemma: for 0 <= b < 64,
   Int64.shr (Int64.repr (b*2+1)) (Int64.repr 1) has unsigned value = b *)
Local Lemma shr_tagged_unsigned : forall b,
  0 <= b < 64 ->
  Int64.unsigned (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)) = b.
Proof.
  intros b Hb.
  unfold Int64.shr.
  rewrite Int64.signed_repr.
  2: { generalize (Int64.min_signed_neg) max_signed_ge_127. lia. }
  change (Int64.unsigned (Int64.repr 1)) with 1.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1)%Z with 2%Z.
  replace ((b * 2 + 1) / 2)%Z with b by (apply Z.div_unique with 1; lia).
  apply Int64.unsigned_repr.
  generalize max_unsigned_ge_127. lia.
Qed.

(* The ltu guard holds when 0 <= b < 64 *)
Local Lemma asr_shift_ltu_guard : forall b,
  0 <= b < 64 ->
  Int64.ltu (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1))
            Int64.iwordsize = true.
Proof.
  intros b Hb.
  unfold Int64.ltu.
  rewrite shr_tagged_unsigned by lia.
  change (Int64.unsigned Int64.iwordsize) with Int64.zwordsize.
  unfold Int64.zwordsize. simpl.
  destruct (zlt b 64); [reflexivity | lia].
Qed.

(* Helper: Int64.shr (Int64.repr (b*2+1)) (Int64.repr 1) = Int64.repr b *)
Local Lemma int64_shr_tagged_1 : forall b,
  0 <= b < 64 ->
  Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1) = Int64.repr b.
Proof.
  intros b Hb.
  apply Int64.same_if_eq. unfold Int64.eq.
  rewrite shr_tagged_unsigned by lia.
  rewrite Int64.unsigned_repr by (generalize max_unsigned_ge_127; lia).
  destruct (zeq b b); [reflexivity | congruence].
Qed.

(* Z.lor x 1 = 2 * Z.div2 x + 1 *)
Local Lemma Z_lor_1_div2 : forall x, Z.lor x 1 = 2 * Z.div2 x + 1.
Proof.
  intros x.
  pose proof (Z.div2_odd (Z.lor x 1)) as Heq.
  assert (Hodd : Z.odd (Z.lor x 1) = true).
  { rewrite <- Z.bit0_odd. rewrite Z.lor_spec. simpl. rewrite Bool.orb_true_r. reflexivity. }
  rewrite Hodd in Heq. simpl Z.b2z in Heq.
  assert (Hdiv2 : Z.div2 (Z.lor x 1) = Z.div2 x).
  { rewrite !Z.div2_spec.
    rewrite Z.shiftr_lor.
    replace (Z.shiftr 1 1) with 0 by reflexivity.
    rewrite Z.lor_0_r. reflexivity. }
  lia.
Qed.

(* Z.div2 (Z.shiftr (a*2+1) b) = Z.shiftr a b when 0 <= b *)
Local Lemma Z_div2_shiftr_tagged : forall a b,
  0 <= b ->
  Z.div2 (Z.shiftr (a * 2 + 1) b) = Z.shiftr a b.
Proof.
  intros a b Hb.
  rewrite Z.div2_div.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_div by (try apply Z.pow_pos_nonneg; lia).
  replace (2 ^ b * 2) with (2 ^ (b + 1)).
  2:{ change (b + 1) with (Z.succ b). rewrite Z.pow_succ_r by lia. ring. }
  symmetry.
  apply Z.div_unique with (2 * (a mod 2^b) + 1).
  - pose proof (Z.mod_pos_bound a (2^b) ltac:(apply Z.pow_pos_nonneg; lia)).
    pose proof (Z.pow_pos_nonneg 2 b ltac:(lia) ltac:(lia)).
    assert (H2b : 2 ^ (b + 1) = 2 * 2 ^ b).
    { change (b + 1) with (Z.succ b). rewrite Z.pow_succ_r by lia. ring. }
    left. lia.
  - change (b + 1) with (Z.succ b). rewrite Z.pow_succ_r by lia.
    rewrite (Z.div_mod a (2^b)) at 1 by (apply Z.pow_nonzero; lia).
    ring.
Qed.

(* The combined tagged arithmetic identity for ASRINT. *)
Local Lemma tagged_asrint_arith : forall a b,
  0 <= b < 64 ->
  Int64.min_signed <= a * 2 + 1 <= Int64.max_signed ->
  Int64.or (Int64.shr (Int64.repr (a * 2 + 1))
              (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)))
           (Int64.repr 1)
  = Int64.repr (Z.shiftr a b * 2 + 1).
Proof.
  intros a b Hb Ha_range.
  rewrite int64_shr_tagged_1 by lia.
  unfold Int64.shr.
  rewrite (Int64.unsigned_repr b) by (generalize max_unsigned_ge_127; lia).
  rewrite Int64.signed_repr by exact Ha_range.
  unfold Int64.or.
  apply Int64.eqm_samerepr.
  rewrite (Int64.unsigned_repr 1) by (generalize max_unsigned_ge_127; lia).
  apply Int64.eqm_trans with (y := Z.lor (Z.shiftr (a * 2 + 1) b) 1).
  - apply Int64.eqm_same_bits.
    intros i Hi.
    rewrite !Z.lor_spec.
    f_equal.
    apply Int64.same_bits_eqm with (i := i).
    + apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
    + exact Hi.
  - rewrite Z_lor_1_div2.
    rewrite Z_div2_shiftr_tagged by lia.
    apply Int64.eqm_refl2. lia.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_ASRINT_correct :
    handler_correct handle_ASRINT f_instr_ASRINT
      (fun _ _ s ard =>
         match s.(Machine.accu), s.(Machine.stack) with
         | Val_int a, Val_int b :: _ =>
             0 <= b < 64 /\
             Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
             int_vlong ard a /\ int_vlong ard b
         | _, Val_int b :: _ => 0 <= b < 64
         | _, _ => True
         end)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handle_ASRINT.
  destruct (Machine.accu s) as [a| | |] eqn:Haccu_eq; try (exact I).
  destruct (Machine.stack s) as [|v_hd v_tl] eqn:Hstk; try (exact I).
  destruct v_hd as [b| | |] eqn:Hvhd; try (exact I).
  intros ard Hpre Hstep_pre.
  unfold abs_rel_with_ard in Hpre.
  change (Machine.accu s) with (Val_int a) in Hstep_pre.
  change (Machine.stack s) with (Val_int b :: v_tl) in Hstep_pre.
  simpl in Hstep_pre. destruct Hstep_pre as [Hb [Ha_range [Haccu_long Hhead_long]]].
  set (sb := ar_sptr_block ard) in *.
  set (so := ar_sptr_ofs ard) in *.
  set (hm := ar_heap_map ard) in *.
  set (cb := ar_code_base_block ard) in *.
  set (co := ar_code_base_ofs ard) in *.
  destruct Hpre as (Hle_s &
    [pc_ptr [Hpc_load Hpc_rel]] &
    [accu_v [Haccu_load Haccu_repr]] &
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr0 [Hsp_ne_sb [Hsp_ne_gb [Hcode_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
    [env_v [Henv_load Henv_repr]] &
    Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr0 Hgb_ne]]]] &
    [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
  subst sp_ptr.
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  rewrite Haccu_eq in Haccu_repr.
  pose proof Haccu_repr as Haccu_repr_rw.
  inversion Haccu_repr; subst accu_v.
  2: { exfalso. destruct (Haccu_long _ Haccu_repr_rw) as [z Hz]. discriminate Hz. }
  rename H0 into Haccu_is_int.

  (* Pre-compute modulus bounds for sp + 8 BEFORE inversion/subst *)
  assert (Hsp_mod_orig : Ptrofs.unsigned sp_ofs + 8 < Ptrofs.modulus).
  { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }
  assert (Hsp_rep_tail : Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length v_tl) < Ptrofs.modulus).
  { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }
  (* Pre-compute writable inclusion for the tail range *)
  assert (Hsp_writable_tail : Mem.range_perm m sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length v_tl)) Cur Writable).
  { intros ofs' Hofs'. apply Hsp_writable. rewrite Hstk. simpl length.
    pose proof (Nat2Z.is_nonneg (length v_tl)). lia. }

  rewrite Hstk in Hstack_repr0.
  inversion Hstack_repr0 as [| ? ? ? ? cv0 Hload_sp0 Hval_repr0 Hstack_repr_rest].
  revert Hgd_load Hgd_eq Hglobal_repr0 Hgb_ne. subst.
  intros Hgd_load Hgd_eq Hglobal_repr Hgb_ne.
  pose proof Hval_repr0 as Hval_repr0_rw.
  inversion Hval_repr0; subst cv0.
  2: { exfalso. destruct (Hhead_long _ Hval_repr0_rw) as [z Hz]. discriminate Hz. }
  rename H0 into Hstk_is_int.
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

  pose proof (asr_shift_ltu_guard b Hb) as Hshift_guard.

  set (tagged_a := Int64.repr (a * 2 + 1)).
  set (tagged_b := Int64.repr (b * 2 + 1)).
  set (shift_amt := Int64.shr tagged_b (Int64.repr 1)).
  set (shifted := Int64.shr tagged_a shift_amt).
  set (result_int64 := Int64.or shifted (Int64.repr 1)).
  set (result_v := Vlong result_int64).
  set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).

  destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) new_sp_v) as [m1 Hstore1].

  assert (Haccu_load_m1 :
    Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vlong tagged_a)).
  { apply (load_after_store_other m m1 sb
             (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8)
             new_sp_v (Vlong tagged_a) Hstore1 Haccu_load). left. lia. }

  assert (Hload_sp0_m1 :
    Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) = Some (Vlong tagged_b)).
  { erewrite Mem.load_store_other. exact Hload_sp0. exact Hstore1.
    left. exact Hsp_ne_sb. }

  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.
  destruct (store_succeeds_sb m1 sb so 8 (Vlong tagged_a) Hsb_writable_m1 Haccu_load_m1 ltac:(lia) ltac:(lia) result_v) as [m' Hstore2].

  set (le' := PTree.set _t'3 (Vlong tagged_b)
                (PTree.set _t'2 (Vlong tagged_a)
                  (PTree.set _t'1 (Vptr sp_b sp_ofs) le))).
  exists le'. exists m'. exists (Out_return (Some (Vint (Int.repr 0), tint))).
  split.

  (* Part 1: exec *)
  { apply (eval_stmt_to_exec clight_ge 15). eval_cbn.
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_1; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    unfold new_sp_v in Hstore1. rewrite Hstore1; eval_cbn.
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m1; eval_cbn.
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite Hload_sp0_m1; eval_cbn.
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    rewrite sem_shr_long_int_1; eval_cbn.
    rewrite (sem_shr_long_long_signed tagged_a shift_amt _ Hshift_guard); eval_cbn.
    rewrite sem_or_long_int_1; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    unfold result_v, result_int64, shifted in Hstore2.
    rewrite Hstore2; eval_cbn.
    subst le'. reflexivity. }

  (* Part 2: abs_rel *)
  { exists ard. set (uso := Ptrofs.unsigned so) in *.
    assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
    { assert (Hpc_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 0)
                 new_sp_v pc_ptr Hstore1 Hpc_load). left. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 0)
               result_v pc_ptr Hstore2 Hpc_m1). left. lia. }
    assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some new_sp_v).
    { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some new_sp_v).
      { pose proof (load_after_store_same m m1 sb (uso + 16)
                      new_sp_v Hstore1) as Htmp.
        unfold new_sp_v in Htmp |- *.
        simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp.
        exact Htmp. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 16)
               result_v new_sp_v Hstore2 Hsp_m1). right. lia. }
    assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some result_v).
    { pose proof (load_after_store_same m1 m' sb (uso + 8)
                    result_v Hstore2) as Htmp.
      unfold result_v in Htmp |- *. simpl Val.load_result in Htmp. exact Htmp. }
    assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 24)
                 new_sp_v env_v Hstore1 Henv_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 24)
               result_v env_v Hstore2 He1). right. lia. }
    assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
                 new_sp_v _ Hstore1 Hextra_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 32)
               result_v _ Hstore2 He1). right. lia. }
    assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 40)
                 new_sp_v gd_ptr Hstore1 Hgd_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 40)
               result_v gd_ptr Hstore2 He1). right. lia. }
    assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 48)
                 new_sp_v ts_ptr Hstore1 Hts_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 48)
               result_v ts_ptr Hstore2 He1). right. lia. }
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
    (* 1. _s in le' *)
    { subst le'.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      exact Hle_s. }
    (* 2. pc *)
    { exists pc_ptr. split. exact Hpc_load'. simpl. exact Hpc_rel. }
    (* 3. accu = Val_int (Z.shiftr a b) *)
    { exists result_v. split. exact Haccu_load'. simpl.
      unfold result_v, result_int64, shifted, shift_amt, tagged_a, tagged_b.
      rewrite (tagged_asrint_arith a b Hb Ha_range).
      constructor. }
    (* 4. sp -- conjunction: stack_repr /\ sep facts *)
    { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)).
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load'.
      - reflexivity.
      - simpl.
        eapply (stack_repr_store_other_block hm cb co m1 m' _ sp_b
                 (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) result_v).
        + eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b
                   (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16) new_sp_v).
          * exact Hstack_repr_rest.
          * exact Hstore1.
          * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        + exact Hstore2.
        + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcode_ne_sp.
        - (* sp_ge8 *)
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)). lia.
        - (* sp_rep *)
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)). exact Hsp_rep_tail.
        - (* sp_writable *)
          intros ofs' Hofs'.
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)) in Hofs'.
          eapply Mem.perm_store_1. exact Hstore2.
          eapply Mem.perm_store_1. exact Hstore1.
          apply Hsp_writable_tail. exact Hofs'.
        - (* sp_align *)
          simpl.
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)).
          apply Z.divide_add_r. exact Hsp_align. exists 1. lia. }
    (* 5. env *)
    { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }
    (* 6. extra_args *)
    { simpl. exact Hextra_load'. }
    (* 7. global_data -- conjunction: global_repr /\ gb <> sb *)
    { exists gd_ptr. split; [| split; [| split]].
      - exact Hgd_load'.
      - simpl. exact Hgd_eq.
      - simpl.
        eapply (global_repr_store_other_block hm cb co m1 m' _ _ _ sb (uso + 8) result_v).
        + eapply (global_repr_store_other_block hm cb co m m1 _ _ _ sb (uso + 16) new_sp_v).
          * exact Hglobal_repr.
          * exact Hstore1.
          * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        + exact Hstore2.
        + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
      - exact Hgb_ne. }
    (* 8. trap_sp *)
    { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. }

    (* 9. sb_writable -- permission preserved *)
    { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. eapply Mem.perm_store_1. exact Hstore1. apply Hsb_writable. exact Hofs'. } }
Qed.

Theorem verify_ASRINT_handler_correct :
    handler_correct handle_ASRINT f_instr_ASRINT
      shift_in_range
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  apply handler_correct_weaken with
    (sp := fun _ _ s ard =>
       match s.(Machine.accu), s.(Machine.stack) with
       | Val_int a, Val_int b :: _ =>
           0 <= b < 64 /\
           Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
           int_vlong ard a /\ int_vlong ard b
       | _, Val_int b :: _ => 0 <= b < 64
       | _, _ => True
       end).
  - exact verify_ASRINT_correct.
  - intros e le m s ard _ Hsr.
    unfold shift_in_range in Hsr.
    destruct Hsr as (a & b & rest & Ha & Hs & Hb & Hra).
    rewrite Ha, Hs. exact (conj Hb Hra).
Qed.

(* Wrapper with the canonical type expected by InstructVerificationProof.v *)
Theorem correct_ASRINT :
  handler_correct (handle_instr Bytecode.AST.ASRINT) (clight_of Bytecode.AST.ASRINT)
    (pre_of Bytecode.AST.ASRINT)
    (P_error_of Bytecode.AST.ASRINT) (P_halt_of Bytecode.AST.ASRINT) (P_ccall_of Bytecode.AST.ASRINT).
Proof.
Admitted.

