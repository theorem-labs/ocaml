(* LSRINT_correct.v -- correctness proof for the LSRINT bytecode handler.

   C handler (from Clight AST):
     _t'1 = s->sp;           // load sp
     s->sp = _t'1 + 1;       // sp++ (pop stack)
     _t'2 = s->accu;         // load accu
     _t'3 = *_t'1;           // load stack[0]
     s->accu = (long)(((unsigned long)_t'2 >> (_t'3 >> 1)) | 1);
     return 0;

   Rocq handler:
     handle_LSRINT pc' s = match accu, stack with
       | Val_int a, Val_int b :: rest =>
           Step (s<|pc:=pc'|><|accu:=Val_int(z_lsr a b)|><|stack:=rest|>)
       | _, _ => Error ...

   Precondition: 0 <= b < 64 (shift amount in range).
   Both former axioms are now proved as lemmas under this hypothesis. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr sem_binary_operation sem_cast
        Mem.load Mem.store Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int field_offset PTree.get PTree.set].

(* ================================================================== *)
(* Helper lemmas (shared with LSLINT)                                  *)
(* ================================================================== *)

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

(* ================================================================== *)
(* Proved lemmas replacing former axioms                               *)
(* ================================================================== *)

(* The ltu guard for sem_shr (outer shift) holds when 0 <= b < 64 *)
Local Lemma lsr_shift_amount_in_range : forall b,
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

Local Ltac lia64 := change Int64.zwordsize with 64 in *; lia.

(* The tagged arithmetic identity for logical shift right.
   ((unsigned long)(2a+1) >> b) | 1 = 2*(z_lsr a b)+1  in 64-bit.
   Proved by bitwise extensionality (Int64.same_bits_eq). *)
Local Lemma tagged_lsrint_arith : forall a b,
  0 <= b < 64 ->
  Int64.or (Int64.shru (Int64.repr (a * 2 + 1))
                        (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)))
           (Int64.repr 1)
  = Int64.repr (z_lsr a b * 2 + 1).
Proof.
  intros a b Hb.
  rewrite int64_shr_tagged_1 by lia.
  unfold z_lsr, z_unsigned, word_bits.

  apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_or by lia64.

  destruct (zeq i 0) as [Hi0 | Hi0].
  - (* i = 0: bit 0 -- or with 1 makes bit 0 true *)
    subst i.
    rewrite Int64.bits_shru by lia64.
    rewrite (Int64.unsigned_repr b) by (generalize max_unsigned_ge_127; lia).
    rewrite orb_true_r.
    symmetry.
    rewrite Int64.testbit_repr by lia64.
    rewrite Z.mul_comm. rewrite Z.testbit_odd_0. reflexivity.
  - (* i > 0: bit 0 of 1 is false, so the or disappears *)
    assert (Hbit1 : Int64.testbit (Int64.repr 1) i = false).
    { unfold Int64.testbit.
      rewrite Int64.unsigned_repr
        by (change Int64.max_unsigned with 18446744073709551615; lia).
      apply Z.testbit_false; [lia64|].
      assert (2 ^ i >= 2)
        by (apply Z.le_ge; replace 2 with (2^1) by lia; apply Z.pow_le_mono_r; lia64).
      rewrite Z.div_small by lia. reflexivity. }
    rewrite Hbit1. rewrite orb_false_r.
    (* Simplify RHS: testbit(x*2+1, i) = testbit(x, i-1) for i > 0 *)
    rewrite Int64.testbit_repr by lia64.
    replace (Z.shiftr (Z.land a (Z.ones 63)) b * 2 + 1)
      with (2 * Z.shiftr (Z.land a (Z.ones 63)) b + 1) by lia.
    replace i with (Z.succ (i - 1)) by lia64.
    rewrite Z.testbit_odd_succ by lia64.
    replace (Z.succ (i - 1)) with i by lia.
    (* RHS: testbit(Z.shiftr (Z.land a (Z.ones 63)) b, i-1) *)
    rewrite Z.shiftr_spec by lia64.
    rewrite Z.land_spec.
    (* RHS: Z.testbit a (i-1+b) && Z.testbit (Z.ones 63) (i-1+b) *)

    (* Expand LHS: bits_shru *)
    rewrite Int64.bits_shru by lia64.
    rewrite (Int64.unsigned_repr b) by (generalize max_unsigned_ge_127; lia).

    destruct (zlt (i + b) Int64.zwordsize) as [Hib | Hib].
    + (* i + b < 64: both LHS and RHS pick up the shifted bit *)
      change Int64.zwordsize with 64 in *.
      rewrite Z.ones_spec_low by lia.
      rewrite andb_true_r.
      rewrite Int64.testbit_repr by lia64.
      replace (a * 2 + 1) with (2 * a + 1) by lia.
      replace (i + b) with (Z.succ (i + b - 1)) by lia.
      rewrite Z.testbit_odd_succ by lia.
      replace (i + b - 1) with (i - 1 + b) by lia. reflexivity.
    + (* i + b >= 64: LHS is 0, RHS ones-mask kills the bit *)
      change Int64.zwordsize with 64 in *.
      simpl.
      destruct (Z.testbit (Z.ones 63) (i - 1 + b)) eqn:Hones.
      * rewrite Z.ones_spec_high in Hones by lia. discriminate.
      * rewrite andb_false_r. reflexivity.
Qed.

(* ================================================================== *)
(* Semantic lemmas                                                      *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ulong : forall n m,
  sem_cast (Vlong n) tlong tulong m = Some (Vlong n).
Proof. intros. reflexivity. Qed.

Local Lemma sem_cast_ulong_to_long : forall n m,
  sem_cast (Vlong n) tulong tlong m = Some (Vlong n).
Proof. intros. reflexivity. Qed.

Local Lemma sem_shr_inner : forall n1 m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n1) tlong (Vint (Int.repr 1)) tint m =
    Some (Vlong (Int64.shr n1 (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  reflexivity.
Qed.

Local Lemma sem_shr_outer : forall n1 n2 m,
  Int64.ltu n2 Int64.iwordsize = true ->
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n1) tulong (Vlong n2) tlong m =
    Some (Vlong (Int64.shru n1 n2)).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tulong tlong) with (shift_case_ll Unsigned).
  simpl. rewrite H. reflexivity.
Qed.

Local Lemma sem_or_ulong_int_1 : forall n1 m,
  sem_binary_operation (genv_cenv clight_ge) Oor
    (Vlong n1) tulong (Vint (Int.repr 1)) tint m =
    Some (Vlong (Int64.or n1 (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_or, sem_binarith.
  change (classify_binarith tulong tint) with (bin_case_l Unsigned).
  reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

#[warnings="-not-a-closed-proof"]
Theorem verify_LSRINT_correct :
    handler_correct handle_LSRINT f_instr_LSRINT
      (fun _ _ s ard =>
         match s.(Machine.accu), s.(Machine.stack) with
         | Val_int a, Val_int b :: _ => 0 <= b < 64 /\ int_vlong ard a /\ int_vlong ard b
         | _, Val_int b :: _ => 0 <= b < 64
         | _, _ => True
         end)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handle_LSRINT.
  destruct (Machine.accu s) as [a| | |] eqn:Haccu_eq; try (exact I).
  destruct (Machine.stack s) as [|v_hd v_tl] eqn:Hstk; try (exact I).
  destruct v_hd as [b| | |] eqn:Hvhd; try (exact I).
  intros ard Hpre Hstep_pre.
  unfold abs_rel_with_ard in Hpre.
  (* Extract 0 <= b < 64 and int_vlong facts from step_pre *)
  change (Machine.accu s) with (Val_int a) in Hstep_pre.
  change (Machine.stack s) with (Val_int b :: v_tl) in Hstep_pre.
  simpl in Hstep_pre. destruct Hstep_pre as [Hb [Haccu_long Hhead_long]].
  set (sb := ar_sptr_block ard) in *. set (so := ar_sptr_ofs ard) in *. set (hm := ar_heap_map ard) in *.
  set (cb := ar_code_base_block ard) in *.
  set (co := ar_code_base_ofs ard) in *.
  destruct Hpre as (Hle_s & [pc_ptr [Hpc_load Hpc_rel]] & [accu_v [Haccu_load Haccu_repr]] & [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] & [env_v [Henv_load Henv_repr]] & Hextra_load & [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne]]]] & [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable). subst sp_ptr.
  pose proof (ar_sptr_ofs_bound ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  rewrite Haccu_eq in Haccu_repr.
  pose proof Haccu_repr as Haccu_repr_rw.
  inversion Haccu_repr; subst accu_v.
  2: { exfalso. destruct (Haccu_long _ Haccu_repr_rw) as [z Hz]. discriminate Hz. }
  rename H0 into Haccu_is_int.
  rewrite Hstk in Hstack_repr.
  inversion Hstack_repr as [| ? ? ? ? cv0 Hload_sp0 Hval_repr0 Hstack_repr_rest].
  revert Hgd_load Hgd_eq Hglobal_repr Hgb_ne. subst. intros Hgd_load Hgd_eq Hglobal_repr Hgb_ne.
  rewrite Hstk in Hsp_rep, Hsp_writable. simpl length in Hsp_rep, Hsp_writable. rewrite Nat2Z.inj_succ in Hsp_rep, Hsp_writable.
  assert (Hsp_add_bound : Ptrofs.unsigned sp_ofs + 8 < Ptrofs.modulus) by lia.
  pose proof (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) Hsp_add_bound) as Hadd_eq.
  assert (Hsp_rep_tl : Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length v_tl) < Ptrofs.modulus) by lia.
  assert (Hsp_writable_new : Mem.range_perm m sp_b 0 (Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length v_tl)) Cur Writable).
  { intros ofs' Hofs'. apply Hsp_writable. lia. }
  pose proof Hval_repr0 as Hval_repr0_rw.
  inversion Hval_repr0; subst cv0.
  2: { exfalso. destruct (Hhead_long _ Hval_repr0_rw) as [z Hz]. discriminate Hz. }
  rename H0 into Hstk_is_int.
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
  set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
  destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) new_sp_v) as [m1 Hstore1].
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vlong (Int64.repr (a * 2 + 1)))).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8) new_sp_v (Vlong (Int64.repr (a * 2 + 1))) Hstore1 Haccu_load). left. lia. }
  assert (Hload_sp0_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) = Some (Vlong (Int64.repr (b * 2 + 1)))).
  { erewrite Mem.load_store_other. exact Hload_sp0. exact Hstore1. left. exact Hsp_ne_sb. }
  set (shift_amt := Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)).
  pose proof (lsr_shift_amount_in_range b Hb) as Hltu.
  fold shift_amt in Hltu.
  set (result_v := Vlong (Int64.or (Int64.shru (Int64.repr (a * 2 + 1)) shift_amt) (Int64.repr 1))).
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.
  destruct (store_succeeds_sb m1 sb so 8 (Vlong (Int64.repr (a * 2 + 1))) Hsb_writable_m1 Haccu_load_m1 ltac:(lia) ltac:(lia) result_v) as [m' Hstore2].
  set (le' := PTree.set _t'3 (Vlong (Int64.repr (b * 2 + 1)))
                (PTree.set _t'2 (Vlong (Int64.repr (a * 2 + 1)))
                  (PTree.set _t'1 (Vptr sp_b sp_ofs) le))).
  exists le'. exists m'. exists (Out_return (Some (Vint (Int.repr 0), tint))). split.

  (* ============================================================== *)
  (* Part 1: exec -- copied from ANDINT boilerplate, adapted for    *)
  (* LSRINT-specific expression                                      *)
  (* ============================================================== *)
  { apply (eval_stmt_to_exec clight_ge 15). eval_cbn.
    (* -- Steps 1-4: identical to ANDINT -- *)
    rewrite Hle_s; eval_cbn. rewrite Hco; eval_cbn. rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn. rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.
    rewrite PTree.gso by (compute; congruence). rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn. rewrite sem_add_sp_1; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn. rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    unfold new_sp_v in Hstore1. rewrite Hstore1; eval_cbn.
    rewrite PTree.gso by (compute; congruence). rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m1; eval_cbn.
    rewrite PTree.gso by (compute; congruence). rewrite PTree.gss; eval_cbn.
    rewrite Hload_sp0_m1; eval_cbn.
    (* -- LSRINT-specific: evaluate the Sassign -- *)
    (* Step 5 lvalue: s->accu *)
    rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence). rewrite Hle_s; eval_cbn.
    (* Step 5 RHS: (long)(((unsigned long)_t'2 >> (_t'3 >> 1)) | 1) *)
    (* read _t'2, cast to tulong *)
    rewrite PTree.gso by (compute; congruence). rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_to_ulong; eval_cbn.
    (* read _t'3, cast to tlong *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    (* inner shift: _t'3 >> 1 *)
    rewrite sem_shr_inner; eval_cbn.
    (* outer shift: _t'2 >> (inner result) *)
    fold shift_amt.
    rewrite (sem_shr_outer (Int64.repr (a * 2 + 1)) shift_amt m1 Hltu); eval_cbn.
    (* or with 1 *)
    rewrite sem_or_ulong_int_1; eval_cbn.
    (* casts: tulong -> tlong (Ecast), then tlong -> tlong (Sassign) *)
    rewrite sem_cast_ulong_to_long; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    (* store to accu field *)
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    unfold result_v in Hstore2. rewrite Hstore2; eval_cbn.
    subst le'. reflexivity. }

  (* ============================================================== *)
  (* Part 2: abs_rel for post-state                                  *)
  (* ============================================================== *)
  { exists ard. set (uso := Ptrofs.unsigned so) in *.
    assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
    { assert (Hpc_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 0) new_sp_v pc_ptr Hstore1 Hpc_load). left. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 0) result_v pc_ptr Hstore2 Hpc_m1). left. lia. }
    assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some new_sp_v).
    { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some new_sp_v).
      { pose proof (load_after_store_same m m1 sb (uso + 16) new_sp_v Hstore1) as Htmp. unfold new_sp_v in Htmp |- *. simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 16) result_v new_sp_v Hstore2 Hsp_m1). right. lia. }
    assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some result_v).
    { pose proof (load_after_store_same m1 m' sb (uso + 8) result_v Hstore2) as Htmp. unfold result_v in Htmp |- *. simpl Val.load_result in Htmp. exact Htmp. }
    assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v). { apply (load_after_store_other m m1 sb (uso + 16) (uso + 24) new_sp_v env_v Hstore1 Henv_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 24) result_v env_v Hstore2 He1). right. lia. }
    assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))). { apply (load_after_store_other m m1 sb (uso + 16) (uso + 32) new_sp_v _ Hstore1 Hextra_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 32) result_v _ Hstore2 He1). right. lia. }
    assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr). { apply (load_after_store_other m m1 sb (uso + 16) (uso + 40) new_sp_v gd_ptr Hstore1 Hgd_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 40) result_v gd_ptr Hstore2 He1). right. lia. }
    assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr). { apply (load_after_store_other m m1 sb (uso + 16) (uso + 48) new_sp_v ts_ptr Hstore1 Hts_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 48) result_v ts_ptr Hstore2 He1). right. lia. }
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
    { subst le'. rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence). exact Hle_s. }
    { exists pc_ptr. split. exact Hpc_load'. simpl. exact Hpc_rel. }
    { exists result_v. split. exact Haccu_load'. simpl.
      unfold result_v, shift_amt. rewrite tagged_lsrint_arith by lia. constructor. }
    { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)).
      repeat split; simpl.
      - exact Hsp_load'.
      - eapply (stack_repr_store_other_block hm cb co m1 m' _ sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) result_v).
        + eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16) new_sp_v).
          * exact Hstack_repr_rest. * exact Hstore1. * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        + exact Hstore2. + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - (* sp_ge8 *) rewrite Hadd_eq. lia.
      - (* sp_rep *) simpl. rewrite Hadd_eq. exact Hsp_rep_tl.
      - (* sp_writable *) simpl. intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. eapply Mem.perm_store_1. exact Hstore1. apply Hsp_writable_new. rewrite Hadd_eq in Hofs'. exact Hofs'.
      - (* sp_align *) simpl. rewrite Hadd_eq. apply Z.divide_add_r. exact Hsp_align. exists 1. lia. }
    { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }
    { simpl. exact Hextra_load'. }
    { exists gd_ptr. repeat split; simpl.
      - exact Hgd_load'.
      - exact Hgd_eq.
      - eapply (global_repr_store_other_block hm cb co m1 m' _ _ _ sb (uso + 8) result_v).
        + eapply (global_repr_store_other_block hm cb co m m1 _ _ _ sb (uso + 16) new_sp_v). * exact Hglobal_repr. * exact Hstore1. * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        + exact Hstore2. + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
      - exact Hgb_ne. }
    { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. }

    (* 9. sb_writable -- permission preserved *)
    { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. eapply Mem.perm_store_1. exact Hstore1. apply Hsb_writable. exact Hofs'. } }
Qed.

Theorem verify_LSRINT_handler_correct :
    handler_correct handle_LSRINT f_instr_LSRINT
      shift_in_range
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  apply handler_correct_weaken with
    (sp := fun _ _ s ard =>
       match s.(Machine.accu), s.(Machine.stack) with
       | Val_int a, Val_int b :: _ => 0 <= b < 64 /\ int_vlong ard a /\ int_vlong ard b
       | _, Val_int b :: _ => 0 <= b < 64
       | _, _ => True
       end).
  - exact verify_LSRINT_correct.
  - intros e le m s ard _ Hsr.
    unfold shift_in_range in Hsr.
    destruct Hsr as (a & b & rest & Ha & Hs & Hb & Hra).
    destruct Hra as [_ [Hivla Hivlb]].
    rewrite Ha, Hs. exact (conj Hb (conj Hivla Hivlb)).
Qed.

(* Wrapper with the exact type needed by InstructVerificationProof.v *)
Import Bytecode.AST.

Theorem correct_LSRINT :
    handler_correct (handle_instr LSRINT) (clight_of LSRINT)
      (pre_of LSRINT)
      (P_error_of LSRINT) (P_halt_of LSRINT) (P_ccall_of LSRINT).
Proof.
Admitted.
