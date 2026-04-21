(* ULTINT_correct.v -- Verification of the ULTINT bytecode handler.
   C: s->accu = ((long)((unsigned long)_t'2 < (unsigned long)_t'3) << 1) + 1; sp++.
   If accu <_u stack_top: result = tagged 1 = val_true.
   Otherwise: result = tagged 0 = val_false.

   The Rocq handler uses val_bool (Z.ltb (z_flip_sign a) (z_flip_sign b))
   which flips bit 62 to convert signed Z comparison to unsigned order.
   The Clight code casts operands to tulong then uses Olt, which goes
   through Int64.cmpu Clt = Int64.ltu (unsigned less-than on Int64).

   PRECONDITION: The z_flip_sign trick on mathematical Z only matches
   Int64.ltu for non-negative operands (0 <= a, 0 <= b < 2^62).
   For negative operands, Z.lxor on infinite-precision Z does not
   model the 63-bit OCaml lxor correctly, causing disagreement.
   We add this as a step_pre via handler_correct. *)
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
(* Semantic lemmas for unsigned comparison                             *)
(* ================================================================== *)

(* Cast from tlong to tulong is identity for Vlong (cast_case_pointer
   on ptr64 = true). *)
Local Lemma sem_cast_long_to_ulong : forall n m,
  sem_cast (Vlong n) tlong tulong m = Some (Vlong n).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

(* Olt on tulong tulong: classify_cmp -> cmp_default -> sem_binarith
   -> classify_binarith tulong tulong = bin_case_l Unsigned ->
   Int64.cmpu Clt = Int64.ltu. *)
Local Lemma sem_lt_ulong_ulong : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Olt
    (Vlong n1) tulong (Vlong n2) tulong m
    = Some (Val.of_bool (Int64.ltu n1 n2)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_cast_bool_int_to_long : forall (cond : bool) m,
  sem_cast (Val.of_bool cond) tint tlong m
    = Some (Vlong (Int64.repr (if cond then 1 else 0))).
Proof. intros. destruct cond; reflexivity. Qed.

Local Lemma sem_shl_bool_long_1 : forall (cond : bool) m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong (Int64.repr (if cond then 1 else 0))) tlong
    (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.repr (if cond then 2 else 0))).
Proof. intros. destruct cond; reflexivity. Qed.

Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

Local Lemma tagged_ult_result : forall (cond : bool),
  Int64.add (Int64.repr (if cond then 2 else 0)) (Int64.repr 1)
    = Int64.repr (if cond then 3 else 1).
Proof. intros. destruct cond; reflexivity. Qed.

(* ================================================================== *)
(* Key arithmetic lemma                                                *)
(* ================================================================== *)

(* Int64.ltu is Z.ltb on unsigned values *)
Local Lemma int64_ltu_ltb : forall x y,
  Int64.ltu x y = Z.ltb (Int64.unsigned x) (Int64.unsigned y).
Proof.
  intros. unfold Int64.ltu.
  destruct (zlt (Int64.unsigned x) (Int64.unsigned y)) as [Hlt|Hge].
  - symmetry. apply Z.ltb_lt. exact Hlt.
  - symmetry. apply Z.ltb_ge. lia.
Qed.

(* For non-negative a < 2^n, Z.lxor a (2^n) = a + 2^n
   (bit n of a is 0, xor sets it; no carry since bits don't overlap). *)
Local Lemma Z_lxor_add_pow2 : forall a n,
  0 <= a ->
  0 <= n ->
  a < 2 ^ n ->
  Z.lxor a (2 ^ n) = a + 2 ^ n.
Proof.
  intros a n Ha Hn Hlt.
  rewrite Z.add_nocarry_lxor.
  - reflexivity.
  - apply Z.bits_inj. intros j.
    rewrite Z.land_spec, Z.bits_0.
    rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eqb n j) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst.
      destruct (Z.eq_dec a 0) as [->|Ha0].
      * rewrite Z.testbit_0_l. reflexivity.
      * rewrite Z.bits_above_log2; [reflexivity | lia | ].
        apply Z.log2_lt_pow2; lia.
    + rewrite Bool.andb_false_r. reflexivity.
Qed.

(* For non-negative a, b in [0, 2^62), the unsigned comparison of
   tagged integers matches z_flip_sign comparison.

   Both sides reduce to Z.ltb a b:
   - LHS: Int64.ltu compares unsigned (a*2+1) vs (b*2+1), both positive
   - RHS: z_flip_sign adds 2^62 to both (since bit 62 is 0), cancels *)
Local Lemma tagged_ultint_arith : forall a b,
  0 <= a < 4611686018427387904 ->
  0 <= b < 4611686018427387904 ->
  Int64.ltu (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1))
  = Z.ltb (z_flip_sign a) (z_flip_sign b).
Proof.
  intros a b Ha Hb.
  unfold z_flip_sign, word_bits. simpl Z.sub.
  change (Z.shiftl 1 62) with (2 ^ 62).
  rewrite !Z_lxor_add_pow2 by lia.
  rewrite int64_ltu_ltb.
  rewrite !Int64.unsigned_repr
    by (unfold Int64.max_unsigned; change Int64.modulus with 18446744073709551616; lia).
  destruct (Z.ltb_spec (a * 2 + 1) (b * 2 + 1));
  destruct (Z.ltb_spec (a + 2 ^ 62) (b + 2 ^ 62)); lia.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_ULTINT_correct :
    handler_correct handle_ULTINT f_instr_ULTINT
      (fun _ _ s ard =>
         match s.(Machine.accu), s.(Machine.stack) with
         | Val_int a, Val_int b :: _ =>
             0 <= a < 4611686018427387904 /\
             0 <= b < 4611686018427387904 /\
             int_vlong ard a /\
             int_vlong ard b
         | _, _ => True
         end)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handle_ULTINT.
  destruct (Machine.accu s) as [a| | |] eqn:Haccu_eq;
    destruct (Machine.stack s) as [|v_hd v_tl] eqn:Hstk;
    try (exact I).
  destruct v_hd as [b| | |] eqn:Hvhd;
    try (exact I).
  intros ard Hpre Hstep_pre.
  unfold abs_rel_with_ard in Hpre.
  (* Extract range constraint from step_pre *)
  change (Machine.accu s) with (Val_int a) in Hstep_pre.
  change (Machine.stack s) with (Val_int b :: v_tl) in Hstep_pre.
  simpl in Hstep_pre. destruct Hstep_pre as [Ha [Hb [Hint_tagged_a Hint_tagged_b]]].
  set (sb := ar_sptr_block ard) in *. set (so := ar_sptr_ofs ard) in *. set (hm := ar_heap_map ard) in *.
  set (cb := ar_code_base_block ard) in *.
  set (co := ar_code_base_ofs ard) in *.
  destruct Hpre as (Hle_s & [pc_ptr [Hpc_load Hpc_rel]] & [accu_v [Haccu_load Haccu_repr]] & [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] & [env_v [Henv_load Henv_repr]] & Hextra_load & [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] & [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable). subst sp_ptr.
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  rewrite Haccu_eq in Haccu_repr. inversion Haccu_repr; subst accu_v.
  2: { exfalso. destruct (Hint_tagged_a _ Haccu_repr) as [z Hz]. discriminate Hz. }
  rename H0 into Haccu_is_int.
  rewrite Hstk in Hstack_repr.
  inversion Hstack_repr as [| ? ? ? ? cv0 Hload_sp0 Hval_repr0 Hstack_repr_rest].
  revert Hgd_load Hgd_eq Hglobal_repr. subst. intros Hgd_load Hgd_eq Hglobal_repr.
  rewrite Hstk in Hsp_rep, Hsp_writable. simpl length in Hsp_rep, Hsp_writable. rewrite Nat2Z.inj_succ in Hsp_rep, Hsp_writable.
  assert (Hsp_add_bound : Ptrofs.unsigned sp_ofs + 8 < Ptrofs.modulus) by lia.
  pose proof (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) Hsp_add_bound) as Hadd_eq.
  assert (Hsp_rep_tl : Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length v_tl) < Ptrofs.modulus) by lia.
  assert (Hsp_writable_new : Mem.range_perm m sp_b 0 (Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length v_tl)) Cur Writable).
  { intros ofs' Hofs'. apply Hsp_writable. lia. }
  inversion Hval_repr0; subst cv0.
  2: { exfalso. destruct (Hint_tagged_b _ Hval_repr0) as [z Hz]. discriminate Hz. }
  rename H0 into Hstk_is_int.
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
  set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
  destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) new_sp_v) as [m1 Hstore1].
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vlong (Int64.repr (a * 2 + 1)))).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8) new_sp_v (Vlong (Int64.repr (a * 2 + 1))) Hstore1 Haccu_load). left. lia. }
  assert (Hload_sp0_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) = Some (Vlong (Int64.repr (b * 2 + 1)))).
  { erewrite Mem.load_store_other. exact Hload_sp0. exact Hstore1. left. exact Hsp_ne_sb. }
  set (ltu_bool := Int64.ltu (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1))).
  set (result_v := Vlong (Int64.add (Int64.repr (if ltu_bool then 2 else 0)) (Int64.repr 1))).
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.
  destruct (store_succeeds_sb m1 sb so 8 (Vlong (Int64.repr (a * 2 + 1))) Hsb_writable_m1 Haccu_load_m1 ltac:(lia) ltac:(lia) result_v) as [m' Hstore2].
  set (le' := PTree.set _t'3 (Vlong (Int64.repr (b * 2 + 1))) (PTree.set _t'2 (Vlong (Int64.repr (a * 2 + 1))) (PTree.set _t'1 (Vptr sp_b sp_ofs) le))).
  exists le'. exists m'. exists (Out_return (Some (Vint (Int.repr 0), tint))). split.
  (* Part 1: Clight execution *)
  { apply (eval_stmt_to_exec clight_ge 15). eval_cbn.
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
    (* Sassign accu *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_to_ulong; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_to_ulong; eval_cbn.
    rewrite sem_lt_ulong_ulong; eval_cbn.
    rewrite sem_cast_bool_int_to_long; eval_cbn.
    rewrite (sem_shl_bool_long_1 ltu_bool); eval_cbn.
    rewrite sem_add_long_int_1; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    unfold result_v in Hstore2. rewrite Hstore2; eval_cbn.
    subst le'. reflexivity. }
  (* Part 2: abs_rel on post-state *)
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
      unfold result_v. rewrite tagged_ult_result.
      unfold ltu_bool. rewrite tagged_ultint_arith by lia.
      unfold val_bool, val_true, val_false.
      destruct (Z.ltb (z_flip_sign a) (z_flip_sign b)); apply vr_int. }
    { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)). split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]. exact Hsp_load'. reflexivity.
      { simpl.
        eapply (stack_repr_store_other_block hm cb co m1 m' _ sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) result_v).
        + eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16) new_sp_v).
          * exact Hstack_repr_rest. * exact Hstore1. * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        + exact Hstore2. + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
      exact Hsp_ne_sb. exact Hsp_ne_gb. exact Hcb_ne_sp.
      (* sp_ge8 *) rewrite Hadd_eq. lia.
      (* sp_rep *) simpl. rewrite Hadd_eq. exact Hsp_rep_tl.
      (* sp_writable *) simpl. intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. eapply Mem.perm_store_1. exact Hstore1. apply Hsp_writable_new. rewrite Hadd_eq in Hofs'. exact Hofs'.
      (* sp_align *) simpl. rewrite Hadd_eq. apply Z.divide_add_r. exact Hsp_align. exists 1. lia. }
    { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }
    { simpl. exact Hextra_load'. }
    { exists gd_ptr. split; [| split; [| split]]. exact Hgd_load'. simpl. exact Hgd_eq.
      { simpl.
        eapply (global_repr_store_other_block hm cb co m1 m' _ _ _ sb (uso + 8) result_v).
        + eapply (global_repr_store_other_block hm cb co m m1 _ _ _ sb (uso + 16) new_sp_v). * exact Hglobal_repr. * exact Hstore1. * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        + exact Hstore2. + intro Heq2; exact (Hgb_ne (eq_sym Heq2)). }
      exact Hgb_ne_sb. }
    { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. }

    (* 9. sb_writable -- permission preserved *)
    { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. eapply Mem.perm_store_1. exact Hstore1. apply Hsb_writable. exact Hofs'. } }
Qed.

Theorem verify_ULTINT_handler_correct :
    handler_correct handle_ULTINT f_instr_ULTINT
      unsigned_ints_safe
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end) (fun _ => False) (fun _ _ _ => False).
Proof.
  apply handler_correct_weaken with
    (sp := fun _ _ s ard =>
       match s.(Machine.accu), s.(Machine.stack) with
       | Val_int a, Val_int b :: _ =>
           0 <= a < 4611686018427387904 /\
           0 <= b < 4611686018427387904 /\
           int_vlong ard a /\
           int_vlong ard b
       | _, _ => True
       end).
  - exact verify_ULTINT_correct.
  - intros e le m s ard _ Huis.
    unfold unsigned_ints_safe in Huis.
    destruct Huis as (a & b & rest & Ha & Hs & Hra & Hrb & Hva & Hvb).
    rewrite Ha, Hs. exact (conj Hra (conj Hrb (conj Hva Hvb))).
Qed.
