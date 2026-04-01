(* UGEINT_correct.v -- Verification of the UGEINT bytecode handler.
   C: s->accu = ((long)((unsigned long)_t'2 >= (unsigned long)_t'3) << 1) + 1; sp++.
   Rocq: val_bool (Z.geb (z_flip_sign a) (z_flip_sign b)).
   The arithmetic lemma is PROVED under OCaml 63-bit int range.
   NO AXIOMS. *)
From Stdlib Require Import ZArith List Strings.String PeanoNat Lia Bool.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
Require Import instruct_handlers InstructSpec StepToBigstep HandlerLemmas.

Open Scope Z_scope.

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr sem_binary_operation sem_cast
        Mem.load Mem.store Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int field_offset PTree.get PTree.set].

(* ================================================================== *)
(* Semantic lemmas for Clight evaluation                               *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ulong : forall n m,
  sem_cast (Vlong n) tlong tulong m = Some (Vlong n).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma sem_ge_ulong_ulong : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Oge
    (Vlong n1) tulong (Vlong n2) tulong m
    = Some (Val.of_bool (negb (Int64.ltu n1 n2))).
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

Local Lemma tagged_uge_result : forall (cond : bool),
  Int64.add (Int64.repr (if cond then 2 else 0)) (Int64.repr 1)
    = Int64.repr (if cond then 3 else 1).
Proof. intros. destruct cond; reflexivity. Qed.

(* ================================================================== *)
(* Z.lxor / z_flip_sign arithmetic                                    *)
(* ================================================================== *)

Local Lemma testbit62_nonneg : forall a : Z,
  0 <= a < 4611686018427387904 ->
  Z.testbit a 62 = false.
Proof.
  intros a Ha.
  apply Z.bits_above_log2; try lia.
  destruct (Z.eq_dec a 0) as [->|Hne].
  - simpl. lia.
  - apply Z.log2_lt_pow2; lia.
Qed.

Local Lemma testbit62_neg : forall a : Z,
  -4611686018427387904 <= a < 0 ->
  Z.testbit a 62 = true.
Proof.
  intros a Ha.
  apply Z.bits_above_log2_neg; try lia.
  destruct (Z.eq_dec (Z.pred (-a)) 0) as [He|Hne].
  - rewrite He. simpl. lia.
  - assert (0 < Z.pred (-a)) by lia.
    apply Z.log2_lt_pow2; lia.
Qed.

Local Lemma land_pow2_zero : forall a n : Z,
  0 <= n ->
  Z.testbit a n = false ->
  Z.land a (2^n) = 0.
Proof.
  intros a n Hn Hbit.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec i n) as [->|Hne].
  - rewrite Hbit. reflexivity.
  - rewrite Z.pow2_bits_false by auto. rewrite Bool.andb_false_r. reflexivity.
Qed.

Local Lemma lxor_pow2_add : forall a n : Z,
  0 <= a -> 0 <= n ->
  Z.testbit a n = false ->
  Z.lxor a (2^n) = a + 2^n.
Proof.
  intros a n Ha Hn Hbit.
  symmetry. apply Z.add_nocarry_lxor.
  apply land_pow2_zero; auto.
Qed.

Local Lemma lxor_neg_lnot : forall a b : Z,
  a < 0 ->
  Z.lxor a b = Z.lnot (Z.lxor (Z.lnot a) b).
Proof.
  intros a b Ha.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec, Z.lnot_spec by lia.
  rewrite Z.lxor_spec, Z.lnot_spec by lia.
  destruct (Z.testbit a n); destruct (Z.testbit b n); reflexivity.
Qed.

Local Lemma z_flip_sign_nonneg_eq : forall a : Z,
  0 <= a < 4611686018427387904 ->
  z_flip_sign a = a + 4611686018427387904.
Proof.
  intros a Ha.
  unfold z_flip_sign, word_bits.
  change (Z.shiftl 1 (63 - 1)) with 4611686018427387904.
  change 4611686018427387904 with (2^62) at 1.
  rewrite lxor_pow2_add; try lia.
  apply testbit62_nonneg; lia.
Qed.

Local Lemma z_flip_sign_neg_eq : forall a : Z,
  -4611686018427387904 <= a < 0 ->
  z_flip_sign a = a - 4611686018427387904.
Proof.
  intros a Ha.
  unfold z_flip_sign, word_bits.
  change (Z.shiftl 1 (63 - 1)) with 4611686018427387904.
  change 4611686018427387904 with (2^62) at 1.
  rewrite lxor_neg_lnot by lia.
  rewrite lxor_pow2_add.
  - unfold Z.lnot. lia.
  - unfold Z.lnot. lia.
  - lia.
  - apply testbit62_nonneg. unfold Z.lnot. lia.
Qed.

(* ================================================================== *)
(* Main arithmetic lemma                                               *)
(* ================================================================== *)

Definition ocaml_int_range (z : Z) : Prop :=
  -4611686018427387904 <= z < 4611686018427387904.

Local Lemma Z_geb_negb_ltb : forall a b, Z.geb a b = negb (Z.ltb a b).
Proof.
  intros. destruct (Z.geb a b) eqn:Hge; destruct (Z.ltb a b) eqn:Hlt;
    try reflexivity;
    rewrite Z.geb_leb in Hge;
    first [rewrite Z.leb_le in Hge | rewrite Z.leb_gt in Hge];
    first [rewrite Z.ltb_lt in Hlt | rewrite Z.ltb_ge in Hlt]; lia.
Qed.

Local Lemma tagged_unsigned_nonneg : forall a : Z,
  0 <= a < 4611686018427387904 ->
  Int64.unsigned (Int64.repr (a * 2 + 1)) = a * 2 + 1.
Proof.
  intros a Ha. apply Int64.unsigned_repr.
  unfold Int64.max_unsigned. change Int64.modulus with 18446744073709551616. lia.
Qed.

Local Lemma tagged_unsigned_neg : forall a : Z,
  -4611686018427387904 <= a < 0 ->
  Int64.unsigned (Int64.repr (a * 2 + 1)) = a * 2 + 1 + 18446744073709551616.
Proof.
  intros a Ha. rewrite Int64.unsigned_repr_eq.
  change Int64.modulus with 18446744073709551616.
  replace (a * 2 + 1)
    with ((a * 2 + 1 + 18446744073709551616) + (-1) * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small; lia.
Qed.

Local Lemma tagged_ugeint_arith : forall a b,
  0 <= a < 4611686018427387904 ->
  0 <= b < 4611686018427387904 ->
  negb (Int64.ltu (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1)))
    = Z.geb (z_flip_sign a) (z_flip_sign b).
Proof.
  intros a b Ha Hb. rewrite Z_geb_negb_ltb.
  unfold Int64.ltu.
  rewrite (tagged_unsigned_nonneg a ltac:(lia)).
  rewrite (tagged_unsigned_nonneg b ltac:(lia)).
  rewrite (z_flip_sign_nonneg_eq a ltac:(lia)).
  rewrite (z_flip_sign_nonneg_eq b ltac:(lia)).
  destruct (zlt _ _); destruct (Z.ltb _ _) eqn:Hlt; simpl; try reflexivity;
    first [apply Z.ltb_lt in Hlt | apply Z.ltb_ge in Hlt]; lia.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_UGEINT_correct :
    handler_correct handle_UGEINT f_instr_UGEINT
      (fun _ _ s _ =>
         match s.(Machine.accu), s.(Machine.stack) with
         | Val_int a, Val_int b :: _ =>
             0 <= a < 4611686018427387904 /\
             0 <= b < 4611686018427387904
         | _, _ => True
         end)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handler_correct, handle_UGEINT.
  destruct (Machine.accu s) as [a| | |] eqn:Haccu_eq; try (exact I).
  destruct (Machine.stack s) as [|v_hd v_tl] eqn:Hstk; try (exact I).
  destruct v_hd as [b| | |] eqn:Hvhd; try (exact I).
  intros ard Hpre Hstep_pre.
  unfold abs_rel_with_ard in Hpre.
  change (Machine.accu s) with (Val_int a) in Hstep_pre.
  change (Machine.stack s) with (Val_int b :: v_tl) in Hstep_pre.
  simpl in Hstep_pre. destruct Hstep_pre as [Ha_range Hb_range].
  set (sb := ar_sptr_block ard) in *.
  set (so := ar_sptr_ofs ard) in *.
  set (hm := ar_heap_map ard) in *.
  destruct Hpre as (Hle_s & [pc_ptr [Hpc_load Hpc_rel]] &
    [accu_v [Haccu_load Haccu_repr]] &
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb Hcb_ne_sp]]]]]]]] &
    [env_v [Henv_load Henv_repr]] & Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
    [ts_ptr [Hts_load Htrap_rel]]). subst sp_ptr.
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep. fold sb in Hblock_sep.
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  rewrite Haccu_eq in Haccu_repr.
  inversion Haccu_repr; subst accu_v. rename H0 into Haccu_is_int.
  rewrite Hstk in Hstack_repr.
  inversion Hstack_repr as [| ? ? ? ? cv0 Hload_sp0 Hval_repr0 Hstack_repr_rest].
  revert Hgd_load Hgd_eq Hglobal_repr. subst.
  intros Hgd_load Hgd_eq Hglobal_repr.
  inversion Hval_repr0; subst cv0. rename H0 into Hstk_is_int.
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
  set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
  destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 16)
              (Vptr sp_b sp_ofs) new_sp_v Hsp_load) as [m1 Hstore1].
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) =
    Some (Vlong (Int64.repr (a * 2 + 1)))).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
      (Ptrofs.unsigned so + 8) new_sp_v _ Hstore1 Haccu_load). left. lia. }
  assert (Hload_sp0_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) =
    Some (Vlong (Int64.repr (b * 2 + 1)))).
  { erewrite Mem.load_store_other. exact Hload_sp0. exact Hstore1.
    left. exact Hblock_sep. }
  set (uge_bool := negb (Int64.ltu (Int64.repr (a * 2 + 1))
                                    (Int64.repr (b * 2 + 1)))).
  set (result_v := Vlong (Int64.add (Int64.repr (if uge_bool then 2 else 0))
                                     (Int64.repr 1))).
  destruct (store_succeeds_from_load m1 sb (Ptrofs.unsigned so + 8)
              (Vlong (Int64.repr (a * 2 + 1))) result_v Haccu_load_m1)
    as [m' Hstore2].
  set (le' := PTree.set _t'3 (Vlong (Int64.repr (b * 2 + 1)))
    (PTree.set _t'2 (Vlong (Int64.repr (a * 2 + 1)))
    (PTree.set _t'1 (Vptr sp_b sp_ofs) le))).
  exists le'. exists m'. exists (Out_return (Some (Vint (Int.repr 0), tint))).
  split.
  { apply (eval_stmt_to_exec clight_ge 15). eval_cbn.
    rewrite Hle_s; eval_cbn. rewrite Hco; eval_cbn. rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
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
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_to_ulong; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_to_ulong; eval_cbn.
    rewrite sem_ge_ulong_ulong; eval_cbn.
    rewrite sem_cast_bool_int_to_long; eval_cbn.
    rewrite (sem_shl_bool_long_1 (negb (Int64.ltu (Int64.repr (a * 2 + 1))
                                                    (Int64.repr (b * 2 + 1))))); eval_cbn.
    rewrite sem_add_long_int_1; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    unfold result_v, uge_bool in Hstore2. rewrite Hstore2; eval_cbn.
    subst le'. reflexivity. }
  { exists ard. set (uso := Ptrofs.unsigned so) in *.
    assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
    { assert (Hpc_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 0)
          new_sp_v pc_ptr Hstore1 Hpc_load). left. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 0)
        result_v pc_ptr Hstore2 Hpc_m1). left. lia. }
    assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some new_sp_v).
    { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some new_sp_v).
      { pose proof (load_after_store_same m m1 sb (uso + 16) new_sp_v Hstore1)
          as Htmp. unfold new_sp_v in Htmp |- *.
        simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 16)
        result_v new_sp_v Hstore2 Hsp_m1). right. lia. }
    assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some result_v).
    { pose proof (load_after_store_same m1 m' sb (uso + 8) result_v Hstore2)
        as Htmp. unfold result_v in Htmp |- *.
      simpl Val.load_result in Htmp. exact Htmp. }
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
    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
    { subst le'.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence). exact Hle_s. }
    { exists pc_ptr. split. exact Hpc_load'. simpl. exact Hpc_rel. }
    { exists result_v. split. exact Haccu_load'. simpl.
      unfold result_v. rewrite tagged_uge_result.
      unfold uge_bool. rewrite (tagged_ugeint_arith a b Ha_range Hb_range).
      destruct (Z.geb (z_flip_sign a) (z_flip_sign b)); constructor. }
    { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)).
      split; [| split; [| split; [| split; [| split]]]]. exact Hsp_load'. reflexivity.
      { simpl.
        eapply (stack_repr_store_other_block hm m1 m' _ sp_b
          (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) result_v).
        + eapply (stack_repr_store_other_block hm m m1 _ sp_b
            (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16) new_sp_v).
          * exact Hstack_repr_rest. * exact Hstore1.
          * intro Heq; exact (Hblock_sep (eq_sym Heq)).
        + exact Hstore2. + intro Heq; exact (Hblock_sep (eq_sym Heq)). }
      exact Hsp_ne_sb. exact Hsp_ne_gb. exact Hcb_ne_sp. }
    { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }
    { simpl. exact Hextra_load'. }
    { exists gd_ptr. split; [| split; [| split]]. exact Hgd_load'. simpl. exact Hgd_eq.
      { simpl.
        eapply (global_repr_store_other_block hm m1 m' _ _ _ sb (uso + 8) result_v).
        + eapply (global_repr_store_other_block hm m m1 _ _ _ sb (uso + 16) new_sp_v).
          * exact Hglobal_repr. * exact Hstore1.
          * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        + exact Hstore2. + intro Heq2; exact (Hgb_ne (eq_sym Heq2)). }
      exact Hgb_ne_sb. }
    { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. } }
Qed.
