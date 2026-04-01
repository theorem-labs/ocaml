(* MULINT_correct.v -- correctness proof for the MULINT handler.
   C handler computes: (((accu >> 1) * (stack_top >> 1)) << 1) + 1
   Tagged arithmetic: shr untags both operands, multiply, shl+1 retags.
   For tagged ints a_tagged = a*2+1, b_tagged = b*2+1:
     ((a*2+1) >> 1) = a, ((b*2+1) >> 1) = b  (arithmetic shift)
     (a * b) << 1 + 1 = (a*b)*2+1 = tagged(a*b)
   Rocq handler: handle_MULINT pops stack, multiplies two ints. *)
From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
Require Import instruct_handlers InstructSpec StepToBigstep HandlerLemmas.
Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr sem_binary_operation sem_cast
        Mem.load Mem.store Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int field_offset PTree.get PTree.set].

(* Semantic lemma: long >> 1 (arithmetic shift right) *)
Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* Semantic lemma: long * long *)
Local Lemma sem_mul_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Omul
    (Vlong n1) tlong (Vlong n2) tlong m
    = Some (Vlong (Int64.mul n1 n2)).
Proof. intros. reflexivity. Qed.

(* Semantic lemma: long << 1 *)
Local Lemma sem_shl_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.shl n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* Semantic lemma: long + int(1) *)
Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* eqm for multiplication *)
Local Lemma eqm64_mul : forall x x' y y',
  Int64.eqm x x' -> Int64.eqm y y' -> Int64.eqm (x * y) (x' * y').
Proof.
  intros x x' y y' [kx Hx] [ky Hy].
  exists (kx * y' + x' * ky + kx * ky * Int64.modulus)%Z.
  nia.
Qed.

Local Lemma eqm64_add : forall x x' y y',
  Int64.eqm x x' -> Int64.eqm y y' -> Int64.eqm (x + y) (x' + y').
Proof.
  intros x x' y y' [kx Hx] [ky Hy].
  exists (kx + ky)%Z. nia.
Qed.

(* Key helper: for odd tagged int n*2+1, the signed arithmetic shift right
   by 1 produces a value congruent to n modulo half_modulus.
   After the outer shl by 1 in the full expression, these half_modulus
   terms become full modulus multiples. We state this as an eqm at
   modulus where the difference is a multiple of half_modulus. *)
Local Lemma shr_tagged_eqm_half : forall n,
  exists k, Int64.signed (Int64.repr (n * 2 + 1)) / 2 = n + k * Int64.half_modulus.
Proof.
  intros n.
  (* signed(repr(n*2+1)) = (n*2+1) + j * modulus for some j *)
  pose proof (Int64.eqm_signed_unsigned (Int64.repr (n * 2 + 1))) as [k1 Hk1].
  pose proof (Int64.eqm_unsigned_repr (n * 2 + 1)) as [k2 Hk2].
  (* Hk1: signed(repr(n*2+1)) = k1*M + unsigned(repr(n*2+1)) *)
  (* Hk2: n*2+1 = k2*M + unsigned(repr(n*2+1)) *)
  set (j := (k1 - k2)%Z).
  assert (Hsigned : Int64.signed (Int64.repr (n * 2 + 1)) = n * 2 + 1 + j * Int64.modulus).
  { unfold j. nia. }
  rewrite Hsigned.
  (* modulus = half_modulus * 2 *)
  assert (HM : Int64.modulus = Int64.half_modulus * 2) by (vm_compute; reflexivity).
  rewrite HM.
  (* (n*2+1 + j*(H*2)) / 2 *)
  replace (n * 2 + 1 + j * (Int64.half_modulus * 2))%Z
    with ((n + j * Int64.half_modulus) * 2 + 1)%Z by lia.
  rewrite Z.div_add_l by lia.
  change (1 / 2)%Z with 0%Z.
  exists j. lia.
Qed.

(* The full tagged multiplication identity. *)
Local Lemma tagged_mulint_arith : forall a b,
  Int64.add
    (Int64.shl
      (Int64.mul
        (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))
        (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)))
      (Int64.repr 1))
    (Int64.repr 1)
  = Int64.repr ((a * b) * 2 + 1).
Proof.
  intros a b.
  unfold Int64.add, Int64.shl, Int64.mul, Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  apply Int64.eqm_samerepr.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 1)%Z with 2%Z.

  set (sa := Int64.signed (Int64.repr (a * 2 + 1)) / 2).
  set (sb := Int64.signed (Int64.repr (b * 2 + 1)) / 2).
  fold sa. fold sb.

  destruct (shr_tagged_eqm_half a) as [ka Hsa_eq].
  destruct (shr_tagged_eqm_half b) as [kb Hsb_eq].
  fold sa in Hsa_eq. fold sb in Hsb_eq.

  (* Peel off unsigned(repr(...)) layers, then prove core eqm directly *)
  eapply Int64.eqm_trans.
  - apply eqm64_add.
    + apply Int64.eqm_unsigned_repr_l.
      apply eqm64_mul.
      * apply Int64.eqm_unsigned_repr_l.
        apply eqm64_mul; apply Int64.eqm_unsigned_repr_l; apply Int64.eqm_refl.
      * apply Int64.eqm_refl.
    + apply Int64.eqm_refl.
  - (* Goal: eqm (sa * sb * 2 + 1) (a*b*2+1) *)
    rewrite Hsa_eq, Hsb_eq.
    set (H := Int64.half_modulus).
    assert (HM : Int64.modulus = H * 2) by (unfold H; vm_compute; reflexivity).
    exists (a * kb + b * ka + ka * kb * H)%Z.
    rewrite HM. nia.
Qed.

Theorem verify_MULINT_correct :
    handler_correct handle_MULINT f_instr_MULINT
      (fun _ _ _ _ => True)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handler_correct, handle_MULINT.
  destruct (Machine.accu s) as [a| | |] eqn:Haccu_eq; try (exact I).
  destruct (Machine.stack s) as [|v_hd v_tl] eqn:Hstk; try (exact I).
  destruct v_hd as [b| | |] eqn:Hvhd; try (exact I).
  intros ard Hpre _. unfold abs_rel_with_ard in Hpre.
  set (sb := ar_sptr_block ard) in *. set (so := ar_sptr_ofs ard) in *. set (hm := ar_heap_map ard) in *.
  destruct Hpre as (Hle_s & [pc_ptr [Hpc_load Hpc_rel]] & [accu_v [Haccu_load Haccu_repr]] & [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb Hcb_ne_sp]]]]]]]] & [env_v [Henv_load Henv_repr]] & Hextra_load & [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] & [ts_ptr [Hts_load Htrap_rel]]). subst sp_ptr.
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep. fold sb in Hblock_sep.
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  rewrite Haccu_eq in Haccu_repr. inversion Haccu_repr; subst accu_v. rename H0 into Haccu_is_int.
  rewrite Hstk in Hstack_repr.
  inversion Hstack_repr as [| ? ? ? ? cv0 Hload_sp0 Hval_repr0 Hstack_repr_rest].
  revert Hgd_load Hgd_eq Hglobal_repr. subst. intros Hgd_load Hgd_eq Hglobal_repr.
  inversion Hval_repr0; subst cv0. rename H0 into Hstk_is_int.
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
  set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
  destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 16)
              (Vptr sp_b sp_ofs) new_sp_v Hsp_load) as [m1 Hstore1].
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vlong (Int64.repr (a * 2 + 1)))).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8) new_sp_v (Vlong (Int64.repr (a * 2 + 1))) Hstore1 Haccu_load). left. lia. }
  assert (Hload_sp0_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) = Some (Vlong (Int64.repr (b * 2 + 1)))).
  { erewrite Mem.load_store_other. exact Hload_sp0. exact Hstore1. left. exact Hblock_sep. }
  set (result_v := Vlong (Int64.add
    (Int64.shl
      (Int64.mul
        (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))
        (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)))
      (Int64.repr 1))
    (Int64.repr 1))).
  destruct (store_succeeds_from_load m1 sb (Ptrofs.unsigned so + 8) (Vlong (Int64.repr (a * 2 + 1))) result_v Haccu_load_m1) as [m' Hstore2].
  set (le' := PTree.set _t'3 (Vlong (Int64.repr (b * 2 + 1))) (PTree.set _t'2 (Vlong (Int64.repr (a * 2 + 1))) (PTree.set _t'1 (Vptr sp_b sp_ofs) le))).
  exists le'. exists m'. exists (Out_return (Some (Vint (Int.repr 0), tint))). split.
  (* ============================================================== *)
  (* Part 1: exec -- step through the C handler                     *)
  (* ============================================================== *)
  { apply (eval_stmt_to_exec clight_ge 20). eval_cbn.
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
    rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence). rewrite Hle_s; eval_cbn.
    (* Evaluate _t'2 in RHS expression *)
    rewrite PTree.gso by (compute; congruence). rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    rewrite sem_shr_long_int_1; eval_cbn.
    (* Evaluate _t'3 in RHS expression *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    rewrite sem_shr_long_int_1; eval_cbn.
    (* Compute mul, cast, shl, add *)
    rewrite sem_mul_long_long; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    rewrite sem_shl_long_int_1; eval_cbn.
    rewrite sem_add_long_int_1; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
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
    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
    { subst le'. rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence). exact Hle_s. }
    { exists pc_ptr. split. exact Hpc_load'. simpl. exact Hpc_rel. }
    { exists result_v. split. exact Haccu_load'. simpl. unfold result_v. rewrite tagged_mulint_arith. constructor. }
    { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)). split; [| split; [| split; [| split; [| split]]]]. exact Hsp_load'. reflexivity. simpl.
      eapply (stack_repr_store_other_block hm m1 m' _ sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) result_v).
      + eapply (stack_repr_store_other_block hm m m1 _ sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16) new_sp_v).
        * exact Hstack_repr_rest. * exact Hstore1. * intro Heq; exact (Hblock_sep (eq_sym Heq)).
            + exact Hstore2. + intro Heq; exact (Hblock_sep (eq_sym Heq)).
      + exact Hsp_ne_sb. + exact Hsp_ne_gb. + exact Hcb_ne_sp. }
    { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }
    { simpl. exact Hextra_load'. }
    { exists gd_ptr. split; [| split; [| split]]. exact Hgd_load'. simpl. exact Hgd_eq. simpl.
      eapply (global_repr_store_other_block hm m1 m' _ _ _ sb (uso + 8) result_v).
      + eapply (global_repr_store_other_block hm m m1 _ _ _ sb (uso + 16) new_sp_v). * exact Hglobal_repr. * exact Hstore1. * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
            + exact Hstore2. + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
      + exact Hgb_ne_sb. }
    { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. } }
Qed.
