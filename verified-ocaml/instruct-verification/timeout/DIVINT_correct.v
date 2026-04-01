(* DIVINT_correct.v -- correctness proof for the DIVINT bytecode handler.

   C (Clight AST):
     _t'1 = s->sp;                          // load sp
     s->sp = _t'1 + 1;                      // sp++ (pop stack)
     _t'3 = *_t'1;                          // load stack[0] (b_tagged)
     _divisor = (long)_t'3 >> 1;            // untag b
     if (_divisor == 0) caml_raise_zero_divide(); else skip;
     _t'2 = s->accu;                        // load accu (a_tagged)
     s->accu = (((long)_t'2 >> 1) / _divisor) << 1 + 1;  // untag, div, retag

   Rocq handler:
     handle_DIVINT pc' s = match accu, stack with
       | Val_int a, Val_int b :: rest =>
           if Z.eqb b 0 then do_raise div_by_zero_exn s
           else Step (s<|pc:=pc'|><|accu:=Val_int(Z.quot a b)|><|stack:=rest|>)
       | _, _ => Error ...

   Precondition (handler_correct_with_pre):
     b <> 0 -- the stack top is nonzero
     Tagged values are in Int64 signed range (true for OCaml 63-bit ints)

   The do_raise case (b=0) is handled vacuously: the precondition is
   False when b=0, so the Step branch from do_raise is discharged. *)

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

(* ================================================================== *)
(* Semantic lemmas for DIVINT C operations                             *)
(* ================================================================== *)

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

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

Local Lemma bool_val_of_bool_tint : forall b m,
  bool_val (Val.of_bool b) tint m = Some b.
Proof. intros [] m; reflexivity. Qed.

Local Lemma sem_shl_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shl n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Tagged arithmetic lemmas for DIVINT                                 *)
(* ================================================================== *)

(* Signed shift right of tagged value gives back the original integer *)
Local Lemma shr_tagged_repr : forall b,
  Int64.min_signed <= b * 2 + 1 <= Int64.max_signed ->
  Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1) = Int64.repr b.
Proof.
  intros b Hrange.
  unfold Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1.
  rewrite Int64.signed_repr by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  f_equal.
  replace ((b * 2 + 1) / 2) with b by (apply Z.div_unique with 1; lia).
  reflexivity.
Qed.

(* When b <> 0 and tagged value is in signed range, the untagged divisor
   is nonzero in Int64 representation. *)
Local Lemma shr_tagged_ne_zero : forall b,
  b <> 0 ->
  Int64.min_signed <= b * 2 + 1 <= Int64.max_signed ->
  Int64.eq (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)) Int64.zero = false.
Proof.
  intros b Hb Hrange.
  rewrite shr_tagged_repr by lia.
  unfold Int64.eq.
  change (Int64.unsigned Int64.zero) with 0.
  destruct (zeq (Int64.unsigned (Int64.repr b)) 0); [|reflexivity].
  exfalso. apply Hb.
  assert (Int64.repr b = Int64.zero) as Hrepr_eq.
  { apply Int64.same_if_eq. unfold Int64.eq. rewrite e. reflexivity. }
  apply (f_equal Int64.signed) in Hrepr_eq.
  rewrite Int64.signed_zero in Hrepr_eq.
  rewrite Int64.signed_repr in Hrepr_eq.
  - exact Hrepr_eq.
  - unfold Int64.min_signed, Int64.max_signed in *.
    generalize Int64.half_modulus_pos. lia.
Qed.

(* shr(n, 1) can never be min_signed: the signed value of shr(n,1) is
   in [-2^62, 2^62-1], which excludes min_signed = -2^63. *)
Local Lemma shr_1_ne_min_signed : forall n,
  Int64.eq (Int64.shr n (Int64.repr 1)) (Int64.repr Int64.min_signed) = false.
Proof.
  intros.
  unfold Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1.
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  apply Int64.eq_false. intro Heq.
  apply (f_equal Int64.signed) in Heq.
  rewrite Int64.signed_repr in Heq.
  2: { pose proof (Int64.signed_range n).
       unfold Int64.min_signed, Int64.max_signed in *.
       generalize Int64.half_modulus_pos. intro Hp. split.
       + apply Z.div_le_lower_bound. lia. unfold Int64.min_signed. lia.
       + apply Z.div_le_upper_bound. lia. unfold Int64.max_signed. lia. }
  rewrite Int64.signed_repr in Heq.
  2: { unfold Int64.min_signed, Int64.max_signed.
       generalize Int64.half_modulus_pos. lia. }
  pose proof (Int64.signed_range n).
  unfold Int64.min_signed, Int64.max_signed in *.
  (* lia can't handle division with opaque half_modulus; concretize it *)
  assert (Hlo : -Int64.half_modulus / 2 <= Int64.signed n / 2).
  { apply Z.div_le_mono. lia. lia. }
  assert (Hhi : Int64.signed n / 2 <= (Int64.half_modulus - 1) / 2).
  { apply Z.div_le_mono. lia. lia. }
  cut (Int64.half_modulus = 9223372036854775808).
  { intro Hval. rewrite Hval in *.
    change (- (9223372036854775808) / 2) with (-4611686018427387904) in Hlo.
    change ((9223372036854775808 - 1) / 2) with 4611686018427387903 in Hhi.
    lia. }
  reflexivity.
Qed.

(* sem_div succeeds on shr'd tagged values when the divisor is nonzero.
   The overflow guard (min_signed / -1) is automatically false because
   shr(n,1) can never equal min_signed. *)
Local Lemma sem_div_shr_succeeds : forall n1 n2 m,
  Int64.eq (Int64.shr n2 (Int64.repr 1)) Int64.zero = false ->
  sem_binary_operation (genv_cenv clight_ge) Odiv
    (Vlong (Int64.shr n1 (Int64.repr 1))) tlong
    (Vlong (Int64.shr n2 (Int64.repr 1))) tlong m
  = Some (Vlong (Int64.divs (Int64.shr n1 (Int64.repr 1))
                             (Int64.shr n2 (Int64.repr 1)))).
Proof.
  intros n1 n2 m Hdivisor.
  unfold sem_binary_operation, sem_div, sem_binarith.
  change (classify_binarith tlong tlong) with (bin_case_l Signed).
  simpl.
  rewrite sem_cast_long_vlong. rewrite sem_cast_long_vlong. simpl.
  rewrite Hdivisor. simpl.
  rewrite shr_1_ne_min_signed. reflexivity.
Qed.

(* The combined tagged division arithmetic identity:
   shl(divs(repr(a), repr(b)), 1) + 1 = repr(Z.quot a b * 2 + 1)
   when a, b are in signed range and b <> 0. *)
Local Lemma tagged_divint_arith : forall a b,
  Int64.min_signed <= a * 2 + 1 <= Int64.max_signed ->
  Int64.min_signed <= b * 2 + 1 <= Int64.max_signed ->
  b <> 0 ->
  Int64.add
    (Int64.shl
      (Int64.divs (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))
                   (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)))
      (Int64.repr 1))
    (Int64.repr 1)
  = Int64.repr (Z.quot a b * 2 + 1).
Proof.
  intros a b Harange Hbrange Hb.
  (* Reduce shr of tagged values *)
  unfold Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1.
  rewrite (Int64.signed_repr (a * 2 + 1)) by lia.
  rewrite (Int64.signed_repr (b * 2 + 1)) by lia.
  rewrite !Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  replace ((a * 2 + 1) / 2) with a by (apply Z.div_unique with 1; lia).
  replace ((b * 2 + 1) / 2) with b by (apply Z.div_unique with 1; lia).
  (* Reduce divs *)
  unfold Int64.divs.
  rewrite Int64.signed_repr
    by (unfold Int64.min_signed, Int64.max_signed in *;
        generalize Int64.half_modulus_pos; lia).
  rewrite Int64.signed_repr
    by (unfold Int64.min_signed, Int64.max_signed in *;
        generalize Int64.half_modulus_pos; lia).
  (* Reduce shl and add *)
  unfold Int64.shl, Int64.add.
  change (Int64.unsigned (Int64.repr 1)) with 1.
  rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
  apply Int64.eqm_samerepr.
  eapply Int64.eqm_trans.
  - apply Int64.eqm_add.
    + eapply Int64.eqm_trans.
      * apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
      * apply Int64.eqm_mult.
        -- apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
        -- apply Int64.eqm_refl.
    + apply Int64.eqm_refl.
  - apply Int64.eqm_refl.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_DIVINT_correct :
    handler_correct_with_pre handle_DIVINT f_instr_DIVINT
      (fun _ s _ =>
         match s.(Machine.accu), s.(Machine.stack) with
         | Val_int a, Val_int b :: _ =>
             b <> 0%Z /\
             Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
             Int64.min_signed <= b * 2 + 1 <= Int64.max_signed
         | _, _ => True
         end)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int b :: _ => Z.eqb b 0 = true
                  | _, _ => True
                  end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handle_DIVINT.

  (* Case split on accu *)
  destruct (Machine.accu s) as [a| | |] eqn:Haccu_eq;
    try (exact I).

  (* Case split on stack *)
  destruct (Machine.stack s) as [|v_hd v_tl] eqn:Hstk;
    try (exact I).

  destruct v_hd as [b| | |] eqn:Hvhd;
    try (exact I).

  (* Now: accu = Val_int a, stack = Val_int b :: v_tl *)
  (* Case split on Z.eqb b 0 *)
  destruct (Z.eqb b 0) eqn:Hbeq.

  - (* b = 0: do_raise case *)
    unfold do_raise.
    destruct (Nat.eqb (trap_sp s) 0) eqn:Htrap.
    + (* Error "unhandled exception": P_error must hold *)
      simpl. rewrite Z.eqb_eq in Hbeq. subst b. reflexivity.
    + (* do_raise walks the trap frame *)
      destruct (skipn _ _) as [|v1 rest1].
      * simpl. rewrite Z.eqb_eq in Hbeq. subst b. reflexivity.
      * destruct v1; try (simpl; rewrite Z.eqb_eq in Hbeq; subst b; reflexivity).
        destruct rest1 as [|v2 rest2];
          try (simpl; rewrite Z.eqb_eq in Hbeq; subst b; reflexivity).
        destruct v2; try (simpl; rewrite Z.eqb_eq in Hbeq; subst b; reflexivity).
        destruct rest2 as [|v3 rest3];
          try (simpl; rewrite Z.eqb_eq in Hbeq; subst b; reflexivity).
        destruct rest3 as [|v4 rest4];
          try (simpl; rewrite Z.eqb_eq in Hbeq; subst b; reflexivity).
        destruct v4; try (simpl; rewrite Z.eqb_eq in Hbeq; subst b; reflexivity).
        (* Step case from do_raise: precondition says b <> 0 but b = 0 *)
        intros ard Hpre Hstep_pre.
        simpl in Hstep_pre.
        rewrite Z.eqb_eq in Hbeq. subst b.
        destruct Hstep_pre as [Hb_ne _]. exfalso. apply Hb_ne. reflexivity.

  - (* b <> 0: normal division *)
    intros ard Hpre Hstep_pre.
    simpl in Hstep_pre.

    (* Extract preconditions *)
    destruct Hstep_pre as (Hb_ne & Harange & Hbrange).

    unfold abs_rel_with_ard in Hpre.
    set (sb := ar_sptr_block ard) in *.
    set (so := ar_sptr_ofs ard) in *.
    set (hm := ar_heap_map ard) in *.
    destruct Hpre as (Hle_s &
      [pc_ptr [Hpc_load Hpc_rel]] &
      [accu_v [Haccu_load Haccu_repr]] &
      [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr
        [Hsp_ne_sb [Hsp_ne_gb Hcb_ne_sp]]]]]]]] &
      [env_v [Henv_load Henv_repr]] &
      Hextra_load &
      [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
      [ts_ptr [Hts_load Htrap_rel]]).
    subst sp_ptr.

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep. fold sb in Hblock_sep.
    pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.

    (* Accu is Val_int a *)
    rewrite Haccu_eq in Haccu_repr.
    inversion Haccu_repr; subst accu_v. rename H0 into Haccu_is_int.

    (* Extract stack head *)
    rewrite Hstk in Hstack_repr.
    inversion Hstack_repr as [| ? ? ? ? cv0 Hload_sp0 Hval_repr0 Hstack_repr_rest].
    revert Hgd_load Hgd_eq Hglobal_repr.
    subst.
    intros Hgd_load Hgd_eq Hglobal_repr.

    (* Stack head is Val_int b *)
    inversion Hval_repr0; subst cv0. rename H0 into Hstk_is_int.

    (* Composite environment facts *)
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    (* --- Store 1: sp field (so+16) gets sp+1 = Vptr sp_b (sp_ofs + 8) --- *)
    set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
    destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 16)
                (Vptr sp_b sp_ofs) new_sp_v Hsp_load)
      as [m1 Hstore1].

    (* --- After store 1: load accu from m1 --- *)
    assert (Haccu_load_m1 :
      Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) =
        Some (Vlong (Int64.repr (a * 2 + 1)))).
    { apply (load_after_store_other m m1 sb
               (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8)
               new_sp_v (Vlong (Int64.repr (a * 2 + 1)))
               Hstore1 Haccu_load). left. lia. }

    (* --- After store 1: load *sp from m1 (different block) --- *)
    assert (Hload_sp0_m1 :
      Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) =
        Some (Vlong (Int64.repr (b * 2 + 1)))).
    { erewrite Mem.load_store_other.
      - exact Hload_sp0.
      - exact Hstore1.
      - left. exact Hblock_sep. }

    (* --- Divisor: shr(b_tagged, 1) --- *)
    set (b_tagged := Int64.repr (b * 2 + 1)).
    set (divisor := Int64.shr b_tagged (Int64.repr 1)).

    (* Divisor is nonzero *)
    assert (Hdivisor_ne : Int64.eq divisor Int64.zero = false).
    { unfold divisor, b_tagged.
      apply shr_tagged_ne_zero; assumption. }

    (* --- Store 2: accu field (so+8) gets the tagged div result --- *)
    set (a_tagged := Int64.repr (a * 2 + 1)).
    set (a_untagged := Int64.shr a_tagged (Int64.repr 1)).
    set (div_result := Int64.divs a_untagged divisor).
    set (result_v := Vlong (Int64.add (Int64.shl div_result (Int64.repr 1))
                                       (Int64.repr 1))).
    destruct (store_succeeds_from_load m1 sb (Ptrofs.unsigned so + 8)
                (Vlong (Int64.repr (a * 2 + 1))) result_v Haccu_load_m1)
      as [m' Hstore2].

    (* Witnesses *)
    set (le' := PTree.set _t'2 (Vlong a_tagged)
                  (PTree.set _divisor (Vlong divisor)
                    (PTree.set _t'3 (Vlong b_tagged)
                      (PTree.set _t'1 (Vptr sp_b sp_ofs) le)))).
    exists le'. exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (* ============================================================== *)
    {
      apply (eval_stmt_to_exec clight_ge 10).

      (* --- Initial reduction --- *)
      eval_cbn.

      (* === Sset _t'1 (s->sp) === *)      rewrite Hle_s; eval_cbn.      rewrite Hco; eval_cbn.      rewrite Hsp_offset; eval_cbn.      rewrite Mptr_Mint64; eval_cbn.      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).      rewrite Hsp_load; eval_cbn.
      (* === Sassign (s->sp = _t'1 + 1) === *)      rewrite PTree.gso by (simpl; congruence).      rewrite Hle_s; eval_cbn.      rewrite PTree.gss; eval_cbn.      rewrite sem_add_sp_1; eval_cbn.      rewrite sem_cast_ptr_to_ptr; eval_cbn.      rewrite Mptr_Mint64; eval_cbn.      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).      unfold new_sp_v in Hstore1. rewrite Hstore1; eval_cbn.
      (* === Sset _t'3 (deref _t'1) === *)      rewrite PTree.gso by (simpl; congruence).      rewrite PTree.gss; eval_cbn.      rewrite Hload_sp0_m1; eval_cbn.
      (* === Sset _divisor = (long)_t'3 >> 1 === *)      rewrite PTree.gss; eval_cbn.      rewrite sem_cast_long_vlong; eval_cbn.      rewrite sem_shr_long_int_1; eval_cbn.
      (* === Sifthenelse (_divisor == 0) Scall Sskip === *)      (* _divisor is in the most recent temp *)      rewrite PTree.gss; eval_cbn.      rewrite sem_eq_long_int_0; eval_cbn.      rewrite Hdivisor_ne; eval_cbn.      rewrite bool_val_of_bool_tint; eval_cbn.      (* false branch: Sskip *)
      (* === Sset _t'2 (s->accu) === *)      rewrite PTree.gso by (simpl; congruence).      rewrite PTree.gso by (simpl; congruence).      rewrite PTree.gso by (simpl; congruence).      rewrite Hle_s; eval_cbn.      rewrite Haccu_offset; eval_cbn.      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).      rewrite Haccu_load_m1; eval_cbn.
      (* === Sassign (s->accu = ...) : lvalue === *)      (* Skip _t'2, _divisor, _t'3, _t'1 to get _s *)      rewrite PTree.gso by (simpl; congruence).      rewrite PTree.gso by (simpl; congruence).      rewrite PTree.gso by (simpl; congruence).      rewrite PTree.gso by (simpl; congruence).      rewrite Hle_s; eval_cbn.
      (* === Sassign rhs: ((cast _t'2 >> 1) / _divisor) << 1 + 1 === *)      (* _t'2: read from le' *)      rewrite PTree.gss; eval_cbn.      (* cast _t'2 tlong tlong *)      rewrite sem_cast_long_vlong; eval_cbn.      (* Oshr: (cast _t'2 tlong) >> 1 *)      rewrite sem_shr_long_int_1; eval_cbn.      (* _divisor: read from le' *)      rewrite PTree.gso by (simpl; congruence).      rewrite PTree.gss; eval_cbn.      (* Odiv: shr(accu,1) / divisor *)      unfold a_tagged, a_untagged, divisor, b_tagged, div_result in *.      rewrite sem_div_shr_succeeds by exact Hdivisor_ne; eval_cbn.      (* cast result tlong tlong *)      rewrite sem_cast_long_vlong; eval_cbn.      (* Oshl: div_result << 1 *)      rewrite sem_shl_long_int_1; eval_cbn.      (* Oadd: shl_result + 1 *)      rewrite sem_add_long_int_1; eval_cbn.      (* Final cast *)      rewrite sem_cast_long_vlong; eval_cbn.
      (* Store to accu field *)      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).      rewrite Hstore2; eval_cbn.
      (* === Sreturn 0 === *)      subst le'. reflexivity.    }
    (* ============================================================== *)    (* Part 2: abs_rel for post-state                                  *)    (* ============================================================== *)    {      exists ard.      set (uso := Ptrofs.unsigned so) in *.
      (* --- Loads from m' (after store2 at so+8, store1 at so+16 in m1) --- *)
      (* pc field at so+0: unaffected by both stores *)      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).      { assert (Hpc_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some pc_ptr).        { apply (load_after_store_other m m1 sb                   (uso + 16) (uso + 0) new_sp_v pc_ptr                   Hstore1 Hpc_load). left. lia. }        apply (load_after_store_other m1 m' sb                 (uso + 8) (uso + 0) result_v pc_ptr                 Hstore2 Hpc_m1). left. lia. }
      (* sp field at so+16: written by store1, unaffected by store2 *)      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some new_sp_v).      { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some new_sp_v).        { pose proof (load_after_store_same m m1 sb (uso + 16) new_sp_v Hstore1) as Htmp.          unfold new_sp_v in Htmp |- *. simpl Val.load_result in Htmp.          rewrite ptr64_true in Htmp.          exact Htmp. }        apply (load_after_store_other m1 m' sb                 (uso + 8) (uso + 16) result_v new_sp_v                 Hstore2 Hsp_m1). right. lia. }
      (* accu field at so+8: written by store2 *)      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some result_v).      { pose proof (load_after_store_same m1 m' sb (uso + 8) result_v Hstore2) as Htmp.        unfold result_v in Htmp |- *. simpl Val.load_result in Htmp.        exact Htmp. }
      (* env field at so+24: unaffected by both stores *)      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).      { assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).        { apply (load_after_store_other m m1 sb                   (uso + 16) (uso + 24) new_sp_v env_v                   Hstore1 Henv_load). right. lia. }        apply (load_after_store_other m1 m' sb                 (uso + 8) (uso + 24) result_v env_v                 Hstore2 Henv_m1). right. lia. }
      (* extra_args field at so+32: unaffected by both stores *)      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).      { assert (Hextra_m1 : Mem.load Mint64 m1 sb (uso + 32) =                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).        { apply (load_after_store_other m m1 sb                   (uso + 16) (uso + 32) new_sp_v _                   Hstore1 Hextra_load). right. lia. }        apply (load_after_store_other m1 m' sb                 (uso + 8) (uso + 32) result_v _                 Hstore2 Hextra_m1). right. lia. }
      (* global_data field at so+40: unaffected by both stores *)      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).      { assert (Hgd_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).        { apply (load_after_store_other m m1 sb                   (uso + 16) (uso + 40) new_sp_v gd_ptr                   Hstore1 Hgd_load). right. lia. }        apply (load_after_store_other m1 m' sb                 (uso + 8) (uso + 40) result_v gd_ptr                 Hstore2 Hgd_m1). right. lia. }
      (* trap_sp field at so+48: unaffected by both stores *)      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).      { assert (Hts_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).        { apply (load_after_store_other m m1 sb                   (uso + 16) (uso + 48) new_sp_v ts_ptr                   Hstore1 Hts_load). right. lia. }        apply (load_after_store_other m1 m' sb                 (uso + 8) (uso + 48) result_v ts_ptr                 Hstore2 Hts_m1). right. lia. }
      split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
      (* 1. _s is in le' *)      { subst le'.        rewrite PTree.gso by (simpl; congruence).        rewrite PTree.gso by (simpl; congruence).        rewrite PTree.gso by (simpl; congruence).        rewrite PTree.gso by (simpl; congruence).        exact Hle_s. }
      (* 2. pc field -- unchanged by handler *)      { exists pc_ptr. split.        - exact Hpc_load'.        - simpl. exact Hpc_rel. }
      (* 3. accu field -- updated to Val_int (Z.quot a b) *)      { exists result_v. split.        - exact Haccu_load'.        - simpl.          unfold result_v, div_result, a_untagged, divisor, a_tagged, b_tagged.          rewrite tagged_divint_arith by assumption.          constructor. }
      (* 4. sp field -- updated to sp + 8 (stack tail) *)      { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)).        split; [| split; [| split; [| split; [| split]]]].        - exact Hsp_load'.        - reflexivity.        - simpl.          eapply (stack_repr_store_other_block hm m1 m' _ sp_b                   (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) result_v).          + eapply (stack_repr_store_other_block hm m m1 _ sp_b                     (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16) new_sp_v).            * exact Hstack_repr_rest.            * exact Hstore1.            * intro Heq; exact (Hblock_sep (eq_sym Heq)).          + exact Hstore2.          + intro Heq; exact (Hblock_sep (eq_sym Heq)).        - exact Hsp_ne_sb.        - exact Hsp_ne_gb.        - exact Hcb_ne_sp. }
      (* 5. env field -- unchanged *)      { exists env_v. split.        - exact Henv_load'.        - simpl. exact Henv_repr. }
      (* 6. extra_args field -- unchanged *)      { simpl. exact Hextra_load'. }
      (* 7. global_data field -- unchanged *)      { exists gd_ptr. split; [| split; [| split]].        - exact Hgd_load'.        - simpl. exact Hgd_eq.        - simpl.          eapply (global_repr_store_other_block hm m1 m' _ _ _ sb (uso + 8) result_v).          + eapply (global_repr_store_other_block hm m m1 _ _ _ sb (uso + 16) new_sp_v).            * exact Hglobal_repr.            * exact Hstore1.            * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).          + exact Hstore2.          + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).        - exact Hgb_ne_sb. }
      (* 8. trap_sp field -- unchanged *)      { exists ts_ptr. split.        - exact Hts_load'.        - simpl. exact Htrap_rel. }    }
Qed.