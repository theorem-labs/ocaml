(* MODINT_correct.v -- correctness proof for the MODINT handler.
   C handler computes: (((accu >> 1) % divisor) << 1) + 1
     where divisor = (stack_top >> 1)
   Tagged arithmetic: shr untags both operands, mod, shl+1 retags.
   For tagged ints a_tagged = a*2+1, b_tagged = b*2+1:
     divisor = ((b*2+1) >> 1) = b (modulo half_modulus)
     ((a*2+1) >> 1) = a (modulo half_modulus)
     (a % b) << 1 + 1 = (Z.rem a b)*2+1 = tagged(Z.rem a b)
   Rocq handler: handle_MODINT pops stack, computes Z.rem, with
   division-by-zero check.

   Uses handler_correct to exclude the b=0 (do_raise) case.
   The do_raise path involves complex trap frame manipulation that
   we sidestep with a nonzero-divisor precondition. *)

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
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.
Local Notation exec := (exec_stmt function_entry1 clight_ge).

(* ================================================================== *)
(* Semantic lemmas for MODINT C code                                   *)
(* ================================================================== *)

(* long >> 1 (arithmetic shift right) *)
Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* long << 1 *)
Local Lemma sem_shl_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.shl n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* long + int(1) *)
Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* long == int(0) when the long is zero *)
Local Lemma sem_cmp_eq_long_int_0_true : forall m,
  sem_binary_operation (genv_cenv clight_ge) Oeq
    (Vlong Int64.zero) tlong (Vint (Int.repr 0)) tint m
    = Some (Vint Int.one).
Proof. intros. reflexivity. Qed.

(* long == int(0) when the long is nonzero *)
Local Lemma sem_cmp_eq_long_int_0_false : forall n m,
  n <> Int64.zero ->
  sem_binary_operation (genv_cenv clight_ge) Oeq
    (Vlong n) tlong (Vint (Int.repr 0)) tint m
    = Some (Vint Int.zero).
Proof.
  intros n m Hne.
  unfold sem_binary_operation, sem_cmp.
  simpl classify_cmp.
  unfold sem_binarith.
  change (classify_binarith tlong tint) with (bin_case_l Signed).
  simpl. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. simpl.
  change (Int64.repr (Int.signed (Int.repr 0))) with Int64.zero.
  rewrite Int64.eq_false by exact Hne.
  reflexivity.
Qed.

(* bool_val of Vint Int.zero *)
Local Lemma bool_val_false : forall m,
  bool_val (Vint Int.zero) tint m = Some false.
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Mod operation on longs: the sem_binary_operation for Omod           *)
(* ================================================================== *)

(* sem_binary_operation Omod on two nonzero longs uses Int64.mods
   provided the divisor is nonzero and it's not the overflow case. *)
Local Lemma sem_mod_long_long : forall n1 n2 m,
  Int64.eq n2 Int64.zero = false ->
  (Int64.eq n1 (Int64.repr Int64.min_signed) &&
   Int64.eq n2 Int64.mone)%bool = false ->
  sem_binary_operation (genv_cenv clight_ge) Omod
    (Vlong n1) tlong (Vlong n2) tlong m
    = Some (Vlong (Int64.mods n1 n2)).
Proof.
  intros n1 n2 m Hne_zero Hno_overflow.
  unfold sem_binary_operation, sem_mod, sem_binarith.
  change (classify_binarith tlong tlong) with (bin_case_l Signed).
  simpl. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. simpl.
  rewrite Hne_zero.
  rewrite Hno_overflow.
  reflexivity.
Qed.

(* ================================================================== *)
(* Tagged modular arithmetic identity                                  *)
(* ================================================================== *)

(* Reuse MULINT's shr_tagged_eqm_half *)
Local Lemma shr_tagged_eqm_half : forall n,
  exists k, Int64.signed (Int64.repr (n * 2 + 1)) / 2 = n + k * Int64.half_modulus.
Proof.
  intros n.
  pose proof (Int64.eqm_signed_unsigned (Int64.repr (n * 2 + 1))) as [k1 Hk1].
  pose proof (Int64.eqm_unsigned_repr (n * 2 + 1)) as [k2 Hk2].
  set (j := (k1 - k2)%Z).
  assert (Hsigned : Int64.signed (Int64.repr (n * 2 + 1)) = n * 2 + 1 + j * Int64.modulus).
  { unfold j. nia. }
  rewrite Hsigned.
  assert (HM : Int64.modulus = Int64.half_modulus * 2) by (vm_compute; reflexivity).
  rewrite HM.
  replace (n * 2 + 1 + j * (Int64.half_modulus * 2))%Z
    with ((n + j * Int64.half_modulus) * 2 + 1)%Z by lia.
  rewrite Z.div_add_l by lia.
  change (1 / 2)%Z with 0%Z.
  exists j. lia.
Qed.

(* The shr of a tagged integer *)
Local Lemma shr_tagged_val : forall n,
  Int64.shr (Int64.repr (n * 2 + 1)) (Int64.repr 1)
  = Int64.repr (Int64.signed (Int64.repr (n * 2 + 1)) / 2).
Proof.
  intros. unfold Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1)%Z with 2%Z.
  reflexivity.
Qed.

(* eqm helper for addition *)
Local Lemma eqm64_add : forall x x' y y',
  Int64.eqm x x' -> Int64.eqm y y' -> Int64.eqm (x + y) (x' + y').
Proof.
  intros x x' y y' [kx Hx] [ky Hy].
  exists (kx + ky)%Z. nia.
Qed.

(* The full tagged MODINT identity.
   We prove it under a precondition that avoids the overflow edge case
   and ensures the divisor is representable. *)

(* Key insight: Z.rem a b = Z.rem (a + k1*H) (b + k2*H) when
   b + k2*H has the same sign behavior.  But this is NOT generally true.
   Instead, we work at the Int64 level: Int64.mods computes
   Z.rem(signed(x), signed(y)), which is what we need. *)

(* We need to show that the C computation:
     ((shr(tagged_a, 1) mod_s shr(tagged_b, 1)) shl 1) + 1
   equals
     tagged(Z.rem a b)
   i.e.
     Int64.repr((Z.rem a b) * 2 + 1)

   where shr(tagged_x, 1) = Int64.repr(signed(tagged_x) / 2)
   and mod_s = Int64.mods = Z.rem on signed values.
*)

(* We prove this under a precondition that b is nonzero and the
   shift/mod operations don't hit edge cases.
   The precondition is captured in step_pre. *)

(* For the proof, we use an abstract approach: define the divisor_val
   and prove the needed properties directly. *)

(* Signed shift right of tagged value gives back the original integer.
   Mirrors DIVINT's shr_tagged_repr. *)
Local Lemma shr_tagged_repr : forall n,
  Int64.min_signed <= n * 2 + 1 <= Int64.max_signed ->
  Int64.shr (Int64.repr (n * 2 + 1)) (Int64.repr 1) = Int64.repr n.
Proof.
  intros n Hrange.
  unfold Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1.
  rewrite Int64.signed_repr by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  f_equal.
  replace ((n * 2 + 1) / 2) with n by (apply Z.div_unique with 1; lia).
  reflexivity.
Qed.

(* Helper: nonzero tagged int has nonzero shr *)
Local Lemma shr_tagged_nonzero : forall b,
  b <> 0%Z ->
  Int64.min_signed <= b * 2 + 1 <= Int64.max_signed ->
  Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1) <> Int64.zero.
Proof.
  intros b Hb_ne Hrange.
  rewrite shr_tagged_repr by lia.
  intro Heq.
  apply (f_equal Int64.signed) in Heq.
  rewrite Int64.signed_zero in Heq.
  rewrite Int64.signed_repr in Heq.
  - exact (Hb_ne Heq).
  - unfold Int64.min_signed, Int64.max_signed in *.
    generalize Int64.half_modulus_pos. lia.
Qed.

(* Helper: the shr of tagged int and its signed value *)
Local Lemma shr_tagged_signed : forall n,
  Int64.min_signed <= n * 2 + 1 <= Int64.max_signed ->
  Int64.signed (Int64.shr (Int64.repr (n * 2 + 1)) (Int64.repr 1)) = n.
Proof.
  intros n Hrange.
  rewrite shr_tagged_repr by lia.
  apply Int64.signed_repr.
  unfold Int64.min_signed, Int64.max_signed in *.
  generalize Int64.half_modulus_pos. lia.
Qed.

(* Overflow check: the mods guards pass when a, b are in range *)
Local Lemma modint_no_overflow : forall a b,
  Int64.min_signed <= a * 2 + 1 <= Int64.max_signed ->
  Int64.min_signed <= b * 2 + 1 <= Int64.max_signed ->
  (Int64.eq (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))
            (Int64.repr Int64.min_signed) &&
   Int64.eq (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1))
            Int64.mone)%bool = false.
Proof.
  intros a b Ha_range Hb_range.
  apply Bool.andb_false_intro1.
  rewrite shr_tagged_repr by lia.
  apply Int64.eq_false.
  intro Heq.
  apply (f_equal Int64.signed) in Heq.
  rewrite Int64.signed_repr in Heq.
  - unfold Int64.min_signed, Int64.max_signed in *.
    change Int64.half_modulus with 9223372036854775808%Z in *.
    vm_compute in Heq. lia.
  - unfold Int64.min_signed, Int64.max_signed in *.
    change Int64.half_modulus with 9223372036854775808%Z in *. lia.
Qed.

(* The main tagged MODINT arithmetic identity *)
Local Lemma tagged_modint_arith : forall a b,
  b <> 0%Z ->
  Int64.min_signed <= a * 2 + 1 <= Int64.max_signed ->
  Int64.min_signed <= b * 2 + 1 <= Int64.max_signed ->
  Int64.add
    (Int64.shl
      (Int64.mods
        (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))
        (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)))
      (Int64.repr 1))
    (Int64.repr 1)
  = Int64.repr ((Z.rem a b) * 2 + 1).
Proof.
  intros a b Hb_ne Ha_range Hb_range.
  rewrite (shr_tagged_repr a) by lia.
  rewrite (shr_tagged_repr b) by lia.
  unfold Int64.mods.
  rewrite (Int64.signed_repr a)
    by (unfold Int64.min_signed, Int64.max_signed in *;
        generalize Int64.half_modulus_pos; lia).
  rewrite (Int64.signed_repr b)
    by (unfold Int64.min_signed, Int64.max_signed in *;
        generalize Int64.half_modulus_pos; lia).
  unfold Int64.shl, Int64.add.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
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
(* Divisor nonzero (for Int64.eq guard in sem_mod)                     *)
(* ================================================================== *)

Local Lemma shr_tagged_eq_false : forall b,
  b <> 0%Z ->
  Int64.min_signed <= b * 2 + 1 <= Int64.max_signed ->
  Int64.eq (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)) Int64.zero = false.
Proof.
  intros b Hb_ne Hb_range.
  apply Int64.eq_false.
  apply shr_tagged_nonzero; assumption.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_MODINT_correct :
    handler_correct handle_MODINT f_instr_MODINT
      (fun _ _ s ard =>
         match s.(Machine.accu), s.(Machine.stack) with
         | Val_int a, Val_int b :: _ =>
             b <> 0%Z /\
             Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
             Int64.min_signed <= b * 2 + 1 <= Int64.max_signed /\
             int_vlong ard a /\
             int_vlong ard b
         | _, _ => True
         end)
      (fun _ s =>
         match s.(Machine.accu), s.(Machine.stack) with
         | Val_int _, Val_int b :: _ => Z.eqb b 0 = true
         | _, _ => True
         end)
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handle_MODINT.

  (* Case split on accu *)
  destruct (Machine.accu s) as [a| | |] eqn:Haccu_eq;
    try (exact I).
  destruct (Machine.stack s) as [|v_hd v_tl] eqn:Hstk;
    try (exact I).
  destruct v_hd as [b| | |] eqn:Hvhd;
    try (exact I).

  (* Now accu = Val_int a, stack = Val_int b :: v_tl *)
  destruct (Z.eqb b 0) eqn:Hb_zero.

  (* ================================================================ *)
  (* Case b = 0: do_raise -- complex, handled by error predicate      *)
  (* ================================================================ *)
  {
    (* do_raise returns either Error or Step depending on trap_sp *)
    unfold do_raise.
    destruct (Nat.eqb (trap_sp s) 0) eqn:Htrap.
    - (* trap_sp = 0: Error "unhandled exception" *)
      reflexivity.
    - (* trap_sp != 0: do_raise returns Step or Error depending on frame *)
      destruct (skipn (Datatypes.length (Machine.stack s) - trap_sp s)
                      (Machine.stack s)) as [|? frame_rest] eqn:Hframe.
      + (* empty frame: Error *)
        reflexivity.
      + destruct v as [handler_pc| | |]; try reflexivity.
        destruct frame_rest as [|? fr2]; try reflexivity.
        destruct v as [prev_tsp| | |]; try reflexivity.
        destruct fr2 as [|saved_env fr3]; try reflexivity.
        destruct fr3 as [|? fr4]; try reflexivity.
        destruct v as [saved_ea| | |]; try reflexivity.
        (* Step case from do_raise: step_pre must be proved False *)
        intros ard _ Hpre.
        destruct Hpre as [Hb_ne _].
        (* Hb_ne: b <> 0, Hb_zero: Z.eqb b 0 = true *)
        rewrite Z.eqb_eq in Hb_zero. exfalso. exact (Hb_ne Hb_zero).
  }

  (* ================================================================ *)
  (* Case b <> 0: Step -- main proof                                   *)
  (* ================================================================ *)
  {
    intros ard Hpre_abs Hpre_extra.
    destruct Hpre_extra as (Hb_ne & Ha_range & Hb_range & Hint_tagged_a & Hint_tagged_b).

    (* Unpack abs_rel_with_ard *)
    set (sb := ar_sptr_block ard) in *.
    set (so := ar_sptr_ofs ard) in *.
    set (hm := ar_heap_map ard) in *.
    set (cb := ar_code_base_block ard) in *.
    set (co := ar_code_base_ofs ard) in *.
    destruct Hpre_abs as (Hle_s &
      [pc_ptr [Hpc_load Hpc_rel]] &
      [accu_v [Haccu_load Haccu_repr]] &
      Hsp_data &
      [env_v [Henv_load Henv_repr]] &
      Hextra_load &
      [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
      [ts_ptr [Hts_load Htrap_rel]] &
      Hsb_writable).
    destruct Hsp_data as [sp_ptr [sp_b [sp_ofs (Hsp_load & Hsp_eq & Hstack_repr
      & Hsp_ne_sb & Hsp_ne_gb & Hcb_ne_sp & Hsp_ge8 & Hsp_bound & Hsp_writable & Hsp_align)]]].
    subst sp_ptr.

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound.
    fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    set (Hblock_sep := Hsp_ne_sb).
    pose proof (global_block_ne_sptr ard) as Hgb_ne.
    fold sb in Hgb_ne.

    (* Accu is Val_int a *)
    rewrite Haccu_eq in Haccu_repr.
    inversion Haccu_repr; subst accu_v.
    2: { exfalso. destruct (Hint_tagged_a _ Haccu_repr) as [z Hz]. discriminate Hz. }
    rename H0 into Haccu_is_int.

    (* Extract stack head *)
    rewrite Hstk in Hstack_repr.
    inversion Hstack_repr as [| ? ? ? ? cv0 Hload_sp0 Hval_repr0 Hstack_repr_rest].
    revert Hgd_load Hgd_eq Hglobal_repr.
    subst.
    intros Hgd_load Hgd_eq Hglobal_repr.

    (* Stack head is Val_int b *)
    inversion Hval_repr0; subst cv0.
    2: { exfalso. destruct (Hint_tagged_b _ Hval_repr0) as [z Hz]. discriminate Hz. }
    rename H0 into Hstk_is_int.

    (* Composite environment facts *)
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    (* --- Abbreviations for C-level values --- *)
    set (b_tagged := Int64.repr (b * 2 + 1)).
    set (a_tagged := Int64.repr (a * 2 + 1)).
    set (divisor_val := Int64.shr b_tagged (Int64.repr 1)).
    set (a_untagged := Int64.shr a_tagged (Int64.repr 1)).
    set (mod_result := Int64.mods a_untagged divisor_val).
    set (result_v := Vlong (Int64.add (Int64.shl mod_result (Int64.repr 1))
                                       (Int64.repr 1))).

    (* --- Store 1: sp field (so+16) gets sp+1 = Vptr sp_b (sp_ofs + 8) --- *)
    set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
    destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) new_sp_v)
      as [m1 Hstore1].

    (* --- After store 1: load accu from m1 --- *)
    assert (Haccu_load_m1 :
      Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vlong a_tagged)).
    { apply (load_after_store_other m m1 sb
               (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8)
               new_sp_v (Vlong a_tagged)
               Hstore1 Haccu_load). left. lia. }

    (* --- After store 1: load *sp from m1 (different block) --- *)
    assert (Hload_sp0_m1 :
      Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) = Some (Vlong b_tagged)).
    { erewrite Mem.load_store_other.
      - exact Hload_sp0.
      - exact Hstore1.
      - left. exact Hblock_sep. }

    (* --- Store 2: accu field (so+8) gets the tagged mod result --- *)
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.
    destruct (store_succeeds_sb m1 sb so 8 (Vlong a_tagged) Hsb_writable_m1 Haccu_load_m1 ltac:(lia) ltac:(lia) result_v)
      as [m' Hstore2].

    (* --- Key properties of divisor_val --- *)
    assert (Hdivisor_ne_zero : divisor_val <> Int64.zero).
    { apply shr_tagged_nonzero; assumption. }
    assert (Hdivisor_eq_false : Int64.eq divisor_val Int64.zero = false).
    { apply Int64.eq_false. exact Hdivisor_ne_zero. }
    assert (Hno_overflow :
      (Int64.eq a_untagged (Int64.repr Int64.min_signed) &&
       Int64.eq divisor_val Int64.mone)%bool = false).
    { apply (modint_no_overflow a b Ha_range Hb_range). }

    (* Witnesses *)
    set (le' := PTree.set _t'2 (Vlong a_tagged)
                  (PTree.set _divisor (Vlong divisor_val)
                    (PTree.set _t'3 (Vlong b_tagged)
                      (PTree.set _t'1 (Vptr sp_b sp_ofs) le)))).
    exists le'. exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: manual bigstep construction                             *)
    (* ============================================================== *)
    {
      set (le1 := PTree.set _t'1 (Vptr sp_b sp_ofs) le).
      set (le2 := PTree.set _t'3 (Vlong b_tagged) le1).
      set (le3 := PTree.set _divisor (Vlong divisor_val) le2).
      assert (Hle'_eq : le' = PTree.set _t'2 (Vlong a_tagged) le3).
      { subst le' le3 le2 le1. reflexivity. }

      (* Outermost: PartA ; PartB *)
      apply exec_Sseq_1 with (t1 := E0) (le1 := le3) (m1 := m1).

      (* PartA: (Sset _t'1 + Sassign s->sp) ; (Sset _t'3 + Sset _divisor) *)
      {
        apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m1).
        { apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m).
          { apply exec_Sset.
            eapply eval_Elvalue.
            - eapply eval_Efield_struct.
              + eapply eval_Elvalue.
                * eapply eval_Ederef. eapply eval_Etempvar. exact Hle_s.
                * apply deref_loc_copy. reflexivity.
              + reflexivity.
              + exact Hco.
              + exact Hsp_offset.
            - apply deref_loc_value with (chunk := Mptr).
              + reflexivity.
              + simpl. rewrite Mptr_Mint64.
                fold so.
                rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
                exact Hsp_load. }
          { eapply exec_Sassign.
            - eapply eval_Efield_struct.
              + eapply eval_Elvalue.
                * eapply eval_Ederef. eapply eval_Etempvar.
                  subst le1. rewrite PTree.gso by (compute; congruence). exact Hle_s.
                * apply deref_loc_copy. reflexivity.
              + reflexivity.
              + exact Hco.
              + exact Hsp_offset.
            - eapply eval_Ebinop.
              + eapply eval_Etempvar. subst le1. rewrite PTree.gss. reflexivity.
              + eapply eval_Econst_int.
              + apply sem_add_sp_1.
            - apply sem_cast_ptr_to_ptr.
            - apply assign_loc_value with (chunk := Mptr).
              + reflexivity.
              + simpl. rewrite Mptr_Mint64.
                fold so.
                rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
                unfold new_sp_v in Hstore1. exact Hstore1. } }
        { apply exec_Sseq_1 with (t1 := E0) (le1 := le2) (m1 := m1).
          { apply exec_Sset.
            eapply eval_Elvalue.
            - eapply eval_Ederef. eapply eval_Etempvar.
              subst le1. rewrite PTree.gss. reflexivity.
            - apply deref_loc_value with (chunk := Mint64).
              + reflexivity.
              + simpl. exact Hload_sp0_m1. }
          { apply exec_Sset.
            eapply eval_Ebinop.
            - eapply eval_Ecast.
              + eapply eval_Etempvar. subst le2. rewrite PTree.gss. reflexivity.
              + apply sem_cast_long_vlong.
            - eapply eval_Econst_int.
            - apply sem_shr_long_int_1. } }
      }

      (* PartB: Sifthenelse ; (Sset _t'2 + Sassign + Sreturn) *)
      {
        apply exec_Sseq_1 with (t1 := E0) (le1 := le3) (m1 := m1).
        (* Sifthenelse *)
        { eapply exec_Sifthenelse.
          - eapply eval_Ebinop.
            + eapply eval_Etempvar. subst le3. rewrite PTree.gss. reflexivity.
            + eapply eval_Econst_int.
            + apply (sem_cmp_eq_long_int_0_false divisor_val m1 Hdivisor_ne_zero).
          - apply bool_val_false.
          - simpl. apply exec_Sskip. }
        (* (Sset _t'2 + Sassign) ; Sreturn *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le') (m1 := m').
        { rewrite Hle'_eq.
          apply exec_Sseq_1 with (t1 := E0)
            (le1 := PTree.set _t'2 (Vlong a_tagged) le3) (m1 := m1).
          (* Sset _t'2 (s->accu) *)
          { apply exec_Sset.
            eapply eval_Elvalue.
            - eapply eval_Efield_struct.
              + eapply eval_Elvalue.
                * eapply eval_Ederef. eapply eval_Etempvar.
                  subst le3 le2 le1.
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  exact Hle_s.
                * apply deref_loc_copy. reflexivity.
              + reflexivity.
              + exact Hco.
              + exact Haccu_offset.
            - apply deref_loc_value with (chunk := Mint64).
              + reflexivity.
              + simpl. fold so.
                rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
                exact Haccu_load_m1. }
          (* Sassign (s->accu) (shl(mod(shr(cast _t'2,1), _divisor),1)+1) *)
          { eapply exec_Sassign.
            - eapply eval_Efield_struct.
              + eapply eval_Elvalue.
                * eapply eval_Ederef. eapply eval_Etempvar.
                  subst le3 le2 le1.
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  exact Hle_s.
                * apply deref_loc_copy. reflexivity.
              + reflexivity.
              + exact Hco.
              + exact Haccu_offset.
            - eapply eval_Ebinop.
              + eapply eval_Ebinop.
                * eapply eval_Ecast.
                  { eapply eval_Ebinop.
                    - eapply eval_Ebinop.
                      + eapply eval_Ecast.
                        * eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
                        * apply sem_cast_long_vlong.
                      + eapply eval_Econst_int.
                      + apply sem_shr_long_int_1.
                    - eapply eval_Etempvar.
                      rewrite PTree.gso by (compute; congruence). subst le3.
                      rewrite PTree.gss. reflexivity.
                    - unfold a_tagged, a_untagged, divisor_val, b_tagged, mod_result in *.
                      apply sem_mod_long_long. exact Hdivisor_eq_false. exact Hno_overflow. }
                  { apply sem_cast_long_vlong. }
                * eapply eval_Econst_int.
                * apply sem_shl_long_int_1.
              + eapply eval_Econst_int.
              + apply sem_add_long_int_1.
            - apply sem_cast_long_vlong.
            - apply assign_loc_value with (chunk := Mint64).
              + reflexivity.
              + simpl. fold so.
                rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
                exact Hstore2. } }
        (* Sreturn 0 *)
        { apply exec_Sreturn_some. eapply eval_Econst_int. }
      }
    }
    (* ============================================================== *)    (* Part 2: abs_rel for post-state                                  *)    (* ============================================================== *)    {      exists ard.      set (uso := Ptrofs.unsigned so) in *.
      (* --- Loads from m' (after store2 at so+8, store1 at so+16 in m1) --- *)
      (* pc field at so+0: unaffected by both stores *)      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).      { assert (Hpc_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some pc_ptr).        { apply (load_after_store_other m m1 sb                   (uso + 16) (uso + 0) new_sp_v pc_ptr                   Hstore1 Hpc_load). left. lia. }        apply (load_after_store_other m1 m' sb                 (uso + 8) (uso + 0) result_v pc_ptr                 Hstore2 Hpc_m1). left. lia. }
      (* sp field at so+16: written by store1, unaffected by store2 *)      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some new_sp_v).      { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some new_sp_v).        { pose proof (load_after_store_same m m1 sb (uso + 16) new_sp_v Hstore1) as Htmp.          unfold new_sp_v in Htmp |- *. simpl Val.load_result in Htmp.          rewrite ptr64_true in Htmp.          exact Htmp. }        apply (load_after_store_other m1 m' sb                 (uso + 8) (uso + 16) result_v new_sp_v                 Hstore2 Hsp_m1). right. lia. }
      (* accu field at so+8: written by store2 *)      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some result_v).      { pose proof (load_after_store_same m1 m' sb (uso + 8) result_v Hstore2) as Htmp.        unfold result_v in Htmp |- *. simpl Val.load_result in Htmp.        exact Htmp. }
      (* env field at so+24: unaffected by both stores *)      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).      { assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).        { apply (load_after_store_other m m1 sb                   (uso + 16) (uso + 24) new_sp_v env_v                   Hstore1 Henv_load). right. lia. }        apply (load_after_store_other m1 m' sb                 (uso + 8) (uso + 24) result_v env_v                 Hstore2 Henv_m1). right. lia. }
      (* extra_args field at so+32: unaffected by both stores *)      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).      { assert (Hextra_m1 : Mem.load Mint64 m1 sb (uso + 32) =                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).        { apply (load_after_store_other m m1 sb                   (uso + 16) (uso + 32) new_sp_v _                   Hstore1 Hextra_load). right. lia. }        apply (load_after_store_other m1 m' sb                 (uso + 8) (uso + 32) result_v _                 Hstore2 Hextra_m1). right. lia. }
      (* global_data field at so+40: unaffected by both stores *)      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).      { assert (Hgd_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).        { apply (load_after_store_other m m1 sb                   (uso + 16) (uso + 40) new_sp_v gd_ptr                   Hstore1 Hgd_load). right. lia. }        apply (load_after_store_other m1 m' sb                 (uso + 8) (uso + 40) result_v gd_ptr                 Hstore2 Hgd_m1). right. lia. }
      (* trap_sp field at so+48: unaffected by both stores *)      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).      { assert (Hts_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).        { apply (load_after_store_other m m1 sb                   (uso + 16) (uso + 48) new_sp_v ts_ptr                   Hstore1 Hts_load). right. lia. }        apply (load_after_store_other m1 m' sb                 (uso + 8) (uso + 48) result_v ts_ptr                 Hstore2 Hts_m1). right. lia. }
      (* 1. _s is in le' *)
      split.
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }
      (* 2. pc field *)
      split.
      { exists pc_ptr. split.
        - exact Hpc_load'.
        - simpl. exact Hpc_rel. }
      (* 3. accu field *)
      split.
      { exists result_v. split.
        - exact Haccu_load'.
        - simpl.
          unfold result_v, mod_result, a_untagged, divisor_val, a_tagged, b_tagged.
          rewrite (tagged_modint_arith a b Hb_ne Ha_range Hb_range).
          constructor. }
      (* 4. sp field *)
      split.
      { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)).
        assert (Hsp_add_ok : Ptrofs.unsigned sp_ofs + 8 < Ptrofs.modulus).
        { rewrite Hstk in Hsp_bound. simpl length in Hsp_bound. lia. }
        split. { exact Hsp_load'. }
        split. { reflexivity. }
        split. { simpl.
          eapply (stack_repr_store_other_block hm cb co m1 m' _ sp_b
                   (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) result_v).
          - eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b
                     (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16) new_sp_v).
            + exact Hstack_repr_rest.
            + exact Hstore1.
            + intro Heq; exact (Hblock_sep (eq_sym Heq)).
          - exact Hstore2.
          - intro Heq; exact (Hblock_sep (eq_sym Heq)). }
        split. { exact Hsp_ne_sb. }
        split. { exact Hsp_ne_gb. }
        split. { exact Hcb_ne_sp. }
        split. { rewrite ptrofs_add_unsigned by lia. lia. }
        split. { simpl length. rewrite ptrofs_add_unsigned by lia.
                 rewrite Hstk in Hsp_bound. simpl length in Hsp_bound. lia. }
        split.
        { intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore2.
        eapply Mem.perm_store_1. exact Hstore1.
        apply Hsp_writable.
        rewrite Hstk. simpl length.
        rewrite ptrofs_add_unsigned in Hofs' by lia.
        simpl length in Hofs'. lia. }
        (* sp_align *)
        simpl.
        rewrite ptrofs_add_unsigned by lia.
        apply Z.divide_add_r. exact Hsp_align. exists 1. lia. }
      (* 5. env field *)
      split.
      { exists env_v. split.
        - exact Henv_load'.
        - simpl. exact Henv_repr. }
      (* 6. extra_args field *)
      split.
      { simpl. exact Hextra_load'. }
      (* 7. global_data field *)
      split.
      { exists gd_ptr.
        split. { exact Hgd_load'. }
        split. { simpl. exact Hgd_eq. }
        split.
        { simpl.
          eapply (global_repr_store_other_block hm cb co m1 m' _ _ _ sb (uso + 8) result_v).
          - eapply (global_repr_store_other_block hm cb co m m1 _ _ _ sb (uso + 16) new_sp_v).
            + exact Hglobal_repr.
            + exact Hstore1.
            + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          - exact Hstore2.
          - intro Heq2; exact (Hgb_ne (eq_sym Heq2)). }
        exact Hgb_ne_sb. }
      (* 8. trap_sp field *)
      split.
      { exists ts_ptr. split.
        - exact Hts_load'.
        - simpl. exact Htrap_rel. }
      (* 9. sb writable *)
      intros ofs' Hofs'.
      eapply Mem.perm_store_1. exact Hstore2.
      eapply Mem.perm_store_1. exact Hstore1.
      apply Hsb_writable. exact Hofs'. }  }
Qed.

(* Exported version with named building-block precondition *)
Theorem verify_MODINT_handler_correct :
    handler_correct handle_MODINT f_instr_MODINT
      divmod_safe
      (fun _ s =>
         match s.(Machine.accu), s.(Machine.stack) with
         | Val_int _, Val_int b :: _ => Z.eqb b 0 = true
         | _, _ => True
         end)
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  apply handler_correct_weaken with
    (sp := fun _ _ s ard =>
       match s.(Machine.accu), s.(Machine.stack) with
       | Val_int a, Val_int b :: _ =>
           b <> 0%Z /\
           Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
           Int64.min_signed <= b * 2 + 1 <= Int64.max_signed /\
           int_vlong ard a /\
           int_vlong ard b
       | _, _ => True
       end).
  - exact verify_MODINT_correct.
  - intros e le m s ard _ Hdm.
    unfold divmod_safe in Hdm.
    destruct Hdm as (a & b & rest & Ha & Hs & Hbne & Hra & Hrb & Hva & Hvb).
    rewrite Ha, Hs. exact (conj Hbne (conj Hra (conj Hrb (conj Hva Hvb)))).
Qed.