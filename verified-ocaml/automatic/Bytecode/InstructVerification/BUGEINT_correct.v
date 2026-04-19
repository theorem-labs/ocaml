(* BUGEINT_correct.v -- BUGEINT handler completeness proof (manual bigstep).

   Rocq handler:
     handle_BUGEINT n target pc' s =
       match s.(accu) with
       | Val_int a => if Z.geb (z_flip_sign n) (z_flip_sign a)
                      then Step (s <|pc := target|>)
                      else Step (s <|pc := pc'|>)
       | _ => Error "BUGEINT: not an integer"
       end

   C handler body (f_instr_BUGEINT):
     preamble: read n from code, advance pc, read accu
     condition: (unsigned long)n >= (unsigned long)(accu >> 1)
     then: branch (pc = pc + *pc)
     else: fall through (pc = pc + 1)

   NO AXIOMS. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.
Local Notation exec := (exec_stmt function_entry1 clight_ge).

(* ================================================================== *)
(* Struct layout                                                       *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_bugeint : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof. rewrite cenv_is_ce. eexists. split; [| split]; reflexivity. Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Local Lemma sem_cast_int_to_ulong : forall i m,
  sem_cast (Vint i) tint tulong m = Some (Vlong (Int64.repr (Int.signed i))).
Proof. intros. unfold sem_cast. simpl classify_cast. simpl. reflexivity. Qed.

Local Lemma sem_cast_long_to_ulong : forall n m,
  sem_cast (Vlong n) tlong tulong m = Some (Vlong n).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof. intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed). simpl. reflexivity. Qed.

Local Lemma sem_ge_ulong_ulong : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Oge
    (Vlong n1) tulong (Vlong n2) tulong m
    = Some (Val.of_bool (negb (Int64.ltu n1 n2))).
Proof. intros. reflexivity. Qed.

Local Lemma bool_val_of_bool : forall b m,
  bool_val (Val.of_bool b) tint m = Some b.
Proof. intros. destruct b; reflexivity. Qed.

Local Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint) (Vint (Int.repr 1)) tint m
  = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof. intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity. Qed.

Local Lemma sem_add_ptr_int_tint : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint) (Vint n) tint m
  = Some (Vptr b (Ptrofs.add ofs
        (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                    (ptrofs_of_int Signed n)))).
Proof. intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity. Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma ptrofs_add_zero : forall ofs,
  Ptrofs.add ofs (Ptrofs.repr 0) = ofs.
Proof. intros. change (Ptrofs.repr 0) with Ptrofs.zero. apply Ptrofs.add_zero. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* ================================================================== *)
(* Comparison lemmas                                                   *)
(* ================================================================== *)

Local Lemma tagged_shr_eq : forall a,
  -4611686018427387904 <= a <= 4611686018427387903 ->
  Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1) = Int64.repr a.
Proof.
  intros a Ha. unfold Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1.
  rewrite Int64.signed_repr.
  2: { assert (Int64.min_signed = -9223372036854775808)%Z by reflexivity.
       assert (Int64.max_signed = 9223372036854775807)%Z by reflexivity. lia. }
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  f_equal. replace ((a * 2 + 1) / 2) with a by (apply Z.div_unique with 1; lia).
  reflexivity.
Qed.

(* Int64.ltu is Z.ltb on unsigned values *)
Local Lemma int64_ltu_ltb : forall x y,
  Int64.ltu x y = Z.ltb (Int64.unsigned x) (Int64.unsigned y).
Proof.
  intros. unfold Int64.ltu.
  destruct (zlt (Int64.unsigned x) (Int64.unsigned y)) as [Hlt|Hge].
  - symmetry. apply Z.ltb_lt. exact Hlt.
  - symmetry. apply Z.ltb_ge. lia.
Qed.

(* For non-negative a, b in [0, 2^62), z_flip_sign adds 2^62, cancels in comparison *)
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

Local Lemma Z_geb_negb_ltb : forall a b, Z.geb a b = negb (Z.ltb a b).
Proof.
  intros. destruct (Z.geb a b) eqn:Hge; destruct (Z.ltb a b) eqn:Hlt;
    try reflexivity;
    rewrite Z.geb_leb in Hge;
    first [rewrite Z.leb_le in Hge | rewrite Z.leb_gt in Hge];
    first [rewrite Z.ltb_lt in Hlt | rewrite Z.ltb_ge in Hlt]; lia.
Qed.

(* Key arithmetic: unsigned >= comparison on tagged ints matches z_flip_sign geb
   for non-negative operands in [0, 2^62) *)
Local Lemma bugeint_arith : forall n a,
  0 <= n ->
  Int.min_signed <= n <= Int.max_signed ->
  0 <= a < 4611686018427387904 ->
  negb (Int64.ltu (Int64.repr (Int.signed (Int.repr n)))
                   (Int64.repr a))
  = Z.geb (z_flip_sign n) (z_flip_sign a).
Proof.
  intros n a Hn_nonneg Hn_range Ha.
  rewrite Z_geb_negb_ltb.
  rewrite Int.signed_repr by exact Hn_range.
  rewrite int64_ltu_ltb.
  rewrite Int64.unsigned_repr.
  2: { unfold Int64.max_unsigned. change Int64.modulus with 18446744073709551616.
       assert (Int.max_signed = 2147483647)%Z by reflexivity. lia. }
  rewrite Int64.unsigned_repr.
  2: { unfold Int64.max_unsigned. change Int64.modulus with 18446744073709551616. lia. }
  unfold z_flip_sign, word_bits. simpl Z.sub.
  change (Z.shiftl 1 62) with (2 ^ 62).
  rewrite Z_lxor_add_pow2 by (try lia; assert (Int.max_signed = 2147483647)%Z by reflexivity; lia).
  rewrite Z_lxor_add_pow2 by lia.
  destruct (Z.ltb_spec n a); destruct (Z.ltb_spec (n + 2^62) (a + 2^62)); try lia; reflexivity.
Qed.

(* Combined: sem_binary_operation Oge on unsigned-cast operands gives the branch condition *)
Local Lemma bugeint_cmp_true : forall n a m,
  0 <= n ->
  Int.min_signed <= n <= Int.max_signed ->
  0 <= a < 4611686018427387904 ->
  Z.geb (z_flip_sign n) (z_flip_sign a) = true ->
  sem_binary_operation (genv_cenv clight_ge) Oge
    (Vlong (Int64.repr (Int.signed (Int.repr n)))) tulong
    (Vlong (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))) tulong m
  = Some (Val.of_bool true).
Proof.
  intros n0 a0 m0 Hn_nonneg Hn_range Ha Hcmp.
  rewrite sem_ge_ulong_ulong. rewrite tagged_shr_eq by lia.
  rewrite (bugeint_arith n0 a0 Hn_nonneg Hn_range Ha). rewrite Hcmp. reflexivity.
Qed.

Local Lemma bugeint_cmp_false : forall n a m,
  0 <= n ->
  Int.min_signed <= n <= Int.max_signed ->
  0 <= a < 4611686018427387904 ->
  Z.geb (z_flip_sign n) (z_flip_sign a) = false ->
  sem_binary_operation (genv_cenv clight_ge) Oge
    (Vlong (Int64.repr (Int.signed (Int.repr n)))) tulong
    (Vlong (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))) tulong m
  = Some (Val.of_bool false).
Proof.
  intros n0 a0 m0 Hn_nonneg Hn_range Ha Hcmp.
  rewrite sem_ge_ulong_ulong. rewrite tagged_shr_eq by lia.
  rewrite (bugeint_arith n0 a0 Hn_nonneg Hn_range Ha). rewrite Hcmp. reflexivity.
Qed.

(* ================================================================== *)
(* pc_rel helpers                                                      *)
(* ================================================================== *)

Local Lemma ptrofs_add_repr : forall a b,
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  intros. rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Local Lemma pc_plus1_eq_gen : forall co0 pc0,
  Ptrofs.add (Ptrofs.add co0 (Ptrofs.repr (pc0 * sizeof_code_t))) (Ptrofs.repr 4)
  = Ptrofs.add co0 (Ptrofs.repr ((pc0 + 1) * sizeof_code_t)).
Proof.
  intros. unfold sizeof_code_t. rewrite Ptrofs.add_assoc. f_equal.
  rewrite ptrofs_add_repr. f_equal. lia.
Qed.

(* ================================================================== *)
(* Field survival                                                      *)
(* ================================================================== *)

Local Ltac prove_field_survives Hstore Hload :=
  apply (load_after_store_other _ _ _ _ _ _ _ Hstore Hload); right; lia.

(* ================================================================== *)
(* Lvalue/Rvalue tactics for s->field reads                            *)
(* ================================================================== *)

Local Ltac eval_s_field_lvalue solve_le co_is Hco Hfld :=
  eapply eval_Efield_struct;
  [ eapply eval_Elvalue;
    [ eapply eval_Ederef; eapply eval_Etempvar; solve_le
    | apply deref_loc_copy; reflexivity ]
  | reflexivity
  | exact Hco
  | exact Hfld ].

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_BUGEINT_correct : forall n target,
    handler_correct (handle_BUGEINT n target) f_instr_BUGEINT
      (fun _ m s ard =>
         ar_code_base_block ard <> ar_sptr_block ard /\
         0 <= n /\
         Int.min_signed <= n <= Int.max_signed /\
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr n)) /\
         (exists ofs_int,
           Mem.load Mint32 m (ar_code_base_block ard)
             (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
                (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))))
           = Some (Vint ofs_int) /\
           Ptrofs.add
             (Ptrofs.add (ar_code_base_ofs ard)
                (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t)))
             (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                         (ptrofs_of_int Signed ofs_int))
           = Ptrofs.add (ar_code_base_ofs ard) (Ptrofs.repr (target * sizeof_code_t))) /\
         match Machine.accu s with
         | Val_int a => 0 <= a < 4611686018427387904
         | _ => False
         end /\
         (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Machine.accu s) cv -> exists z, cv = Vlong z))
      (fun msg s => msg = "BUGEINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros n target e le m s.
  unfold handle_BUGEINT.
  destruct (Machine.accu s) as [a | tag fields | addr | addr ofs_cl] eqn:Haccu_eq.

  (* ================================================================ *)
  (* Case 1: accu = Val_int a                                          *)
  (* ================================================================ *)
  {
    destruct (Z.geb (z_flip_sign n) (z_flip_sign a)) eqn:Hcmp.

    (* ============================================================== *)
    (* Case 1a: z_flip_sign n >= z_flip_sign a => branch taken         *)
    (* ============================================================== *)
    { simpl.
      intros ard Hpre Hstep_pre.
      unfold abs_rel_with_ard in Hpre.
      set (sb := ar_sptr_block ard) in *. set (so := ar_sptr_ofs ard) in *.
      set (hm := ar_heap_map ard) in *. set (cb := ar_code_base_block ard) in *.
      set (co := ar_code_base_ofs ard) in *.
      destruct Hpre as (Hle_s & [pc_ptr [Hpc_load Hpc_rel]] &
        [accu_v [Haccu_load Haccu_repr]] &
        [sp_ptr [sp_b [sp_ofs (Hsp_load & Hsp_eq & Hstack_repr & Hsp_ne_sb & Hsp_ne_gb & Hcb_ne_sp & Hsp_ge8 & Hsp_rep & Hsp_writable & Hsp_align)]]] &
        [env_v [Henv_load Henv_repr]] & Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne]]]] &
        [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
      subst sp_ptr.
      destruct Hstep_pre as (Hcb_ne_sb & Hn_nonneg & Hn_range & Hcode_n & [ofs_int [Hcode_ofs Hofs_eq]] & Haccu_range & Haccu_long).
      pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
      destruct interp_state_co_bugeint as [co_is [Hco [Hpc_offset Haccu_offset]]].
      unfold pc_rel in Hpc_rel. subst pc_ptr.
      set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.
      rewrite Haccu_eq in Haccu_repr. pose proof Haccu_repr as Haccu_repr_rw.
      inversion Haccu_repr; subst accu_v.
      2: { exfalso.
           destruct (Haccu_long _ Haccu_repr_rw) as [z Hz]. discriminate Hz. }

      (* pc_plus1: C pc after advancing past operand *)
      set (pc1 := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
      set (pc1_v := Vptr cb pc1).
      (* branch_pc: C pc after branch *)
      set (branch_ofs := Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                                     (ptrofs_of_int Signed ofs_int)).
      set (branch_pc := Ptrofs.add pc1 branch_ofs).
      set (branch_pc_v := Vptr cb branch_pc).

      (* Store 1: pc <- pc1_v *)
      destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia) pc1_v) as [m1 Hstore1].
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hw1.
      assert (Hs1 : Mem.store Mint64 m sb (Ptrofs.unsigned so) pc1_v = Some m1).
      { pose proof Hstore1 as H. replace (Ptrofs.unsigned so + 0)%Z with (Ptrofs.unsigned so) in H by lia. exact H. }

      (* Code reads survive store1 *)
      assert (Hcn1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) = Some (Vint (Int.repr n))).
      { erewrite Mem.load_store_other. exact Hcode_n. exact Hs1. left. exact Hcb_ne_sb. }
      assert (Hpc1_eq : pc1 = Ptrofs.add co (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))).
      { unfold pc1, pc_ofs. apply pc_plus1_eq_gen. }
      assert (Hco1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t)))) = Some (Vint ofs_int)).
      { erewrite Mem.load_store_other. exact Hcode_ofs. exact Hs1. left. exact Hcb_ne_sb. }

      (* pc1 read from m1 *)
      assert (Hpc_m1_0 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) = Some pc1_v).
      { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 0) pc1_v Hstore1) as H.
        unfold pc1_v in H |- *. rewrite load_result_vptr in H. exact H. }
      assert (Hpc_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so) = Some pc1_v).
      { pose proof Hpc_m1_0 as H. replace (Ptrofs.unsigned so + 0)%Z with (Ptrofs.unsigned so) in H by lia. exact H. }
      assert (Haccu_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vlong (Int64.repr (a * 2 + 1)))).
      { prove_field_survives Hs1 Haccu_load. }

      (* Store 2: pc <- branch_pc_v *)
      destruct (store_succeeds_sb m1 sb so 0 pc1_v Hw1 Hpc_m1_0 ltac:(lia) ltac:(lia) branch_pc_v) as [m2 Hstore2].
      assert (Hs2 : Mem.store Mint64 m1 sb (Ptrofs.unsigned so) branch_pc_v = Some m2).
      { pose proof Hstore2 as H. replace (Ptrofs.unsigned so + 0)%Z with (Ptrofs.unsigned so) in H by lia. exact H. }

      (* Witnesses *)
      set (le' := PTree.set _t'7 (Vint ofs_int) (PTree.set _t'6 (Vptr cb pc1) (PTree.set _t'5 (Vptr cb pc1)
                    (PTree.set _t'3 (Vlong (Int64.repr (a * 2 + 1))) (PTree.set _t'2 (Vint (Int.repr n))
                      (PTree.set _t'1 (Vptr cb pc_ofs) le)))))).
      exists le', m2, (Out_return (Some (Vint (Int.repr 0), tint))).
      split.

      (* Part 1: manual bigstep *)
      {
        set (le1 := PTree.set _t'1 (Vptr cb pc_ofs) le).
        set (le2 := PTree.set _t'2 (Vint (Int.repr n)) le1).
        set (le3 := PTree.set _t'3 (Vlong (Int64.repr (a * 2 + 1))) le2).

        (* Outer: preamble ; Sreturn *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le') (m1 := m2).

        { (* Preamble *)
          apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m1).

          { (* Sset _t'1 ; Sassign pc *)
            apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m).

            { apply exec_Sset.
              eapply eval_Elvalue.
              - eval_s_field_lvalue ltac:(exact Hle_s) co_is Hco Hpc_offset.
              - apply deref_loc_value with (chunk := Mptr).
                + reflexivity.
                + simpl. rewrite Mptr_Mint64.
                  rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
                  exact Hpc_load. }

            { eapply exec_Sassign.
              - eval_s_field_lvalue ltac:(subst le1; rewrite PTree.gso by (compute; congruence); exact Hle_s)
                  co_is Hco Hpc_offset.
              - eapply eval_Ebinop.
                + eapply eval_Etempvar. subst le1. rewrite PTree.gss. reflexivity.
                + eapply eval_Econst_int.
                + apply sem_add_pc_1.
              - apply sem_cast_ptr_tint_to_ptr_tint.
              - apply assign_loc_value with (chunk := Mptr).
                + reflexivity.
                + simpl. rewrite Mptr_Mint64. rewrite (ptrofs_add_zero so).
                  fold pc1_v. exact Hs1. } }

          { (* Sset _t'2 ; (Sset _t'3 ; Sifthenelse) *)
            apply exec_Sseq_1 with (t1 := E0) (le1 := le2) (m1 := m1).

            { apply exec_Sset.
              eapply eval_Elvalue.
              - eapply eval_Ederef. eapply eval_Etempvar. subst le1. rewrite PTree.gss. reflexivity.
              - apply deref_loc_value with (chunk := Mint32).
                + reflexivity.
                + simpl. exact Hcn1. }

            { apply exec_Sseq_1 with (t1 := E0) (le1 := le3) (m1 := m1).

              { apply exec_Sset.
                eapply eval_Elvalue.
                - eval_s_field_lvalue ltac:(subst le2 le1;
                    rewrite PTree.gso by (compute; congruence);
                    rewrite PTree.gso by (compute; congruence); exact Hle_s)
                    co_is Hco Haccu_offset.
                - apply deref_loc_value with (chunk := Mint64).
                  + reflexivity.
                  + simpl. rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
                    exact Haccu_m1. }

              { (* Sifthenelse: unsigned >= comparison true => then branch *)
                eapply exec_Sifthenelse.

                { eapply eval_Ebinop.
                  - eapply eval_Ecast.
                    + eapply eval_Etempvar. subst le3 le2. rewrite PTree.gso by (compute; congruence). rewrite PTree.gss. reflexivity.
                    + apply sem_cast_int_to_ulong.
                  - eapply eval_Ecast.
                    + eapply eval_Ebinop.
                      * eapply eval_Ecast.
                        { eapply eval_Etempvar. subst le3. rewrite PTree.gss. reflexivity. }
                        { apply sem_cast_long_vlong. }
                      * eapply eval_Econst_int.
                      * apply sem_shr_long_int_1.
                    + apply sem_cast_long_to_ulong.
                  - apply (bugeint_cmp_true n a m1 Hn_nonneg Hn_range Haccu_range Hcmp). }

                { apply bool_val_of_bool. }

                { (* Then branch: Sset _t'5 ; Sset _t'6 ; Sset _t'7 ; Sassign *)
                  simpl.
                  set (le4 := PTree.set _t'5 (Vptr cb pc1) le3).
                  set (le5 := PTree.set _t'6 (Vptr cb pc1) le4).
                  set (le6 := PTree.set _t'7 (Vint ofs_int) le5).
                  apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m1).

                  { apply exec_Sset. eapply eval_Elvalue.
                    - eval_s_field_lvalue ltac:(subst le3 le2 le1;
                        rewrite PTree.gso by (compute; congruence);
                        rewrite PTree.gso by (compute; congruence);
                        rewrite PTree.gso by (compute; congruence); exact Hle_s)
                        co_is Hco Hpc_offset.
                    - apply deref_loc_value with (chunk := Mptr).
                      + reflexivity.
                      + simpl. rewrite Mptr_Mint64. rewrite (ptrofs_add_zero so). exact Hpc_m1. }

                  { apply exec_Sseq_1 with (t1 := E0) (le1 := le5) (m1 := m1).

                    { apply exec_Sset. eapply eval_Elvalue.
                      - eval_s_field_lvalue ltac:(subst le4 le3 le2 le1;
                          rewrite PTree.gso by (compute; congruence);
                          rewrite PTree.gso by (compute; congruence);
                          rewrite PTree.gso by (compute; congruence);
                          rewrite PTree.gso by (compute; congruence); exact Hle_s)
                          co_is Hco Hpc_offset.
                      - apply deref_loc_value with (chunk := Mptr).
                        + reflexivity.
                        + simpl. rewrite Mptr_Mint64. rewrite (ptrofs_add_zero so). exact Hpc_m1. }

                    { apply exec_Sseq_1 with (t1 := E0) (le1 := le6) (m1 := m1).

                      { apply exec_Sset. eapply eval_Elvalue.
                        - eapply eval_Ederef. eapply eval_Etempvar. subst le5. rewrite PTree.gss. reflexivity.
                        - apply deref_loc_value with (chunk := Mint32).
                          + reflexivity.
                          + simpl. rewrite Hpc1_eq. exact Hco1. }

                      { eapply exec_Sassign.
                        - eapply eval_Efield_struct.
                          + eapply eval_Elvalue.
                            * eapply eval_Ederef. eapply eval_Etempvar.
                              unfold le'.
                              repeat (rewrite PTree.gso by (compute; congruence)).
                              exact Hle_s.
                            * apply deref_loc_copy. reflexivity.
                          + reflexivity.
                          + exact Hco.
                          + exact Hpc_offset.
                        - eapply eval_Ebinop.
                          + eapply eval_Etempvar. unfold le'.
                            rewrite PTree.gso by (compute; congruence).
                            rewrite PTree.gso by (compute; congruence). rewrite PTree.gss. reflexivity.
                          + eapply eval_Etempvar. unfold le'. rewrite PTree.gss. reflexivity.
                          + apply sem_add_ptr_int_tint.
                        - apply sem_cast_ptr_tint_to_ptr_tint.
                        - apply assign_loc_value with (chunk := Mptr).
                          + reflexivity.
                          + simpl. rewrite Mptr_Mint64. rewrite (ptrofs_add_zero so).
                            fold branch_pc_v. exact Hs2. } } } } } } } }

        { apply exec_Sreturn_some. eapply eval_Econst_int. }
      }

      (* Part 2: abs_rel *)
      {
        assert (Hbr_eq : branch_pc = Ptrofs.add co (Ptrofs.repr (target * sizeof_code_t))).
        { unfold branch_pc, branch_ofs. rewrite Hpc1_eq. exact Hofs_eq. }
        set (new_co := Ptrofs.sub branch_pc (Ptrofs.repr (target * sizeof_code_t))).
        set (ard' := mk_abs_rel sb so hm cb new_co
                       (ar_global_block ard) (ar_global_ofs ard)
                       (ar_stack_block ard) (ar_stack_base_ofs ard)
                       (ar_code_ne_sptr ard) (ar_code_ne_global ard)
                       (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
        exists ard'. set (uso := Ptrofs.unsigned so) in *.

        assert (Hpc2 : Mem.load Mint64 m2 sb (uso + 0) = Some branch_pc_v).
        { pose proof (load_after_store_same m1 m2 sb (uso + 0) branch_pc_v Hstore2) as H.
          unfold branch_pc_v in H |- *. rewrite load_result_vptr in H. exact H. }
        assert (Ha2 : Mem.load Mint64 m2 sb (uso + 8) = Some (Vlong (Int64.repr (a * 2 + 1)))).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 8) = Some (Vlong (Int64.repr (a * 2 + 1)))) by (prove_field_survives Hs1 Haccu_load).
          prove_field_survives Hs2 Hx. }
        assert (Hs2' : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b sp_ofs)) by (prove_field_survives Hs1 Hsp_load).
          prove_field_survives Hs2 Hx. }
        assert (He2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 24) = Some env_v) by (prove_field_survives Hs1 Henv_load).
          prove_field_survives Hs2 Hx. }
        assert (Hx2 : Mem.load Mint64 m2 sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))) by (prove_field_survives Hs1 Hextra_load).
          prove_field_survives Hs2 Hx. }
        assert (Hg2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr) by (prove_field_survives Hs1 Hgd_load).
          prove_field_survives Hs2 Hx. }
        assert (Ht2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr) by (prove_field_survives Hs1 Hts_load).
          prove_field_survives Hs2 Hx. }

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
        - subst le'. repeat (rewrite PTree.gso by (compute; congruence)). exact Hle_s.
        - exists branch_pc_v. split. exact Hpc2. simpl. unfold pc_rel, branch_pc_v. f_equal. unfold new_co.
          rewrite Ptrofs.sub_add_opp. rewrite Ptrofs.add_assoc.
          rewrite (Ptrofs.add_commut (Ptrofs.neg _) _). rewrite <- Ptrofs.sub_add_opp.
          rewrite Ptrofs.sub_idem. symmetry. apply Ptrofs.add_zero.
        - exists (Vlong (Int64.repr (a * 2 + 1))). split. exact Ha2. simpl. rewrite Haccu_eq. apply vr_int.
        - exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
          + exact Hs2'.
          + reflexivity.
          + simpl. eapply stack_repr_co_shift. eapply (stack_repr_store_other_block hm cb co m1 m2 _ sp_b sp_ofs sb uso branch_pc_v).
            * eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b sp_ofs sb uso pc1_v).
              exact Hstack_repr. exact Hs1. intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
            * exact Hs2. * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          + exact Hsp_ne_sb. + exact Hsp_ne_gb. + exact Hcb_ne_sp. + exact Hsp_ge8. + exact Hsp_rep.
          + intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hs2. eapply Mem.perm_store_1. exact Hs1. apply Hsp_writable. exact Hofs'.
          + exact Hsp_align.
        - exists env_v. split. exact He2. simpl. eapply val_repr_co_shift. exact Henv_repr.
        - simpl. exact Hx2.
        - exists gd_ptr. split; [| split; [| split]].
          + exact Hg2. + simpl. exact Hgd_eq.
          + simpl. eapply global_repr_co_shift. eapply (global_repr_store_other_block hm cb co m1 m2 _ _ _ sb uso branch_pc_v).
            * eapply (global_repr_store_other_block hm cb co m m1 _ _ _ sb uso pc1_v).
              exact Hglobal_repr. exact Hs1. intro Heq; exact (Hgb_ne (eq_sym Heq)).
            * exact Hs2. * intro Heq; exact (Hgb_ne (eq_sym Heq)).
          + exact Hgb_ne.
        - exists ts_ptr. split. exact Ht2. simpl. exact Htrap_rel.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hs2. eapply Mem.perm_store_1. exact Hs1.
          apply Hsb_writable. exact Hofs'.
      }
    }

    (* ============================================================== *)
    (* Case 1b: z_flip_sign n < z_flip_sign a => fall through          *)
    (* ============================================================== *)
    { simpl.
      intros ard Hpre Hstep_pre.
      unfold abs_rel_with_ard in Hpre.
      set (sb := ar_sptr_block ard) in *. set (so := ar_sptr_ofs ard) in *.
      set (hm := ar_heap_map ard) in *. set (cb := ar_code_base_block ard) in *.
      set (co := ar_code_base_ofs ard) in *.
      destruct Hpre as (Hle_s & [pc_ptr [Hpc_load Hpc_rel]] &
        [accu_v [Haccu_load Haccu_repr]] &
        [sp_ptr [sp_b [sp_ofs (Hsp_load & Hsp_eq & Hstack_repr & Hsp_ne_sb & Hsp_ne_gb & Hcb_ne_sp & Hsp_ge8 & Hsp_rep & Hsp_writable & Hsp_align)]]] &
        [env_v [Henv_load Henv_repr]] & Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne]]]] &
        [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
      subst sp_ptr.
      destruct Hstep_pre as (Hcb_ne_sb & Hn_nonneg & Hn_range & Hcode_n & [ofs_int [Hcode_ofs Hofs_eq]] & Haccu_range & Haccu_long).
      pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
      destruct interp_state_co_bugeint as [co_is [Hco [Hpc_offset Haccu_offset]]].
      unfold pc_rel in Hpc_rel. subst pc_ptr.
      set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.
      rewrite Haccu_eq in Haccu_repr. pose proof Haccu_repr as Haccu_repr_rw.
      inversion Haccu_repr; subst accu_v.
      2: { exfalso.
           destruct (Haccu_long _ Haccu_repr_rw) as [z Hz]. discriminate Hz. }

      set (pc1 := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
      set (pc1_v := Vptr cb pc1).
      set (pc2 := Ptrofs.add pc1 (Ptrofs.repr 4)).
      set (pc2_v := Vptr cb pc2).

      (* Store 1 *)
      destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia) pc1_v) as [m1 Hstore1].
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hw1.
      assert (Hs1 : Mem.store Mint64 m sb (Ptrofs.unsigned so) pc1_v = Some m1).
      { pose proof Hstore1 as H. replace (Ptrofs.unsigned so + 0)%Z with (Ptrofs.unsigned so) in H by lia. exact H. }
      assert (Hcn1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) = Some (Vint (Int.repr n))).
      { erewrite Mem.load_store_other. exact Hcode_n. exact Hs1. left. exact Hcb_ne_sb. }
      assert (Hpc_m1_0 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) = Some pc1_v).
      { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 0) pc1_v Hstore1) as H.
        unfold pc1_v in H |- *. rewrite load_result_vptr in H. exact H. }
      assert (Hpc_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so) = Some pc1_v).
      { pose proof Hpc_m1_0 as H. replace (Ptrofs.unsigned so + 0)%Z with (Ptrofs.unsigned so) in H by lia. exact H. }
      assert (Haccu_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vlong (Int64.repr (a * 2 + 1)))).
      { prove_field_survives Hs1 Haccu_load. }

      (* Store 2 *)
      destruct (store_succeeds_sb m1 sb so 0 pc1_v Hw1 Hpc_m1_0 ltac:(lia) ltac:(lia) pc2_v) as [m2 Hstore2].
      assert (Hs2 : Mem.store Mint64 m1 sb (Ptrofs.unsigned so) pc2_v = Some m2).
      { pose proof Hstore2 as H. replace (Ptrofs.unsigned so + 0)%Z with (Ptrofs.unsigned so) in H by lia. exact H. }

      set (le' := PTree.set _t'4 (Vptr cb pc1) (PTree.set _t'3 (Vlong (Int64.repr (a * 2 + 1)))
                    (PTree.set _t'2 (Vint (Int.repr n)) (PTree.set _t'1 (Vptr cb pc_ofs) le)))).
      exists le', m2, (Out_return (Some (Vint (Int.repr 0), tint))).
      split.

      (* Part 1: manual bigstep *)
      {
        set (le1 := PTree.set _t'1 (Vptr cb pc_ofs) le).
        set (le2 := PTree.set _t'2 (Vint (Int.repr n)) le1).
        set (le3 := PTree.set _t'3 (Vlong (Int64.repr (a * 2 + 1))) le2).

        apply exec_Sseq_1 with (t1 := E0) (le1 := le') (m1 := m2).

        { apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m1).

          { apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m).
            { apply exec_Sset. eapply eval_Elvalue.
              - eval_s_field_lvalue ltac:(exact Hle_s) co_is Hco Hpc_offset.
              - apply deref_loc_value with (chunk := Mptr). reflexivity.
                simpl. rewrite Mptr_Mint64. rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)). exact Hpc_load. }
            { eapply exec_Sassign.
              - eval_s_field_lvalue ltac:(subst le1; rewrite PTree.gso by (compute; congruence); exact Hle_s)
                  co_is Hco Hpc_offset.
              - eapply eval_Ebinop. eapply eval_Etempvar. subst le1. rewrite PTree.gss. reflexivity. eapply eval_Econst_int. apply sem_add_pc_1.
              - apply sem_cast_ptr_tint_to_ptr_tint.
              - apply assign_loc_value with (chunk := Mptr). reflexivity.
                simpl. rewrite Mptr_Mint64. rewrite (ptrofs_add_zero so). fold pc1_v. exact Hs1. } }

          { apply exec_Sseq_1 with (t1 := E0) (le1 := le2) (m1 := m1).
            { apply exec_Sset. eapply eval_Elvalue.
              - eapply eval_Ederef. eapply eval_Etempvar. subst le1. rewrite PTree.gss. reflexivity.
              - apply deref_loc_value with (chunk := Mint32). reflexivity. simpl. exact Hcn1. }

            { apply exec_Sseq_1 with (t1 := E0) (le1 := le3) (m1 := m1).
              { apply exec_Sset. eapply eval_Elvalue.
                - eval_s_field_lvalue ltac:(subst le2 le1;
                    rewrite PTree.gso by (compute; congruence);
                    rewrite PTree.gso by (compute; congruence); exact Hle_s)
                    co_is Hco Haccu_offset.
                - apply deref_loc_value with (chunk := Mint64). reflexivity.
                  simpl. rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)). exact Haccu_m1. }

              { (* Sifthenelse: comparison false => else branch *)
                eapply exec_Sifthenelse.
                { eapply eval_Ebinop.
                  - eapply eval_Ecast.
                    + eapply eval_Etempvar. subst le3 le2. rewrite PTree.gso by (compute; congruence). rewrite PTree.gss. reflexivity.
                    + apply sem_cast_int_to_ulong.
                  - eapply eval_Ecast.
                    + eapply eval_Ebinop.
                      * eapply eval_Ecast. eapply eval_Etempvar. subst le3. rewrite PTree.gss. reflexivity.
                        apply sem_cast_long_vlong.
                      * eapply eval_Econst_int.
                      * apply sem_shr_long_int_1.
                    + apply sem_cast_long_to_ulong.
                  - apply (bugeint_cmp_false n a m1 Hn_nonneg Hn_range Haccu_range Hcmp). }
                { apply bool_val_of_bool. }
                { simpl.
                  set (le4 := PTree.set _t'4 (Vptr cb pc1) le3).
                  apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m1).
                  { apply exec_Sset. eapply eval_Elvalue.
                    - eval_s_field_lvalue ltac:(subst le3 le2 le1;
                        rewrite PTree.gso by (compute; congruence);
                        rewrite PTree.gso by (compute; congruence);
                        rewrite PTree.gso by (compute; congruence); exact Hle_s)
                        co_is Hco Hpc_offset.
                    - apply deref_loc_value with (chunk := Mptr). reflexivity.
                      simpl. rewrite Mptr_Mint64. rewrite (ptrofs_add_zero so). exact Hpc_m1. }
                  { eapply exec_Sassign.
                    - eapply eval_Efield_struct.
                      + eapply eval_Elvalue.
                        * eapply eval_Ederef. eapply eval_Etempvar.
                          unfold le'.
                          repeat (rewrite PTree.gso by (compute; congruence)).
                          exact Hle_s.
                        * apply deref_loc_copy. reflexivity.
                      + reflexivity.
                      + exact Hco.
                      + exact Hpc_offset.
                    - eapply eval_Ebinop.
                      + eapply eval_Etempvar. unfold le'. rewrite PTree.gss. reflexivity.
                      + eapply eval_Econst_int.
                      + apply sem_add_pc_1.
                    - apply sem_cast_ptr_tint_to_ptr_tint.
                    - apply assign_loc_value with (chunk := Mptr). reflexivity.
                      simpl. rewrite Mptr_Mint64. rewrite (ptrofs_add_zero so).
                      fold pc2_v. exact Hs2. } } } } } }

        { apply exec_Sreturn_some. eapply eval_Econst_int. }
      }

      (* Part 2: abs_rel *)
      {
        set (new_co := Ptrofs.add co (Ptrofs.repr (2 * sizeof_code_t))).
        set (ard' := mk_abs_rel sb so hm cb new_co
                       (ar_global_block ard) (ar_global_ofs ard)
                       (ar_stack_block ard) (ar_stack_base_ofs ard)
                       (ar_code_ne_sptr ard) (ar_code_ne_global ard)
                       (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
        exists ard'. set (uso := Ptrofs.unsigned so) in *.

        assert (Hpc2 : Mem.load Mint64 m2 sb (uso + 0) = Some pc2_v).
        { pose proof (load_after_store_same m1 m2 sb (uso + 0) pc2_v Hstore2) as H.
          unfold pc2_v in H |- *. rewrite load_result_vptr in H. exact H. }
        assert (Ha2 : Mem.load Mint64 m2 sb (uso + 8) = Some (Vlong (Int64.repr (a * 2 + 1)))).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 8) = Some (Vlong (Int64.repr (a * 2 + 1)))) by (prove_field_survives Hs1 Haccu_load).
          prove_field_survives Hs2 Hx. }
        assert (Hsp2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b sp_ofs)) by (prove_field_survives Hs1 Hsp_load).
          prove_field_survives Hs2 Hx. }
        assert (He2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 24) = Some env_v) by (prove_field_survives Hs1 Henv_load).
          prove_field_survives Hs2 Hx. }
        assert (Hx2 : Mem.load Mint64 m2 sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))) by (prove_field_survives Hs1 Hextra_load).
          prove_field_survives Hs2 Hx. }
        assert (Hg2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr) by (prove_field_survives Hs1 Hgd_load).
          prove_field_survives Hs2 Hx. }
        assert (Ht2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
        { assert (Hx : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr) by (prove_field_survives Hs1 Hts_load).
          prove_field_survives Hs2 Hx. }

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
        - subst le'. repeat (rewrite PTree.gso by (compute; congruence)). exact Hle_s.
        - exists pc2_v. split. exact Hpc2. simpl. unfold pc_rel. f_equal.
          subst pc2_v pc2 pc1 pc_ofs new_co. unfold sizeof_code_t.
          rewrite !Ptrofs.add_assoc. f_equal.
          rewrite (Ptrofs.add_commut (Ptrofs.repr (2 * 4)) _). reflexivity.
        - exists (Vlong (Int64.repr (a * 2 + 1))). split. exact Ha2. simpl. rewrite Haccu_eq. apply vr_int.
        - exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
          + exact Hsp2. + reflexivity.
          + simpl. eapply stack_repr_co_shift. eapply (stack_repr_store_other_block hm cb co m1 m2 _ sp_b sp_ofs sb uso pc2_v).
            * eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b sp_ofs sb uso pc1_v).
              exact Hstack_repr. exact Hs1. intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
            * exact Hs2. * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          + exact Hsp_ne_sb. + exact Hsp_ne_gb. + exact Hcb_ne_sp. + exact Hsp_ge8. + exact Hsp_rep.
          + intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hs2. eapply Mem.perm_store_1. exact Hs1. apply Hsp_writable. exact Hofs'.
          + exact Hsp_align.
        - exists env_v. split. exact He2. simpl. eapply val_repr_co_shift. exact Henv_repr.
        - simpl. exact Hx2.
        - exists gd_ptr. split; [| split; [| split]].
          + exact Hg2. + simpl. exact Hgd_eq.
          + simpl. eapply global_repr_co_shift. eapply (global_repr_store_other_block hm cb co m1 m2 _ _ _ sb uso pc2_v).
            * eapply (global_repr_store_other_block hm cb co m m1 _ _ _ sb uso pc1_v).
              exact Hglobal_repr. exact Hs1. intro Heq; exact (Hgb_ne (eq_sym Heq)).
            * exact Hs2. * intro Heq; exact (Hgb_ne (eq_sym Heq)).
          + exact Hgb_ne.
        - exists ts_ptr. split. exact Ht2. simpl. exact Htrap_rel.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hs2. eapply Mem.perm_store_1. exact Hs1. apply Hsb_writable. exact Hofs'.
      }
    }
  }

  (* ================================================================ *)
  (* Cases 2-4: non-integer accu => Error, precise P_error            *)
  (* ================================================================ *)
  - exact (conj eq_refl I).
  - exact (conj eq_refl I).
  - exact (conj eq_refl I).
Qed.

(* Wrapper with building-block precondition for Module Type *)
Theorem verify_BUGEINT_handler_correct : forall n target,
    0 <= n -> Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BUGEINT n target) f_instr_BUGEINT
      (pre_and (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_unsigned_int) accu_is_long)
      (fun msg s => msg = "BUGEINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros n target Hn0 Hn.
  eapply handler_correct_weaken.
  - exact (verify_BUGEINT_correct n target).
  - intros e le m s ard _ [[[[Hne Hca] Hbo] Hai] Hal].
    exact (conj Hne (conj Hn0 (conj Hn (conj Hca (conj Hbo (conj Hai Hal)))))).
Qed.
