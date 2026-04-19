(* RAISE_NOTRACE_correct.v -- RAISE handler correctness proof.

   RAISE pops a trap frame from the stack, restoring pc, sp, trap_sp,
   env, and extra_args.  This is the exception-raising instruction.

   C code (f_instr_RAISE_NOTRACE):
     _t'11 = s->trap_sp;   s->sp = _t'11;
     _t'9 = s->sp;  _t'10 = *(cast _t'9 (tptr(tptr tint)) + 0);  s->pc = _t'10;
     _t'6 = s->sp;  _t'7 = s->sp;  _t'8 = *(_t'7 + 1);
     s->trap_sp = _t'6 + (_t'8 >> 1);
     _t'4 = s->sp;  _t'5 = *(_t'4 + 2);  s->env = _t'5;
     _t'2 = s->sp;  _t'3 = *(_t'2 + 3);  s->extra_args = _t'3 >> 1;
     _t'1 = s->sp;  s->sp = _t'1 + 4;
     return 0;

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
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int Ptrofs.of_int64
        field_offset
        PTree.get PTree.set].

(* raise_step_pre is imported from InstructSpec.v *)

(* ================================================================== *)
(* Struct layout                                                       *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full) /\
  field_offset ce _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset ce _trap_sp (co_members co) = Errors.OK (48, Full).
Proof.
  eexists. split; [| split; [| split; [| split; [| split]]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_raise_notrace : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full) /\
  field_offset (genv_cenv clight_ge) _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset (genv_cenv clight_ge) _trap_sp (co_members co) = Errors.OK (48, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Local Lemma sem_cast_ptlong_to_ptptint_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tlong) (tptr (tptr tint)) m = Some (Vptr b ofs).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma sem_add_ptptint_0 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr (tptr tint)) (Vint (Int.repr 0)) tint m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr (tptr tint)) tint) with (add_case_pi (tptr tint) Signed).
  unfold sem_add_ptr_int. change (sizeof (genv_cenv clight_ge) (tptr tint)) with 8%Z.
  f_equal. f_equal. unfold ptrofs_of_int.
  change (Ptrofs.of_ints (Int.repr 0)) with Ptrofs.zero.
  rewrite Ptrofs.mul_zero, Ptrofs.add_zero. reflexivity.
Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma sem_cast_long_to_long : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof. intros. unfold sem_cast. simpl classify_cast. rewrite ptr64_true. reflexivity. Qed.

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed). simpl. reflexivity.
Qed.

Local Lemma sem_add_ptr_tlong : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vlong n) tlong m
  = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tlong) with (add_case_pl tlong).
  unfold sem_add_ptr_long. reflexivity.
Qed.

Local Lemma sem_add_sp_2 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 2)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_sp_3 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 3)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 24))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_sp_4 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 4)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 32))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_RAISE_NOTRACE_correct :
    handler_correct (fun _pc s => do_raise s.(accu) s) f_instr_RAISE_NOTRACE
      raise_step_pre
      (fun msg _ => msg = "unhandled exception"%string \/
                    msg = "RAISE: malformed trap frame"%string)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handler_correct. simpl. unfold do_raise.
  destruct (Nat.eqb (trap_sp s) 0) eqn:Htsp_eq.
  - left. reflexivity.
  - set (k := Nat.sub (length (Machine.stack s)) (trap_sp s)).
    set (frame_top := skipn k (Machine.stack s)).
    destruct frame_top as [| v0 frame1] eqn:Hft.
    + right. reflexivity.
    + destruct v0 as [handler_pc | | |]; try (right; reflexivity).
      destruct frame1 as [| v1 frame2]; try (right; reflexivity).
      destruct v1 as [prev_tsp | | |]; try (right; reflexivity).
      destruct frame2 as [| saved_env frame3]; try (right; reflexivity).
      destruct frame3 as [| v3 rest]; try (right; reflexivity).
      destruct v3 as [saved_ea | | |]; try (right; reflexivity).

      (* ================================================================ *)
      (* Step case                                                         *)
      (* ================================================================ *)

      intros ard Hpre Hstep_pre.
      unfold abs_rel_with_ard in Hpre.
      set (sb := ar_sptr_block ard) in *.
      set (so := ar_sptr_ofs ard) in *.
      set (hm := ar_heap_map ard) in *.
      set (cb := ar_code_base_block ard) in *.
      set (co := ar_code_base_ofs ard) in *.
      set (gb := ar_global_block ard) in *.
      set (go_ := ar_global_ofs ard) in *.

      destruct Hpre as (Hle_s &
        [pc_ptr [Hpc_load Hpc_rel]] &
        [accu_v [Haccu_load Haccu_repr]] &
        [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr
          [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
        [env_v [Henv_load Henv_repr]] &
        Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
        [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
      subst sp_ptr.

      pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].

      destruct interp_state_co_raise_notrace as [co_is [Hco [Hpc_offset [Hsp_offset [Henv_offset [Hextra_offset Htrap_offset]]]]]].

      (* Derive trap_sp > 0 and decompose trap_sp_rel *)
      assert (Htsp_ne0 : trap_sp s <> 0%nat).
      { intro Heq. rewrite Heq in Htsp_eq. simpl in Htsp_eq. discriminate. }
      destruct (trap_sp s) as [| tsp'] eqn:Htsp_val.
      { exfalso. exact (Htsp_ne0 eq_refl). }
      simpl in Htrap_rel.
      (* Htrap_rel : ts_ptr = Vptr stk_b (Ptrofs.sub stk_base (Ptrofs.repr (Z.of_nat (S tsp') * 8))) *)

      set (stk_b := ar_stack_block ard) in *.
      set (stk_base := ar_stack_base_ofs ard) in *.
      set (trap_ofs := Ptrofs.sub stk_base (Ptrofs.repr (Z.of_nat (S tsp') * 8))) in *.
      (* ts_ptr = Vptr stk_b trap_ofs *)
      set (ts_b := stk_b).
      set (ts_ofs := trap_ofs).
      assert (Hts_eq : ts_ptr = Vptr ts_b ts_ofs) by exact Htrap_rel.

      (* Specialize step_pre *)
      unfold raise_step_pre in Hstep_pre.
      rewrite Htsp_val in Hstep_pre.
      specialize (Hstep_pre handler_pc prev_tsp saved_env saved_ea rest Hft).
      (* After unfolding, raw accessors appear. Fold them back before destructuring. *)
      fold stk_b stk_base in Hstep_pre.
      change (Ptrofs.sub stk_base (Ptrofs.repr (Z.of_nat (S tsp') * 8))) with trap_ofs in Hstep_pre.
      fold hm cb co in Hstep_pre.
      destruct Hstep_pre as (Hframe_pre & Hrest_stack_repr & Hts_ne_sb & Hts_ne_gb & Hcb_ne_ts &
        Hts_writable & Hts_align & Htrap_rel_new & Hts_ge8).
      unfold raise_frame_pre in Hframe_pre.
      fold hm cb co stk_b stk_base in Hframe_pre.
      change (Ptrofs.sub stk_base (Ptrofs.repr (Z.of_nat (S tsp') * 8))) with trap_ofs in Hframe_pre.
      destruct Hframe_pre as (
        (pc_b & pc_ofs & Hload_sp0 & Hpc_rel_new) &
        Hload_sp1 &
        (env_cv & Hload_sp2 & Henv_repr_new) &
        Hload_sp3 &
        _ & _ & Hshr_tsp &
        Hea_nonneg & _ &
        Hshr_ea &
        Hts_32_fits & Hrest_fits).
      (* Hts_32_fits contains raw terms after unfold; provide bound for ts_ofs *)
      assert (Hts_ofs_32 : Ptrofs.unsigned ts_ofs + 32 < Ptrofs.modulus) by exact Hts_32_fits.
      assert (Hts_ofs_rest : Ptrofs.unsigned ts_ofs + 32 + 8 * Z.of_nat (length rest) < Ptrofs.modulus) by exact Hrest_fits.
      pose proof (Ptrofs.unsigned_range ts_ofs) as [Hts_ofs_nonneg _].
      (* Provide a usable fact linking the raw and rewritten offset forms *)
      assert (Hnsp_eq : Ptrofs.unsigned (Ptrofs.add trap_ofs (Ptrofs.repr 32)) =
                         Ptrofs.unsigned ts_ofs + 32).
      { apply ptrofs_add_unsigned; lia. }

      set (new_sp_ofs := Ptrofs.add ts_ofs (Ptrofs.repr 32)).
      set (new_trap_ptr := Vptr ts_b (Ptrofs.add ts_ofs
             (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr prev_tsp))))).
      set (new_pc_v := Vptr pc_b pc_ofs).
      set (new_extra := Vlong (Int64.shr (Int64.repr (saved_ea * 2 + 1)) (Int64.repr 1))).
      (* use Ptrofs.unsigned so directly -- no uso abbreviation *)

      (* Store 1: sp <- trap_sp *)
      destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs)
                  Hsb_writable Hsp_load ltac:(lia) ltac:(lia) (Vptr ts_b ts_ofs))
        as [m1 Hstore1].
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hw1.

      (* Store 2: pc <- handler_pc *)
      assert (Hpc_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so +0) = Some pc_ptr).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so +16) (Ptrofs.unsigned so +0)
                 (Vptr ts_b ts_ofs) pc_ptr Hstore1 Hpc_load). left. lia. }
      destruct (store_succeeds_sb m1 sb so 0 pc_ptr Hw1 Hpc_m1 ltac:(lia) ltac:(lia) new_pc_v)
        as [m2 Hstore2].
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore2 Hw1) as Hw2.

      (* Store 3: trap_sp <- new_trap_ptr *)
      assert (Hts_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so +48) = Some (Vptr ts_b ts_ofs)).
      { assert (Hm1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so +48) = Some (Vptr ts_b ts_ofs)).
        { rewrite <- Hts_eq.
          apply (load_after_store_other m m1 sb (Ptrofs.unsigned so +16) (Ptrofs.unsigned so +48)
                   (Vptr ts_b ts_ofs) ts_ptr Hstore1 Hts_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so +0) (Ptrofs.unsigned so +48)
                 new_pc_v (Vptr ts_b ts_ofs) Hstore2 Hm1). right. lia. }
      destruct (store_succeeds_sb m2 sb so 48 (Vptr ts_b ts_ofs) Hw2 Hts_m2 ltac:(lia) ltac:(lia) new_trap_ptr)
        as [m3 Hstore3].
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore3 Hw2) as Hw3.

      (* Store 4: env <- env_cv *)
      assert (Henv_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so +24) = Some env_v).
      { assert (Hm1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so +24) = Some env_v).
        { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so +16) (Ptrofs.unsigned so +24)
                   (Vptr ts_b ts_ofs) env_v Hstore1 Henv_load). right. lia. }
        assert (Hm2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so +24) = Some env_v).
        { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so +0) (Ptrofs.unsigned so +24)
                   new_pc_v env_v Hstore2 Hm1). right. lia. }
        apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so +48) (Ptrofs.unsigned so +24)
                 new_trap_ptr env_v Hstore3 Hm2). left. lia. }
      destruct (store_succeeds_sb m3 sb so 24 env_v Hw3 Henv_m3 ltac:(lia) ltac:(lia) env_cv)
        as [m4 Hstore4].
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore4 Hw3) as Hw4.

      (* Store 5: extra_args <- shr(ea,1) *)
      assert (Hex_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so +32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { assert (Hm1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so +32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so +16) (Ptrofs.unsigned so +32)
                   (Vptr ts_b ts_ofs) _ Hstore1 Hextra_load). right. lia. }
        assert (Hm2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so +32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so +0) (Ptrofs.unsigned so +32)
                   new_pc_v _ Hstore2 Hm1). right. lia. }
        assert (Hm3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so +32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so +48) (Ptrofs.unsigned so +32)
                   new_trap_ptr _ Hstore3 Hm2). left. lia. }
        apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so +24) (Ptrofs.unsigned so +32)
                 env_cv _ Hstore4 Hm3). right. lia. }
      destruct (store_succeeds_sb m4 sb so 32 _ Hw4 Hex_m4 ltac:(lia) ltac:(lia) new_extra)
        as [m5 Hstore5].
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore5 Hw4) as Hw5.

      (* Store 6: sp <- sp + 4 *)
      assert (Hsp_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so +16) = Some (Vptr ts_b ts_ofs)).
      { assert (Hm1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so +16) = Some (Vptr ts_b ts_ofs)).
        { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so +16) (Vptr ts_b ts_ofs) Hstore1) as H.
          simpl Val.load_result in H. rewrite ptr64_true in H. exact H. }
        assert (Hm2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so +16) = Some (Vptr ts_b ts_ofs)).
        { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so +0) (Ptrofs.unsigned so +16)
                   new_pc_v _ Hstore2 Hm1). right. lia. }
        assert (Hm3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so +16) = Some (Vptr ts_b ts_ofs)).
        { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so +48) (Ptrofs.unsigned so +16)
                   new_trap_ptr _ Hstore3 Hm2). left. lia. }
        assert (Hm4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so +16) = Some (Vptr ts_b ts_ofs)).
        { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so +24) (Ptrofs.unsigned so +16)
                   env_cv _ Hstore4 Hm3). left. lia. }
        apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so +32) (Ptrofs.unsigned so +16)
                 new_extra _ Hstore5 Hm4). left. lia. }
      destruct (store_succeeds_sb m5 sb so 16 (Vptr ts_b ts_ofs) Hw5 Hsp_m5 ltac:(lia) ltac:(lia)
                  (Vptr ts_b new_sp_ofs))
        as [m6 Hstore6].

      (* Trap frame loads survive all stores (ts_b <> sb) *)
      assert (Hsp0_m1 : Mem.load Mint64 m1 ts_b (Ptrofs.unsigned ts_ofs) = Some (Vptr pc_b pc_ofs)).
      { erewrite Mem.load_store_other. exact Hload_sp0. exact Hstore1.
        left. intro H; apply Hts_ne_sb; auto. }
      assert (Hsp0_m2 : Mem.load Mint64 m2 ts_b (Ptrofs.unsigned ts_ofs) = Some (Vptr pc_b pc_ofs)).
      { erewrite Mem.load_store_other. exact Hsp0_m1. exact Hstore2.
        left. intro H; apply Hts_ne_sb; auto. }
      assert (Hsp1_m1 : Mem.load Mint64 m1 ts_b (Ptrofs.unsigned ts_ofs + 8) = Some (Vlong (Int64.repr (prev_tsp * 2 + 1)))).
      { erewrite Mem.load_store_other. exact Hload_sp1. exact Hstore1.
        left. intro H; apply Hts_ne_sb; auto. }
      assert (Hsp1_m2 : Mem.load Mint64 m2 ts_b (Ptrofs.unsigned ts_ofs + 8) = Some (Vlong (Int64.repr (prev_tsp * 2 + 1)))).
      { erewrite Mem.load_store_other. exact Hsp1_m1. exact Hstore2.
        left. intro H; apply Hts_ne_sb; auto. }
      assert (Hsp2_m3 : Mem.load Mint64 m3 ts_b (Ptrofs.unsigned ts_ofs + 16) = Some env_cv).
      { assert (H1 : Mem.load Mint64 m1 ts_b (Ptrofs.unsigned ts_ofs + 16) = Some env_cv).
        { erewrite Mem.load_store_other. exact Hload_sp2. exact Hstore1. left. intro H; apply Hts_ne_sb; auto. }
        assert (H2 : Mem.load Mint64 m2 ts_b (Ptrofs.unsigned ts_ofs + 16) = Some env_cv).
        { erewrite Mem.load_store_other. exact H1. exact Hstore2. left. intro H; apply Hts_ne_sb; auto. }
        erewrite Mem.load_store_other. exact H2. exact Hstore3. left. intro H; apply Hts_ne_sb; auto. }
      assert (Hsp3_m4 : Mem.load Mint64 m4 ts_b (Ptrofs.unsigned ts_ofs + 24) = Some (Vlong (Int64.repr (saved_ea * 2 + 1)))).
      { assert (H1 : Mem.load Mint64 m1 ts_b (Ptrofs.unsigned ts_ofs + 24) = Some (Vlong (Int64.repr (saved_ea * 2 + 1)))).
        { erewrite Mem.load_store_other. exact Hload_sp3. exact Hstore1. left. intro H; apply Hts_ne_sb; auto. }
        assert (H2 : Mem.load Mint64 m2 ts_b (Ptrofs.unsigned ts_ofs + 24) = Some (Vlong (Int64.repr (saved_ea * 2 + 1)))).
        { erewrite Mem.load_store_other. exact H1. exact Hstore2. left. intro H; apply Hts_ne_sb; auto. }
        assert (H3 : Mem.load Mint64 m3 ts_b (Ptrofs.unsigned ts_ofs + 24) = Some (Vlong (Int64.repr (saved_ea * 2 + 1)))).
        { erewrite Mem.load_store_other. exact H2. exact Hstore3. left. intro H; apply Hts_ne_sb; auto. }
        erewrite Mem.load_store_other. exact H3. exact Hstore4. left. intro H; apply Hts_ne_sb; auto. }

      (* sp field through stores *)
      assert (Hsp_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so +16) = Some (Vptr ts_b ts_ofs)).
      { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so +16) (Vptr ts_b ts_ofs) Hstore1) as H.
        simpl Val.load_result in H. rewrite ptr64_true in H. exact H. }
      assert (Hsp_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so +16) = Some (Vptr ts_b ts_ofs)).
      { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so +0) (Ptrofs.unsigned so +16) new_pc_v _ Hstore2 Hsp_m1). right. lia. }
      assert (Hsp_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so +16) = Some (Vptr ts_b ts_ofs)).
      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so +48) (Ptrofs.unsigned so +16) new_trap_ptr _ Hstore3 Hsp_m2). left. lia. }
      assert (Hsp_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so +16) = Some (Vptr ts_b ts_ofs)).
      { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so +24) (Ptrofs.unsigned so +16) env_cv _ Hstore4 Hsp_m3). left. lia. }

      (* Witnesses *)
      set (le1 := PTree.set _t'11 (Vptr ts_b ts_ofs) le).
      set (le2 := PTree.set _t'9 (Vptr ts_b ts_ofs) le1).
      set (le3 := PTree.set _t'10 (Vptr pc_b pc_ofs) le2).
      set (le4 := PTree.set _t'6 (Vptr ts_b ts_ofs) le3).
      set (le5 := PTree.set _t'7 (Vptr ts_b ts_ofs) le4).
      set (le6 := PTree.set _t'8 (Vlong (Int64.repr (prev_tsp * 2 + 1))) le5).
      set (le7 := PTree.set _t'4 (Vptr ts_b ts_ofs) le6).
      set (le8 := PTree.set _t'5 env_cv le7).
      set (le9 := PTree.set _t'2 (Vptr ts_b ts_ofs) le8).
      set (le10 := PTree.set _t'3 (Vlong (Int64.repr (saved_ea * 2 + 1))) le9).
      set (le11 := PTree.set _t'1 (Vptr ts_b ts_ofs) le10).

      exists le11, m6, (Out_return (Some (Vint (Int.repr 0), tint))).
      split.

      (* Part 1: exec *)
      {
        apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m1).
        { apply (eval_stmt_to_exec clight_ge 15). eval_cbn.
          rewrite Hle_s; eval_cbn. try rewrite Hco; eval_cbn. try rewrite Htrap_offset; eval_cbn.
          rewrite Mptr_Mint64; eval_cbn.
          rewrite (ptrofs_add_unsigned so 48 ltac:(lia) ltac:(lia)). rewrite Hts_load; eval_cbn. rewrite Hts_eq; eval_cbn.
          rewrite PTree.gss; eval_cbn.
          rewrite PTree.gso by (compute; congruence). rewrite Hle_s; eval_cbn. try rewrite Hco; eval_cbn. try rewrite Hsp_offset; eval_cbn.
          rewrite sem_cast_ptr_to_ptr; eval_cbn. rewrite Mptr_Mint64; eval_cbn.
          rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)). rewrite Hstore1; eval_cbn.
          reflexivity. }
        apply exec_Sseq_1 with (t1 := E0) (le1 := le3) (m1 := m2).
        { apply (eval_stmt_to_exec clight_ge 20). eval_cbn.
          unfold le1.
          rewrite PTree.gso by (compute; congruence). rewrite Hle_s; eval_cbn. try rewrite Hco; eval_cbn. try rewrite Hsp_offset; eval_cbn.
          rewrite Mptr_Mint64; eval_cbn. rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)). rewrite Hsp_m1; eval_cbn.
          rewrite PTree.gss; eval_cbn.
          rewrite sem_cast_ptlong_to_ptptint_vptr; eval_cbn.
          rewrite (sem_add_ptptint_0 ts_b ts_ofs m1); eval_cbn.
          rewrite Mptr_Mint64; eval_cbn. rewrite Hsp0_m1; eval_cbn.
          repeat (rewrite PTree.gso by (compute; congruence)). rewrite Hle_s; eval_cbn. try rewrite Hco; eval_cbn. try rewrite Hpc_offset; eval_cbn.
          rewrite PTree.gss; eval_cbn. rewrite sem_cast_ptr_tint_to_ptr_tint; eval_cbn.
          rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)). rewrite Mptr_Mint64; eval_cbn.
          fold new_pc_v. rewrite Hstore2; eval_cbn. reflexivity. }
        apply exec_Sseq_1 with (t1 := E0) (le1 := le6) (m1 := m3).
        { apply (eval_stmt_to_exec clight_ge 25). eval_cbn.
          unfold le3, le2, le1. repeat (rewrite PTree.gso by (compute; congruence)).
          rewrite Hle_s; eval_cbn. try rewrite Hco; eval_cbn. try rewrite Hsp_offset; eval_cbn.
          rewrite Mptr_Mint64; eval_cbn. rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)). rewrite Hsp_m2; eval_cbn.
          rewrite PTree.gso by (compute; congruence). repeat (rewrite PTree.gso by (compute; congruence)).
          rewrite Hle_s; eval_cbn. try rewrite Hco; eval_cbn. try rewrite Hsp_offset; eval_cbn.
          rewrite Mptr_Mint64; eval_cbn. rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)). rewrite Hsp_m2; eval_cbn.
          rewrite PTree.gss; eval_cbn. rewrite sem_cast_ptr_to_ptr; eval_cbn. rewrite sem_add_sp_1; eval_cbn.
          rewrite (ptrofs_add_unsigned ts_ofs 8 ltac:(lia) ltac:(lia)). rewrite Hsp1_m2; eval_cbn.
          repeat (rewrite PTree.gso by (compute; congruence)). rewrite Hle_s; eval_cbn. try rewrite Hco; eval_cbn. try rewrite Htrap_offset; eval_cbn.
          rewrite Mptr_Mint64; eval_cbn.
          repeat (try rewrite PTree.gss; try (rewrite PTree.gso by (compute; congruence))); eval_cbn.
          repeat (try rewrite PTree.gss; try (rewrite PTree.gso by (compute; congruence))); eval_cbn.
          rewrite sem_cast_long_to_long; eval_cbn.
          rewrite (sem_shr_long_int_1 (Int64.repr (prev_tsp * 2 + 1)) m2); eval_cbn.
          rewrite Hshr_tsp; eval_cbn.
          rewrite (sem_add_ptr_tlong ts_b ts_ofs (Int64.repr prev_tsp) m2); eval_cbn.
          rewrite sem_cast_ptr_to_ptr; eval_cbn.
          rewrite (ptrofs_add_unsigned so 48 ltac:(lia) ltac:(lia)).
          fold new_trap_ptr. rewrite Hstore3; eval_cbn. reflexivity. }
        apply exec_Sseq_1 with (t1 := E0) (le1 := le8) (m1 := m4).
        { apply (eval_stmt_to_exec clight_ge 20). eval_cbn.
          unfold le6, le5, le4, le3, le2, le1.
          repeat (rewrite PTree.gso by (compute; congruence)). rewrite Hle_s; eval_cbn. try rewrite Hco; eval_cbn. try rewrite Hsp_offset; eval_cbn.
          rewrite Mptr_Mint64; eval_cbn. rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)). rewrite Hsp_m3; eval_cbn.
          rewrite PTree.gss; eval_cbn. rewrite sem_add_sp_2; eval_cbn.
          rewrite (ptrofs_add_unsigned ts_ofs 16 ltac:(lia) ltac:(lia)). rewrite Hsp2_m3; eval_cbn.
          repeat (rewrite PTree.gso by (compute; congruence)). rewrite Hle_s; eval_cbn. try rewrite Hco; eval_cbn. try rewrite Henv_offset; eval_cbn.
          rewrite PTree.gss; eval_cbn.
          rewrite (sem_cast_long_val_repr hm cb co saved_env env_cv m3 Henv_repr_new); eval_cbn.
          rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)). rewrite Hstore4; eval_cbn. reflexivity. }
        apply exec_Sseq_1 with (t1 := E0) (le1 := le10) (m1 := m5).
        { apply (eval_stmt_to_exec clight_ge 20). eval_cbn.
          unfold le8, le7, le6, le5, le4, le3, le2, le1.
          repeat (rewrite PTree.gso by (compute; congruence)). rewrite Hle_s; eval_cbn. try rewrite Hco; eval_cbn. try rewrite Hsp_offset; eval_cbn.
          rewrite Mptr_Mint64; eval_cbn. rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)). rewrite Hsp_m4; eval_cbn.
          rewrite PTree.gss; eval_cbn. rewrite sem_add_sp_3; eval_cbn.
          rewrite (ptrofs_add_unsigned ts_ofs 24 ltac:(lia) ltac:(lia)). rewrite Hsp3_m4; eval_cbn.
          repeat (rewrite PTree.gso by (compute; congruence)). rewrite Hle_s; eval_cbn. try rewrite Hco; eval_cbn. try rewrite Hextra_offset; eval_cbn.
          rewrite PTree.gss; eval_cbn.
          rewrite sem_cast_long_to_long; eval_cbn.
          rewrite (sem_shr_long_int_1 (Int64.repr (saved_ea * 2 + 1)) m4); eval_cbn.
          rewrite sem_cast_long_vlong; eval_cbn. fold new_extra.
          rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)). rewrite Hstore5; eval_cbn. reflexivity. }
        apply exec_Sseq_1 with (t1 := E0) (le1 := le11) (m1 := m6).
        { apply (eval_stmt_to_exec clight_ge 15). eval_cbn.
          unfold le10, le9, le8, le7, le6, le5, le4, le3, le2, le1.
          repeat (rewrite PTree.gso by (compute; congruence)). rewrite Hle_s; eval_cbn. try rewrite Hco; eval_cbn. try rewrite Hsp_offset; eval_cbn.
          rewrite Mptr_Mint64; eval_cbn. rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)). rewrite Hsp_m5; eval_cbn.
          repeat (rewrite PTree.gso by (compute; congruence)). rewrite Hle_s; eval_cbn. try rewrite Hco; eval_cbn. try rewrite Hsp_offset; eval_cbn.
          rewrite Mptr_Mint64; eval_cbn. rewrite PTree.gss; eval_cbn.
          rewrite (sem_add_sp_4 ts_b ts_ofs m5); eval_cbn. fold new_sp_ofs.
          rewrite sem_cast_ptr_to_ptr; eval_cbn.
          rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)). rewrite Hstore6; eval_cbn. reflexivity. }
        apply exec_Sreturn_some. eapply eval_Econst_int.
      }

      (* Part 2: abs_rel *)
      {
        set (ard' := mk_abs_rel sb so hm cb co gb go_
                       (ar_stack_block ard) (ar_stack_base_ofs ard)
                       (ar_code_ne_sptr ard) (ar_code_ne_global ard)
                       (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
        exists ard'.

        (* Final loads *)
        assert (Hpc6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so +0) = Some new_pc_v).
        { assert (H2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so +0) = Some new_pc_v).
          { pose proof (load_after_store_same m1 m2 sb (Ptrofs.unsigned so +0) new_pc_v Hstore2) as H.
            unfold new_pc_v in H. simpl Val.load_result in H. rewrite ptr64_true in H. exact H. }
          assert (H3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so +0) = Some new_pc_v).
          { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so +48) (Ptrofs.unsigned so +0) new_trap_ptr _ Hstore3 H2). left. lia. }
          assert (H4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so +0) = Some new_pc_v).
          { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so +24) (Ptrofs.unsigned so +0) env_cv _ Hstore4 H3). left. lia. }
          assert (H5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so +0) = Some new_pc_v).
          { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so +32) (Ptrofs.unsigned so +0) new_extra _ Hstore5 H4). left. lia. }
          apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so +16) (Ptrofs.unsigned so +0) (Vptr ts_b new_sp_ofs) _ Hstore6 H5). left. lia. }

        assert (Hacc6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so +8) = Some accu_v).
        { assert (H1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so +8) = Some accu_v).
          { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so +16) (Ptrofs.unsigned so +8) (Vptr ts_b ts_ofs) _ Hstore1 Haccu_load). left. lia. }
          assert (H2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so +8) = Some accu_v).
          { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so +0) (Ptrofs.unsigned so +8) new_pc_v _ Hstore2 H1). right. lia. }
          assert (H3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so +8) = Some accu_v).
          { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so +48) (Ptrofs.unsigned so +8) new_trap_ptr _ Hstore3 H2). left. lia. }
          assert (H4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so +8) = Some accu_v).
          { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so +24) (Ptrofs.unsigned so +8) env_cv _ Hstore4 H3). left. lia. }
          assert (H5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so +8) = Some accu_v).
          { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so +32) (Ptrofs.unsigned so +8) new_extra _ Hstore5 H4). left. lia. }
          apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so +16) (Ptrofs.unsigned so +8) (Vptr ts_b new_sp_ofs) _ Hstore6 H5). left. lia. }

        assert (Hsp6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so +16) = Some (Vptr ts_b new_sp_ofs)).
        { pose proof (load_after_store_same m5 m6 sb (Ptrofs.unsigned so +16) (Vptr ts_b new_sp_ofs) Hstore6) as H.
          simpl Val.load_result in H. rewrite ptr64_true in H. exact H. }

        assert (Henv6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so +24) = Some env_cv).
        { assert (H4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so +24) = Some env_cv).
          { pose proof (load_after_store_same m3 m4 sb (Ptrofs.unsigned so +24) env_cv Hstore4) as H.
            rewrite (val_repr_load_result hm cb co saved_env env_cv Henv_repr_new) in H. exact H. }
          assert (H5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so +24) = Some env_cv).
          { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so +32) (Ptrofs.unsigned so +24) new_extra _ Hstore5 H4). left. lia. }
          apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so +16) (Ptrofs.unsigned so +24) (Vptr ts_b new_sp_ofs) _ Hstore6 H5). right. lia. }

        assert (Hex6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so +32) = Some new_extra).
        { assert (H5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so +32) = Some new_extra).
          { pose proof (load_after_store_same m4 m5 sb (Ptrofs.unsigned so +32) new_extra Hstore5) as H.
            unfold new_extra in H. simpl Val.load_result in H. exact H. }
          apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so +16) (Ptrofs.unsigned so +32) (Vptr ts_b new_sp_ofs) _ Hstore6 H5). right. lia. }

        assert (Hgd6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so +40) = Some gd_ptr).
        { assert (H1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so +40) = Some gd_ptr).
          { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so +16) (Ptrofs.unsigned so +40) (Vptr ts_b ts_ofs) _ Hstore1 Hgd_load). right. lia. }
          assert (H2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so +40) = Some gd_ptr).
          { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so +0) (Ptrofs.unsigned so +40) new_pc_v _ Hstore2 H1). right. lia. }
          assert (H3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so +40) = Some gd_ptr).
          { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so +48) (Ptrofs.unsigned so +40) new_trap_ptr _ Hstore3 H2). left. lia. }
          assert (H4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so +40) = Some gd_ptr).
          { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so +24) (Ptrofs.unsigned so +40) env_cv _ Hstore4 H3). right. lia. }
          assert (H5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so +40) = Some gd_ptr).
          { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so +32) (Ptrofs.unsigned so +40) new_extra _ Hstore5 H4). right. lia. }
          apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so +16) (Ptrofs.unsigned so +40) (Vptr ts_b new_sp_ofs) _ Hstore6 H5). right. lia. }

        assert (Hts6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so +48) = Some new_trap_ptr).
        { assert (H3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so +48) = Some new_trap_ptr).
          { pose proof (load_after_store_same m2 m3 sb (Ptrofs.unsigned so +48) new_trap_ptr Hstore3) as H.
            unfold new_trap_ptr in H. simpl Val.load_result in H. rewrite ptr64_true in H. exact H. }
          assert (H4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so +48) = Some new_trap_ptr).
          { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so +24) (Ptrofs.unsigned so +48) env_cv _ Hstore4 H3). right. lia. }
          assert (H5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so +48) = Some new_trap_ptr).
          { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so +32) (Ptrofs.unsigned so +48) new_extra _ Hstore5 H4). right. lia. }
          apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so +16) (Ptrofs.unsigned so +48) (Vptr ts_b new_sp_ofs) _ Hstore6 H5). right. lia. }

        assert (Hw6 : Mem.range_perm m6 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
        { intros o Ho. eapply Mem.perm_store_1; [exact Hstore6|].
          eapply Mem.perm_store_1; [exact Hstore5|]. eapply Mem.perm_store_1; [exact Hstore4|].
          eapply Mem.perm_store_1; [exact Hstore3|]. eapply Mem.perm_store_1; [exact Hstore2|].
          eapply Mem.perm_store_1; [exact Hstore1|]. apply Hsb_writable. exact Ho. }

        assert (Hstk6 : stack_repr hm cb co m6 rest ts_b new_sp_ofs).
        { apply (stack_repr_store_other_block hm cb co m5 m6 _ ts_b _ sb (Ptrofs.unsigned so +16) (Vptr ts_b new_sp_ofs)).
          - apply (stack_repr_store_other_block hm cb co m4 m5 _ ts_b _ sb (Ptrofs.unsigned so +32) new_extra).
            + apply (stack_repr_store_other_block hm cb co m3 m4 _ ts_b _ sb (Ptrofs.unsigned so +24) env_cv).
              * apply (stack_repr_store_other_block hm cb co m2 m3 _ ts_b _ sb (Ptrofs.unsigned so +48) new_trap_ptr).
                { apply (stack_repr_store_other_block hm cb co m1 m2 _ ts_b _ sb (Ptrofs.unsigned so +0) new_pc_v).
                  { apply (stack_repr_store_other_block hm cb co m m1 _ ts_b _ sb (Ptrofs.unsigned so +16) (Vptr ts_b ts_ofs)).
                    exact Hrest_stack_repr. exact Hstore1. exact (not_eq_sym Hts_ne_sb). }
                  exact Hstore2. exact (not_eq_sym Hts_ne_sb). }
                exact Hstore3. exact (not_eq_sym Hts_ne_sb).
              * exact Hstore4. * exact (not_eq_sym Hts_ne_sb).
            + exact Hstore5. + exact (not_eq_sym Hts_ne_sb).
          - exact Hstore6. - exact (not_eq_sym Hts_ne_sb). }

        assert (Hle_s6 : le11 ! _s = Some (Vptr sb so)).
        { subst le11 le10 le9 le8 le7 le6 le5 le4 le3 le2 le1.
          repeat (rewrite PTree.gso by (compute; congruence)). exact Hle_s. }

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

        (* 1. _s *) { exact Hle_s6. }

        (* 2. pc *) { exists new_pc_v. split. exact Hpc6. simpl. exact Hpc_rel_new. }

        (* 3. accu *) { exists accu_v. split. exact Hacc6. simpl. eapply val_repr_co_shift. exact Haccu_repr. }

        (* 4. sp *)
        { exists (Vptr ts_b new_sp_ofs), ts_b, new_sp_ofs.
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
          - exact Hsp6.
          - reflexivity.
          - simpl stack. eapply stack_repr_co_shift. exact Hstk6.
          - exact Hts_ne_sb.
          - exact Hts_ne_gb.
          - exact Hcb_ne_ts.
          - unfold new_sp_ofs. rewrite (ptrofs_add_unsigned ts_ofs 32 ltac:(lia) ltac:(lia)). lia.
          - simpl stack. unfold new_sp_ofs. rewrite (ptrofs_add_unsigned ts_ofs 32 ltac:(lia) ltac:(lia)). lia.
          - simpl stack. unfold new_sp_ofs. rewrite (ptrofs_add_unsigned ts_ofs 32 ltac:(lia) ltac:(lia)).
            intros o Ho. eapply Mem.perm_store_1; [exact Hstore6|].
            eapply Mem.perm_store_1; [exact Hstore5|]. eapply Mem.perm_store_1; [exact Hstore4|].
            eapply Mem.perm_store_1; [exact Hstore3|]. eapply Mem.perm_store_1; [exact Hstore2|].
            eapply Mem.perm_store_1; [exact Hstore1|].
            assert (Ho' : 0 <= o < Ptrofs.unsigned (Ptrofs.add trap_ofs (Ptrofs.repr 32)) + 8 * Z.of_nat (length rest)) by (rewrite Hnsp_eq; lia).
            apply Hts_writable. exact Ho'.
          - unfold new_sp_ofs. rewrite (ptrofs_add_unsigned ts_ofs 32 ltac:(lia) ltac:(lia)).
            rewrite Hnsp_eq in Hts_align. exact Hts_align. }

        (* 5. env *) { exists env_cv. split. exact Henv6. simpl. eapply val_repr_co_shift. exact Henv_repr_new. }

        (* 6. extra_args *)
        { simpl. unfold new_extra in Hex6. rewrite Hshr_ea in Hex6.
          rewrite Z2Nat.id by lia. exact Hex6. }

        (* 7. global_data *)
        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd6.
          - simpl. exact Hgd_eq.
          - simpl. eapply global_repr_co_shift.
            apply (global_repr_store_other_block hm cb co m5 m6 _ gb go_ sb (Ptrofs.unsigned so +16) (Vptr ts_b new_sp_ofs)).
            + apply (global_repr_store_other_block hm cb co m4 m5 _ gb go_ sb (Ptrofs.unsigned so +32) new_extra).
              * apply (global_repr_store_other_block hm cb co m3 m4 _ gb go_ sb (Ptrofs.unsigned so +24) env_cv).
                { apply (global_repr_store_other_block hm cb co m2 m3 _ gb go_ sb (Ptrofs.unsigned so +48) new_trap_ptr).
                  { apply (global_repr_store_other_block hm cb co m1 m2 _ gb go_ sb (Ptrofs.unsigned so +0) new_pc_v).
                    { apply (global_repr_store_other_block hm cb co m m1 _ gb go_ sb (Ptrofs.unsigned so +16) (Vptr ts_b ts_ofs)).
                      exact Hglobal_repr. exact Hstore1. intro H; exact (global_block_ne_sptr ard (eq_sym H)). }
                    exact Hstore2. intro H; exact (global_block_ne_sptr ard (eq_sym H)). }
                  exact Hstore3. intro H; exact (global_block_ne_sptr ard (eq_sym H)). }
                exact Hstore4. intro H; exact (global_block_ne_sptr ard (eq_sym H)).
              * exact Hstore5. * intro H; exact (global_block_ne_sptr ard (eq_sym H)).
            + exact Hstore6. + intro H; exact (global_block_ne_sptr ard (eq_sym H)).
          - exact Hgb_ne_sb. }

        (* 8. trap_sp *) { exists new_trap_ptr. split. exact Hts6. simpl.
          rewrite Hshr_tsp in Htrap_rel_new. exact Htrap_rel_new. }

        (* 9. sb_writable *) { exact Hw6. }
      }
Qed.
