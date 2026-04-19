(* GETGLOBALFIELD_correct.v -- GETGLOBALFIELD completeness proof.

   GETGLOBALFIELD reads two operands from the code buffer:
     N = global index, P = field index.
   It loads global_data[N], then dereferences field P of that value,
   stores the result in accu, and advances pc by 2 (past both operands).

   C code (f_instr_GETGLOBALFIELD):
     Phase 1 (GETGLOBAL part):
       _t'7 = s->global_data;
       _t'8 = s->pc;
       _t'9 = *_t'8;                     read N from code buffer
       _t'10 = *(global_data + _t'9);    load global_data[N]
       s->accu = _t'10;
     Phase 2 (advance pc):
       _t'6 = s->pc;
       s->pc = _t'6 + 1;                 advance pc past N
     Phase 3 (GETFIELD part):
       _t'2 = s->accu;                   read accu = global_data[N]
       _t'3 = s->pc;
       _t'4 = *_t'3;                     read P from code buffer
       _t'5 = *((long ptr)_t'2 + _t'4);  load field P of global[N]
       s->accu = _t'5;
     Phase 4 (advance pc):
       _t'1 = s->pc;
       s->pc = _t'1 + 1;                 advance pc past P
       return 0;

   Rocq handler:
     handle_GETGLOBALFIELD n p pc' s =
       match nth_error s.(global) n with
       | Some glob =>
         match field_or_heap s glob p with
         | Some v => Step (s <|pc := pc'|> <|accu := v|>)
         | None => Error "GETGLOBALFIELD: field access failed"
         end
       | None => Error "GETGLOBALFIELD: index out of bounds"
       end

   Four stores: accu (global[N]), pc (advance 1),
                accu (field[P]), pc (advance 1).

   NO AXIOMS.  NO ADMITTED. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
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
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout: _pc at 0, _accu at 8, _global_data at 40            *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _global_data (co_members co) = Errors.OK (40, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_ggf : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _global_data (co_members co) = Errors.OK (40, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Lemma sem_add_pc_1_ggf : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint_ggf : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_cast_long_to_ptr_vptr_ggf : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma load_result_vlong_ggf : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr_ggf : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* pc_rel shift by 2 code positions (two operands consumed).
   Goal: ((co + rocq_pc*4) + 4) + 4 = (co + 8) + rocq_pc*4
   Strategy: reassociate to co + (rocq_pc*4 + 4 + 4)
             and co + (8 + rocq_pc*4), then commute inner terms. *)
Lemma pc_rel_shift_2 : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add (Ptrofs.add co
                     (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                     (Ptrofs.repr 4))
                     (Ptrofs.repr 4)))
         cb (Ptrofs.add co (Ptrofs.repr (2 * sizeof_code_t))) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal.
  (* LHS is: Ptrofs.add (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * 4)))
                                      (Ptrofs.repr 4))
                          (Ptrofs.repr 4)
     RHS is: Ptrofs.add (Ptrofs.add co (Ptrofs.repr (2 * 4)))
                          (Ptrofs.repr (rocq_pc * 4))
     Reassociate both sides fully right. *)
  rewrite (Ptrofs.add_assoc (Ptrofs.add co (Ptrofs.repr (rocq_pc * 4)))
             (Ptrofs.repr 4) (Ptrofs.repr 4)).
  rewrite (Ptrofs.add_assoc co (Ptrofs.repr (rocq_pc * 4))
             (Ptrofs.add (Ptrofs.repr 4) (Ptrofs.repr 4))).
  rewrite (Ptrofs.add_assoc co (Ptrofs.repr (2 * 4))
             (Ptrofs.repr (rocq_pc * 4))).
  f_equal.
  rewrite Ptrofs.add_commut.
  reflexivity.
Qed.

(* ================================================================== *)
(* Architectural constant                                              *)
(* ================================================================== *)

Lemma ptrofs_modulus_large_ggf : (Ptrofs.modulus > 8)%Z.
Proof.
  unfold Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  simpl. reflexivity.
Qed.

(* ================================================================== *)
(* Key lemma: global_repr + nth_error => Mem.load                     *)
(* ================================================================== *)

Lemma nat_iter_succ_r_ggf : forall {A} (f : A -> A) n x,
  Nat.iter (S n) f x = Nat.iter n f (f x).
Proof.
  intros A f n. revert f. induction n as [| n' IH]; intros f x.
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma global_repr_nth_error_ptrofs_ggf : forall hm cb0 co0 m gs gb go n v,
  global_repr hm cb0 co0 m gs gb go ->
  nth_error gs n = Some v ->
  exists cv,
    Mem.load Mint64 m gb
      (Ptrofs.unsigned (Nat.iter n (fun p => Ptrofs.add p (Ptrofs.repr 8)) go))
    = Some cv /\
    val_repr hm cb0 co0 v cv.
Proof.
  intros hm cb0 co0 m gs gb go n v Hgr.
  revert n.
  induction Hgr as [| v0 vs b ofs cv0 Hload Hval_repr Hgr' IH];
    intros n Hnth.
  - destruct n; discriminate Hnth.
  - destruct n as [| n'].
    + simpl in Hnth. injection Hnth as Heq. subst v.
      exists cv0. simpl. split; [exact Hload | exact Hval_repr].
    + simpl in Hnth.
      specialize (IH n' Hnth).
      destruct IH as [cv' [Hload' Hval_repr']].
      exists cv'. split; [| exact Hval_repr'].
      rewrite nat_iter_succ_r_ggf. exact Hload'.
Qed.

Lemma iter_add_8_unsigned_ggf : forall go n,
  Ptrofs.unsigned go + Z.of_nat n * 8 < Ptrofs.modulus ->
  Ptrofs.unsigned (Nat.iter n (fun p => Ptrofs.add p (Ptrofs.repr 8)) go)
  = Ptrofs.unsigned go + Z.of_nat n * 8.
Proof.
  intros go n.
  revert go.
  induction n as [| n' IH]; intros go Hbound.
  - simpl. lia.
  - rewrite nat_iter_succ_r_ggf.
    pose proof (Ptrofs.unsigned_range go) as [Hgo_pos Hgo_lt].
    pose proof ptrofs_modulus_large_ggf as Hmod_gt_8.
    assert (H8_repr : Ptrofs.unsigned (Ptrofs.repr 8) = 8).
    { apply Ptrofs.unsigned_repr. unfold Ptrofs.max_unsigned. lia. }
    set (go' := Ptrofs.add go (Ptrofs.repr 8)).
    assert (Hgo'_unsigned : Ptrofs.unsigned go' = Ptrofs.unsigned go + 8).
    { subst go'. unfold Ptrofs.add.
      rewrite H8_repr.
      apply Ptrofs.unsigned_repr. unfold Ptrofs.max_unsigned.
      replace (Z.of_nat (S n')) with (Z.of_nat n' + 1)%Z in Hbound by lia. lia. }
    rewrite IH.
    + rewrite Hgo'_unsigned.
      replace (Z.of_nat (S n')) with (Z.of_nat n' + 1)%Z by lia. lia.
    + rewrite Hgo'_unsigned.
      replace (Z.of_nat (S n')) with (Z.of_nat n' + 1)%Z in Hbound by lia. lia.
Qed.

Lemma global_repr_nth_error_ggf : forall hm cb0 co0 m gs gb go n v,
  global_repr hm cb0 co0 m gs gb go ->
  nth_error gs n = Some v ->
  Ptrofs.unsigned go + Z.of_nat n * 8 < Ptrofs.modulus ->
  exists cv,
    Mem.load Mint64 m gb (Ptrofs.unsigned go + Z.of_nat n * 8) = Some cv /\
    val_repr hm cb0 co0 v cv.
Proof.
  intros hm cb0 co0 m gs gb go n v Hgr Hnth Hbound.
  destruct (global_repr_nth_error_ptrofs_ggf hm cb0 co0 m gs gb go n v Hgr Hnth)
    as [cv [Hload Hval_repr]].
  exists cv. split; [| exact Hval_repr].
  rewrite <- (iter_add_8_unsigned_ggf go n Hbound).
  exact Hload.
Qed.

(* ================================================================== *)
(* Pointer arithmetic: global_data + n                                 *)
(* ================================================================== *)

Lemma sem_add_global_n_ggf : forall gb go i m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr gb go) (tptr tlong)
    (Vint i) tint
    m = Some (Vptr gb (Ptrofs.add go
                (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed i)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma ptrofs_global_offset_ggf : forall go n,
  0 <= Z.of_nat n <= Int.max_signed ->
  Ptrofs.unsigned go + Z.of_nat n * 8 < Ptrofs.modulus ->
  Ptrofs.unsigned (Ptrofs.add go
    (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat n)))))
  = Ptrofs.unsigned go + Z.of_nat n * 8.
Proof.
  intros go n Hn_range Hbound.
  unfold ptrofs_of_int.
  change (Ptrofs.of_ints (Int.repr (Z.of_nat n)))
    with (Ptrofs.repr (Int.signed (Int.repr (Z.of_nat n)))).
  change Int.max_signed with 2147483647 in Hn_range.
  rewrite Int.signed_repr by
    (unfold Int.min_signed, Int.max_signed, Int.half_modulus, Int.modulus,
     Int.wordsize, Wordsize_32.wordsize; simpl; lia).
  unfold Ptrofs.add, Ptrofs.mul.
  pose proof ptrofs_modulus_large_ggf as Hmod_gt.
  rewrite (Ptrofs.unsigned_repr 8) by (unfold Ptrofs.max_unsigned; lia).
  rewrite (Ptrofs.unsigned_repr (Z.of_nat n)).
  2: { unfold Ptrofs.max_unsigned. pose proof (Ptrofs.unsigned_range go). lia. }
  rewrite Ptrofs.unsigned_repr.
  - rewrite Ptrofs.unsigned_repr. lia.
    unfold Ptrofs.max_unsigned.
    change Ptrofs.modulus with 18446744073709551616%Z. lia.
  - rewrite (Ptrofs.unsigned_repr (8 * Z.of_nat n)).
    2: { unfold Ptrofs.max_unsigned. change Ptrofs.modulus with 18446744073709551616%Z. lia. }
    pose proof (Ptrofs.unsigned_range go). unfold Ptrofs.max_unsigned.
    change Ptrofs.modulus with 18446744073709551616%Z in *. lia.
Qed.

(* ================================================================== *)
(* Pointer arithmetic: (tptr tlong) + int p                            *)
(* ================================================================== *)

Lemma sem_add_ptr_long_p : forall b ofs i m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong)
    (Vint i) tint
    m = Some (Vptr b (Ptrofs.add ofs
                (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed i)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_GETGLOBALFIELD_correct : forall n p,
    handler_correct (handle_GETGLOBALFIELD n p) f_instr_GETGLOBALFIELD
      (fun _ m s ard =>
         (* Code buffer contains Int.repr (Z.of_nat n) at current PC *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* Code buffer contains Int.repr (Z.of_nat p) at PC+1 *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))) (Ptrofs.repr 4)))
         = Some (Vint (Int.repr (Z.of_nat p))) /\
         0 <= Z.of_nat n <= Int.max_signed /\
         0 <= Z.of_nat p <= Int.max_signed /\
         Ptrofs.unsigned (ar_global_ofs ard) + Z.of_nat n * 8 < Ptrofs.modulus /\
         (* When field_or_heap succeeds, the C memory has the field value,
            the global's C representation is a pointer on a block distinct
            from sb, and the field load is at that pointer + p*8. *)
         (forall glob v cv_global,
            nth_error s.(Machine.global) n = Some glob ->
            field_or_heap s glob p = Some v ->
            val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) glob cv_global ->
            exists b ofs cv,
              cv_global = Vptr b ofs /\
              b <> ar_sptr_block ard /\
              Mem.load Mint64 m b
                (Ptrofs.unsigned (Ptrofs.add ofs
                   (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat p))))))
                = Some cv /\
              val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) v cv))
      (fun msg s =>
         (nth_error s.(Machine.global) n = None /\ msg = "GETGLOBALFIELD: index out of bounds"%string) \/
         (exists glob, nth_error s.(Machine.global) n = Some glob /\
            field_or_heap s glob p = None /\ msg = "GETGLOBALFIELD: field access failed"%string))
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros n p.
  intros e le m s.
  unfold handle_GETGLOBALFIELD.
  destruct (nth_error (Machine.global s) n) as [glob|] eqn:Hnth.

  2: { (* Error: global index out of bounds *)
    left. split; reflexivity.
  }

  destruct (field_or_heap s glob p) as [fval|] eqn:Hfoh.

  2: { (* Error: field access failed *)
    right. exists glob. split; [reflexivity | split; [exact Hfoh | reflexivity]].
  }

  (* Step case *)
  intros ard Hpre Hstep_pre.
  unfold abs_rel_with_ard in Hpre.

  set (sb := ar_sptr_block ard) in *.
  set (so := ar_sptr_ofs ard) in *.
  set (hm := ar_heap_map ard) in *.
  set (cb := ar_code_base_block ard) in *.
  set (co := ar_code_base_ofs ard) in *.
  set (gb := ar_global_block ard) in *.
  set (go := ar_global_ofs ard) in *.

  destruct Hpre as (Hle_s &
    [pc_ptr [Hpc_load Hpc_rel]] &
    [accu_v [Haccu_load Haccu_repr]] &
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
    [env_v [Henv_load Henv_repr]] &
    Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
    [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
  subst sp_ptr. subst gd_ptr.

  destruct Hstep_pre as (Hcode_load_n & Hcode_load_p & Hn_range & Hp_range & Hgo_bound & Hfield_pre).

  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb gb in Hgb_ne.
  pose proof (code_block_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  destruct interp_state_co_ggf as [co_is [Hco [Hpc_offset [Haccu_offset Hgd_offset]]]].

  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* Get global value from memory *)
  destruct (global_repr_nth_error_ggf hm cb co m _ gb go n glob Hglobal_repr Hnth Hgo_bound)
    as [cv_global [Hglobal_load Hglobal_val_repr]].

  (* Pointer arithmetic for global *)
  assert (Hptr_arith_n : Ptrofs.unsigned (Ptrofs.add go
            (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat n)))))
          = Ptrofs.unsigned go + Z.of_nat n * 8).
  { apply ptrofs_global_offset_ggf; assumption. }

  (* Get field value from heap precondition *)
  destruct (Hfield_pre glob fval cv_global eq_refl Hfoh Hglobal_val_repr)
    as [fb [fofs [cv_field [Hcv_global_ptr [Hfb_ne_sb [Hfield_load Hfield_val_repr]]]]]].
  subst cv_global.

  (* ============================================================== *)
  (* Store 1: accu <- Vptr fb fofs (global[N])                       *)
  (* ============================================================== *)
  destruct (store_succeeds_sb m sb so 8 accu_v Hsb_writable Haccu_load ltac:(lia) ltac:(lia) (Vptr fb fofs))
    as [m1 Hstore1].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

  (* pc in m1 *)
  assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 8)
             (Ptrofs.unsigned so + 0) (Vptr fb fofs) (Vptr cb pc_ofs)
             Hstore1 Hpc_load).
    left. lia. }

  (* Code loads survive store1 (different block) *)
  assert (Hcode_load_n_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
            Some (Vint (Int.repr (Z.of_nat n)))).
  { eapply code_buffer_load_at; [exact Hcode_load_n | exact Hstore1 | exact Hcb_ne]. }

  (* ============================================================== *)
  (* Store 2: pc <- pc + 1 (advance past N)                          *)
  (* ============================================================== *)
  set (pc_ofs_1 := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
  set (pc_v_1 := Vptr cb pc_ofs_1).

  destruct (store_succeeds_sb m1 sb so 0 (Vptr cb pc_ofs) Hsb_writable_m1 Hpc_load_m1 ltac:(lia) ltac:(lia) pc_v_1)
    as [m2 Hstore2].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore2 Hsb_writable_m1) as Hsb_writable_m2.

  (* accu in m2 *)
  assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr fb fofs)).
  { assert (Haccu_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vptr fb fofs)).
    { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 8) (Vptr fb fofs) Hstore1) as Htmp.
      rewrite load_result_vptr_ggf in Htmp. exact Htmp. }
    apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 8) pc_v_1 (Vptr fb fofs)
             Hstore2 Haccu_m1). right. lia. }

  (* pc in m2 *)
  assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) =
            Some pc_v_1).
  { pose proof (load_after_store_same m1 m2 sb (Ptrofs.unsigned so + 0) pc_v_1 Hstore2) as Htmp.
    unfold pc_v_1 in Htmp |- *. rewrite load_result_vptr_ggf in Htmp. exact Htmp. }

  (* Code load for P survives stores 1,2 *)
  assert (Hcode_load_p_m2 : Mem.load Mint32 m2 cb (Ptrofs.unsigned pc_ofs_1) =
            Some (Vint (Int.repr (Z.of_nat p)))).
  { assert (Hcode_load_p_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned (Ptrofs.add pc_ofs (Ptrofs.repr 4))) =
              Some (Vint (Int.repr (Z.of_nat p)))).
    { eapply code_buffer_load_at; [exact Hcode_load_p | exact Hstore1 | exact Hcb_ne]. }
    eapply code_buffer_load_at; [exact Hcode_load_p_m1 | exact Hstore2 | exact Hcb_ne]. }

  (* Field load survives stores 1,2 (fb <> sb) *)
  set (field_ofs := Ptrofs.unsigned (Ptrofs.add fofs
         (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat p)))))) in *.
  assert (Hfield_load_m2 : Mem.load Mint64 m2 fb field_ofs = Some cv_field).
  { assert (Hfield_load_m1 : Mem.load Mint64 m1 fb field_ofs = Some cv_field).
    { erewrite Mem.load_store_other. exact Hfield_load. exact Hstore1.
      left. intro Heq. exact (Hfb_ne_sb Heq). }
    erewrite Mem.load_store_other. exact Hfield_load_m1. exact Hstore2.
    left. intro Heq. exact (Hfb_ne_sb Heq). }

  (* ============================================================== *)
  (* Store 3: accu <- cv_field (field[P] of global[N])               *)
  (* ============================================================== *)
  destruct (store_succeeds_sb m2 sb so 8 (Vptr fb fofs) Hsb_writable_m2 Haccu_load_m2 ltac:(lia) ltac:(lia) cv_field)
    as [m3 Hstore3].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore3 Hsb_writable_m2) as Hsb_writable_m3.

  (* pc in m3 *)
  assert (Hpc_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 0) =
            Some pc_v_1).
  { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 8)
             (Ptrofs.unsigned so + 0) cv_field pc_v_1
             Hstore3 Hpc_load_m2). left. lia. }

  (* ============================================================== *)
  (* Store 4: pc <- pc + 1 (advance past P)                          *)
  (* ============================================================== *)
  set (pc_ofs_2 := Ptrofs.add pc_ofs_1 (Ptrofs.repr 4)).
  set (pc_v_2 := Vptr cb pc_ofs_2).

  destruct (store_succeeds_sb m3 sb so 0 pc_v_1 Hsb_writable_m3 Hpc_load_m3 ltac:(lia) ltac:(lia) pc_v_2)
    as [m4 Hstore4].

  (* Global load in m1 (for sem evaluation) *)
  assert (Hglobal_load_m1 : Mem.load Mint64 m1 gb
            (Ptrofs.unsigned go + Z.of_nat n * 8) = Some (Vptr fb fofs)).
  { erewrite Mem.load_store_other. exact Hglobal_load. exact Hstore1.
    left. intro Heq. exact (Hgb_ne Heq). }

  (* ============================================================== *)
  (* Witnesses                                                       *)
  (* ============================================================== *)

  set (le' := PTree.set _t'1 pc_v_1
              (PTree.set _t'5 cv_field
              (PTree.set _t'4 (Vint (Int.repr (Z.of_nat p)))
              (PTree.set _t'3 pc_v_1
              (PTree.set _t'2 (Vptr fb fofs)
              (PTree.set _t'6 (Vptr cb pc_ofs)
              (PTree.set _t'10 (Vptr fb fofs)
              (PTree.set _t'9 (Vint (Int.repr (Z.of_nat n)))
              (PTree.set _t'8 (Vptr cb pc_ofs)
              (PTree.set _t'7 (Vptr gb go) le)))))))))).
  exists le'. exists m4.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ============================================================== *)
  (* Part 1: exec via computational evaluator                        *)
  (* ============================================================== *)
  {
    apply (eval_stmt_to_exec clight_ge 30).
    eval_cbn.

    (* ============================================================ *)
    (* Phase 1: GETGLOBAL part                                       *)
    (* ============================================================ *)

    (* S1: Sset _t'7 (s->global_data) *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hgd_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 40 ltac:(lia) ltac:(lia)).
    rewrite Hgd_load; eval_cbn.

    (* S2: Sset _t'8 (s->pc) *)
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Hpc_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load; eval_cbn.

    (* S3: Sset _t'9 (deref _t'8) -- read N from code buffer *)
    rewrite PTree.gss; eval_cbn.
    rewrite Hcode_load_n; eval_cbn.

    (* S4: Sset _t'10 (deref (cast(_t'7) + _t'9)) -- load global[N] *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_ptr_to_ptr gb go m); eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_global_n_ggf gb go (Int.repr (Z.of_nat n)) m); eval_cbn.
    rewrite Hptr_arith_n.
    rewrite Hglobal_load; eval_cbn.

    (* S5: Sassign (s->accu) _t'10 *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_vptr fb fofs); eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Hstore1; eval_cbn.

    (* ============================================================ *)
    (* Phase 2: advance pc past N                                    *)
    (* ============================================================ *)

    (* S6: Sset _t'6 (s->pc) -- read pc from m1 *)
    repeat rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m1; eval_cbn.

    (* S7: Sassign (s->pc) (_t'6 + 1) *)
    repeat rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_pc_1_ggf cb pc_ofs m1); eval_cbn.
    rewrite (sem_cast_ptr_tint_to_ptr_tint_ggf cb pc_ofs_1); eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    fold pc_v_1.
    rewrite Hstore2; eval_cbn.

    (* ============================================================ *)
    (* Phase 3: GETFIELD part                                        *)
    (* ============================================================ *)

    (* S8: Sset _t'2 (s->accu) -- read accu from m2 *)
    repeat rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m2; eval_cbn.

    (* S9: Sset _t'3 (s->pc) -- read pc from m2 *)
    repeat rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m2; eval_cbn.

    (* S10: Sset _t'4 (deref _t'3) -- read P from code buffer *)
    rewrite PTree.gss; eval_cbn.
    rewrite Hcode_load_p_m2; eval_cbn.

    (* S11: Sset _t'5 (deref (cast(_t'2) + _t'4)) -- load field[P] *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_to_ptr_vptr_ggf fb fofs m2); eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_ptr_long_p fb fofs (Int.repr (Z.of_nat p)) m2); eval_cbn.
    fold field_ofs.
    rewrite Hfield_load_m2; eval_cbn.

    (* S12: Sassign (s->accu) _t'5 *)
    repeat rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hfield_val_repr); eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Hstore3; eval_cbn.

    (* ============================================================ *)
    (* Phase 4: advance pc past P                                    *)
    (* ============================================================ *)

    (* S13: Sset _t'1 (s->pc) -- read pc from m3 *)
    repeat rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m3; eval_cbn.

    (* S14: Sassign (s->pc) (_t'1 + 1) *)
    repeat rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    unfold pc_v_1.
    rewrite (sem_add_pc_1_ggf cb pc_ofs_1 m3); eval_cbn.
    rewrite (sem_cast_ptr_tint_to_ptr_tint_ggf cb (Ptrofs.add pc_ofs_1 (Ptrofs.repr 4))); eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    fold pc_ofs_2. fold pc_v_2.
    rewrite Hstore4; eval_cbn.

    (* S15: Sreturn 0 *)
    subst le'. reflexivity.
  }

  (* ============================================================== *)
  (* Part 2: abs_rel for post-state                                  *)
  (* ============================================================== *)
  {
    set (new_co := Ptrofs.add co (Ptrofs.repr (2 * sizeof_code_t))).
    set (ard' := mk_abs_rel
      (ar_sptr_block ard) (ar_sptr_ofs ard) (ar_heap_map ard)
      (ar_code_base_block ard) new_co
      (ar_global_block ard) (ar_global_ofs ard)
      (ar_stack_block ard) (ar_stack_base_ofs ard)
      (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
    exists ard'.

    (* pc at Ptrofs.unsigned so+0: written by store4 *)
    assert (Hpc_load4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 0) = Some pc_v_2).
    { pose proof (load_after_store_same m3 m4 sb (Ptrofs.unsigned so + 0) pc_v_2 Hstore4) as Htmp.
      unfold pc_v_2 in Htmp |- *. rewrite load_result_vptr_ggf in Htmp. exact Htmp. }

    (* accu at Ptrofs.unsigned so+8: written by store3, survives store4 *)
    assert (Haccu_load4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 8) = Some cv_field).
    { assert (Haccu_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 8) = Some cv_field).
      { pose proof (load_after_store_same m2 m3 sb (Ptrofs.unsigned so + 8) cv_field Hstore3) as Htmp.
        rewrite (val_repr_load_result hm cb co fval cv_field Hfield_val_repr) in Htmp.
        exact Htmp. }
      apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 8)
               pc_v_2 cv_field Hstore4 Haccu_m3). right. lia. }

    (* sp at Ptrofs.unsigned so+16: survives all 4 stores *)
    assert (Hsp_load4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
    { assert (Hsp_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 16)
                 (Vptr fb fofs) (Vptr sp_b sp_ofs) Hstore1 Hsp_load). right. lia. }
      assert (Hsp_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
                 pc_v_1 (Vptr sp_b sp_ofs) Hstore2 Hsp_m1). right. lia. }
      assert (Hsp_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 16)
                 cv_field (Vptr sp_b sp_ofs) Hstore3 Hsp_m2). right. lia. }
      apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
               pc_v_2 (Vptr sp_b sp_ofs) Hstore4 Hsp_m3). right. lia. }

    (* env at Ptrofs.unsigned so+24: survives all 4 stores *)
    assert (Henv_load4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { assert (Henv_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some env_v).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 24)
                 (Vptr fb fofs) env_v Hstore1 Henv_load). right. lia. }
      assert (Henv_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 24) = Some env_v).
      { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 24)
                 pc_v_1 env_v Hstore2 Henv_m1). right. lia. }
      assert (Henv_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 24) = Some env_v).
      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 24)
                 cv_field env_v Hstore3 Henv_m2). right. lia. }
      apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 24)
               pc_v_2 env_v Hstore4 Henv_m3). right. lia. }

    (* extra_args at Ptrofs.unsigned so+32: survives all 4 stores *)
    assert (Hextra_load4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { assert (Hextra_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 32)
                 (Vptr fb fofs) _ Hstore1 Hextra_load). right. lia. }
      assert (Hextra_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 32)
                 pc_v_1 _ Hstore2 Hextra_m1). right. lia. }
      assert (Hextra_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 32)
                 cv_field _ Hstore3 Hextra_m2). right. lia. }
      apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 32)
               pc_v_2 _ Hstore4 Hextra_m3). right. lia. }

    (* global_data at Ptrofs.unsigned so+40: survives all 4 stores *)
    assert (Hgd_load4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 40) = Some (Vptr gb go)).
    { assert (Hgd_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 40) = Some (Vptr gb go)).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 40)
                 (Vptr fb fofs) (Vptr gb go) Hstore1 Hgd_load). right. lia. }
      assert (Hgd_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 40) = Some (Vptr gb go)).
      { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 40)
                 pc_v_1 (Vptr gb go) Hstore2 Hgd_m1). right. lia. }
      assert (Hgd_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 40) = Some (Vptr gb go)).
      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 40)
                 cv_field (Vptr gb go) Hstore3 Hgd_m2). right. lia. }
      apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 40)
               pc_v_2 (Vptr gb go) Hstore4 Hgd_m3). right. lia. }

    (* trap_sp at Ptrofs.unsigned so+48: survives all 4 stores *)
    assert (Hts_load4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
    { assert (Hts_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 48)
                 (Vptr fb fofs) ts_ptr Hstore1 Hts_load). right. lia. }
      assert (Hts_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 48)
                 pc_v_1 ts_ptr Hstore2 Hts_m1). right. lia. }
      assert (Hts_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 48)
                 cv_field ts_ptr Hstore3 Hts_m2). right. lia. }
      apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 48)
               pc_v_2 ts_ptr Hstore4 Hts_m3). right. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le' *)
    { subst le'.
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
      exact Hle_s. }

    (* 2. pc field -- updated to pc_v_2 *)
    { exists pc_v_2. split.
      - exact Hpc_load4.
      - simpl. subst pc_v_2 pc_ofs_2 pc_ofs_1.
        apply pc_rel_shift_2. }

    (* 3. accu field -- updated to field value *)
    { exists cv_field. split.
      - exact Haccu_load4.
      - simpl. eapply val_repr_co_shift. exact Hfield_val_repr. }

    (* 4. sp field -- unchanged *)
    { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load4.
      - reflexivity.
      - simpl.
        eapply stack_repr_co_shift.
        eapply (stack_repr_store_other_block hm cb co m3 m4 _ sp_b sp_ofs sb (Ptrofs.unsigned so + 0) pc_v_2).
        + eapply (stack_repr_store_other_block hm cb co m2 m3 _ sp_b sp_ofs sb (Ptrofs.unsigned so + 8) cv_field).
          * eapply (stack_repr_store_other_block hm cb co m1 m2 _ sp_b sp_ofs sb (Ptrofs.unsigned so + 0) pc_v_1).
            -- eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b sp_ofs sb (Ptrofs.unsigned so + 8) (Vptr fb fofs)).
               ++ exact Hstack_repr.
               ++ exact Hstore1.
               ++ intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
            -- exact Hstore2.
            -- intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          * exact Hstore3.
          * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        + exact Hstore4.
        + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - exact Hsp_ge8.
      - exact Hsp_rep.
      - intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore4.
        eapply Mem.perm_store_1. exact Hstore3.
        eapply Mem.perm_store_1. exact Hstore2.
        eapply Mem.perm_store_1. exact Hstore1.
        apply Hsp_writable. exact Hofs'.
      - exact Hsp_align. }

    (* 5. env field -- unchanged *)
    { exists env_v. split.
      - exact Henv_load4.
      - simpl. eapply val_repr_co_shift. exact Henv_repr. }

    (* 6. extra_args field -- unchanged *)
    { simpl. exact Hextra_load4. }

    (* 7. global_data field -- unchanged *)
    { exists (Vptr gb go). split; [| split; [| split]].
      - exact Hgd_load4.
      - simpl. reflexivity.
      - simpl.
        eapply global_repr_co_shift.
        eapply (global_repr_store_other_block hm cb co m3 m4 _
                 gb go sb (Ptrofs.unsigned so + 0) pc_v_2).
        + eapply (global_repr_store_other_block hm cb co m2 m3 _
                   gb go sb (Ptrofs.unsigned so + 8) cv_field).
          * eapply (global_repr_store_other_block hm cb co m1 m2 _
                     gb go sb (Ptrofs.unsigned so + 0) pc_v_1).
            -- eapply (global_repr_store_other_block hm cb co m m1 _
                         gb go sb (Ptrofs.unsigned so + 8) (Vptr fb fofs)).
               ++ exact Hglobal_repr.
               ++ exact Hstore1.
               ++ intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
            -- exact Hstore2.
            -- intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          * exact Hstore3.
          * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        + exact Hstore4.
        + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load4.
      - simpl. exact Htrap_rel. }

    (* 9. sb_writable -- permission preserved through all 4 stores *)
    { intros ofs' Hofs'.
      eapply Mem.perm_store_1. exact Hstore4.
      eapply Mem.perm_store_1. exact Hstore3.
      eapply Mem.perm_store_1. exact Hstore2.
      eapply Mem.perm_store_1. exact Hstore1.
      apply Hsb_writable. exact Hofs'. }
  }
Qed.
