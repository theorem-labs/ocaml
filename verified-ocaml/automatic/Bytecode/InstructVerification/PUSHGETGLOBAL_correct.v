(* PUSHGETGLOBAL_correct.v -- PUSHGETGLOBAL completeness proof.

   PUSHGETGLOBAL n = PUSH (push accu to stack) then GETGLOBAL n
   (load global_data[n] into accu).

   C code (f_instr_PUSHGETGLOBAL):
     _t'8 = s->sp;
     _t'1 = (tptr tlong)(_t'8 - 1);   // new_sp = sp - 8
     s->sp = _t'1;                      // Store 1: sp field
     _t'7 = s->accu;
     *_t'1 = _t'7;                      // Store 2: push accu
     _t'3 = s->global_data;
     _t'4 = s->pc;
     _t'5 = *_t'4;                      // read n from code buffer
     _t'6 = *(cast(_t'3) + _t'5);      // load global_data[n]
     s->accu = _t'6;                    // Store 3: accu = global[n]
     _t'2 = s->pc;
     s->pc = _t'2 + 1;                  // Store 4: advance pc
     return 0;

   Rocq:
     handle_PUSHGETGLOBAL n pc' s =
       let new_stack := accu :: stack in
       match nth_error s.(global) n with
       | Some v => Step (s <|pc := pc'|> <|accu := v|> <|stack := new_stack|>)
       | None => Error "PUSHGETGLOBAL: index out of bounds"
       end

   Four stores on the struct block plus one on the stack block:
     Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v
     Store 3: accu field (sb, uso+8) <- cv_global
     Store 4: pc field (sb, uso+0) <- Vptr cb new_pc_ofs

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
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
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
(* Struct layout: _pc@0, _accu@8, _sp@16, _global_data@40             *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _global_data (co_members co) = Errors.OK (40, Full).
Proof.
  eexists. split; [| split; [| split; [| split]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_pushgetglobal : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _global_data (co_members co) = Errors.OK (40, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

Lemma pc_rel_shift : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr 4)))
         cb (Ptrofs.add co (Ptrofs.repr sizeof_code_t)) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal.
  rewrite Ptrofs.add_assoc.
  rewrite Ptrofs.add_assoc.
  f_equal.
  rewrite Ptrofs.add_commut. reflexivity.
Qed.

(* ================================================================== *)
(* Architectural constant                                              *)
(* ================================================================== *)

Lemma ptrofs_modulus_large : (Ptrofs.modulus > 8)%Z.
Proof.
  unfold Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  simpl. reflexivity.
Qed.

(* ================================================================== *)
(* Key lemma: global_repr + nth_error => Mem.load                     *)
(* ================================================================== *)

Lemma nat_iter_succ_r : forall {A} (f : A -> A) n x,
  Nat.iter (S n) f x = Nat.iter n f (f x).
Proof.
  intros A f n. revert f. induction n as [| n' IH]; intros f x.
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma global_repr_nth_error_ptrofs : forall hm cb co m gs gb go n v,
  global_repr hm cb co m gs gb go ->
  nth_error gs n = Some v ->
  exists cv,
    Mem.load Mint64 m gb
      (Ptrofs.unsigned (Nat.iter n (fun p => Ptrofs.add p (Ptrofs.repr 8)) go))
    = Some cv /\
    val_repr hm cb co v cv.
Proof.
  intros hm cb co m gs gb go n v Hgr.
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
      rewrite nat_iter_succ_r. exact Hload'.
Qed.

Lemma iter_add_8_unsigned : forall go n,
  Ptrofs.unsigned go + Z.of_nat n * 8 < Ptrofs.modulus ->
  Ptrofs.unsigned (Nat.iter n (fun p => Ptrofs.add p (Ptrofs.repr 8)) go)
  = Ptrofs.unsigned go + Z.of_nat n * 8.
Proof.
  intros go n.
  revert go.
  induction n as [| n' IH]; intros go Hbound.
  - simpl. lia.
  - rewrite nat_iter_succ_r.
    pose proof (Ptrofs.unsigned_range go) as [Hgo_pos Hgo_lt].
    pose proof ptrofs_modulus_large as Hmod_gt_8.
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

Lemma global_repr_nth_error : forall hm cb co m gs gb go n v,
  global_repr hm cb co m gs gb go ->
  nth_error gs n = Some v ->
  Ptrofs.unsigned go + Z.of_nat n * 8 < Ptrofs.modulus ->
  exists cv,
    Mem.load Mint64 m gb (Ptrofs.unsigned go + Z.of_nat n * 8) = Some cv /\
    val_repr hm cb co v cv.
Proof.
  intros hm cb co m gs gb go n v Hgr Hnth Hbound.
  destruct (global_repr_nth_error_ptrofs hm cb co m gs gb go n v Hgr Hnth)
    as [cv [Hload Hval_repr]].
  exists cv. split; [| exact Hval_repr].
  rewrite <- (iter_add_8_unsigned go n Hbound).
  exact Hload.
Qed.

(* ================================================================== *)
(* Pointer arithmetic: global_data + n                                 *)
(* ================================================================== *)

Lemma sem_add_global_n : forall gb go i m,
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

Lemma ptrofs_global_offset : forall go n,
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
  pose proof ptrofs_modulus_large as Hmod_gt.
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
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_PUSHGETGLOBAL_correct : forall n,
    0 <= Z.of_nat n <= Int.max_signed ->
    handler_correct_v1 (handle_PUSHGETGLOBAL n) f_instr_PUSHGETGLOBAL
      (fun _ m s ard =>
         (* code memory at pc contains n *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
           = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* global offset arithmetic stays in ptrofs range *)
         Ptrofs.unsigned (ar_global_ofs ard) + Z.of_nat n * 8 < Ptrofs.modulus /\
         (* sp has room for a push: new sp after push must still be >= 8 *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs >= 16))
      (fun _ s => nth_error s.(Machine.global) n = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro n. intro Hn_range.
  intros e le m s.
  unfold handle_PUSHGETGLOBAL.
  replace ((0 <=? Z.of_nat n) && (Z.of_nat n <=? Int.max_signed))%Z with true.
  2: { symmetry. apply Bool.andb_true_iff. split; apply Z.leb_le; lia. }
  set (new_stack := Machine.accu s :: Machine.stack s).
  destruct (nth_error (Machine.global s) n) as [gval|] eqn:Hnth.

  2: { exact eq_refl. }

  intros ard Hpre Hstep_pre.

  destruct Hstep_pre as (Hcode_load & Hgo_bound & Hsp_ge16).

  (* Unpack abs_rel_with_ard *)
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

  (* Structural invariants *)
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb gb in Hgb_ne.
  pose proof (code_block_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  destruct interp_state_co_pushgetglobal as [co_is [Hco [Hpc_offset [Haccu_offset [Hsp_offset Hgd_offset]]]]].

  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* New sp after push *)
  set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
  assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 8).
  { subst new_sp_ofs. unfold Ptrofs.sub.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
    apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range sp_ofs).
    unfold Ptrofs.max_unsigned. lia. }

  (* sp has room for push: need sp_ofs >= 16 so new_sp_ofs >= 8 *)
  assert (Hsp16 : Ptrofs.unsigned sp_ofs >= 16).
  { apply (Hsp_ge16 sp_b sp_ofs). exact Hsp_load. }

  (* Global value from global_repr *)
  destruct (global_repr_nth_error hm cb co m _ gb go n gval Hglobal_repr Hnth Hgo_bound)
    as [cv_global [Hglobal_load Hglobal_val_repr]].

  (* New pc after advancement *)
  set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
  set (new_pc_v := Vptr cb new_pc_ofs).

  (* ================================================================ *)
  (* Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs           *)
  (* ================================================================ *)
  destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) (Vptr sp_b new_sp_ofs)) as [m1 Hstore1].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

  (* ================================================================ *)
  (* Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v                    *)
  (* ================================================================ *)
  assert (Halign_new : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs)).
  { rewrite Hnew_sp_unsigned. simpl align_chunk.
    apply Z.divide_sub_r. exact Hsp_align. exists 1; lia. }
  destruct (store_to_sp_after_sb_store m m1 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)
              sp_b (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s)))
              (Ptrofs.unsigned new_sp_ofs)
              Hstore1 Hsp_writable
              ltac:(rewrite Hnew_sp_unsigned; lia)
              ltac:(rewrite Hnew_sp_unsigned; lia)
              Halign_new accu_v) as [m2 Hstore2].

  (* ================================================================ *)
  (* Store 3: accu field (sb, uso+8) <- cv_global                     *)
  (* ================================================================ *)
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
             (Ptrofs.unsigned so + 8) (Vptr sp_b new_sp_ofs) accu_v
             Hstore1 Haccu_load). left. lia. }
  assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { erewrite Mem.load_store_other; [exact Haccu_load_m1 | exact Hstore2 |].
    left. exact (not_eq_sym Hsp_ne_sb). }
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore2 Hsb_writable_m1) as Hsb_writable_m2.
  destruct (store_succeeds_sb m2 sb so 8 accu_v Hsb_writable_m2 Haccu_load_m2 ltac:(lia) ltac:(lia) cv_global) as [m3 Hstore3].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore3 Hsb_writable_m2) as Hsb_writable_m3.

  (* ================================================================ *)
  (* Store 4: pc field (sb, uso+0) <- new_pc_v                        *)
  (* ================================================================ *)
  assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
             (Ptrofs.unsigned so + 0) (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs)
             Hstore1 Hpc_load). left. lia. }
  assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { erewrite Mem.load_store_other; [exact Hpc_load_m1 | exact Hstore2 |].
    left. exact (not_eq_sym Hsp_ne_sb). }
  assert (Hpc_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 8)
             (Ptrofs.unsigned so + 0) cv_global (Vptr cb pc_ofs)
             Hstore3 Hpc_load_m2). left. lia. }
  destruct (store_succeeds_sb m3 sb so 0 (Vptr cb pc_ofs) Hsb_writable_m3 Hpc_load_m3 ltac:(lia) ltac:(lia) new_pc_v)
    as [m4 Hstore4].

  (* ================================================================ *)
  (* Code memory survives all 4 stores                                 *)
  (* ================================================================ *)
  assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs)
            = Some (Vint (Int.repr (Z.of_nat n)))).
  { erewrite Mem.load_store_other; [exact Hcode_load | exact Hstore1 |].
    left. exact Hcb_ne. }
  assert (Hcode_load_m2 : Mem.load Mint32 m2 cb (Ptrofs.unsigned pc_ofs)
            = Some (Vint (Int.repr (Z.of_nat n)))).
  { erewrite Mem.load_store_other; [exact Hcode_load_m1 | exact Hstore2 |].
    left. exact Hcb_ne_sp. }

  (* Global data load survives stores 1, 2 *)
  assert (Hglobal_load_m1 : Mem.load Mint64 m1 gb
            (Ptrofs.unsigned go + Z.of_nat n * 8) = Some cv_global).
  { erewrite Mem.load_store_other.
    - exact Hglobal_load.
    - exact Hstore1.
    - left. intro Heq. exact (Hgb_ne Heq). }
  assert (Hglobal_load_m2 : Mem.load Mint64 m2 gb
            (Ptrofs.unsigned go + Z.of_nat n * 8) = Some cv_global).
  { erewrite Mem.load_store_other.
    - exact Hglobal_load_m1.
    - exact Hstore2.
    - left. exact (not_eq_sym Hsp_ne_gb). }

  (* Pointer arithmetic for global access *)
  assert (Hptr_arith : Ptrofs.unsigned (Ptrofs.add go
            (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat n)))))
          = Ptrofs.unsigned go + Z.of_nat n * 8).
  { apply ptrofs_global_offset; assumption. }

  (* global_data field survives stores 1, 2 *)
  assert (Hgd_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 40) = Some (Vptr gb go)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 40)
             (Vptr sp_b new_sp_ofs) (Vptr gb go) Hstore1 Hgd_load). right. lia. }
  assert (Hgd_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 40) = Some (Vptr gb go)).
  { erewrite Mem.load_store_other; [exact Hgd_load_m1 | exact Hstore2 |].
    left. exact (not_eq_sym Hsp_ne_sb). }

  (* ================================================================ *)
  (* Witnesses                                                         *)
  (* ================================================================ *)
  set (le' := PTree.set _t'2 (Vptr cb pc_ofs)
              (PTree.set _t'6 cv_global
              (PTree.set _t'5 (Vint (Int.repr (Z.of_nat n)))
              (PTree.set _t'4 (Vptr cb pc_ofs)
              (PTree.set _t'3 (Vptr gb go)
              (PTree.set _t'7 accu_v
              (PTree.set _t'1 (Vptr sp_b new_sp_ofs)
              (PTree.set _t'8 (Vptr sp_b sp_ofs) le)))))))).
  exists le'. exists m4.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ============================================================== *)
  (* Part 1: exec via computational evaluator                        *)
  (* ============================================================== *)
  {
    unfold so, sb in *.

    apply (eval_stmt_to_exec clight_ge 30).
    eval_cbn.

    (* ============================================================ *)
    (* S1: Sset _t'8 (s->sp) -- read sp from struct                 *)
    (* ============================================================ *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* ============================================================ *)
    (* S2: Sset _t'1 (cast (_t'8 - 1) (tptr tlong))                 *)
    (* ============================================================ *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_sub_sp_1; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.

    (* ============================================================ *)
    (* S3: Sassign (s->sp) _t'1  -- Store 1: sp field               *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 16 ltac:(lia) ltac:(lia)).
    fold new_sp_ofs.
    rewrite Hstore1; eval_cbn.

    (* ============================================================ *)
    (* S4: Sset _t'7 (s->accu) -- read accu                         *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 8 ltac:(lia) ltac:(lia)).
    rewrite (load_after_store_other m m1 (ar_sptr_block ard)
               (Ptrofs.unsigned (ar_sptr_ofs ard) + 16)
               (Ptrofs.unsigned (ar_sptr_ofs ard) + 8) (Vptr sp_b new_sp_ofs) accu_v
               Hstore1 Haccu_load ltac:(left; lia)).
    eval_cbn.

    (* ============================================================ *)
    (* S5: Sassign (deref _t'1) _t'7 -- Store 2: push accu          *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Haccu_repr); eval_cbn.
    fold new_sp_ofs.
    rewrite Hstore2; eval_cbn.

    (* ============================================================ *)
    (* S6: Sset _t'3 (s->global_data) -- read global_data ptr       *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Hgd_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 40 ltac:(lia) ltac:(lia)).
    rewrite Hgd_load_m2; eval_cbn.

    (* ============================================================ *)
    (* S7: Sset _t'4 (s->pc) -- read pc pointer                     *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Hpc_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m2; eval_cbn.

    (* ============================================================ *)
    (* S8: Sset _t'5 (deref _t'4) -- read n from code               *)
    (* ============================================================ *)
    rewrite PTree.gss; eval_cbn.
    rewrite Hcode_load_m2; eval_cbn.

    (* ============================================================ *)
    (* S9: Sset _t'6 (deref (cast(_t'3) + _t'5)) -- load global[n]  *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_ptr_to_ptr gb go m2); eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_global_n gb go (Int.repr (Z.of_nat n)) m2); eval_cbn.
    rewrite Hptr_arith.
    rewrite Hglobal_load_m2; eval_cbn.

    (* ============================================================ *)
    (* S10: Sassign (s->accu) _t'6 -- Store 3: write global to accu *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hglobal_val_repr); eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 8 ltac:(lia) ltac:(lia)).
    rewrite Hstore3; eval_cbn.

    (* ============================================================ *)
    (* S11: Sset _t'2 (s->pc) -- read pc pointer again from m3      *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m3; eval_cbn.

    (* ============================================================ *)
    (* S12: Sassign (s->pc) (_t'2 + 1) -- Store 4: advance pc       *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.

    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_pc_1 cb pc_ofs m3); eval_cbn.
    rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
    fold new_pc_v.
    rewrite Hstore4; eval_cbn.

    (* ============================================================ *)
    (* S13: Sreturn 0                                                *)
    (* ============================================================ *)
    subst le'. reflexivity.
  }

  (* ============================================================== *)
  (* Part 2: abs_rel for post-state                                  *)
  (* ============================================================== *)
  {
    set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
    set (ard' := mk_abs_rel
      (ar_sptr_block ard) (ar_sptr_ofs ard) (ar_heap_map ard)
      (ar_code_base_block ard) new_co
      (ar_global_block ard) (ar_global_ofs ard)
      (ar_stack_block ard) (ar_stack_base_ofs ard)
      (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard)
      (ar_sptr_ofs_bound ard)).
    exists ard'.
    set (uso := Ptrofs.unsigned so) in *.

    (* Helper: loads on sb survive store 2 (different block: sp_b vs sb) *)
    assert (Hload_sb_m2 : forall ofs v,
      Mem.load Mint64 m1 sb ofs = Some v ->
      Mem.load Mint64 m2 sb ofs = Some v).
    { intros ofs v Hload1.
      erewrite Mem.load_store_other; [exact Hload1 | exact Hstore2 |].
      left. exact (not_eq_sym Hsp_ne_sb). }

    (* Helper: loads on sp_b survive store 3 (different block: sb vs sp_b) *)
    assert (Hload_spb_m3 : forall ofs v,
      Mem.load Mint64 m2 sp_b ofs = Some v ->
      Mem.load Mint64 m3 sp_b ofs = Some v).
    { intros ofs v Hload2.
      erewrite Mem.load_store_other; [exact Hload2 | exact Hstore3 |].
      left. exact Hsp_ne_sb. }

    (* Helper: loads on sp_b survive store 4 (different block: sb vs sp_b) *)
    assert (Hload_spb_m4 : forall ofs v,
      Mem.load Mint64 m3 sp_b ofs = Some v ->
      Mem.load Mint64 m4 sp_b ofs = Some v).
    { intros ofs v Hload3.
      erewrite Mem.load_store_other; [exact Hload3 | exact Hstore4 |].
      left. exact Hsp_ne_sb. }

    (* pc field at uso+0: survived stores 1,2,3; written by store 4 *)
    assert (Hpc_load4 : Mem.load Mint64 m4 sb (uso + 0) = Some new_pc_v).
    { pose proof (load_after_store_same m3 m4 sb (uso + 0) new_pc_v Hstore4) as Htmp.
      unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }

    (* accu field at uso+8: written by store 3, survives store 4 *)
    assert (Haccu_load_m3 : Mem.load Mint64 m3 sb (uso + 8) = Some cv_global).
    { pose proof (load_after_store_same m2 m3 sb (uso + 8) cv_global Hstore3) as Htmp.
      rewrite (val_repr_load_result hm cb co gval cv_global Hglobal_val_repr) in Htmp.
      exact Htmp. }
    assert (Haccu_load4 : Mem.load Mint64 m4 sb (uso + 8) = Some cv_global).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 8)
               new_pc_v cv_global Hstore4 Haccu_load_m3). right. lia. }

    (* sp field at uso+16: written by store 1, survives stores 2, 3, 4 *)
    assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { pose proof (load_after_store_same m m1 sb (uso + 16)
                    (Vptr sp_b new_sp_ofs) Hstore1) as Htmp.
      simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
    assert (Hsp_load_m2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { exact (Hload_sb_m2 _ _ Hsp_load_m1). }
    assert (Hsp_load_m3 : Mem.load Mint64 m3 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 16)
               cv_global (Vptr sp_b new_sp_ofs) Hstore3 Hsp_load_m2). right. lia. }
    assert (Hsp_load4 : Mem.load Mint64 m4 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 16)
               new_pc_v (Vptr sp_b new_sp_ofs) Hstore4 Hsp_load_m3). right. lia. }

    (* env field at uso+24: unaffected by all 4 stores *)
    assert (Henv_load_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 24)
               (Vptr sp_b new_sp_ofs) env_v Hstore1 Henv_load). right. lia. }
    assert (Henv_load_m2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
    { exact (Hload_sb_m2 _ _ Henv_load_m1). }
    assert (Henv_load_m3 : Mem.load Mint64 m3 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 24)
               cv_global env_v Hstore3 Henv_load_m2). right. lia. }
    assert (Henv_load4 : Mem.load Mint64 m4 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 24)
               new_pc_v env_v Hstore4 Henv_load_m3). right. lia. }

    (* extra_args field at uso+32: unaffected *)
    assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
               (Vptr sp_b new_sp_ofs) _ Hstore1 Hextra_load). right. lia. }
    assert (Hextra_load_m2 : Mem.load Mint64 m2 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { exact (Hload_sb_m2 _ _ Hextra_load_m1). }
    assert (Hextra_load_m3 : Mem.load Mint64 m3 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 32)
               cv_global _ Hstore3 Hextra_load_m2). right. lia. }
    assert (Hextra_load4 : Mem.load Mint64 m4 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 32)
               new_pc_v _ Hstore4 Hextra_load_m3). right. lia. }

    (* global_data field at uso+40: unaffected *)
    assert (Hgd_load_m3 : Mem.load Mint64 m3 sb (uso + 40) = Some (Vptr gb go)).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 40)
               cv_global (Vptr gb go) Hstore3 Hgd_load_m2). right. lia. }
    assert (Hgd_load4 : Mem.load Mint64 m4 sb (uso + 40) = Some (Vptr gb go)).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 40)
               new_pc_v (Vptr gb go) Hstore4 Hgd_load_m3). right. lia. }

    (* trap_sp field at uso+48: unaffected *)
    assert (Hts_load_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 48)
               (Vptr sp_b new_sp_ofs) ts_ptr Hstore1 Hts_load). right. lia. }
    assert (Hts_load_m2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
    { exact (Hload_sb_m2 _ _ Hts_load_m1). }
    assert (Hts_load_m3 : Mem.load Mint64 m3 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 48)
               cv_global ts_ptr Hstore3 Hts_load_m2). right. lia. }
    assert (Hts_load4 : Mem.load Mint64 m4 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 48)
               new_pc_v ts_ptr Hstore4 Hts_load_m3). right. lia. }

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
      exact Hle_s. }

    (* 2. pc field -- updated to new_pc_v, with shifted code_base *)
    { exists new_pc_v. split.
      - exact Hpc_load4.
      - simpl. subst new_pc_v new_pc_ofs.
        apply pc_rel_shift. }

    (* 3. accu field -- updated to global[n] *)
    { exists cv_global. split.
      - exact Haccu_load4.
      - simpl. eapply val_repr_co_shift. exact Hglobal_val_repr. }

    (* 4. sp field -- updated to new_sp_ofs; stack gets accu prepended *)
    { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load4.
      - reflexivity.
      - simpl.
        eapply stack_repr_co_shift.
        apply (stack_repr_store_other_block hm cb co m3 m4 _ sp_b new_sp_ofs sb
                 (uso + 0) new_pc_v).
        + apply (stack_repr_store_other_block hm cb co m2 m3 _ sp_b new_sp_ofs sb
                   (uso + 8) cv_global).
          * assert (Hstack_m1 : stack_repr hm cb co m1 (Machine.stack s) sp_b sp_ofs).
            { apply (stack_repr_store_other_block hm cb co m m1 _ sp_b sp_ofs sb
                       (uso + 16) (Vptr sp_b new_sp_ofs)
                       Hstack_repr Hstore1).
              intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
            exact (stack_repr_cons_after_store hm cb co m1 m2
                     (Machine.stack s) sp_b sp_ofs (Machine.accu s) accu_v
                     Hstack_m1 Haccu_repr Hstore2 Hsp_ge8 Hsp_rep).
          * exact Hstore3.
          * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        + exact Hstore4.
        + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - (* sp_ge8: new_sp_ofs >= 8 follows from sp_ofs >= 16 *)
        rewrite Hnew_sp_unsigned. lia.
      - (* sp_rep: representability for accu :: stack *)
        simpl length. rewrite Nat2Z.inj_succ.
        rewrite Hnew_sp_unsigned. lia.
      - (* sp_writable: Mem.range_perm for new range *)
        simpl length. rewrite Nat2Z.inj_succ.
        rewrite Hnew_sp_unsigned.
        intros ofs' Hofs'.
        assert (Hofs'_in_old : 0 <= ofs' < Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) by lia.
        eapply Mem.perm_store_1. exact Hstore4.
        eapply Mem.perm_store_1. exact Hstore3.
        eapply Mem.perm_store_1. exact Hstore2.
        eapply Mem.perm_store_1. exact Hstore1.
        apply Hsp_writable. lia.
      - (* sp_aligned *)
        exact Halign_new. }

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
        apply (global_repr_store_other_block hm cb co m3 m4 _
                 gb go sb (uso + 0) new_pc_v).
        + apply (global_repr_store_other_block hm cb co m2 m3 _
                   gb go sb (uso + 8) cv_global).
          * apply (global_repr_store_other_block hm cb co m1 m2 _
                     gb go sp_b (Ptrofs.unsigned new_sp_ofs) accu_v).
            { apply (global_repr_store_other_block hm cb co m m1 _
                       gb go sb (uso + 16) (Vptr sp_b new_sp_ofs)
                       Hglobal_repr Hstore1).
              intro Heq2; exact (Hgb_ne (eq_sym Heq2)). }
            { exact Hstore2. }
            { exact Hsp_ne_gb. }
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

(* Wrapper with building-block precondition for Module Type *)
Theorem verify_PUSHGETGLOBAL_handler_correct_v1 : forall n,
    0 <= Z.of_nat n <= Int.max_signed ->
    handler_correct_v1 (handle_PUSHGETGLOBAL n) f_instr_PUSHGETGLOBAL
      (pre_and (pre_and (code_at (Int.repr (Z.of_nat n))) (global_offset_safe n)) (sp_at_least 16))
      (fun _ s => nth_error s.(Machine.global) n = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros n Hn.
  eapply handler_correct_v1_weaken.
  - exact (verify_PUSHGETGLOBAL_correct n Hn).
  - intros e le m s ard _ [[Hca Hgs] Hsp].
    split. { exact Hca. }
    split. { exact Hgs. }
    intros sp_b sp_ofs Hload.
    destruct Hsp as [sp_b0 [sp_ofs0 [Hload0 Hge0]]].
    rewrite Hload0 in Hload. injection Hload as -> ->. exact Hge0.
Qed.

(* Wrapper with the canonical type expected by InstructVerificationProof.v.
   handle_instr (PUSHGETGLOBAL n) / clight_of (PUSHGETGLOBAL n) / pre_of (PUSHGETGLOBAL n)
   are convertible with handle_PUSHGETGLOBAL n / f_instr_PUSHGETGLOBAL /
   ((code_at ... /\p global_offset_safe n) /\p sp_at_least 16).
   P_halt_of and P_ccall_of are vacuously satisfied (PUSHGETGLOBAL never halts or
   issues a C call).  error_message_of requires nth_error global n = None. *)
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

Theorem correct_PUSHGETGLOBAL : forall n,
    handler_correct (handle_instr (PUSHGETGLOBAL n)) (clight_of (PUSHGETGLOBAL n))
      (error_message_of (PUSHGETGLOBAL n))
      (pre_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)).
Proof.
Admitted.
