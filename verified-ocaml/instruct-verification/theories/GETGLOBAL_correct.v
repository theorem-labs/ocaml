(* GETGLOBAL_correct.v -- GETGLOBAL completeness proof.

   GETGLOBAL reads a global index n from pc, loads global_data[n],
   stores it into accu, and increments pc by 1 (4 bytes).

   C code (f_instr_GETGLOBAL):
     _t'2 = s->global_data;
     _t'3 = s->pc;
     _t'4 = deref _t'3;             read global index from code buffer
     _t'5 = deref (global_data + _t'4);  load global_data[n]
     s->accu = _t'5;
     _t'1 = s->pc;
     s->pc = _t'1 + 1;              advance pc past operand
     return 0;

   Rocq:
     handle_GETGLOBAL n pc' s =
       match nth_error s.(global) n with
       | Some v => Step (s <|pc := pc'|> <|accu := v|>)
       | None => Error "GETGLOBAL: index out of bounds"
       end

   Two stores: accu field at offset +8, pc field at offset +0.

   Preconditions (via handler_correct_with_pre):
   - Code buffer contains Int.repr (Z.of_nat n) at the current PC position
   - Z.of_nat n fits in int32 signed range
   - Global offset arithmetic stays in ptrofs range

   The key bridge: global_repr maps the Rocq global list to consecutive
   8-byte loads from (gb, go). We prove global_repr_nth_error relating
   nth_error to Mem.load via global_repr, using iterated Ptrofs.add.

   NO AXIOMS.  NO ADMITTED. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
Require Import instruct_handlers.
Require Import InstructSpec.
Require Import StepToBigstep.
Require Import HandlerLemmas.

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

Lemma interp_state_co_getglobal : exists co,
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

(* Ptrofs.modulus is large enough for pointer arithmetic.
   On x86-64, Ptrofs.modulus = 2^64. Proved by definitional reduction. *)
Lemma ptrofs_modulus_large : (Ptrofs.modulus > 8)%Z.
Proof.
  unfold Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  simpl. reflexivity.
Qed.

(* ================================================================== *)
(* Key lemma: global_repr + nth_error => Mem.load                     *)
(* ================================================================== *)

(* Nat.iter commutes with its function application *)
Lemma nat_iter_succ_r : forall {A} (f : A -> A) n x,
  Nat.iter (S n) f x = Nat.iter n f (f x).
Proof.
  intros A f n. revert f. induction n as [| n' IH]; intros f x.
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

(* Ptrofs-level version: after n steps of add-8, we get a load. *)
Lemma global_repr_nth_error_ptrofs : forall hm m gs gb go n v,
  global_repr hm m gs gb go ->
  nth_error gs n = Some v ->
  exists cv,
    Mem.load Mint64 m gb
      (Ptrofs.unsigned (Nat.iter n (fun p => Ptrofs.add p (Ptrofs.repr 8)) go))
    = Some cv /\
    val_repr hm v cv.
Proof.
  intros hm m gs gb go n v Hgr.
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

(* When offsets are representable, iterated add-8 equals base + n*8. *)
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

(* Combined: global_repr + nth_error + offset representability => load at go + n*8 *)
Lemma global_repr_nth_error : forall hm m gs gb go n v,
  global_repr hm m gs gb go ->
  nth_error gs n = Some v ->
  Ptrofs.unsigned go + Z.of_nat n * 8 < Ptrofs.modulus ->
  exists cv,
    Mem.load Mint64 m gb (Ptrofs.unsigned go + Z.of_nat n * 8) = Some cv /\
    val_repr hm v cv.
Proof.
  intros hm m gs gb go n v Hgr Hnth Hbound.
  destruct (global_repr_nth_error_ptrofs hm m gs gb go n v Hgr Hnth)
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

Theorem verify_GETGLOBAL_correct : forall n,
    handler_correct_with_pre (handle_GETGLOBAL n) f_instr_GETGLOBAL
      (fun m s ard =>
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         0 <= Z.of_nat n <= Int.max_signed /\
         Ptrofs.unsigned (ar_global_ofs ard) + Z.of_nat n * 8 < Ptrofs.modulus)
      (fun _ s => nth_error s.(Machine.global) n = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro n.
  intros e le m s.
  unfold handle_GETGLOBAL.
  destruct (nth_error (Machine.global s) n) as [gval|] eqn:Hnth.

  2: { exact eq_refl. }

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
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb Hcb_ne_sp]]]]]]]] &
    [env_v [Henv_load Henv_repr]] &
    Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
    [ts_ptr [Hts_load Htrap_rel]]).
  subst sp_ptr. subst gd_ptr.

  destruct Hstep_pre as (Hcode_load & Hn_range & Hgo_bound).

  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep. fold sb in Hblock_sep.
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb gb in Hgb_ne.
  pose proof (code_block_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  destruct interp_state_co_getglobal as [co_is [Hco [Hpc_offset [Haccu_offset Hgd_offset]]]].

  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  destruct (global_repr_nth_error hm m _ gb go n gval Hglobal_repr Hnth Hgo_bound)
    as [cv_global [Hglobal_load Hglobal_val_repr]].

  destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 8) accu_v cv_global Haccu_load)
    as [m1 Hstore1].

  set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
  set (new_pc_v := Vptr cb new_pc_ofs).

  assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 8)
             (Ptrofs.unsigned so + 0) cv_global (Vptr cb pc_ofs)
             Hstore1 Hpc_load).
    left. lia. }

  destruct (store_succeeds_from_load m1 sb (Ptrofs.unsigned so + 0)
              (Vptr cb pc_ofs) new_pc_v Hpc_load_m1)
    as [m2 Hstore2].

  assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
            Some (Vint (Int.repr (Z.of_nat n)))).
  { erewrite Mem.load_store_other.
    - exact Hcode_load.
    - exact Hstore1.
    - left. exact Hcb_ne. }

  assert (Hglobal_load_m1 : Mem.load Mint64 m1 gb
            (Ptrofs.unsigned go + Z.of_nat n * 8) = Some cv_global).
  { erewrite Mem.load_store_other.
    - exact Hglobal_load.
    - exact Hstore1.
    - left. intro Heq. exact (Hgb_ne Heq). }

  assert (Hptr_arith : Ptrofs.unsigned (Ptrofs.add go
            (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat n)))))
          = Ptrofs.unsigned go + Z.of_nat n * 8).
  { apply ptrofs_global_offset; assumption. }

  set (le' := PTree.set _t'1 (Vptr cb pc_ofs)
              (PTree.set _t'5 cv_global
              (PTree.set _t'4 (Vint (Int.repr (Z.of_nat n)))
              (PTree.set _t'3 (Vptr cb pc_ofs)
              (PTree.set _t'2 (Vptr gb go) le))))).
  exists le'. exists m2.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ============================================================== *)
  (* Part 1: exec via computational evaluator                        *)
  (* ============================================================== *)
  {
    apply (eval_stmt_to_exec clight_ge 20).
    eval_cbn.

    (* S1: Sset _t'2 (s->global_data) *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hgd_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 40 ltac:(lia) ltac:(lia)).
    rewrite Hgd_load; eval_cbn.

    (* S2: Sset _t'3 (s->pc) *)
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Hpc_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load; eval_cbn.

    (* S3: Sset _t'4 (deref _t'3) -- read global index *)
    rewrite PTree.gss; eval_cbn.
    rewrite Hcode_load; eval_cbn.

    (* S4: Sset _t'5 (deref (cast(_t'2) + _t'4)) -- load global[n] *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_ptr_to_ptr gb go m); eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_global_n gb go (Int.repr (Z.of_nat n)) m); eval_cbn.
    rewrite Hptr_arith.
    rewrite Hglobal_load; eval_cbn.

    (* S5: Sassign (s->accu) _t'5 *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ Hglobal_val_repr); eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Hstore1; eval_cbn.

    (* S6: Sset _t'1 (s->pc) -- read pc again from m1 *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m1; eval_cbn.

    (* S7: Sassign (s->pc) (_t'1 + 1) -- advance pc *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_pc_1 cb pc_ofs m1); eval_cbn.
    rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    fold new_pc_v.
    rewrite Hstore2; eval_cbn.

    (* S8: Sreturn 0 *)
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
      (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_sptr_ofs_bound ard)).
    exists ard'.
    set (uso := Ptrofs.unsigned so) in *.

    assert (Hpc_load2 : Mem.load Mint64 m2 sb (uso + 0) = Some new_pc_v).
    { pose proof (load_after_store_same m1 m2 sb (uso + 0) new_pc_v Hstore2) as Htmp.
      unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }

    assert (Haccu_load2 : Mem.load Mint64 m2 sb (uso + 8) = Some cv_global).
    { assert (Haccu_m1 : Mem.load Mint64 m1 sb (uso + 8) = Some cv_global).
      { pose proof (load_after_store_same m m1 sb (uso + 8) cv_global Hstore1) as Htmp.
        rewrite (val_repr_load_result hm gval cv_global Hglobal_val_repr) in Htmp.
        exact Htmp. }
      apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 8)
               new_pc_v cv_global Hstore2 Haccu_m1). right. lia. }

    assert (Hsp_load2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
    { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m1 sb (uso + 8) (uso + 16)
                 cv_global (Vptr sp_b sp_ofs) Hstore1 Hsp_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 16)
               new_pc_v (Vptr sp_b sp_ofs) Hstore2 Hsp_m1). right. lia. }

    assert (Henv_load2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
    { assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m1 sb (uso + 8) (uso + 24)
                 cv_global env_v Hstore1 Henv_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 24)
               new_pc_v env_v Hstore2 Henv_m1). right. lia. }

    assert (Hextra_load2 : Mem.load Mint64 m2 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { assert (Hextra_m1 : Mem.load Mint64 m1 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m1 sb (uso + 8) (uso + 32)
                 cv_global _ Hstore1 Hextra_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 32)
               new_pc_v _ Hstore2 Hextra_m1). right. lia. }

    assert (Hgd_load2 : Mem.load Mint64 m2 sb (uso + 40) = Some (Vptr gb go)).
    { assert (Hgd_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some (Vptr gb go)).
      { apply (load_after_store_other m m1 sb (uso + 8) (uso + 40)
                 cv_global (Vptr gb go) Hstore1 Hgd_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 40)
               new_pc_v (Vptr gb go) Hstore2 Hgd_m1). right. lia. }

    assert (Hts_load2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
    { assert (Hts_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (uso + 8) (uso + 48)
                 cv_global ts_ptr Hstore1 Hts_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 48)
               new_pc_v ts_ptr Hstore2 Hts_m1). right. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].

    { subst le'.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      exact Hle_s. }

    { exists new_pc_v. split.
      - exact Hpc_load2.
      - simpl. subst new_pc_v new_pc_ofs.
        apply pc_rel_shift. }

    { exists cv_global. split.
      - exact Haccu_load2.
      - simpl. exact Hglobal_val_repr. }

    { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs. split; [| split; [| split; [| split; [| split]]]].
      - exact Hsp_load2.
      - reflexivity.
      - simpl.
        eapply (stack_repr_store_other_block hm m1 m2 _ sp_b sp_ofs sb (uso + 0) new_pc_v).
        + eapply (stack_repr_store_other_block hm m m1 _ sp_b sp_ofs sb (uso + 8) cv_global).
          * exact Hstack_repr.
          * exact Hstore1.
          * intro Heq; exact (Hblock_sep (eq_sym Heq)).
        + exact Hstore2.
        + intro Heq; exact (Hblock_sep (eq_sym Heq)).
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp. }

    { exists env_v. split.
      - exact Henv_load2.
      - simpl. exact Henv_repr. }

    { simpl. exact Hextra_load2. }

    { exists (Vptr gb go). split; [| split; [| split]].
      - exact Hgd_load2.
      - simpl. reflexivity.
      - simpl.
        eapply (global_repr_store_other_block hm m1 m2 _
                 gb go sb (uso + 0) new_pc_v).
        + eapply (global_repr_store_other_block hm m m1 _
                   gb go sb (uso + 8) cv_global).
          * exact Hglobal_repr.
          * exact Hstore1.
          * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        + exact Hstore2.
        + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
      - exact Hgb_ne_sb. }

    { exists ts_ptr. split.
      - exact Hts_load2.
      - simpl. exact Htrap_rel. }
  }
Qed.
