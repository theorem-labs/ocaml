(* ASSIGN_correct.v -- ASSIGN completeness proof.

   ASSIGN reads n from *pc, stores accu into sp[n], sets accu to val_unit,
   and increments pc by 1 (4 bytes).

   C code (from clightgen):
     _t'1 = s->pc;
     s->pc = _t'1 + 1;             // advance pc past n argument
     _t'2 = s->sp;
     _t'3 = *_t'1;                  // read n from bytecode stream
     _t'4 = s->accu;
     *(sp + n) = _t'4;             // store accu at stack[n]
     s->accu = ((0 << 1) + 1);    // val_unit = 1
     return 0;

   Rocq:
     handle_ASSIGN n pc' s =
       match set_nth (stack s) n (accu s) with
       | Some new_stack => Step (s <|pc:=pc'|> <|accu:=val_unit|> <|stack:=new_stack|>)
       | None => Error "ASSIGN: stack underflow"
       end

   Three stores: pc field at offset +0, stack at sp[n], accu field at offset +8.

   Uses handler_correct_with_pre with preconditions for:
   - Code buffer contains n at current PC
   - Code block is separate from struct block
   - Stack store at sp[n] succeeds in m1 (after pc store)
   All lemmas are proved; no axioms introduced. *)

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
(* Struct layout: _pc at offset 0, _accu at offset 8, _sp at offset 16 *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_all : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full).
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

(* sp + n for (tptr tlong) + tint: sizeof(tlong) = 8, so result = sp + 8*n *)
Lemma sem_add_sp_n : forall sp_b sp_ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint n) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs
                (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tlong))
                            (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma ptrofs_add_zero : forall ofs,
  Ptrofs.add ofs (Ptrofs.repr 0) = ofs.
Proof.
  intros. change (Ptrofs.repr 0) with Ptrofs.zero.
  apply Ptrofs.add_zero.
Qed.

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* pc_rel with shifted code base *)
Lemma pc_rel_shift : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr 4)))
         cb (Ptrofs.add co (Ptrofs.repr sizeof_code_t)) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal. rewrite Ptrofs.add_assoc. rewrite Ptrofs.add_assoc.
  f_equal. rewrite Ptrofs.add_commut. reflexivity.
Qed.

(* ================================================================== *)
(* Pointer arithmetic: sp_ofs + 8 * n as Ptrofs                       *)
(* ================================================================== *)

Lemma ptrofs_of_int_signed_nat : forall n,
  (0 <= Z.of_nat n <= Int.max_signed)%Z ->
  ptrofs_of_int Signed (Int.repr (Z.of_nat n)) = Ptrofs.repr (Z.of_nat n).
Proof.
  intros n Hrange.
  unfold ptrofs_of_int, Ptrofs.of_ints.
  f_equal.
  rewrite Int.signed_repr; [reflexivity |].
  assert (Hmin : Int.min_signed = (-2147483648)%Z) by reflexivity.
  assert (Hmax : Int.max_signed = 2147483647%Z) by reflexivity.
  lia.
Qed.

Lemma sp_offset_n_unsigned : forall sp_ofs n,
  (0 <= Z.of_nat n <= Int.max_signed)%Z ->
  Ptrofs.unsigned sp_ofs + 8 * Z.of_nat n < Ptrofs.modulus ->
  Ptrofs.unsigned
    (Ptrofs.add sp_ofs
       (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tlong))
                   (ptrofs_of_int Signed (Int.repr (Z.of_nat n)))))
  = Ptrofs.unsigned sp_ofs + 8 * Z.of_nat n.
Proof.
  intros sp_ofs n Hn_range Hfit.
  change (sizeof (genv_cenv clight_ge) tlong) with 8%Z.
  rewrite (ptrofs_of_int_signed_nat n Hn_range).
  unfold Ptrofs.add, Ptrofs.mul.
  pose proof (Ptrofs.unsigned_range sp_ofs) as [Hsp_lo Hsp_hi].
  assert (Hmu : Ptrofs.max_unsigned = Ptrofs.modulus - 1) by reflexivity.
  assert (Hmod : Ptrofs.modulus = 18446744073709551616) by reflexivity.
  assert (H8ok : 0 <= 8 <= Ptrofs.max_unsigned) by (rewrite Hmu, Hmod; lia).
  assert (Hn_ok : 0 <= Z.of_nat n <= Ptrofs.max_unsigned) by (rewrite Hmu, Hmod; lia).
  assert (H8n_ok : 0 <= 8 * Z.of_nat n <= Ptrofs.max_unsigned) by (rewrite Hmu, Hmod; lia).
  assert (Hsum_ok : 0 <= Ptrofs.unsigned sp_ofs + 8 * Z.of_nat n <= Ptrofs.max_unsigned) by (rewrite Hmu, Hmod; lia).
  rewrite (Ptrofs.unsigned_repr 8 H8ok).
  rewrite (Ptrofs.unsigned_repr (Z.of_nat n) Hn_ok).
  rewrite (Ptrofs.unsigned_repr _ H8n_ok).
  rewrite (Ptrofs.unsigned_repr _ Hsum_ok).
  lia.
Qed.

(* ================================================================== *)
(* stack_repr_update: updating element n preserves stack_repr          *)
(* ================================================================== *)

Lemma stack_repr_update : forall hm m m' stk sp_b sp_ofs n v cv new_stk,
  stack_repr hm m stk sp_b sp_ofs ->
  set_nth stk n v = Some new_stk ->
  val_repr hm v cv ->
  Mem.store Mint64 m sp_b (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat n) cv = Some m' ->
  stack_repr hm m' new_stk sp_b sp_ofs.
Proof.
  intros hm m m' stk sp_b sp_ofs n v cv new_stk. revert m m' sp_ofs n new_stk.
  induction stk as [| hd tl IH]; intros m m' sp_ofs n new_stk
    Hsr Hset Hvr Hstore.
  - (* stk = [] => set_nth fails *)
    simpl in Hset. discriminate.
  - destruct n as [| n'].
    + (* n = 0: update head *)
      simpl in Hset. injection Hset as <-.
      inversion Hsr; subst.
      econstructor.
      * (* Load the head: stored value *)
        replace (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat 0)%Z
          with (Ptrofs.unsigned sp_ofs) in Hstore by lia.
        pose proof (load_after_store_same m m' sp_b (Ptrofs.unsigned sp_ofs) cv Hstore) as Htmp.
        rewrite (val_repr_load_result hm v cv Hvr) in Htmp.
        exact Htmp.
      * exact Hvr.
      * (* Tail unchanged: store at head doesn't overlap tail *)
        replace (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat 0)%Z
          with (Ptrofs.unsigned sp_ofs) in Hstore by lia.
        eapply stack_repr_store_same_block_lower; eauto.
        pose proof (sp_ofs_stack_representable hm m (hd :: tl) sp_b sp_ofs Hsr) as Hrep.
        simpl length in Hrep.
        rewrite (ptrofs_add_unsigned sp_ofs 8
          ltac:(lia) ltac:(lia)).
        lia.
    + (* n = S n': update in tail *)
      simpl in Hset.
      destruct (set_nth tl n' v) as [tl' |] eqn:Hset_tl; [| discriminate].
      injection Hset as <-.
      inversion Hsr; subst.
      pose proof (sp_ofs_stack_representable hm m (hd :: tl) sp_b sp_ofs Hsr) as Hrep.
      simpl length in Hrep.
      assert (Hstore_ofs : Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (S n')
                         = Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat n')
        by (rewrite Nat2Z.inj_succ; lia).
      econstructor.
      * (* Head unchanged: store at sp_ofs + 8*(S n') doesn't overlap sp_ofs *)
        erewrite Mem.load_store_other; eauto.
        right. left.
        change (size_chunk Mint64) with 8%Z.
        rewrite Hstore_ofs.
        pose proof (Zle_0_nat n'). lia.
      * assumption.
      * (* Tail: apply IH *)
        assert (Htail_unsigned : Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 8)) = Ptrofs.unsigned sp_ofs + 8).
        { apply ptrofs_add_unsigned; lia. }
        eapply IH; eauto.
        rewrite Htail_unsigned.
        rewrite Hstore_ofs in Hstore.
        exact Hstore.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_ASSIGN_correct : forall n,
    handler_correct_with_pre (handle_ASSIGN n) f_instr_ASSIGN
      (fun m s ard =>
         (* Code buffer contains n at current PC *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* Code block is separate from struct block *)
         ar_code_base_block ard <> ar_sptr_block ard /\
         (* n fits in signed int32 range *)
         (0 <= Z.of_nat n <= Int.max_signed)%Z /\
         (* Stack store at sp[n] succeeds after pc store *)
         (forall m1 sp_b sp_ofs accu_v,
           stack_repr (ar_heap_map ard) m1 (Machine.stack s) sp_b sp_ofs ->
           val_repr (ar_heap_map ard) (Machine.accu s) accu_v ->
           Ptrofs.unsigned sp_ofs + 8 * Z.of_nat n < Ptrofs.modulus ->
           exists m_sw,
             Mem.store Mint64 m1 sp_b
               (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat n) accu_v = Some m_sw))
      (fun _ s => set_nth s.(Machine.stack) n s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).
Proof.
  intro n.
  intros e le m s.
  unfold handler_correct_with_pre, handle_ASSIGN.

  (* Case split on set_nth *)
  destruct (set_nth (Machine.stack s) n (Machine.accu s)) as [new_stack |] eqn:Hset.

  2: { (* Error case: set_nth returned None *) reflexivity. }

  (* Step case *)
  intros ard Hpre Hstep_pre.

  (* Unpack abs_rel_with_ard *)
  set (sb := ar_sptr_block ard) in *.
  set (so := ar_sptr_ofs ard) in *.
  set (hm := ar_heap_map ard) in *.
  set (cb := ar_code_base_block ard) in *.
  set (co := ar_code_base_ofs ard) in *.
  destruct Hpre as (Hle_s &
    [pc_ptr [Hpc_load Hpc_rel]] &
    [accu_v [Haccu_load Haccu_repr]] &
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb Hcb_ne_sp]]]]]]]] &
    [env_v [Henv_load Henv_repr]] &
    Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
    [ts_ptr [Hts_load Htrap_rel]]).
  subst sp_ptr.

  (* Unpack step precondition *)
  destruct Hstep_pre as [Hcode_load [Hcb_ne [Hn_range Hstack_store_pre]]].

  (* Structural invariants *)
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos Hso_hi].
  pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep. fold sb in Hblock_sep.
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  (* Hsp_ne_gb already from destruct *)
  pose proof (sp_ofs_stack_representable hm m (Machine.stack s) sp_b sp_ofs Hstack_repr) as Hsp_rep.

  (* n < length stack (from set_nth success) *)
  assert (Hn_lt : (n < length (Machine.stack s))%nat).
  { clear -Hset. revert n new_stack Hset.
    induction (Machine.stack s) as [| x xs IHxs]; intros k ns Hset.
    - simpl in Hset. discriminate.
    - destruct k as [| k'].
      + simpl. lia.
      + simpl in Hset.
        destruct (set_nth xs k' (Machine.accu s)) as [tl'|] eqn:Hsub; [| discriminate].
        simpl. specialize (IHxs k' tl' Hsub). lia. }

  (* Offset representability: sp_ofs + 8*n < modulus *)
  assert (Hofs_fit : Ptrofs.unsigned sp_ofs + 8 * Z.of_nat n < Ptrofs.modulus).
  { apply (proj1 (Nat2Z.inj_lt n (length (Machine.stack s)))) in Hn_lt as Hn_lt_Z. lia. }

  (* Composite environment *)
  destruct interp_state_co_all as [co_is [Hco [Hpc_offset [Haccu_offset Hsp_offset]]]].

  (* pc_ptr is a concrete Vptr *)
  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* New pc after advancement *)
  set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
  set (new_pc_v := Vptr cb new_pc_ofs).

  (* ============================================================ *)
  (* Store 1: s->pc = _t'1 + 1 (pc field at uso+0)               *)
  (* ============================================================ *)
  destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 0)
              (Vptr cb pc_ofs) new_pc_v Hpc_load)
    as [m1 Hstore_pc].

  (* After store 1: loads from m1 *)
  assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b sp_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 16) new_pc_v (Vptr sp_b sp_ofs)
             Hstore_pc Hsp_load). right. lia. }

  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) =
            Some accu_v).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 8) new_pc_v accu_v
             Hstore_pc Haccu_load). right. lia. }

  (* Code buffer survives store to sb (different block) *)
  assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
            Some (Vint (Int.repr (Z.of_nat n)))).
  { erewrite Mem.load_store_other; [exact Hcode_load | exact Hstore_pc |].
    left. exact Hcb_ne. }

  (* Stack repr survives store to sb *)
  assert (Hstack_repr_m1 : stack_repr hm m1 (Machine.stack s) sp_b sp_ofs).
  { apply (stack_repr_store_other_block hm m m1 _ sp_b sp_ofs sb
             (Ptrofs.unsigned so + 0) new_pc_v Hstack_repr Hstore_pc).
    intro Heq; exact (Hblock_sep (eq_sym Heq)). }

  (* ============================================================ *)
  (* Store 2: *(sp + n) = _t'4  (stack write at sp_b, sp_ofs+8*n) *)
  (* ============================================================ *)
  destruct (Hstack_store_pre m1 sp_b sp_ofs accu_v Hstack_repr_m1 Haccu_repr Hofs_fit)
    as [m2 Hstore_stack].

  (* Loads on sb survive store to sp_b (different block) *)
  assert (Hload_m2_sb : forall ofs v,
    Mem.load Mint64 m1 sb ofs = Some v ->
    Mem.load Mint64 m2 sb ofs = Some v).
  { intros ofs v Hload1.
    erewrite Mem.load_store_other; [exact Hload1 | exact Hstore_stack |].
    left. exact (not_eq_sym Hblock_sep). }

  assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) =
            Some accu_v).
  { apply Hload_m2_sb. exact Haccu_load_m1. }

  (* ============================================================ *)
  (* Store 3: s->accu = val_unit = ((0 << 1) + 1) = 1            *)
  (* ============================================================ *)
  set (unit_v := Vlong (Int64.repr 1)).
  destruct (store_succeeds_from_load m2 sb (Ptrofs.unsigned so + 8)
              accu_v unit_v Haccu_load_m2)
    as [m3 Hstore_accu].

  (* ============================================================ *)
  (* Witnesses for existentials                                    *)
  (* ============================================================ *)
  set (le' := PTree.set _t'4 accu_v
              (PTree.set _t'3 (Vint (Int.repr (Z.of_nat n)))
              (PTree.set _t'2 (Vptr sp_b sp_ofs)
              (PTree.set _t'1 (Vptr cb pc_ofs) le)))).

  set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
  set (ard' := mk_abs_rel
    (ar_sptr_block ard) (ar_sptr_ofs ard) (ar_heap_map ard)
    (ar_code_base_block ard) new_co
    (ar_global_block ard) (ar_global_ofs ard)
    (ar_stack_block ard) (ar_stack_base_ofs ard)
    (ar_code_ne_sptr ard) (ar_code_ne_global ard)
    (ar_sptr_ofs_bound ard)).

  exists le'. exists m3.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  (* Rewrite for the sp+n offset used in store *)
  assert (Hsp_n_unsigned :
    Ptrofs.unsigned
      (Ptrofs.add sp_ofs
         (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tlong))
                     (ptrofs_of_int Signed (Int.repr (Z.of_nat n)))))
    = Ptrofs.unsigned sp_ofs + 8 * Z.of_nat n).
  { apply sp_offset_n_unsigned; assumption. }

  split.

  (* ============================================================== *)
  (* Part 1: exec via computational evaluator                        *)
  (* ============================================================== *)
  {
    apply (eval_stmt_to_exec clight_ge 20).
    eval_cbn.

    (* Normalized hypotheses: drop +0 from pc load/store *)
    assert (Hpc_load' : Mem.load Mint64 m sb (Ptrofs.unsigned so) =
              Some (Vptr cb pc_ofs)).
    { replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0) by lia.
      exact Hpc_load. }
    assert (Hstore_pc' : Mem.store Mint64 m sb (Ptrofs.unsigned so) new_pc_v =
              Some m1).
    { replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0) by lia.
      exact Hstore_pc. }

    (* S1: Sset _t'1 (s->pc) -- read pc from struct *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hpc_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    (* After eval_cbn, set abbreviations may be expanded in goal.
       Use change to re-fold them. *)
    change (ar_sptr_ofs ard) with so.
    change (ar_sptr_block ard) with sb.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    (* Use setoid_rewrite or rewrite at specific position *)
    replace (Mem.load Mint64 m sb (Ptrofs.unsigned so + 0))
      with (Some (Vptr cb pc_ofs)) by (symmetry; exact Hpc_load).
    lazy beta iota zeta.

    (* S2: Sassign (s->pc) (_t'1 + 1) -- advance pc *)
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_pc_1 cb pc_ofs m); eval_cbn.
    change (Ptrofs.add pc_ofs (Ptrofs.repr 4)) with new_pc_ofs.
    rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    change (ar_sptr_block ard) with sb.
    change (ar_sptr_ofs ard) with so.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    fold new_pc_v.
    rewrite Hstore_pc; eval_cbn.

    (* S3: Sset _t'2 (s->sp) *)
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    change (ar_sptr_block ard) with sb.
    change (ar_sptr_ofs ard) with so.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m1; eval_cbn.

    (* S4: Sset _t'3 ( *_t'1) -- read n from code buffer *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite Hcode_load_m1; eval_cbn.

    (* S5: Sset _t'4 (s->accu) *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    change (ar_sptr_block ard) with sb.
    change (ar_sptr_ofs ard) with so.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m1; eval_cbn.

    (* S6: Sassign *(sp + n) _t'4 -- store accu at stack[n] *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_sp_n sp_b sp_ofs (Int.repr (Z.of_nat n)) m1); eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr hm _ accu_v m1 Haccu_repr); eval_cbn.
    change (Ptrofs.repr 8) with (Ptrofs.repr (sizeof ge tlong)); rewrite Hsp_n_unsigned.
    rewrite Hstore_stack; eval_cbn.

    (* S7: Sassign (s->accu) ((0 << 1) + 1) = 1 *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    change (ar_sptr_block ard) with sb.
    change (ar_sptr_ofs ard) with so.
    rewrite (sem_cast_int_to_long_0 m2); eval_cbn.
    rewrite (sem_shl_long_0_1 m2); eval_cbn.
    rewrite (sem_add_long_int_0_1 m2); eval_cbn.
    rewrite (sem_cast_long_vlong (Int64.repr 1)); eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    fold unit_v.
    rewrite Hstore_accu; eval_cbn.

    (* S8: Sreturn 0 *)
    subst le'. reflexivity.
  }

  (* ============================================================== *)
  (* Part 2: abs_rel for post-state                                  *)
  (* ============================================================== *)
  {
    exists ard'.
    set (uso := Ptrofs.unsigned so) in *.

    (* pc field at uso+0: written by store_pc, survives other stores *)
    assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some new_pc_v).
    { pose proof (load_after_store_same m m1 sb (uso + 0) new_pc_v Hstore_pc) as Htmp.
      subst new_pc_v new_pc_ofs. rewrite load_result_vptr in Htmp. exact Htmp. }
    assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (uso + 0) = Some new_pc_v).
    { apply Hload_m2_sb. exact Hpc_load_m1. }
    assert (Hpc_load3 : Mem.load Mint64 m3 sb (uso + 0) = Some new_pc_v).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 0)
               unit_v new_pc_v Hstore_accu Hpc_load_m2). left. lia. }

    (* accu field at uso+8: written by store_accu (m2->m3) *)
    assert (Haccu_load3 : Mem.load Mint64 m3 sb (uso + 8) = Some unit_v).
    { pose proof (load_after_store_same m2 m3 sb (uso + 8) unit_v Hstore_accu) as Htmp.
      subst unit_v. rewrite load_result_vlong in Htmp. exact Htmp. }

    (* sp field at uso+16: unaffected by all stores *)
    assert (Hsp_load3 : Mem.load Mint64 m3 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 16)
               unit_v (Vptr sp_b sp_ofs) Hstore_accu).
      apply Hload_m2_sb. exact Hsp_load_m1.
      right. lia. }

    (* env field at uso+24 *)
    assert (Henv_load_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m m1 sb (uso + 0) (uso + 24)
               new_pc_v env_v Hstore_pc Henv_load). right. lia. }
    assert (Henv_load3 : Mem.load Mint64 m3 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 24)
               unit_v env_v Hstore_accu).
      apply Hload_m2_sb. exact Henv_load_m1. right. lia. }

    (* extra_args field at uso+32 *)
    assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m m1 sb (uso + 0) (uso + 32)
               new_pc_v _ Hstore_pc Hextra_load). right. lia. }
    assert (Hextra_load3 : Mem.load Mint64 m3 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 32)
               unit_v _ Hstore_accu).
      apply Hload_m2_sb. exact Hextra_load_m1. right. lia. }

    (* global_data field at uso+40 *)
    assert (Hgd_load_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
    { apply (load_after_store_other m m1 sb (uso + 0) (uso + 40)
               new_pc_v gd_ptr Hstore_pc Hgd_load). right. lia. }
    assert (Hgd_load3 : Mem.load Mint64 m3 sb (uso + 40) = Some gd_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 40)
               unit_v gd_ptr Hstore_accu).
      apply Hload_m2_sb. exact Hgd_load_m1. right. lia. }

    (* trap_sp field at uso+48 *)
    assert (Hts_load_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m m1 sb (uso + 0) (uso + 48)
               new_pc_v ts_ptr Hstore_pc Hts_load). right. lia. }
    assert (Hts_load3 : Mem.load Mint64 m3 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 48)
               unit_v ts_ptr Hstore_accu).
      apply Hload_m2_sb. exact Hts_load_m1. right. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].

    (* 1. _s is in le' *)
    { subst le'.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      exact Hle_s. }

    (* 2. pc field *)
    { exists new_pc_v. split.
      - exact Hpc_load3.
      - simpl. subst new_pc_v new_pc_ofs.
        apply pc_rel_shift. }

    (* 3. accu field -- updated to val_unit = Val_int 0 *)
    { exists unit_v. split.
      - exact Haccu_load3.
      - simpl. subst unit_v. exact (vr_int _ 0). }

    (* 4. sp field -- same pointer, but stack_repr for new_stack *)
    { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
      split; [| split; [| split; [| split; [| split]]]].
      - exact Hsp_load3.
      - reflexivity.
      - simpl.
        apply (stack_repr_store_other_block (ar_heap_map ard) m2 m3 _ sp_b sp_ofs sb
                 (uso + 8) unit_v).
        + eapply (stack_repr_update (ar_heap_map ard) m1 m2 (Machine.stack s) sp_b sp_ofs n
                    (Machine.accu s) accu_v new_stack).
          * exact Hstack_repr_m1.
          * exact Hset.
          * exact Haccu_repr.
          * exact Hstore_stack.
        + exact Hstore_accu.
        + intro Heq; exact (Hblock_sep (eq_sym Heq)).
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp. }

    (* 5. env field *)
    { exists env_v. split.
      - exact Henv_load3.
      - simpl. exact Henv_repr. }

    (* 6. extra_args field *)
    { simpl. exact Hextra_load3. }

    (* 7. global_data field *)
    { exists gd_ptr. split; [| split; [| split]].
      - exact Hgd_load3.
      - simpl. exact Hgd_eq.
      - simpl.
        apply (global_repr_store_other_block (ar_heap_map ard) m2 m3 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (uso + 8) unit_v).
        + apply (global_repr_store_other_block (ar_heap_map ard) m1 m2 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sp_b (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat n) accu_v).
          * apply (global_repr_store_other_block (ar_heap_map ard) m m1 _
                     (ar_global_block ard) (ar_global_ofs ard)
                     sb (uso + 0) new_pc_v
                     Hglobal_repr Hstore_pc).
            intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          * exact Hstore_stack.
          * exact Hsp_ne_gb.
        + exact Hstore_accu.
        + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field *)
    { exists ts_ptr. split.
      - exact Hts_load3.
      - simpl. exact Htrap_rel. }
  }
Qed.
