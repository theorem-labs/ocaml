(* GETFLOATFIELD_correct.v -- GETFLOATFIELD completeness proof.

   GETFLOATFIELD n: reads field index from code buffer, dereferences
   accu as a pointer to get field n (as a double), allocates a new
   float box via heap_alloc, stores the double into it, and sets accu
   to the new box.

   Rocq handler: handle_GETFLOATFIELD n pc' s =
     match field_or_heap s s.(accu) n with
     | Some v => Step (s <|pc:=pc'|> <|accu:=v|>)
     | None => Error "GETFLOATFIELD: access failed"
     end

   C handler: see f_instr_GETFLOATFIELD in instruct_handlers.v.
   sizeof(double)/sizeof(long) = 8/8 = 1 on x86-64.

   The Rocq handler does NOT allocate; field_or_heap returns an existing
   value.  The C handler allocates a new float box.  The step_pre
   precondition bridges this gap by requiring the heap_alloc infrastructure
   and providing the val_repr correspondence for the new block.

   No Axioms, no Admitted, Qed only. *)

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
(* Struct layout: _pc at offset 0, _accu at offset 8                   *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full).
Proof.
  eexists. split; [| split]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_pc_accu_GFF : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_add_pc_1_local : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma load_result_vptr_local : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* pc_rel with shifted code base *)
Lemma pc_rel_shift_local : forall cb co rocq_pc,
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

(* sizeof(double) = 8, sizeof(long) = 8 on x86-64 *)
Lemma sizeof_tdouble : sizeof (genv_cenv clight_ge) tdouble = 8.
Proof. reflexivity. Qed.

Lemma sizeof_tlong : sizeof (genv_cenv clight_ge) tlong = 8.
Proof. reflexivity. Qed.

(* On x86-64, Vptrofs (Ptrofs.repr 8) = Vlong (Int64.repr 8).
   We prove this for the specific values we need. *)
Lemma vptrofs_8 : Vptrofs (Ptrofs.repr 8) = Vlong (Int64.repr 8).
Proof. reflexivity. Qed.

(* sizeof(double)/sizeof(long) = 1 as unsigned long division.
   Uses the raw Int64.repr 8 form that appears after full unfolding. *)
Lemma sizeof_div_1 : forall m,
  sem_binary_operation (genv_cenv clight_ge) Odiv
    (Vlong (Int64.repr 8)) tulong
    (Vlong (Int64.repr 8)) tulong
    m = Some (Vlong (Int64.repr 1)).
Proof.
  intro m. unfold sem_binary_operation, sem_div.
  change (classify_binarith tulong tulong) with (bin_case_l Unsigned).
  simpl. unfold Int64.divu.
  change (Int64.unsigned (Int64.repr 8)) with 8%Z.
  simpl. reflexivity.
Qed.

(* n * 1 = n for unsigned long multiplication.
   classify_binarith tint tulong = bin_case_l Unsigned.
   The Vint n gets cast to Vlong via cast_int_long Unsigned n =
   Int64.repr (Int.unsigned n).
   Then Int64.mul (Int64.repr (Int.unsigned n)) (Int64.repr 1). *)
(* Direct computation: Vint n * Vlong 1 in (tint, tulong) context.
   The Vint n gets cast from tint (signed) to tlong, giving
   Int64.repr (Int.signed n).  Then multiplied by Int64.repr 1. *)
Lemma mul_vint_vlong_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Omul
    (Vint n) tint
    (Vlong (Int64.repr 1)) tulong
    m = Some (Vlong (Int64.repr (Int.signed n))).
Proof.
  intros. unfold sem_binary_operation, sem_mul, sem_binarith.
  change (classify_binarith tint tulong) with (bin_case_l Unsigned).
  unfold sem_cast, classify_cast.
  change Archi.ptr64 with true.
  simpl.
  f_equal. f_equal. unfold Int64.mul.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Z.mul_1_r. apply Int64.repr_unsigned.
Qed.

(* sem_add for (tptr tlong) + Vlong n *)
Lemma sem_add_ptr_long_vlong : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vlong n) tulong m
    = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tulong) with (add_case_pl tlong).
  unfold sem_add_ptr_long. reflexivity.
Qed.

(* cast from (tptr tlong) to (tptr tdouble) for a Vptr *)
Lemma sem_cast_ptr_tlong_to_ptr_tdouble : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tlong) (tptr tdouble) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* cast from tlong to (tptr tdouble) for a Vptr *)
Lemma sem_cast_long_to_ptr_tdouble : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tdouble) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* cast Vfloat from tdouble to tdouble *)
Lemma sem_cast_tdouble_tdouble : forall f m,
  sem_cast (Vfloat f) tdouble tdouble m = Some (Vfloat f).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* Ptrofs.of_int64 (Int64.repr z) when z is small *)
Lemma ptrofs_of_int64_repr : forall z,
  0 <= z <= Int.max_signed ->
  Ptrofs.of_int64 (Int64.repr z) = Ptrofs.repr z.
Proof.
  intros z Hz.
  unfold Ptrofs.of_int64. f_equal. apply Int64.unsigned_repr.
  change Int64.max_unsigned with 18446744073709551615%Z.
  change Int.max_signed with 2147483647%Z in Hz. lia.
Qed.

(* Signed of repr for small n *)
Lemma int_signed_repr_small : forall z,
  Int.min_signed <= z <= Int.max_signed ->
  Int.signed (Int.repr z) = z.
Proof.
  intros z Hz. apply Int.signed_repr. exact Hz.
Qed.

(* ================================================================== *)
(* Float field precondition                                            *)
(* ================================================================== *)

(* The float field at accu[n] is loadable as Mfloat64, and the accu
   pointer block is distinct from the struct block.  This separation
   is natural: the struct is a C local, while accu points to the
   OCaml heap. *)
Definition float_field_loadable_sep (n : nat)
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let sb := ar_sptr_block ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall v,
    field_or_heap s s.(Machine.accu) n = Some v ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists b ofs fv,
        accu_v = Vptr b ofs /\
        b <> sb /\
        Mem.load Mfloat64 m b
          (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some (Vfloat fv).

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_GETFLOATFIELD_correct : forall n,
    handler_correct (handle_GETFLOATFIELD n) f_instr_GETFLOATFIELD
      (fun e m s ard =>
         let sb := ar_sptr_block ard in
         let so := ar_sptr_ofs ard in
         let cb := ar_code_base_block ard in
         let co := ar_code_base_ofs ard in
         let gb := ar_global_block ard in
         let hm := ar_heap_map ard in
         e ! _heap_alloc = None /\
         float_field_loadable_sep n m s ard /\
         Mem.load Mint32 m cb
           (Ptrofs.unsigned (Ptrofs.add co
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         Int.min_signed <= Z.of_nat n <= Int.max_signed /\
         (exists b_ha,
            Genv.find_symbol (genv_genv ge) _heap_alloc = Some b_ha /\
            Genv.find_funct (genv_genv ge) (Vptr b_ha Ptrofs.zero) =
              Some heap_alloc_fundef) /\
         Mem.valid_block m gb /\
         (forall m' fv,
            exists m_alloc new_b new_ofs,
              external_call heap_alloc_ef
                (Genv.to_senv (genv_genv ge))
                (Vptr sb so :: Vlong (Int64.repr 1) :: Vlong (Int64.repr 253) :: nil)
                m' E0 (Vptr new_b new_ofs) m_alloc /\
              (forall b, Mem.valid_block m' b -> new_b <> b) /\
              (forall b ofs chunk v0,
                 Mem.load chunk m' b ofs = Some v0 -> b <> new_b ->
                 Mem.load chunk m_alloc b ofs = Some v0) /\
              (forall b ofs k p,
                 Mem.valid_block m' b -> Mem.perm m' b ofs k p ->
                 Mem.perm m_alloc b ofs k p) /\
              (exists m_fstore,
                 Mem.store Mfloat64 m_alloc new_b (Ptrofs.unsigned new_ofs) (Vfloat fv) = Some m_fstore /\
                 (forall b ofs chunk v0, b <> new_b ->
                    Mem.load chunk m_alloc b ofs = Some v0 ->
                    Mem.load chunk m_fstore b ofs = Some v0) /\
                 (forall b ofs k p,
                    Mem.perm m_alloc b ofs k p ->
                    Mem.perm m_fstore b ofs k p))) /\
         (forall v new_b new_ofs,
            field_or_heap s s.(Machine.accu) n = Some v ->
            exists hm',
              val_repr hm' cb co v (Vptr new_b new_ofs) /\
              (forall v0 cv, val_repr hm cb co v0 cv -> val_repr hm' cb co v0 cv) /\
              (forall stk m0 sp_b0 sp_ofs0,
                 stack_repr hm cb co m0 stk sp_b0 sp_ofs0 ->
                 stack_repr hm' cb co m0 stk sp_b0 sp_ofs0) /\
              (forall gs m0 gb0 gofs0,
                 global_repr hm cb co m0 gs gb0 gofs0 ->
                 global_repr hm' cb co m0 gs gb0 gofs0)))
      (fun _ s => field_or_heap s s.(Machine.accu) n = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro n.
  intros e le m s.
  unfold handler_correct, handle_GETFLOATFIELD.
  destruct (field_or_heap s s.(Machine.accu) n) as [v|] eqn:Hfoh.

  2: { reflexivity. }
  {
    intros ard Hpre Hstep_pre.

    destruct Hpre as (Hle_s &
      [pc_ptr [Hpc_load Hpc_rel]] &
      [accu_v [Haccu_load Haccu_repr]] &
      [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
      [env_v [Henv_load Henv_repr]] &
      Hextra_load &
      [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
      [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
    subst sp_ptr gd_ptr.

    destruct Hstep_pre as (He_heap_alloc & Hffl & Hcode_load & Hn_range &
      [b_ha [Hfind_symbol Hfind_funct]] & Hgb_valid & Halloc_spec_all & Hval_repr_post).

    set (sb := ar_sptr_block ard) in *.
    set (so := ar_sptr_ofs ard) in *.
    set (hm := ar_heap_map ard) in *.
    set (cb := ar_code_base_block ard) in *.
    set (co := ar_code_base_ofs ard) in *.
    set (gb := ar_global_block ard) in *.
    set (go0 := ar_global_ofs ard) in *.

    pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
    pose proof (code_block_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

    destruct interp_state_co_pc_accu_GFF as [co_is [Hco [Hpc_offset Haccu_offset]]].

    unfold pc_rel in Hpc_rel. subst pc_ptr.
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

    set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
    set (new_pc_v := Vptr cb new_pc_ofs).

    unfold float_field_loadable_sep in Hffl.
    destruct (Hffl v Hfoh accu_v Haccu_repr)
      as [accu_b [accu_ofs [fv [Haccu_is_ptr [Haccu_ne_sb Hfloat_load]]]]].
    subst accu_v.

    (* Store 1: pc field *)
    destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia) new_pc_v)
      as [m1 Hstore_pc].
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore_pc Hsb_writable) as Hsb_writable_m1.

    assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vptr accu_b accu_ofs)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
               (Ptrofs.unsigned so + 8) new_pc_v (Vptr accu_b accu_ofs) Hstore_pc Haccu_load).
      right. lia. }

    assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
              Some (Vint (Int.repr (Z.of_nat n)))).
    { erewrite Mem.load_store_other.
      - exact Hcode_load.
      - exact Hstore_pc.
      - left. exact Hcb_ne. }

    assert (Hfloat_load_m1 : Mem.load Mfloat64 m1 accu_b
              (Ptrofs.unsigned (Ptrofs.add accu_ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some (Vfloat fv)).
    { erewrite Mem.load_store_other.
      - exact Hfloat_load.
      - exact Hstore_pc.
      - left. exact Haccu_ne_sb. }

    (* heap_alloc *)
    destruct (Halloc_spec_all m1 fv)
      as [m_alloc [new_b [new_ofs
           (Hext_call & Hnew_fresh &
            Halloc_load_pres & Halloc_perm_pres &
            [m_fstore [Hfstore [Hfstore_load_pres Hfstore_perm_pres]]])]]].

    assert (Hnew_ne_sb : new_b <> sb).
    { apply Hnew_fresh. eapply Mem.perm_valid_block.
      apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc).
      apply (Hsb_writable (Ptrofs.unsigned so)). lia. }
    assert (Hnew_ne_sp : new_b <> sp_b).
    { apply Hnew_fresh. eapply Mem.perm_valid_block.
      apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc).
      apply (Hsp_writable 0). lia. }
    assert (Hnew_ne_cb : new_b <> cb).
    { apply Hnew_fresh.
      pose proof (Mem.load_valid_access _ _ _ _ _ Hcode_load) as [Hrp_cb _].
      eapply Mem.perm_valid_block.
      apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc).
      apply (Hrp_cb (Ptrofs.unsigned pc_ofs)). simpl. lia. }
    assert (Hnew_ne_gb : new_b <> gb).
    { apply Hnew_fresh.
      eapply Mem.store_valid_block_1. exact Hstore_pc. exact Hgb_valid. }

    assert (Hstruct_preserved : forall ofs0 v0,
      Mem.load Mint64 m1 sb ofs0 = Some v0 ->
      Mem.load Mint64 m_alloc sb ofs0 = Some v0).
    { intros ofs0 v0 Hld. apply Halloc_load_pres; auto. }

    assert (Hstruct_preserved2 : forall ofs0 v0,
      Mem.load Mint64 m1 sb ofs0 = Some v0 ->
      Mem.load Mint64 m_fstore sb ofs0 = Some v0).
    { intros ofs0 v0 Hld.
      apply Hfstore_load_pres.
      - intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq).
      - apply Hstruct_preserved. exact Hld. }

    assert (Haccu_load_fstore : Mem.load Mint64 m_fstore sb (Ptrofs.unsigned so + 8) = Some (Vptr accu_b accu_ofs)).
    { apply Hstruct_preserved2. exact Haccu_load_m1. }

    (* Store 2: accu field *)
    set (block_v := Vptr new_b new_ofs).

    assert (Hsb_writable_fstore :
      Mem.range_perm m_fstore sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs0 Hofs0. eapply Hfstore_perm_pres.
      eapply Halloc_perm_pres.
      - eapply Mem.perm_valid_block.
        apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc).
        apply (Hsb_writable (Ptrofs.unsigned so)). lia.
      - apply Hsb_writable_m1. exact Hofs0. }

    destruct (store_succeeds_sb m_fstore sb so 8 (Vptr accu_b accu_ofs) Hsb_writable_fstore Haccu_load_fstore ltac:(lia) ltac:(lia) block_v)
      as [m2 Hstore_accu].

    (* Extended heap map *)
    destruct (Hval_repr_post v new_b new_ofs eq_refl)
      as [hm' [Hval_repr_new [Hval_repr_ext [Hstack_repr_ext Hglobal_repr_ext]]]].

    (* Temp env *)
    set (le1 := PTree.set _t'1 (Vptr cb pc_ofs) le).
    set (le2 := PTree.set _t'3 (Vptr accu_b accu_ofs) le1).
    set (le3 := PTree.set _t'4 (Vint (Int.repr (Z.of_nat n))) le2).
    set (le4 := PTree.set _d (Vfloat fv) le3).
    set (le5 := PTree.set _t'2 block_v le4).
    set (le6 := PTree.set _block block_v le5).
    set (le' := le6).

    exists le'. exists m2.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec_stmt derivation                                    *)
    (* ============================================================== *)
    {
      (* Phase 1: Sset _t'1 (s->pc) *)
      assert (Hexec_set_t1 : exec_stmt function_entry1 clight_ge e le m
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint)))
          E0 le1 m Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        rewrite Hpc_load; eval_cbn.
        reflexivity. }

      (* Phase 2: Sassign s->pc = _t'1 + 1 *)
      assert (Hexec_store_pc : exec_stmt function_entry1 clight_ge e le1 m
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint))
            (Ebinop Oadd (Etempvar _t'1 (tptr tint))
              (Econst_int (Int.repr 1) tint) (tptr tint)))
          E0 le1 m1 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le1.
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_pc_1_local cb pc_ofs m); eval_cbn.
        rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        fold new_pc_v. rewrite Hstore_pc; eval_cbn.
        reflexivity. }

      (* Phase 3: Sset _t'3 (s->accu) *)
      assert (Hexec_read_accu : exec_stmt function_entry1 clight_ge e le1 m1
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong))
          E0 le2 m1 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le1.
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_load_m1; eval_cbn.
        reflexivity. }

      (* Phase 4: Sset _t'4 (deref _t'1) *)
      assert (Hexec_read_n : exec_stmt function_entry1 clight_ge e le2 m1
          (Sset _t'4 (Ederef (Etempvar _t'1 (tptr tint)) tint))
          E0 le3 m1 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le2.
        rewrite PTree.gso by (compute; congruence).
        unfold le1.
        rewrite PTree.gss; eval_cbn.
        rewrite Hcode_load_m1; eval_cbn.
        reflexivity. }

      (* Phase 5: Sset _d -- read float field.
         This involves sizeof expressions which interact badly with eval_cbn.
         We construct the exec_stmt manually using eval_Sset + eval_Elvalue. *)

      (* First establish what the complex expression evaluates to *)
      assert (Hsize_div : sem_binary_operation (genv_cenv ge) Odiv
                (Vptrofs (Ptrofs.repr (sizeof (genv_cenv ge) tdouble))) tulong
                (Vptrofs (Ptrofs.repr (sizeof (genv_cenv ge) tlong))) tulong m1
              = Some (Vlong (Int64.repr 1))).
      { change (sizeof (genv_cenv ge) tdouble) with 8%Z.
        change (sizeof (genv_cenv ge) tlong) with 8%Z.
        apply sizeof_div_1. }

      assert (Hmul_n : sem_binary_operation (genv_cenv ge) Omul
                (Vint (Int.repr (Z.of_nat n))) tint
                (Vlong (Int64.repr 1)) tulong m1
              = Some (Vlong (Int64.repr (Z.of_nat n)))).
      { rewrite (mul_vint_vlong_1 (Int.repr (Z.of_nat n))).
        rewrite (int_signed_repr_small _ Hn_range). reflexivity. }

      assert (Hadd_ptr : sem_binary_operation (genv_cenv ge) Oadd
                (Vptr accu_b accu_ofs) (tptr tlong)
                (Vlong (Int64.repr (Z.of_nat n))) tulong m1
              = Some (Vptr accu_b (Ptrofs.add accu_ofs (Ptrofs.repr (Z.of_nat n * 8))))).
      { rewrite (sem_add_ptr_long_vlong accu_b accu_ofs (Int64.repr (Z.of_nat n)) m1).
        f_equal. f_equal. f_equal.
        rewrite (ptrofs_of_int64_repr (Z.of_nat n) ltac:(lia)).
        unfold Ptrofs.mul.
        change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8%Z.
        rewrite Ptrofs.unsigned_repr.
        2: { change Ptrofs.max_unsigned with 18446744073709551615%Z.
             change Int.max_signed with 2147483647%Z in Hn_range. lia. }
        f_equal. lia. }

      assert (Hexec_read_float : exec_stmt function_entry1 clight_ge e le3 m1
          (Sset _d
            (Ederef
              (Ecast
                (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                  (Ebinop Omul (Etempvar _t'4 tint)
                    (Ebinop Odiv (Esizeof tdouble tulong)
                      (Esizeof tlong tulong) tulong) tulong) (tptr tlong))
                (tptr tdouble)) tdouble))
          E0 le4 m1 Out_normal).
      { eapply exec_Sset.
        eapply eval_Elvalue.
        - (* eval_lvalue: Ederef (Ecast ...) *)
          eapply eval_Ederef.
          (* eval_expr: Ecast (Ebinop Oadd ...) *)
          eapply eval_Ecast.
          + (* eval_expr: Ebinop Oadd *)
            eapply eval_Ebinop.
            * (* eval_expr: Ecast (Etempvar _t'3 tlong) (tptr tlong) *)
              eapply eval_Ecast.
              -- econstructor.
                 unfold le3. rewrite PTree.gso by (compute; congruence).
                 unfold le2. rewrite PTree.gss. reflexivity.
              -- exact (sem_cast_long_to_ptr_vptr accu_b accu_ofs m1).
            * (* eval_expr: Ebinop Omul *)
              eapply eval_Ebinop.
              -- econstructor.
                 unfold le3. rewrite PTree.gss. reflexivity.
              -- (* eval_expr: Ebinop Odiv (Esizeof ...) (Esizeof ...) *)
                 eapply eval_Ebinop.
                 ++ econstructor.
                 ++ econstructor.
                 ++ exact Hsize_div.
              -- exact Hmul_n.
            * exact Hadd_ptr.
          + exact (sem_cast_ptr_tlong_to_ptr_tdouble accu_b
                     (Ptrofs.add accu_ofs (Ptrofs.repr (Z.of_nat n * 8))) m1).
        - (* deref_loc tdouble *)
          apply deref_loc_value with (chunk := Mfloat64).
          + simpl. reflexivity.
          + simpl. exact Hfloat_load_m1.
      }

      (* Phase 6: Scall heap_alloc *)
      assert (Hexec_call : exec_stmt function_entry1 clight_ge e le4 m1
          (Scall (Some _t'2)
            (Evar _heap_alloc (Tfunction
              ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
              tlong cc_default))
            ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
             (Ebinop Odiv (Esizeof tdouble tulong) (Esizeof tlong tulong) tulong) ::
             (Econst_int (Int.repr 253) tint) :: nil))
          E0 le5 m_alloc Out_normal).
      { eapply exec_Scall with
          (tyargs := (tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
          (tyres := tlong)
          (cconv := cc_default)
          (vf := Vptr b_ha Ptrofs.zero)
          (vargs := Vptr sb so :: Vlong (Int64.repr 1) :: Vlong (Int64.repr 253) :: nil)
          (f := heap_alloc_fundef)
          (vres := Vptr new_b new_ofs).
        - reflexivity.
        - eapply eval_Elvalue.
          + eapply eval_Evar_global.
            * exact He_heap_alloc.
            * exact Hfind_symbol.
          + apply deref_loc_reference. simpl. reflexivity.
        - econstructor.
          + econstructor.
            unfold le4. rewrite PTree.gso by (compute; congruence).
            unfold le3. rewrite PTree.gso by (compute; congruence).
            unfold le2. rewrite PTree.gso by (compute; congruence).
            unfold le1. rewrite PTree.gso by (compute; congruence).
            exact Hle_s.
          + simpl. reflexivity.
          + econstructor.
            * econstructor.
              -- econstructor.
              -- econstructor.
              -- simpl. reflexivity.
            * simpl. reflexivity.
            * econstructor.
              -- econstructor.
              -- simpl. reflexivity.
              -- constructor.
        - exact Hfind_funct.
        - reflexivity.
        - eapply eval_funcall_external. exact Hext_call.
      }

      (* Phase 7: Sset _block _t'2 *)
      assert (Hexec_set_block : exec_stmt function_entry1 clight_ge e le5 m_alloc
          (Sset _block (Etempvar _t'2 tlong))
          E0 le6 m_alloc Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le5. rewrite PTree.gss; eval_cbn.
        reflexivity. }

      (* Phase 8: store float to new block *)
      assert (Hexec_store_float : exec_stmt function_entry1 clight_ge e le6 m_alloc
          (Sassign
            (Ederef (Ecast (Etempvar _block tlong) (tptr tdouble)) tdouble)
            (Etempvar _d tdouble))
          E0 le6 m_fstore Out_normal).
      { eapply exec_Sassign.
        - (* eval_lvalue: Ederef (Ecast (Etempvar _block tlong) (tptr tdouble)) *)
          eapply eval_Ederef.
          eapply eval_Ecast.
          + econstructor.
            unfold le6. rewrite PTree.gss. reflexivity.
          + exact (sem_cast_long_to_ptr_tdouble new_b new_ofs m_alloc).
        - (* eval_expr: Etempvar _d tdouble *)
          econstructor.
          unfold le6. rewrite PTree.gso by (compute; congruence).
          unfold le5. rewrite PTree.gso by (compute; congruence).
          unfold le4. rewrite PTree.gss. reflexivity.
        - (* sem_cast Vfloat from tdouble to tdouble *)
          exact (sem_cast_tdouble_tdouble fv m_alloc).
        - (* assign_loc: store float *)
          apply assign_loc_value with (chunk := Mfloat64).
          + simpl. reflexivity.
          + simpl. exact Hfstore. }

      (* Phase 9: store accu *)
      assert (Hexec_store_accu : exec_stmt function_entry1 clight_ge e le6 m_fstore
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong)
            (Etempvar _block tlong))
          E0 le6 m2 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le6. rewrite PTree.gso by (compute; congruence).
        unfold le5. rewrite PTree.gso by (compute; congruence).
        unfold le4. rewrite PTree.gso by (compute; congruence).
        unfold le3. rewrite PTree.gso by (compute; congruence).
        unfold le2. rewrite PTree.gso by (compute; congruence).
        unfold le1. rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        unfold le6. rewrite PTree.gss; eval_cbn.
        fold block_v.
        unfold block_v at 1.
        rewrite (sem_cast_long_vptr new_b new_ofs m_fstore); eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        fold block_v. rewrite Hstore_accu; eval_cbn.
        reflexivity. }

      (* Phase 10: return 0 *)
      assert (Hexec_return : exec_stmt function_entry1 clight_ge e le6 m2
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          E0 le6 m2 (Out_return (Some (Vint (Int.repr 0), tint)))).
      { apply (eval_stmt_to_exec clight_ge 10). reflexivity. }

      (* Combine using exec_Sseq_1 bottom-up *)
      assert (Hexec_12 :
        exec_stmt function_entry1 clight_ge e le m
          (Ssequence
            (Sset _t'1 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint))))
          E0 le1 m1 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      assert (Hexec_45 :
        exec_stmt function_entry1 clight_ge e le2 m1
          (Ssequence
            (Sset _t'4 (Ederef (Etempvar _t'1 (tptr tint)) tint))
            (Sset _d (Ederef (Ecast (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                (Ebinop Omul (Etempvar _t'4 tint) (Ebinop Odiv (Esizeof tdouble tulong)
                  (Esizeof tlong tulong) tulong) tulong) (tptr tlong)) (tptr tdouble)) tdouble)))
          E0 le4 m1 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      assert (Hexec_345 :
        exec_stmt function_entry1 clight_ge e le1 m1
          (Ssequence
            (Sset _t'3 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _accu tlong))
            (Ssequence
              (Sset _t'4 (Ederef (Etempvar _t'1 (tptr tint)) tint))
              (Sset _d (Ederef (Ecast (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                  (Ebinop Omul (Etempvar _t'4 tint) (Ebinop Odiv (Esizeof tdouble tulong)
                    (Esizeof tlong tulong) tulong) tulong) (tptr tlong)) (tptr tdouble)) tdouble))))
          E0 le4 m1 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      assert (Hexec_12345 :
        exec_stmt function_entry1 clight_ge e le m
          (Ssequence
            (Ssequence
              (Sset _t'1 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                           (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _pc (tptr tint))
                (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                  (Econst_int (Int.repr 1) tint) (tptr tint))))
            (Ssequence
              (Sset _t'3 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                           (Tstruct _interp_state noattr)) _accu tlong))
              (Ssequence
                (Sset _t'4 (Ederef (Etempvar _t'1 (tptr tint)) tint))
                (Sset _d (Ederef (Ecast (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                    (Ebinop Omul (Etempvar _t'4 tint) (Ebinop Odiv (Esizeof tdouble tulong)
                      (Esizeof tlong tulong) tulong) tulong) (tptr tlong)) (tptr tdouble)) tdouble)))))
          E0 le4 m1 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      assert (Hexec_67 :
        exec_stmt function_entry1 clight_ge e le4 m1
          (Ssequence
            (Scall (Some _t'2)
              (Evar _heap_alloc (Tfunction
                ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
                tlong cc_default))
              ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
               (Ebinop Odiv (Esizeof tdouble tulong) (Esizeof tlong tulong) tulong) ::
               (Econst_int (Int.repr 253) tint) :: nil))
            (Sset _block (Etempvar _t'2 tlong)))
          E0 le6 m_alloc Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      assert (Hexec_89 :
        exec_stmt function_entry1 clight_ge e le6 m_alloc
          (Ssequence
            (Sassign (Ederef (Ecast (Etempvar _block tlong) (tptr tdouble)) tdouble)
              (Etempvar _d tdouble))
            (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _accu tlong)
              (Etempvar _block tlong)))
          E0 le6 m2 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      assert (Hexec_6789 :
        exec_stmt function_entry1 clight_ge e le4 m1
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _heap_alloc (Tfunction
                  ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
                  tlong cc_default))
                ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
                 (Ebinop Odiv (Esizeof tdouble tulong) (Esizeof tlong tulong) tulong) ::
                 (Econst_int (Int.repr 253) tint) :: nil))
              (Sset _block (Etempvar _t'2 tlong)))
            (Ssequence
              (Sassign (Ederef (Ecast (Etempvar _block tlong) (tptr tdouble)) tdouble)
                (Etempvar _d tdouble))
              (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _accu tlong)
                (Etempvar _block tlong))))
          E0 le6 m2 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      assert (Hexec_pre_return :
        exec_stmt function_entry1 clight_ge e le m
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'1 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                             (Tstruct _interp_state noattr)) _pc (tptr tint)))
                (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                           (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                    (Econst_int (Int.repr 1) tint) (tptr tint))))
              (Ssequence
                (Sset _t'3 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                             (Tstruct _interp_state noattr)) _accu tlong))
                (Ssequence
                  (Sset _t'4 (Ederef (Etempvar _t'1 (tptr tint)) tint))
                  (Sset _d (Ederef (Ecast (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                      (Ebinop Omul (Etempvar _t'4 tint) (Ebinop Odiv (Esizeof tdouble tulong)
                        (Esizeof tlong tulong) tulong) tulong) (tptr tlong)) (tptr tdouble)) tdouble)))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _heap_alloc (Tfunction
                    ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
                    tlong cc_default))
                  ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
                   (Ebinop Odiv (Esizeof tdouble tulong) (Esizeof tlong tulong) tulong) ::
                   (Econst_int (Int.repr 253) tint) :: nil))
                (Sset _block (Etempvar _t'2 tlong)))
              (Ssequence
                (Sassign (Ederef (Ecast (Etempvar _block tlong) (tptr tdouble)) tdouble)
                  (Etempvar _d tdouble))
                (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                           (Tstruct _interp_state noattr)) _accu tlong)
                  (Etempvar _block tlong)))))
          E0 le6 m2 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      (* Full body = pre_return; return *)
      change (fn_body f_instr_GETFLOATFIELD) with
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'1
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
                (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                    (Econst_int (Int.repr 1) tint) (tptr tint))))
              (Ssequence
                (Sset _t'3
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong))
                (Ssequence
                  (Sset _t'4 (Ederef (Etempvar _t'1 (tptr tint)) tint))
                  (Sset _d
                    (Ederef
                      (Ecast
                        (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                          (Ebinop Omul (Etempvar _t'4 tint)
                            (Ebinop Odiv (Esizeof tdouble tulong)
                              (Esizeof tlong tulong) tulong) tulong) (tptr tlong))
                        (tptr tdouble)) tdouble)))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _heap_alloc (Tfunction
                    ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
                    tlong cc_default))
                  ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
                   (Ebinop Odiv (Esizeof tdouble tulong) (Esizeof tlong tulong) tulong) ::
                   (Econst_int (Int.repr 253) tint) :: nil))
                (Sset _block (Etempvar _t'2 tlong)))
              (Ssequence
                (Sassign
                  (Ederef (Ecast (Etempvar _block tlong) (tptr tdouble)) tdouble)
                  (Etempvar _d tdouble))
                (Sassign
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong)
                  (Etempvar _block tlong)))))
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))).

      replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
      set (ard' := mk_abs_rel
        sb so hm'
        cb new_co
        gb go0
        (ar_stack_block ard) (ar_stack_base_ofs ard)
        (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
      exists ard'.

      set (uso := Ptrofs.unsigned so) in *.

      assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some new_pc_v).
      { pose proof (load_after_store_same m m1 sb (uso + 0) new_pc_v Hstore_pc) as Htmp.
        unfold new_pc_v in Htmp |- *. rewrite load_result_vptr_local in Htmp. exact Htmp. }

      assert (Hpc_load2 : Mem.load Mint64 m2 sb (uso + 0) = Some new_pc_v).
      { apply (load_after_store_other m_fstore m2 sb (uso + 8) (uso + 0)
                 block_v new_pc_v Hstore_accu).
        - apply Hstruct_preserved2. exact Hpc_load_m1.
        - left. lia. }

      assert (Haccu_load2 : Mem.load Mint64 m2 sb (uso + 8) = Some block_v).
      { pose proof (load_after_store_same m_fstore m2 sb (uso + 8) block_v Hstore_accu) as Htmp.
        unfold block_v in Htmp |- *. rewrite load_result_vptr_local in Htmp. exact Htmp. }

      assert (Hfield_survive : forall field_ofs v0,
        field_ofs >= 16 ->
        Mem.load Mint64 m sb (uso + field_ofs) = Some v0 ->
        Mem.load Mint64 m2 sb (uso + field_ofs) = Some v0).
      { intros fo v0 Hfo Hload.
        assert (H1 : Mem.load Mint64 m1 sb (uso + fo) = Some v0).
        { apply (load_after_store_other m m1 sb (uso + 0) (uso + fo)
                   new_pc_v v0 Hstore_pc Hload). right. lia. }
        assert (H3 : Mem.load Mint64 m_fstore sb (uso + fo) = Some v0).
        { apply Hstruct_preserved2. exact H1. }
        apply (load_after_store_other m_fstore m2 sb (uso + 8) (uso + fo)
                 block_v v0 Hstore_accu H3). right. lia. }

      assert (Hsp_load2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { apply Hfield_survive; [lia | exact Hsp_load]. }

      assert (Henv_load2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
      { apply Hfield_survive; [lia | exact Henv_load]. }

      assert (Hextra_load2 : Mem.load Mint64 m2 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply Hfield_survive; [lia | exact Hextra_load]. }

      assert (Hgd_load2 : Mem.load Mint64 m2 sb (uso + 40) = Some (Vptr gb go0)).
      { apply Hfield_survive; [lia | exact Hgd_load]. }

      assert (Hts_load2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
      { apply Hfield_survive; [lia | exact Hts_load]. }

      (* Stack repr *)
      assert (Hstack_m1 : stack_repr hm cb co m1 (Machine.stack s) sp_b sp_ofs).
      { eapply (stack_repr_store_other_block hm cb co); eauto. }

      assert (Hsp_ne_new : sp_b <> new_b).
      { intro Heq; symmetry in Heq; exact (Hnew_ne_sp Heq). }
      assert (Hgb_ne_new : gb <> new_b).
      { intro Heq; symmetry in Heq; exact (Hnew_ne_gb Heq). }

      assert (Hstack_alloc : stack_repr hm cb co m_alloc (Machine.stack s) sp_b sp_ofs).
      { clear -Hstack_m1 Halloc_load_pres Hsp_ne_new.
        induction Hstack_m1 as [| v0 vs sp_b0 sp_ofs0 cv Hld Hvr Htl IH].
        - constructor.
        - econstructor.
          + apply Halloc_load_pres. exact Hld. exact Hsp_ne_new.
          + exact Hvr.
          + apply IH. exact Hsp_ne_new. }

      assert (Hstack_fstore : stack_repr hm cb co m_fstore (Machine.stack s) sp_b sp_ofs).
      { clear -Hstack_alloc Hfstore_load_pres Hsp_ne_new.
        induction Hstack_alloc as [| v0 vs sp_b0 sp_ofs0 cv Hld Hvr Htl IH].
        - constructor.
        - econstructor.
          + apply Hfstore_load_pres. exact Hsp_ne_new. exact Hld.
          + exact Hvr.
          + apply IH. exact Hsp_ne_new. }

      assert (Hstack2 : stack_repr hm cb co m2 (Machine.stack s) sp_b sp_ofs).
      { eapply (stack_repr_store_other_block hm cb co); eauto. }

      (* Global repr *)
      assert (Hglobal_m1 : global_repr hm cb co m1 (Machine.global s) gb go0).
      { eapply (global_repr_store_other_block hm cb co); eauto. }

      assert (Hglobal_alloc : global_repr hm cb co m_alloc (Machine.global s) gb go0).
      { clear -Hglobal_m1 Halloc_load_pres Hgb_ne_new.
        induction Hglobal_m1 as [| v0 vs gb0 gofs0 cv Hld Hvr Htl IH].
        - constructor.
        - econstructor.
          + apply Halloc_load_pres. exact Hld. exact Hgb_ne_new.
          + exact Hvr.
          + apply IH. exact Hgb_ne_new. }

      assert (Hglobal_fstore : global_repr hm cb co m_fstore (Machine.global s) gb go0).
      { clear -Hglobal_alloc Hfstore_load_pres Hgb_ne_new.
        induction Hglobal_alloc as [| v0 vs gb0 gofs0 cv Hld Hvr Htl IH].
        - constructor.
        - econstructor.
          + apply Hfstore_load_pres. exact Hgb_ne_new. exact Hld.
          + exact Hvr.
          + apply IH. exact Hgb_ne_new. }

      assert (Hglobal2 : global_repr hm cb co m2 (Machine.global s) gb go0).
      { eapply (global_repr_store_other_block hm cb co); eauto. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s in le' *)
      { subst le' le6 le5 le4 le3 le2 le1.
        repeat (rewrite PTree.gso by (compute; congruence)).
        exact Hle_s. }

      (* 2. pc field *)
      { exists new_pc_v. split.
        - exact Hpc_load2.
        - simpl. subst new_pc_v new_pc_ofs.
          apply pc_rel_shift_local. }

      (* 3. accu field *)
      { exists block_v. split.
        - exact Haccu_load2.
        - simpl. eapply val_repr_co_shift. exact Hval_repr_new. }

      (* 4. sp field *)
      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load2.
        - reflexivity.
        - simpl. eapply stack_repr_co_shift. apply Hstack_repr_ext. exact Hstack2.
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs0 Hofs0.
          eapply Mem.perm_store_1. exact Hstore_accu.
          eapply Hfstore_perm_pres.
          eapply Halloc_perm_pres.
          + eapply Mem.perm_valid_block.
            apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc).
            apply (Hsp_writable 0). lia.
          + eapply Mem.perm_store_1. exact Hstore_pc.
            apply Hsp_writable. exact Hofs0.
        - exact Hsp_align. }

      (* 5. env field *)
      { exists env_v. split.
        - exact Henv_load2.
        - simpl. eapply val_repr_co_shift. apply Hval_repr_ext. exact Henv_repr. }

      (* 6. extra_args field *)
      { simpl. exact Hextra_load2. }

      (* 7. global_data field *)
      { exists (Vptr gb go0). split; [| split; [| split]].
        - exact Hgd_load2.
        - simpl. reflexivity.
        - simpl. eapply global_repr_co_shift. apply Hglobal_repr_ext. exact Hglobal2.
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field *)
      { exists ts_ptr. split.
        - exact Hts_load2.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable *)
      { intros ofs0 Hofs0.
        eapply Mem.perm_store_1. exact Hstore_accu.
        eapply Hfstore_perm_pres.
        eapply Halloc_perm_pres.
        - eapply Mem.perm_valid_block.
          apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc).
          apply (Hsb_writable (Ptrofs.unsigned so)). lia.
        - eapply Mem.perm_store_1. exact Hstore_pc.
          apply Hsb_writable. exact Hofs0. }
    }
  }
Qed.
