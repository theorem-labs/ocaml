(* MAKEBLOCK2_correct.v -- MAKEBLOCK2 completeness proof.

   MAKEBLOCK2 reads tag from *pc, calls heap_alloc(s, 2, tag), stores
   accu as field 0, stack[0] as field 1, advances sp by 1, and sets
   accu to the block ptr.

   C code (f_instr_MAKEBLOCK2):
     t1 = s.pc; s.pc = t1+1; t7 = deref t1; tag = (uchar)t7;
     t2 = heap_alloc(s, 2, tag); block = t2;
     t6 = s.accu; deref(block+0) = t6;
     t4 = s.sp; t5 = deref(t4+0); deref(block+1) = t5;
     t3 = s.sp; s.sp = t3+1;
     s.accu = block;
     return 0;

   Rocq:
     handle_MAKEBLOCK2 t pc' s =
       match s.(stack) with
       | v1 :: rest =>
         let '(s', ptr) := heap_alloc s t [s.(accu); v1] in
         Step (s' <|pc:=pc'|> <|accu:=ptr|> <|stack:=rest|>)
       | _ => Error "MAKEBLOCK2: stack underflow"
       end.

   Extends MAKEBLOCK1 pattern with an additional field store (field 1
   from stack[0]) and sp advancement. *)

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
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout                                                       *)
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

Lemma interp_state_co_pc_accu_sp : exists co,
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

Lemma sem_add_pc_1_mk2 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint_mk2 : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_cast_int_to_tuchar_mk2 : forall n m,
  sem_cast (Vint n) tint tuchar m = Some (Vint (Int.zero_ext 8 n)).
Proof.
  intros. unfold sem_cast. simpl classify_cast. simpl. reflexivity.
Qed.

Lemma sem_cast_tuchar_to_tlong_mk2 : forall n m,
  sem_cast (Vint n) tuchar tlong m =
    Some (Vlong (Int64.repr (Int.unsigned n))).
Proof.
  intros. unfold sem_cast. simpl classify_cast. simpl. reflexivity.
Qed.

Lemma int_zero_ext_8_small_mk2 : forall z,
  0 <= z <= 255 ->
  Int.zero_ext 8 (Int.repr z) = Int.repr z.
Proof.
  intros z Hz.
  apply Int.same_bits_eq; intros i Hi.
  rewrite Int.bits_zero_ext by lia.
  destruct (Coqlib.zlt i 8); auto.
  rewrite Int.testbit_repr by lia.
  symmetry.
  apply Zbits.Ztestbit_above with (n := 8%nat). simpl.
  change (two_power_nat 8) with 256%Z. lia. lia.
Qed.

Lemma int_unsigned_repr_small_mk2 : forall z,
  0 <= z <= 255 ->
  Int.unsigned (Int.repr z) = z.
Proof.
  intros z Hz.
  apply Int.unsigned_repr.
  unfold Int.max_unsigned. change Int.modulus with 4294967296%Z. lia.
Qed.

Lemma pc_rel_shift_mk2 : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr 4)))
         cb (Ptrofs.add co (Ptrofs.repr sizeof_code_t)) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal. rewrite Ptrofs.add_assoc. rewrite Ptrofs.add_assoc.
  f_equal. rewrite Ptrofs.add_commut. reflexivity.
Qed.

Lemma load_result_vlong_mk2 : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr_mk2 : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* sem_add for sp + 1 on tptr tlong (from HandlerLemmas) *)

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_MAKEBLOCK2_correct : forall t,
    handler_correct (handle_MAKEBLOCK2 t) f_instr_MAKEBLOCK2
      (fun e m s ard =>
         let sb := ar_sptr_block ard in
         let so := ar_sptr_ofs ard in
         let cb := ar_code_base_block ard in
         let co := ar_code_base_ofs ard in
         let gb := ar_global_block ard in
         let sp_b := ar_stack_block ard in
         (* 0. e does not bind _heap_alloc *)
         e ! _heap_alloc = None /\
         (* 1. The code buffer contains Int.repr (Z.of_nat t) at the current PC *)
         Mem.load Mint32 m cb
           (Ptrofs.unsigned (Ptrofs.add co
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat t))) /\
         (* 2. t fits in unsigned char range *)
         (0 <= Z.of_nat t <= 255) /\
         (* 3. Heap map freshness: next_addr is not yet mapped *)
         (ar_heap_map ard) (next_addr s) = None /\
         (* 3a. Global block is valid *)
         Mem.valid_block m gb /\
         (* 4. Genv lookup for heap_alloc *)
         (exists b_ha,
            Genv.find_symbol (genv_genv ge) _heap_alloc = Some b_ha /\
            Genv.find_funct (genv_genv ge) (Vptr b_ha Ptrofs.zero) =
              Some heap_alloc_fundef) /\
         (* 5. heap_alloc: for any memory m', allocation succeeds *)
         (forall m',
            exists m_alloc new_b new_ofs,
              external_call heap_alloc_ef
                (Genv.to_senv (genv_genv ge))
                (Vptr sb so :: Vlong (Int64.repr 2) :: Vlong (Int64.repr (Z.of_nat t)) :: nil)
                m' E0 (Vptr new_b new_ofs) m_alloc /\
              (* Freshness: new block is fresh *)
              (forall b, Mem.valid_block m' b -> new_b <> b) /\
              (* Load preservation on existing blocks *)
              (forall b ofs chunk v,
                 Mem.load chunk m' b ofs = Some v -> b <> new_b ->
                 Mem.load chunk m_alloc b ofs = Some v) /\
              (* Permission preservation *)
              (forall b ofs k p,
                 Mem.valid_block m' b -> Mem.perm m' b ofs k p ->
                 Mem.perm m_alloc b ofs k p) /\
              (* Field 0 storable + load-back + other-block preservation *)
              (forall cv, exists m_store,
                 Mem.store Mint64 m_alloc new_b (Ptrofs.unsigned new_ofs) cv = Some m_store /\
                 Mem.load Mint64 m_store new_b (Ptrofs.unsigned new_ofs) =
                   Some (Val.load_result Mint64 cv) /\
                 (forall b ofs chunk v, b <> new_b ->
                    Mem.load chunk m_alloc b ofs = Some v ->
                    Mem.load chunk m_store b ofs = Some v) /\
                 (* Field 1 storable + load-back + other-block preservation *)
                 (forall cv1, exists m_store1,
                    Mem.store Mint64 m_store new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) cv1 = Some m_store1 /\
                    Mem.load Mint64 m_store1 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) =
                      Some (Val.load_result Mint64 cv1) /\
                    (forall b ofs chunk v, b <> new_b ->
                       Mem.load chunk m_store b ofs = Some v ->
                       Mem.load chunk m_store1 b ofs = Some v) /\
                    (* Permission preservation through both field stores *)
                    (forall b ofs k p,
                       Mem.perm m_alloc b ofs k p ->
                       Mem.perm m_store1 b ofs k p)))))
      (fun _ s => match s.(Machine.stack) with _ :: _ => False | _ => True end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro t.
  intros e le m s.
  unfold handle_MAKEBLOCK2. simpl.

  (* Destruct the stack *)
  destruct (Machine.stack s) as [| v1 rest] eqn:Hstk.
  - (* Empty stack: Error case *)
    exact I.
  - (* v1 :: rest: Step case *)
    intros ard Hpre Hstep_pre.
    unfold abs_rel_with_ard in Hpre.

    set (sb := ar_sptr_block ard) in *.
    set (so := ar_sptr_ofs ard) in *.
    set (hm := ar_heap_map ard) in *.
    set (cb := ar_code_base_block ard) in *.
    set (co := ar_code_base_ofs ard) in *.
    set (gb := ar_global_block ard) in *.
    set (go0 := ar_global_ofs ard) in *.

    destruct Hpre as (Hle_s &
      [pc_ptr [Hpc_load Hpc_rel]] &
      [accu_v [Haccu_load Haccu_repr]] &
      [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
      [env_v [Henv_load Henv_repr]] &
      Hextra_load &
      [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
      [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
    subst sp_ptr gd_ptr.

    destruct Hstep_pre as (He_heap_alloc & Hcode_load & Ht_range & Hhm_fresh &
      Hgb_valid & [b_ha [Hfind_symbol Hfind_funct]] & Halloc_spec_all).

    (* Invert stack_repr to get head element *)
    rewrite Hstk in Hstack_repr.
    inversion Hstack_repr as [| v1' rest' sp_b' sp_ofs' cv1 Hsp0_load Hcv1_repr Hstack_repr_rest].
    subst.

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
    pose proof (code_block_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

    (* Composite environment *)
    destruct interp_state_co_pc_accu_sp as [co_is [Hco [Hpc_offset [Haccu_offset Hsp_offset]]]].

    (* pc_ptr is a concrete Vptr *)
    unfold pc_rel in Hpc_rel. subst pc_ptr.
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

    (* New pc after advancement *)
    set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
    set (new_pc_v := Vptr cb new_pc_ofs).

    (* --- Store 1: pc field --- *)
    destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia) new_pc_v)
      as [m1 Hstore_pc].

    (* Accu survives pc store *)
    assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
               (Ptrofs.unsigned so + 8) new_pc_v accu_v Hstore_pc Haccu_load).
      right. lia. }

    (* Code load survives pc store (different block) *)
    assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
              Some (Vint (Int.repr (Z.of_nat t)))).
    { erewrite Mem.load_store_other.
      - exact Hcode_load.
      - exact Hstore_pc.
      - left. exact Hcb_ne. }

    (* Tag value: cast and convert *)
    set (tag_int := Int.repr (Z.of_nat t)).
    set (tag_uchar := Int.zero_ext 8 tag_int).
    set (tag_z := Z.of_nat t).

    assert (Htag_uchar_eq : tag_uchar = tag_int).
    { subst tag_uchar tag_int. apply int_zero_ext_8_small_mk2. exact Ht_range. }

    assert (Htag_unsigned : Int.unsigned tag_uchar = tag_z).
    { rewrite Htag_uchar_eq. subst tag_int tag_z. apply int_unsigned_repr_small_mk2. exact Ht_range. }

    (* Sp load survives pc store *)
    assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
               (Ptrofs.unsigned so + 16) new_pc_v (Vptr sp_b sp_ofs) Hstore_pc Hsp_load).
      right. lia. }

    (* --- heap_alloc call --- *)
    destruct (Halloc_spec_all m1)
      as [m_alloc [new_b [new_ofs
           (Hext_call & Hnew_fresh &
            Halloc_load_pres & Halloc_perm_pres & Hcan_store)]]].

    (* Derive freshness for specific blocks *)
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

    (* Derive struct field preservation from generic load preservation *)
    assert (Hstruct_preserved : forall ofs v,
      Mem.load Mint64 m1 sb ofs = Some v ->
      Mem.load Mint64 m_alloc sb ofs = Some v).
    { intros ofs0 v0 Hld. apply Halloc_load_pres; auto. }

    (* Accu in m_alloc *)
    assert (Haccu_load_alloc : Mem.load Mint64 m_alloc sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { apply Hstruct_preserved. exact Haccu_load_m1. }

    (* Sp in m_alloc *)
    assert (Hsp_load_alloc : Mem.load Mint64 m_alloc sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
    { apply Hstruct_preserved. exact Hsp_load_m1. }

    (* stack[0] load survives: m -> m1 (store to sb, sp_b <> sb) -> m_alloc *)
    assert (Hsp0_load_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) = Some cv1).
    { erewrite Mem.load_store_other.
      - exact Hsp0_load.
      - exact Hstore_pc.
      - left. exact (Hsp_ne_sb). }
    assert (Hsp0_load_alloc : Mem.load Mint64 m_alloc sp_b (Ptrofs.unsigned sp_ofs) = Some cv1).
    { apply Halloc_load_pres.
      - exact Hsp0_load_m1.
      - intro Heq; symmetry in Heq; exact (Hnew_ne_sp Heq). }

    (* --- Store field 0: *(block + 0) = accu_v --- *)
    destruct (Hcan_store accu_v) as [m_f0 [Hstore_f0 [Hload_f0 [Hf0_load_pres Hcan_store_f1]]]].

    (* Struct field loads survive field 0 store *)
    assert (Hstruct_preserved_f0 : forall ofs0 v0,
      Mem.load Mint64 m1 sb ofs0 = Some v0 ->
      Mem.load Mint64 m_f0 sb ofs0 = Some v0).
    { intros ofs0 v0 Hld.
      apply Hf0_load_pres.
      - intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq).
      - apply Hstruct_preserved. exact Hld. }

    (* Sp in m_f0 *)
    assert (Hsp_load_f0 : Mem.load Mint64 m_f0 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
    { apply Hstruct_preserved_f0. exact Hsp_load_m1. }

    (* stack[0] in m_f0 *)
    assert (Hsp0_load_f0 : Mem.load Mint64 m_f0 sp_b (Ptrofs.unsigned sp_ofs) = Some cv1).
    { apply Hf0_load_pres.
      - intro Heq; symmetry in Heq; exact (Hnew_ne_sp Heq).
      - exact Hsp0_load_alloc. }

    (* --- Store field 1: *(block + 1) = cv1 --- *)
    destruct (Hcan_store_f1 cv1) as [m_f1 [Hstore_f1 [Hload_f1 [Hf1_load_pres Hf1_perm_pres]]]].

    (* Struct field loads survive field 1 store *)
    assert (Hstruct_preserved_f1 : forall ofs0 v0,
      Mem.load Mint64 m1 sb ofs0 = Some v0 ->
      Mem.load Mint64 m_f1 sb ofs0 = Some v0).
    { intros ofs0 v0 Hld.
      apply Hf1_load_pres.
      - intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq).
      - apply Hstruct_preserved_f0. exact Hld. }

    (* Sp in m_f1 *)
    assert (Hsp_load_f1 : Mem.load Mint64 m_f1 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
    { apply Hstruct_preserved_f1. exact Hsp_load_m1. }

    (* Accu in m_f1 *)
    assert (Haccu_load_f1 : Mem.load Mint64 m_f1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { apply Hstruct_preserved_f1. exact Haccu_load_m1. }

    (* --- Store 2: sp field <- Vptr sp_b (sp_ofs + 8) --- *)
    set (new_sp_ofs := Ptrofs.add sp_ofs (Ptrofs.repr 8)).
    set (new_sp_v := Vptr sp_b new_sp_ofs).

    (* sb_writable through all intermediate memories *)
    assert (Hsb_writable_m1 :
      Mem.range_perm m1 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { eapply sb_writable_after_store; eauto. }
    assert (Hsb_writable_f1 :
      Mem.range_perm m_f1 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs0 Hofs0. eapply Hf1_perm_pres.
      eapply Halloc_perm_pres.
      - eapply Mem.perm_valid_block.
        apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc).
        apply (Hsb_writable (Ptrofs.unsigned so)). lia.
      - apply Hsb_writable_m1. exact Hofs0. }

    destruct (store_succeeds_sb m_f1 sb so 16 (Vptr sp_b sp_ofs) Hsb_writable_f1 Hsp_load_f1 ltac:(lia) ltac:(lia) new_sp_v)
      as [m2 Hstore_sp].

    (* Accu in m2 *)
    assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { apply (load_after_store_other m_f1 m2 sb (Ptrofs.unsigned so + 16)
               (Ptrofs.unsigned so + 8) new_sp_v accu_v Hstore_sp Haccu_load_f1).
      left. lia. }

    (* --- Store 3: accu field <- block_v --- *)
    set (block_v := Vptr new_b new_ofs).

    assert (Hsb_writable_m2 :
      Mem.range_perm m2 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { eapply sb_writable_after_store; eauto. }

    destruct (store_succeeds_sb m2 sb so 8 accu_v Hsb_writable_m2 Haccu_load_m2 ltac:(lia) ltac:(lia) block_v)
      as [m3 Hstore_accu].

    (* Final memory chain: m -> m1 (pc) -> m_alloc (heap_alloc) ->
       m_f0 (field 0) -> m_f1 (field 1) -> m2 (sp) -> m3 (accu) *)

    (* --- Heap map extension --- *)
    set (addr := next_addr s).
    set (hm' := fun n => if Nat.eqb n addr then Some (new_b, new_ofs) else hm n).

    assert (Hval_repr_ext : forall v cv, val_repr hm cb co v cv -> val_repr hm' cb co v cv).
    { intros v cv Hvr.
      inversion Hvr; subst.
      - constructor.
      - econstructor. unfold hm'.
        destruct (Nat.eqb addr0 addr) eqn:Heq.
        + apply Nat.eqb_eq in Heq. subst addr0.
          exfalso. unfold addr in H. rewrite Hhm_fresh in H. discriminate.
        + exact H.
      - econstructor.
        + unfold hm'. destruct (Nat.eqb addr0 addr) eqn:Heq.
          * apply Nat.eqb_eq in Heq. subst addr0.
            exfalso. unfold addr in H. rewrite Hhm_fresh in H. discriminate.
          * exact H.
        + reflexivity.
      - constructor.
      - econstructor. }

    assert (Hval_repr_new : val_repr hm' cb co (Val_ptr addr) block_v).
    { econstructor. unfold hm'. rewrite Nat.eqb_refl. reflexivity. }

    assert (Hstack_repr_ext : forall stk m0 sp_b0 sp_ofs0,
      stack_repr hm cb co m0 stk sp_b0 sp_ofs0 -> stack_repr hm' cb co m0 stk sp_b0 sp_ofs0).
    { intros stk0 m0 sp_b0 sp_ofs0 Hsr.
      induction Hsr.
      - constructor.
      - econstructor; eauto. }

    assert (Hglobal_repr_ext : forall gs m0 gb0 gofs0,
      global_repr hm cb co m0 gs gb0 gofs0 -> global_repr hm' cb co m0 gs gb0 gofs0).
    { intros gs0 m0 gb0 gofs0 Hgr.
      induction Hgr.
      - constructor.
      - econstructor; eauto. }

    (* --- Build witnesses for existential --- *)
    set (le1 := PTree.set _t'1 (Vptr cb pc_ofs) le).
    set (le2 := PTree.set _t'7 (Vint tag_int) le1).
    set (le3 := PTree.set _tag (Vint tag_uchar) le2).
    set (le4 := PTree.set _t'2 block_v le3).
    set (le5 := PTree.set _block block_v le4).
    set (le6 := PTree.set _t'6 accu_v le5).
    (* After store field 0, read sp for field 1 *)
    set (le7 := PTree.set _t'4 (Vptr sp_b sp_ofs) le6).
    set (le8 := PTree.set _t'5 cv1 le7).
    (* After store field 1, read sp for sp advance *)
    set (le9 := PTree.set _t'3 (Vptr sp_b sp_ofs) le8).
    set (le' := le9).

    exists le'. exists m3.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec_stmt derivation                                    *)
    (* ============================================================== *)
    {
      (* Phase 1: Sset _t'1 (s->pc) *)
      assert (Hexec_set_t1 : exec_stmt function_entry1 clight_ge e le m
          (Sset _t'1 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
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

      (* Phase 2: Sassign (s->pc) (_t'1 + 1) *)
      assert (Hexec_store_pc : exec_stmt function_entry1 clight_ge e le1 m
          (Sassign
            (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
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
        rewrite (sem_add_pc_1_mk2 cb pc_ofs m); eval_cbn.
        rewrite (sem_cast_ptr_tint_to_ptr_tint_mk2 cb new_pc_ofs); eval_cbn.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        fold new_pc_v.
        rewrite Hstore_pc; eval_cbn.
        reflexivity. }

      (* Phase 3: Sset _t'7 deref(_t'1) *)
      assert (Hexec_read_tag : exec_stmt function_entry1 clight_ge e le1 m1
          (Sset _t'7 (Ederef (Etempvar _t'1 (tptr tint)) tint))
          E0 le2 m1 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le1.
        rewrite PTree.gss; eval_cbn.
        rewrite Hcode_load_m1; eval_cbn.
        reflexivity. }

      (* Phase 4: Sset _tag (cast _t'7 tuchar) *)
      assert (Hexec_set_tag : exec_stmt function_entry1 clight_ge e le2 m1
          (Sset _tag (Ecast (Etempvar _t'7 tint) tuchar))
          E0 le3 m1 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le2.
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_cast_int_to_tuchar_mk2 tag_int m1); eval_cbn.
        reflexivity. }

      (* Phase 5: Scall heap_alloc *)
      assert (Hexec_call : exec_stmt function_entry1 clight_ge e le3 m1
          (Scall (Some _t'2)
            (Evar _heap_alloc (Tfunction
              ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
              tlong cc_default))
            ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
             (Econst_int (Int.repr 2) tint) :: (Etempvar _tag tuchar) :: nil))
          E0 le4 m_alloc Out_normal).
      { assert (Hcast_tag : sem_cast (Vint tag_uchar) tuchar tlong m1 =
                  Some (Vlong (Int64.repr (Int.unsigned tag_uchar)))).
        { apply sem_cast_tuchar_to_tlong_mk2. }
        rewrite Htag_unsigned in Hcast_tag.

        eapply exec_Scall with
          (tyargs := (tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
          (tyres := tlong)
          (cconv := cc_default)
          (vf := Vptr b_ha Ptrofs.zero)
          (vargs := Vptr sb so :: Vlong (Int64.repr 2) :: Vlong (Int64.repr tag_z) :: nil)
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
            unfold le3. rewrite PTree.gso by (compute; congruence).
            unfold le2. rewrite PTree.gso by (compute; congruence).
            unfold le1. rewrite PTree.gso by (compute; congruence).
            exact Hle_s.
          + simpl. reflexivity.
          + econstructor.
            * econstructor.
            * simpl. reflexivity.
            * econstructor.
              -- econstructor.
                 unfold le3. rewrite PTree.gss. reflexivity.
              -- exact Hcast_tag.
              -- constructor.
        - exact Hfind_funct.
        - reflexivity.
        - eapply eval_funcall_external. exact Hext_call.
      }

      (* Phase 6: Sset _block _t'2 *)
      assert (Hexec_set_block : exec_stmt function_entry1 clight_ge e le4 m_alloc
          (Sset _block (Etempvar _t'2 tlong))
          E0 le5 m_alloc Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le4. rewrite PTree.gss; eval_cbn.
        reflexivity. }

      (* Phase 7: Sset _t'6 (s->accu) *)
      assert (Hexec_read_accu : exec_stmt function_entry1 clight_ge e le5 m_alloc
          (Sset _t'6
            (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                     (Tstruct _interp_state noattr)) _accu tlong))
          E0 le6 m_alloc Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le5.
        rewrite PTree.gso by (compute; congruence).
        unfold le4.
        rewrite PTree.gso by (compute; congruence).
        unfold le3.
        rewrite PTree.gso by (compute; congruence).
        unfold le2.
        rewrite PTree.gso by (compute; congruence).
        unfold le1.
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_load_alloc; eval_cbn.
        reflexivity. }

      (* Phase 8: Sassign deref(block+0) = _t'6 -- store field 0 *)
      assert (Hexec_store_f0 : exec_stmt function_entry1 clight_ge e le6 m_alloc
          (Sassign
            (Ederef
              (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
            (Etempvar _t'6 tlong))
          E0 le6 m_f0 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le6.
        rewrite PTree.gso by (compute; congruence).
        unfold le5.
        rewrite PTree.gss; eval_cbn.
        fold block_v.
        replace (sem_cast block_v tlong (tptr tlong) m_alloc) with (Some block_v) by (unfold block_v, sem_cast; simpl classify_cast; reflexivity); eval_cbn.
        unfold block_v at 1. rewrite (sem_add_sp_0 new_b new_ofs m_alloc); eval_cbn.
        unfold le6. rewrite PTree.gss; eval_cbn.
        rewrite (sem_cast_long_val_repr hm cb co (Machine.accu s) accu_v m_alloc Haccu_repr);
          eval_cbn.
        rewrite Hstore_f0; eval_cbn.
        reflexivity. }

      (* Phase 9: Sset _t'4 (s->sp) *)
      assert (Hexec_read_sp : exec_stmt function_entry1 clight_ge e le6 m_f0
          (Sset _t'4
            (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                     (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          E0 le7 m_f0 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le6.
        rewrite PTree.gso by (compute; congruence).
        unfold le5.
        rewrite PTree.gso by (compute; congruence).
        unfold le4.
        rewrite PTree.gso by (compute; congruence).
        unfold le3.
        rewrite PTree.gso by (compute; congruence).
        unfold le2.
        rewrite PTree.gso by (compute; congruence).
        unfold le1.
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hsp_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
        rewrite Hsp_load_f0; eval_cbn.
        reflexivity. }

      (* Phase 10: Sset _t'5 deref(_t'4 + 0) -- read stack[0] *)
      assert (Hexec_read_sp0 : exec_stmt function_entry1 clight_ge e le7 m_f0
          (Sset _t'5
            (Ederef
              (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
          E0 le8 m_f0 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le7.
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_sp_0 sp_b sp_ofs m_f0); eval_cbn.
        rewrite Hsp0_load_f0; eval_cbn.
        reflexivity. }

      (* Phase 11: Sassign deref(block+1) = _t'5 -- store field 1 *)
      assert (Hexec_store_f1 : exec_stmt function_entry1 clight_ge e le8 m_f0
          (Sassign
            (Ederef
              (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
            (Etempvar _t'5 tlong))
          E0 le8 m_f1 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le8.
        rewrite PTree.gso by (compute; congruence).
        unfold le7.
        rewrite PTree.gso by (compute; congruence).
        unfold le6.
        rewrite PTree.gso by (compute; congruence).
        unfold le5.
        rewrite PTree.gss; eval_cbn.
        fold block_v.
        replace (sem_cast block_v tlong (tptr tlong) m_f0) with (Some block_v) by (unfold block_v, sem_cast; simpl classify_cast; reflexivity); eval_cbn.
        unfold block_v at 1. rewrite (sem_add_sp_1 new_b new_ofs m_f0); eval_cbn.
        unfold le8. rewrite PTree.gss; eval_cbn.
        rewrite (sem_cast_long_val_repr hm cb co v1 cv1 m_f0 Hcv1_repr);
          eval_cbn.
        rewrite Hstore_f1; eval_cbn.
        reflexivity. }

      (* Phase 12: Sset _t'3 (s->sp) -- read sp again for sp advance *)
      assert (Hexec_read_sp2 : exec_stmt function_entry1 clight_ge e le8 m_f1
          (Sset _t'3
            (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                     (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          E0 le9 m_f1 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le8.
        rewrite PTree.gso by (compute; congruence).
        unfold le7.
        rewrite PTree.gso by (compute; congruence).
        unfold le6.
        rewrite PTree.gso by (compute; congruence).
        unfold le5.
        rewrite PTree.gso by (compute; congruence).
        unfold le4.
        rewrite PTree.gso by (compute; congruence).
        unfold le3.
        rewrite PTree.gso by (compute; congruence).
        unfold le2.
        rewrite PTree.gso by (compute; congruence).
        unfold le1.
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hsp_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
        rewrite Hsp_load_f1; eval_cbn.
        reflexivity. }

      (* Phase 13: Sassign (s->sp) (_t'3 + 1) -- sp advance *)
      assert (Hexec_store_sp : exec_stmt function_entry1 clight_ge e le9 m_f1
          (Sassign
            (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                     (Tstruct _interp_state noattr)) _sp (tptr tlong))
            (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)))
          E0 le9 m2 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le9.
        rewrite PTree.gso by (compute; congruence).
        unfold le8.
        rewrite PTree.gso by (compute; congruence).
        unfold le7.
        rewrite PTree.gso by (compute; congruence).
        unfold le6.
        rewrite PTree.gso by (compute; congruence).
        unfold le5.
        rewrite PTree.gso by (compute; congruence).
        unfold le4.
        rewrite PTree.gso by (compute; congruence).
        unfold le3.
        rewrite PTree.gso by (compute; congruence).
        unfold le2.
        rewrite PTree.gso by (compute; congruence).
        unfold le1.
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hsp_offset; eval_cbn.
        unfold le9. rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_sp_1 sp_b sp_ofs m_f1); eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (sem_cast_ptr_to_ptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) m_f1); eval_cbn.
        rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
        unfold new_sp_v, new_sp_ofs in Hstore_sp.
        rewrite Hstore_sp; eval_cbn.
        reflexivity. }

      (* Phase 14: Sassign (s->accu) _block *)
      assert (Hexec_store_accu : exec_stmt function_entry1 clight_ge e le9 m2
          (Sassign
            (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                     (Tstruct _interp_state noattr)) _accu tlong)
            (Etempvar _block tlong))
          E0 le9 m3 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le9.
        rewrite PTree.gso by (compute; congruence).
        unfold le8.
        rewrite PTree.gso by (compute; congruence).
        unfold le7.
        rewrite PTree.gso by (compute; congruence).
        unfold le6.
        rewrite PTree.gso by (compute; congruence).
        unfold le5.
        rewrite PTree.gso by (compute; congruence).
        unfold le4.
        rewrite PTree.gso by (compute; congruence).
        unfold le3.
        rewrite PTree.gso by (compute; congruence).
        unfold le2.
        rewrite PTree.gso by (compute; congruence).
        unfold le1.
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        unfold le9.
        rewrite PTree.gso by (compute; congruence).
        unfold le8.
        rewrite PTree.gso by (compute; congruence).
        unfold le7.
        rewrite PTree.gso by (compute; congruence).
        unfold le6.
        rewrite PTree.gso by (compute; congruence).
        unfold le5.
        rewrite PTree.gss; eval_cbn.
        fold block_v.
        unfold block_v at 1.
        rewrite (sem_cast_long_vptr new_b new_ofs m2); eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        fold block_v. rewrite Hstore_accu; eval_cbn.
        reflexivity. }

      (* Phase 15: Sreturn 0 *)
      assert (Hexec_return : exec_stmt function_entry1 clight_ge e le9 m3
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          E0 le9 m3 (Out_return (Some (Vint (Int.repr 0), tint)))).
      { apply (eval_stmt_to_exec clight_ge 10). reflexivity. }

      (* Now combine all phases *)

      (* Seq: Sset _t'1; Sassign s->pc *)
      assert (Hexec_pc_advance :
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

      (* Seq: Sset _t'7; Sset _tag *)
      assert (Hexec_tag_read :
        exec_stmt function_entry1 clight_ge e le1 m1
          (Ssequence
            (Sset _t'7 (Ederef (Etempvar _t'1 (tptr tint)) tint))
            (Sset _tag (Ecast (Etempvar _t'7 tint) tuchar)))
          E0 le3 m1 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      (* Seq: pc_advance; tag_read *)
      assert (Hexec_pc_tag :
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
              (Sset _t'7 (Ederef (Etempvar _t'1 (tptr tint)) tint))
              (Sset _tag (Ecast (Etempvar _t'7 tint) tuchar))))
          E0 le3 m1 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      (* Seq: Scall; Sset _block *)
      assert (Hexec_alloc_block :
        exec_stmt function_entry1 clight_ge e le3 m1
          (Ssequence
            (Scall (Some _t'2)
              (Evar _heap_alloc (Tfunction
                ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
                tlong cc_default))
              ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
               (Econst_int (Int.repr 2) tint) :: (Etempvar _tag tuchar) :: nil))
            (Sset _block (Etempvar _t'2 tlong)))
          E0 le5 m_alloc Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      (* Seq: Sset _t'6 (accu); Sassign *(block+0) *)
      assert (Hexec_read_store_f0 :
        exec_stmt function_entry1 clight_ge e le5 m_alloc
          (Ssequence
            (Sset _t'6
              (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _accu tlong))
            (Sassign
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                  (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
              (Etempvar _t'6 tlong)))
          E0 le6 m_f0 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      (* Seq: Sset _t'4 (sp); Sset _t'5 deref(t4+0); Sassign *(block+1) *)
      assert (Hexec_read_sp_store_f1 :
        exec_stmt function_entry1 clight_ge e le6 m_f0
          (Ssequence
            (Sset _t'4
              (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Ssequence
              (Sset _t'5
                (Ederef
                  (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                    (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                    (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
                (Etempvar _t'5 tlong))))
          E0 le8 m_f1 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1.
        - exact Hexec_read_sp.
        - replace E0 with (E0 ** E0) by reflexivity.
          eapply exec_Sseq_1; eauto. }

      (* Seq: Sset _t'3 (sp); Sassign s->sp = t3+1 *)
      assert (Hexec_sp_advance :
        exec_stmt function_entry1 clight_ge e le8 m_f1
          (Ssequence
            (Sset _t'3
              (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Sassign
              (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _sp (tptr tlong))
              (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
                (Econst_int (Int.repr 1) tint) (tptr tlong))))
          E0 le9 m2 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      (* Seq: sp_advance; store_accu *)
      assert (Hexec_sp_accu :
        exec_stmt function_entry1 clight_ge e le8 m_f1
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _sp (tptr tlong)))
              (Sassign
                (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _sp (tptr tlong))
                (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong))))
            (Sassign
              (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _accu tlong)
              (Etempvar _block tlong)))
          E0 le9 m3 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      (* Seq: read_store_f0; read_sp_store_f1; sp_accu *)
      assert (Hexec_fields_sp_accu :
        exec_stmt function_entry1 clight_ge e le5 m_alloc
          (Ssequence
            (Ssequence
              (Sset _t'6
                (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _accu tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                    (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                (Etempvar _t'6 tlong)))
            (Ssequence
              (Ssequence
                (Sset _t'4
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                           (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Ssequence
                  (Sset _t'5
                    (Ederef
                      (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                        (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                        (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
                    (Etempvar _t'5 tlong))))
              (Ssequence
                (Ssequence
                  (Sset _t'3
                    (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                             (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                  (Sassign
                    (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                             (Tstruct _interp_state noattr)) _sp (tptr tlong))
                    (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
                      (Econst_int (Int.repr 1) tint) (tptr tlong))))
                (Sassign
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                           (Tstruct _interp_state noattr)) _accu tlong)
                  (Etempvar _block tlong)))))
          E0 le9 m3 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto.
        replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      (* Seq: alloc_block; fields_sp_accu *)
      assert (Hexec_alloc_rest :
        exec_stmt function_entry1 clight_ge e le3 m1
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _heap_alloc (Tfunction
                  ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
                  tlong cc_default))
                ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
                 (Econst_int (Int.repr 2) tint) :: (Etempvar _tag tuchar) :: nil))
              (Sset _block (Etempvar _t'2 tlong)))
            (Ssequence
              (Ssequence
                (Sset _t'6
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                           (Tstruct _interp_state noattr)) _accu tlong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                      (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                  (Etempvar _t'6 tlong)))
              (Ssequence
                (Ssequence
                  (Sset _t'4
                    (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                             (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                  (Ssequence
                    (Sset _t'5
                      (Ederef
                        (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                          (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                          (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
                      (Etempvar _t'5 tlong))))
                (Ssequence
                  (Ssequence
                    (Sset _t'3
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                               (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                    (Sassign
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                               (Tstruct _interp_state noattr)) _sp (tptr tlong))
                      (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
                        (Econst_int (Int.repr 1) tint) (tptr tlong))))
                  (Sassign
                    (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                             (Tstruct _interp_state noattr)) _accu tlong)
                    (Etempvar _block tlong))))))
          E0 le9 m3 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      (* The full pre-return body *)
      assert (Hexec_body_pre_return :
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
                (Sset _t'7 (Ederef (Etempvar _t'1 (tptr tint)) tint))
                (Sset _tag (Ecast (Etempvar _t'7 tint) tuchar))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _heap_alloc (Tfunction
                    ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
                    tlong cc_default))
                  ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
                   (Econst_int (Int.repr 2) tint) :: (Etempvar _tag tuchar) :: nil))
                (Sset _block (Etempvar _t'2 tlong)))
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                             (Tstruct _interp_state noattr)) _accu tlong))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                        (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                    (Etempvar _t'6 tlong)))
                (Ssequence
                  (Ssequence
                    (Sset _t'4
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                               (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                    (Ssequence
                      (Sset _t'5
                        (Ederef
                          (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                            (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                            (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
                        (Etempvar _t'5 tlong))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'3
                        (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                 (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                      (Sassign
                        (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                 (Tstruct _interp_state noattr)) _sp (tptr tlong))
                        (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
                          (Econst_int (Int.repr 1) tint) (tptr tlong))))
                    (Sassign
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                               (Tstruct _interp_state noattr)) _accu tlong)
                      (Etempvar _block tlong)))))))
          E0 le9 m3 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

      (* Full body = pre_return; return *)
      change (fn_body f_instr_MAKEBLOCK2) with
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'1
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
                (Sassign
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                    (Econst_int (Int.repr 1) tint) (tptr tint))))
              (Ssequence
                (Sset _t'7 (Ederef (Etempvar _t'1 (tptr tint)) tint))
                (Sset _tag (Ecast (Etempvar _t'7 tint) tuchar))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _heap_alloc (Tfunction
                    ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
                    tlong cc_default))
                  ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
                   (Econst_int (Int.repr 2) tint) :: (Etempvar _tag tuchar) :: nil))
                (Sset _block (Etempvar _t'2 tlong)))
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                             (Tstruct _interp_state noattr)) _accu tlong))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                        (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                    (Etempvar _t'6 tlong)))
                (Ssequence
                  (Ssequence
                    (Sset _t'4
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                               (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                    (Ssequence
                      (Sset _t'5
                        (Ederef
                          (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                            (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                            (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
                        (Etempvar _t'5 tlong))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'3
                        (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                 (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                      (Sassign
                        (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                 (Tstruct _interp_state noattr)) _sp (tptr tlong))
                        (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
                          (Econst_int (Int.repr 1) tint) (tptr tlong))))
                    (Sassign
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                               (Tstruct _interp_state noattr)) _accu tlong)
                      (Etempvar _block tlong)))))))
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

      (* pc field at uso+0: written by store_pc in m1, preserved through
         m_alloc, m_f0, m_f1 (stores to new_b), m2 (store at uso+16),
         m3 (store at uso+8) *)
      assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some new_pc_v).
      { pose proof (load_after_store_same m m1 sb (uso + 0) new_pc_v Hstore_pc) as Htmp.
        unfold new_pc_v in Htmp |- *. rewrite load_result_vptr_mk2 in Htmp. exact Htmp. }

      assert (Hpc_load_f1 : Mem.load Mint64 m_f1 sb (uso + 0) = Some new_pc_v).
      { apply Hstruct_preserved_f1. exact Hpc_load_m1. }

      assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (uso + 0) = Some new_pc_v).
      { apply (load_after_store_other m_f1 m2 sb (uso + 16) (uso + 0)
                 new_sp_v new_pc_v Hstore_sp Hpc_load_f1). left. lia. }

      assert (Hpc_load3 : Mem.load Mint64 m3 sb (uso + 0) = Some new_pc_v).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 0)
                 block_v new_pc_v Hstore_accu Hpc_load_m2). left. lia. }

      (* accu field at uso+8: store_accu wrote block_v *)
      assert (Haccu_load3 : Mem.load Mint64 m3 sb (uso + 8) = Some block_v).
      { pose proof (load_after_store_same m2 m3 sb (uso + 8) block_v Hstore_accu) as Htmp.
        unfold block_v in Htmp |- *. rewrite load_result_vptr_mk2 in Htmp. exact Htmp. }

      (* sp field at uso+16: written by store_sp in m2, preserved through m3 *)
      assert (Hsp_load_m2 : Mem.load Mint64 m2 sb (uso + 16) = Some new_sp_v).
      { pose proof (load_after_store_same m_f1 m2 sb (uso + 16) new_sp_v Hstore_sp) as Htmp.
        unfold new_sp_v in Htmp |- *. rewrite load_result_vptr_mk2 in Htmp. exact Htmp. }

      assert (Hsp_load3 : Mem.load Mint64 m3 sb (uso + 16) = Some new_sp_v).
      { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 16)
                 block_v new_sp_v Hstore_accu Hsp_load_m2). right. lia. }

      (* Helper: struct fields at offsets >= 24 survive all stores *)
      assert (Hfield_survive : forall field_ofs v,
        field_ofs >= 24 ->
        Mem.load Mint64 m sb (uso + field_ofs) = Some v ->
        Mem.load Mint64 m3 sb (uso + field_ofs) = Some v).
      { intros fo v Hfo Hload.
        assert (H1 : Mem.load Mint64 m1 sb (uso + fo) = Some v).
        { apply (load_after_store_other m m1 sb (uso + 0) (uso + fo)
                   new_pc_v v Hstore_pc Hload). right. lia. }
        assert (H2 : Mem.load Mint64 m_f1 sb (uso + fo) = Some v).
        { apply Hstruct_preserved_f1. exact H1. }
        assert (H3 : Mem.load Mint64 m2 sb (uso + fo) = Some v).
        { apply (load_after_store_other m_f1 m2 sb (uso + 16) (uso + fo)
                   new_sp_v v Hstore_sp H2). right. lia. }
        apply (load_after_store_other m2 m3 sb (uso + 8) (uso + fo)
                 block_v v Hstore_accu H3). right. lia. }

      assert (Henv_load3 : Mem.load Mint64 m3 sb (uso + 24) = Some env_v).
      { apply Hfield_survive; [lia | exact Henv_load]. }

      assert (Hextra_load3 : Mem.load Mint64 m3 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply Hfield_survive; [lia | exact Hextra_load]. }

      assert (Hgd_load3 : Mem.load Mint64 m3 sb (uso + 40) = Some (Vptr gb go0)).
      { apply Hfield_survive; [lia | exact Hgd_load]. }

      assert (Hts_load3 : Mem.load Mint64 m3 sb (uso + 48) = Some ts_ptr).
      { apply Hfield_survive; [lia | exact Hts_load]. }

      (* Stack repr in m3: the new stack is 'rest' at sp_b (sp_ofs + 8) *)
      assert (Hsp_ne_new : sp_b <> new_b).
      { intro Heq; symmetry in Heq; exact (Hnew_ne_sp Heq). }
      assert (Hgb_ne_new : gb <> new_b).
      { intro Heq; symmetry in Heq; exact (Hnew_ne_gb Heq). }

      (* stack_repr for rest in m: from inversion of Hstack_repr *)
      (* Hstack_repr_rest : stack_repr hm m rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) *)

      (* Thread through memories *)
      assert (Hstack_rest_m1 : stack_repr hm cb co m1 rest sp_b new_sp_ofs).
      { eapply (stack_repr_store_other_block hm cb co); eauto. }

      assert (Hstack_rest_alloc : stack_repr hm cb co m_alloc rest sp_b new_sp_ofs).
      { clear -Hstack_rest_m1 Halloc_load_pres Hsp_ne_new.
        induction Hstack_rest_m1 as [| v vs sp_b0 sp_ofs0 cv0 Hld Hvr Htl IH].
        - constructor.
        - econstructor.
          + apply Halloc_load_pres. exact Hld. exact Hsp_ne_new.
          + exact Hvr.
          + apply IH. exact Hsp_ne_new. }

      assert (Hstack_rest_f0 : stack_repr hm cb co m_f0 rest sp_b new_sp_ofs).
      { eapply (stack_repr_store_other_block hm cb co); eauto. }

      assert (Hstack_rest_f1 : stack_repr hm cb co m_f1 rest sp_b new_sp_ofs).
      { eapply (stack_repr_store_other_block hm cb co); eauto. }

      assert (Hstack_rest_m2 : stack_repr hm cb co m2 rest sp_b new_sp_ofs).
      { eapply (stack_repr_store_other_block hm cb co); eauto. }

      assert (Hstack_rest_m3 : stack_repr hm cb co m3 rest sp_b new_sp_ofs).
      { eapply (stack_repr_store_other_block hm cb co); eauto. }

      (* Global repr in m3 *)
      assert (Hglobal_m1 : global_repr hm cb co m1 (Machine.global s) gb go0).
      { eapply (global_repr_store_other_block hm cb co); eauto. }

      assert (Hglobal_alloc : global_repr hm cb co m_alloc (Machine.global s) gb go0).
      { clear -Hglobal_m1 Halloc_load_pres Hgb_ne_new.
        induction Hglobal_m1 as [| v vs gb0 gofs0 cv0 Hld Hvr Htl IH].
        - constructor.
        - econstructor.
          + apply Halloc_load_pres. exact Hld. exact Hgb_ne_new.
          + exact Hvr.
          + apply IH. exact Hgb_ne_new. }

      assert (Hglobal_f0 : global_repr hm cb co m_f0 (Machine.global s) gb go0).
      { eapply (global_repr_store_other_block hm cb co); eauto. }

      assert (Hglobal_f1 : global_repr hm cb co m_f1 (Machine.global s) gb go0).
      { eapply (global_repr_store_other_block hm cb co); eauto. }

      assert (Hglobal_m2 : global_repr hm cb co m2 (Machine.global s) gb go0).
      { eapply (global_repr_store_other_block hm cb co); eauto. }

      assert (Hglobal3 : global_repr hm cb co m3 (Machine.global s) gb go0).
      { eapply (global_repr_store_other_block hm cb co); eauto. }

      (* Now build abs_rel *)
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s in le' *)
      { subst le' le9 le8 le7 le6 le5 le4 le3 le2 le1.
        repeat (rewrite PTree.gso by (compute; congruence)).
        exact Hle_s. }

      (* 2. pc field *)
      { exists new_pc_v. split.
        - exact Hpc_load3.
        - simpl. subst new_pc_v new_pc_ofs.
          apply pc_rel_shift_mk2. }

      (* 3. accu field -- Val_ptr addr *)
      { exists block_v. split.
        - exact Haccu_load3.
        - simpl. eapply val_repr_co_shift. exact Hval_repr_new. }

      (* 4. sp field -- new_sp_v = Vptr sp_b (sp_ofs + 8) *)
      { exists new_sp_v, sp_b, new_sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
        - exact Hsp_load3.
        - reflexivity.
        - simpl. eapply stack_repr_co_shift. apply Hstack_repr_ext. exact Hstack_rest_m3.
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - (* Ptrofs.unsigned new_sp_ofs >= 8 *)
          unfold new_sp_ofs.
          rewrite Ptrofs.add_unsigned.
          rewrite (Ptrofs.unsigned_repr 8).
          2: { unfold Ptrofs.max_unsigned. pose proof Ptrofs.modulus_pos. lia. }
          rewrite Ptrofs.unsigned_repr.
          2: { pose proof (Ptrofs.unsigned_range sp_ofs).
               unfold Ptrofs.max_unsigned.
               rewrite Hstk in Hsp_rep. simpl length in Hsp_rep.
               lia. }
          lia.
        - (* sp representable *)
          unfold new_sp_ofs.
          rewrite Ptrofs.add_unsigned.
          rewrite (Ptrofs.unsigned_repr 8).
          2: { unfold Ptrofs.max_unsigned. pose proof Ptrofs.modulus_pos. lia. }
          rewrite Ptrofs.unsigned_repr.
          2: { pose proof (Ptrofs.unsigned_range sp_ofs).
               unfold Ptrofs.max_unsigned.
               rewrite Hstk in Hsp_rep. simpl length in Hsp_rep.
               lia. }
          simpl Machine.stack. rewrite Hstk in Hsp_rep. simpl length in Hsp_rep.
          lia.
        - split.
          + (* sp_writable *)
            intros ofs0 Hofs0.
            simpl Machine.stack in Hofs0.
            eapply Mem.perm_store_1. exact Hstore_accu.
            eapply Mem.perm_store_1. exact Hstore_sp.
            eapply Hf1_perm_pres.
            eapply Halloc_perm_pres.
            * eapply Mem.perm_valid_block.
              apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc).
              apply (Hsp_writable 0). lia.
            * eapply Mem.perm_store_1. exact Hstore_pc.
              apply Hsp_writable.
              rewrite Hstk. simpl length.
              unfold new_sp_ofs in Hofs0.
              rewrite Ptrofs.add_unsigned in Hofs0.
              rewrite (Ptrofs.unsigned_repr 8) in Hofs0.
              2: { unfold Ptrofs.max_unsigned. pose proof Ptrofs.modulus_pos. lia. }
              rewrite Ptrofs.unsigned_repr in Hofs0.
              2: { pose proof (Ptrofs.unsigned_range sp_ofs).
                   unfold Ptrofs.max_unsigned.
                   rewrite Hstk in Hsp_rep. simpl length in Hsp_rep.
                   lia. }
              lia.
          + (* sp_align *)
            unfold new_sp_ofs.
            destruct Hsp_align as [k Hk].
            exists (k + 1). rewrite Ptrofs.add_unsigned.
            rewrite (Ptrofs.unsigned_repr 8).
            2: { unfold Ptrofs.max_unsigned. pose proof Ptrofs.modulus_pos. lia. }
            rewrite Ptrofs.unsigned_repr.
            2: { pose proof (Ptrofs.unsigned_range sp_ofs).
                 unfold Ptrofs.max_unsigned.
                 rewrite Hstk in Hsp_rep. simpl length in Hsp_rep.
                 lia. }
            change (align_chunk Mint64) with 8%Z in Hk |- *.
            lia.
      }

      (* 5. env field -- unchanged *)
      { exists env_v. split.
        - exact Henv_load3.
        - simpl. eapply val_repr_co_shift. apply Hval_repr_ext. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { simpl. exact Hextra_load3. }

      (* 7. global_data field -- unchanged *)
      { exists (Vptr gb go0). split; [| split; [| split]].
        - exact Hgd_load3.
        - simpl. reflexivity.
        - simpl. eapply global_repr_co_shift. apply Hglobal_repr_ext. exact Hglobal3.
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load3.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable *)
      { intros ofs0 Hofs0.
        eapply Mem.perm_store_1. exact Hstore_accu.
        eapply Mem.perm_store_1. exact Hstore_sp.
        eapply Hf1_perm_pres.
        eapply Halloc_perm_pres.
        - eapply Mem.perm_valid_block.
          apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc).
          apply (Hsb_writable (Ptrofs.unsigned so)). lia.
        - eapply Mem.perm_store_1. exact Hstore_pc.
          apply Hsb_writable. exact Hofs0. }
    }
Qed.

Definition MAKEBLOCK2_correct_for_spec : forall t, 0 <= Z.of_nat t <= 255 ->
    handler_correct (handle_MAKEBLOCK2 t) f_instr_MAKEBLOCK2
      (heap_alloc_with_stores 2 (Z.of_nat t) alloc_store_2
       /\p code_at (Int.repr (Z.of_nat t)))
      (fun _ s => match s.(Machine.stack) with _ :: _ => False | _ => True end)
      (fun _ => False) (fun _ _ _ => False).
  Proof.
    intros t Hrange. eapply handler_correct_weaken.
    - exact (verify_MAKEBLOCK2_correct t).
    - intros e le m s ard _ [[Hhap Hsu] Hcode].
      unfold heap_alloc_pre in Hhap.
      destruct Hhap as (H0 & H2 & H3 & H4 & H5).
      split; [exact H0|]. split; [exact Hcode|]. split; [exact Hrange|].
      split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
      intros m'. destruct (H5 m') as (ma & nb & no & He & Hf & Hl & Hp).
      exists ma, nb, no.
      split; [exact He|]. split; [exact Hf|]. split; [exact Hl|].
      split; [exact Hp|].
      (* alloc_store_2 has 5 inner conjuncts; MAKEBLOCK2 inline has 4 (no field0-load-pres) *)
      pose proof (Hsu m' ma nb no He Hf Hl Hp) as Has2.
      intros cv. destruct (Has2 cv) as (ms & Hs & Hld & Hld_other & Hinner).
      exists ms. split; [exact Hs|]. split; [exact Hld|]. split; [exact Hld_other|].
      intros cv1. destruct (Hinner cv1) as (ms1 & Hs1 & Hld1 & _ & Hld1_other & Hperm).
      exists ms1. split; [exact Hs1|]. split; [exact Hld1|]. split; [exact Hld1_other|].
      exact Hperm.
  Qed.
