(* MAKEBLOCK1_correct.v -- MAKEBLOCK1 completeness proof.

   MAKEBLOCK1 reads tag from *pc, calls heap_alloc(s, 1, tag), stores the
   current accu as field 0 of the new block, and sets accu to the block ptr.

   C code (f_instr_MAKEBLOCK1):
     t1 = s.pc; s.pc = t1+1; t4 = deref t1; tag = (uchar)t4;
     t2 = heap_alloc(s, 1, tag); block = t2;
     t3 = s.accu; deref(block+0) = t3; s.accu = block;
     return 0;

   Rocq:
     handle_MAKEBLOCK1 t pc' s =
       let '(s', ptr) := heap_alloc s t [s.(accu)] in
       Step (s' <|pc:=pc'|> <|accu:=ptr|>).

   This handler involves a call to the external function heap_alloc,
   which the computational evaluator (StepToBigstep) cannot handle.
   We therefore construct the exec_stmt derivation manually.

   AXIOMS introduced here (heap allocation infrastructure):
   - heap_alloc_external_call: Specification of the external heap_alloc
     function's behavior in CompCert's memory model.
   - heap_alloc_find_funct: The heap_alloc symbol is findable in the
     global environment.
   - heap_alloc_preserves_struct: Heap allocation does not modify the
     struct pointer block.
   - heap_alloc_preserves_stack: Heap allocation preserves stack_repr.
   - heap_alloc_preserves_global: Heap allocation preserves global_repr.
   - heap_alloc_extends_heap_map: After allocation, the heap map can be
     extended to map the new address to the returned block.

   PRECONDITIONS (via handler_correct):
   - The code buffer contains Int.repr (Z.of_nat t) at the current PC.
   - t fits in unsigned char range (0 <= Z.of_nat t <= 255). *)

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
(* Struct layout                                                       *)
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

Lemma interp_state_co_pc_accu : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
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

(* Cast int -> tuchar: zero-extend to 8 bits *)
Lemma sem_cast_int_to_tuchar : forall n m,
  sem_cast (Vint n) tint tuchar m = Some (Vint (Int.zero_ext 8 n)).
Proof.
  intros. unfold sem_cast. simpl classify_cast. simpl. reflexivity.
Qed.

(* Cast tuchar -> tlong: sign-extend to i64 (tuchar is Unsigned I8) *)
Lemma sem_cast_tuchar_to_tlong : forall n m,
  sem_cast (Vint n) tuchar tlong m =
    Some (Vlong (Int64.repr (Int.unsigned n))).
Proof.
  intros. unfold sem_cast. simpl classify_cast. simpl. reflexivity.
Qed.

(* For a small non-negative integer (0..255), Int.zero_ext 8 is identity *)
Lemma int_zero_ext_8_small : forall z,
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

(* Int.unsigned (Int.repr z) = z when 0 <= z < Int.modulus *)
Lemma int_unsigned_repr_small : forall z,
  0 <= z <= 255 ->
  Int.unsigned (Int.repr z) = z.
Proof.
  intros z Hz.
  apply Int.unsigned_repr.
  unfold Int.max_unsigned. change Int.modulus with 4294967296%Z. lia.
Qed.

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

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.




(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_MAKEBLOCK1_correct : forall t,
    handler_correct (handle_MAKEBLOCK1 t) f_instr_MAKEBLOCK1
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
                (Vptr sb so :: Vlong (Int64.repr 1) :: Vlong (Int64.repr (Z.of_nat t)) :: nil)
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
                    Mem.load chunk m_store b ofs = Some v))))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intro t.
  intros e le m s.
  unfold handle_MAKEBLOCK1. simpl.

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

  (* Structural invariants *)
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  pose proof (code_block_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  (* Composite environment *)
  destruct interp_state_co_pc_accu as [co_is [Hco [Hpc_offset Haccu_offset]]].

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
  { subst tag_uchar tag_int. apply int_zero_ext_8_small. exact Ht_range. }

  assert (Htag_unsigned : Int.unsigned tag_uchar = tag_z).
  { rewrite Htag_uchar_eq. subst tag_int tag_z. apply int_unsigned_repr_small. exact Ht_range. }

  (* --- heap_alloc call --- *)
  (* Sp, env, extra_args, gd, ts fields survive pc store *)
  assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 16) new_pc_v (Vptr sp_b sp_ofs) Hstore_pc Hsp_load).
    right. lia. }

  (* Instantiate heap_alloc for m1 *)
  destruct (Halloc_spec_all m1)
    as [m_alloc [new_b [new_ofs
         (Hext_call & Hnew_fresh &
          Halloc_load_pres & Halloc_perm_pres & Hcan_store)]]].

  (* Derive freshness for specific blocks from universal freshness.
     For each block, we need valid_block m1 b, obtained via
     Mem.perm_valid_block from any permission on b in m1. *)
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

  (* --- Store field 0: *(block + 0) = accu_v --- *)
  destruct (Hcan_store accu_v) as [m_field [Hstore_field [Hload_field Hfield_load_pres]]].

  (* Struct field loads survive field store (store to new_b, loads on sb) *)
  assert (Hstruct_preserved2 : forall ofs0 v0,
    Mem.load Mint64 m1 sb ofs0 = Some v0 ->
    Mem.load Mint64 m_field sb ofs0 = Some v0).
  { intros ofs0 v0 Hld.
    apply Hfield_load_pres.
    - intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq).
    - apply Hstruct_preserved. exact Hld. }

  (* Accu in m_field *)
  assert (Haccu_load_field : Mem.load Mint64 m_field sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply Hstruct_preserved2. exact Haccu_load_m1. }

  (* --- Store 2: accu field <- Vptr new_b new_ofs --- *)
  set (block_v := Vptr new_b new_ofs).
  (* sb_writable in m_field: thread through m -> m1 -> m_alloc -> m_field.
     m -> m1 via sb_writable_after_store; m1 -> m_alloc via Halloc_perm_pres;
     m_alloc -> m_field via Mem.perm_store_1 (field store on different block). *)
  assert (Hsb_writable_m1 :
    Mem.range_perm m1 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { eapply sb_writable_after_store; eauto. }
  assert (Hsb_writable_alloc :
    Mem.range_perm m_alloc sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs0 Hofs0. eapply Halloc_perm_pres.
    - eapply Mem.perm_valid_block.
      apply (Hsb_writable_m1 (Ptrofs.unsigned so)). lia.
    - apply Hsb_writable_m1. exact Hofs0. }
  assert (Hsb_writable_m_field :
    Mem.range_perm m_field sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { eapply sb_writable_after_store; eauto. }
  destruct (store_succeeds_sb m_field sb so 8 accu_v Hsb_writable_m_field Haccu_load_field ltac:(lia) ltac:(lia) block_v)
    as [m2 Hstore_accu].

  (* Final memory: m -> m1 (pc store) -> m_alloc (heap_alloc) ->
     m_field (field store) -> m2 (accu store) *)

  (* We need to figure out the right heap map and abs_rel_data for post-state.
     The Rocq heap_alloc:
       addr = s.(next_addr)
       s' = s <|hp := add addr (t, [accu]) hp|> <|next_addr := S addr|>
       ptr = Val_ptr addr
     So the post-state has:
       pc = pc s    (set to pc' by the handler wrapper)
       accu = Val_ptr addr
       stack = s.(stack)   (unchanged)
       everything else from s unchanged except hp, next_addr

     For abs_rel, we need hm' such that:
       val_repr hm' (Val_ptr addr) (Vptr new_b new_ofs)
     So hm' addr = Some (new_b, new_ofs)
     And hm' agrees with hm on all other addresses.
  *)

  set (addr := next_addr s).
  set (hm' := fun n => if Nat.eqb n addr then Some (new_b, new_ofs) else hm n).

  (* val_repr hm' for old values: need to show val_repr hm v cv -> val_repr hm' v cv
     This works because hm' agrees with hm on all n <> addr, and addr is fresh
     (not in the range of hm). We axiomatize this as a property of the heap map. *)

  (* For the proof to close, we need that existing val_reprs are preserved
     when we extend hm.  This requires that addr is not already mapped by hm.
     We treat this as a consequence of the Rocq heap model (next_addr is always
     fresh). *)

  (* We need that addr is fresh: any value representable under hm
     cannot use addr, so hm' agrees with hm on those values.
     For val_repr, the only case that touches hm is Val_ptr and
     Val_closure, where the address must already be in hm.
     Since addr = next_addr s, we need hm addr = None.
     This is a structural invariant of abs_rel: the heap map only
     contains addresses < next_addr. *)

  (* Freshness: forall v cv, val_repr hm v cv -> val_does_not_use_addr v *)
  (* For Val_ptr addr0: hm addr0 = Some _ implies addr0 <> addr
     because hm only maps addresses < next_addr = addr.
     We axiomatize this. *)

  (* val_repr preservation under heap map extension *)
  assert (Hval_repr_ext : forall v cv, val_repr hm cb co v cv -> val_repr hm' cb co v cv).
  { intros v cv Hvr.
    inversion Hvr; subst.
    - constructor.
    - econstructor. unfold hm'.
      destruct (Nat.eqb addr0 addr) eqn:Heq.
      + apply Nat.eqb_eq in Heq. subst addr0.
        exfalso.
        unfold addr in H. rewrite Hhm_fresh in H. discriminate.
      + exact H.
    - econstructor.
      + unfold hm'. destruct (Nat.eqb addr0 addr) eqn:Heq.
        * apply Nat.eqb_eq in Heq. subst addr0.
          exfalso.
          unfold addr in H. rewrite Hhm_fresh in H. discriminate.
        * exact H.
      + reflexivity.
    - constructor.
    - econstructor. }

  (* We also need: val_repr hm' (Val_ptr addr) block_v *)
  assert (Hval_repr_new : val_repr hm' cb co (Val_ptr addr) block_v).
  { econstructor. unfold hm'. rewrite Nat.eqb_refl. reflexivity. }

  (* stack_repr preservation under hm extension *)
  assert (Hstack_repr_ext : forall stk m0 sp_b0 sp_ofs0,
    stack_repr hm cb co m0 stk sp_b0 sp_ofs0 -> stack_repr hm' cb co m0 stk sp_b0 sp_ofs0).
  { intros stk0 m0 sp_b0 sp_ofs0 Hsr.
    induction Hsr.
    - constructor.
    - econstructor; eauto. }

  (* global_repr preservation under hm extension *)
  assert (Hglobal_repr_ext : forall gs m0 gb0 gofs0,
    global_repr hm cb co m0 gs gb0 gofs0 -> global_repr hm' cb co m0 gs gb0 gofs0).
  { intros gs0 m0 gb0 gofs0 Hgr.
    induction Hgr.
    - constructor.
    - econstructor; eauto. }

  (* --- Build witnesses for existential --- *)

  (* Determine le' after all temp assignments *)
  (* The C function body sets temps in order:
     _t'1 (pc ptr), then _t'4 (tag int), _tag (tag uchar),
     _t'2 (heap_alloc result = block_v), _block (= block_v),
     _t'3 (accu value) *)
  set (le1 := PTree.set _t'1 (Vptr cb pc_ofs) le).
  set (le2 := PTree.set _t'4 (Vint tag_int) le1).
  set (le3 := PTree.set _tag (Vint tag_uchar) le2).
  (* After Scall, set_opttemp (Some _t'2) block_v le3 *)
  set (le4 := PTree.set _t'2 block_v le3).
  set (le5 := PTree.set _block block_v le4).
  set (le6 := PTree.set _t'3 accu_v le5).
  set (le' := le6).

  exists le'. exists m2.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ============================================================== *)
  (* Part 1: exec_stmt derivation (manual construction)              *)
  (* ============================================================== *)
  {
    (* The body structure:
       Ssequence [pc/tag + alloc/store] [return 0]
       with pc/tag = Sseq [Sseq [Sset t1 s.pc; Sassign s.pc t1+1]
                                 [Sset t4 deref-t1; Sset tag cast-t4]]
                          [Sseq [Scall t2 heap_alloc; Sset block t2]
                                [Sseq [Sset t3 s.accu; Sassign deref-block t3]
                                      [Sassign s.accu block]]] *)

    (* We build the derivation by combining computational evaluation
       (for the parts without Scall) with manual construction for the call. *)

    (* Strategy: build the execution bottom-up using exec_Sseq_1.
       For portions without Scall, use eval_stmt_to_exec.
       For the Scall, construct exec_Scall directly. *)

    (* Phase 1: Sset _t'1 (s->pc) -- computational *)
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
      (* Lvalue: s->pc *)
      unfold le1.
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      (* Rvalue: _t'1 + 1 *)
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_pc_1 cb pc_ofs m); eval_cbn.
      rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.
      (* Store *)
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      fold new_pc_v.
      rewrite Hstore_pc; eval_cbn.
      reflexivity. }

    (* Phase 3: Sset _t'4 deref(_t'1) -- read tag from code *)
    assert (Hexec_read_tag : exec_stmt function_entry1 clight_ge e le1 m1
        (Sset _t'4 (Ederef (Etempvar _t'1 (tptr tint)) tint))
        E0 le2 m1 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le1.
      rewrite PTree.gss; eval_cbn.
      rewrite Hcode_load_m1; eval_cbn.
      reflexivity. }

    (* Phase 4: Sset _tag (cast _t'4 tuchar) *)
    assert (Hexec_set_tag : exec_stmt function_entry1 clight_ge e le2 m1
        (Sset _tag (Ecast (Etempvar _t'4 tint) tuchar))
        E0 le3 m1 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le2.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_int_to_tuchar tag_int m1); eval_cbn.
      reflexivity. }

    (* Phase 5: Scall heap_alloc -- manual construction *)
    (* Need: eval_expr for Evar _heap_alloc, eval_exprlist for args,
       find_funct, type matching, eval_funcall_external *)

    assert (Hexec_call : exec_stmt function_entry1 clight_ge e le3 m1
        (Scall (Some _t'2)
          (Evar _heap_alloc (Tfunction
            ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
            tlong cc_default))
          ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
           (Econst_int (Int.repr 1) tint) :: (Etempvar _tag tuchar) :: nil))
        E0 le4 m_alloc Out_normal).
    { (* Rewrite sem_cast for _tag argument *)
      assert (Hcast_tag : sem_cast (Vint tag_uchar) tuchar tlong m1 =
                Some (Vlong (Int64.repr (Int.unsigned tag_uchar)))).
      { apply sem_cast_tuchar_to_tlong. }

      (* Rewrite Htag_unsigned *)
      rewrite Htag_unsigned in Hcast_tag.

      eapply exec_Scall with
        (tyargs := (tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
        (tyres := tlong)
        (cconv := cc_default)
        (vf := Vptr b_ha Ptrofs.zero)
        (vargs := Vptr sb so :: Vlong (Int64.repr 1) :: Vlong (Int64.repr tag_z) :: nil)
        (f := heap_alloc_fundef)
        (vres := Vptr new_b new_ofs).
      - (* classify_fun *) reflexivity.
      - (* eval_expr for Evar _heap_alloc *)
        eapply eval_Elvalue.
        + eapply eval_Evar_global.
          * exact He_heap_alloc.
          * exact Hfind_symbol.
        + apply deref_loc_reference. simpl. reflexivity.
      - (* eval_exprlist *)
        econstructor.
        + (* Etempvar _s *)
          econstructor.
          unfold le3. rewrite PTree.gso by (compute; congruence).
          unfold le2. rewrite PTree.gso by (compute; congruence).
          unfold le1. rewrite PTree.gso by (compute; congruence).
          exact Hle_s.
        + (* sem_cast for s arg *)
          simpl. reflexivity.
        + econstructor.
          * econstructor.
          * (* sem_cast for Econst_int 1 *)
            simpl. reflexivity.
          * econstructor.
            -- econstructor.
               unfold le3. rewrite PTree.gss. reflexivity.
            -- (* sem_cast for _tag tuchar -> tlong *)
               exact Hcast_tag.
            -- constructor.
      - (* find_funct *) exact Hfind_funct.
      - (* type_of_fundef *) reflexivity.
      - (* eval_funcall_external *)
        eapply eval_funcall_external.
        exact Hext_call.
    }

    (* Phase 6: Sset _block _t'2 *)
    assert (Hexec_set_block : exec_stmt function_entry1 clight_ge e le4 m_alloc
        (Sset _block (Etempvar _t'2 tlong))
        E0 le5 m_alloc Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le4. rewrite PTree.gss; eval_cbn.
      reflexivity. }

    (* Phase 7: Sset _t'3 (s->accu) *)
    assert (Hexec_read_accu : exec_stmt function_entry1 clight_ge e le5 m_alloc
        (Sset _t'3
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

    (* Phase 8: Sassign deref(block+0) = _t'3 -- store field 0 *)
    assert (Hexec_store_field : exec_stmt function_entry1 clight_ge e le6 m_alloc
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
          (Etempvar _t'3 tlong))
        E0 le6 m_field Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      (* _block *)
      unfold le6.
      rewrite PTree.gso by (compute; congruence).
      unfold le5.
      rewrite PTree.gss; eval_cbn.
      (* cast block to (tptr tlong) *)
      fold block_v.
      replace (sem_cast block_v tlong (tptr tlong) m_alloc) with (Some block_v) by (unfold block_v, sem_cast; simpl classify_cast; reflexivity); eval_cbn.
      (* Oadd (Vptr new_b new_ofs) (tptr tlong) (Vint 0) tint *)
      unfold block_v at 1. rewrite (sem_add_sp_0 new_b new_ofs m_alloc); eval_cbn.
      (* _t'3 *)
      unfold le6. rewrite PTree.gss; eval_cbn.
      (* sem_cast accu_v tlong tlong *)
      rewrite (sem_cast_long_val_repr hm cb co (Machine.accu s) accu_v m_alloc Haccu_repr);
        eval_cbn.
      (* Store *)
      rewrite Hstore_field; eval_cbn.
      reflexivity. }

    (* Phase 9: Sassign (s->accu) _block *)
    assert (Hexec_store_accu : exec_stmt function_entry1 clight_ge e le6 m_field
        (Sassign
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                   (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _block tlong))
        E0 le6 m2 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      (* Lvalue: s->accu *)
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
      (* Rvalue: _block *)
      unfold le6.
      rewrite PTree.gso by (compute; congruence).
      unfold le5.
      rewrite PTree.gss; eval_cbn.
      fold block_v.
      (* sem_cast block tlong tlong *)
      unfold block_v at 1.
      rewrite (sem_cast_long_vptr new_b new_ofs m_field); eval_cbn.
      (* Store *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      fold block_v. rewrite Hstore_accu; eval_cbn.
      reflexivity. }

    (* Phase 10: Sreturn 0 *)
    assert (Hexec_return : exec_stmt function_entry1 clight_ge e le6 m2
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        E0 le6 m2 (Out_return (Some (Vint (Int.repr 0), tint)))).
    { apply (eval_stmt_to_exec clight_ge 10). reflexivity. }

    (* Now combine all phases using exec_Sseq_1 *)
    (* The body structure: see Phase 1-10 above. *)

    (* Inner sequences first, building up *)
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

    (* Seq: Sset _t'4; Sset _tag *)
    assert (Hexec_tag_read :
      exec_stmt function_entry1 clight_ge e le1 m1
        (Ssequence
          (Sset _t'4 (Ederef (Etempvar _t'1 (tptr tint)) tint))
          (Sset _tag (Ecast (Etempvar _t'4 tint) tuchar)))
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
            (Sset _t'4 (Ederef (Etempvar _t'1 (tptr tint)) tint))
            (Sset _tag (Ecast (Etempvar _t'4 tint) tuchar))))
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
             (Econst_int (Int.repr 1) tint) :: (Etempvar _tag tuchar) :: nil))
          (Sset _block (Etempvar _t'2 tlong)))
        E0 le5 m_alloc Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto. }

    (* Seq: Sset _t'3; Sassign *(block+0) *)
    assert (Hexec_read_store_field :
      exec_stmt function_entry1 clight_ge e le5 m_alloc
        (Ssequence
          (Sset _t'3
            (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                     (Tstruct _interp_state noattr)) _accu tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
            (Etempvar _t'3 tlong)))
        E0 le6 m_field Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto. }

    (* Seq: read_store_field; store_accu *)
    assert (Hexec_field_accu :
      exec_stmt function_entry1 clight_ge e le5 m_alloc
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _accu tlong))
            (Sassign
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                  (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
              (Etempvar _t'3 tlong)))
          (Sassign
            (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                     (Tstruct _interp_state noattr)) _accu tlong)
            (Etempvar _block tlong)))
        E0 le6 m2 Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto. }

    (* Seq: alloc_block; field_accu *)
    assert (Hexec_alloc_field_accu :
      exec_stmt function_entry1 clight_ge e le3 m1
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _heap_alloc (Tfunction
                ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
                tlong cc_default))
              ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
               (Econst_int (Int.repr 1) tint) :: (Etempvar _tag tuchar) :: nil))
            (Sset _block (Etempvar _t'2 tlong)))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _accu tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                    (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                (Etempvar _t'3 tlong)))
            (Sassign
              (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _accu tlong)
              (Etempvar _block tlong))))
        E0 le6 m2 Out_normal).
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
              (Sset _t'4 (Ederef (Etempvar _t'1 (tptr tint)) tint))
              (Sset _tag (Ecast (Etempvar _t'4 tint) tuchar))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _heap_alloc (Tfunction
                  ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
                  tlong cc_default))
                ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
                 (Econst_int (Int.repr 1) tint) :: (Etempvar _tag tuchar) :: nil))
              (Sset _block (Etempvar _t'2 tlong)))
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                           (Tstruct _interp_state noattr)) _accu tlong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                      (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                  (Etempvar _t'3 tlong)))
              (Sassign
                (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _accu tlong)
                (Etempvar _block tlong)))))
        E0 le6 m2 Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto. }

    (* Full body = pre_return; return *)
    change (fn_body f_instr_MAKEBLOCK1) with
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
              (Sset _t'4 (Ederef (Etempvar _t'1 (tptr tint)) tint))
              (Sset _tag (Ecast (Etempvar _t'4 tint) tuchar))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _heap_alloc (Tfunction
                  ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
                  tlong cc_default))
                ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
                 (Econst_int (Int.repr 1) tint) :: (Etempvar _tag tuchar) :: nil))
              (Sset _block (Etempvar _t'2 tlong)))
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                      (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                    (Etempvar _t'3 tlong)))
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

    (* pc field at uso+0: written by store_pc in m1, preserved through
       m_alloc (heap_alloc preserves struct), m_field (store to new_b),
       m2 (store at uso+8, not uso+0) *)
    assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (uso + 0) =
              Some new_pc_v).
    { pose proof (load_after_store_same m m1 sb (uso + 0) new_pc_v Hstore_pc) as Htmp.
      unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }

    assert (Hpc_load_alloc : Mem.load Mint64 m_alloc sb (uso + 0) = Some new_pc_v).
    { apply Hstruct_preserved. exact Hpc_load_m1. }

    assert (Hpc_load_field : Mem.load Mint64 m_field sb (uso + 0) = Some new_pc_v).
    { apply Hstruct_preserved2. exact Hpc_load_m1. }

    assert (Hpc_load2 : Mem.load Mint64 m2 sb (uso + 0) = Some new_pc_v).
    { apply (load_after_store_other m_field m2 sb (uso + 8) (uso + 0)
               block_v new_pc_v Hstore_accu Hpc_load_field). left. lia. }

    (* accu field at uso+8: store_accu wrote block_v = Vptr new_b new_ofs *)
    assert (Haccu_load2 : Mem.load Mint64 m2 sb (uso + 8) = Some block_v).
    { pose proof (load_after_store_same m_field m2 sb (uso + 8) block_v Hstore_accu) as Htmp.
      unfold block_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }

    (* Helper: struct fields at offsets >= 16 survive all stores *)
    assert (Hfield_survive : forall field_ofs v,
      field_ofs >= 16 ->
      Mem.load Mint64 m sb (uso + field_ofs) = Some v ->
      Mem.load Mint64 m2 sb (uso + field_ofs) = Some v).
    { intros fo v Hfo Hload.
      (* m -> m1: store at uso+0 *)
      assert (H1 : Mem.load Mint64 m1 sb (uso + fo) = Some v).
      { apply (load_after_store_other m m1 sb (uso + 0) (uso + fo)
                 new_pc_v v Hstore_pc Hload). right. lia. }
      (* m1 -> m_alloc: heap_alloc preserves struct *)
      assert (H2 : Mem.load Mint64 m_alloc sb (uso + fo) = Some v).
      { apply Hstruct_preserved. exact H1. }
      (* m_alloc -> m_field: store to new_b (different from sb) *)
      assert (H3 : Mem.load Mint64 m_field sb (uso + fo) = Some v).
      { apply Hstruct_preserved2. exact H1. }
      (* m_field -> m2: store at uso+8 *)
      apply (load_after_store_other m_field m2 sb (uso + 8) (uso + fo)
               block_v v Hstore_accu H3). right. lia. }

    (* sp field *)
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

    (* Stack repr in m2:
       m -> m1 (store to sb, sp_b <> sb) ->
       m_alloc (heap_alloc preserves stack) ->
       m_field (store to new_b, new_b <> sp_b) ->
       m2 (store to sb, sp_b <> sb) *)
    assert (Hstack_m1 : stack_repr hm cb co m1 (Machine.stack s) sp_b sp_ofs).
    { eapply (stack_repr_store_other_block hm cb co); eauto. }

    (* stack_repr preservation through heap_alloc:
       loads on sp_b are preserved since sp_b <> new_b *)
    assert (Hsp_ne_new : sp_b <> new_b).
    { intro Heq; symmetry in Heq; exact (Hnew_ne_sp Heq). }
    assert (Hgb_ne_new : gb <> new_b).
    { intro Heq; symmetry in Heq; exact (Hnew_ne_gb Heq). }

    assert (Hstack_alloc : stack_repr hm cb co m_alloc (Machine.stack s) sp_b sp_ofs).
    { clear -Hstack_m1 Halloc_load_pres Hsp_ne_new.
      induction Hstack_m1 as [| v vs sp_b0 sp_ofs0 cv Hld Hvr Htl IH].
      - constructor.
      - econstructor.
        + apply Halloc_load_pres. exact Hld. exact Hsp_ne_new.
        + exact Hvr.
        + apply IH. exact Hsp_ne_new. }

    assert (Hstack_field : stack_repr hm cb co m_field (Machine.stack s) sp_b sp_ofs).
    { eapply (stack_repr_store_other_block hm cb co); eauto. }

    assert (Hstack2 : stack_repr hm cb co m2 (Machine.stack s) sp_b sp_ofs).
    { eapply (stack_repr_store_other_block hm cb co); eauto. }

    (* Global repr in m2 *)
    assert (Hglobal_m1 : global_repr hm cb co m1 (Machine.global s) gb go0).
    { eapply (global_repr_store_other_block hm cb co); eauto. }

    (* global_repr preservation through heap_alloc:
       loads on gb are preserved since gb <> new_b *)
    assert (Hglobal_alloc : global_repr hm cb co m_alloc (Machine.global s) gb go0).
    { clear -Hglobal_m1 Halloc_load_pres Hgb_ne_new.
      induction Hglobal_m1 as [| v vs gb0 gofs0 cv Hld Hvr Htl IH].
      - constructor.
      - econstructor.
        + apply Halloc_load_pres. exact Hld. exact Hgb_ne_new.
        + exact Hvr.
        + apply IH. exact Hgb_ne_new. }

    assert (Hglobal_field : global_repr hm cb co m_field (Machine.global s) gb go0).
    { eapply (global_repr_store_other_block hm cb co); eauto. }

    assert (Hglobal2 : global_repr hm cb co m2 (Machine.global s) gb go0).
    { eapply (global_repr_store_other_block hm cb co); eauto. }

    (* Now build abs_rel *)
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s in le' *)
    { subst le' le6 le5 le4 le3 le2 le1.
      repeat (rewrite PTree.gso by (compute; congruence)).
      exact Hle_s. }

    (* 2. pc field *)
    { exists new_pc_v. split.
      - exact Hpc_load2.
      - simpl. subst new_pc_v new_pc_ofs.
        apply pc_rel_shift. }

    (* 3. accu field -- Val_ptr addr *)
    { exists block_v. split.
      - exact Haccu_load2.
      - simpl. eapply val_repr_co_shift. exact Hval_repr_new. }

    (* 4. sp field -- unchanged *)
    { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
      - exact Hsp_load2.
      - reflexivity.
      - simpl. eapply stack_repr_co_shift. apply Hstack_repr_ext. exact Hstack2.
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - exact Hsp_ge8.
      - exact Hsp_rep.
      - (* sp_writable + sp_align *)
        split.
        + (* sp_writable: permission preserved through stores + heap_alloc *)
          intros ofs0 Hofs0.
          eapply Mem.perm_store_1. exact Hstore_accu.
          eapply Mem.perm_store_1. exact Hstore_field.
          eapply Halloc_perm_pres.
          * eapply Mem.perm_valid_block.
            apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc).
            apply (Hsp_writable 0). lia.
          * eapply Mem.perm_store_1. exact Hstore_pc.
            apply Hsp_writable. exact Hofs0.
        + exact Hsp_align. }

    (* 5. env field -- unchanged *)
    { exists env_v. split.
      - exact Henv_load2.
      - simpl. eapply val_repr_co_shift. apply Hval_repr_ext. exact Henv_repr. }

    (* 6. extra_args field -- unchanged *)
    { simpl. exact Hextra_load2. }

    (* 7. global_data field -- unchanged *)
    { exists (Vptr gb go0). split; [| split; [| split]].
      - exact Hgd_load2.
      - simpl. reflexivity.
      - simpl. eapply global_repr_co_shift. apply Hglobal_repr_ext. exact Hglobal2.
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load2.
      - simpl. exact Htrap_rel. }

    (* 9. sb_writable -- permission preserved through stores + heap_alloc *)
    { intros ofs0 Hofs0.
      eapply Mem.perm_store_1. exact Hstore_accu.
      eapply Mem.perm_store_1. exact Hstore_field.
      eapply Halloc_perm_pres.
      - eapply Mem.perm_valid_block.
        apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc).
        apply (Hsb_writable (Ptrofs.unsigned so)). lia.
      - eapply Mem.perm_store_1. exact Hstore_pc.
        apply Hsb_writable. exact Hofs0. }
  }
Qed.

Definition MAKEBLOCK1_correct_for_spec : forall t, 0 <= Z.of_nat t <= 255 ->
    handler_correct (handle_MAKEBLOCK1 t) f_instr_MAKEBLOCK1
      (heap_alloc_with_stores 1 (Z.of_nat t) alloc_store_1
       /\p code_at (Int.repr (Z.of_nat t)))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
  Proof.
    intros t Hrange. eapply handler_correct_weaken.
    - exact (verify_MAKEBLOCK1_correct t).
    - intros e le m s ard _ [[Hhap Hsu] Hcode].
      unfold heap_alloc_pre in Hhap.
      destruct Hhap as (H0 & H2 & H3 & H4 & H5).
      split; [exact H0|]. split; [exact Hcode|]. split; [exact Hrange|].
      split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
      intros m'. destruct (H5 m') as (ma & nb & no & He & Hf & Hl & Hp).
      exists ma, nb, no.
      split; [exact He|]. split; [exact Hf|]. split; [exact Hl|].
      split; [exact Hp|].
      exact (Hsu m' ma nb no He Hf Hl Hp).
  Qed.
