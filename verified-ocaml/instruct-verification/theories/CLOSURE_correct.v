(* CLOSURE_correct.v -- CLOSURE handler completeness proof.

   CLOSURE reads nvars and code_ofs from the code buffer, optionally pushes
   accu onto the stack (if nvars > 0), allocates a closure block of size
   (nvars + 2) with tag 247 (Closure_tag), copies nvars env variables from
   the stack to the block, stores the code pointer and closinfo, advances
   pc, restores sp, and sets accu to the new closure.

   This proof handles the nvars = 0 case (no env variables to copy).
   The C if-branch (nvars > 0) is skipped, and the for-loop executes
   0 iterations.  The heap_alloc call allocates a 2-field block.

   Rocq handle_CLOSURE 0 code_ofs pc' s:
     let stk := s.(stack) in
     let fields := [Val_int code_ofs; Val_int 0] in
     let '(s', base_ptr) := heap_alloc s Closure_tag fields in
     let addr := ... in
     Step (s' <|pc:=pc'|> <|accu:=Val_closure addr 0|> <|stack:=stk|>). *)

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
Require Import ExternalCallSpecs.

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

Lemma sem_add_pc_1_closure : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint_cl : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* Cast Vint -> tint -> tint is identity *)
Lemma sem_cast_int_tint_tint : forall n m,
  sem_cast (Vint n) tint tint m = Some (Vint n).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* Oadd (Vint a) tint (Vint b) tint = Some (Vint (Int.add a b)) *)
Lemma sem_add_int_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vint a) tint (Vint b) tint m = Some (Vint (Int.add a b)).
Proof. intros. reflexivity. Qed.

(* Ogt (Vint n) tint (Vint 0) tint comparison *)
Lemma sem_cmp_gt_int_0 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Ogt
    (Vint n) tint
    (Vint (Int.repr 0)) tint
    m = Some (Val.of_bool (Int.lt (Int.repr 0) n)).
Proof. intros. reflexivity. Qed.

(* Olt (Vint i) tint (Vint n) tint comparison *)
Lemma sem_cmp_lt_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Olt
    (Vint a) tint
    (Vint b) tint
    m = Some (Val.of_bool (Int.lt a b)).
Proof. intros. reflexivity. Qed.

(* Oshl (Vint a) tint (Vint b) tint *)
Lemma sem_shl_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vint n) tint (Vint (Int.repr 1)) tint m =
    Some (Vint (Int.shl n (Int.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tint tint) with (shift_case_ii Signed).
  simpl.
  change (Int.ltu (Int.repr 1) Int.iwordsize) with true.
  reflexivity.
Qed.

(* Cast Vint -> tint -> tlong *)
Lemma sem_cast_int_to_tlong : forall n m,
  sem_cast (Vint n) tint tlong m = Some (Vlong (Int64.repr (Int.signed n))).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* Cast Vptr -> tlong -> tptr tlong *)
Lemma sem_cast_vptr_tlong_to_ptr_tlong : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* Cast Vptr -> tlong -> tptr (tptr tint) *)
Lemma sem_cast_vptr_tlong_to_ptr_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr (tptr tint)) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* Oadd (Vptr b ofs) (tptr (tptr tint)) (Vint 0) tint *)
Lemma sem_add_ptr_ptr_tint_0 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr (tptr tint))
    (Vint (Int.repr 0)) tint
    m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr (tptr tint)) tint) with (add_case_pi (tptr tint) Signed).
  unfold sem_add_ptr_int. f_equal. f_equal.
  change (sizeof (genv_cenv clight_ge) (tptr tint)) with 8%Z.
  unfold ptrofs_of_int.
  change (Ptrofs.of_ints (Int.repr 0)) with Ptrofs.zero.
  rewrite Ptrofs.mul_zero, Ptrofs.add_zero. reflexivity.
Qed.

(* Oadd Vptr (tptr tlong) + Vint n tint *)
Lemma sem_add_ptr_tlong_int : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong)
    (Vint n) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* Oor (Vlong a) tlong (Vint b) tint -- mixed types, the Vint is cast to Vlong
   via Int.signed before the or operation *)
Lemma sem_or_long_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Oor
    (Vlong a) tlong
    (Vint b) tint
    m = Some (Vlong (Int64.or a (Int64.repr (Int.signed b)))).
Proof.
  intros. unfold sem_binary_operation, sem_or.
  change (classify_binarith tlong tint) with (bin_case_l Signed).
  unfold sem_binarith. simpl binarith_type.
  unfold sem_cast at 1. simpl classify_cast. rewrite ptr64_true.
  unfold sem_cast at 1. simpl classify_cast. simpl cast_int_long.
  reflexivity.
Qed.

(* Oadd Vptr (tptr tint) + Vint n tint *)
Lemma sem_add_ptr_tint_int : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint n) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* ================================================================== *)
(* Pointer arithmetic helpers                                          *)
(* ================================================================== *)

Lemma ptrofs_of_int_signed_0 :
  ptrofs_of_int Signed (Int.repr 0) = Ptrofs.zero.
Proof. reflexivity. Qed.

Lemma ptrofs_of_int_signed_1 :
  ptrofs_of_int Signed (Int.repr 1) = Ptrofs.one.
Proof. reflexivity. Qed.

Lemma ptrofs_mul_8_0 :
  Ptrofs.mul (Ptrofs.repr 8) Ptrofs.zero = Ptrofs.zero.
Proof. rewrite Ptrofs.mul_zero. reflexivity. Qed.

Lemma load_result_vlong_cl : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr_cl : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* ================================================================== *)
(* Deref: Cast Vptr b ofs tlong -> deref_loc reference *)
(* ================================================================== *)

(* Int.lt (Int.repr 0) (Int.repr 0) = false *)
Lemma int_lt_0_0 : Int.lt (Int.repr 0) (Int.repr 0) = false.
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Main theorem: nvars = 0 case                                        *)
(* ================================================================== *)

Theorem verify_CLOSURE_correct : forall code_ofs,
    handler_correct (handle_CLOSURE 0 code_ofs) f_instr_CLOSURE
      (fun e m s ard =>
         let sb := ar_sptr_block ard in
         let so := ar_sptr_ofs ard in
         let cb := ar_code_base_block ard in
         let co := ar_code_base_ofs ard in
         let gb := ar_global_block ard in
         (* e does not bind heap_alloc *)
         e ! _heap_alloc = None /\
         (* Code buffer: nvars=0 at current PC *)
         Mem.load Mint32 m cb
           (Ptrofs.unsigned (Ptrofs.add co
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr 0)) /\
         (* Code buffer: code_ofs at PC+1 *)
         Mem.load Mint32 m cb
           (Ptrofs.unsigned (Ptrofs.add co
              (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))))
         = Some (Vint (Int.repr code_ofs)) /\
         (* code_ofs fits in signed int range *)
         (Int.min_signed <= code_ofs <= Int.max_signed) /\
         (* Heap map freshness *)
         (ar_heap_map ard) (next_addr s) = None /\
         (* Global block valid *)
         Mem.valid_block m gb /\
         (* Genv lookup for heap_alloc *)
         (exists b_ha,
            Genv.find_symbol (genv_genv ge) _heap_alloc = Some b_ha /\
            Genv.find_funct (genv_genv ge) (Vptr b_ha Ptrofs.zero) =
              Some heap_alloc_fundef) /\
         (* heap_alloc spec: for any memory m', allocate 2 fields with tag 247 *)
         (forall m',
            exists m_alloc new_b new_ofs,
              external_call heap_alloc_ef
                (Genv.to_senv (genv_genv ge))
                (Vptr sb so :: Vlong (Int64.repr 2) :: Vlong (Int64.repr 247) :: nil)
                m' E0 (Vptr new_b new_ofs) m_alloc /\
              (forall b, Mem.valid_block m' b -> new_b <> b) /\
              (forall b ofs chunk v,
                 Mem.load chunk m' b ofs = Some v -> b <> new_b ->
                 Mem.load chunk m_alloc b ofs = Some v) /\
              (forall b ofs k p,
                 Mem.valid_block m' b -> Mem.perm m' b ofs k p ->
                 Mem.perm m_alloc b ofs k p) /\
              (* Field 0 storable (code ptr as Vptr) *)
              (forall cv, exists m_s0,
                 Mem.store Mint64 m_alloc new_b (Ptrofs.unsigned new_ofs) cv = Some m_s0 /\
                 Mem.load Mint64 m_s0 new_b (Ptrofs.unsigned new_ofs) =
                   Some (Val.load_result Mint64 cv) /\
                 (forall b ofs chunk v, b <> new_b ->
                    Mem.load chunk m_alloc b ofs = Some v ->
                    Mem.load chunk m_s0 b ofs = Some v) /\
                 (* Field 1 storable after field 0 *)
                 (forall cv1, exists m_s1,
                    Mem.store Mint64 m_s0 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) cv1 = Some m_s1 /\
                    Mem.load Mint64 m_s1 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) =
                      Some (Val.load_result Mint64 cv1) /\
                    (* Load at field 0 preserved *)
                    (forall v0, Mem.load Mint64 m_s0 new_b (Ptrofs.unsigned new_ofs) = Some v0 ->
                       Mem.load Mint64 m_s1 new_b (Ptrofs.unsigned new_ofs) = Some v0) /\
                    (forall b ofs chunk v, b <> new_b ->
                       Mem.load chunk m_s0 b ofs = Some v ->
                       Mem.load chunk m_s1 b ofs = Some v) /\
                    (forall b ofs k p,
                       Mem.valid_block m_s0 b -> Mem.perm m_s0 b ofs k p ->
                       Mem.perm m_s1 b ofs k p)))))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intro code_ofs.
  intros e le m s.
  unfold handle_CLOSURE. simpl Nat.ltb.

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

  destruct Hstep_pre as (He_heap_alloc & Hcode_nvars & Hcode_ofs & Hcode_ofs_range &
    Hhm_fresh & Hgb_valid & [b_ha [Hfind_symbol Hfind_funct]] & Halloc_spec_all).

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

  (* New pc after first advancement (reading nvars) *)
  set (pc_ofs_1 := Ptrofs.add pc_ofs (Ptrofs.repr 4)).

  (* --- Store 1: advance pc for nvars read --- *)
  destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia) (Vptr cb pc_ofs_1))
    as [m1 Hstore_pc1].

  (* Accu survives pc store *)
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 8) (Vptr cb pc_ofs_1) accu_v Hstore_pc1 Haccu_load).
    right. lia. }

  (* Code load survives pc store (different block) *)
  assert (Hcode_nvars_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
            Some (Vint (Int.repr 0))).
  { erewrite Mem.load_store_other.
    - exact Hcode_nvars.
    - exact Hstore_pc1.
    - left. exact Hcb_ne. }

  (* Code_ofs load survives pc store *)
  assert (Hcode_ofs_m1 : Mem.load Mint32 m1 cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t)))) =
    Some (Vint (Int.repr code_ofs))).
  { erewrite Mem.load_store_other.
    - exact Hcode_ofs.
    - exact Hstore_pc1.
    - left. exact Hcb_ne. }

  (* Sp, env, extra, global, trap survive pc store *)
  assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 16) (Vptr cb pc_ofs_1) (Vptr sp_b sp_ofs) Hstore_pc1 Hsp_load).
    right. lia. }

  (* --- Conditional: nvars > 0 is false (nvars=0), skip the push --- *)
  (* The if branch takes the Sskip path (else), so no stack push. *)

  (* --- heap_alloc: allocate 2-field block with tag 247 --- *)
  (* We need to compute the alloc size: 2 + 0 = 2 *)
  (* In the C: Ebinop Oadd (Econst_int 2) (Etempvar _nvars tint) *)

  (* Instantiate heap_alloc for m1 *)
  destruct (Halloc_spec_all m1)
    as [m_alloc [new_b [new_ofs
         (Hext_call & Hnew_fresh &
          Halloc_load_pres & Halloc_perm_pres & Hcan_store_f0)]]].

  (* Derive freshness for specific blocks *)
  assert (Hnew_ne_sb : new_b <> sb).
  { apply Hnew_fresh. eapply Mem.perm_valid_block.
    apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc1).
    apply (Hsb_writable (Ptrofs.unsigned so)). lia. }
  assert (Hnew_ne_sp : new_b <> sp_b).
  { apply Hnew_fresh. eapply Mem.perm_valid_block.
    apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc1).
    apply (Hsp_writable 0). lia. }
  assert (Hnew_ne_cb : new_b <> cb).
  { apply Hnew_fresh.
    pose proof (Mem.load_valid_access _ _ _ _ _ Hcode_nvars) as [Hrp_cb _].
    eapply Mem.perm_valid_block.
    apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc1).
    apply (Hrp_cb (Ptrofs.unsigned pc_ofs)). simpl. lia. }
  assert (Hnew_ne_gb : new_b <> gb).
  { apply Hnew_fresh.
    eapply Mem.store_valid_block_1. exact Hstore_pc1. exact Hgb_valid. }

  (* Derive struct field preservation from generic load preservation *)
  assert (Hstruct_preserved : forall ofs v,
    Mem.load Mint64 m1 sb ofs = Some v ->
    Mem.load Mint64 m_alloc sb ofs = Some v).
  { intros ofs0 v0 Hld. apply Halloc_load_pres; auto. }

  (* Accu in m_alloc *)
  assert (Haccu_load_alloc : Mem.load Mint64 m_alloc sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply Hstruct_preserved. exact Haccu_load_m1. }

  (* --- Store field 0: code pointer --- *)
  (* The code: block[0] = pc + *pc (which is pc + code_ofs)
     After reading nvars, pc has been advanced once.
     The C reads *pc (code_ofs at what is now pc position after nvars).
     Actually the C stores (t'6 + t'8) where t'6=t'7=pc, t'8=deref(t'7)=code_ofs.
     But pc has been advanced once for nvars.  The code then reads code_ofs
     from the SECOND word in the instruction.

     After storing pc_ofs_1 (advanced past nvars), the C reads *pc = code_ofs word.
     t'6 = s.pc = pc_ofs_1 (the advanced pc)
     t'7 = s.pc = pc_ofs_1
     t'8 = *t'7 = code_ofs (from code buffer at pc_ofs_1)
     code_ptr_val = t'6 + t'8 = pc_ofs_1 + code_ofs * 4

     This is: Vptr cb (Ptrofs.add pc_ofs_1 (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr code_ofs))))
  *)

  set (code_ptr_val := Vptr cb (Ptrofs.add pc_ofs_1
    (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr code_ofs))))).

  destruct (Hcan_store_f0 code_ptr_val)
    as [m_s0 [Hstore_f0 [Hload_f0 [Hf0_load_pres Hcan_store_f1]]]].

  (* --- Store field 1: closinfo = (2 << 1) | 1 = 5 --- *)
  set (closinfo_val := Vlong (Int64.or (Int64.repr (Int.signed (Int.shl (Int.repr 2) (Int.repr 1)))) (Int64.repr 1))).

  destruct (Hcan_store_f1 closinfo_val)
    as [m_s1 [Hstore_f1 [Hload_f1 [Hf1_load_f0_pres [Hf1_load_pres Hf1_perm_pres]]]]].

  (* --- Store: advance pc past code_ofs word --- *)
  set (pc_ofs_2 := Ptrofs.add pc_ofs_1 (Ptrofs.repr 4)).

  (* sb_writable threads through stores *)
  assert (Hsb_writable_m1 :
    Mem.range_perm m1 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { eapply sb_writable_after_store; eauto. }
  assert (Hsb_writable_alloc :
    Mem.range_perm m_alloc sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs0 Hofs0. eapply Halloc_perm_pres.
    - eapply Mem.perm_valid_block.
      apply (Hsb_writable_m1 (Ptrofs.unsigned so)). lia.
    - apply Hsb_writable_m1. exact Hofs0. }
  assert (Hsb_writable_s0 :
    Mem.range_perm m_s0 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs0 Hofs0. eapply Mem.perm_store_1. exact Hstore_f0. apply Hsb_writable_alloc. exact Hofs0. }
  assert (Hsb_writable_s1 :
    Mem.range_perm m_s1 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs0 Hofs0. eapply Hf1_perm_pres.
    - eapply Mem.perm_valid_block.
      apply (Hsb_writable_s0 (Ptrofs.unsigned so)). lia.
    - apply Hsb_writable_s0. exact Hofs0. }

  (* pc field in m_s1 *)
  assert (Hpc_load_s1 : Mem.load Mint64 m_s1 sb (Ptrofs.unsigned so + 0) =
    Some (Vptr cb pc_ofs_1)).
  { apply Hf1_load_pres; auto.
    apply Hf0_load_pres; auto.
    apply Hstruct_preserved.
    pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 0) (Vptr cb pc_ofs_1) Hstore_pc1) as Htmp.
    rewrite load_result_vptr_cl in Htmp. exact Htmp. }

  (* Store pc field: pc_ofs_1 -> pc_ofs_2 *)
  destruct (store_succeeds_sb m_s1 sb so 0 (Vptr cb pc_ofs_1) Hsb_writable_s1 Hpc_load_s1 ltac:(lia) ltac:(lia) (Vptr cb pc_ofs_2))
    as [m_pc2 Hstore_pc2].

  (* --- Store: sp field (sp + nvars = sp + 0 = sp, no change needed) --- *)
  (* For nvars=0, Oadd sp nvars = sp + 0*8 = sp. But the C does:
     Sassign sp (sp + nvars).  With nvars=0, sp' = sp + 0 = sp.
     However, the C cast interpretation of adding an int to a (tptr tlong)
     means sp' = sp + 0*8 = sp.  So the sp store writes the same value.
     We still need to do the store. *)

  (* sp field in m_s1 *)
  assert (Hsp_load_s1 : Mem.load Mint64 m_s1 sb (Ptrofs.unsigned so + 16) =
    Some (Vptr sp_b sp_ofs)).
  { apply Hf1_load_pres.
    - intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq).
    - apply Hf0_load_pres.
      + intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq).
      + apply Hstruct_preserved. exact Hsp_load_m1. }

  assert (Hsp_load_pc2 : Mem.load Mint64 m_pc2 sb (Ptrofs.unsigned so + 16) =
    Some (Vptr sp_b sp_ofs)).
  { apply (load_after_store_other m_s1 m_pc2 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 16) (Vptr cb pc_ofs_2) (Vptr sp_b sp_ofs) Hstore_pc2 Hsp_load_s1).
    right. lia. }

  assert (Hsb_writable_pc2 :
    Mem.range_perm m_pc2 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { eapply sb_writable_after_store; eauto. }

  destruct (store_succeeds_sb m_pc2 sb so 16 (Vptr sp_b sp_ofs) Hsb_writable_pc2 Hsp_load_pc2 ltac:(lia) ltac:(lia) (Vptr sp_b sp_ofs))
    as [m_sp Hstore_sp].

  (* --- Store: accu field <- Vptr new_b new_ofs --- *)
  set (block_v := Vptr new_b new_ofs).

  assert (Haccu_load_pc2 : Mem.load Mint64 m_pc2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m_s1 m_pc2 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 8) (Vptr cb pc_ofs_2) accu_v Hstore_pc2).
    - apply Hf1_load_pres.
      + intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq).
      + apply Hf0_load_pres.
        * intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq).
        * apply Hstruct_preserved. exact Haccu_load_m1.
    - right. lia. }

  assert (Haccu_load_sp : Mem.load Mint64 m_sp sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m_pc2 m_sp sb (Ptrofs.unsigned so + 16)
             (Ptrofs.unsigned so + 8) (Vptr sp_b sp_ofs) accu_v Hstore_sp Haccu_load_pc2).
    left. lia. }

  assert (Hsb_writable_sp :
    Mem.range_perm m_sp sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { eapply sb_writable_after_store; eauto. }

  destruct (store_succeeds_sb m_sp sb so 8 accu_v Hsb_writable_sp Haccu_load_sp ltac:(lia) ltac:(lia) block_v)
    as [m_final Hstore_accu].

  (* Final memory chain: m -> m1 (pc store) -> m_alloc (heap_alloc) ->
     m_s0 (field 0 store) -> m_s1 (field 1 store) ->
     m_pc2 (pc advance) -> m_sp (sp restore) -> m_final (accu store) *)

  (* Heap map extension *)
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
    - constructor. }

  assert (Hval_repr_new : val_repr hm' cb co (Val_closure addr 0) block_v).
  { unfold block_v. change (Z.of_nat 0 * 8)%Z with 0%Z.
    rewrite <- (Ptrofs.add_zero new_ofs) at 1.
    apply vr_closure with (b := new_b) (ofs := new_ofs).
    - unfold hm'. rewrite Nat.eqb_refl. reflexivity.
    - reflexivity. }

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

  (* --- Determine le' --- *)
  (* The function temps in order of assignment:
     _t'1 = s.pc (old pc)
     _nvars = *t'1 (= 0)
     After skipping the if-branch:
     _t'3 = heap_alloc result
     _block = t'3
     Then the for-loop with _i: enters with i=0, exits immediately (0 < 0 is false).
     _t'6 = s.pc (= pc_ofs_1 after first advance)
     _t'7 = s.pc (= pc_ofs_1)
     _t'8 = *t'7 (= code_ofs)
     block[0] = t'6 + t'8
     block[1] = closinfo
     _t'5 = s.pc (= pc_ofs_1)
     s.pc = t'5 + 1 (= pc_ofs_2)
     _t'4 = s.sp
     s.sp = t'4 + nvars (= sp + 0 = sp)
     s.accu = block
  *)
  set (le1 := PTree.set _t'1 (Vptr cb pc_ofs) le).
  set (le2 := PTree.set _nvars (Vint (Int.repr 0)) le1).
  set (le3 := PTree.set _t'3 block_v le2).
  set (le4 := PTree.set _block block_v le3).
  set (le5 := PTree.set _i (Vint (Int.repr 0)) le4).
  set (le6 := PTree.set _t'6 (Vptr cb pc_ofs_1) le5).
  set (le7 := PTree.set _t'7 (Vptr cb pc_ofs_1) le6).
  set (le8 := PTree.set _t'8 (Vint (Int.repr code_ofs)) le7).
  set (le9 := PTree.set _t'5 (Vptr cb pc_ofs_1) le8).
  set (le10 := PTree.set _t'4 (Vptr sp_b sp_ofs) le9).
  set (le' := le10).

  exists le'. exists m_final.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ============================================================== *)
  (* Part 1: exec_stmt derivation (manual construction)              *)
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

    (* Phase 2: Sassign (s->pc) (_t'1 + 1) -- advance pc *)
    assert (Hexec_store_pc1 : exec_stmt function_entry1 clight_ge e le1 m
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
      rewrite (sem_add_pc_1_closure cb pc_ofs m); eval_cbn.
      rewrite (sem_cast_ptr_tint_to_ptr_tint_cl cb pc_ofs_1); eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      fold pc_ofs_1. rewrite Hstore_pc1; eval_cbn.
      reflexivity. }

    (* Phase 3: Sset _nvars (deref _t'1) -- read nvars from code *)
    assert (Hexec_read_nvars : exec_stmt function_entry1 clight_ge e le1 m1
        (Sset _nvars (Ederef (Etempvar _t'1 (tptr tint)) tint))
        E0 le2 m1 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le1.
      rewrite PTree.gss; eval_cbn.
      rewrite Hcode_nvars_m1; eval_cbn.
      reflexivity. }

    (* Phases 1-3: pc advance + read nvars *)
    assert (Hexec_pc_nvars :
      exec_stmt function_entry1 clight_ge e le m
        (Ssequence
          (Ssequence
            (Sset _t'1 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint))))
          (Sset _nvars (Ederef (Etempvar _t'1 (tptr tint)) tint)))
        E0 le2 m1 Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      - replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto.
      - eauto. }

    (* Phase 4: Sifthenelse (nvars > 0) -- takes else branch (Sskip) *)
    assert (Hexec_if_skip : exec_stmt function_entry1 clight_ge e le2 m1
        (Sifthenelse (Ebinop Ogt (Etempvar _nvars tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'12
                  (Efield
                    (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Sset _t'2
                  (Ecast
                    (Ebinop Osub (Etempvar _t'12 (tptr tlong))
                      (Econst_int (Int.repr 1) tint) (tptr tlong))
                    (tptr tlong))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong))
                (Etempvar _t'2 (tptr tlong))))
            (Ssequence
              (Sset _t'11
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong))
              (Sassign (Ederef (Etempvar _t'2 (tptr tlong)) tlong)
                (Etempvar _t'11 tlong))))
          Sskip)
        E0 le2 m1 Out_normal).
    { eapply exec_Sifthenelse with (b := false).
      - (* eval_expr: nvars > 0 *)
        eapply eval_Ebinop.
        + eapply eval_Etempvar.
          unfold le2. rewrite PTree.gss. reflexivity.
        + eapply eval_Econst_int.
        + apply sem_cmp_gt_int_0.
      - (* bool_val Vfalse tint = Some false *)
        rewrite int_lt_0_0. simpl. reflexivity.
      - (* exec Sskip *)
        constructor. }

    (* Phase 5: Scall heap_alloc -- allocate 2-field block *)
    (* heap_alloc(s, 2+nvars, 247) with nvars=0 gives heap_alloc(s, 2, 247) *)

    (* Need: sem_cast (Vint 0) tint tint = Some (Vint 0) *)
    (* sem_add (Vint 2) (Vint 0) = Vint 2 *)
    (* sem_cast (Vint 2) tint tlong = Some (Vlong (Int64.repr 2)) *)
    assert (Hexec_call : exec_stmt function_entry1 clight_ge e le2 m1
        (Scall (Some _t'3)
          (Evar _heap_alloc (Tfunction
                              ((tptr (Tstruct _interp_state noattr)) ::
                               tlong :: tlong :: nil) tlong cc_default))
          ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
           (Ebinop Oadd (Econst_int (Int.repr 2) tint)
             (Etempvar _nvars tint) tint) ::
           (Econst_int (Int.repr 247) tint) :: nil))
        E0 le3 m_alloc Out_normal).
    { eapply exec_Scall with
        (tyargs := (tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
        (tyres := tlong)
        (cconv := cc_default)
        (vf := Vptr b_ha Ptrofs.zero)
        (vargs := Vptr sb so :: Vlong (Int64.repr 2) :: Vlong (Int64.repr 247) :: nil)
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
          unfold le2. rewrite PTree.gso by (compute; congruence).
          unfold le1. rewrite PTree.gso by (compute; congruence).
          exact Hle_s.
        + simpl. reflexivity.
        + econstructor.
          * (* Ebinop Oadd (Econst 2) (Etempvar nvars) *)
            econstructor; [econstructor | econstructor; unfold le2; rewrite PTree.gss; reflexivity | simpl; reflexivity].
          * (* sem_cast (Vint 2) tint tlong *)
            simpl. reflexivity.
          * econstructor.
            -- econstructor.
            -- simpl. reflexivity.
            -- constructor.
      - exact Hfind_funct.
      - reflexivity.
      - eapply eval_funcall_external. exact Hext_call. }

    (* Phase 6: Sset _block _t'3 *)
    assert (Hexec_set_block : exec_stmt function_entry1 clight_ge e le3 m_alloc
        (Sset _block (Etempvar _t'3 tlong))
        E0 le4 m_alloc Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le3. rewrite PTree.gss; eval_cbn.
      reflexivity. }

    (* Phase 7: The for-loop with 0 iterations.
       Sloop (Sseq (Sifthenelse (i < nvars) Sskip Sbreak) body) (Sset i (i+1))
       With i=0 and nvars=0, the condition 0 < 0 is false, so we break immediately. *)

    assert (Hexec_loop_init : exec_stmt function_entry1 clight_ge e le4 m_alloc
        (Sset _i (Econst_int (Int.repr 0) tint))
        E0 le5 m_alloc Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn. reflexivity. }

    (* The loop body: Sifthenelse (i < nvars) Sskip Sbreak; copy statement *)
    (* With i=0 and nvars=0, the condition evaluates to false, so Sbreak. *)
    assert (Hexec_loop_cond_break : exec_stmt function_entry1 clight_ge e le5 m_alloc
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Etempvar _nvars tint) tint)
          Sskip
          Sbreak)
        E0 le5 m_alloc (Out_break)).
    { eapply exec_Sifthenelse with (b := false).
      - eapply eval_Ebinop.
        + eapply eval_Etempvar. unfold le5. rewrite PTree.gss. reflexivity.
        + eapply eval_Etempvar.
          unfold le5. rewrite PTree.gso by (compute; congruence).
          unfold le4. rewrite PTree.gso by (compute; congruence).
          unfold le3. rewrite PTree.gso by (compute; congruence).
          unfold le2. rewrite PTree.gss. reflexivity.
        + apply sem_cmp_lt_int.
      - rewrite int_lt_0_0. simpl. reflexivity.
      - constructor. }

    (* The Ssequence inside the loop: condition check followed by copy body.
       Since condition breaks, the sequence also breaks. *)
    assert (Hexec_loop_body_break : exec_stmt function_entry1 clight_ge e le5 m_alloc
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Etempvar _nvars tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'9
              (Efield
                (Ederef
                  (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Ssequence
              (Sset _t'10
                (Ederef
                  (Ebinop Oadd (Etempvar _t'9 (tptr tlong))
                    (Etempvar _i tint) (tptr tlong)) tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Ecast (Etempvar _block tlong) (tptr tlong))
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 2) tint) tint)
                    (tptr tlong)) tlong) (Etempvar _t'10 tlong)))))
        E0 le5 m_alloc Out_break).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_2. exact Hexec_loop_cond_break.
      discriminate. }

    (* The Sloop exits with Out_normal when the body returns Out_break. *)
    assert (Hexec_loop : exec_stmt function_entry1 clight_ge e le5 m_alloc
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Etempvar _nvars tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _t'9
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong)))
              (Ssequence
                (Sset _t'10
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'9 (tptr tlong))
                      (Etempvar _i tint) (tptr tlong)) tlong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Ecast (Etempvar _block tlong) (tptr tlong))
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 2) tint) tint)
                      (tptr tlong)) tlong) (Etempvar _t'10 tlong)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint)
              (Econst_int (Int.repr 1) tint) tint)))
        E0 le5 m_alloc Out_normal).
    { eapply exec_Sloop_stop1.
      - exact Hexec_loop_body_break.
      - constructor. }

    (* Sset _i; Sloop *)
    assert (Hexec_init_loop :
      exec_stmt function_entry1 clight_ge e le4 m_alloc
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Etempvar _nvars tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'9
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Ssequence
                  (Sset _t'10
                    (Ederef
                      (Ebinop Oadd (Etempvar _t'9 (tptr tlong))
                        (Etempvar _i tint) (tptr tlong)) tlong))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Ecast (Etempvar _block tlong) (tptr tlong))
                        (Ebinop Oadd (Etempvar _i tint)
                          (Econst_int (Int.repr 2) tint) tint)
                        (tptr tlong)) tlong) (Etempvar _t'10 tlong)))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint)
                (Econst_int (Int.repr 1) tint) tint))))
        E0 le5 m_alloc Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto. }

    (* Phase 8: Read pc for code pointer + store block[0] *)
    (* t'6 = s.pc, t'7 = s.pc, t'8 = deref(t'7), block[0] = t'6 + t'8 *)

    (* pc field in m_alloc *)
    assert (Hpc_load_alloc : Mem.load Mint64 m_alloc sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs_1)).
    { apply Hstruct_preserved.
      pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 0) (Vptr cb pc_ofs_1) Hstore_pc1) as Htmp.
      rewrite load_result_vptr_cl in Htmp. exact Htmp. }

    (* code_ofs word load in m_alloc *)
    (* pc_ofs_1 = pc_ofs + 4.  In the abs_rel, pc = (pc s + 1) * sizeof_code_t.
       But we have pc_ofs_1 = Ptrofs.add pc_ofs (Ptrofs.repr 4).
       And sizeof_code_t = 4.
       So (Machine.pc s + 1) * sizeof_code_t = Machine.pc s * sizeof_code_t + 4.
       Therefore Ptrofs.add co (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))
       = Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t + 4))
       = Ptrofs.add (Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) (Ptrofs.repr 4)
       = Ptrofs.add pc_ofs (Ptrofs.repr 4)
       = pc_ofs_1

       So loading from cb at pc_ofs_1 gives code_ofs.
    *)
    assert (Hpc_ofs_1_eq : pc_ofs_1 =
      Ptrofs.add co (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))).
    { unfold pc_ofs_1, pc_ofs, sizeof_code_t.
      rewrite Ptrofs.add_assoc. f_equal.
      rewrite Ptrofs.add_unsigned.
      apply Ptrofs.eqm_samerepr.
      eapply Ptrofs.eqm_trans.
      - apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
      - apply Ptrofs.eqm_refl2. lia. }

    assert (Hcode_ofs_load_alloc : Mem.load Mint32 m_alloc cb (Ptrofs.unsigned pc_ofs_1) =
              Some (Vint (Int.repr code_ofs))).
    { rewrite Hpc_ofs_1_eq.
      apply Halloc_load_pres.
      - erewrite Mem.load_store_other.
        + exact Hcode_ofs.
        + exact Hstore_pc1.
        + left. exact Hcb_ne.
      - intro Heq; symmetry in Heq; exact (Hnew_ne_cb Heq). }

    assert (Hexec_set_t6 : exec_stmt function_entry1 clight_ge e le5 m_alloc
        (Sset _t'6
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        E0 le6 m_alloc Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le5. rewrite PTree.gso by (compute; congruence).
      unfold le4. rewrite PTree.gso by (compute; congruence).
      unfold le3. rewrite PTree.gso by (compute; congruence).
      unfold le2. rewrite PTree.gso by (compute; congruence).
      unfold le1. rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load_alloc; eval_cbn.
      reflexivity. }

    assert (Hexec_set_t7 : exec_stmt function_entry1 clight_ge e le6 m_alloc
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        E0 le7 m_alloc Out_normal).
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
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load_alloc; eval_cbn.
      reflexivity. }

    assert (Hexec_set_t8 : exec_stmt function_entry1 clight_ge e le7 m_alloc
        (Sset _t'8 (Ederef (Etempvar _t'7 (tptr tint)) tint))
        E0 le8 m_alloc Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le7. rewrite PTree.gss; eval_cbn.
      rewrite Hcode_ofs_load_alloc; eval_cbn.
      reflexivity. }

    (* Store: block[0] = t'6 + t'8 = code_ptr_val *)
    assert (Hexec_store_code_ptr : exec_stmt function_entry1 clight_ge e le8 m_alloc
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Ecast (Etempvar _block tlong) (tptr (tptr tint)))
              (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
            (tptr tint))
          (Ebinop Oadd (Etempvar _t'6 (tptr tint))
            (Etempvar _t'8 tint) (tptr tint)))
        E0 le8 m_s0 Out_normal).
    { eapply exec_Sassign with (v := code_ptr_val).
      - (* lvalue: Ederef (Oadd (cast _block to ptr ptr tint) (const 0)) *)
        eapply eval_Ederef.
        eapply eval_Ebinop.
        + eapply eval_Ecast.
          * eapply eval_Etempvar.
            unfold le8. rewrite PTree.gso by (compute; congruence).
            unfold le7. rewrite PTree.gso by (compute; congruence).
            unfold le6. rewrite PTree.gso by (compute; congruence).
            unfold le5. rewrite PTree.gso by (compute; congruence).
            unfold le4. rewrite PTree.gss. reflexivity.
          * apply sem_cast_vptr_tlong_to_ptr_ptr_tint.
        + eapply eval_Econst_int.
        + apply sem_add_ptr_ptr_tint_0.
      - (* rvalue: Oadd t'6 t'8 *)
        eapply eval_Ebinop.
        + eapply eval_Etempvar.
          unfold le8.
          rewrite PTree.gso by (compute; congruence).
          unfold le7. rewrite PTree.gso by (compute; congruence).
          unfold le6. rewrite PTree.gss. reflexivity.
        + eapply eval_Etempvar.
          unfold le8. rewrite PTree.gss. reflexivity.
        + apply sem_add_ptr_tint_int.
      - (* sem_cast rhs to lhs type: tptr tint -> tptr tint *)
        apply sem_cast_ptr_tint_to_ptr_tint_cl.
      - (* assign_loc: store at block[0] *)
        eapply assign_loc_value.
        + reflexivity.
        + unfold Mem.storev. rewrite Mptr_Mint64. exact Hstore_f0. }

    (* Phase 9: Store block[1] = closinfo *)
    assert (Hexec_store_closinfo : exec_stmt function_entry1 clight_ge e le8 m_s0
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
          (Ebinop Oor
            (Ecast
              (Ebinop Oshl (Econst_int (Int.repr 2) tint)
                (Econst_int (Int.repr 1) tint) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong))
        E0 le8 m_s1 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      (* Resolve _block lookup *)
      unfold le8. rewrite PTree.gso by (compute; congruence).
      unfold le7. rewrite PTree.gso by (compute; congruence).
      unfold le6. rewrite PTree.gso by (compute; congruence).
      unfold le5. rewrite PTree.gso by (compute; congruence).
      unfold le4. rewrite PTree.gss; eval_cbn.
      fold block_v.
      (* Cast block_v (Vptr) from tlong to (tptr tlong) *)
      replace (sem_cast block_v tlong (tptr tlong) m_s0)
        with (Some block_v)
        by (unfold block_v, sem_cast; simpl classify_cast; reflexivity);
        eval_cbn.
      (* sem_add: block + 1 *)
      unfold block_v at 1.
      rewrite (sem_add_sp_1 new_b new_ofs m_s0); eval_cbn.
      (* Evaluate the rvalue: (2 << 1) | 1 *)
      (* shl is handled by eval_cbn since sem_binary_operation is opaque
         but the constants are all ints, we need sem_shl_int_1 *)
      rewrite sem_shl_int_1; eval_cbn.
      rewrite sem_cast_int_to_tlong; eval_cbn.
      rewrite sem_or_long_int; eval_cbn.
      (* Cast closinfo from tlong to tlong *)
      rewrite sem_cast_long_vlong; eval_cbn.
      (* Normalize Int.signed (Int.repr 1) to 1 so fold closinfo_val matches *)
      change (Int64.repr (Int.signed (Int.repr 1))) with (Int64.repr 1).
      fold closinfo_val.
      rewrite Hstore_f1; eval_cbn.
      reflexivity. }

    (* Phase 10: Read pc (t'5 = s.pc), advance pc (s.pc = t'5 + 1) *)
    (* pc in m_s1 was preserved from m_alloc through field stores *)
    assert (Hexec_set_t5 : exec_stmt function_entry1 clight_ge e le8 m_s1
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        E0 le9 m_s1 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le8. rewrite PTree.gso by (compute; congruence).
      unfold le7. rewrite PTree.gso by (compute; congruence).
      unfold le6. rewrite PTree.gso by (compute; congruence).
      unfold le5. rewrite PTree.gso by (compute; congruence).
      unfold le4. rewrite PTree.gso by (compute; congruence).
      unfold le3. rewrite PTree.gso by (compute; congruence).
      unfold le2. rewrite PTree.gso by (compute; congruence).
      unfold le1. rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load_s1; eval_cbn.
      reflexivity. }

    assert (Hexec_store_pc2 : exec_stmt function_entry1 clight_ge e le9 m_s1
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'5 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint)))
        E0 le9 m_pc2 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le9. rewrite PTree.gso by (compute; congruence).
      unfold le8. rewrite PTree.gso by (compute; congruence).
      unfold le7. rewrite PTree.gso by (compute; congruence).
      unfold le6. rewrite PTree.gso by (compute; congruence).
      unfold le5. rewrite PTree.gso by (compute; congruence).
      unfold le4. rewrite PTree.gso by (compute; congruence).
      unfold le3. rewrite PTree.gso by (compute; congruence).
      unfold le2. rewrite PTree.gso by (compute; congruence).
      unfold le1. rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_pc_1_closure cb pc_ofs_1 m_s1); eval_cbn.
      rewrite (sem_cast_ptr_tint_to_ptr_tint_cl cb pc_ofs_2); eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      fold pc_ofs_2. rewrite Hstore_pc2; eval_cbn.
      reflexivity. }

    (* Phase 11: Read sp (t'4 = s.sp), store sp = t'4 + nvars *)
    assert (Hexec_set_t4 : exec_stmt function_entry1 clight_ge e le9 m_pc2
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        E0 le10 m_pc2 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le9. rewrite PTree.gso by (compute; congruence).
      unfold le8. rewrite PTree.gso by (compute; congruence).
      unfold le7. rewrite PTree.gso by (compute; congruence).
      unfold le6. rewrite PTree.gso by (compute; congruence).
      unfold le5. rewrite PTree.gso by (compute; congruence).
      unfold le4. rewrite PTree.gso by (compute; congruence).
      unfold le3. rewrite PTree.gso by (compute; congruence).
      unfold le2. rewrite PTree.gso by (compute; congruence).
      unfold le1. rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hsp_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      rewrite Hsp_load_pc2; eval_cbn.
      reflexivity. }

    assert (Hexec_store_sp : exec_stmt function_entry1 clight_ge e le10 m_pc2
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong))
          (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
            (Etempvar _nvars tint) (tptr tlong)))
        E0 le10 m_sp Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      (* lvalue: s->sp *)
      unfold le10. rewrite PTree.gso by (compute; congruence).
      unfold le9. rewrite PTree.gso by (compute; congruence).
      unfold le8. rewrite PTree.gso by (compute; congruence).
      unfold le7. rewrite PTree.gso by (compute; congruence).
      unfold le6. rewrite PTree.gso by (compute; congruence).
      unfold le5. rewrite PTree.gso by (compute; congruence).
      unfold le4. rewrite PTree.gso by (compute; congruence).
      unfold le3. rewrite PTree.gso by (compute; congruence).
      unfold le2. rewrite PTree.gso by (compute; congruence).
      unfold le1. rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hsp_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      (* rvalue: t'4 + nvars *)
      rewrite PTree.gss; eval_cbn.
      unfold le10.
      rewrite PTree.gso by (compute; congruence).
      unfold le9. rewrite PTree.gso by (compute; congruence).
      unfold le8. rewrite PTree.gso by (compute; congruence).
      unfold le7. rewrite PTree.gso by (compute; congruence).
      unfold le6. rewrite PTree.gso by (compute; congruence).
      unfold le5. rewrite PTree.gso by (compute; congruence).
      unfold le4. rewrite PTree.gso by (compute; congruence).
      unfold le3. rewrite PTree.gso by (compute; congruence).
      unfold le2. rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_ptr_tlong_int sp_b sp_ofs (Int.repr 0) m_pc2); eval_cbn.
      (* sp + 0*8 = sp *)
      change (Ptrofs.add sp_ofs (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr 0))))
        with (Ptrofs.add sp_ofs Ptrofs.zero).
      rewrite Ptrofs.add_zero.
      rewrite (sem_cast_ptr_to_ptr sp_b sp_ofs m_pc2); eval_cbn.
      (* store *)
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      rewrite Hstore_sp; eval_cbn.
      reflexivity. }

    (* Phase 12: Store accu = block *)
    assert (Hexec_store_accu : exec_stmt function_entry1 clight_ge e le10 m_sp
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _block tlong))
        E0 le10 m_final Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      (* lvalue: s->accu *)
      unfold le10. rewrite PTree.gso by (compute; congruence).
      unfold le9. rewrite PTree.gso by (compute; congruence).
      unfold le8. rewrite PTree.gso by (compute; congruence).
      unfold le7. rewrite PTree.gso by (compute; congruence).
      unfold le6. rewrite PTree.gso by (compute; congruence).
      unfold le5. rewrite PTree.gso by (compute; congruence).
      unfold le4. rewrite PTree.gso by (compute; congruence).
      unfold le3. rewrite PTree.gso by (compute; congruence).
      unfold le2. rewrite PTree.gso by (compute; congruence).
      unfold le1. rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Haccu_offset; eval_cbn.
      (* rvalue: _block *)
      unfold le10. rewrite PTree.gso by (compute; congruence).
      unfold le9. rewrite PTree.gso by (compute; congruence).
      unfold le8. rewrite PTree.gso by (compute; congruence).
      unfold le7. rewrite PTree.gso by (compute; congruence).
      unfold le6. rewrite PTree.gso by (compute; congruence).
      unfold le5. rewrite PTree.gso by (compute; congruence).
      unfold le4. rewrite PTree.gss; eval_cbn.
      fold block_v.
      replace (sem_cast block_v tlong tlong m_sp) with (Some block_v)
        by (unfold block_v; apply (sem_cast_long_vptr new_b new_ofs m_sp)); eval_cbn.
      (* store *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Hstore_accu; eval_cbn.
      reflexivity. }

    (* Phase 13: Return 0 *)
    assert (Hexec_return : exec_stmt function_entry1 clight_ge e le10 m_final
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        E0 le10 m_final (Out_return (Some (Vint (Int.repr 0), tint)))).
    { apply (eval_stmt_to_exec clight_ge 10). reflexivity. }

    (* Now combine all phases.  The fn_body of f_instr_CLOSURE is a big
       Ssequence tree.  We build the execution bottom-up. *)

    (* Build up intermediate sequences *)

    (* Seq: set_t1; store_pc1 *)
    assert (Hexec_s12 : exec_stmt function_entry1 clight_ge e le m
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

    (* Seq: set_t5; store_pc2 *)
    assert (Hexec_pc2_seq : exec_stmt function_entry1 clight_ge e le8 m_s1
      (Ssequence
        (Sset _t'5
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                   (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'5 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      E0 le9 m_pc2 Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto. }

    (* Seq: set_t4; store_sp *)
    assert (Hexec_sp_seq : exec_stmt function_entry1 clight_ge e le9 m_pc2
      (Ssequence
        (Sset _t'4
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                   (Tstruct _interp_state noattr)) _sp (tptr tlong))
          (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
            (Etempvar _nvars tint) (tptr tlong))))
      E0 le10 m_sp Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto. }

    (* Seq: sp_seq; store_accu *)
    assert (Hexec_sp_accu : exec_stmt function_entry1 clight_ge e le9 m_pc2
      (Ssequence
        (Ssequence
          (Sset _t'4
            (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                     (Tstruct _interp_state noattr)) _sp (tptr tlong))
            (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
              (Etempvar _nvars tint) (tptr tlong))))
        (Sassign
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _block tlong)))
      E0 le10 m_final Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto. }

    (* Seq: pc2_seq; sp_accu *)
    assert (Hexec_pc2_sp_accu : exec_stmt function_entry1 clight_ge e le8 m_s1
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
          (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                     (Tstruct _interp_state noattr)) _pc (tptr tint))
            (Ebinop Oadd (Etempvar _t'5 (tptr tint))
              (Econst_int (Int.repr 1) tint) (tptr tint))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _sp (tptr tlong))
              (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                (Etempvar _nvars tint) (tptr tlong))))
          (Sassign
            (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
            (Etempvar _block tlong))))
      E0 le10 m_final Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto. }

    (* Seq: store_closinfo; pc2_sp_accu *)
    assert (Hexec_closinfo_rest : exec_stmt function_entry1 clight_ge e le8 m_s0
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
          (Ebinop Oor
            (Ecast
              (Ebinop Oshl (Econst_int (Int.repr 2) tint)
                (Econst_int (Int.repr 1) tint) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong))
        (Ssequence
          (Ssequence
            (Sset _t'5
              (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint))))
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
              (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _sp (tptr tlong))
                (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                  (Etempvar _nvars tint) (tptr tlong))))
            (Sassign
              (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong)
              (Etempvar _block tlong)))))
      E0 le10 m_final Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto. }

    (* Now we need to match the exact fn_body of f_instr_CLOSURE.
       The body is a big nested Ssequence ending with Sreturn. *)

    (* Build: set_t6; [set_t7; [set_t8; store_code_ptr]] *)
    assert (Hexec_t7_t8_code : exec_stmt function_entry1 clight_ge e le6 m_alloc
      (Ssequence
        (Sset _t'7
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Ssequence
          (Sset _t'8 (Ederef (Etempvar _t'7 (tptr tint)) tint))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Ecast (Etempvar _block tlong) (tptr (tptr tint)))
                (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
              (tptr tint))
            (Ebinop Oadd (Etempvar _t'6 (tptr tint))
              (Etempvar _t'8 tint) (tptr tint)))))
      E0 le8 m_s0 Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      - exact Hexec_set_t7.
      - replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto. }

    assert (Hexec_t6_code : exec_stmt function_entry1 clight_ge e le5 m_alloc
      (Ssequence
        (Sset _t'6
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Ssequence
          (Sset _t'7
            (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
          (Ssequence
            (Sset _t'8 (Ederef (Etempvar _t'7 (tptr tint)) tint))
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Ecast (Etempvar _block tlong) (tptr (tptr tint)))
                  (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
                (tptr tint))
              (Ebinop Oadd (Etempvar _t'6 (tptr tint))
                (Etempvar _t'8 tint) (tptr tint))))))
      E0 le8 m_s0 Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto. }

    (* Build: init_loop; t6_code *)
    assert (Hexec_loop_code : exec_stmt function_entry1 clight_ge e le4 m_alloc
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Etempvar _nvars tint) tint)
                Sskip Sbreak)
              (Ssequence
                (Sset _t'9
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Ssequence
                  (Sset _t'10
                    (Ederef (Ebinop Oadd (Etempvar _t'9 (tptr tlong))
                      (Etempvar _i tint) (tptr tlong)) tlong))
                  (Sassign
                    (Ederef (Ebinop Oadd
                      (Ecast (Etempvar _block tlong) (tptr tlong))
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 2) tint) tint)
                      (tptr tlong)) tlong) (Etempvar _t'10 tlong)))))
            (Sset _i (Ebinop Oadd (Etempvar _i tint)
              (Econst_int (Int.repr 1) tint) tint))))
        (Ssequence
          (Ssequence
            (Sset _t'6
              (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Ssequence
              (Sset _t'7
                (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Ssequence
                (Sset _t'8 (Ederef (Etempvar _t'7 (tptr tint)) tint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Ecast (Etempvar _block tlong) (tptr (tptr tint)))
                      (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
                    (tptr tint))
                  (Ebinop Oadd (Etempvar _t'6 (tptr tint))
                    (Etempvar _t'8 tint) (tptr tint))))))
          (Ssequence
            (Sassign
              (Ederef (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
              (Ebinop Oor
                (Ecast (Ebinop Oshl (Econst_int (Int.repr 2) tint)
                  (Econst_int (Int.repr 1) tint) tint) tlong)
                (Econst_int (Int.repr 1) tint) tlong))
            (Ssequence
              (Ssequence
                (Sset _t'5
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
                (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                           (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                    (Econst_int (Int.repr 1) tint) (tptr tint))))
              (Ssequence
                (Ssequence
                  (Sset _t'4
                    (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                  (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                             (Tstruct _interp_state noattr)) _sp (tptr tlong))
                    (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                      (Etempvar _nvars tint) (tptr tlong))))
                (Sassign
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong)
                  (Etempvar _block tlong)))))))
      E0 le10 m_final Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      - exact Hexec_init_loop.
      - replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1.
        + exact Hexec_t6_code.
        + exact Hexec_closinfo_rest. }

    (* Build: Scall; Sset block; loop_code *)
    assert (Hexec_alloc_block_loop_code : exec_stmt function_entry1 clight_ge e le2 m1
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _heap_alloc (Tfunction
                                ((tptr (Tstruct _interp_state noattr)) ::
                                 tlong :: tlong :: nil) tlong cc_default))
            ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
             (Ebinop Oadd (Econst_int (Int.repr 2) tint)
               (Etempvar _nvars tint) tint) ::
             (Econst_int (Int.repr 247) tint) :: nil))
          (Sset _block (Etempvar _t'3 tlong)))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Etempvar _nvars tint) tint)
                  Sskip Sbreak)
                (Ssequence
                  (Sset _t'9
                    (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                  (Ssequence
                    (Sset _t'10
                      (Ederef (Ebinop Oadd (Etempvar _t'9 (tptr tlong))
                        (Etempvar _i tint) (tptr tlong)) tlong))
                    (Sassign
                      (Ederef (Ebinop Oadd
                        (Ecast (Etempvar _block tlong) (tptr tlong))
                        (Ebinop Oadd (Etempvar _i tint)
                          (Econst_int (Int.repr 2) tint) tint)
                        (tptr tlong)) tlong) (Etempvar _t'10 tlong)))))
              (Sset _i (Ebinop Oadd (Etempvar _i tint)
                (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Ssequence
              (Sset _t'6
                (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Ssequence
                (Sset _t'7
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
                (Ssequence
                  (Sset _t'8 (Ederef (Etempvar _t'7 (tptr tint)) tint))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Ecast (Etempvar _block tlong) (tptr (tptr tint)))
                        (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
                      (tptr tint))
                    (Ebinop Oadd (Etempvar _t'6 (tptr tint))
                      (Etempvar _t'8 tint) (tptr tint))))))
            (Ssequence
              (Sassign
                (Ederef (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
                (Ebinop Oor
                  (Ecast (Ebinop Oshl (Econst_int (Int.repr 2) tint)
                    (Econst_int (Int.repr 1) tint) tint) tlong)
                  (Econst_int (Int.repr 1) tint) tlong))
              (Ssequence
                (Ssequence
                  (Sset _t'5
                    (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint)))
                  (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                             (Tstruct _interp_state noattr)) _pc (tptr tint))
                    (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                      (Econst_int (Int.repr 1) tint) (tptr tint))))
                (Ssequence
                  (Ssequence
                    (Sset _t'4
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                    (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                               (Tstruct _interp_state noattr)) _sp (tptr tlong))
                      (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                        (Etempvar _nvars tint) (tptr tlong))))
                  (Sassign
                    (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _accu tlong)
                    (Etempvar _block tlong))))))))
      E0 le10 m_final Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      - replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto.
      - exact Hexec_loop_code. }

    (* Build: if_skip; alloc_block_loop_code *)
    assert (Hexec_if_alloc : exec_stmt function_entry1 clight_ge e le2 m1
      (Ssequence
        (Sifthenelse (Ebinop Ogt (Etempvar _nvars tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'12
                  (Efield
                    (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Sset _t'2
                  (Ecast
                    (Ebinop Osub (Etempvar _t'12 (tptr tlong))
                      (Econst_int (Int.repr 1) tint) (tptr tlong))
                    (tptr tlong))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong))
                (Etempvar _t'2 (tptr tlong))))
            (Ssequence
              (Sset _t'11
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong))
              (Sassign (Ederef (Etempvar _t'2 (tptr tlong)) tlong)
                (Etempvar _t'11 tlong))))
          Sskip)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _heap_alloc (Tfunction
                                  ((tptr (Tstruct _interp_state noattr)) ::
                                   tlong :: tlong :: nil) tlong cc_default))
              ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
               (Ebinop Oadd (Econst_int (Int.repr 2) tint)
                 (Etempvar _nvars tint) tint) ::
               (Econst_int (Int.repr 247) tint) :: nil))
            (Sset _block (Etempvar _t'3 tlong)))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Etempvar _nvars tint) tint)
                    Sskip Sbreak)
                  (Ssequence
                    (Sset _t'9
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                    (Ssequence
                      (Sset _t'10
                        (Ederef (Ebinop Oadd (Etempvar _t'9 (tptr tlong))
                          (Etempvar _i tint) (tptr tlong)) tlong))
                      (Sassign
                        (Ederef (Ebinop Oadd
                          (Ecast (Etempvar _block tlong) (tptr tlong))
                          (Ebinop Oadd (Etempvar _i tint)
                            (Econst_int (Int.repr 2) tint) tint)
                          (tptr tlong)) tlong) (Etempvar _t'10 tlong)))))
                (Sset _i (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Ssequence
                (Sset _t'6
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
                (Ssequence
                  (Sset _t'7
                    (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint)))
                  (Ssequence
                    (Sset _t'8 (Ederef (Etempvar _t'7 (tptr tint)) tint))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Ecast (Etempvar _block tlong) (tptr (tptr tint)))
                          (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
                        (tptr tint))
                      (Ebinop Oadd (Etempvar _t'6 (tptr tint))
                        (Etempvar _t'8 tint) (tptr tint))))))
              (Ssequence
                (Sassign
                  (Ederef (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                    (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
                  (Ebinop Oor
                    (Ecast (Ebinop Oshl (Econst_int (Int.repr 2) tint)
                      (Econst_int (Int.repr 1) tint) tint) tlong)
                    (Econst_int (Int.repr 1) tint) tlong))
                (Ssequence
                  (Ssequence
                    (Sset _t'5
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _pc (tptr tint)))
                    (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                               (Tstruct _interp_state noattr)) _pc (tptr tint))
                      (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                        (Econst_int (Int.repr 1) tint) (tptr tint))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'4
                        (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                      (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                 (Tstruct _interp_state noattr)) _sp (tptr tlong))
                        (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                          (Etempvar _nvars tint) (tptr tlong))))
                    (Sassign
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _accu tlong)
                      (Etempvar _block tlong)))))))))
      E0 le10 m_final Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto. }

    (* Build: pc_nvars; if_alloc *)
    eassert (Hexec_pre_return : exec_stmt function_entry1 clight_ge e le m
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'1 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint))))
          (Sset _nvars (Ederef (Etempvar _t'1 (tptr tint)) tint)))
        (Ssequence
          (Sifthenelse (Ebinop Ogt (Etempvar _nvars tint)
                         (Econst_int (Int.repr 0) tint) tint)
            _
            Sskip)
          _))
      E0 le10 m_final Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      - exact Hexec_pc_nvars.
      - exact Hexec_if_alloc. }

    (* The full body matches fn_body. Use change to equate. *)
    change (fn_body f_instr_CLOSURE) with
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
            (Sset _nvars (Ederef (Etempvar _t'1 (tptr tint)) tint)))
          (Ssequence
            (Sifthenelse (Ebinop Ogt (Etempvar _nvars tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'12
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                    (Sset _t'2
                      (Ecast (Ebinop Osub (Etempvar _t'12 (tptr tlong))
                        (Econst_int (Int.repr 1) tint) (tptr tlong))
                        (tptr tlong))))
                  (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong))
                    (Etempvar _t'2 (tptr tlong))))
                (Ssequence
                  (Sset _t'11 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong))
                  (Sassign (Ederef (Etempvar _t'2 (tptr tlong)) tlong)
                    (Etempvar _t'11 tlong))))
              Sskip)
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _heap_alloc (Tfunction
                    ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
                    tlong cc_default))
                  ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
                   (Ebinop Oadd (Econst_int (Int.repr 2) tint)
                     (Etempvar _nvars tint) tint) ::
                   (Econst_int (Int.repr 247) tint) :: nil))
                (Sset _block (Etempvar _t'3 tlong)))
              (Ssequence
                (Ssequence
                  (Sset _i (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                     (Etempvar _nvars tint) tint)
                        Sskip Sbreak)
                      (Ssequence
                        (Sset _t'9 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                        (Ssequence
                          (Sset _t'10 (Ederef (Ebinop Oadd (Etempvar _t'9 (tptr tlong))
                            (Etempvar _i tint) (tptr tlong)) tlong))
                          (Sassign (Ederef (Ebinop Oadd
                            (Ecast (Etempvar _block tlong) (tptr tlong))
                            (Ebinop Oadd (Etempvar _i tint)
                              (Econst_int (Int.repr 2) tint) tint)
                            (tptr tlong)) tlong) (Etempvar _t'10 tlong)))))
                    (Sset _i (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint))))
                (Ssequence
                  (Ssequence
                    (Sset _t'6 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint)))
                    (Ssequence
                      (Sset _t'7 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _pc (tptr tint)))
                      (Ssequence
                        (Sset _t'8 (Ederef (Etempvar _t'7 (tptr tint)) tint))
                        (Sassign (Ederef (Ebinop Oadd
                          (Ecast (Etempvar _block tlong) (tptr (tptr tint)))
                          (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
                          (tptr tint))
                          (Ebinop Oadd (Etempvar _t'6 (tptr tint))
                            (Etempvar _t'8 tint) (tptr tint))))))
                  (Ssequence
                    (Sassign (Ederef (Ebinop Oadd
                      (Ecast (Etempvar _block tlong) (tptr tlong))
                      (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
                      (Ebinop Oor
                        (Ecast (Ebinop Oshl (Econst_int (Int.repr 2) tint)
                          (Econst_int (Int.repr 1) tint) tint) tlong)
                        (Econst_int (Int.repr 1) tint) tlong))
                    (Ssequence
                      (Ssequence
                        (Sset _t'5 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _pc (tptr tint)))
                        (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _pc (tptr tint))
                          (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                            (Econst_int (Int.repr 1) tint) (tptr tint))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'4 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                          (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _sp (tptr tlong))
                            (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                              (Etempvar _nvars tint) (tptr tlong))))
                        (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _accu tlong)
                          (Etempvar _block tlong))))))))))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))).

    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1; eauto.
  }

  (* ============================================================== *)
  (* Part 2: abs_rel for post-state                                  *)
  (* ============================================================== *)
  {
    set (new_co := Ptrofs.add (Ptrofs.add co (Ptrofs.repr sizeof_code_t)) (Ptrofs.repr sizeof_code_t)).
    set (ard' := mk_abs_rel
      sb so hm'
      cb new_co
      gb go0
      (ar_stack_block ard) (ar_stack_base_ofs ard)
      (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
    exists ard'.

    set (uso := Ptrofs.unsigned so) in *.

    (* pc field: written by store_pc2 in m_pc2, preserved through m_sp, m_final *)
    assert (Hpc_load_pc2 : Mem.load Mint64 m_pc2 sb (uso + 0) =
              Some (Vptr cb pc_ofs_2)).
    { pose proof (load_after_store_same m_s1 m_pc2 sb (uso + 0) (Vptr cb pc_ofs_2) Hstore_pc2) as Htmp.
      rewrite load_result_vptr_cl in Htmp. exact Htmp. }

    assert (Hpc_load_sp : Mem.load Mint64 m_sp sb (uso + 0) = Some (Vptr cb pc_ofs_2)).
    { apply (load_after_store_other m_pc2 m_sp sb (uso + 16) (uso + 0)
               (Vptr sp_b sp_ofs) (Vptr cb pc_ofs_2) Hstore_sp Hpc_load_pc2).
      left. lia. }

    assert (Hpc_load_final : Mem.load Mint64 m_final sb (uso + 0) = Some (Vptr cb pc_ofs_2)).
    { apply (load_after_store_other m_sp m_final sb (uso + 8) (uso + 0)
               block_v (Vptr cb pc_ofs_2) Hstore_accu Hpc_load_sp).
      left. lia. }

    (* accu field: written by store_accu *)
    assert (Haccu_load_final : Mem.load Mint64 m_final sb (uso + 8) = Some block_v).
    { pose proof (load_after_store_same m_sp m_final sb (uso + 8) block_v Hstore_accu) as Htmp.
      unfold block_v in Htmp |- *. rewrite load_result_vptr_cl in Htmp. exact Htmp. }

    (* Helper: struct fields at offsets = 16 or >= 24 survive through all stores *)
    assert (Hfield_survive : forall field_ofs v,
      (field_ofs = 16 \/ field_ofs >= 24) ->
      Mem.load Mint64 m sb (uso + field_ofs) = Some v ->
      Mem.load Mint64 m_final sb (uso + field_ofs) = Some v).
    { intros fo v Hfo Hload.
      (* m -> m1: store at uso+0 *)
      assert (H1 : Mem.load Mint64 m1 sb (uso + fo) = Some v).
      { apply (load_after_store_other m m1 sb (uso + 0) (uso + fo)
                 (Vptr cb pc_ofs_1) v Hstore_pc1 Hload). right. lia. }
      (* m1 -> m_alloc *)
      assert (H2 : Mem.load Mint64 m_alloc sb (uso + fo) = Some v).
      { apply Hstruct_preserved. exact H1. }
      (* m_alloc -> m_s0 *)
      assert (H3 : Mem.load Mint64 m_s0 sb (uso + fo) = Some v).
      { apply Hf0_load_pres; auto. }
      (* m_s0 -> m_s1 *)
      assert (H4 : Mem.load Mint64 m_s1 sb (uso + fo) = Some v).
      { apply Hf1_load_pres; auto. }
      (* m_s1 -> m_pc2: store at uso+0 *)
      assert (H5 : Mem.load Mint64 m_pc2 sb (uso + fo) = Some v).
      { apply (load_after_store_other m_s1 m_pc2 sb (uso + 0) (uso + fo)
                 (Vptr cb pc_ofs_2) v Hstore_pc2 H4). right. lia. }
      (* m_pc2 -> m_sp: store at uso+16 *)
      assert (H6 : Mem.load Mint64 m_sp sb (uso + fo) = Some v).
      { destruct (Z.eq_dec fo 16).
        - subst fo.
          pose proof (load_after_store_same m_pc2 m_sp sb (uso + 16) (Vptr sp_b sp_ofs) Hstore_sp) as Htmp.
          rewrite load_result_vptr_cl in Htmp. rewrite Htmp.
          (* Need: v = Vptr sp_b sp_ofs *)
          (* We stored (Vptr sp_b sp_ofs) at uso+16, and the original value there was also (Vptr sp_b sp_ofs) *)
          rewrite Hsp_load in Hload. injection Hload. intro Heq. rewrite Heq. reflexivity.
        - apply (load_after_store_other m_pc2 m_sp sb (uso + 16) (uso + fo)
                   (Vptr sp_b sp_ofs) v Hstore_sp H5).
          right. lia. }
      (* m_sp -> m_final: store at uso+8 *)
      apply (load_after_store_other m_sp m_final sb (uso + 8) (uso + fo)
               block_v v Hstore_accu H6). right. lia. }

    (* sp field *)
    assert (Hsp_load_final : Mem.load Mint64 m_final sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
    { apply Hfield_survive; [left; lia | exact Hsp_load]. }

    assert (Henv_load_final : Mem.load Mint64 m_final sb (uso + 24) = Some env_v).
    { apply Hfield_survive; [right; lia | exact Henv_load]. }

    assert (Hextra_load_final : Mem.load Mint64 m_final sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply Hfield_survive; [right; lia | exact Hextra_load]. }

    assert (Hgd_load_final : Mem.load Mint64 m_final sb (uso + 40) = Some (Vptr gb go0)).
    { apply Hfield_survive; [right; lia | exact Hgd_load]. }

    assert (Hts_load_final : Mem.load Mint64 m_final sb (uso + 48) = Some ts_ptr).
    { apply Hfield_survive; [right; lia | exact Hts_load]. }

    (* Stack repr in m_final *)
    assert (Hsp_ne_new : sp_b <> new_b).
    { intro Heq; symmetry in Heq; exact (Hnew_ne_sp Heq). }
    assert (Hgb_ne_new : gb <> new_b).
    { intro Heq; symmetry in Heq; exact (Hnew_ne_gb Heq). }

    assert (Hstack_m1 : stack_repr hm cb co m1 (Machine.stack s) sp_b sp_ofs).
    { eapply (stack_repr_store_other_block hm cb co); eauto. }

    assert (Hstack_alloc : stack_repr hm cb co m_alloc (Machine.stack s) sp_b sp_ofs).
    { clear -Hstack_m1 Halloc_load_pres Hsp_ne_new.
      induction Hstack_m1 as [| v vs sp_b0 sp_ofs0 cv Hld Hvr Htl IH].
      - constructor.
      - econstructor.
        + apply Halloc_load_pres. exact Hld. exact Hsp_ne_new.
        + exact Hvr.
        + apply IH. exact Hsp_ne_new. }

    assert (Hstack_s0 : stack_repr hm cb co m_s0 (Machine.stack s) sp_b sp_ofs).
    { eapply (stack_repr_store_other_block hm cb co); eauto. }

    assert (Hstack_s1 : stack_repr hm cb co m_s1 (Machine.stack s) sp_b sp_ofs).
    { clear -Hstack_s0 Hf1_load_pres Hsp_ne_new.
      induction Hstack_s0 as [| v vs sp_b0 sp_ofs0 cv Hld Hvr Htl IH].
      - constructor.
      - econstructor.
        + apply Hf1_load_pres.
          * exact Hsp_ne_new.
          * exact Hld.
        + exact Hvr.
        + apply IH. exact Hsp_ne_new. }

    assert (Hstack_pc2 : stack_repr hm cb co m_pc2 (Machine.stack s) sp_b sp_ofs).
    { eapply (stack_repr_store_other_block hm cb co); eauto. }

    assert (Hstack_sp : stack_repr hm cb co m_sp (Machine.stack s) sp_b sp_ofs).
    { eapply (stack_repr_store_other_block hm cb co); eauto. }

    assert (Hstack_final : stack_repr hm cb co m_final (Machine.stack s) sp_b sp_ofs).
    { eapply (stack_repr_store_other_block hm cb co); eauto. }

    (* Global repr in m_final *)
    assert (Hglobal_m1 : global_repr hm cb co m1 (Machine.global s) gb go0).
    { eapply (global_repr_store_other_block hm cb co); eauto. }

    assert (Hglobal_alloc : global_repr hm cb co m_alloc (Machine.global s) gb go0).
    { clear -Hglobal_m1 Halloc_load_pres Hgb_ne_new.
      induction Hglobal_m1 as [| v vs gb0 gofs0 cv Hld Hvr Htl IH].
      - constructor.
      - econstructor.
        + apply Halloc_load_pres. exact Hld. exact Hgb_ne_new.
        + exact Hvr.
        + apply IH. exact Hgb_ne_new. }

    assert (Hglobal_s0 : global_repr hm cb co m_s0 (Machine.global s) gb go0).
    { eapply (global_repr_store_other_block hm cb co); eauto. }

    assert (Hglobal_s1 : global_repr hm cb co m_s1 (Machine.global s) gb go0).
    { clear -Hglobal_s0 Hf1_load_pres Hgb_ne_new.
      induction Hglobal_s0 as [| v vs gb0 gofs0 cv Hld Hvr Htl IH].
      - constructor.
      - econstructor.
        + apply Hf1_load_pres.
          * exact Hgb_ne_new.
          * exact Hld.
        + exact Hvr.
        + apply IH. exact Hgb_ne_new. }

    assert (Hglobal_pc2 : global_repr hm cb co m_pc2 (Machine.global s) gb go0).
    { eapply (global_repr_store_other_block hm cb co); eauto. }

    assert (Hglobal_sp : global_repr hm cb co m_sp (Machine.global s) gb go0).
    { eapply (global_repr_store_other_block hm cb co); eauto. }

    assert (Hglobal_final : global_repr hm cb co m_final (Machine.global s) gb go0).
    { eapply (global_repr_store_other_block hm cb co); eauto. }

    (* Now build abs_rel *)
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s in le' *)
    { subst le' le10 le9 le8 le7 le6 le5 le4 le3 le2 le1.
      repeat (rewrite PTree.gso by (compute; congruence)).
      exact Hle_s. }

    (* 2. pc field -- advanced twice *)
    { exists (Vptr cb pc_ofs_2). split.
      - exact Hpc_load_final.
      - simpl.
        (* Need to show pc_rel for the post-state pc.
           The Rocq post-state has pc = pc'.
           In the dispatch loop, pc' = pc s + 2 (opcode consumed, plus 2 args: nvars and code_ofs).
           The C code advanced pc twice: once for nvars, once for code_ofs.
           So pc_ofs_2 = pc_ofs + 8 = co + (pc s * 4) + 8
                        = co + (pc s + 2) * 4
                        = co + pc' * 4
           But wait: pc' in the Rocq handler_correct is the argument to handle_CLOSURE.
           In the dispatch loop: pc' = pc s + args_consumed.
           For CLOSURE, it consumes 2 args (nvars, code_ofs), so pc' = pc s + 2.
           But actually looking at the Rocq definition:
           handle_CLOSURE nvars code_ofs pc' s -> pc' is externally provided.
           In the dispatch loop: pc' comes from the instruction decoding.

           In the handler_correct framework, s.(pc) is the CURRENT pc before the
           dispatch loop advances it.  abs_rel_pre has pc at s.(pc) + 1
           (dispatch consumed opcode).  But abs_rel (the invariant) has pc at s.(pc).

           For the post-state, the Rocq handler sets pc := pc'.
           The abs_rel postcondition needs:
             pc_rel pc_ptr cb new_co pc'
           where new_co = co + 2 * sizeof_code_t (we advanced pc twice in the handler).

           Actually, looking at MAKEBLOCK1:
             new_co = Ptrofs.add co (Ptrofs.repr sizeof_code_t)
           and pc_rel uses:
             pc_ptr = Vptr cb (Ptrofs.add new_co (Ptrofs.repr (pc' * sizeof_code_t)))

           For CLOSURE, the handler reads 2 values from the code buffer.
           The handler itself advances pc twice (once for nvars, once for code_ofs).
           But wait: the initial pc in abs_rel_with_ard is for the post-dispatch state.
           The pc stored in the struct is: co + (pc s + 1) * sizeof_code_t
           = co + pc s * sizeof_code_t + sizeof_code_t
           = pc_ofs + sizeof_code_t = pc_ofs_1.

           Hmm, actually in the abs_rel_with_ard, the initial pc is:
           pc_rel pc_ptr cb co s.(pc)
           = pc_ptr = Vptr cb (Ptrofs.add co (Ptrofs.repr (s.(pc) * sizeof_code_t)))
           = Vptr cb pc_ofs

           So co is the code base.  After the handler:
           - We advanced pc twice in C (pc_ofs -> pc_ofs_1 -> pc_ofs_2)
           - pc_ofs_2 = pc_ofs + 8 = co + (pc s) * 4 + 8 = co + (pc s + 2) * 4

           For the post abs_rel, we need to choose new_co such that:
           pc_ofs_2 = Ptrofs.add new_co (Ptrofs.repr (pc' * sizeof_code_t))

           But pc' in the Rocq handler is whatever was passed.
           The dispatch loop passes pc' = pc s + number_of_operands + 1
           (where +1 is for the opcode itself).
           For CLOSURE: pc' = pc s + 2 + 1 = pc s + 3? No...

           Let me re-read how handler_correct works. *)
        (* Actually, the abs_rel uses:
           pc_rel pc_ptr cb co s.(pc)
           where s is the PRE-state (before dispatch), and co is part of ard.

           The POST-state abs_rel needs:
           pc_rel pc_ptr' cb co' s'.(pc)
           where s' is the Rocq post-state and co' is the NEW code base.

           The Rocq handle_CLOSURE 0 code_ofs pc' s gives:
           s' with pc = pc'

           The C code starts with pc at co + (pc s) * 4 (from abs_rel).
           Then it:
           1. Advances pc by 1 (reads nvars): pc becomes co + (pc s) * 4 + 4
           2. Later advances pc by 1 again (reads code_ofs): pc becomes co + (pc s) * 4 + 8

           The final C pc is: co + (pc s) * 4 + 8 = co + (pc s + 2) * 4

           For the postcondition abs_rel:
           pc_rel (Vptr cb pc_ofs_2) cb co' pc'

           This means: pc_ofs_2 = Ptrofs.add co' (Ptrofs.repr (pc' * sizeof_code_t))

           co + (pc s) * 4 + 8 = co' + pc' * 4

           If we set co' = co + 2 * 4 = co + 8, then:
           co + (pc s) * 4 + 8 = (co + 8) + pc' * 4
           => (pc s) * 4 = pc' * 4
           => pc s = pc'

           But that's not right. The Rocq handler gets pc' from the dispatch loop.
           In the dispatch loop, for CLOSURE with 2 operands:
           pc' = pc s + 2 (opcode + 2 operands, but opcode was already consumed).

           Hmm, let me look at how MAKEBLOCK1 handles this.

           In MAKEBLOCK1:
           new_co = Ptrofs.add co (Ptrofs.repr sizeof_code_t)
           And the postcondition is pc_rel for pc' where:
           handle_MAKEBLOCK1 t pc' s -> pc' = pc s + 1 (1 operand: tag)

           MAKEBLOCK1 advances pc once in C (reads tag).
           new_co = co + 4
           pc_ofs_after = co + (pc s) * 4 + 4 = (co + 4) + (pc s) * 4

           Then pc_rel (Vptr cb pc_ofs_after) cb new_co (pc s)
           = Vptr cb (Ptrofs.add new_co (Ptrofs.repr ((pc s) * sizeof_code_t)))
           = Vptr cb (Ptrofs.add (co + 4) (Ptrofs.repr ((pc s) * 4)))
           = Vptr cb (co + 4 + (pc s) * 4)
           = Vptr cb (co + (pc s) * 4 + 4)
           = Vptr cb pc_ofs_after  -- correct!

           But wait, the postcondition uses s'.(pc), not pc s.
           In MAKEBLOCK1, s' has pc from the outer wrapper, which sets pc = pc'.
           Actually... let me look at it more carefully.

           In MAKEBLOCK1_correct, the handler_correct says:
           match handler s.(pc) s with Step s' => ... abs_rel e le' m' s'

           handle_MAKEBLOCK1 t does NOT take pc' - it's passed as the
           FIRST argument to handler_correct.  Looking at the definition:
           handler_correct (handle_MAKEBLOCK1 t) f_instr_MAKEBLOCK1 ...

           And handler_correct says:
           match handler s.(pc) s with Step s' => ...

           So handler = handle_MAKEBLOCK1 t, and:
           handle_MAKEBLOCK1 t (pc s) s -- wait, that's not how it works.
           handler_correct takes handler : Z -> state -> step_result.
           So handler (pc s) s = handle_MAKEBLOCK1 t (pc s) s.

           But handle_MAKEBLOCK1 takes t pc' s. So pc' = pc s.

           Hmm, that means for MAKEBLOCK1:
           s' = ... <|pc := pc s|> ...
           And the postcondition abs_rel has s'.(pc) = pc s.
           new_co = co + 4 (shifted by one operand).
           pc_rel ... cb new_co (pc s)
           = Vptr cb (new_co + (pc s) * 4) = Vptr cb (co + 4 + (pc s) * 4)

           That matches the stored pc_ofs_after = co + (pc s) * 4 + 4. Good.

           For CLOSURE:
           handler_correct (handle_CLOSURE 0 code_ofs) f_instr_CLOSURE
           handler = handle_CLOSURE 0 code_ofs : Z -> state -> step_result
           handler (pc s) s = handle_CLOSURE 0 code_ofs (pc s) s
           pc' in handle_CLOSURE = pc s

           So s' has pc = pc s.
           The C advances pc twice (reads nvars and code_ofs).
           new_co = co + 2 * sizeof_code_t = co + 8.
           pc_ofs_2 = co + (pc s) * 4 + 8 = (co + 8) + (pc s) * 4
           pc_rel (Vptr cb pc_ofs_2) cb new_co (pc s)
           = Vptr cb ((co + 8) + (pc s) * 4) -- matches!
        *)
        unfold pc_rel, new_co, pc_ofs_2, pc_ofs_1, pc_ofs, sizeof_code_t.
        rewrite !Ptrofs.add_assoc.
        rewrite <- (Ptrofs.add_assoc (Ptrofs.repr 4) (Ptrofs.repr 4)).
        rewrite (Ptrofs.add_commut (Ptrofs.add (Ptrofs.repr 4) (Ptrofs.repr 4))).
        reflexivity. }

    (* 3. accu field -- Val_closure addr 0 *)
    { exists block_v. split.
      - exact Haccu_load_final.
      - simpl. eapply val_repr_co_shift. exact Hval_repr_new. }

    (* 4. sp field -- unchanged (nvars = 0, stack unchanged) *)
    { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
      - exact Hsp_load_final.
      - reflexivity.
      - simpl. eapply stack_repr_co_shift. apply Hstack_repr_ext. exact Hstack_final.
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - exact Hsp_ge8.
      - exact Hsp_rep.
      - split.
        + intros ofs0 Hofs0.
          eapply Mem.perm_store_1. exact Hstore_accu.
          eapply Mem.perm_store_1. exact Hstore_sp.
          eapply Mem.perm_store_1. exact Hstore_pc2.
          eapply Hf1_perm_pres.
          * eapply Mem.perm_valid_block.
            eapply Mem.perm_store_1. exact Hstore_f0.
            eapply Halloc_perm_pres.
            ** eapply Mem.perm_valid_block.
               apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc1).
               apply (Hsp_writable 0). lia.
            ** eapply Mem.perm_store_1. exact Hstore_pc1.
               apply Hsp_writable. exact Hofs0.
          * eapply Mem.perm_store_1. exact Hstore_f0.
            eapply Halloc_perm_pres.
            ** eapply Mem.perm_valid_block.
               apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc1).
               apply (Hsp_writable 0). lia.
            ** eapply Mem.perm_store_1. exact Hstore_pc1.
               apply Hsp_writable. exact Hofs0.
        + exact Hsp_align. }

    (* 5. env field -- unchanged *)
    { exists env_v. split.
      - exact Henv_load_final.
      - simpl. eapply val_repr_co_shift. apply Hval_repr_ext. exact Henv_repr. }

    (* 6. extra_args field -- unchanged *)
    { simpl. exact Hextra_load_final. }

    (* 7. global_data field -- unchanged *)
    { exists (Vptr gb go0). split; [| split; [| split]].
      - exact Hgd_load_final.
      - simpl. reflexivity.
      - simpl. eapply global_repr_co_shift. apply Hglobal_repr_ext. exact Hglobal_final.
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load_final.
      - simpl. exact Htrap_rel. }

    (* 9. sb_writable *)
    { intros ofs0 Hofs0.
      eapply Mem.perm_store_1. exact Hstore_accu.
      eapply Mem.perm_store_1. exact Hstore_sp.
      eapply Mem.perm_store_1. exact Hstore_pc2.
      eapply Hf1_perm_pres.
      - eapply Mem.perm_valid_block.
        apply (Hsb_writable_s0 (Ptrofs.unsigned so)). lia.
      - apply Hsb_writable_s0. exact Hofs0. }
  }
Qed.
