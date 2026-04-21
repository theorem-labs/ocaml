(* PUSH_RETADDR_correct.v -- PUSH_RETADDR handler correctness proof.

   PUSH_RETADDR pushes 3 values onto the stack:
     sp[0] = (long)(pc + *pc)   -- return address (code pointer)
     sp[1] = env                -- saved environment
     sp[2] = (extra_args<<1)|1  -- saved extra_args (tagged integer)

   Then: pc += 1; return 0.

   Rocq handler (Interpret.v):
     handle_PUSH_RETADDR ret_addr pc' s =
       let frame := Val_int ret_addr :: s.(env) ::
                     Val_int (Z.of_nat s.(extra_args)) :: s.(stack) in
       Step (s <|pc := pc'|> <|stack := frame|>)

   With vr_code_ptr in val_repr, code pointers (Vptr cb ofs) can
   represent Val_int values.  The step_pre provides the branch offset
   and resulting code pointer, bridging the C Vptr and Rocq Val_int.

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
(* Struct layout                                                        *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full) /\
  field_offset ce _extra_args (co_members co) = Errors.OK (32, Full).
Proof.
  eexists. split; [| split; [| split; [| split; [| split]]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_push_retaddr : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full) /\
  field_offset (genv_cenv clight_ge) _extra_args (co_members co) = Errors.OK (32, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Local Lemma sem_sub_sp_3 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 3)) tint
    m = Some (Vptr sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 24))).
Proof.
  intros. unfold sem_binary_operation, sem_sub.
  change (classify_sub (tptr tlong) tint) with (sub_case_pi tlong Signed).
  cbv beta iota.
  change (sizeof (genv_cenv clight_ge) tlong) with 8%Z.
  unfold ptrofs_of_int. reflexivity.
Qed.

Local Lemma sem_cast_ptint_to_long : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) tlong m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

Local Lemma sem_shl_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong n) tlong
    (Vint (Int.repr 1)) tint
    m = Some (Vlong (Int64.shl' n (Int.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl. reflexivity.
Qed.

Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

Local Lemma sem_add_sp_2 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 2)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_ptr_int_tint : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint) (Vint n) tint m
  = Some (Vptr b (Ptrofs.add ofs
        (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                    (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* pc_rel with shifted code base: after pc += 1, code_base advances by sizeof_code_t *)
Local Lemma pc_rel_shift : forall cb co rocq_pc,
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
(* Step precondition                                                    *)
(* ================================================================== *)

(* The step_pre requires:
   1. A branch offset at the current PC in the code buffer, such that
      pc + offset = ret_addr (in code pointer terms).
   2. sp >= 32 to accommodate 3 pushes.
   3. extra_args fits for shl encoding. *)
Definition push_retaddr_step_pre (ret_addr : Z)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  (* There exists a branch offset at the current PC position *)
  (exists ofs_int,
     Mem.load Mint32 m cb
       (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
     = Some (Vint ofs_int) /\
     Ptrofs.add
       (Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t)))
       (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                   (ptrofs_of_int Signed ofs_int))
     = Ptrofs.add co (Ptrofs.repr (ret_addr * sizeof_code_t))) /\
  (* sp >= 32 to accommodate 3 pushes (24 bytes) below current sp *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs >= 32) /\
  (* extra_args fits for shl encoding *)
  Z.of_nat (Machine.extra_args s) < Int64.half_modulus.

(* Tagged integer encoding: (ea << 1) + 1 = ea * 2 + 1 *)
Local Lemma tagged_ea_arith : forall ea,
  0 <= ea -> ea < Int64.half_modulus ->
  Int64.add (Int64.shl' (Int64.repr ea) (Int.repr 1)) (Int64.repr 1)
  = Int64.repr (ea * 2 + 1).
Proof.
  intros ea Hge Hlt.
  unfold Int64.shl', Int64.shl.
  change (Int.unsigned (Int.repr 1)) with 1%Z.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 1)%Z with 2%Z.
  rewrite Int64.add_unsigned.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_trans with (y := (ea * 2 + 1)%Z).
  2: { apply Int64.eqm_refl. }
  apply Int64.eqm_add.
  - apply Int64.eqm_unsigned_repr_l.
    apply Int64.eqm_mult.
    + apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
    + apply Int64.eqm_refl.
  - apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_PUSH_RETADDR_correct : forall ret_addr,
    handler_correct (handle_PUSH_RETADDR ret_addr) f_instr_PUSH_RETADDR
      (push_retaddr_step_pre ret_addr)
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intro ret_addr.
  intros e le m s.
  unfold handler_correct, handle_PUSH_RETADDR. simpl.
  intros ard Hpre Hstep_pre.

  (* Extract abs_rel fields *)
  unfold abs_rel_with_ard in Hpre.
  set (sb := ar_sptr_block ard) in *.
  set (so := ar_sptr_ofs ard) in *.
  set (hm := ar_heap_map ard) in *.
  set (cb := ar_code_base_block ard) in *.
  set (co := ar_code_base_ofs ard) in *.

  destruct Hpre as (Hle_s &
    [pc_ptr [Hpc_load Hpc_rel]] &
    [accu_v [Haccu_load Haccu_repr]] &
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
    [env_v [Henv_load Henv_repr]] &
    Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
    [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
  subst sp_ptr. subst gd_ptr.

  (* Extract step_pre *)
  destruct Hstep_pre as ([ofs_int [Hofs_load Hofs_eq]] & Hsp_ge32 & Hextra_fits).

  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  destruct interp_state_co_push_retaddr as [co_is [Hco [Hpc_offset [Haccu_offset [Hsp_offset [Henv_offset Hextra_offset]]]]]].

  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* Get sp_ofs >= 32 *)
  pose proof (Hsp_ge32 sp_b sp_ofs Hsp_load) as Hsp_ge32'.

  (* new_sp = sp - 3 slots = sp - 24 bytes *)
  set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 24)).

  assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 24).
  { subst new_sp_ofs. unfold Ptrofs.sub.
    change (Ptrofs.unsigned (Ptrofs.repr 24)) with 24.
    apply Ptrofs.unsigned_repr.
    pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }

  (* new sp alignment *)
  assert (Halign_new : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs)).
  { rewrite Hnew_sp_unsigned. simpl.
    apply Z.divide_sub_r; [exact Hsp_align | exists 3; lia]. }

  (* extra_args tagged encoding *)
  set (ea_nat := Machine.extra_args s).
  set (ea_long := Int64.repr (Z.of_nat ea_nat)).
  set (ea_tagged := Int64.add (Int64.shl' ea_long (Int.repr 1)) (Int64.repr 1)).

  (* The code pointer value: pc + *pc gives the return address pointer *)
  set (ret_addr_ofs := Ptrofs.add co (Ptrofs.repr (ret_addr * sizeof_code_t))).
  set (ret_addr_v := Vptr cb ret_addr_ofs).

  (* ---- Store 1: sp field at (sb, uso+16) <- Vptr sp_b new_sp_ofs ---- *)
  destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia)
              (Vptr sp_b new_sp_ofs))
    as [m1 Hstore1].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

  (* sp load in m1 *)
  assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs) Hstore1) as H.
    simpl Val.load_result in H. rewrite ptr64_true in H. exact H. }

  (* Stack writable in m1 *)
  assert (Hsp_writable_m1 : Mem.range_perm m1 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore1. apply Hsp_writable. exact Hofs'. }

  (* ---- Store 2: ret_addr_v at new_sp[0] on the stack block ---- *)
  destruct (Mem.valid_access_store m1 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs) ret_addr_v) as [m2 Hstore2].
  { split.
    - intros ofs' Hofs'. apply Hsp_writable_m1.
      rewrite Hnew_sp_unsigned in Hofs'. simpl size_chunk in Hofs'.
      pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - exact Halign_new. }

  (* ---- Store 3: env at new_sp[1] = new_sp_ofs + 8 ---- *)
  assert (Hsp_writable_m2 : Mem.range_perm m2 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. apply Hsp_writable_m1. exact Hofs'. }
  destruct (Mem.valid_access_store m2 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 8) env_v) as [m3 Hstore3].
  { split.
    - intros ofs' Hofs'. apply Hsp_writable_m2.
      rewrite Hnew_sp_unsigned in Hofs'. simpl size_chunk in Hofs'.
      pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - apply Z.divide_add_r. exact Halign_new. exists 1. simpl. lia. }

  (* ---- Store 4: tagged(extra_args) at new_sp[2] = new_sp_ofs + 16 ---- *)
  assert (Hsp_writable_m3 : Mem.range_perm m3 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore3. apply Hsp_writable_m2. exact Hofs'. }
  destruct (Mem.valid_access_store m3 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 16)
              (Vlong ea_tagged)) as [m4 Hstore4].
  { split.
    - intros ofs' Hofs'. apply Hsp_writable_m3.
      rewrite Hnew_sp_unsigned in Hofs'. simpl size_chunk in Hofs'.
      pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - apply Z.divide_add_r. exact Halign_new. exists 2. simpl. lia. }

  (* sb writable through stack stores *)
  assert (Hsb_writable_m4 : Mem.range_perm m4 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs' Hofs'.
    eapply Mem.perm_store_1. exact Hstore4.
    eapply Mem.perm_store_1. exact Hstore3.
    eapply Mem.perm_store_1. exact Hstore2.
    apply Hsb_writable_m1. exact Hofs'. }

  (* ---- Store 5: pc field at (sb, uso+0) <- new pc value ---- *)
  set (new_pc_ofs := Ptrofs.add co (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))).
  set (new_pc_v := Vptr cb new_pc_ofs).

  assert (Hpc_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { assert (Hpc_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 0)
               (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs) Hstore1 Hpc_load). left. lia. }
    erewrite Mem.load_store_other. 2: exact Hstore4.
    erewrite Mem.load_store_other. 2: exact Hstore3.
    erewrite Mem.load_store_other. 2: exact Hstore2.
    exact Hpc_m1.
    all: left; intro Heq; apply Hsp_ne_sb; auto. }

  destruct (store_succeeds_sb m4 sb so 0 (Vptr cb pc_ofs)
              Hsb_writable_m4 Hpc_load_m4 ltac:(lia) ltac:(lia) new_pc_v)
    as [m5 Hstore5].

  (* ---- Intermediate loads ---- *)

  (* pc load in m1 *)
  assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 0)
             (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs) Hstore1 Hpc_load). left. lia. }

  (* Code buffer load for *pc in m1: offset at pc position *)
  assert (Hofs_load_m1 : Mem.load Mint32 m1 cb
            (Ptrofs.unsigned pc_ofs) = Some (Vint ofs_int)).
  { fold pc_ofs in Hofs_load.
    erewrite Mem.load_store_other. exact Hofs_load. exact Hstore1.
    left. exact Hcb_ne. }

  (* env load in m1 *)
  assert (Henv_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some env_v).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 24)
             (Vptr sp_b new_sp_ofs) env_v Hstore1 Henv_load). right. lia. }

  (* extra_args load in m1 *)
  assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) =
            Some (Vlong ea_long)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 32)
             (Vptr sp_b new_sp_ofs) (Vlong ea_long) Hstore1 Hextra_load). right. lia. }

  (* sp load survives stack stores *)
  assert (Hsp_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { erewrite Mem.load_store_other. exact Hsp_load_m1. exact Hstore2.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hsp_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { erewrite Mem.load_store_other. exact Hsp_load_m2. exact Hstore3.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* pc load survives stack stores *)
  assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { erewrite Mem.load_store_other. exact Hpc_load_m1. exact Hstore2.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* env load survives stack stores *)
  assert (Henv_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 24) = Some env_v).
  { erewrite Mem.load_store_other. exact Henv_load_m1. exact Hstore2.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* extra_args load survives stack stores *)
  assert (Hextra_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 32) =
            Some (Vlong ea_long)).
  { erewrite Mem.load_store_other. 2: exact Hstore3.
    erewrite Mem.load_store_other. 2: exact Hstore2.
    exact Hextra_load_m1.
    all: left; intro Heq; apply Hsp_ne_sb; auto. }

  (* pc load m4 *)
  assert (Hpc_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { erewrite Mem.load_store_other. exact Hpc_load_m2. exact Hstore3.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hpc_load_m4' : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { exact Hpc_load_m4. }

  (* ---- Witnesses for exists ---- *)
  set (le1 := PTree.set _t'10 (Vptr sp_b sp_ofs) le).
  (* After sp store: m1 *)
  set (le2 := PTree.set _t'6 (Vptr sp_b new_sp_ofs) le1).
  set (le3 := PTree.set _t'7 (Vptr cb pc_ofs) le2).
  set (le4 := PTree.set _t'8 (Vptr cb pc_ofs) le3).
  set (le5 := PTree.set _t'9 (Vint ofs_int) le4).
  (* After ret_addr store: m2 *)
  set (le6 := PTree.set _t'4 (Vptr sp_b new_sp_ofs) le5).
  set (le7 := PTree.set _t'5 env_v le6).
  (* After env store: m3 *)
  set (le8 := PTree.set _t'2 (Vptr sp_b new_sp_ofs) le7).
  set (le9 := PTree.set _t'3 (Vlong ea_long) le8).
  (* After ea store: m4 *)
  set (le10 := PTree.set _t'1 (Vptr cb pc_ofs) le9).
  (* After pc field store: m5 *)

  exists le10. exists m5.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ================================================================ *)
  (* Part 1: exec -- the C body executes                               *)
  (* ================================================================ *)
  {
    apply (eval_stmt_to_exec clight_ge 50).
    eval_cbn.

    (* S1: Sset _t'10 (s->sp) *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* S2: Sassign s->sp = _t'10 - 3 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_sub_sp_3 sp_b sp_ofs m); eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    fold new_sp_ofs. rewrite Hstore1; eval_cbn.

    (* S3: Sset _t'6 (s->sp) -- in m1 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m1; eval_cbn.

    (* S4: Sset _t'7 (s->pc) -- in m1 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn.
    try rewrite Hpc_offset; try eval_cbn.
    try rewrite Mptr_Mint64; try eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m1; eval_cbn.

    (* S5: Sset _t'8 (s->pc) -- same value *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn.
    try rewrite Hpc_offset; try eval_cbn.
    try rewrite Mptr_Mint64; try eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m1; eval_cbn.

    (* S6: Sset _t'9 = *_t'8 -- read branch offset *)
    rewrite PTree.gss; eval_cbn.
    rewrite Hofs_load_m1; eval_cbn.

    (* S7: Sassign *(sp + 0) = (long)(pc + *pc) *)
    (* LHS: _t'6 + 0 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_sp_0 sp_b new_sp_ofs m1); eval_cbn.
    (* RHS: Ecast (Ebinop Oadd _t'7 _t'9 (tptr tint)) tlong *)
    (* _t'7 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite PTree.gss; eval_cbn.
    (* _t'9 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite PTree.gss; eval_cbn.
    (* Oadd: ptr + int *)
    rewrite (sem_add_ptr_int_tint cb pc_ofs ofs_int m1); eval_cbn.
    change (sizeof (genv_cenv clight_ge) tint) with 4%Z in Hofs_eq.
    fold co in Hofs_eq.
    fold ret_addr_ofs in Hofs_eq.
    replace (Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) with pc_ofs in Hofs_eq by reflexivity.
    rewrite Hofs_eq.
    (* Cast (tptr tint) -> tlong *)
    rewrite (sem_cast_ptint_to_long cb ret_addr_ofs m1); eval_cbn.
    (* Sassign implicit cast tlong -> tlong *)
    rewrite (sem_cast_long_vptr cb ret_addr_ofs m1); eval_cbn.
    (* Store: ret_addr at sp[0] *)
    fold new_sp_ofs ret_addr_v.
    replace (Val.load_result Mint64 ret_addr_v) with ret_addr_v
      by (unfold ret_addr_v; simpl; rewrite ptr64_true; reflexivity).
    rewrite Hstore2; eval_cbn.

    (* S8: Sset _t'4 (s->sp) -- in m2 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m2; eval_cbn.

    (* S9: Sset _t'5 (s->env) -- in m2 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Henv_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
    rewrite Henv_load_m2; eval_cbn.

    (* S10: Sassign *(sp + 1) = env *)
    (* LHS: _t'4 *)
    rewrite PTree.gso by (cbv; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_sp_1 sp_b new_sp_ofs m2); eval_cbn.
    (* RHS: _t'5 *)
    rewrite PTree.gss; eval_cbn.
    (* Sassign implicit cast tlong -> tlong *)
    rewrite (sem_cast_long_val_repr hm cb co (Machine.env s) env_v m2 Henv_repr); eval_cbn.
    (* Store *)
    assert (Hstore3' : Mem.store Mint64 m2 sp_b
              (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 8))) env_v = Some m3).
    { rewrite (ptrofs_add_unsigned new_sp_ofs 8 ltac:(lia) ltac:(rewrite Hnew_sp_unsigned; lia)).
      exact Hstore3. }
    rewrite Hstore3'; eval_cbn.

    (* S11: Sset _t'2 (s->sp) -- in m3 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m3; eval_cbn.

    (* S12: Sset _t'3 (s->extra_args) -- in m3 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Hextra_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
    rewrite Hextra_load_m3; eval_cbn.

    (* S13: Sassign *(sp + 2) = (ea << 1) + 1 *)
    (* LHS: _t'2 *)
    rewrite PTree.gso by (cbv; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_sp_2 sp_b new_sp_ofs m3); eval_cbn.
    (* RHS: compute (_t'3 << 1) + 1 *)
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_vlong ea_long m3); eval_cbn.
    rewrite (sem_shl_long_int_1 ea_long m3); eval_cbn.
    rewrite (sem_add_long_int_1 (Int64.shl' ea_long (Int.repr 1)) m3); eval_cbn.
    rewrite (sem_cast_long_vlong _ m3); eval_cbn.
    fold ea_tagged.
    (* Store *)
    assert (Hstore4' : Mem.store Mint64 m3 sp_b
              (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 16))) (Vlong ea_tagged) = Some m4).
    { rewrite (ptrofs_add_unsigned new_sp_ofs 16 ltac:(lia) ltac:(rewrite Hnew_sp_unsigned; lia)).
      exact Hstore4. }
    rewrite Hstore4'; eval_cbn.

    (* S14: Sset _t'1 (s->pc) -- in m4 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m4'; eval_cbn.

    (* S15: Sassign s->pc = _t'1 + 1 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_pc_1 cb pc_ofs m4); eval_cbn.
    rewrite (sem_cast_ptr_tint_to_ptr_tint cb _ m4); eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    fold new_pc_v.
    assert (Hpc_ofs_add : Ptrofs.add pc_ofs (Ptrofs.repr 4) = new_pc_ofs).
    { subst pc_ofs new_pc_ofs. rewrite Ptrofs.add_assoc. f_equal.
      unfold sizeof_code_t.
      rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
      apply Ptrofs.eqm_trans with (Machine.pc s * 4 + 4)%Z.
      - apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
      - apply Ptrofs.eqm_refl2. lia. }
    rewrite Hpc_ofs_add. fold new_pc_v.
    rewrite Hstore5; eval_cbn.

    (* S16: Sreturn 0 *)
    reflexivity.
  }

  (* ================================================================ *)
  (* Part 2: abs_rel for post-state                                    *)
  (* ================================================================ *)
  {
    (* Construct ard' with shifted code_base_ofs (pc += 1 advanced by sizeof_code_t) *)
    set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
    set (ard' := mk_abs_rel sb so hm cb new_co
                   (ar_global_block ard) (ar_global_ofs ard)
                   (ar_stack_block ard) (ar_stack_base_ofs ard)
                   (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard)
                   (ar_sptr_ofs_bound ard)).
    exists ard'.

    (* ---- Loads in m5 ---- *)

    (* pc field at uso+0: written in store5 *)
    assert (Hpc_load5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
    { pose proof (load_after_store_same m4 m5 sb (Ptrofs.unsigned so + 0) new_pc_v Hstore5) as H.
      unfold new_pc_v in H. simpl Val.load_result in H. rewrite ptr64_true in H. exact H. }

    (* accu field at uso+8 in m5 *)
    assert (Haccu_load5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { assert (Haccu_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8)
                 (Vptr sp_b new_sp_ofs) accu_v Hstore1 Haccu_load). left. lia. }
      assert (Haccu_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 8) = Some accu_v).
      { erewrite Mem.load_store_other. 2: exact Hstore4.
        erewrite Mem.load_store_other. 2: exact Hstore3.
        erewrite Mem.load_store_other. 2: exact Hstore2.
        exact Haccu_m1.
        all: left; intro Heq; apply Hsp_ne_sb; auto. }
      apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 8)
               new_pc_v accu_v Hstore5 Haccu_m4). right. lia. }

    (* sp field at uso+16 in m5 *)
    assert (Hsp_load5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 16) =
              Some (Vptr sp_b new_sp_ofs)).
    { assert (Hsp_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 16) =
                Some (Vptr sp_b new_sp_ofs)).
      { erewrite Mem.load_store_other. 2: exact Hstore4.
        erewrite Mem.load_store_other. 2: exact Hstore3.
        erewrite Mem.load_store_other. 2: exact Hstore2.
        exact Hsp_load_m1.
        all: left; intro Heq; apply Hsp_ne_sb; auto. }
      apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
               new_pc_v (Vptr sp_b new_sp_ofs) Hstore5 Hsp_m4). right. lia. }

    (* env field at uso+24 in m5 *)
    assert (Henv_load5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { assert (Henv_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 24) = Some env_v).
      { erewrite Mem.load_store_other. 2: exact Hstore4.
        erewrite Mem.load_store_other. 2: exact Hstore3.
        erewrite Mem.load_store_other. 2: exact Hstore2.
        exact Henv_load_m1.
        all: left; intro Heq; apply Hsp_ne_sb; auto. }
      apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 24)
               new_pc_v env_v Hstore5 Henv_m4). right. lia. }

    (* extra_args field at uso+32 in m5 *)
    assert (Hextra_load5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (Machine.extra_args s))))).
    { assert (Hextra_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 32) =
                Some (Vlong ea_long)).
      { erewrite Mem.load_store_other. 2: exact Hstore4.
        erewrite Mem.load_store_other. 2: exact Hstore3.
        erewrite Mem.load_store_other. 2: exact Hstore2.
        exact Hextra_load_m1.
        all: left; intro Heq; apply Hsp_ne_sb; auto. }
      apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 32)
               new_pc_v (Vlong ea_long) Hstore5 Hextra_m4). right. lia. }

    (* global_data field at uso+40 *)
    assert (Hgd_load5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
    { assert (Hgd_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 40)
                 (Vptr sp_b new_sp_ofs) (Vptr (ar_global_block ard) (ar_global_ofs ard)) Hstore1 Hgd_load). right. lia. }
      assert (Hgd_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { erewrite Mem.load_store_other. 2: exact Hstore4.
        erewrite Mem.load_store_other. 2: exact Hstore3.
        erewrite Mem.load_store_other. 2: exact Hstore2.
        exact Hgd_m1.
        all: left; intro Heq; apply Hsp_ne_sb; auto. }
      apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 40)
               new_pc_v (Vptr (ar_global_block ard) (ar_global_ofs ard)) Hstore5 Hgd_m4). right. lia. }

    (* trap_sp field at uso+48 *)
    assert (Hts_load5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
    { assert (Hts_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 48)
                 (Vptr sp_b new_sp_ofs) ts_ptr Hstore1 Hts_load). right. lia. }
      assert (Hts_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { erewrite Mem.load_store_other. 2: exact Hstore4.
        erewrite Mem.load_store_other. 2: exact Hstore3.
        erewrite Mem.load_store_other. 2: exact Hstore2.
        exact Hts_m1.
        all: left; intro Heq; apply Hsp_ne_sb; auto. }
      apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 48)
               new_pc_v ts_ptr Hstore5 Hts_m4). right. lia. }

    (* sb_writable in m5 *)
    assert (Hsb_writable_m5 : Mem.range_perm m5 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs' Hofs'.
      eapply Mem.perm_store_1. exact Hstore5.
      apply Hsb_writable_m4. exact Hofs'. }

    (* ---- Build stack_repr for the new stack ---- *)
    (* New stack: Val_int ret_addr :: env :: Val_int(Z.of_nat ea) :: stack
       at sp_b, new_sp_ofs *)

    (* Build stack_repr for old stack in m5, starting at sp_ofs *)
    assert (Hstk_m5 : stack_repr hm cb co m5 (Machine.stack s) sp_b sp_ofs).
    { eapply stack_repr_store_other_block.
      eapply stack_repr_store_same_block_lower.
      eapply stack_repr_store_same_block_lower.
      eapply stack_repr_store_same_block_lower.
      eapply stack_repr_store_other_block.
      exact Hstack_repr. exact Hstore1.
      intro Heq; apply Hsp_ne_sb; auto.
      exact Hstore2. rewrite Hnew_sp_unsigned. lia. exact Hsp_rep.
      exact Hstore3. rewrite Hnew_sp_unsigned. lia. exact Hsp_rep.
      exact Hstore4. rewrite Hnew_sp_unsigned. lia. exact Hsp_rep.
      exact Hstore5. intro Heq; apply Hsp_ne_sb; auto. }

    (* Build stack_repr for ea :: stack at new_sp_ofs + 16 = sp_ofs - 8 *)
    assert (Hea_stk : stack_repr hm cb co m5 (Val_int (Z.of_nat ea_nat) :: Machine.stack s)
              sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 8))).
    { econstructor.
      - (* Mem.load at sp_ofs - 8 gives ea_tagged *)
        assert (Hea_m4 : Mem.load Mint64 m4 sp_b (Ptrofs.unsigned new_sp_ofs + 16)
                  = Some (Vlong ea_tagged)).
        { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore4) as H.
          simpl Val.load_result in H. exact H. }
        assert (Hea_m5 : Mem.load Mint64 m5 sp_b (Ptrofs.unsigned new_sp_ofs + 16)
                  = Some (Vlong ea_tagged)).
        { erewrite Mem.load_store_other. exact Hea_m4. exact Hstore5.
          left. intro Heq; apply Hsp_ne_sb; auto. }
        unfold Ptrofs.sub.
        rewrite (Ptrofs.unsigned_repr 8).
        2: { pose proof Ptrofs.modulus_pos. unfold Ptrofs.max_unsigned. lia. }
        rewrite Ptrofs.unsigned_repr.
        2: { pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }
        rewrite Hnew_sp_unsigned in Hea_m5.
        replace (Ptrofs.unsigned sp_ofs - 24 + 16) with (Ptrofs.unsigned sp_ofs - 8) in Hea_m5 by lia.
        exact Hea_m5.
      - (* val_repr for tagged ea *)
        unfold ea_tagged, ea_long.
        rewrite tagged_ea_arith by lia.
        constructor.
      - (* rest at sp_ofs *)
        replace (Ptrofs.add (Ptrofs.sub sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8)) with sp_ofs.
        exact Hstk_m5.
        rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc.
        rewrite (Ptrofs.add_commut (Ptrofs.neg (Ptrofs.repr 8)) (Ptrofs.repr 8)).
        rewrite Ptrofs.add_neg_zero, Ptrofs.add_zero. reflexivity. }

    (* Build stack_repr for env :: ea :: stack at new_sp_ofs + 8 = sp_ofs - 16 *)
    assert (Henv_stk : stack_repr hm cb co m5
              (Machine.env s :: Val_int (Z.of_nat ea_nat) :: Machine.stack s)
              sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 16))).
    { econstructor.
      - (* Mem.load at sp_ofs - 16 gives env_v *)
        assert (Henv_sp_m3 : Mem.load Mint64 m3 sp_b (Ptrofs.unsigned new_sp_ofs + 8)
                  = Some env_v).
        { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore3) as H.
          rewrite (val_repr_load_result hm cb co _ _ Henv_repr) in H. exact H. }
        assert (Henv_sp_m5 : Mem.load Mint64 m5 sp_b (Ptrofs.unsigned new_sp_ofs + 8)
                  = Some env_v).
        { erewrite Mem.load_store_other. 2: exact Hstore5.
          erewrite Mem.load_store_other. 2: exact Hstore4.
          exact Henv_sp_m3.
          2: left; intro Heq; apply Hsp_ne_sb; auto.
          right. rewrite Hnew_sp_unsigned. simpl size_chunk. lia. }
        unfold Ptrofs.sub.
        rewrite (Ptrofs.unsigned_repr 16).
        2: { pose proof Ptrofs.modulus_pos. unfold Ptrofs.max_unsigned. lia. }
        rewrite Ptrofs.unsigned_repr.
        2: { pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }
        rewrite Hnew_sp_unsigned in Henv_sp_m5.
        replace (Ptrofs.unsigned sp_ofs - 24 + 8) with (Ptrofs.unsigned sp_ofs - 16) in Henv_sp_m5 by lia.
        exact Henv_sp_m5.
      - exact Henv_repr.
      - replace (Ptrofs.add (Ptrofs.sub sp_ofs (Ptrofs.repr 16)) (Ptrofs.repr 8))
          with (Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
        exact Hea_stk.
        apply Ptrofs.same_if_eq. unfold Ptrofs.eq.
        rewrite (ptrofs_add_unsigned (Ptrofs.sub sp_ofs (Ptrofs.repr 16)) 8).
        2: { lia. }
        2: { unfold Ptrofs.sub. change (Ptrofs.unsigned (Ptrofs.repr 16)) with 16.
             rewrite Ptrofs.unsigned_repr.
             - lia.
             - pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }
        unfold Ptrofs.sub.
        change (Ptrofs.unsigned (Ptrofs.repr 16)) with 16.
        change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
        rewrite !Ptrofs.unsigned_repr.
        2: { pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }
        2: { pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }
        destruct (Coqlib.zeq _ _) as [_|Habs]; [reflexivity | exfalso; apply Habs; lia]. }

    (* Build stack_repr for Val_int ret_addr :: env :: ea :: stack at new_sp_ofs *)
    assert (Hret_stk : stack_repr hm cb co m5
              (Val_int ret_addr :: Machine.env s :: Val_int (Z.of_nat ea_nat) :: Machine.stack s)
              sp_b new_sp_ofs).
    { econstructor.
      - (* Mem.load at new_sp_ofs gives ret_addr_v *)
        assert (Hret_m2 : Mem.load Mint64 m2 sp_b (Ptrofs.unsigned new_sp_ofs) = Some ret_addr_v).
        { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore2) as H.
          unfold ret_addr_v in H. simpl Val.load_result in H. rewrite ptr64_true in H. exact H. }
        erewrite Mem.load_store_other. 2: exact Hstore5.
        erewrite Mem.load_store_other. 2: exact Hstore4.
        erewrite Mem.load_store_other. 2: exact Hstore3.
        exact Hret_m2.
        all: first [ (left; intro Heq; exact (Hsp_ne_sb Heq)) |
                     (right; rewrite Hnew_sp_unsigned; simpl size_chunk; lia) ].
      - (* val_repr for ret_addr: use vr_code_ptr *)
        unfold ret_addr_v, ret_addr_ofs.
        exact (vr_code_ptr hm cb co ret_addr co).
      - replace (Ptrofs.add new_sp_ofs (Ptrofs.repr 8))
          with (Ptrofs.sub sp_ofs (Ptrofs.repr 16)).
        exact Henv_stk.
        apply Ptrofs.same_if_eq. unfold Ptrofs.eq.
        rewrite (ptrofs_add_unsigned new_sp_ofs 8 ltac:(lia) ltac:(rewrite Hnew_sp_unsigned; lia)).
        rewrite Hnew_sp_unsigned.
        unfold Ptrofs.sub.
        change (Ptrofs.unsigned (Ptrofs.repr 16)) with 16.
        rewrite Ptrofs.unsigned_repr.
        2: { pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }
        destruct (Coqlib.zeq _ _) as [_|Habs]; [reflexivity | exfalso; apply Habs; lia]. }

    (* le10 ! _s *)
    assert (Hle10_s : le10 ! _s = Some (Vptr sb so)).
    { subst le10 le9 le8 le7 le6 le5 le4 le3 le2 le1.
      repeat (rewrite PTree.gso by (compute; congruence)).
      exact Hle_s. }

    (* sp_writable in m5 *)
    assert (Hsp_writable_m5 : Mem.range_perm m5 sp_b 0
              (Ptrofs.unsigned new_sp_ofs +
               8 * Z.of_nat (length (Val_int ret_addr :: Machine.env s :: Val_int (Z.of_nat ea_nat) :: Machine.stack s)))
              Cur Writable).
    { intros ofs' Hofs'. simpl length in Hofs'. rewrite Hnew_sp_unsigned in Hofs'.
      eapply Mem.perm_store_1. exact Hstore5.
      eapply Mem.perm_store_1. exact Hstore4.
      eapply Mem.perm_store_1. exact Hstore3.
      eapply Mem.perm_store_1. exact Hstore2.
      eapply Mem.perm_store_1. exact Hstore1.
      apply Hsp_writable. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le' *)
    { exact Hle10_s. }

    (* 2. pc field -- updated to new_pc_v, with shifted code base *)
    { exists new_pc_v. split.
      - exact Hpc_load5.
      - simpl. unfold pc_rel, new_pc_v, new_pc_ofs, new_co.
        f_equal. rewrite Ptrofs.add_assoc. f_equal.
        unfold sizeof_code_t.
        rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
        apply Ptrofs.eqm_trans with (4 + Machine.pc s * 4)%Z.
        + apply Ptrofs.eqm_refl2. lia.
        + apply Ptrofs.eqm_add; apply Ptrofs.eqm_unsigned_repr. }

    (* 3. accu field -- unchanged *)
    { exists accu_v. split.
      - exact Haccu_load5.
      - simpl. eapply val_repr_co_shift. exact Haccu_repr. }

    (* 4. sp field -- points to new_sp_ofs, new stack *)
    { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load5.
      - reflexivity.
      - simpl. eapply stack_repr_co_shift. exact Hret_stk.
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - rewrite Hnew_sp_unsigned. lia.
      - rewrite Hnew_sp_unsigned. simpl length. lia.
      - exact Hsp_writable_m5.
      - exact Halign_new. }

    (* 5. env field -- unchanged *)
    { exists env_v. split.
      - exact Henv_load5.
      - simpl. eapply val_repr_co_shift. exact Henv_repr. }

    (* 6. extra_args field -- unchanged *)
    { simpl. exact Hextra_load5. }

    (* 7. global_data field -- unchanged *)
    { exists (Vptr (ar_global_block ard) (ar_global_ofs ard)). split; [| split; [| split]].
      - exact Hgd_load5.
      - simpl. reflexivity.
      - simpl. eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m4 m5 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (Ptrofs.unsigned so + 0) new_pc_v).
        apply (global_repr_store_other_block hm cb co m3 m4 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sp_b (Ptrofs.unsigned new_sp_ofs + 16) (Vlong ea_tagged)).
        apply (global_repr_store_other_block hm cb co m2 m3 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sp_b (Ptrofs.unsigned new_sp_ofs + 8) env_v).
        apply (global_repr_store_other_block hm cb co m1 m2 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sp_b (Ptrofs.unsigned new_sp_ofs) ret_addr_v).
        apply (global_repr_store_other_block hm cb co m m1 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)).
        exact Hglobal_repr.
        exact Hstore1. intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
        exact Hstore2. intro Heq2; exact (Hsp_ne_gb Heq2).
        exact Hstore3. intro Heq2; exact (Hsp_ne_gb Heq2).
        exact Hstore4. intro Heq2; exact (Hsp_ne_gb Heq2).
        exact Hstore5. intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load5.
      - simpl. exact Htrap_rel. }

    (* 9. sb_writable *)
    { exact Hsb_writable_m5. }
  }
Qed.

(* Wrapper with the exact type expected by InstructVerificationProof.v.
   handle_instr (PUSH_RETADDR z) = handle_PUSH_RETADDR z and
   clight_of (PUSH_RETADDR z) = f_instr_PUSH_RETADDR by computation.
   pre_of (PUSH_RETADDR z) = push_retaddr_step_pre z by computation.
   Since handle_PUSH_RETADDR always returns Step, the P_error/P_halt/P_ccall
   predicates are dead code in the match — the proof term is identical. *)
Import Bytecode.AST.
Definition correct_PUSH_RETADDR : forall z,
    handler_correct (handle_instr (PUSH_RETADDR z)) (clight_of (PUSH_RETADDR z))
      (pre_of (PUSH_RETADDR z))
      (P_error_of (PUSH_RETADDR z)) (P_halt_of (PUSH_RETADDR z)) (P_ccall_of (PUSH_RETADDR z)).
Proof.
  intro z.
  exact (verify_PUSH_RETADDR_correct z).
Qed.
