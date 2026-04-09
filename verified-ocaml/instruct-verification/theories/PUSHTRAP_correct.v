(* PUSHTRAP_correct.v -- PUSHTRAP handler correctness proof.

   PUSHTRAP pushes 4 values onto the stack and updates trap_sp:
     sp[0] = (tptr tint)(pc + *pc)       -- handler address (code pointer)
     sp[1] = ((trap_sp - new_sp) << 1)|1 -- tagged trap link (distance)
     sp[2] = env                         -- saved environment
     sp[3] = (extra_args << 1) | 1       -- tagged extra_args

   Then: trap_sp = new_sp; pc += 1; return 0.

   Rocq handler (Interpret.v):
     handle_PUSHTRAP handler_pc pc' s =
       let prev_tsp := Val_int (Z.of_nat s.(trap_sp)) in
       let new_stack := Val_int handler_pc :: prev_tsp ::
                        s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: s.(stack) in
       let new_tsp := length new_stack in
       Step (s <|pc := pc'|> <|stack := new_stack|> <|trap_sp := new_tsp|>)

   Key design: vr_code_ptr makes val_repr for sp[0] trivial regardless of
   the specific branch offset.  The step_pre provides all arithmetic needed.

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
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul Ptrofs.of_ints
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout                                                        *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets_pushtrap : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full) /\
  field_offset ce _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset ce _trap_sp (co_members co) = Errors.OK (48, Full).
Proof.
  eexists. split; [| split; [| split; [| split; [| split; [| split]]]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce_pushtrap : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_pushtrap : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full) /\
  field_offset (genv_cenv clight_ge) _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset (genv_cenv clight_ge) _trap_sp (co_members co) = Errors.OK (48, Full).
Proof.
  rewrite cenv_is_ce_pushtrap. exact ce_offsets_pushtrap.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Local Lemma sem_sub_sp_4 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 4)) tint
    m = Some (Vptr sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 32))).
Proof.
  intros. unfold sem_binary_operation, sem_sub.
  change (classify_sub (tptr tlong) tint) with (sub_case_pi tlong Signed).
  cbv beta iota.
  change (sizeof (genv_cenv clight_ge) tlong) with 8%Z.
  unfold ptrofs_of_int. reflexivity.
Qed.

Local Lemma sem_add_sp_3 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 3)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 24))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_sp_2_local : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 2)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* Cast tptr tlong -> tptr (tptr tint): pointer-to-pointer = identity on 64-bit *)
Local Lemma sem_cast_ptrtlong_to_ptrptrint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tlong) (tptr (tptr tint)) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast.
  change (classify_cast (tptr tlong) (tptr (tptr tint))) with cast_case_pointer.
  reflexivity.
Qed.

(* tptr (tptr tint) + 0 = same ptr *)
Local Lemma sem_add_sp_0_ptrint : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr (tptr tint))
    (Vint (Int.repr 0)) tint
    m = Some (Vptr sp_b sp_ofs).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr (tptr tint)) tint) with (add_case_pi (tptr tint) Signed).
  unfold sem_add_ptr_int. f_equal. f_equal.
  change (sizeof (genv_cenv clight_ge) (tptr tint)) with 8%Z.
  unfold ptrofs_of_int.
  change (Ptrofs.of_ints (Int.repr 0)) with Ptrofs.zero.
  rewrite Ptrofs.mul_zero, Ptrofs.add_zero. reflexivity.
Qed.

Local Lemma sem_add_ptr_int_tint_local : forall b ofs n m,
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

Local Lemma sem_cast_ptr_tint_to_ptr_tint_local : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_add_pc_1_local : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma tagged_int_arith : forall n,
  0 <= n -> n < Int64.half_modulus ->
  Int64.add (Int64.shl' (Int64.repr n) (Int.repr 1)) (Int64.repr 1)
  = Int64.repr (n * 2 + 1).
Proof.
  intros n Hge Hlt.
  unfold Int64.shl', Int64.shl.
  change (Int.unsigned (Int.repr 1)) with 1%Z.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 1)%Z with 2%Z.
  rewrite Int64.add_unsigned.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_trans with (y := (n * 2 + 1)%Z).
  2: { apply Int64.eqm_refl. }
  apply Int64.eqm_add.
  - apply Int64.eqm_unsigned_repr_l.
    apply Int64.eqm_mult.
    + apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
    + apply Int64.eqm_refl.
  - apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
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
    (Vlong n) tlong
    (Vint (Int.repr 1)) tint
    m = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add tlong tint) with add_default.
  unfold sem_binarith. simpl. reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_PUSHTRAP_correct : forall handler_pc,
    handler_correct (handle_PUSHTRAP handler_pc) f_instr_PUSHTRAP
      (pushtrap_step_pre handler_pc)
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intro handler_pc.
  intros e le m s.
  unfold handler_correct, handle_PUSHTRAP. simpl.
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
  unfold pushtrap_step_pre in Hstep_pre.
  fold sb so hm cb co in Hstep_pre.
  destruct Hstep_pre as
    ([ofs_int Hofs_load] & Hsp_ge40 & Hextra_fits & Htrap_fits &
     Htrap_sub & Htrap_rel_new).

  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  destruct interp_state_co_pushtrap as [co_is [Hco [Hpc_offset [Haccu_offset [Hsp_offset [Henv_offset [Hextra_offset Htrap_sp_offset]]]]]]].

  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* Get sp_ofs >= 40 *)
  pose proof (Hsp_ge40 sp_b sp_ofs Hsp_load) as Hsp_ge40'.

  (* new_sp = sp - 4 slots = sp - 32 bytes *)
  set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 32)).

  assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 32).
  { subst new_sp_ofs. unfold Ptrofs.sub.
    change (Ptrofs.unsigned (Ptrofs.repr 32)) with 32.
    apply Ptrofs.unsigned_repr.
    pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }

  (* new sp alignment *)
  assert (Halign_new : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs)).
  { rewrite Hnew_sp_unsigned. simpl.
    apply Z.divide_sub_r; [exact Hsp_align | exists 4; lia]. }

  (* extra_args and trap_sp tagged values *)
  set (ea_nat := Machine.extra_args s).
  set (ea_long := Int64.repr (Z.of_nat ea_nat)).
  set (ea_tagged := Int64.add (Int64.shl' ea_long (Int.repr 1)) (Int64.repr 1)).

  set (tsp_nat := Machine.trap_sp s).
  set (tsp_tagged := Int64.add (Int64.shl' (Int64.repr (Z.of_nat tsp_nat)) (Int.repr 1)) (Int64.repr 1)).

  (* Trap link computation (in m; sem_sub doesn't access memory so also in m1/m2) *)
  pose proof (Htrap_sub sp_b sp_ofs ts_ptr Hsp_load Hts_load) as Htrap_sub'.

  (* New trap_sp_rel for post-state *)
  pose proof (Htrap_rel_new sp_b sp_ofs Hsp_load) as Htrap_rel_new'.

  (* handler addr values — use numeric 4 so fold handler_ofs works after eval_cbn
     reduces sizeof (genv_cenv clight_ge) tint to 4 *)
  set (handler_ofs := Ptrofs.add pc_ofs
         (Ptrofs.mul (Ptrofs.repr 4)
                     (ptrofs_of_int Signed ofs_int))).
  set (handler_addr_v := Vptr cb handler_ofs).

  (* ---- Store 1: sp field at (sb, uso+16) <- Vptr sp_b new_sp_ofs ---- *)
  destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia)
              (Vptr sp_b new_sp_ofs))
    as [m1 Hstore1].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

  assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs) Hstore1) as H.
    simpl Val.load_result in H. rewrite ptr64_true in H. exact H. }

  assert (Hsp_writable_m1 : Mem.range_perm m1 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore1. apply Hsp_writable. exact Hofs'. }

  (* ---- Store 2: handler_addr at new_sp[0] ---- *)
  destruct (Mem.valid_access_store m1 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs) handler_addr_v) as [m2 Hstore2].
  { split.
    - intros ofs' Hofs'. apply Hsp_writable_m1.
      rewrite Hnew_sp_unsigned in Hofs'. simpl size_chunk in Hofs'.
      pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - exact Halign_new. }

  assert (Hsp_writable_m2 : Mem.range_perm m2 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. apply Hsp_writable_m1. exact Hofs'. }

  (* ---- Store 3: tagged trap_link at new_sp[1] ---- *)
  assert (Htrap_sub_m2 : sem_binary_operation (genv_cenv clight_ge) Osub ts_ptr (tptr tlong)
            (Vptr sp_b new_sp_ofs) (tptr tlong) m2
          = Some (Vlong (Int64.repr (Z.of_nat tsp_nat)))).
  { exact Htrap_sub'. }

  destruct (Mem.valid_access_store m2 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 8)
              (Vlong tsp_tagged)) as [m3 Hstore3].
  { split.
    - intros ofs' Hofs'. apply Hsp_writable_m2.
      rewrite Hnew_sp_unsigned in Hofs'. simpl size_chunk in Hofs'.
      pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - apply Z.divide_add_r. exact Halign_new. exists 1. simpl. lia. }

  assert (Hsp_writable_m3 : Mem.range_perm m3 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore3. apply Hsp_writable_m2. exact Hofs'. }

  (* ---- Store 4: env_v at new_sp[2] ---- *)
  destruct (Mem.valid_access_store m3 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 16) env_v) as [m4 Hstore4].
  { split.
    - intros ofs' Hofs'. apply Hsp_writable_m3.
      rewrite Hnew_sp_unsigned in Hofs'. simpl size_chunk in Hofs'.
      pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - apply Z.divide_add_r. exact Halign_new. exists 2. simpl. lia. }

  assert (Hsp_writable_m4 : Mem.range_perm m4 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore4. apply Hsp_writable_m3. exact Hofs'. }

  (* ---- Store 5: tagged ea at new_sp[3] ---- *)
  destruct (Mem.valid_access_store m4 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 24)
              (Vlong ea_tagged)) as [m5 Hstore5].
  { split.
    - intros ofs' Hofs'. apply Hsp_writable_m4.
      rewrite Hnew_sp_unsigned in Hofs'. simpl size_chunk in Hofs'.
      pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - apply Z.divide_add_r. exact Halign_new. exists 3. simpl. lia. }

  (* sb writable through stack stores *)
  assert (Hsb_writable_m5 : Mem.range_perm m5 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs' Hofs'.
    eapply Mem.perm_store_1. exact Hstore5.
    eapply Mem.perm_store_1. exact Hstore4.
    eapply Mem.perm_store_1. exact Hstore3.
    eapply Mem.perm_store_1. exact Hstore2.
    apply Hsb_writable_m1. exact Hofs'. }

  (* ---- Store 6: trap_sp field at (sb, uso+48) <- Vptr sp_b new_sp_ofs ---- *)
  assert (Hts_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 48)
             (Vptr sp_b new_sp_ofs) ts_ptr Hstore1 Hts_load). right. lia. }

  assert (Hts_load_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
  { erewrite Mem.load_store_other. 2: exact Hstore5.
    erewrite Mem.load_store_other. 2: exact Hstore4.
    erewrite Mem.load_store_other. 2: exact Hstore3.
    erewrite Mem.load_store_other. 2: exact Hstore2.
    exact Hts_load_m1.
    all: left; intro Heq; apply Hsp_ne_sb; auto. }

  destruct (store_succeeds_sb m5 sb so 48 ts_ptr Hsb_writable_m5 Hts_load_m5 ltac:(lia) ltac:(lia)
              (Vptr sp_b new_sp_ofs))
    as [m6 Hstore6].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore6 Hsb_writable_m5) as Hsb_writable_m6.

  (* ---- Store 7: pc field at (sb, uso+0) <- new pc ---- *)
  set (new_pc_ofs := Ptrofs.add co (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))).
  set (new_pc_v := Vptr cb new_pc_ofs).

  assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 0)
             (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs) Hstore1 Hpc_load). left. lia. }

  assert (Hpc_load_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { erewrite Mem.load_store_other. 2: exact Hstore5.
    erewrite Mem.load_store_other. 2: exact Hstore4.
    erewrite Mem.load_store_other. 2: exact Hstore3.
    erewrite Mem.load_store_other. 2: exact Hstore2.
    exact Hpc_load_m1.
    all: left; intro Heq; apply Hsp_ne_sb; auto. }

  assert (Hpc_load_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 48) (Ptrofs.unsigned so + 0)
             (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs) Hstore6 Hpc_load_m5). left. lia. }

  destruct (store_succeeds_sb m6 sb so 0 (Vptr cb pc_ofs)
              Hsb_writable_m6 Hpc_load_m6 ltac:(lia) ltac:(lia) new_pc_v)
    as [m7 Hstore7].

  (* ---- Intermediate loads ---- *)

  (* Code buffer *pc in m1 *)
  assert (Hofs_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) = Some (Vint ofs_int)).
  { erewrite Mem.load_store_other. exact Hofs_load. exact Hstore1. left. exact Hcb_ne. }

  (* sp load in m2, m3, m4 *)
  assert (Hsp_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b new_sp_ofs)).
  { erewrite Mem.load_store_other. exact Hsp_load_m1. exact Hstore2.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hsp_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b new_sp_ofs)).
  { erewrite Mem.load_store_other. exact Hsp_load_m2. exact Hstore3.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hsp_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b new_sp_ofs)).
  { erewrite Mem.load_store_other. exact Hsp_load_m3. exact Hstore4.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hsp_load_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b new_sp_ofs)).
  { erewrite Mem.load_store_other. exact Hsp_load_m4. exact Hstore5.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* trap_sp load in m2 (for S9 subtraction) *)
  assert (Hts_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
  { erewrite Mem.load_store_other. exact Hts_load_m1. exact Hstore2.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* pc load in m2 *)
  assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) = Some (Vptr cb pc_ofs)).
  { erewrite Mem.load_store_other. exact Hpc_load_m1. exact Hstore2.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* env load in m1, m3 *)
  assert (Henv_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some env_v).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 24)
             (Vptr sp_b new_sp_ofs) env_v Hstore1 Henv_load). right. lia. }
  assert (Henv_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 24) = Some env_v).
  { erewrite Mem.load_store_other. 2: exact Hstore3.
    erewrite Mem.load_store_other. 2: exact Hstore2.
    exact Henv_load_m1.
    all: left; intro Heq; apply Hsp_ne_sb; auto. }

  (* extra_args load in m1, m4 *)
  assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) = Some (Vlong ea_long)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 32)
             (Vptr sp_b new_sp_ofs) (Vlong ea_long) Hstore1 Hextra_load). right. lia. }
  assert (Hextra_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 32) = Some (Vlong ea_long)).
  { erewrite Mem.load_store_other. 2: exact Hstore4.
    erewrite Mem.load_store_other. 2: exact Hstore3.
    erewrite Mem.load_store_other. 2: exact Hstore2.
    exact Hextra_load_m1.
    all: left; intro Heq; apply Hsp_ne_sb; auto. }

  (* ---- Witnesses ---- *)
  set (le1 := PTree.set _t'14 (Vptr sp_b sp_ofs) le).
  set (le2 := PTree.set _t'10 (Vptr sp_b new_sp_ofs) le1).
  set (le3 := PTree.set _t'11 (Vptr cb pc_ofs) le2).
  set (le4 := PTree.set _t'12 (Vptr cb pc_ofs) le3).
  set (le5 := PTree.set _t'13 (Vint ofs_int) le4).
  set (le6 := PTree.set _t'7 (Vptr sp_b new_sp_ofs) le5).
  set (le7 := PTree.set _t'8 ts_ptr le6).
  set (le8 := PTree.set _t'9 (Vptr sp_b new_sp_ofs) le7).
  set (le9 := PTree.set _t'5 (Vptr sp_b new_sp_ofs) le8).
  set (le10 := PTree.set _t'6 env_v le9).
  set (le11 := PTree.set _t'3 (Vptr sp_b new_sp_ofs) le10).
  set (le12 := PTree.set _t'4 (Vlong ea_long) le11).
  set (le13 := PTree.set _t'2 (Vptr sp_b new_sp_ofs) le12).
  set (le14 := PTree.set _t'1 (Vptr cb pc_ofs) le13).

  exists le14. exists m7.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ================================================================ *)
  (* Part 1: exec -- the C body executes                               *)
  (* ================================================================ *)
  {
    apply (eval_stmt_to_exec clight_ge 60).
    eval_cbn.

    (* S1: Sset _t'14 (s->sp) -- read old sp *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* S2: Sassign s->sp = _t'14 - 4 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_sub_sp_4 sp_b sp_ofs m); eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    fold new_sp_ofs. rewrite Hstore1; eval_cbn.

    (* S3: Sset _t'10 (s->sp) -- read new sp in m1 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m1; eval_cbn.

    (* S4: Sset _t'11 (s->pc) -- read pc *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Hpc_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m1; eval_cbn.

    (* S5: Sset _t'12 (s->pc) -- read pc again *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m1; eval_cbn.

    (* S6: Sset _t'13 = *_t'12 -- read branch offset *)
    rewrite PTree.gss; eval_cbn.
    rewrite Hofs_load_m1; eval_cbn.

    (* S7: Sassign *(cast(sp, tptr(tptr int)) + 0) = pc + offset -- sp[0] = handler addr *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_ptrtlong_to_ptrptrint sp_b new_sp_ofs m1); eval_cbn.
    rewrite (sem_add_sp_0_ptrint sp_b new_sp_ofs m1); eval_cbn.
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite PTree.gss; eval_cbn.
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_ptr_int_tint_local cb pc_ofs ofs_int m1).
    change (sizeof (genv_cenv clight_ge) tint) with 4%Z.
    fold handler_ofs.
    rewrite (sem_cast_ptr_tint_to_ptr_tint_local cb handler_ofs m1); eval_cbn.
    fold handler_addr_v.
    change Mptr with Mint64.
    replace (Val.load_result Mint64 handler_addr_v) with handler_addr_v
      by (unfold handler_addr_v; simpl; rewrite ptr64_true; reflexivity).
    rewrite Hstore2; eval_cbn.

    (* S8: Sset _t'7 (s->sp) -- in m2 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m2; eval_cbn.

    (* S9: Sset _t'8 (s->trap_sp) -- in m2 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Htrap_sp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 48 ltac:(lia) ltac:(lia)).
    rewrite Hts_load_m2; eval_cbn.

    (* S10: Sset _t'9 (s->sp) -- in m2 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m2; eval_cbn.

    (* S11: Sassign *(sp + 1) = ((_t'8 - _t'9) << 1) | 1 -- sp[1] = tagged trap link *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.
    rewrite (sem_add_sp_1 sp_b new_sp_ofs m2); eval_cbn.
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite PTree.gss; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    (* sem_sub ts_ptr new_sp *)
    rewrite Htrap_sub_m2; eval_cbn.
    (* cast tlong -> tlong *)
    rewrite (sem_cast_long_vlong _ m2); eval_cbn.
    (* shl by 1 *)
    rewrite (sem_shl_long_int_1 _ m2); eval_cbn.
    (* add 1 *)
    rewrite (sem_add_long_int_1 _ m2); eval_cbn.
    rewrite (sem_cast_long_vlong _ m2); eval_cbn.
    fold tsp_tagged.
    (* Store *)
    assert (Hstore3' : Mem.store Mint64 m2 sp_b
              (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 8)))
              (Vlong tsp_tagged) = Some m3).
    { rewrite (ptrofs_add_unsigned new_sp_ofs 8 ltac:(lia) ltac:(rewrite Hnew_sp_unsigned; lia)).
      unfold tsp_tagged. exact Hstore3. }
    replace (Val.load_result Mint64 (Vlong tsp_tagged)) with (Vlong tsp_tagged)
      by reflexivity.
    rewrite Hstore3'; eval_cbn.

    (* S12: Sset _t'5 (s->sp) -- in m3 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m3; eval_cbn.

    (* S13: Sset _t'6 (s->env) -- in m3 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Henv_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
    rewrite Henv_load_m3; eval_cbn.

    (* S14: Sassign *(sp + 2) = env -- sp[2] = env *)
    rewrite PTree.gso by (cbv; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_sp_2_local sp_b new_sp_ofs m3); eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr hm cb co (Machine.env s) env_v m3 Henv_repr); eval_cbn.
    assert (Hstore4' : Mem.store Mint64 m3 sp_b
              (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 16))) env_v = Some m4).
    { rewrite (ptrofs_add_unsigned new_sp_ofs 16 ltac:(lia) ltac:(rewrite Hnew_sp_unsigned; lia)).
      exact Hstore4. }
    rewrite Hstore4'; eval_cbn.

    (* S15: Sset _t'3 (s->sp) -- in m4 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m4; eval_cbn.

    (* S16: Sset _t'4 (s->extra_args) -- in m4 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Hextra_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
    rewrite Hextra_load_m4; eval_cbn.

    (* S17: Sassign *(sp + 3) = (ea << 1) | 1 -- sp[3] = tagged ea *)
    rewrite PTree.gso by (cbv; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_sp_3 sp_b new_sp_ofs m4); eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_vlong ea_long m4); eval_cbn.
    rewrite (sem_shl_long_int_1 ea_long m4); eval_cbn.
    rewrite (sem_add_long_int_1 _ m4); eval_cbn.
    rewrite (sem_cast_long_vlong _ m4); eval_cbn.
    fold ea_tagged.
    assert (Hstore5' : Mem.store Mint64 m4 sp_b
              (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 24))) (Vlong ea_tagged) = Some m5).
    { rewrite (ptrofs_add_unsigned new_sp_ofs 24 ltac:(lia) ltac:(rewrite Hnew_sp_unsigned; lia)).
      exact Hstore5. }
    rewrite Hstore5'; eval_cbn.

    (* S18: Sset _t'2 (s->sp) -- in m5 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m5; eval_cbn.

    (* S19: Sassign s->trap_sp = _t'2 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 48 ltac:(lia) ltac:(lia)).
    rewrite Hstore6; eval_cbn.

    (* S20: Sset _t'1 (s->pc) -- in m6 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m6; eval_cbn.

    (* S21: Sassign s->pc = _t'1 + 1 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_pc_1_local cb pc_ofs m6); eval_cbn.
    rewrite (sem_cast_ptr_tint_to_ptr_tint_local cb _ m6); eval_cbn.
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
    rewrite Hstore7; eval_cbn.

    (* S22: Sreturn 0 *)
    reflexivity.
  }

  (* ================================================================ *)
  (* Part 2: abs_rel for post-state                                    *)
  (* ================================================================ *)
  {
    set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
    set (ard' := mk_abs_rel sb so hm cb new_co
                   (ar_global_block ard) (ar_global_ofs ard)
                   (ar_stack_block ard) (ar_stack_base_ofs ard)
                   (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard)
                   (ar_sptr_ofs_bound ard)).
    exists ard'.

    (* ---- Loads in m7 ---- *)

    assert (Hpc_load7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
    { pose proof (load_after_store_same m6 m7 sb (Ptrofs.unsigned so + 0) new_pc_v Hstore7) as H.
      unfold new_pc_v in H. simpl Val.load_result in H. rewrite ptr64_true in H. exact H. }

    assert (Haccu_load7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { assert (Haccu_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8)
                 (Vptr sp_b new_sp_ofs) accu_v Hstore1 Haccu_load). left. lia. }
      assert (Haccu_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 8) = Some accu_v).
      { erewrite Mem.load_store_other. 2: exact Hstore5.
        erewrite Mem.load_store_other. 2: exact Hstore4.
        erewrite Mem.load_store_other. 2: exact Hstore3.
        erewrite Mem.load_store_other. 2: exact Hstore2.
        exact Haccu_m1.
        all: left; intro Heq; apply Hsp_ne_sb; auto. }
      assert (Haccu_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 8) = Some accu_v).
      { apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 48) (Ptrofs.unsigned so + 8)
                 (Vptr sp_b new_sp_ofs) accu_v Hstore6 Haccu_m5). left. lia. }
      apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 8)
               new_pc_v accu_v Hstore7 Haccu_m6). right. lia. }

    assert (Hsp_load7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 16) =
              Some (Vptr sp_b new_sp_ofs)).
    { assert (Hsp_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 16) =
                Some (Vptr sp_b new_sp_ofs)).
      { apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 48) (Ptrofs.unsigned so + 16)
                 (Vptr sp_b new_sp_ofs) (Vptr sp_b new_sp_ofs) Hstore6 Hsp_load_m5). left. lia. }
      apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
               new_pc_v (Vptr sp_b new_sp_ofs) Hstore7 Hsp_m6). right. lia. }

    assert (Henv_load7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { assert (Henv_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 24) = Some env_v).
      { erewrite Mem.load_store_other. 2: exact Hstore5.
        erewrite Mem.load_store_other. 2: exact Hstore4.
        erewrite Mem.load_store_other. 2: exact Hstore3.
        erewrite Mem.load_store_other. 2: exact Hstore2.
        exact Henv_load_m1.
        all: left; intro Heq; apply Hsp_ne_sb; auto. }
      assert (Henv_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 24) = Some env_v).
      { apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 48) (Ptrofs.unsigned so + 24)
                 (Vptr sp_b new_sp_ofs) env_v Hstore6 Henv_m5). left. lia. }
      apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 24)
               new_pc_v env_v Hstore7 Henv_m6). right. lia. }

    assert (Hextra_load7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (Machine.extra_args s))))).
    { assert (Hextra_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 32) =
                Some (Vlong ea_long)).
      { erewrite Mem.load_store_other. 2: exact Hstore5. exact Hextra_load_m4.
        left; intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hextra_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 32) = Some (Vlong ea_long)).
      { apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 48) (Ptrofs.unsigned so + 32)
                 (Vptr sp_b new_sp_ofs) (Vlong ea_long) Hstore6 Hextra_m5). left. lia. }
      apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 32)
               new_pc_v (Vlong ea_long) Hstore7 Hextra_m6). right. lia. }

    assert (Hgd_load7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 40) =
              Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
    { assert (Hgd_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 40) =
                Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 40)
                 (Vptr sp_b new_sp_ofs) (Vptr (ar_global_block ard) (ar_global_ofs ard)) Hstore1 Hgd_load). right. lia. }
      assert (Hgd_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 40) =
                Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { erewrite Mem.load_store_other. 2: exact Hstore5.
        erewrite Mem.load_store_other. 2: exact Hstore4.
        erewrite Mem.load_store_other. 2: exact Hstore3.
        erewrite Mem.load_store_other. 2: exact Hstore2.
        exact Hgd_m1.
        all: left; intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hgd_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 40) =
                Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 48) (Ptrofs.unsigned so + 40)
                 (Vptr sp_b new_sp_ofs) (Vptr (ar_global_block ard) (ar_global_ofs ard)) Hstore6 Hgd_m5). left. lia. }
      apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 40)
               new_pc_v (Vptr (ar_global_block ard) (ar_global_ofs ard)) Hstore7 Hgd_m6). right. lia. }

    (* trap_sp field: now = new_sp (written by store6) *)
    assert (Hts_load7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 48) =
              Some (Vptr sp_b new_sp_ofs)).
    { assert (Hts_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 48) = Some (Vptr sp_b new_sp_ofs)).
      { pose proof (load_after_store_same m5 m6 sb (Ptrofs.unsigned so + 48) (Vptr sp_b new_sp_ofs) Hstore6) as H.
        simpl Val.load_result in H. rewrite ptr64_true in H. exact H. }
      apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 48)
               new_pc_v (Vptr sp_b new_sp_ofs) Hstore7 Hts_m6). right. lia. }

    assert (Hsb_writable_m7 : Mem.range_perm m7 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs' Hofs'.
      eapply Mem.perm_store_1. exact Hstore7.
      apply Hsb_writable_m6. exact Hofs'. }

    (* ---- Build stack_repr for the new stack ---- *)

    (* Old stack in m7 *)
    assert (Hstk_m7 : stack_repr hm cb co m7 (Machine.stack s) sp_b sp_ofs).
    { eapply stack_repr_store_other_block.
      eapply stack_repr_store_other_block.
      eapply stack_repr_store_same_block_lower.
      eapply stack_repr_store_same_block_lower.
      eapply stack_repr_store_same_block_lower.
      eapply stack_repr_store_same_block_lower.
      eapply stack_repr_store_other_block.
      exact Hstack_repr. exact Hstore1. intro Heq; apply Hsp_ne_sb; auto.
      exact Hstore2. rewrite Hnew_sp_unsigned. lia. exact Hsp_rep.
      exact Hstore3. rewrite Hnew_sp_unsigned. lia. exact Hsp_rep.
      exact Hstore4. rewrite Hnew_sp_unsigned. lia. exact Hsp_rep.
      exact Hstore5. rewrite Hnew_sp_unsigned. lia. exact Hsp_rep.
      exact Hstore6. intro Heq; apply Hsp_ne_sb; auto.
      exact Hstore7. intro Heq; apply Hsp_ne_sb; auto. }

    (* ea :: old_stack at sp_ofs - 8 = new_sp_ofs + 24 *)
    assert (Hea_stk : stack_repr hm cb co m7 (Val_int (Z.of_nat ea_nat) :: Machine.stack s)
              sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 8))).
    { econstructor.
      - assert (Hea_m5 : Mem.load Mint64 m5 sp_b (Ptrofs.unsigned new_sp_ofs + 24) = Some (Vlong ea_tagged)).
        { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore5) as H. simpl Val.load_result in H. exact H. }
        assert (Hea_m7 : Mem.load Mint64 m7 sp_b (Ptrofs.unsigned new_sp_ofs + 24) = Some (Vlong ea_tagged)).
        { erewrite Mem.load_store_other. 2: exact Hstore7.
          erewrite Mem.load_store_other. 2: exact Hstore6.
          exact Hea_m5. all: left; intro Heq; apply Hsp_ne_sb; auto. }
        unfold Ptrofs.sub.
        rewrite (Ptrofs.unsigned_repr 8 ltac:(pose proof Ptrofs.modulus_pos; unfold Ptrofs.max_unsigned; lia)).
        rewrite Ptrofs.unsigned_repr; [| pose proof (Ptrofs.unsigned_range sp_ofs); unfold Ptrofs.max_unsigned; lia].
        rewrite Hnew_sp_unsigned in Hea_m7.
        replace (Ptrofs.unsigned sp_ofs - 32 + 24) with (Ptrofs.unsigned sp_ofs - 8) in Hea_m7 by lia.
        exact Hea_m7.
      - unfold ea_tagged, ea_long. rewrite tagged_int_arith by (unfold ea_nat; lia). constructor.
      - replace (Ptrofs.add (Ptrofs.sub sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8)) with sp_ofs.
        exact Hstk_m7.
        rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc.
        rewrite (Ptrofs.add_commut (Ptrofs.neg (Ptrofs.repr 8)) (Ptrofs.repr 8)).
        rewrite Ptrofs.add_neg_zero, Ptrofs.add_zero. reflexivity. }

    (* env :: ea :: old_stack at sp_ofs - 16 = new_sp_ofs + 16 *)
    assert (Henv_stk : stack_repr hm cb co m7
              (Machine.env s :: Val_int (Z.of_nat ea_nat) :: Machine.stack s)
              sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 16))).
    { econstructor.
      - assert (Henv_sp_m4 : Mem.load Mint64 m4 sp_b (Ptrofs.unsigned new_sp_ofs + 16) = Some env_v).
        { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore4) as H.
          rewrite (val_repr_load_result hm cb co _ _ Henv_repr) in H. exact H. }
        assert (Henv_sp_m7 : Mem.load Mint64 m7 sp_b (Ptrofs.unsigned new_sp_ofs + 16) = Some env_v).
        { erewrite Mem.load_store_other. 2: exact Hstore7.
          erewrite Mem.load_store_other. 2: exact Hstore6.
          erewrite Mem.load_store_other. 2: exact Hstore5.
          exact Henv_sp_m4.
          all: first [ (left; intro Heq; exact (Hsp_ne_sb Heq)) |
                       (right; rewrite Hnew_sp_unsigned; simpl size_chunk; lia) ]. }
        unfold Ptrofs.sub.
        rewrite (Ptrofs.unsigned_repr 16 ltac:(pose proof Ptrofs.modulus_pos; unfold Ptrofs.max_unsigned; lia)).
        rewrite Ptrofs.unsigned_repr; [| pose proof (Ptrofs.unsigned_range sp_ofs); unfold Ptrofs.max_unsigned; lia].
        rewrite Hnew_sp_unsigned in Henv_sp_m7.
        replace (Ptrofs.unsigned sp_ofs - 32 + 16) with (Ptrofs.unsigned sp_ofs - 16) in Henv_sp_m7 by lia.
        exact Henv_sp_m7.
      - exact Henv_repr.
      - replace (Ptrofs.add (Ptrofs.sub sp_ofs (Ptrofs.repr 16)) (Ptrofs.repr 8))
          with (Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
        exact Hea_stk.
        apply Ptrofs.same_if_eq. unfold Ptrofs.eq.
        rewrite (ptrofs_add_unsigned (Ptrofs.sub sp_ofs (Ptrofs.repr 16)) 8 ltac:(lia)).
        2: { unfold Ptrofs.sub. change (Ptrofs.unsigned (Ptrofs.repr 16)) with 16.
             rewrite Ptrofs.unsigned_repr; [lia | pose proof (Ptrofs.unsigned_range sp_ofs); unfold Ptrofs.max_unsigned; lia]. }
        unfold Ptrofs.sub. change (Ptrofs.unsigned (Ptrofs.repr 16)) with 16. change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
        rewrite !Ptrofs.unsigned_repr; [| pose proof (Ptrofs.unsigned_range sp_ofs); unfold Ptrofs.max_unsigned; lia | pose proof (Ptrofs.unsigned_range sp_ofs); unfold Ptrofs.max_unsigned; lia].
        destruct (Coqlib.zeq _ _) as [_|Habs]; [reflexivity | exfalso; apply Habs; lia]. }

    (* Val_int trap_sp :: env :: ea :: old_stack at sp_ofs - 24 = new_sp_ofs + 8 *)
    assert (Htsp_stk : stack_repr hm cb co m7
              (Val_int (Z.of_nat tsp_nat) ::
               Machine.env s :: Val_int (Z.of_nat ea_nat) :: Machine.stack s)
              sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 24))).
    { econstructor.
      - assert (Htl_m3 : Mem.load Mint64 m3 sp_b (Ptrofs.unsigned new_sp_ofs + 8) = Some (Vlong tsp_tagged)).
        { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore3) as H.
          simpl Val.load_result in H. exact H. }
        assert (Htl_m7 : Mem.load Mint64 m7 sp_b (Ptrofs.unsigned new_sp_ofs + 8) = Some (Vlong tsp_tagged)).
        { erewrite Mem.load_store_other. 2: exact Hstore7.
          erewrite Mem.load_store_other. 2: exact Hstore6.
          erewrite Mem.load_store_other. 2: exact Hstore5.
          erewrite Mem.load_store_other. 2: exact Hstore4.
          exact Htl_m3.
          all: first [ (left; intro Heq; exact (Hsp_ne_sb Heq)) |
                       (right; rewrite Hnew_sp_unsigned; simpl size_chunk; lia) ]. }
        unfold Ptrofs.sub.
        rewrite (Ptrofs.unsigned_repr 24 ltac:(pose proof Ptrofs.modulus_pos; unfold Ptrofs.max_unsigned; lia)).
        rewrite Ptrofs.unsigned_repr; [| pose proof (Ptrofs.unsigned_range sp_ofs); unfold Ptrofs.max_unsigned; lia].
        rewrite Hnew_sp_unsigned in Htl_m7.
        replace (Ptrofs.unsigned sp_ofs - 32 + 8) with (Ptrofs.unsigned sp_ofs - 24) in Htl_m7 by lia.
        exact Htl_m7.
      - unfold tsp_tagged. rewrite tagged_int_arith by (unfold tsp_nat; lia). constructor.
      - replace (Ptrofs.add (Ptrofs.sub sp_ofs (Ptrofs.repr 24)) (Ptrofs.repr 8))
          with (Ptrofs.sub sp_ofs (Ptrofs.repr 16)).
        exact Henv_stk.
        unfold Ptrofs.sub. f_equal.
        change (Ptrofs.unsigned (Ptrofs.repr 24)) with 24.
        change (Ptrofs.unsigned (Ptrofs.repr 16)) with 16.
        unfold Ptrofs.add.
        change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
        rewrite Ptrofs.unsigned_repr
          by (pose proof (Ptrofs.unsigned_range sp_ofs); unfold Ptrofs.max_unsigned; lia).
        f_equal. lia. }

    (* Val_int handler_pc :: Val_int trap_sp :: env :: ea :: old_stack at new_sp_ofs *)
    assert (Hhnd_stk : stack_repr hm cb co m7
              (Val_int handler_pc ::
               Val_int (Z.of_nat tsp_nat) :: Machine.env s ::
               Val_int (Z.of_nat ea_nat) :: Machine.stack s)
              sp_b new_sp_ofs).
    { econstructor.
      - (* load at new_sp_ofs gives handler_addr_v *)
        assert (Hhnd_m2 : Mem.load Mint64 m2 sp_b (Ptrofs.unsigned new_sp_ofs) = Some handler_addr_v).
        { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore2) as H.
          unfold handler_addr_v in H. simpl Val.load_result in H. rewrite ptr64_true in H. exact H. }
        erewrite Mem.load_store_other. 2: exact Hstore7.
        erewrite Mem.load_store_other. 2: exact Hstore6.
        erewrite Mem.load_store_other. 2: exact Hstore5.
        erewrite Mem.load_store_other. 2: exact Hstore4.
        erewrite Mem.load_store_other. 2: exact Hstore3.
        exact Hhnd_m2.
        all: first [ (left; intro Heq; exact (Hsp_ne_sb Heq)) |
                     (right; rewrite Hnew_sp_unsigned; simpl size_chunk; lia) ].
      - (* val_repr: use vr_code_ptr with co_val chosen so the addition matches *)
        unfold handler_addr_v.
        replace handler_ofs with
          (Ptrofs.add (Ptrofs.sub handler_ofs (Ptrofs.repr (handler_pc * sizeof_code_t)))
                      (Ptrofs.repr (handler_pc * sizeof_code_t))).
        + apply vr_code_ptr.
        + rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc.
          rewrite (Ptrofs.add_commut (Ptrofs.neg _)).
          rewrite Ptrofs.add_neg_zero, Ptrofs.add_zero. reflexivity.
      - replace (Ptrofs.add new_sp_ofs (Ptrofs.repr 8))
          with (Ptrofs.sub sp_ofs (Ptrofs.repr 24)).
        exact Htsp_stk.
        apply Ptrofs.same_if_eq. unfold Ptrofs.eq.
        rewrite (ptrofs_add_unsigned new_sp_ofs 8 ltac:(lia) ltac:(rewrite Hnew_sp_unsigned; lia)).
        rewrite Hnew_sp_unsigned.
        unfold Ptrofs.sub. change (Ptrofs.unsigned (Ptrofs.repr 24)) with 24.
        rewrite Ptrofs.unsigned_repr; [| pose proof (Ptrofs.unsigned_range sp_ofs); unfold Ptrofs.max_unsigned; lia].
        destruct (Coqlib.zeq _ _) as [_|Habs]; [reflexivity | exfalso; apply Habs; lia]. }

    (* le14 ! _s *)
    assert (Hle14_s : le14 ! _s = Some (Vptr sb so)).
    { subst le14 le13 le12 le11 le10 le9 le8 le7 le6 le5 le4 le3 le2 le1.
      repeat (rewrite PTree.gso by (compute; congruence)).
      exact Hle_s. }

    (* sp_writable in m7 for new stack *)
    set (new_stack := Val_int handler_pc :: Val_int (Z.of_nat tsp_nat) ::
                      Machine.env s :: Val_int (Z.of_nat ea_nat) :: Machine.stack s).
    assert (Hsp_writable_m7 : Mem.range_perm m7 sp_b 0
              (Ptrofs.unsigned new_sp_ofs + 8 * Z.of_nat (length new_stack)) Cur Writable).
    { intros ofs' Hofs'. unfold new_stack in Hofs'. simpl length in Hofs'.
      rewrite Hnew_sp_unsigned in Hofs'.
      eapply Mem.perm_store_1. exact Hstore7.
      eapply Mem.perm_store_1. exact Hstore6.
      eapply Mem.perm_store_1. exact Hstore5.
      eapply Mem.perm_store_1. exact Hstore4.
      eapply Mem.perm_store_1. exact Hstore3.
      eapply Mem.perm_store_1. exact Hstore2.
      eapply Mem.perm_store_1. exact Hstore1.
      apply Hsp_writable. lia. }

    (* New stack alignment *)
    assert (Hnew_sp_ge8 : Ptrofs.unsigned new_sp_ofs >= 8).
    { rewrite Hnew_sp_unsigned. lia. }

    (* New stack representability *)
    assert (Hnew_sp_rep : Ptrofs.unsigned new_sp_ofs + 8 * Z.of_nat (length new_stack) < Ptrofs.modulus).
    { unfold new_stack. simpl length. rewrite Hnew_sp_unsigned. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le' *)
    { exact Hle14_s. }

    (* 2. pc field -- updated to new_pc_v, with shifted code base *)
    { exists new_pc_v. split.
      - exact Hpc_load7.
      - simpl. unfold pc_rel, new_pc_v, new_pc_ofs, new_co.
        f_equal. rewrite Ptrofs.add_assoc. f_equal.
        unfold sizeof_code_t.
        rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
        apply Ptrofs.eqm_trans with (4 + Machine.pc s * 4)%Z.
        + apply Ptrofs.eqm_refl2. lia.
        + apply Ptrofs.eqm_add; apply Ptrofs.eqm_unsigned_repr. }

    (* 3. accu -- unchanged *)
    { exists accu_v. split. exact Haccu_load7. simpl. eapply val_repr_co_shift. exact Haccu_repr. }

    (* 4. sp field -- new_sp_ofs with new_stack *)
    { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load7.
      - reflexivity.
      - simpl. eapply stack_repr_co_shift. exact Hhnd_stk.
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - exact Hnew_sp_ge8.
      - exact Hnew_sp_rep.
      - exact Hsp_writable_m7.
      - exact Halign_new. }

    (* 5. env -- unchanged *)
    { exists env_v. split. exact Henv_load7. simpl. eapply val_repr_co_shift. exact Henv_repr. }

    (* 6. extra_args -- unchanged *)
    { simpl. exact Hextra_load7. }

    (* 7. global_data -- unchanged *)
    { exists (Vptr (ar_global_block ard) (ar_global_ofs ard)). split; [| split; [| split]].
      - exact Hgd_load7.
      - simpl. reflexivity.
      - simpl. eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m6 m7 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (Ptrofs.unsigned so + 0) new_pc_v).
        apply (global_repr_store_other_block hm cb co m5 m6 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (Ptrofs.unsigned so + 48) (Vptr sp_b new_sp_ofs)).
        apply (global_repr_store_other_block hm cb co m4 m5 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sp_b (Ptrofs.unsigned new_sp_ofs + 24) (Vlong ea_tagged)).
        apply (global_repr_store_other_block hm cb co m3 m4 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sp_b (Ptrofs.unsigned new_sp_ofs + 16) env_v).
        apply (global_repr_store_other_block hm cb co m2 m3 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sp_b (Ptrofs.unsigned new_sp_ofs + 8) (Vlong tsp_tagged)).
        apply (global_repr_store_other_block hm cb co m1 m2 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sp_b (Ptrofs.unsigned new_sp_ofs) handler_addr_v).
        apply (global_repr_store_other_block hm cb co m m1 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)).
        exact Hglobal_repr.
        exact Hstore1. intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
        exact Hstore2. intro Heq2; exact (Hsp_ne_gb Heq2).
        exact Hstore3. intro Heq2; exact (Hsp_ne_gb Heq2).
        exact Hstore4. intro Heq2; exact (Hsp_ne_gb Heq2).
        exact Hstore5. intro Heq2; exact (Hsp_ne_gb Heq2).
        exact Hstore6. intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
        exact Hstore7. intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field -- updated to new_sp *)
    { exists (Vptr sp_b new_sp_ofs). split.
      - exact Hts_load7.
      - simpl.
        (* trap_sp_rel (Vptr sp_b new_sp_ofs) stk_b stk_base (4 + length stack) *)
        (* = trap_sp_rel new_sp stk_b stk_base new_tsp *)
        (* provided by Htrap_rel_new' *)
        exact Htrap_rel_new'. }

    (* 9. sb_writable *)
    { exact Hsb_writable_m7. }
  }
Qed.
