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

(* Local copy of the CLOSURE env copy loop AST (from instruct_handlers.v).
   Copies nvars values from sp[0..nvars-1] to block[2..nvars+1]. *)
Local Definition closure_env_loop_body : statement :=
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
              (tptr tlong)) tlong) (Etempvar _t'10 tlong))))).

Local Definition closure_env_loop_incr : statement :=
  (Sset _i
    (Ebinop Oadd (Etempvar _i tint)
      (Econst_int (Int.repr 1) tint) tint)).

Local Definition closure_env_loop : statement :=
  Sloop closure_env_loop_body closure_env_loop_incr.

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

Lemma sem_cast_int_to_long : forall n m,
  sem_cast (Vint n) tint tlong m = Some (Vlong (Int64.repr (Int.signed n))).
Proof.
  intros. unfold sem_cast.
  change (classify_cast tint tlong) with (cast_case_i2l Signed).
  simpl. reflexivity.
Qed.

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
    { apply Hfield_survive; [lia | exact Henv_load]. }

    assert (Hextra_load_final : Mem.load Mint64 m_final sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply Hfield_survive; [lia | exact Hextra_load]. }

    assert (Hgd_load_final : Mem.load Mint64 m_final sb (uso + 40) = Some (Vptr gb go0)).
    { apply Hfield_survive; [lia | exact Hgd_load]. }

    assert (Hts_load_final : Mem.load Mint64 m_final sb (uso + 48) = Some ts_ptr).
    { apply Hfield_survive; [lia | exact Hts_load]. }

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

(* ================================================================== *)
(* Helper lemma: Int.lt (Int.repr 0) (Int.repr (Z.of_nat (S n)))      *)
(* when 0 <= Z.of_nat (S n) <= Int.max_signed                         *)
(* ================================================================== *)

Lemma int_lt_0_S : forall n : nat,
  Z.of_nat (S n) <= Int.max_signed ->
  Int.lt (Int.repr 0) (Int.repr (Z.of_nat (S n))) = true.
Proof.
  intros n Hle.
  unfold Int.lt.
  assert (H0 : Int.signed (Int.repr 0) = 0).
  { rewrite Int.signed_repr; [reflexivity |].
    compute. split; intro; discriminate. }
  assert (HS : Int.signed (Int.repr (Z.of_nat (S n))) = Z.of_nat (S n)).
  { rewrite Int.signed_repr; [reflexivity |].
    split; [| exact Hle].
    change Int.min_signed with (-2147483648)%Z. lia. }
  rewrite H0, HS.
  destruct (zlt 0 (Z.of_nat (S n))); [reflexivity | lia].
Qed.

(* ================================================================== *)
(* Pointer arithmetic helpers for the env copy loop                    *)
(* ================================================================== *)

Local Lemma ptrofs_max_unsigned_large : (Ptrofs.max_unsigned >= 2^32)%Z.
Proof. vm_compute. discriminate. Qed.

Local Lemma ptrofs_mul_8 : forall n,
  0 <= n ->
  n * 8 <= Ptrofs.max_unsigned ->
  Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.repr n) = Ptrofs.repr (n * 8).
Proof.
  intros n Hn0 Hn8.
  unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 8).
  2: { pose proof ptrofs_max_unsigned_large. lia. }
  rewrite Ptrofs.unsigned_repr.
  2: { lia. }
  f_equal. lia.
Qed.

Local Lemma ptrofs_of_int_signed_repr : forall z,
  Int.min_signed <= z <= Int.max_signed ->
  ptrofs_of_int Signed (Int.repr z) = Ptrofs.repr z.
Proof.
  intros. unfold ptrofs_of_int. simpl. unfold Ptrofs.of_ints.
  rewrite Int.signed_repr. reflexivity. lia.
Qed.

(* ================================================================== *)
(* Helper: extract loadable+castable stack values from stack_repr      *)
(* ================================================================== *)

Local Lemma ptrofs_add_repr : forall a b,
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  intros. rewrite Ptrofs.add_unsigned.
  apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add;
    apply Ptrofs.eqm_sym;
    apply Ptrofs.eqm_unsigned_repr.
Qed.

Local Lemma stack_repr_nth : forall n hm cb0 co0 m stk sp_b sp_ofs v,
  stack_repr hm cb0 co0 m stk sp_b sp_ofs ->
  nth_error stk n = Some v ->
  exists cv,
    Mem.load Mint64 m sp_b
      (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some cv /\
    val_repr hm cb0 co0 v cv.
Proof.
  induction n as [| n' IH]; intros hm cb0 co0 m stk sp_b sp_ofs v Hsr Hnth.
  - destruct stk as [| v0 rest]; [discriminate |].
    simpl in Hnth. inversion Hnth; subst.
    inversion Hsr as [| xv xvs xb xofs xcv Hload Hvr Hrest].
    subst xv xvs xb xofs.
    exists xcv. split.
    + replace (Z.of_nat 0 * 8)%Z with 0%Z by lia.
      change (Ptrofs.repr 0) with Ptrofs.zero.
      rewrite Ptrofs.add_zero. exact Hload.
    + exact Hvr.
  - destruct stk as [| v0 rest]; [discriminate |].
    simpl in Hnth.
    inversion Hsr as [| xv xvs xb xofs xcv Hload Hvr Hrest].
    subst xv xvs xb xofs.
    specialize (IH hm cb0 co0 m rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) v Hrest Hnth).
    destruct IH as [cv' [Hload' Hvr']].
    exists cv'. split.
    + replace (Z.of_nat (S n') * 8)%Z with (8 + Z.of_nat n' * 8)%Z by lia.
      rewrite <- ptrofs_add_repr.
      rewrite <- Ptrofs.add_assoc.
      exact Hload'.
    + exact Hvr'.
Qed.

(* ================================================================== *)
(* Helper: closure env copy loop execution                             *)
(* Proves the Sloop part by induction on remaining iterations n.       *)
(* k is the current loop counter, k+n = nvars_nat.                    *)
(* ================================================================== *)

Lemma closure_env_loop_exec : forall n,
  forall (k : nat) (e : Clight.env) (le : temp_env) (m : mem)
         (sp_b : block) (sp_ofs' : ptrofs)
         (sb : block) (so : ptrofs)
         (new_b : block) (new_ofs : ptrofs)
         (nvars_nat : nat),
    (k + n = nvars_nat)%nat ->
    (0 <= Z.of_nat (nvars_nat + 2) <= Int.max_signed) ->
    le ! _i = Some (Vint (Int.repr (Z.of_nat k))) ->
    le ! _s = Some (Vptr sb so) ->
    le ! _block = Some (Vptr new_b new_ofs) ->
    le ! _nvars = Some (Vint (Int.repr (Z.of_nat nvars_nat))) ->
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs') ->
    (* Stack values loadable and castable for remaining iterations *)
    (forall j, (k <= j < nvars_nat)%nat ->
      exists cv, Mem.load Mint64 m sp_b
        (Ptrofs.unsigned sp_ofs' + Z.of_nat j * 8) = Some cv /\
      forall m', sem_cast cv tlong tlong m' = Some cv) ->
    (* New block writable for remaining fields *)
    Mem.range_perm m new_b
      (Ptrofs.unsigned new_ofs + Z.of_nat (k + 2) * 8)
      (Ptrofs.unsigned new_ofs + Z.of_nat (nvars_nat + 2) * 8) Cur Writable ->
    (align_chunk Mint64 | Ptrofs.unsigned new_ofs) ->
    new_b <> sp_b -> new_b <> sb ->
    Ptrofs.unsigned new_ofs + Z.of_nat (nvars_nat + 2) * 8 < Ptrofs.modulus ->
    Ptrofs.unsigned sp_ofs' + Z.of_nat nvars_nat * 8 < Ptrofs.modulus ->
    Ptrofs.unsigned so + 56 < Ptrofs.modulus ->
    (align_chunk Mint64 | Ptrofs.unsigned sp_ofs') ->
    exists le' m',
      exec_stmt function_entry1 clight_ge e le m
        closure_env_loop E0 le' m' Out_normal /\
      le' ! _s = Some (Vptr sb so) /\
      le' ! _block = Some (Vptr new_b new_ofs) /\
      le' ! _nvars = Some (Vint (Int.repr (Z.of_nat nvars_nat))) /\
      (forall ofs v, Mem.load Mint64 m sb ofs = Some v ->
         Mem.load Mint64 m' sb ofs = Some v) /\
      (forall b ofs k0 p, Mem.perm m b ofs k0 p -> Mem.perm m' b ofs k0 p) /\
      (forall b ofs chunk v, b <> new_b ->
         Mem.load chunk m b ofs = Some v ->
         Mem.load chunk m' b ofs = Some v).
Proof.
  induction n as [| n' IH]; intros k e le m sp_b sp_ofs' sb so new_b new_ofs nvars_nat
    Hkn Hnvars_range Hle_i Hle_s Hle_block Hle_nvars
    Hsp_load Hstack_load Hnew_rperm Hnew_align
    Hnew_ne_sp Hnew_ne_sb Hnew_ofs_bound Hsp_ofs_bound Hso_bound Hsp_align.

  (* ================================================================ *)
  (* Base case: n = 0, loop terminates immediately                     *)
  (* ================================================================ *)
  {
    exists le, m.
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    - unfold closure_env_loop.
      eapply exec_Sloop_stop1.
      + eapply exec_Sseq_2.
        * eapply exec_Sifthenelse with (b := false).
          -- econstructor; [econstructor; exact Hle_i | econstructor; exact Hle_nvars |].
             exact (sem_cmp_lt_int (Int.repr (Z.of_nat k)) (Int.repr (Z.of_nat nvars_nat)) m).
          -- unfold bool_val. simpl. f_equal. unfold Val.of_bool.
             replace nvars_nat with k by lia.
             unfold Int.lt.
             destruct (zlt _ _); [exfalso; lia | reflexivity].
          -- simpl. eapply exec_Sbreak.
        * discriminate.
      + constructor.
    - assumption.
    - assumption.
    - assumption.
    - auto.
    - auto.
    - auto.
  }

  (* ================================================================ *)
  (* Inductive case: n = S n', execute one iteration + recurse         *)
  (* ================================================================ *)
  {
    destruct interp_state_co_pc_accu_sp as [co_is [Hco [Hpc_offset [Haccu_offset Hsp_offset]]]].
    rewrite cenv_is_ce in Hco, Hpc_offset, Haccu_offset, Hsp_offset.

    (* Stack value at position k *)
    destruct (Hstack_load k ltac:(lia)) as [cv_k [Hload_sp_k Hcast_k]].

    (* Store to block[k+2] must succeed *)
    assert (Hstore_valid : Mem.valid_access m Mint64 new_b
              (Ptrofs.unsigned new_ofs + Z.of_nat (k + 2) * 8) Writable).
    { split.
      - intros ofs0 Hofs0. apply Hnew_rperm. simpl in Hofs0. lia.
      - change (align_chunk Mint64) with 8.
        destruct Hnew_align as [q Hq].
        change (align_chunk Mint64) with 8 in Hq.
        exists (q + Z.of_nat (k + 2)). lia. }
    destruct (Mem.valid_access_store m Mint64 new_b
                (Ptrofs.unsigned new_ofs + Z.of_nat (k + 2) * 8) cv_k Hstore_valid)
      as [m_k Hstore_k].

    (* le after body *)
    set (le_body := PTree.set _i (Vint (Int.repr (Z.of_nat (S k))))
            (PTree.set _t'10 cv_k
              (PTree.set _t'9 (Vptr sp_b sp_ofs') le))) in *.

    (* Apply IH *)
    assert (IH_result : exists le_post m_post,
      exec_stmt function_entry1 clight_ge e le_body m_k
        closure_env_loop E0 le_post m_post Out_normal /\
      le_post ! _s = Some (Vptr sb so) /\
      le_post ! _block = Some (Vptr new_b new_ofs) /\
      le_post ! _nvars = Some (Vint (Int.repr (Z.of_nat nvars_nat))) /\
      (forall ofs v, Mem.load Mint64 m_k sb ofs = Some v ->
         Mem.load Mint64 m_post sb ofs = Some v) /\
      (forall b ofs k0 p, Mem.perm m_k b ofs k0 p -> Mem.perm m_post b ofs k0 p) /\
      (forall b ofs chunk v, b <> new_b ->
         Mem.load chunk m_k b ofs = Some v ->
         Mem.load chunk m_post b ofs = Some v)).
    {
      apply (IH (S k) e le_body m_k sp_b sp_ofs' sb so new_b new_ofs nvars_nat).
      - lia.
      - assumption.
      - subst le_body. rewrite PTree.gss. reflexivity.
      - subst le_body. repeat (rewrite PTree.gso by (compute; congruence)). assumption.
      - subst le_body. repeat (rewrite PTree.gso by (compute; congruence)). assumption.
      - subst le_body. repeat (rewrite PTree.gso by (compute; congruence)). assumption.
      - erewrite Mem.load_store_other; [exact Hsp_load | exact Hstore_k |].
        left. exact (not_eq_sym Hnew_ne_sb).
      - intros j Hj.
        destruct (Hstack_load j ltac:(lia)) as [cv_j [Hload_j Hcast_j]].
        exists cv_j. split; [| exact Hcast_j].
        erewrite Mem.load_store_other; [exact Hload_j | exact Hstore_k |].
        left. exact (not_eq_sym Hnew_ne_sp).
      - intros ofs0 Hofs0. eapply Mem.perm_store_1. exact Hstore_k.
        apply Hnew_rperm. lia.
      - assumption.
      - assumption.
      - assumption.
      - assumption.
      - assumption.
      - assumption.
      - assumption.
    }
    destruct IH_result as (le_post & m_post &
      Hloop_exec & Hpost_s & Hpost_block & Hpost_nvars &
      Hpost_sb & Hpost_perm & Hpost_load).

    exists le_post, m_post.
    split; [| split; [| split; [| split; [| split; [| split]]]]].

    - (* exec: one iteration then recurse *)
      unfold closure_env_loop.
      replace E0 with (E0 ** E0 ** E0) by reflexivity.
      eapply exec_Sloop_loop.

      + (* s1: condition true + body *)
        unfold closure_env_loop_body.
        replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1.
        * (* Sifthenelse: condition true → Sskip *)
          eapply exec_Sifthenelse with (b := true).
          -- econstructor; [econstructor; exact Hle_i | econstructor; exact Hle_nvars |].
             exact (sem_cmp_lt_int (Int.repr (Z.of_nat k)) (Int.repr (Z.of_nat nvars_nat)) m).
          -- unfold bool_val. simpl. f_equal. unfold Val.of_bool.
             unfold Int.lt.
             rewrite Int.signed_repr by (pose proof Int.min_signed_neg; lia).
             rewrite Int.signed_repr by (pose proof Int.min_signed_neg; lia).
             destruct (zlt (Z.of_nat k) (Z.of_nat nvars_nat)); [reflexivity | lia].
          -- simpl. eapply exec_Sskip.
        * (* body: t'9=sp, t'10=sp[k], block[k+2]=t'10 *)
          replace E0 with (E0 ** E0) by reflexivity.
          eapply exec_Sseq_1.
          -- (* Sset _t'9: load sp from struct *)
             apply (eval_stmt_to_exec clight_ge 10). eval_cbn.
             rewrite Hle_s; eval_cbn. rewrite cenv_is_ce; eval_cbn.
             rewrite Hco; eval_cbn. rewrite Hsp_offset; eval_cbn.
             try rewrite Mptr_Mint64; eval_cbn.
             rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
             rewrite Hsp_load; eval_cbn.
             reflexivity.
          -- replace E0 with (E0 ** E0) by reflexivity.
             eapply exec_Sseq_1.
             ++ (* Sset _t'10: load sp[k] *)
                apply (eval_stmt_to_exec clight_ge 10). eval_cbn.
                rewrite PTree.gss; eval_cbn.
                rewrite PTree.gso by (compute; congruence).
                rewrite Hle_i; eval_cbn.
                rewrite sem_add_ptr_tlong_int; eval_cbn.
                try rewrite Mptr_Mint64; eval_cbn.
                rewrite ptrofs_of_int_signed_repr
                  by (pose proof Int.min_signed_neg; lia).
                rewrite ptrofs_mul_8
                  by (unfold Ptrofs.max_unsigned;
                      pose proof (Ptrofs.unsigned_range sp_ofs'); lia).
                rewrite (ptrofs_add_unsigned sp_ofs' (Z.of_nat k * 8)
                  ltac:(pose proof (Ptrofs.unsigned_range sp_ofs'); lia) ltac:(lia)).
                rewrite Hload_sp_k; eval_cbn.
                reflexivity.
             ++ (* Sassign: block[k+2] = t'10 *)
                eapply exec_Sassign.
                ** (* eval_lvalue for LHS: *(cast(block) + (i+2)) *)
                   econstructor. econstructor. econstructor.
                   --- (* cast(block) from tlong to tptr tlong *)
                       eapply eval_Etempvar.
                       rewrite PTree.gso by (compute; congruence).
                       rewrite PTree.gso by (compute; congruence).
                       exact Hle_block.
                   --- exact (sem_cast_vptr_tlong_to_ptr_tlong new_b new_ofs m).
                   --- (* i+2 *)
                       econstructor.
                       +++ eapply eval_Etempvar.
                           rewrite PTree.gso by (compute; congruence).
                           rewrite PTree.gso by (compute; congruence).
                           exact Hle_i.
                       +++ econstructor.
                       +++ exact (sem_add_int_int (Int.repr (Z.of_nat k)) (Int.repr 2) m).
                   --- exact (sem_add_ptr_tlong_int new_b new_ofs
                         (Int.add (Int.repr (Z.of_nat k)) (Int.repr 2)) m).
                ** (* eval_expr for RHS: _t'10 *)
                   econstructor. rewrite PTree.gss. reflexivity.
                ** (* sem_cast *)
                   exact (Hcast_k m).
                ** (* assign_loc *)
                   econstructor.
                   --- reflexivity.
                   --- unfold Mem.storev.
                       rewrite Int.add_unsigned.
                       rewrite (Int.unsigned_repr (Z.of_nat k)).
                       2: { pose proof Int.max_signed_unsigned. split; lia. }
                       rewrite (Int.unsigned_repr 2).
                       2: { pose proof Int.max_signed_unsigned. split; lia. }
                       rewrite ptrofs_of_int_signed_repr.
                       2: { pose proof Int.min_signed_neg. split; lia. }
                       replace (Int.repr (Z.of_nat k + 2))
                         with (Int.repr (Z.of_nat (k + 2)))
                         by (f_equal; lia).
                       rewrite ptrofs_mul_8
                         by (unfold Ptrofs.max_unsigned;
                             pose proof (Ptrofs.unsigned_range new_ofs); lia).
                       rewrite ptrofs_add_unsigned
                         by (pose proof (Ptrofs.unsigned_range new_ofs); lia).
                       replace (Z.of_nat k + 2) with (Z.of_nat (k + 2)) by lia.
                       exact Hstore_k.

      + (* out_normal_or_continue *)
        constructor.

      + (* s2: increment _i := _i + 1 *)
        unfold closure_env_loop_incr.
        apply (eval_stmt_to_exec clight_ge 5). eval_cbn.
        do 2 (rewrite PTree.gso by (compute; congruence)).
        rewrite Hle_i; eval_cbn.
        rewrite sem_add_int_int; eval_cbn.
        replace (Int.add (Int.repr (Z.of_nat k)) (Int.repr 1))
          with (Int.repr (Z.of_nat (S k))).
        2: { rewrite Int.add_unsigned.
             rewrite (Int.unsigned_repr (Z.of_nat k))
               by (pose proof Int.max_signed_unsigned; split; lia).
             rewrite (Int.unsigned_repr 1)
               by (pose proof Int.max_signed_unsigned; split; lia).
             f_equal. lia. }
        reflexivity.

      + (* Sloop recurse *)
        fold closure_env_loop.
        replace (PTree.set _i (Vint (Int.repr (Z.of_nat (S k))))
                  (PTree.set _t'10 cv_k
                    (PTree.set _t'9 (Vptr sp_b sp_ofs') le)))
          with le_body.
        { exact Hloop_exec. }
        subst le_body. reflexivity.

    - exact Hpost_s.
    - exact Hpost_block.
    - exact Hpost_nvars.
    - intros ofs v Hld. apply Hpost_sb.
      erewrite Mem.load_store_other; [exact Hld | exact Hstore_k |].
      left. exact (not_eq_sym Hnew_ne_sb).
    - intros b ofs k0 p Hp. apply Hpost_perm.
      eapply Mem.perm_store_1. exact Hstore_k. exact Hp.
    - intros b ofs chunk v Hne Hld. apply Hpost_load; [exact Hne |].
      erewrite Mem.load_store_other; [exact Hld | exact Hstore_k |].
      left. exact Hne.
  }
Qed.

(* ================================================================== *)
(* Main theorem: arbitrary nvars                                       *)
(* ================================================================== *)

Theorem verify_CLOSURE_general_correct : forall nvars code_ofs,
    (0 <= Z.of_nat nvars <= Int.max_signed) ->
    Int.min_signed <= code_ofs <= Int.max_signed ->
    handler_correct (handle_CLOSURE nvars code_ofs) f_instr_CLOSURE
      (closure_general_step_pre nvars code_ofs)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros nvars code_ofs Hnvars_range Hcode_ofs_range.
  destruct nvars as [| nvars'].

  (* ============================================================== *)
  (* Case nvars = 0: delegate to verify_CLOSURE_correct              *)
  (* ============================================================== *)
  { eapply handler_correct_weaken.
    - exact (verify_CLOSURE_correct code_ofs).
    - intros e le m s ard Hpre Hstep_pre.
      unfold closure_general_step_pre in Hstep_pre.
      destruct Hstep_pre as (He_heap_alloc & Hcode_nvars & Hcode_ofs & Hcode_ofs_range2 &
        Hnvars_range2 & _Hnvars_stack_bound & Hhm_fresh & Hgb_valid & [b_ha [Hfind_symbol Hfind_funct]] &
        Halloc_spec_all).
      simpl Z.of_nat in Hcode_nvars. simpl Nat.add in Halloc_spec_all.
      split; [exact He_heap_alloc |].
      split; [exact Hcode_nvars |].
      split; [exact Hcode_ofs |].
      split; [exact Hcode_ofs_range2 |].
      split; [exact Hhm_fresh |].
      split; [exact Hgb_valid |].
      split; [exists b_ha; split; [exact Hfind_symbol | exact Hfind_funct] |].
      (* Strip trailing range_perm and align conjuncts from alloc spec *)
      intros m'. specialize (Halloc_spec_all m').
      destruct Halloc_spec_all as (m_alloc & new_b & new_ofs & Hec & Hfresh & Hload_pres & Hperm_pres & Hfield0 & _Hrperm & _Halign & _Hbound).
      exists m_alloc, new_b, new_ofs.
      exact (conj Hec (conj Hfresh (conj Hload_pres (conj Hperm_pres Hfield0)))). }

  (* ============================================================== *)
  (* Case nvars = S nvars': full proof                                *)
  (* ============================================================== *)

  set (nvars := S nvars').

  intros e le m s.
  unfold handle_CLOSURE.
  replace (Nat.ltb 0 nvars) with true
    by (unfold nvars; destruct nvars'; reflexivity).

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

  unfold closure_general_step_pre in Hstep_pre.
  destruct Hstep_pre as (He_heap_alloc & Hcode_nvars & Hcode_ofs & Hcode_ofs_range2 &
    Hnvars_range2 & Hnvars_stack_bound & Hhm_fresh & Hgb_valid & [b_ha [Hfind_symbol Hfind_funct]] &
    Halloc_spec_all).

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
            Some (Vint (Int.repr (Z.of_nat nvars)))).
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

  assert (Hsb_writable_m1 :
    Mem.range_perm m1 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { eapply sb_writable_after_store; eauto. }

  (* --- Phase 4: if-then branch: push accu onto stack (nvars > 0) --- *)
  (* sp' = sp - 1, *sp' = accu *)

  set (sp_ofs' := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).

  assert (Hsp_writable_m1 : Mem.range_perm m1 sp_b 0
    (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) Cur Writable).
  { intros ofs0 Hofs0. eapply Mem.perm_store_1. exact Hstore_pc1.
    apply Hsp_writable. exact Hofs0. }

  (* Store sp' = sp - 8 to struct *)
  destruct (store_succeeds_sb m1 sb so 16 (Vptr sp_b sp_ofs) Hsb_writable_m1 Hsp_load_m1 ltac:(lia) ltac:(lia) (Vptr sp_b sp_ofs'))
    as [m2 Hstore_sp_push].

  assert (Hsb_writable_m2 :
    Mem.range_perm m2 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { eapply sb_writable_after_store; eauto. }

  (* Accu survives sp push store *)
  assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 16)
             (Ptrofs.unsigned so + 8) (Vptr sp_b sp_ofs') accu_v Hstore_sp_push Haccu_load_m1).
    left. lia. }

  (* Read accu from struct *)
  (* Store accu to *sp' = sp_b[sp_ofs - 8] *)
  assert (Hsp_ofs'_val : Ptrofs.unsigned sp_ofs' = Ptrofs.unsigned sp_ofs - 8).
  { unfold sp_ofs'. unfold Ptrofs.sub.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
    apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range sp_ofs).
    unfold Ptrofs.max_unsigned. lia. }

  assert (Hsp_ofs'_align : (align_chunk Mint64 | Ptrofs.unsigned sp_ofs')).
  { rewrite Hsp_ofs'_val. simpl align_chunk in *.
    destruct Hsp_align as [k Hk].
    exists (k - 1)%Z. lia. }

  (* We can store to sp_b at sp_ofs' *)
  assert (Hcan_store_push : forall cv, exists m',
    Mem.store Mint64 m2 sp_b (Ptrofs.unsigned sp_ofs') cv = Some m').
  { intros cv.
    destruct (Mem.valid_access_store m2 Mint64 sp_b (Ptrofs.unsigned sp_ofs') cv) as [m' Hst].
    { split.
      - intros ofs0 Hofs0.
        eapply Mem.perm_store_1. exact Hstore_sp_push.
        eapply Mem.perm_store_1. exact Hstore_pc1.
        apply Hsp_writable.
        rewrite Hsp_ofs'_val in Hofs0. simpl size_chunk in Hofs0. lia.
      - exact Hsp_ofs'_align. }
    exists m'. exact Hst. }

  destruct (Hcan_store_push accu_v) as [m3 Hstore_accu_push].

  (* Stack repr after push *)
  assert (Hstack_m1 : stack_repr hm cb co m1 (Machine.stack s) sp_b sp_ofs).
  { eapply (stack_repr_store_other_block hm cb co); eauto. }

  assert (Hstack_m2 : stack_repr hm cb co m2 (Machine.stack s) sp_b sp_ofs).
  { eapply (stack_repr_store_other_block hm cb co); eauto. }

  assert (Hstack_pushed : stack_repr hm cb co m3 (Machine.accu s :: Machine.stack s) sp_b sp_ofs').
  { eapply stack_repr_cons_after_store; eauto. }

  (* Code loads survive through m2, m3 *)
  assert (Hcode_nvars_m3 : Mem.load Mint32 m3 cb (Ptrofs.unsigned pc_ofs) =
            Some (Vint (Int.repr (Z.of_nat nvars)))).
  { erewrite Mem.load_store_other. 2: exact Hstore_accu_push. 2: left; intro; subst; exact (Hcb_ne_sp eq_refl).
    erewrite Mem.load_store_other. 2: exact Hstore_sp_push. 2: left; exact Hcb_ne.
    exact Hcode_nvars_m1. }

  (* Sp load in m3 (points to sp_ofs') *)
  assert (Hsp_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 16) =
    Some (Vptr sp_b sp_ofs')).
  { erewrite Mem.load_store_other. 2: exact Hstore_accu_push. 2: left; intro; subst; exact (Hsp_ne_sb eq_refl).
    pose proof (load_after_store_same m1 m2 sb (Ptrofs.unsigned so + 16) (Vptr sp_b sp_ofs') Hstore_sp_push) as Htmp.
    rewrite load_result_vptr_cl in Htmp. exact Htmp. }

  assert (Hsb_writable_m3 :
    Mem.range_perm m3 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs0 Hofs0.
    eapply Mem.perm_store_1. exact Hstore_accu_push.
    eapply Mem.perm_store_1. exact Hstore_sp_push.
    apply Hsb_writable_m1. exact Hofs0. }

  (* --- Phase 5: heap_alloc: allocate (2 + nvars)-field block --- *)

  destruct (Halloc_spec_all m3)
    as [m_alloc [new_b [new_ofs
         (Hext_call & Hnew_fresh &
          Halloc_load_pres & Halloc_perm_pres & Hcan_store_f0 &
          Hnew_range_perm & Hnew_align & Hnew_ofs_bound)]]].

  (* Derive freshness for specific blocks *)
  assert (Hnew_ne_sb : new_b <> sb).
  { apply Hnew_fresh. eapply Mem.perm_valid_block.
    apply (Hsb_writable_m3 (Ptrofs.unsigned so)). lia. }
  assert (Hnew_ne_sp : new_b <> sp_b).
  { apply Hnew_fresh. eapply Mem.perm_valid_block.
    eapply Mem.perm_store_1. exact Hstore_accu_push.
    eapply Mem.perm_store_1. exact Hstore_sp_push.
    eapply Mem.perm_store_1. exact Hstore_pc1.
    apply (Hsp_writable 0). lia. }
  assert (Hnew_ne_cb : new_b <> cb).
  { apply Hnew_fresh.
    assert (Hcb_valid : Mem.valid_block m cb).
    { eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies.
      eapply Mem.load_valid_access. exact Hcode_nvars. constructor. }
    eapply Mem.store_valid_block_1. exact Hstore_accu_push.
    eapply Mem.store_valid_block_1. exact Hstore_sp_push.
    eapply Mem.store_valid_block_1. exact Hstore_pc1.
    exact Hcb_valid. }
  assert (Hnew_ne_gb : new_b <> gb).
  { apply Hnew_fresh.
    eapply Mem.store_valid_block_1. exact Hstore_accu_push.
    eapply Mem.store_valid_block_1. exact Hstore_sp_push.
    eapply Mem.store_valid_block_1. exact Hstore_pc1.
    exact Hgb_valid. }

  (* Struct field preservation *)
  assert (Hstruct_preserved_alloc : forall ofs v,
    Mem.load Mint64 m3 sb ofs = Some v ->
    Mem.load Mint64 m_alloc sb ofs = Some v).
  { intros ofs0 v0 Hld. apply Halloc_load_pres; auto. }

  (* Accu in m_alloc -- not needed directly but sp_load is *)
  assert (Hsp_load_alloc : Mem.load Mint64 m_alloc sb (Ptrofs.unsigned so + 16) =
    Some (Vptr sp_b sp_ofs')).
  { apply Hstruct_preserved_alloc. exact Hsp_load_m3. }

  assert (Hsb_writable_alloc :
    Mem.range_perm m_alloc sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs0 Hofs0. eapply Halloc_perm_pres.
    - eapply Mem.perm_valid_block.
      apply (Hsb_writable_m3 (Ptrofs.unsigned so)). lia.
    - apply Hsb_writable_m3. exact Hofs0. }

  (* --- Phase 6: Sset _block --- (same as nvars=0) *)

  set (block_v := Vptr new_b new_ofs).

  (* --- Phase 7: Loop via hypothesis --- *)
  (* The loop postcondition from step_pre gives us the post-loop state *)

  (* Build the le environment just before the loop *)
  set (le1 := PTree.set _t'1 (Vptr cb pc_ofs) le).
  set (le2 := PTree.set _nvars (Vint (Int.repr (Z.of_nat nvars))) le1).
  set (le2a := PTree.set _t'12 (Vptr sp_b sp_ofs) le2).
  set (le2b := PTree.set _t'2 (Vptr sp_b sp_ofs') le2a).
  set (le2c := PTree.set _t'11 accu_v le2b).
  set (le3 := PTree.set _t'3 block_v le2c).
  set (le4 := PTree.set _block block_v le3).

  (* Prove le4 has the needed bindings for the loop postcondition *)
  assert (Hle4_s : le4 ! _s = Some (Vptr sb so)).
  { unfold le4, le3, le2c, le2b, le2a, le2, le1.
    repeat (rewrite PTree.gso by (compute; congruence)).
    exact Hle_s. }

  assert (Hle4_block : le4 ! _block = Some (Vptr new_b new_ofs)).
  { unfold le4. rewrite PTree.gss. reflexivity. }

  assert (Hle4_nvars : le4 ! _nvars = Some (Vint (Int.repr (Z.of_nat nvars)))).
  { unfold le4, le3, le2c, le2b, le2a.
    repeat (rewrite PTree.gso by (compute; congruence)).
    unfold le2. rewrite PTree.gss. reflexivity. }

  (* Loop postcondition: proved via closure_env_loop_exec *)

  (* Transfer stack_repr from m3 to m_alloc *)
  assert (Hstack_alloc : stack_repr hm cb co m_alloc
    (Machine.accu s :: Machine.stack s) sp_b sp_ofs').
  { clear -Hstack_pushed Halloc_load_pres Hnew_ne_sp.
    induction Hstack_pushed as [| v0 vs b ofs cv0 Hld Hvr Hrest IH'].
    - constructor.
    - econstructor; [| exact Hvr | exact (IH' Hnew_ne_sp)].
      apply Halloc_load_pres; [exact Hld | exact (not_eq_sym Hnew_ne_sp)]. }

  (* Offset bounds *)
  assert (Hsp_ofs_bound : Ptrofs.unsigned sp_ofs' + Z.of_nat nvars * 8 < Ptrofs.modulus).
  { rewrite Hsp_ofs'_val.
    pose proof (Nat2Z.is_nonneg nvars).
    simpl length in Hsp_rep. lia. }

  (* Stack values loadable and castable in m_alloc *)
  assert (Hstack_load_alloc : forall j, (j < nvars)%nat ->
    exists cv, Mem.load Mint64 m_alloc sp_b
      (Ptrofs.unsigned sp_ofs' + Z.of_nat j * 8) = Some cv /\
    forall m', sem_cast cv tlong tlong m' = Some cv).
  { intros j Hj.
    assert (Hnth : exists v, nth_error (Machine.accu s :: Machine.stack s) j = Some v).
    { destruct (nth_error (Machine.accu s :: Machine.stack s) j) as [v|] eqn:Hnth.
      - exists v. reflexivity.
      - apply nth_error_None in Hnth. exfalso. simpl length in Hnth. lia. }
    destruct Hnth as [v Hv_nth].
    destruct (stack_repr_nth j hm cb co m_alloc
      (Machine.accu s :: Machine.stack s) sp_b sp_ofs' v Hstack_alloc Hv_nth)
      as [cv [Hload_cv Hvr_cv]].
    exists cv. split.
    - rewrite (ptrofs_add_unsigned sp_ofs' (Z.of_nat j * 8)
        ltac:(pose proof (Ptrofs.unsigned_range sp_ofs'); lia)
        ltac:(lia)) in Hload_cv.
      exact Hload_cv.
    - intro m'. exact (sem_cast_long_val_repr hm cb co v cv m' Hvr_cv). }

  assert (Hnew_ofs_bound_nat : Ptrofs.unsigned new_ofs + Z.of_nat (nvars + 2) * 8 < Ptrofs.modulus).
  { lia. }

  (* Execute Sset _i 0 then apply loop lemma *)
  set (le5 := PTree.set _i (Vint (Int.repr 0)) le4).

  assert (Hle5_i : le5 ! _i = Some (Vint (Int.repr 0))).
  { subst le5. rewrite PTree.gss. reflexivity. }
  assert (Hle5_s : le5 ! _s = Some (Vptr sb so)).
  { subst le5. rewrite PTree.gso by (compute; congruence). exact Hle4_s. }
  assert (Hle5_block : le5 ! _block = Some (Vptr new_b new_ofs)).
  { subst le5. rewrite PTree.gso by (compute; congruence). exact Hle4_block. }
  assert (Hle5_nvars : le5 ! _nvars = Some (Vint (Int.repr (Z.of_nat nvars)))).
  { subst le5. rewrite PTree.gso by (compute; congruence). exact Hle4_nvars. }

  assert (Hloop_inner : exists le_loop m_loop,
    exec_stmt function_entry1 clight_ge e le5 m_alloc
      closure_env_loop E0 le_loop m_loop Out_normal /\
    le_loop ! _s = Some (Vptr sb so) /\
    le_loop ! _block = Some (Vptr new_b new_ofs) /\
    le_loop ! _nvars = Some (Vint (Int.repr (Z.of_nat nvars))) /\
    (forall ofs v, Mem.load Mint64 m_alloc sb ofs = Some v ->
       Mem.load Mint64 m_loop sb ofs = Some v) /\
    (forall b ofs k p, Mem.perm m_alloc b ofs k p -> Mem.perm m_loop b ofs k p) /\
    (forall b ofs chunk v, b <> new_b ->
       Mem.load chunk m_alloc b ofs = Some v ->
       Mem.load chunk m_loop b ofs = Some v)).
  { apply (closure_env_loop_exec nvars 0 e le5 m_alloc sp_b sp_ofs' sb so
      new_b new_ofs nvars).
    - lia.
    - replace (nvars + 2)%nat with (2 + nvars)%nat by lia. exact Hnvars_range2.
    - change (Z.of_nat 0) with 0%Z. exact Hle5_i.
    - exact Hle5_s.
    - exact Hle5_block.
    - exact Hle5_nvars.
    - exact Hsp_load_alloc.
    - intros j Hj. apply Hstack_load_alloc. lia.
    - intros ofs0 Hofs0. apply Hnew_range_perm. lia.
    - exact Hnew_align.
    - exact Hnew_ne_sp.
    - exact Hnew_ne_sb.
    - exact Hnew_ofs_bound_nat.
    - exact Hsp_ofs_bound.
    - exact Hso_bound.
    - rewrite Hsp_ofs'_val. simpl align_chunk in *.
      destruct Hsp_align as [k0 Hk0]. exists (k0 - 1)%Z. lia. }

  destruct Hloop_inner as (le_li & m_li & Hloop_exec & Hpost_s & Hpost_block &
    Hpost_nvars & Hpost_sb & Hpost_perm & Hpost_load).

  assert (Hloop_result :
    exists le_loop0 m_loop0,
      exec_stmt function_entry1 clight_ge e le4 m_alloc
        (Ssequence (Sset _i (Econst_int (Int.repr 0) tint))
           closure_env_loop)
        E0 le_loop0 m_loop0 Out_normal /\
      le_loop0 ! _s = Some (Vptr sb so) /\
      le_loop0 ! _block = Some (Vptr new_b new_ofs) /\
      le_loop0 ! _nvars = Some (Vint (Int.repr (Z.of_nat nvars))) /\
      (forall ofs v,
         Mem.load Mint64 m_alloc sb ofs = Some v ->
         Mem.load Mint64 m_loop0 sb ofs = Some v) /\
      (forall b ofs k p,
         Mem.perm m_alloc b ofs k p ->
         Mem.perm m_loop0 b ofs k p) /\
      (forall b ofs chunk v,
         b <> new_b ->
         Mem.load chunk m_alloc b ofs = Some v ->
         Mem.load chunk m_loop0 b ofs = Some v)).
  { exists le_li, m_li.
    split; [| exact (conj Hpost_s (conj Hpost_block (conj Hpost_nvars
      (conj Hpost_sb (conj Hpost_perm Hpost_load)))))].
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    - apply (eval_stmt_to_exec clight_ge 5). eval_cbn.
      reflexivity.
    - exact Hloop_exec. }
  destruct Hloop_result
    as [le_loop [m_loop (Hexec_loop_full & Hle_loop_s & Hle_loop_block &
         Hle_loop_nvars & Hloop_sb_pres & Hloop_perm_pres & Hloop_load_pres)]].

  (* --- Phases 8-9: Store field 0 and field 1 on post-loop memory --- *)

  (* The heap_alloc spec gives stores for any m'.  We need to get stores
     on m_loop.  But the alloc_spec was for m3, not m_loop.  The spec says
     "forall m'" but that m' is the input to heap_alloc.

     Actually, re-reading the step_pre:
     Halloc_spec_all : forall m', exists ...
     But the stores are: Hcan_store_f0 uses m_alloc (the output of alloc).
     The loop runs AFTER alloc (on m_alloc -> m_loop via the loop).
     We need to store on m_loop, not m_alloc.

     The alloc spec field stores are chained: alloc gives m_alloc,
     then can store field 0 on m_alloc -> m_s0,
     then field 1 on m_s0 -> m_s1.
     But the loop runs AFTER alloc (m_alloc -> m_loop).
     We need to store fields 0 and 1 on m_loop, not m_alloc.

     The key insight: the alloc spec's store chains work on m_alloc,
     but we need them on m_loop.  Since the loop only modifies new_b
     (stores env vars at new_b + (i+2)*8 for i=0..nvars-1), and the
     field 0/1 stores also go to new_b, we can't just reuse them.

     But wait: the step_pre's alloc spec says "forall m'" meaning
     the alloc CAN be called on any memory.  The stores, however,
     are on the RESULT of alloc applied to that specific m'.
     We already called alloc on m3, getting m_alloc.

     For the loop: it modifies m_alloc to m_loop, potentially changing
     new_b's contents (at offsets >= 16).  Field 0 is at new_ofs,
     field 1 is at new_ofs+8.  The loop writes at new_ofs+16, new_ofs+24, etc.

     So we need Mem.valid_access_store to get fresh stores on m_loop.
     The permissions on new_b in m_loop are preserved from m_alloc
     (the loop preserves permissions via Hloop_perm_pres).

     Actually, the step_pre structure already handles this.
     Looking again at the alloc spec:
       (forall cv, exists m_s0,
          Mem.store Mint64 m_alloc new_b ... cv = Some m_s0 ...)
     This stores on m_alloc.  After the loop (m_loop), we need to
     store on m_loop.  We can use Mem.valid_access_store directly.

     But actually, we need the FULL chain: store field 0, THEN store field 1.
     We can:
     1. Use Mem.valid_access_store on m_loop for field 0 -> m_s0_loop
     2. Use Mem.valid_access_store on m_s0_loop for field 1 -> m_s1_loop
     We need permissions, which we get from the alloc spec + loop perm pres.

     Alternatively, we can re-instantiate Halloc_spec_all for a different memory,
     but that gives a different new_b, which is wrong.

     Let me use a different approach: use the alloc spec's stores on m_alloc
     to extract alignment info, then use Mem.valid_access_store on m_loop.
  *)

  (* Get alignment from the alloc spec stores *)
  destruct (Hcan_store_f0 (Vlong Int64.zero))
    as [m_s0_dummy [Hstore_f0_dummy [_ [_ Hcan_store_f1_dummy]]]].

  (* Extract valid_access from store_f0_dummy *)
  pose proof (Mem.store_valid_access_3 _ _ _ _ _ _ Hstore_f0_dummy) as [Hrp_f0 Halign_f0].

  (* Field 0 is writable in m_loop *)
  assert (Hf0_perm_loop : Mem.range_perm m_loop new_b (Ptrofs.unsigned new_ofs) (Ptrofs.unsigned new_ofs + 8) Cur Writable).
  { intros ofs0 Hofs0. apply Hloop_perm_pres.
    apply (Hrp_f0 ofs0). simpl size_chunk. lia. }

  (* Store field 0 on m_loop *)
  set (code_ptr_val := Vptr cb (Ptrofs.add pc_ofs_1
    (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr code_ofs))))).

  destruct (Mem.valid_access_store m_loop Mint64 new_b (Ptrofs.unsigned new_ofs) code_ptr_val) as [m_s0 Hstore_f0].
  { split; [intros ofs0 Hofs0; apply Hf0_perm_loop; simpl size_chunk in Hofs0; lia | exact Halign_f0]. }

  assert (Hload_f0 : Mem.load Mint64 m_s0 new_b (Ptrofs.unsigned new_ofs) =
    Some (Val.load_result Mint64 code_ptr_val)).
  { eapply Mem.load_store_same. exact Hstore_f0. }

  assert (Hf0_load_pres : forall b ofs chunk v, b <> new_b ->
    Mem.load chunk m_loop b ofs = Some v -> Mem.load chunk m_s0 b ofs = Some v).
  { intros b0 ofs0 chunk v0 Hne Hld.
    erewrite Mem.load_store_other. exact Hld. exact Hstore_f0. left. exact Hne. }

  (* Field 1 alignment -- derive from dummy *)
  destruct (Hcan_store_f1_dummy (Vlong Int64.zero))
    as [m_s1_dummy [Hstore_f1_dummy [_ [_ [_ _]]]]].
  pose proof (Mem.store_valid_access_3 _ _ _ _ _ _ Hstore_f1_dummy) as [Hrp_f1_alloc Halign_f1].

  (* Field 1 writable in m_alloc (derive from dummy chain via perm_store_2) *)
  assert (Hrp_f1_m_alloc : Mem.range_perm m_alloc new_b
    (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8)))
    (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8)) + size_chunk Mint64) Cur Writable).
  { intros ofs0 Hofs0. eapply Mem.perm_store_2. exact Hstore_f0_dummy.
    apply (Hrp_f1_alloc ofs0). exact Hofs0. }

  (* Field 1 writable in m_s0 *)
  assert (Hf1_perm_s0 : Mem.range_perm m_s0 new_b
    (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8)))
    (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8)) + 8) Cur Writable).
  { intros ofs0 Hofs0.
    eapply Mem.perm_store_1. exact Hstore_f0.
    apply Hloop_perm_pres.
    apply (Hrp_f1_m_alloc ofs0). simpl size_chunk. lia. }

  set (closinfo_val := Vlong (Int64.or (Int64.repr (Int.signed (Int.shl (Int.repr 2) (Int.repr 1)))) (Int64.repr 1))).

  destruct (Mem.valid_access_store m_s0 Mint64 new_b
    (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) closinfo_val) as [m_s1 Hstore_f1].
  { split.
    - intros ofs0 Hofs0. apply Hf1_perm_s0. simpl size_chunk in Hofs0. lia.
    - exact Halign_f1. }

  assert (Hload_f1 : Mem.load Mint64 m_s1 new_b
    (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) =
    Some (Val.load_result Mint64 closinfo_val)).
  { eapply Mem.load_store_same. exact Hstore_f1. }

  assert (Hf1_load_f0_pres : forall v0,
    Mem.load Mint64 m_s0 new_b (Ptrofs.unsigned new_ofs) = Some v0 ->
    Mem.load Mint64 m_s1 new_b (Ptrofs.unsigned new_ofs) = Some v0).
  { intros v0 Hld.
    erewrite Mem.load_store_other. exact Hld. exact Hstore_f1.
    (* Field 0 at new_ofs, field 1 at Ptrofs.add new_ofs (Ptrofs.repr 8).
       Use Ptrofs.unsigned_add_either to case-split on wrap/no-wrap. *)
    pose proof (Ptrofs.unsigned_add_either new_ofs (Ptrofs.repr 8)) as [Hno_wrap | Hwrap].
    - (* No wrap: field_1_ofs = new_ofs + 8 *)
      right. left. simpl size_chunk.
      change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8 in Hno_wrap. lia.
    - (* Wrap: field_1_ofs = new_ofs + 8 - modulus (very small) *)
      right. right. simpl size_chunk.
      change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8 in Hwrap.
      pose proof (Ptrofs.unsigned_range new_ofs) as [Hno_lo Hno_hi].
      pose proof (Ptrofs.unsigned_range (Ptrofs.add new_ofs (Ptrofs.repr 8))) as [Hf1_lo _].
      (* modulus >= 16 since ptr64 = true *)
      assert (Hmod_big : Ptrofs.modulus >= 16).
      { unfold Ptrofs.modulus, Ptrofs.wordsize.
        change Archi.ptr64 with true. cbv. intro. discriminate. }
      lia. }

  assert (Hf1_load_pres : forall b ofs chunk v, b <> new_b ->
    Mem.load chunk m_s0 b ofs = Some v -> Mem.load chunk m_s1 b ofs = Some v).
  { intros b0 ofs0 chunk v0 Hne Hld.
    erewrite Mem.load_store_other. exact Hld. exact Hstore_f1. left. exact Hne. }

  assert (Hf1_perm_pres : forall b ofs k p,
    Mem.valid_block m_s0 b -> Mem.perm m_s0 b ofs k p -> Mem.perm m_s1 b ofs k p).
  { intros. eapply Mem.perm_store_1. exact Hstore_f1. exact H0. }

  (* --- Phases 10-12: pc advance, sp advance, accu store --- *)

  set (pc_ofs_2 := Ptrofs.add pc_ofs_1 (Ptrofs.repr 4)).

  (* sb_writable threads through all stores *)
  assert (Hsb_writable_loop :
    Mem.range_perm m_loop sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs0 Hofs0. apply Hloop_perm_pres. apply Hsb_writable_alloc. exact Hofs0. }

  assert (Hsb_writable_s0 :
    Mem.range_perm m_s0 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs0 Hofs0. eapply Mem.perm_store_1. exact Hstore_f0. apply Hsb_writable_loop. exact Hofs0. }

  assert (Hsb_writable_s1 :
    Mem.range_perm m_s1 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs0 Hofs0. eapply Hf1_perm_pres.
    - eapply Mem.perm_valid_block.
      apply (Hsb_writable_s0 (Ptrofs.unsigned so)). lia.
    - apply Hsb_writable_s0. exact Hofs0. }

  (* pc field in m_loop -- preserved from m_alloc through loop *)
  assert (Hpc_load_alloc : Mem.load Mint64 m_alloc sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs_1)).
  { apply Hstruct_preserved_alloc.
    erewrite Mem.load_store_other.
    2: exact Hstore_accu_push. 2: left; intro; subst; exact (Hsp_ne_sb eq_refl).
    erewrite Mem.load_store_other.
    2: exact Hstore_sp_push. 2: right; simpl size_chunk; lia.
    pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 0) (Vptr cb pc_ofs_1) Hstore_pc1) as Htmp.
    rewrite load_result_vptr_cl in Htmp. exact Htmp. }

  assert (Hpc_load_loop : Mem.load Mint64 m_loop sb (Ptrofs.unsigned so + 0) =
    Some (Vptr cb pc_ofs_1)).
  { apply Hloop_sb_pres. exact Hpc_load_alloc. }

  assert (Hpc_load_s1 : Mem.load Mint64 m_s1 sb (Ptrofs.unsigned so + 0) =
    Some (Vptr cb pc_ofs_1)).
  { apply Hf1_load_pres; auto. }

  (* Store pc field: pc_ofs_1 -> pc_ofs_2 *)
  destruct (store_succeeds_sb m_s1 sb so 0 (Vptr cb pc_ofs_1) Hsb_writable_s1 Hpc_load_s1 ltac:(lia) ltac:(lia) (Vptr cb pc_ofs_2))
    as [m_pc2 Hstore_pc2].

  (* sp field in m_s1 *)
  assert (Hsp_load_loop : Mem.load Mint64 m_loop sb (Ptrofs.unsigned so + 16) =
    Some (Vptr sp_b sp_ofs')).
  { apply Hloop_sb_pres. exact Hsp_load_alloc. }

  assert (Hsp_load_s1 : Mem.load Mint64 m_s1 sb (Ptrofs.unsigned so + 16) =
    Some (Vptr sp_b sp_ofs')).
  { apply Hf1_load_pres.
    - intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq).
    - apply Hf0_load_pres.
      + intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq).
      + exact Hsp_load_loop. }

  assert (Hsp_load_pc2 : Mem.load Mint64 m_pc2 sb (Ptrofs.unsigned so + 16) =
    Some (Vptr sp_b sp_ofs')).
  { apply (load_after_store_other m_s1 m_pc2 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 16) (Vptr cb pc_ofs_2) (Vptr sp_b sp_ofs') Hstore_pc2 Hsp_load_s1).
    right. lia. }

  assert (Hsb_writable_pc2 :
    Mem.range_perm m_pc2 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { eapply sb_writable_after_store; eauto. }

  (* sp advance: sp = sp' + nvars = sp - 8 + nvars * 8 *)
  set (sp_ofs_final := Ptrofs.add sp_ofs' (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat nvars))))).

  destruct (store_succeeds_sb m_pc2 sb so 16 (Vptr sp_b sp_ofs') Hsb_writable_pc2 Hsp_load_pc2 ltac:(lia) ltac:(lia) (Vptr sp_b sp_ofs_final))
    as [m_sp Hstore_sp].

  (* accu field in m_s1 *)
  assert (Haccu_load_alloc : Mem.load Mint64 m_alloc sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply Hstruct_preserved_alloc.
    erewrite Mem.load_store_other.
    2: exact Hstore_accu_push. 2: left; intro; subst; exact (Hsp_ne_sb eq_refl).
    erewrite Mem.load_store_other.
    2: exact Hstore_sp_push. 2: right; simpl size_chunk; lia.
    exact Haccu_load_m1. }

  assert (Haccu_load_loop : Mem.load Mint64 m_loop sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply Hloop_sb_pres. exact Haccu_load_alloc. }

  assert (Haccu_load_s1 : Mem.load Mint64 m_s1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply Hf1_load_pres; auto. }

  assert (Haccu_load_pc2 : Mem.load Mint64 m_pc2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m_s1 m_pc2 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 8) (Vptr cb pc_ofs_2) accu_v Hstore_pc2 Haccu_load_s1).
    right. lia. }

  assert (Haccu_load_sp : Mem.load Mint64 m_sp sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m_pc2 m_sp sb (Ptrofs.unsigned so + 16)
             (Ptrofs.unsigned so + 8) (Vptr sp_b sp_ofs_final) accu_v Hstore_sp Haccu_load_pc2).
    left. lia. }

  assert (Hsb_writable_sp :
    Mem.range_perm m_sp sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { eapply sb_writable_after_store; eauto. }

  destruct (store_succeeds_sb m_sp sb so 8 accu_v Hsb_writable_sp Haccu_load_sp ltac:(lia) ltac:(lia) block_v)
    as [m_final Hstore_accu].

  (* Final memory chain: m -> m1 (pc store) -> m2 (sp push) -> m3 (accu to stack) ->
     m_alloc (heap_alloc) -> m_loop (env copy loop) ->
     m_s0 (field 0) -> m_s1 (field 1) ->
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
        exfalso. unfold addr, hm in H. rewrite Hhm_fresh in H. discriminate.
      + exact H.
    - econstructor.
      + unfold hm'. destruct (Nat.eqb addr0 addr) eqn:Heq.
        * apply Nat.eqb_eq in Heq. subst addr0.
          exfalso. unfold addr, hm in H. rewrite Hhm_fresh in H. discriminate.
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
  (* le5 already defined: PTree.set _i (Vint (Int.repr 0)) le4 *)
  (* le_loop is the result after the loop -- it has _s, _block, _nvars etc *)
  set (le6 := PTree.set _t'6 (Vptr cb pc_ofs_1) le_loop).
  set (le7 := PTree.set _t'7 (Vptr cb pc_ofs_1) le6).
  set (le8 := PTree.set _t'8 (Vint (Int.repr code_ofs)) le7).
  set (le9 := PTree.set _t'5 (Vptr cb pc_ofs_1) le8).
  set (le10 := PTree.set _t'4 (Vptr sp_b sp_ofs') le9).
  set (le' := le10).

  exists le'. exists m_final.
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

    (* Phases 1-3 combined *)
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

    (* Phase 4: if-then branch: nvars > 0 is TRUE, push accu *)
    (* Sub-phase 4a: read sp (t'12 = s.sp) *)
    assert (Hexec_set_t12 : exec_stmt function_entry1 clight_ge e le2 m1
        (Sset _t'12
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        E0 le2a m1 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le2. rewrite PTree.gso by (compute; congruence).
      unfold le1. rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hsp_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      rewrite Hsp_load_m1; eval_cbn.
      reflexivity. }

    (* Sub-phase 4b: t'2 = cast(sp - 1) *)
    assert (Hexec_set_t2 : exec_stmt function_entry1 clight_ge e le2a m1
        (Sset _t'2
          (Ecast
            (Ebinop Osub (Etempvar _t'12 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong))
            (tptr tlong)))
        E0 le2b m1 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le2a. rewrite PTree.gss; eval_cbn.
      rewrite (sem_sub_sp_1 sp_b sp_ofs m1); eval_cbn. fold sp_ofs'.
      rewrite (sem_cast_ptr_to_ptr sp_b sp_ofs' m1); eval_cbn.
      reflexivity. }

    (* Sub-phase 4c: s.sp = t'2 (store sp' to struct) *)
    assert (Hexec_store_sp_push : exec_stmt function_entry1 clight_ge e le2b m1
        (Sassign
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
          (Etempvar _t'2 (tptr tlong)))
        E0 le2b m2 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le2b. rewrite PTree.gso by (compute; congruence).
      unfold le2a. rewrite PTree.gso by (compute; congruence).
      unfold le2. rewrite PTree.gso by (compute; congruence).
      unfold le1. rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hsp_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      unfold le2b. rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_ptr_to_ptr sp_b sp_ofs' m1); eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      rewrite Hstore_sp_push; eval_cbn.
      reflexivity. }

    (* Sub-phase 4d: read accu (t'11 = s.accu) *)
    assert (Hexec_set_t11 : exec_stmt function_entry1 clight_ge e le2b m2
        (Sset _t'11
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
        E0 le2c m2 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le2b. rewrite PTree.gso by (compute; congruence).
      unfold le2a. rewrite PTree.gso by (compute; congruence).
      unfold le2. rewrite PTree.gso by (compute; congruence).
      unfold le1. rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Haccu_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Haccu_load_m2; eval_cbn.
      reflexivity. }

    (* Sub-phase 4e: *t'2 = t'11 (store accu to stack) *)
    assert (Hexec_store_accu_push : exec_stmt function_entry1 clight_ge e le2c m2
        (Sassign (Ederef (Etempvar _t'2 (tptr tlong)) tlong)
          (Etempvar _t'11 tlong))
        E0 le2c m3 Out_normal).
    { eapply exec_Sassign.
      - eapply eval_Ederef.
        eapply eval_Etempvar.
        unfold le2c. rewrite PTree.gso by (compute; congruence).
        unfold le2b. rewrite PTree.gss. reflexivity.
      - eapply eval_Etempvar.
        unfold le2c. rewrite PTree.gss. reflexivity.
      - apply (sem_cast_long_val_repr hm cb co (Machine.accu s) accu_v m2 Haccu_repr).
      - eapply assign_loc_value.
        + reflexivity.
        + unfold Mem.storev.
          exact Hstore_accu_push. }

    (* Combine the if-then branch sub-phases *)
    assert (Hexec_push_sp_dec : exec_stmt function_entry1 clight_ge e le2 m1
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
        E0 le2b m2 Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      - replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto.
      - eauto. }

    assert (Hexec_push_accu : exec_stmt function_entry1 clight_ge e le2b m2
        (Ssequence
          (Sset _t'11
            (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
          (Sassign (Ederef (Etempvar _t'2 (tptr tlong)) tlong)
            (Etempvar _t'11 tlong)))
        E0 le2c m3 Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto. }

    assert (Hexec_if_body : exec_stmt function_entry1 clight_ge e le2 m1
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
            (Sset _t'11
              (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong))
            (Sassign (Ederef (Etempvar _t'2 (tptr tlong)) tlong)
              (Etempvar _t'11 tlong))))
        E0 le2c m3 Out_normal).
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto. }

    (* The full if-then-else: condition is true *)
    assert (Hexec_if_then : exec_stmt function_entry1 clight_ge e le2 m1
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
        E0 le2c m3 Out_normal).
    { eapply exec_Sifthenelse with (b := true).
      - (* eval_expr: nvars > 0 *)
        eapply eval_Ebinop.
        + eapply eval_Etempvar.
          unfold le2. rewrite PTree.gss. reflexivity.
        + eapply eval_Econst_int.
        + apply sem_cmp_gt_int_0.
      - (* bool_val (Val.of_bool (Int.lt 0 (S nvars'))) = Some true *)
        unfold nvars.
        rewrite (int_lt_0_S nvars' ltac:(unfold nvars in Hnvars_range2; lia)).
        simpl. reflexivity.
      - exact Hexec_if_body. }

    (* Phase 5: Scall heap_alloc *)
    assert (Hexec_call : exec_stmt function_entry1 clight_ge e le2c m3
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
        (vargs := Vptr sb so :: Vlong (Int64.repr (Z.of_nat (2 + nvars))) :: Vlong (Int64.repr 247) :: nil)
        (f := heap_alloc_fundef)
        (vres := Vptr new_b new_ofs).
      - reflexivity.
      - eapply eval_Elvalue.
        + eapply eval_Evar_global.
          * unfold le2c, le2b, le2a, le2, le1.
            repeat (rewrite PTree.gso by (compute; congruence)).
            exact He_heap_alloc.
          * exact Hfind_symbol.
        + apply deref_loc_reference. simpl. reflexivity.
      - econstructor.
        + econstructor.
          unfold le2c. rewrite PTree.gso by (compute; congruence).
          unfold le2b. rewrite PTree.gso by (compute; congruence).
          unfold le2a. rewrite PTree.gso by (compute; congruence).
          unfold le2. rewrite PTree.gso by (compute; congruence).
          unfold le1. rewrite PTree.gso by (compute; congruence).
          exact Hle_s.
        + simpl. reflexivity.
        + econstructor.
          * econstructor.
            -- econstructor.
            -- econstructor.
               unfold le2c. rewrite PTree.gso by (compute; congruence).
               unfold le2b. rewrite PTree.gso by (compute; congruence).
               unfold le2a. rewrite PTree.gso by (compute; congruence).
               unfold le2. rewrite PTree.gss. reflexivity.
            -- simpl. reflexivity.
          * (* sem_cast (Vint (Int.add (Int.repr 2) (Int.repr nvars))) tint tlong *)
            change (typeof (Ebinop Oadd (Econst_int (Int.repr 2) tint)
                     (Etempvar _nvars tint) tint)) with tint.
            rewrite sem_cast_int_to_long.
            simpl cast_int_int.
            change (Z.pos (Pos.of_succ_nat nvars')) with (Z.of_nat nvars).
            replace (Int.signed (Int.add (Int.repr 2) (Int.repr (Z.of_nat nvars))))
              with (Z.of_nat (2 + nvars)).
            { reflexivity. }
            rewrite Nat2Z.inj_add. simpl (Z.of_nat 2).
            symmetry.
            rewrite <- (Int.signed_repr (2 + Z.of_nat nvars)).
            2: { change Int.min_signed with (-2147483648)%Z.
                 change Int.max_signed with 2147483647%Z.
                 pose proof (proj2 Hnvars_range2) as Hnr.
                 change Int.max_signed with 2147483647%Z in Hnr. lia. }
            f_equal. rewrite Int.add_unsigned.
            apply Int.eqm_samerepr. apply Int.eqm_refl2.
            rewrite !Int.unsigned_repr;
              (change Int.max_unsigned with 4294967295%Z;
               change Int.max_signed with 2147483647%Z in Hnvars_range2; lia).
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

    (* Phase 7: init loop var + loop -- uses the postcondition *)
    (* The exec_stmt from the loop postcondition includes the Sset _i init *)

    (* Phase 8: Read pc for code pointer + store block[0] *)
    (* code_ofs word load in m_loop *)
    assert (Hpc_ofs_1_eq : pc_ofs_1 =
      Ptrofs.add co (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))).
    { unfold pc_ofs_1, pc_ofs, sizeof_code_t.
      rewrite Ptrofs.add_assoc. f_equal.
      rewrite Ptrofs.add_unsigned.
      apply Ptrofs.eqm_samerepr.
      eapply Ptrofs.eqm_trans.
      - apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
      - apply Ptrofs.eqm_refl2. lia. }

    assert (Hcode_ofs_load_loop : Mem.load Mint32 m_loop cb (Ptrofs.unsigned pc_ofs_1) =
              Some (Vint (Int.repr code_ofs))).
    { rewrite Hpc_ofs_1_eq.
      apply Hloop_load_pres.
      - intro Heq; symmetry in Heq; exact (Hnew_ne_cb Heq).
      - apply Halloc_load_pres.
        + erewrite Mem.load_store_other.
          2: exact Hstore_accu_push. 2: left; intro; subst; exact (Hcb_ne_sp eq_refl).
          erewrite Mem.load_store_other.
          2: exact Hstore_sp_push. 2: left; exact Hcb_ne.
          erewrite Mem.load_store_other.
          2: exact Hstore_pc1. 2: left; exact Hcb_ne.
          exact Hcode_ofs.
        + intro Heq; symmetry in Heq; exact (Hnew_ne_cb Heq). }

    assert (Hcode_ofs_load_alloc : Mem.load Mint32 m_alloc cb (Ptrofs.unsigned pc_ofs_1) =
              Some (Vint (Int.repr code_ofs))).
    { rewrite Hpc_ofs_1_eq.
      apply Halloc_load_pres.
      - erewrite Mem.load_store_other.
        2: exact Hstore_accu_push. 2: left; intro; subst; exact (Hcb_ne_sp eq_refl).
        erewrite Mem.load_store_other.
        2: exact Hstore_sp_push. 2: left; exact Hcb_ne.
        erewrite Mem.load_store_other.
        2: exact Hstore_pc1. 2: left; exact Hcb_ne.
        exact Hcode_ofs.
      - intro Heq; symmetry in Heq; exact (Hnew_ne_cb Heq). }

    assert (Hexec_set_t6 : exec_stmt function_entry1 clight_ge e le_loop m_loop
        (Sset _t'6
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        E0 le6 m_loop Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      rewrite Hle_loop_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      fold sb. fold so.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load_loop; eval_cbn.
      reflexivity. }

    assert (Hexec_set_t7 : exec_stmt function_entry1 clight_ge e le6 m_loop
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        E0 le7 m_loop Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le6. rewrite PTree.gso by (compute; congruence).
      rewrite Hle_loop_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      fold sb. fold so.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load_loop; eval_cbn.
      reflexivity. }

    assert (Hexec_set_t8 : exec_stmt function_entry1 clight_ge e le7 m_loop
        (Sset _t'8 (Ederef (Etempvar _t'7 (tptr tint)) tint))
        E0 le8 m_loop Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le7. rewrite PTree.gss; eval_cbn.
      rewrite Hcode_ofs_load_loop; eval_cbn.
      reflexivity. }

    (* Store: block[0] = t'6 + t'8 = code_ptr_val *)
    assert (Hexec_store_code_ptr : exec_stmt function_entry1 clight_ge e le8 m_loop
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
      - eapply eval_Ederef.
        eapply eval_Ebinop.
        + eapply eval_Ecast.
          * eapply eval_Etempvar.
            unfold le8. rewrite PTree.gso by (compute; congruence).
            unfold le7. rewrite PTree.gso by (compute; congruence).
            unfold le6. rewrite PTree.gso by (compute; congruence).
            rewrite Hle_loop_block. reflexivity.
          * apply sem_cast_vptr_tlong_to_ptr_ptr_tint.
        + eapply eval_Econst_int.
        + apply sem_add_ptr_ptr_tint_0.
      - eapply eval_Ebinop.
        + eapply eval_Etempvar.
          unfold le8.
          rewrite PTree.gso by (compute; congruence).
          unfold le7. rewrite PTree.gso by (compute; congruence).
          unfold le6. rewrite PTree.gss. reflexivity.
        + eapply eval_Etempvar.
          unfold le8. rewrite PTree.gss. reflexivity.
        + apply sem_add_ptr_tint_int.
      - apply sem_cast_ptr_tint_to_ptr_tint_cl.
      - eapply assign_loc_value.
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
      unfold le8. rewrite PTree.gso by (compute; congruence).
      unfold le7. rewrite PTree.gso by (compute; congruence).
      unfold le6. rewrite PTree.gso by (compute; congruence).
      rewrite Hle_loop_block; eval_cbn.
      fold block_v.
      replace (sem_cast block_v tlong (tptr tlong) m_s0)
        with (Some block_v)
        by (unfold block_v, sem_cast; simpl classify_cast; reflexivity);
        eval_cbn.
      unfold block_v at 1.
      rewrite (sem_add_sp_1 new_b new_ofs m_s0); eval_cbn.
      rewrite sem_shl_int_1; eval_cbn.
      rewrite sem_cast_int_to_tlong; eval_cbn.
      rewrite sem_or_long_int; eval_cbn.
      rewrite sem_cast_long_vlong; eval_cbn.
      change (Int64.repr (Int.signed (Int.repr 1))) with (Int64.repr 1).
      fold closinfo_val.
      rewrite Hstore_f1; eval_cbn.
      reflexivity. }

    (* Phase 10: Read pc (t'5 = s.pc), advance pc (s.pc = t'5 + 1) *)
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
      rewrite Hle_loop_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      fold sb. fold so.
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
      rewrite Hle_loop_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_pc_1_closure cb pc_ofs_1 m_s1); eval_cbn.
      rewrite (sem_cast_ptr_tint_to_ptr_tint_cl cb pc_ofs_2); eval_cbn.
      fold sb. fold so.
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
      rewrite Hle_loop_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hsp_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      fold sb. fold so.
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
      rewrite Hle_loop_s; eval_cbn.
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
      rewrite Hle_loop_nvars.
      fold sp_ofs'.
      rewrite (sem_add_ptr_tlong_int sp_b sp_ofs' (Int.repr (Z.of_nat nvars)) m_pc2).
      fold sp_ofs_final.
      rewrite (sem_cast_ptr_to_ptr sp_b sp_ofs_final m_pc2); eval_cbn.
      fold sb. fold so.
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
      rewrite Hle_loop_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Haccu_offset; eval_cbn.
      (* rvalue: _block *)
      unfold le10. rewrite PTree.gso by (compute; congruence).
      unfold le9. rewrite PTree.gso by (compute; congruence).
      unfold le8. rewrite PTree.gso by (compute; congruence).
      unfold le7. rewrite PTree.gso by (compute; congruence).
      unfold le6. rewrite PTree.gso by (compute; congruence).
      rewrite Hle_loop_block; eval_cbn.
      fold block_v.
      replace (sem_cast block_v tlong tlong m_sp) with (Some block_v)
        by (unfold block_v; apply (sem_cast_long_vptr new_b new_ofs m_sp)); eval_cbn.
      fold sb. fold so.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Hstore_accu; eval_cbn.
      reflexivity. }

    (* Phase 13: Return 0 *)
    assert (Hexec_return : exec_stmt function_entry1 clight_ge e le10 m_final
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        E0 le10 m_final (Out_return (Some (Vint (Int.repr 0), tint)))).
    { apply (eval_stmt_to_exec clight_ge 10). reflexivity. }

    (* Now combine all phases.  The fn_body is the same Ssequence tree. *)

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

    (* Build: set_t7; [set_t8; store_code_ptr] *)
    assert (Hexec_t7_t8_code : exec_stmt function_entry1 clight_ge e le6 m_loop
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

    assert (Hexec_t6_code : exec_stmt function_entry1 clight_ge e le_loop m_loop
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

    (* Build: init_loop; [t6_code; closinfo_rest] *)
    (* The loop_full exec gives us from le4 m_alloc through the loop *)

    assert (Hexec_loop_code : exec_stmt function_entry1 clight_ge e le4 m_alloc
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          closure_env_loop)
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
      - exact Hexec_loop_full.
      - replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1.
        + exact Hexec_t6_code.
        + exact Hexec_closinfo_rest. }

    (* Build: Scall; Sset block; loop_code *)
    assert (Hexec_alloc_block_loop_code : exec_stmt function_entry1 clight_ge e le2c m3
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
            closure_env_loop)
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

    (* Build: if_then; alloc_block_loop_code *)
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
              closure_env_loop)
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
      eapply exec_Sseq_1.
      - exact Hexec_if_then.
      - (* le2c flows from the if-then branch to the alloc call.
           But wait: the if-then branch exits with le2c, m3.
           The alloc_block_loop_code starts from le2c m3. *)
        exact Hexec_alloc_block_loop_code. }

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

    (* Match fn_body *)
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

    (* pc field: written by store_pc2, preserved through m_sp, m_final *)
    assert (Hpc_load_pc2 : Mem.load Mint64 m_pc2 sb (uso + 0) =
              Some (Vptr cb pc_ofs_2)).
    { pose proof (load_after_store_same m_s1 m_pc2 sb (uso + 0) (Vptr cb pc_ofs_2) Hstore_pc2) as Htmp.
      rewrite load_result_vptr_cl in Htmp. exact Htmp. }

    assert (Hpc_load_sp : Mem.load Mint64 m_sp sb (uso + 0) = Some (Vptr cb pc_ofs_2)).
    { apply (load_after_store_other m_pc2 m_sp sb (uso + 16) (uso + 0)
               (Vptr sp_b sp_ofs_final) (Vptr cb pc_ofs_2) Hstore_sp Hpc_load_pc2).
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
      field_ofs >= 24 ->
      Mem.load Mint64 m sb (uso + field_ofs) = Some v ->
      Mem.load Mint64 m_final sb (uso + field_ofs) = Some v).
    { intros fo v Hfo Hload.
      (* m -> m1: store at uso+0 *)
      assert (H1 : Mem.load Mint64 m1 sb (uso + fo) = Some v).
      { apply (load_after_store_other m m1 sb (uso + 0) (uso + fo)
                 (Vptr cb pc_ofs_1) v Hstore_pc1 Hload). right. lia. }
      (* m1 -> m2: store at uso+16 *)
      assert (H2 : Mem.load Mint64 m2 sb (uso + fo) = Some v).
      { apply (load_after_store_other m1 m2 sb (uso + 16) (uso + fo)
                 (Vptr sp_b sp_ofs') v Hstore_sp_push H1). right. lia. }
      (* m2 -> m3: store at sp_b *)
      assert (H3 : Mem.load Mint64 m3 sb (uso + fo) = Some v).
      { erewrite Mem.load_store_other. exact H2. exact Hstore_accu_push.
        left. intro; subst; exact (Hsp_ne_sb eq_refl). }
      (* m3 -> m_alloc *)
      assert (H4 : Mem.load Mint64 m_alloc sb (uso + fo) = Some v).
      { apply Hstruct_preserved_alloc. exact H3. }
      (* m_alloc -> m_loop *)
      assert (H5 : Mem.load Mint64 m_loop sb (uso + fo) = Some v).
      { apply Hloop_sb_pres. exact H4. }
      (* m_loop -> m_s0 *)
      assert (H6 : Mem.load Mint64 m_s0 sb (uso + fo) = Some v).
      { apply Hf0_load_pres; auto. }
      (* m_s0 -> m_s1 *)
      assert (H7 : Mem.load Mint64 m_s1 sb (uso + fo) = Some v).
      { apply Hf1_load_pres; auto. }
      (* m_s1 -> m_pc2: store at uso+0 *)
      assert (H8 : Mem.load Mint64 m_pc2 sb (uso + fo) = Some v).
      { apply (load_after_store_other m_s1 m_pc2 sb (uso + 0) (uso + fo)
                 (Vptr cb pc_ofs_2) v Hstore_pc2 H7). right. lia. }
      (* m_pc2 -> m_sp: store at uso+16 *)
      assert (H9 : Mem.load Mint64 m_sp sb (uso + fo) = Some v).
      { apply (load_after_store_other m_pc2 m_sp sb (uso + 16) (uso + fo)
                 (Vptr sp_b sp_ofs_final) v Hstore_sp H8).
        right. lia. }
      (* m_sp -> m_final: store at uso+8 *)
      apply (load_after_store_other m_sp m_final sb (uso + 8) (uso + fo)
               block_v v Hstore_accu H9). right. lia. }

    (* sp field: stored at m_sp with sp_ofs_final *)
    assert (Hsp_load_sp : Mem.load Mint64 m_sp sb (uso + 16) = Some (Vptr sp_b sp_ofs_final)).
    { pose proof (load_after_store_same m_pc2 m_sp sb (uso + 16) (Vptr sp_b sp_ofs_final) Hstore_sp) as Htmp.
      rewrite load_result_vptr_cl in Htmp. exact Htmp. }

    assert (Hsp_load_final : Mem.load Mint64 m_final sb (uso + 16) = Some (Vptr sp_b sp_ofs_final)).
    { apply (load_after_store_other m_sp m_final sb (uso + 8) (uso + 16)
               block_v (Vptr sp_b sp_ofs_final) Hstore_accu Hsp_load_sp).
      right. lia. }

    assert (Henv_load_final : Mem.load Mint64 m_final sb (uso + 24) = Some env_v).
    { apply Hfield_survive; [lia | exact Henv_load]. }

    assert (Hextra_load_final : Mem.load Mint64 m_final sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply Hfield_survive; [lia | exact Hextra_load]. }

    assert (Hgd_load_final : Mem.load Mint64 m_final sb (uso + 40) = Some (Vptr gb go0)).
    { apply Hfield_survive; [lia | exact Hgd_load]. }

    assert (Hts_load_final : Mem.load Mint64 m_final sb (uso + 48) = Some ts_ptr).
    { apply Hfield_survive; [lia | exact Hts_load]. }

    (* Stack repr for the post-state *)
    (* The Rocq post-state stack is skipn nvars (accu :: stack s).
       sp_ofs_final = sp_ofs' + nvars * 8 = sp_ofs - 8 + nvars * 8.
       Since nvars = S nvars', sp_ofs_final = sp_ofs - 8 + (1 + nvars') * 8
       = sp_ofs + nvars' * 8. *)

    (* We need stack_repr for the skipn'd stack at sp_ofs_final in m_final.
       The stack in m3 was accu :: stack s at sp_ofs'.
       After the loop/stores, the sp_b contents for the skipn'd portion are preserved.

       key insight: skipn nvars (accu :: stack s) starts at position nvars
       in the stack stored at sp_b starting from sp_ofs'.
       Each element is 8 bytes, so the skipn'd stack starts at sp_ofs' + nvars * 8 = sp_ofs_final.

       The values at those positions are the same as in m3 because:
       - m3 -> m_alloc: alloc preserves sp_b loads (sp_b <> new_b)
       - m_alloc -> m_loop: loop preserves sp_b loads (new_b <> sp_b)
       - m_loop -> m_s0, m_s1: field stores on new_b preserve sp_b
       - m_s1 -> m_pc2: store on sb preserves sp_b
       - m_pc2 -> m_sp: store on sb preserves sp_b
       - m_sp -> m_final: store on sb preserves sp_b
    *)

    assert (Hsp_ne_new : sp_b <> new_b).
    { intro Heq; symmetry in Heq; exact (Hnew_ne_sp Heq). }
    assert (Hgb_ne_new : gb <> new_b).
    { intro Heq; symmetry in Heq; exact (Hnew_ne_gb Heq). }

    (* Build stack_repr in m_final for the skipn'd stack *)
    (* First, get stack_repr for accu :: stack in m3 at sp_ofs' *)
    (* Then show it survives to m_final *)
    (* Then use an inductive argument to get the skipn'd part *)

    (* stack_repr for pushed stack in m3 *)
    (* Already have: Hstack_pushed : stack_repr hm cb co m3 (accu :: stack s) sp_b sp_ofs' *)

    (* Hstack_alloc already proved above *)

    (* Survive: m_alloc -> m_loop *)
    assert (Hstack_loop : stack_repr hm cb co m_loop (Machine.accu s :: Machine.stack s) sp_b sp_ofs').
    { clear -Hstack_alloc Hloop_load_pres Hsp_ne_new.
      induction Hstack_alloc as [| v vs sp_b0 sp_ofs0 cv Hld Hvr Htl IH].
      - constructor.
      - econstructor.
        + apply Hloop_load_pres. exact Hsp_ne_new. exact Hld.
        + exact Hvr.
        + apply IH. exact Hsp_ne_new. }

    (* Survive: m_loop -> m_s0 *)
    assert (Hstack_s0 : stack_repr hm cb co m_s0 (Machine.accu s :: Machine.stack s) sp_b sp_ofs').
    { eapply (stack_repr_store_other_block hm cb co); eauto. }

    (* Survive: m_s0 -> m_s1 *)
    assert (Hstack_s1 : stack_repr hm cb co m_s1 (Machine.accu s :: Machine.stack s) sp_b sp_ofs').
    { clear -Hstack_s0 Hf1_load_pres Hsp_ne_new.
      induction Hstack_s0 as [| v vs sp_b0 sp_ofs0 cv Hld Hvr Htl IH].
      - constructor.
      - econstructor.
        + apply Hf1_load_pres. exact Hsp_ne_new. exact Hld.
        + exact Hvr.
        + apply IH. exact Hsp_ne_new. }

    (* Survive: m_s1 -> m_pc2 *)
    assert (Hstack_pc2 : stack_repr hm cb co m_pc2 (Machine.accu s :: Machine.stack s) sp_b sp_ofs').
    { eapply (stack_repr_store_other_block hm cb co); eauto. }

    (* Survive: m_pc2 -> m_sp *)
    assert (Hstack_sp : stack_repr hm cb co m_sp (Machine.accu s :: Machine.stack s) sp_b sp_ofs').
    { eapply (stack_repr_store_other_block hm cb co); eauto. }

    (* Survive: m_sp -> m_final *)
    assert (Hstack_final_full : stack_repr hm cb co m_final (Machine.accu s :: Machine.stack s) sp_b sp_ofs').
    { eapply (stack_repr_store_other_block hm cb co); eauto. }

    (* Now prove that skipn nvars of the stack starting at sp_ofs'
       has stack_repr at sp_ofs' + nvars * 8 = sp_ofs_final *)
    assert (Hstack_skipn : forall (n : nat) (stk : list Value.value) (m0 : mem) (b : block) (sofs : ptrofs),
      (n <= length stk)%nat ->
      stack_repr hm cb co m0 stk b sofs ->
      stack_repr hm cb co m0 (skipn n stk) b
        (Ptrofs.add sofs (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.repr (Z.of_nat n))))).
    { induction n as [| n' IH_n].
      - intros stk0 m0 b0 sofs0 Hle Hsr.
        simpl skipn. change (Z.of_nat 0) with 0%Z.
        rewrite Ptrofs.mul_zero. rewrite Ptrofs.add_zero. exact Hsr.
      - intros stk0 m0 b0 sofs0 Hle Hsr.
        destruct stk0 as [| hd tl].
        + simpl in Hle. lia.
        + simpl skipn. inversion Hsr as [| v vs b_sr ofs_sr cv Hload Hvr Htl]; subst.
          assert (Hle' : (n' <= length tl)%nat) by (simpl in Hle; lia).
          specialize (IH_n tl m0 b0 (Ptrofs.add sofs0 (Ptrofs.repr 8)) Hle' Htl).
          (* Need: Ptrofs.add sofs0 (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.repr (Z.of_nat (S n'))))
             = Ptrofs.add (Ptrofs.add sofs0 (Ptrofs.repr 8))
                 (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.repr (Z.of_nat n'))) *)
          replace (Ptrofs.add sofs0 (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.repr (Z.of_nat (S n')))))
            with (Ptrofs.add (Ptrofs.add sofs0 (Ptrofs.repr 8))
                   (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.repr (Z.of_nat n')))).
          2: { rewrite Ptrofs.add_assoc. f_equal.
               rewrite Nat2Z.inj_succ.
               replace (Ptrofs.repr (Z.succ (Z.of_nat n')))
                 with (Ptrofs.add (Ptrofs.repr 1) (Ptrofs.repr (Z.of_nat n'))).
               2: { rewrite Ptrofs.add_unsigned.
                    apply Ptrofs.eqm_samerepr.
                    apply Ptrofs.eqm_trans with (1 + Z.of_nat n')%Z.
                    - apply Ptrofs.eqm_sym.
                      apply Ptrofs.eqm_add; apply Ptrofs.eqm_unsigned_repr.
                    - apply Ptrofs.eqm_refl2. lia. }
               rewrite Ptrofs.mul_add_distr_r.
               f_equal. }
          exact IH_n. }

    assert (Hlen_ge : (nvars <= length (Machine.accu s :: Machine.stack s))%nat).
    { simpl. exact Hnvars_stack_bound. }

    pose proof (Hstack_skipn nvars (Machine.accu s :: Machine.stack s)
      m_final sp_b sp_ofs' Hlen_ge Hstack_final_full) as Hstack_skipn_result.

    assert (Hsp_ofs_final_eq : sp_ofs_final =
      Ptrofs.add sp_ofs' (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.repr (Z.of_nat nvars)))).
    { unfold sp_ofs_final. f_equal. f_equal.
      unfold ptrofs_of_int.
      apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_refl2.
      rewrite Int.signed_repr.
      2: { change Int.min_signed with (-2147483648)%Z.
           change Int.max_signed with 2147483647%Z.
           change Int.max_signed with 2147483647%Z in Hnvars_range2. lia. }
      reflexivity. }

    rewrite <- Hsp_ofs_final_eq in Hstack_skipn_result.

    (* Unsigned value of sp_ofs_final *)
    assert (Hsp_ofs_final_unsigned : Ptrofs.unsigned sp_ofs_final =
      Ptrofs.unsigned sp_ofs - 8 + Z.of_nat nvars * 8).
    { unfold sp_ofs_final, ptrofs_of_int.
      change (Ptrofs.of_ints (Int.repr (Z.of_nat nvars)))
        with (Ptrofs.repr (Int.signed (Int.repr (Z.of_nat nvars)))).
      rewrite Int.signed_repr
        by (change Int.min_signed with (-2147483648)%Z;
            change Int.max_signed with 2147483647%Z in Hnvars_range2 |- *; lia).
      rewrite Ptrofs.mul_signed.
      rewrite Ptrofs.signed_repr.
      2: { change Ptrofs.min_signed with (-9223372036854775808)%Z.
           change Ptrofs.max_signed with 9223372036854775807%Z. lia. }
      rewrite Ptrofs.signed_repr.
      2: { change Ptrofs.min_signed with (-9223372036854775808)%Z.
           change Ptrofs.max_signed with 9223372036854775807%Z.
           change Int.max_signed with 2147483647%Z in Hnvars_range2. lia. }
      change Int.max_signed with 2147483647%Z in Hnvars_range2.
      rewrite Nat2Z.inj_add in Hnvars_range2.
      assert (Hnvars_range3 : Z.of_nat nvars <= 2147483645)
        by (simpl (Z.of_nat 2) in Hnvars_range2; lia).
      assert (Hnat_le : (nvars <= S (length (Machine.stack s)))%nat)
        by exact Hnvars_stack_bound.
      apply Nat2Z.inj_le in Hnat_le.
      rewrite Nat2Z.inj_succ in Hnat_le.
      change Ptrofs.modulus with 18446744073709551616%Z in Hsp_rep.
      rewrite Ptrofs.add_unsigned.
      rewrite (Ptrofs.unsigned_repr (8 * Z.of_nat nvars)).
      2: { change Ptrofs.max_unsigned with 18446744073709551615%Z.
           pose proof (Nat2Z.is_nonneg nvars).
           lia. }
      rewrite Ptrofs.unsigned_repr.
      2: { change Ptrofs.max_unsigned with 18446744073709551615%Z.
           rewrite Hsp_ofs'_val. lia. }
      rewrite Hsp_ofs'_val. lia. }

    (* Global repr in m_final *)
    assert (Hglobal_m1 : global_repr hm cb co m1 (Machine.global s) gb go0).
    { eapply (global_repr_store_other_block hm cb co); eauto. }

    assert (Hglobal_m2 : global_repr hm cb co m2 (Machine.global s) gb go0).
    { eapply (global_repr_store_other_block hm cb co); eauto. }

    assert (Hglobal_m3 : global_repr hm cb co m3 (Machine.global s) gb go0).
    { eapply (global_repr_store_other_block hm cb co); eauto. }

    assert (Hglobal_alloc : global_repr hm cb co m_alloc (Machine.global s) gb go0).
    { clear -Hglobal_m3 Halloc_load_pres Hgb_ne_new.
      induction Hglobal_m3 as [| v vs gb0 gofs0 cv Hld Hvr Htl IH].
      - constructor.
      - econstructor.
        + apply Halloc_load_pres. exact Hld. exact Hgb_ne_new.
        + exact Hvr.
        + apply IH. exact Hgb_ne_new. }

    assert (Hglobal_loop : global_repr hm cb co m_loop (Machine.global s) gb go0).
    { clear -Hglobal_alloc Hloop_load_pres Hgb_ne_new.
      induction Hglobal_alloc as [| v vs gb0 gofs0 cv Hld Hvr Htl IH].
      - constructor.
      - econstructor.
        + apply Hloop_load_pres. exact Hgb_ne_new. exact Hld.
        + exact Hvr.
        + apply IH. exact Hgb_ne_new. }

    assert (Hglobal_s0 : global_repr hm cb co m_s0 (Machine.global s) gb go0).
    { eapply (global_repr_store_other_block hm cb co); eauto. }

    assert (Hglobal_s1 : global_repr hm cb co m_s1 (Machine.global s) gb go0).
    { clear -Hglobal_s0 Hf1_load_pres Hgb_ne_new.
      induction Hglobal_s0 as [| v vs gb0 gofs0 cv Hld Hvr Htl IH].
      - constructor.
      - econstructor.
        + apply Hf1_load_pres. exact Hgb_ne_new. exact Hld.
        + exact Hvr.
        + apply IH. exact Hgb_ne_new. }

    assert (Hglobal_pc2 : global_repr hm cb co m_pc2 (Machine.global s) gb go0).
    { eapply (global_repr_store_other_block hm cb co); eauto. }

    assert (Hglobal_sp : global_repr hm cb co m_sp (Machine.global s) gb go0).
    { eapply (global_repr_store_other_block hm cb co); eauto. }

    assert (Hglobal_final : global_repr hm cb co m_final (Machine.global s) gb go0).
    { eapply (global_repr_store_other_block hm cb co); eauto. }

    (* sp_writable in m_final *)
    assert (Hsp_writable_final : forall ofs0,
      0 <= ofs0 < Ptrofs.unsigned sp_ofs_final +
        8 * Z.of_nat (length (skipn nvars (Machine.accu s :: Machine.stack s))) ->
      Mem.perm m_final sp_b ofs0 Cur Writable).
    { intros ofs0 Hofs0.
      eapply Mem.perm_store_1. exact Hstore_accu.
      eapply Mem.perm_store_1. exact Hstore_sp.
      eapply Mem.perm_store_1. exact Hstore_pc2.
      eapply Hf1_perm_pres.
      - eapply Mem.perm_valid_block.
        eapply Mem.perm_store_1. exact Hstore_f0.
        eapply Hloop_perm_pres.
        eapply Halloc_perm_pres.
        + eapply Mem.perm_valid_block.
          eapply Mem.perm_store_1. exact Hstore_accu_push.
          eapply Mem.perm_store_1. exact Hstore_sp_push.
          eapply Mem.perm_store_1. exact Hstore_pc1.
          apply (Hsp_writable 0). lia.
        + eapply Mem.perm_store_1. exact Hstore_accu_push.
          eapply Mem.perm_store_1. exact Hstore_sp_push.
          eapply Mem.perm_store_1. exact Hstore_pc1.
          apply Hsp_writable.
          assert (Hbound_eq : Ptrofs.unsigned sp_ofs_final +
              8 * Z.of_nat (length (skipn nvars (Machine.accu s :: Machine.stack s))) =
              Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))).
          { rewrite Hsp_ofs_final_unsigned.
            rewrite skipn_length. simpl length.
            assert (Hmin2 : (nvars <= S (length (Machine.stack s)))%nat)
              by exact Hnvars_stack_bound.
            rewrite Nat2Z.inj_sub by exact Hmin2.
            rewrite (Nat2Z.inj_succ (length (Machine.stack s))).
            unfold Z.succ.
            pose proof (Nat2Z.is_nonneg nvars) as Hnvars_nonneg.
            lia. }
          rewrite Hbound_eq in Hofs0. exact Hofs0.
      - eapply Mem.perm_store_1. exact Hstore_f0.
        eapply Hloop_perm_pres.
        eapply Halloc_perm_pres.
        + eapply Mem.perm_valid_block.
          eapply Mem.perm_store_1. exact Hstore_accu_push.
          eapply Mem.perm_store_1. exact Hstore_sp_push.
          eapply Mem.perm_store_1. exact Hstore_pc1.
          apply (Hsp_writable 0). lia.
        + eapply Mem.perm_store_1. exact Hstore_accu_push.
          eapply Mem.perm_store_1. exact Hstore_sp_push.
          eapply Mem.perm_store_1. exact Hstore_pc1.
          apply Hsp_writable.
          rewrite Hsp_ofs_final_unsigned in Hofs0.
          rewrite skipn_length in Hofs0. simpl length in Hofs0.
          assert (Hmin2 : (nvars <= S (length (Machine.stack s)))%nat)
            by exact Hnvars_stack_bound.
          rewrite Nat2Z.inj_sub in Hofs0 by exact Hmin2.
          rewrite (Nat2Z.inj_succ (length (Machine.stack s))) in Hofs0.
          unfold Z.succ in Hofs0.
          pose proof (Nat2Z.is_nonneg nvars) as Hnvars_nonneg.
          lia. }

    (* Now build abs_rel *)
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s in le' *)
    { subst le' le10 le9 le8 le7 le6.
      repeat (rewrite PTree.gso by (compute; congruence)).
      exact Hle_loop_s. }

    (* 2. pc field -- advanced twice *)
    { exists (Vptr cb pc_ofs_2). split.
      - exact Hpc_load_final.
      - simpl.
        unfold pc_rel, new_co, pc_ofs_2, pc_ofs_1, pc_ofs, sizeof_code_t.
        rewrite !Ptrofs.add_assoc.
        rewrite <- (Ptrofs.add_assoc (Ptrofs.repr 4) (Ptrofs.repr 4)).
        rewrite (Ptrofs.add_commut (Ptrofs.add (Ptrofs.repr 4) (Ptrofs.repr 4))).
        reflexivity. }

    (* 3. accu field -- Val_closure addr 0 *)
    { exists block_v. split.
      - exact Haccu_load_final.
      - simpl. eapply val_repr_co_shift. exact Hval_repr_new. }

    (* 4. sp field *)
    { exists (Vptr sp_b sp_ofs_final), sp_b, sp_ofs_final.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
      - exact Hsp_load_final.
      - reflexivity.
      - simpl.
        change (skipn nvars' (Machine.stack s)) with (skipn nvars (Machine.accu s :: Machine.stack s)).
        eapply stack_repr_co_shift. apply Hstack_repr_ext. exact Hstack_skipn_result.
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - (* sp_ofs_final >= 8 *)
        rewrite Hsp_ofs_final_unsigned.
        unfold nvars. simpl Z.of_nat. lia.
      - (* sp_rep: sp_ofs_final + 8 * |rest| < Ptrofs.modulus *)
        simpl Machine.stack.
        change (skipn nvars' (Machine.stack s)) with (skipn nvars (Machine.accu s :: Machine.stack s)).
        assert (Hmin : (nvars <= S (length (Machine.stack s)))%nat)
          by exact Hnvars_stack_bound.
        assert (Hbound_eq2 : Ptrofs.unsigned sp_ofs_final +
            8 * Z.of_nat (length (skipn nvars (Machine.accu s :: Machine.stack s))) =
            Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))).
        { rewrite Hsp_ofs_final_unsigned.
          rewrite skipn_length. simpl length.
          rewrite Nat2Z.inj_sub by exact Hmin.
          rewrite Nat2Z.inj_succ. unfold Z.succ.
          pose proof (Nat2Z.is_nonneg nvars) as Hnvars_nn.
          lia. }
        rewrite Hbound_eq2. exact Hsp_rep.
      - split.
        + (* sp_writable *)
          intros ofs0 Hofs0.
          apply Hsp_writable_final. exact Hofs0.
        + (* sp_align: 8 | Ptrofs.unsigned sp_ofs_final *)
          (* sp_ofs_final = sp_ofs - 8 + nvars * 8 (no-wrap),
             8 | sp_ofs (from Hsp_align), 8 | nvars * 8 trivially, 8 | 8 *)
          simpl align_chunk in *.
          rewrite Hsp_ofs_final_unsigned.
          destruct Hsp_align as [k Hk].
          exists (k - 1 + Z.of_nat nvars).
          lia. }

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

Definition CLOSURE_correct_for_spec : forall nvars code_ofs,
    (0 <= Z.of_nat (2 + nvars) <= Int.max_signed) ->
    Int.min_signed <= code_ofs <= Int.max_signed ->
    handler_correct (handle_CLOSURE nvars code_ofs) f_instr_CLOSURE
      (closure_general_step_pre nvars code_ofs)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
  Proof.
    intros nvars code_ofs Hnvars_range Hcode_ofs_range.
    apply verify_CLOSURE_general_correct.
    - rewrite Nat2Z.inj_add in Hnvars_range. simpl (Z.of_nat 2) in Hnvars_range.
      split; [apply Nat2Z.is_nonneg | lia].
    - exact Hcode_ofs_range.
  Qed.
