(* CLOSUREREC_correct.v -- CLOSUREREC handler completeness proof.

   CLOSUREREC creates recursive closures. It allocates a heap block for
   mutually-recursive functions, fills in code pointers and infix headers,
   then pushes closures onto the stack.

   This proof handles the simplest non-trivial case:
     nfuncs = 1, nvars = 0, code_offsets = [code_ofs]

   In this case:
   - nvars > 0 branch is skipped (no env vars to push/copy)
   - The first for-loop (copying env vars) executes 0 iterations
   - envofs = nfuncs * 3 - 1 = 2, blksize = envofs + nvars = 2
   - heap_alloc allocates a 2-field block with tag 247 (Closure_tag)
   - block[0] = code pointer, block[1] = closinfo
   - The second for-loop (infix headers for additional functions) starts
     at i=1 and checks i < nfuncs=1, which is false, so 0 iterations
   - One closure is pushed onto the stack, accu = closure_0

   Rocq handle_CLOSUREREC 1 0 [code_ofs] pc' s:
     let stk := s.(stack) in   -- nvars=0, no push
     let fields := [Val_int code_ofs; Val_int 0] in  -- code_ptr, closinfo
     let '(s', base_ptr) := heap_alloc s Closure_tag fields in
     let addr := ... in
     Step (s' <|pc:=pc'|> <|accu:=Val_closure addr 0|>
              <|stack:= Val_closure addr 0 :: stk|>). *)

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

Lemma interp_state_co_pc_accu_sp_cr : exists co,
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

Local Lemma sem_cast_int_tint_tint : forall n m,
  sem_cast (Vint n) tint tint m = Some (Vint n).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_add_int_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vint a) tint (Vint b) tint m = Some (Vint (Int.add a b)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_sub_int_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vint a) tint (Vint b) tint m = Some (Vint (Int.sub a b)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_mul_int_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Omul
    (Vint a) tint (Vint b) tint m = Some (Vint (Int.mul a b)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_cmp_gt_int_0 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Ogt
    (Vint n) tint
    (Vint (Int.repr 0)) tint
    m = Some (Val.of_bool (Int.lt (Int.repr 0) n)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_cmp_lt_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Olt
    (Vint a) tint
    (Vint b) tint
    m = Some (Val.of_bool (Int.lt a b)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_shl_int_1 : forall n m,
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

Local Lemma sem_cast_int_to_tlong : forall n m,
  sem_cast (Vint n) tint tlong m = Some (Vlong (Int64.repr (Int.signed n))).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_cast_int_to_tulong : forall n m,
  sem_cast (Vint n) tint tulong m = Some (Vlong (Int64.repr (Int.signed n))).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_cast_vptr_tlong_to_ptr_tlong : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_cast_vptr_ptr_tint_to_tlong : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) tlong m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. rewrite ptr64_true. reflexivity.
Qed.

Local Lemma sem_cast_vptr_tlong_to_ptr_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr (tptr tint)) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_add_ptr_ptr_tint_0 : forall b ofs m,
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

Local Lemma sem_add_ptr_tlong_int : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong)
    (Vint n) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_ptr_tlong_ulong : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong)
    (Vlong n) tulong
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tulong) with (add_case_pl tlong).
  unfold sem_add_ptr_long. reflexivity.
Qed.

Local Lemma sem_add_ptr_tint_int : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint n) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_or_long_int : forall a b m,
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

Local Lemma sem_add_ulong_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong a) tulong (Vint b) tint m
    = Some (Vlong (Int64.add a (Int64.repr (Int.signed b)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add tulong tint) with (add_default).
  unfold sem_binarith. simpl binarith_type.
  unfold sem_cast at 1. simpl classify_cast. rewrite ptr64_true.
  unfold sem_cast at 1. simpl classify_cast.
  reflexivity.
Qed.

Local Lemma sem_shl_ulong_int : forall a b m,
  Int.ltu b Int64.iwordsize' = true ->
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong a) tulong (Vint b) tint m
    = Some (Vlong (Int64.shl a (Int64.repr (Int.unsigned b)))).
Proof.
  intros a b m Hltu.
  unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tulong tint) with (shift_case_li Unsigned).
  simpl. rewrite Hltu. reflexivity.
Qed.

Local Lemma sem_or_ulong_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Oor
    (Vlong a) tulong (Vint b) tint m
    = Some (Vlong (Int64.or a (Int64.repr (Int.signed b)))).
Proof.
  intros. unfold sem_binary_operation, sem_or.
  change (classify_binarith tulong tint) with (bin_case_l Unsigned).
  unfold sem_binarith. simpl binarith_type.
  unfold sem_cast at 1. simpl classify_cast. rewrite ptr64_true.
  unfold sem_cast at 1. simpl classify_cast.
  reflexivity.
Qed.

Local Lemma sem_cast_ulong_to_tlong : forall n m,
  sem_cast (Vlong n) tulong tlong m = Some (Vlong n).
Proof.
  intros. unfold sem_cast. simpl classify_cast. rewrite ptr64_true. reflexivity.
Qed.

Local Lemma ptrofs_of_int_signed_0 :
  ptrofs_of_int Signed (Int.repr 0) = Ptrofs.zero.
Proof. reflexivity. Qed.

Local Lemma ptrofs_of_int_signed_1 :
  ptrofs_of_int Signed (Int.repr 1) = Ptrofs.one.
Proof. reflexivity. Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

Local Lemma int_lt_0_0 : Int.lt (Int.repr 0) (Int.repr 0) = false.
Proof. reflexivity. Qed.

Local Lemma int_lt_1_1 : Int.lt (Int.repr 1) (Int.repr 1) = false.
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Main theorem: nfuncs=1, nvars=0, code_offsets=[code_ofs]            *)
(* ================================================================== *)

Theorem verify_CLOSUREREC_correct : forall code_ofs,
    handler_correct (handle_CLOSUREREC 1 0 [code_ofs]) f_instr_CLOSUREREC
      (fun e m s ard =>
         let sb := ar_sptr_block ard in
         let so := ar_sptr_ofs ard in
         let cb := ar_code_base_block ard in
         let co := ar_code_base_ofs ard in
         let gb := ar_global_block ard in
         (* e does not bind heap_alloc *)
         e ! _heap_alloc = None /\
         (* Code buffer: nfuncs=1 at current PC *)
         Mem.load Mint32 m cb
           (Ptrofs.unsigned (Ptrofs.add co
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr 1)) /\
         (* Code buffer: nvars=0 at PC+1 *)
         Mem.load Mint32 m cb
           (Ptrofs.unsigned (Ptrofs.add co
              (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))))
         = Some (Vint (Int.repr 0)) /\
         (* Code buffer: code_ofs at PC+2 *)
         Mem.load Mint32 m cb
           (Ptrofs.unsigned (Ptrofs.add co
              (Ptrofs.repr ((Machine.pc s + 2) * sizeof_code_t))))
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
              (* Field 0 storable (code ptr) *)
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
                       Mem.perm m_s1 b ofs k p)))) /\
         (* sp writable at position below current sp for the push *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs >= 16 /\
            (align_chunk Mint64 | Ptrofs.unsigned sp_ofs - 8) /\
            Ptrofs.unsigned sp_ofs - 8 + 8 < Ptrofs.modulus))
      (fun msg _ => msg = "CLOSUREREC: no code offsets"%string -> False)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro code_ofs.
  intros e le m s.

  (* Reduce handle_CLOSUREREC 1 0 [code_ofs] (pc s) s *)
  unfold handle_CLOSUREREC. simpl Nat.ltb.

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

  destruct Hstep_pre as (He_heap_alloc & Hcode_nfuncs & Hcode_nvars & Hcode_ofs & Hcode_ofs_range &
    Hhm_fresh & Hgb_valid & [b_ha [Hfind_symbol Hfind_funct]] & Halloc_spec_all & Hsp_push_pre).

  (* Structural invariants *)
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  pose proof (code_block_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  (* Composite environment *)
  destruct interp_state_co_pc_accu_sp_cr as [co_is [Hco [Hpc_offset [Haccu_offset Hsp_offset]]]].

  (* pc_ptr is a concrete Vptr *)
  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* New pc after first advancement (reading nfuncs) *)
  set (pc_ofs_1 := Ptrofs.add pc_ofs (Ptrofs.repr 4)).

  (* --- Store 1: advance pc for nfuncs read --- *)
  destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia) (Vptr cb pc_ofs_1))
    as [m1 Hstore_pc1].

  (* Fields survive pc store *)
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 8) (Vptr cb pc_ofs_1) accu_v Hstore_pc1 Haccu_load).
    right. lia. }

  assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 16) (Vptr cb pc_ofs_1) (Vptr sp_b sp_ofs) Hstore_pc1 Hsp_load).
    right. lia. }

  (* Code loads survive pc store (different block) *)
  assert (Hcode_nfuncs_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
            Some (Vint (Int.repr 1))).
  { erewrite Mem.load_store_other.
    - exact Hcode_nfuncs.
    - exact Hstore_pc1.
    - left. exact Hcb_ne. }

  (* New pc after second advancement (reading nvars) *)
  set (pc_ofs_2 := Ptrofs.add pc_ofs_1 (Ptrofs.repr 4)).

  (* --- Store 2: advance pc for nvars read --- *)
  assert (Hsb_writable_m1 :
    Mem.range_perm m1 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { eapply sb_writable_after_store; eauto. }

  assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
    Some (Vptr cb pc_ofs_1)).
  { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 0) (Vptr cb pc_ofs_1) Hstore_pc1) as Htmp.
    rewrite load_result_vptr in Htmp. exact Htmp. }

  destruct (store_succeeds_sb m1 sb so 0 (Vptr cb pc_ofs_1) Hsb_writable_m1 Hpc_load_m1 ltac:(lia) ltac:(lia) (Vptr cb pc_ofs_2))
    as [m2 Hstore_pc2].

  assert (Hpc_ofs_1_eq : pc_ofs_1 =
    Ptrofs.add co (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))).
  { unfold pc_ofs_1, pc_ofs, sizeof_code_t.
    rewrite Ptrofs.add_assoc. f_equal.
    rewrite Ptrofs.add_unsigned.
    apply Ptrofs.eqm_samerepr.
    eapply Ptrofs.eqm_trans.
    - apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
    - apply Ptrofs.eqm_refl2. lia. }

  assert (Hcode_nvars_m1 : Mem.load Mint32 m1 cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t)))) =
    Some (Vint (Int.repr 0))).
  { erewrite Mem.load_store_other.
    - exact Hcode_nvars.
    - exact Hstore_pc1.
    - left. exact Hcb_ne. }

  assert (Hcode_nvars_m2 : Mem.load Mint32 m2 cb
    (Ptrofs.unsigned pc_ofs_1) =
    Some (Vint (Int.repr 0))).
  { erewrite Mem.load_store_other.
    - rewrite Hpc_ofs_1_eq. exact Hcode_nvars_m1.
    - exact Hstore_pc2.
    - left. exact Hcb_ne. }

  (* Accu, sp survive second pc store *)
  assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 8) (Vptr cb pc_ofs_2) accu_v Hstore_pc2 Haccu_load_m1).
    right. lia. }

  assert (Hsp_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
  { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 16) (Vptr cb pc_ofs_2) (Vptr sp_b sp_ofs) Hstore_pc2 Hsp_load_m1).
    right. lia. }

  (* --- Conditional: nvars > 0 is false (nvars=0), skip the push --- *)

  (* --- heap_alloc: allocate 2-field block with tag 247 --- *)
  (* envofs = nfuncs * 3 - 1 = 1*3-1 = 2 (as unsigned long)
     blksize = envofs + nvars = 2 + 0 = 2 *)

  (* Instantiate heap_alloc for m2 *)
  destruct (Halloc_spec_all m2)
    as [m_alloc [new_b [new_ofs
         (Hext_call & Hnew_fresh &
          Halloc_load_pres & Halloc_perm_pres & Hcan_store_f0)]]].

  (* Derive freshness for specific blocks *)
  assert (Hnew_ne_sb : new_b <> sb).
  { apply Hnew_fresh. eapply Mem.perm_valid_block.
    apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc2).
    apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc1).
    apply (Hsb_writable (Ptrofs.unsigned so)). lia. }
  assert (Hnew_ne_sp : new_b <> sp_b).
  { apply Hnew_fresh. eapply Mem.perm_valid_block.
    apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc2).
    apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc1).
    apply (Hsp_writable 0). lia. }
  assert (Hnew_ne_cb : new_b <> cb).
  { apply Hnew_fresh.
    pose proof (Mem.load_valid_access _ _ _ _ _ Hcode_nfuncs) as [Hrp_cb _].
    eapply Mem.perm_valid_block.
    apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc2).
    apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc1).
    apply (Hrp_cb (Ptrofs.unsigned pc_ofs)). simpl. lia. }
  assert (Hnew_ne_gb : new_b <> gb).
  { apply Hnew_fresh.
    eapply Mem.store_valid_block_1. exact Hstore_pc2.
    eapply Mem.store_valid_block_1. exact Hstore_pc1. exact Hgb_valid. }

  (* Struct field preservation from generic load preservation *)
  assert (Hstruct_preserved : forall ofs v,
    Mem.load Mint64 m2 sb ofs = Some v ->
    Mem.load Mint64 m_alloc sb ofs = Some v).
  { intros ofs0 v0 Hld. apply Halloc_load_pres; auto. }

  (* Accu in m_alloc *)
  assert (Haccu_load_alloc : Mem.load Mint64 m_alloc sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply Hstruct_preserved. exact Haccu_load_m2. }

  (* --- Store field 0: code pointer --- *)
  (* After reading nfuncs and nvars, pc has been advanced twice.
     pc is now at pc_ofs_2. The C reads code_ofs from *pc (at pc_ofs_2).
     code_ptr_val = pc_base + code_ofs_value *)

  assert (Hptrofs_4_4 : Ptrofs.add (Ptrofs.repr 4) (Ptrofs.repr 4) = Ptrofs.repr 8).
  { rewrite Ptrofs.add_unsigned.
    apply Ptrofs.eqm_samerepr.
    unfold Ptrofs.eqm. exists 0.
    change (Ptrofs.unsigned (Ptrofs.repr 4)) with 4. lia. }

  assert (Hpc_ofs_2_eq : pc_ofs_2 =
    Ptrofs.add co (Ptrofs.repr ((Machine.pc s + 2) * sizeof_code_t))).
  { unfold pc_ofs_2, pc_ofs_1, pc_ofs, sizeof_code_t.
    rewrite !Ptrofs.add_assoc. f_equal.
    rewrite Hptrofs_4_4.
    rewrite Ptrofs.add_unsigned.
    apply Ptrofs.eqm_samerepr.
    eapply Ptrofs.eqm_trans.
    - apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
    - apply Ptrofs.eqm_refl2. lia. }

  set (code_ptr_val := Vptr cb (Ptrofs.add pc_ofs_2
    (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr code_ofs))))).

  set (envofs_val := Int64.repr 2).
  set (closinfo_val := Vlong (Int64.or (Int64.shl envofs_val (Int64.repr (Int.unsigned (Int.repr 1)))) (Int64.repr (Int.signed (Int.repr 1))))).

  (* sb_writable threads through stores *)
  assert (Hsb_writable_m2 :
    Mem.range_perm m2 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { eapply sb_writable_after_store; eauto. }
  assert (Hsb_writable_alloc :
    Mem.range_perm m_alloc sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs0 Hofs0. eapply Halloc_perm_pres.
    - eapply Mem.perm_valid_block.
      apply (Hsb_writable_m2 (Ptrofs.unsigned so)). lia.
    - apply Hsb_writable_m2. exact Hofs0. }

  (* sp_push_ofs = sp_ofs - 8 *)
  set (sp_push_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
  set (block_v := Vptr new_b new_ofs).

  (* We need sp_b writable at sp_push_ofs *)
  assert (Hsp_push_pre_inst := Hsp_push_pre sp_b sp_ofs Hsp_load).
  destruct Hsp_push_pre_inst as [Hsp_ofs_ge16 [Hsp_push_align Hsp_push_rep]].

  (* Prove sp_push_ofs unsigned value *)
  assert (Hsp_push_unsigned : Ptrofs.unsigned sp_push_ofs = Ptrofs.unsigned sp_ofs - 8).
  { unfold sp_push_ofs, Ptrofs.sub.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
    rewrite Ptrofs.unsigned_repr.
    - lia.
    - pose proof (Ptrofs.unsigned_range sp_ofs).
      change Ptrofs.max_unsigned with (Ptrofs.modulus - 1). lia. }

  (* --- Store: sp += nvars (nvars=0, sp stays at sp_push_ofs) --- *)
  (* With nvars=0, Oadd sp 0 = sp. Actually in CLOSUREREC the sp adjustment
     for nvars happens AFTER the env copy loop, restoring sp.
     With nvars=0 the adjustment is sp += 0 = no-op. *)

  (* --- Read sp, sp -= 1, push block, set accu --- *)
  (* After the second for-loop (0 iterations), the C code:
     1. Reads sp (which is sp_push_ofs after the push in the nvars>0 branch,
        but for nvars=0 no push happened, so sp is still sp_ofs)
     Wait -- for nvars=0, the if-branch is skipped (no push of accu onto stack).
     Then after the env copy loop (0 iterations), the C does:
       sp21 = s->sp;
       s->sp = sp21 + nvars;  // sp += 0 = no-op
     Then:
       sp20 = s->sp;
       t'5 = sp20 - 1;
       s->sp = t'5;
       *t'5 = block;
     Then:
       s->accu = block;

     So the final sp = sp_ofs - 8 = sp_push_ofs, and *sp_push_ofs = block_v.
     This pushes the closure onto the stack.
  *)

  (* Actually re-reading the C more carefully for the nvars=0 case:
     The sp field at this point still holds sp_ofs (no push happened).
     After the nvars env-copy loop (0 iters):
       t'21 = s->sp (= sp_ofs)
       s->sp = t'21 + nvars (= sp_ofs + 0*8 = sp_ofs)
     Then:
       t'20 = s->sp (= sp_ofs)
       t'5 = t'20 - 1 (= sp_ofs - 8 = sp_push_ofs)
       s->sp = t'5 (= sp_push_ofs)
       *t'5 = block
     Then:
       s->accu = block
  *)

  (* So we need: m_s1 has sp = sp_ofs.
     Store sp field to sp_ofs + 0 = sp_ofs (no change, but store still happens).
     Then sp -= 1 -> sp_push_ofs, store block at sp_push_ofs. *)

  (* Re-structure: skip the sp_push store from before and track properly *)
  (* Actually let me reconsider. In the C function for CLOSUREREC:
     1. Read nfuncs (advance pc)
     2. Read nvars (advance pc)
     3. Compute envofs = nfuncs*3 - 1 = 2
     4. Compute blksize = envofs + nvars = 2
     5. if nvars > 0: push accu, decrement sp (SKIPPED for nvars=0)
     6. Call heap_alloc(s, blksize=2, tag=247) -> block
     7. Set p = (tptr tlong)(block) + envofs  (p points past the 2 fields to where env vars go)
     8. For i=0 to nvars-1: copy stack[i] to *p, p++  (0 iterations)
     9. sp21 = s->sp; s->sp = sp21 + nvars (sp += 0 = no-op)
     10. sp20 = s->sp; t'5 = sp20 - 1; s->sp = t'5; *t'5 = block  (push block on stack)
     11. s->accu = block
     12. Set p = (tptr tlong)(block) + 0  (p = block base)
     13. t'6 = p; p = t'6 + 1  (save old p, advance p)
     14. Read code_ofs from *pc; *t'6 = pc + code_ofs  (store code ptr at block[0])
     15. t'7 = p; p = t'7 + 1  (save old p, advance p)
     16. *t'7 = (envofs << 1) | 1  (store closinfo at block[1])
     17. For i=1 to nfuncs-1: write infix header + code ptr + closinfo, push closure  (0 iterations)
     18. Advance pc by nfuncs
     19. Return 0

     Wait, I need to re-read the C body more carefully. Let me re-examine.
  *)

  (* Looking at the C body of f_instr_CLOSUREREC starting at line 4941:

     Phase A: Read nfuncs
       t'1 = s->pc; s->pc = t'1 + 1; nfuncs = *t'1;

     Phase B: Read nvars
       t'2 = s->pc; s->pc = t'2 + 1; nvars = *t'2;

     Phase C: Compute envofs and blksize
       envofs = (unsigned long)(nfuncs * 3 - 1);
       blksize = envofs + nvars;

     Phase D: if (nvars > 0) { push accu onto stack } else Sskip

     Phase E: heap_alloc(s, blksize, 247) -> t'4 -> block

     Phase F: p = (tptr tlong)(block) + envofs

     Phase G: for (i=0; i<nvars; i++) { *p = sp[i]; p++; }  (env copy)

     Phase H: sp21 = s->sp; s->sp = sp21 + nvars  (restore sp)

     Phase I: sp20 = s->sp; t'5 = sp20 - 1; s->sp = t'5; *t'5 = block  (push block)

     Phase J: s->accu = block

     Phase K: p = (tptr tlong)(block) + 0  (reset p to block base)

     Phase L: t'6 = p; p = t'6 + 1  (save/advance)
              t'17 = s->pc; t'18 = s->pc; t'19 = *((t'18) + 0);
              *t'6 = (tlong)(t'17 + t'19)  (store code ptr at block[0])

     Phase M: t'7 = p; p = t'7 + 1  (save/advance)
              *t'7 = (tlong)((envofs << 1) | 1)  (store closinfo at block[1])

     Phase N: for (i=1; i<nfuncs; i++) { ... infix headers ... }  (0 iters)

     Phase O: t'12 = s->pc; s->pc = t'12 + nfuncs  (advance pc by nfuncs)

     Phase P: return 0

  So the ORDER is: alloc, push block onto stack, set accu, THEN fill block fields.
  This is different from CLOSURE! In CLOSURE the order is alloc, fill, then update accu.
  *)

  (* Re-do the memory chain:
     m -> m1 (pc advance for nfuncs) -> m2 (pc advance for nvars) ->
     m_alloc (heap_alloc) ->
     m_sp1 (sp field: sp_ofs -> sp_push_ofs, writing sp -= 1 in struct) ->
     m_sp2 (store block at sp_push_ofs, writing *sp = block) ->
     m_accu (accu field: accu -> block_v) ->
     m_s0 (store code_ptr at block[0]) ->
     m_s1 (store closinfo at block[1]) ->
     m_pc3 (pc field: advance by nfuncs) ->
     m_final
  *)

  (* Actually, let me re-read the C body order more carefully from the Clight AST *)
  (* Looking at lines 4982-5313, after the if/heap_alloc/env-copy section:

     Ssequence                          -- Phase H-I-J block
       (Ssequence                       -- H: sp += nvars
         (Sset _t'21 (s->sp))
         (Sassign (s->sp) (t'21 + nvars)))
       (Ssequence                       -- I-J-K-L-M-N-O
         (Ssequence                     -- I: sp--, *sp = block
           (Ssequence
             (Ssequence
               (Sset _t'20 (s->sp))
               (Sset _t'5 (cast (t'20 - 1) (tptr tlong))))
             (Sassign (s->sp) t'5))
           (Sassign [deref t'5] block))
         (Ssequence                     -- J-K-L-M-N-O
           (Sassign (s->accu) block)    -- J: accu = block
           (Ssequence                   -- K-L-M-N-O
             (Sset _p (cast block (tptr tlong) + 0))  -- K: p = block+0
             (Ssequence                 -- L-M-N-O
               (Ssequence               -- L: code ptr
                 (Ssequence
                   (Sset _t'6 p)
                   (Sset _p (t'6 + 1)))
                 (Ssequence
                   (Sset _t'17 (s->pc))
                   (Ssequence
                     (Sset _t'18 (s->pc))
                     (Ssequence
                       (Sset _t'19 [deref(t'18 + 0)])
                       (Sassign [deref t'6] (tlong)(t'17 + t'19))))))
               (Ssequence               -- M-N-O
                 (Ssequence             -- M: closinfo
                   (Ssequence
                     (Sset _t'7 p)
                     (Sset _p (t'7 + 1)))
                   (Sassign [deref t'7] (envofs<<1)|1))
                 (Ssequence             -- N-O
                   (Ssequence           -- N: infix loop (0 iters)
                     (Sset _i 1)
                     (Sloop ...))
                   (Ssequence           -- O: pc advance
                     (Sset _t'12 (s->pc))
                     (Sassign (s->pc) (t'12 + nfuncs)))))))))

     So the full memory chain for nfuncs=1, nvars=0 is:

     m -> m1 (store pc_ofs_1 at sb[0]) -> m2 (store pc_ofs_2 at sb[0]) ->
     m_alloc (heap_alloc) ->
     [no sp store for sp += nvars since nvars=0, sp value unchanged] ->
     m_sp_dec (store sp_push_ofs at sb[16]) ->
     m_push (store block_v at sp_b[sp_push_ofs]) ->
     m_accu (store block_v at sb[8]) ->
     m_s0 (store code_ptr at new_b[0]) ->
     m_s1 (store closinfo at new_b[8]) ->
     m_pc3 (store pc_ofs_3 at sb[0]) ->
     m_final = m_pc3

     where pc_ofs_3 = pc_ofs_2 + nfuncs*4 = pc_ofs_2 + 4
  *)

  (* Let's restart the memory chain properly *)

  (* sp field in m_alloc *)
  assert (Hsp_load_alloc : Mem.load Mint64 m_alloc sb (Ptrofs.unsigned so + 16) =
    Some (Vptr sp_b sp_ofs)).
  { apply Hstruct_preserved. exact Hsp_load_m2. }

  (* Phase H: sp += nvars = sp += 0 = sp (no change but store happens) *)
  (* The C does: t'21 = s->sp; s->sp = t'21 + nvars
     With nvars=0: s->sp = sp_ofs + 0*8 = sp_ofs (no change) *)
  destruct (store_succeeds_sb m_alloc sb so 16 (Vptr sp_b sp_ofs) Hsb_writable_alloc Hsp_load_alloc ltac:(lia) ltac:(lia) (Vptr sp_b sp_ofs))
    as [m_sp_adj Hstore_sp_adj].

  assert (Hsb_writable_sp_adj :
    Mem.range_perm m_sp_adj sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { eapply sb_writable_after_store; eauto. }

  (* Phase I: sp20 = s->sp; t'5 = sp20 - 1; s->sp = t'5; *t'5 = block *)
  assert (Hsp_load_sp_adj : Mem.load Mint64 m_sp_adj sb (Ptrofs.unsigned so + 16) =
    Some (Vptr sp_b sp_ofs)).
  { pose proof (load_after_store_same m_alloc m_sp_adj sb (Ptrofs.unsigned so + 16) (Vptr sp_b sp_ofs) Hstore_sp_adj) as Htmp.
    rewrite load_result_vptr in Htmp. exact Htmp. }

  destruct (store_succeeds_sb m_sp_adj sb so 16 (Vptr sp_b sp_ofs) Hsb_writable_sp_adj Hsp_load_sp_adj ltac:(lia) ltac:(lia) (Vptr sp_b sp_push_ofs))
    as [m_sp_dec Hstore_sp_dec].

  assert (Hsb_writable_sp_dec :
    Mem.range_perm m_sp_dec sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { eapply sb_writable_after_store; eauto. }

  (* sp_b writable at sp_push_ofs in m_sp_dec *)
  assert (Hsp_push_perm_sp_dec : Mem.valid_access m_sp_dec Mint64 sp_b (Ptrofs.unsigned sp_push_ofs) Writable).
  { split.
    - intros ofs0 Hofs0. simpl in Hofs0.
      eapply Mem.perm_store_1. exact Hstore_sp_dec.
      eapply Mem.perm_store_1. exact Hstore_sp_adj.
      eapply Halloc_perm_pres.
      + eapply Mem.perm_valid_block.
        apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc2).
        apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc1).
        apply (Hsp_writable 0). lia.
      + apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc2).
        apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc1).
        apply Hsp_writable. simpl in Hofs0. rewrite Hsp_push_unsigned in Hofs0. lia.
    - rewrite Hsp_push_unsigned. exact Hsp_push_align. }

  destruct (Mem.valid_access_store m_sp_dec Mint64 sp_b (Ptrofs.unsigned sp_push_ofs) block_v Hsp_push_perm_sp_dec)
    as [m_push Hstore_push].

  (* Phase J: s->accu = block *)
  assert (Hsb_writable_push :
    Mem.range_perm m_push sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs0 Hofs0.
    eapply Mem.perm_store_1. exact Hstore_push.
    apply Hsb_writable_sp_dec. exact Hofs0. }

  assert (Haccu_load_push : Mem.load Mint64 m_push sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { erewrite Mem.load_store_other.
    - (* m_sp_dec -> m_push: store at sp_b, load at sb, different blocks *)
      apply (load_after_store_other m_sp_adj m_sp_dec sb (Ptrofs.unsigned so + 16)
               (Ptrofs.unsigned so + 8) (Vptr sp_b sp_push_ofs) accu_v).
      + exact Hstore_sp_dec.
      + apply (load_after_store_other m_alloc m_sp_adj sb (Ptrofs.unsigned so + 16)
                 (Ptrofs.unsigned so + 8) (Vptr sp_b sp_ofs) accu_v Hstore_sp_adj Haccu_load_alloc).
        left. lia.
      + left. lia.
    - exact Hstore_push.
    - left. intro Heq. symmetry in Heq. exact (Hsp_ne_sb Heq). }

  destruct (store_succeeds_sb m_push sb so 8 accu_v Hsb_writable_push Haccu_load_push ltac:(lia) ltac:(lia) block_v)
    as [m_accu Hstore_accu].

  assert (Hsb_writable_accu :
    Mem.range_perm m_accu sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { eapply sb_writable_after_store; eauto. }

  (* Phase L: store code_ptr at block[0] *)
  (* pc field in m_accu *)
  assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) =
    Some (Vptr cb pc_ofs_2)).
  { pose proof (load_after_store_same m1 m2 sb (Ptrofs.unsigned so + 0) (Vptr cb pc_ofs_2) Hstore_pc2) as Htmp.
    rewrite load_result_vptr in Htmp. exact Htmp. }

  assert (Hpc_load_accu : Mem.load Mint64 m_accu sb (Ptrofs.unsigned so + 0) =
    Some (Vptr cb pc_ofs_2)).
  { apply (load_after_store_other m_push m_accu sb (Ptrofs.unsigned so + 8)
             (Ptrofs.unsigned so + 0) block_v (Vptr cb pc_ofs_2) Hstore_accu).
    - erewrite Mem.load_store_other.
      + apply (load_after_store_other m_sp_adj m_sp_dec sb (Ptrofs.unsigned so + 16)
                   (Ptrofs.unsigned so + 0) (Vptr sp_b sp_push_ofs) (Vptr cb pc_ofs_2)).
          -- exact Hstore_sp_dec.
          -- apply (load_after_store_other m_alloc m_sp_adj sb (Ptrofs.unsigned so + 16)
                      (Ptrofs.unsigned so + 0) (Vptr sp_b sp_ofs) (Vptr cb pc_ofs_2) Hstore_sp_adj).
             ++ apply Hstruct_preserved. exact Hpc_load_m2.
             ++ left. lia.
          -- left. lia.
      + exact Hstore_push.
      + left. intro Heq. symmetry in Heq. exact (Hsp_ne_sb Heq).
    - left. lia. }

  (* code_ofs load in m_accu *)
  assert (Hcode_ofs_load_accu : Mem.load Mint32 m_accu cb (Ptrofs.unsigned pc_ofs_2) =
    Some (Vint (Int.repr code_ofs))).
  { rewrite Hpc_ofs_2_eq.
    erewrite Mem.load_store_other; [| exact Hstore_accu | left; exact Hcb_ne].
    erewrite Mem.load_store_other; [| exact Hstore_push | left; intro Heq; exact (Hcb_ne_sp Heq)].
    erewrite Mem.load_store_other; [| exact Hstore_sp_dec | left; exact Hcb_ne].
    erewrite Mem.load_store_other; [| exact Hstore_sp_adj | left; exact Hcb_ne].
    apply Halloc_load_pres.
    - erewrite Mem.load_store_other; [| exact Hstore_pc2 | left; exact Hcb_ne].
      erewrite Mem.load_store_other; [| exact Hstore_pc1 | left; exact Hcb_ne].
      exact Hcode_ofs.
    - intro Heq; symmetry in Heq; exact (Hnew_ne_cb Heq). }

  (* Now we can store code_ptr to block[0] in m_accu *)
  (* But we need to know the new block is storable in m_accu *)
  (* The stores to sb and sp_b don't affect new_b since new_b is fresh *)

  assert (Hcan_store_f0_accu : forall cv, exists m_f0,
    Mem.store Mint64 m_accu new_b (Ptrofs.unsigned new_ofs) cv = Some m_f0).
  { intro cv.
    assert (Hva : Mem.valid_access m_accu Mint64 new_b (Ptrofs.unsigned new_ofs) Writable).
    { destruct (Hcan_store_f0 cv) as [ms0 [Hs0 _]].
      pose proof (Mem.store_valid_access_3 _ _ _ _ _ _ Hs0) as [Hrp Ha].
      split; [| exact Ha].
      intros ofs0 Hofs0.
      eapply Mem.perm_store_1. exact Hstore_accu.
      eapply Mem.perm_store_1. exact Hstore_push.
      eapply Mem.perm_store_1. exact Hstore_sp_dec.
      eapply Mem.perm_store_1. exact Hstore_sp_adj.
      apply Hrp. exact Hofs0. }
    destruct (Mem.valid_access_store m_accu Mint64 new_b (Ptrofs.unsigned new_ofs) cv Hva) as [m_s Hm_s].
    exists m_s. exact Hm_s. }

  destruct (Hcan_store_f0_accu code_ptr_val) as [m_f0 Hstore_f0'].

  (* Store closinfo at block[1] in m_f0 *)
  assert (Hcan_store_f1_f0 : forall cv, exists m_f1,
    Mem.store Mint64 m_f0 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) cv = Some m_f1).
  { intro cv.
    destruct (Hcan_store_f0 code_ptr_val) as [ms0 [Hs0 [_ [_ Hcsf1]]]].
    destruct (Hcsf1 cv) as [ms1 [Hs1 _]].
    (* ms0 has valid_access at field 1 (from storability of Hs1) *)
    pose proof (Mem.store_valid_access_3 _ _ _ _ _ _ Hs1) as Hva_ms0.
    (* m_alloc has valid_access at field 1 (reverse through Hs0) *)
    pose proof (Mem.store_valid_access_2 _ _ _ _ _ _ Hs0 _ _ _ _ Hva_ms0) as Hva_alloc.
    (* Thread forward through all intermediate stores *)
    assert (Hva : Mem.valid_access m_f0 Mint64 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) Writable).
    { eapply Mem.store_valid_access_1. exact Hstore_f0'.
      eapply Mem.store_valid_access_1. exact Hstore_accu.
      eapply Mem.store_valid_access_1. exact Hstore_push.
      eapply Mem.store_valid_access_1. exact Hstore_sp_dec.
      eapply Mem.store_valid_access_1. exact Hstore_sp_adj.
      exact Hva_alloc. }
    destruct (Mem.valid_access_store m_f0 Mint64 new_b _ cv Hva) as [m_s Hm_s].
    exists m_s. exact Hm_s. }

  destruct (Hcan_store_f1_f0 closinfo_val) as [m_f1 Hstore_f1'].

  (* Phase O: advance pc by nfuncs=1 *)
  set (pc_ofs_3 := Ptrofs.add pc_ofs_2 (Ptrofs.repr 4)).

  assert (Hsb_writable_f1 :
    Mem.range_perm m_f1 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs0 Hofs0.
    eapply Mem.perm_store_1. exact Hstore_f1'.
    eapply Mem.perm_store_1. exact Hstore_f0'.
    apply Hsb_writable_accu. exact Hofs0. }

  assert (Hpc_load_f1 : Mem.load Mint64 m_f1 sb (Ptrofs.unsigned so + 0) =
    Some (Vptr cb pc_ofs_2)).
  { erewrite Mem.load_store_other.
    - erewrite Mem.load_store_other.
      + exact Hpc_load_accu.
      + exact Hstore_f0'.
      + left. intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq).
    - exact Hstore_f1'.
    - left. intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq). }

  destruct (store_succeeds_sb m_f1 sb so 0 (Vptr cb pc_ofs_2) Hsb_writable_f1 Hpc_load_f1 ltac:(lia) ltac:(lia) (Vptr cb pc_ofs_3))
    as [m_final Hstore_pc3].

  set (m_chain_final := m_final).

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
  (* The function temps in order of assignment for nfuncs=1, nvars=0:
     _t'1 = s.pc (old pc)
     _nfuncs = *t'1 (= 1)
     _t'2 = s.pc (= pc_ofs_1)
     _nvars = *t'2 (= 0)
     _envofs = (unsigned long)(nfuncs * 3 - 1) = 2
     _blksize = envofs + nvars = 2
     -- if nvars > 0 skipped --
     _t'4 = heap_alloc result (as tlong)
     _block = t'4
     _p = (tptr tlong)(block) + envofs
     -- for-loop i=0; i<0 skipped --
     _i = 0 after loop init
     _t'21 = s.sp
     -- sp += nvars (no-op) --
     _t'20 = s.sp
     _t'5 = sp20 - 1 = sp_push_ofs
     -- s.sp = t'5, *t'5 = block --
     -- s.accu = block --
     _p = (tptr tlong)(block) + 0
     _t'6 = p
     _p = t'6 + 1
     _t'17 = s.pc
     _t'18 = s.pc
     _t'19 = *(t'18 + 0)
     -- *t'6 = (tlong)(t'17 + t'19) --
     _t'7 = p
     _p = t'7 + 1
     -- *t'7 = closinfo --
     -- for i=1; i<1 skipped --
     _i = 1 after loop init
     _t'12 = s.pc
     -- s.pc = t'12 + nfuncs --
  *)

  set (p_init := Vptr new_b (Ptrofs.add new_ofs (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 envofs_val)))).
  set (p_base := Vptr new_b new_ofs).
  set (p_base_plus1 := Vptr new_b (Ptrofs.add new_ofs (Ptrofs.repr 8))).
  set (p_base_plus2 := Vptr new_b (Ptrofs.add new_ofs (Ptrofs.repr 16))).

  set (le_t1 := PTree.set _t'1 (Vptr cb pc_ofs) le).
  set (le_nfuncs := PTree.set _nfuncs (Vint (Int.repr 1)) le_t1).
  set (le_t2 := PTree.set _t'2 (Vptr cb pc_ofs_1) le_nfuncs).
  set (le_nvars := PTree.set _nvars (Vint (Int.repr 0)) le_t2).
  set (le_envofs := PTree.set _envofs (Vlong envofs_val) le_nvars).
  set (le_blksize := PTree.set _blksize (Vlong (Int64.repr 2)) le_envofs).
  set (le_t4 := PTree.set _t'4 block_v le_blksize).
  set (le_block := PTree.set _block block_v le_t4).
  set (le_p := PTree.set _p p_init le_block).
  set (le_i := PTree.set _i (Vint (Int.repr 0)) le_p).
  set (le_t21 := PTree.set _t'21 (Vptr sp_b sp_ofs) le_i).
  set (le_t20 := PTree.set _t'20 (Vptr sp_b sp_ofs) le_t21).
  set (le_t5 := PTree.set _t'5 (Vptr sp_b sp_push_ofs) le_t20).
  set (le_p2 := PTree.set _p p_base le_t5).
  set (le_t6 := PTree.set _t'6 p_base le_p2).
  set (le_p3 := PTree.set _p p_base_plus1 le_t6).
  set (le_t17 := PTree.set _t'17 (Vptr cb pc_ofs_2) le_p3).
  set (le_t18 := PTree.set _t'18 (Vptr cb pc_ofs_2) le_t17).
  set (le_t19 := PTree.set _t'19 (Vint (Int.repr code_ofs)) le_t18).
  set (le_t7 := PTree.set _t'7 p_base_plus1 le_t19).
  set (le_p4 := PTree.set _p p_base_plus2 le_t7).
  (* With 0 loop iterations, _envofs is not re-set. *)
  set (le_i2 := PTree.set _i (Vint (Int.repr 1)) le_p4).
  eexists. exists m_final.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ============================================================== *)
  (* Part 1: exec_stmt derivation                                    *)
  (* ============================================================== *)
  {
    (* We need to match the fn_body of f_instr_CLOSUREREC.
       Due to extreme complexity, we use the eval_stmt_to_exec approach
       for leaf statements and build up with exec_Sseq_1 / exec_Sseq_2. *)

    (* The fn_body is too large to `change` directly. Instead we prove
       exec of the fn_body by building from the inside out.
       We'll construct exec_stmt for each phase and chain them. *)

    (* We use a single large eval_stmt_to_exec call.
       But the body is too big for this. Let's instead prove each
       sub-statement individually and chain them. *)

    (* Phase A: Read nfuncs *)
    (* t'1 = s->pc *)
    assert (Hexec_set_t1 : exec_stmt function_entry1 clight_ge e le m
        (Sset _t'1
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                   (Tstruct _interp_state noattr)) _pc (tptr tint)))
        E0 le_t1 m Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load; eval_cbn.
      reflexivity. }

    (* s->pc = t'1 + 1 *)
    assert (Hexec_store_pc1 : exec_stmt function_entry1 clight_ge e le_t1 m
        (Sassign
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                   (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'1 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint)))
        E0 le_t1 m1 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le_t1.
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_pc_1 cb pc_ofs m); eval_cbn.
      rewrite (sem_cast_ptr_tint_to_ptr_tint cb pc_ofs_1); eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      fold pc_ofs_1. rewrite Hstore_pc1; eval_cbn.
      reflexivity. }

    (* nfuncs = *t'1 *)
    assert (Hexec_read_nfuncs : exec_stmt function_entry1 clight_ge e le_t1 m1
        (Sset _nfuncs (Ederef (Etempvar _t'1 (tptr tint)) tint))
        E0 le_nfuncs m1 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le_t1.
      rewrite PTree.gss; eval_cbn.
      rewrite Hcode_nfuncs_m1; eval_cbn.
      reflexivity. }

    (* Split fn_body = (body_main ; return 0) using evar for the placeholder. *)
    evar (rest_body : statement).
    assert (Hfn_body_split : fn_body f_instr_CLOSUREREC =
      Ssequence
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
            (Sset _nfuncs (Ederef (Etempvar _t'1 (tptr tint)) tint)))
          rest_body)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))).
    { subst rest_body. reflexivity. }
    rewrite Hfn_body_split. clear Hfn_body_split.
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    2:{ apply (eval_stmt_to_exec clight_ge 10). reflexivity. }

    (* Build Phase A top-level sequence *)
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { (* Phase A: three statements chained *)
      replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      - replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto.
      - exact Hexec_read_nfuncs. }

    (* Phase B: Read nvars *)
    (* t'2 = s->pc (= pc_ofs_1) *)
    assert (Hexec_set_t2 : exec_stmt function_entry1 clight_ge e le_nfuncs m1
        (Sset _t'2
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                   (Tstruct _interp_state noattr)) _pc (tptr tint)))
        E0 le_t2 m1 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le_nfuncs, le_t1.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load_m1; eval_cbn.
      reflexivity. }

    (* s->pc = t'2 + 1 *)
    assert (Hexec_store_pc2 : exec_stmt function_entry1 clight_ge e le_t2 m1
        (Sassign
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                   (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint)))
        E0 le_t2 m2 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le_t2, le_nfuncs, le_t1.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_pc_1 cb pc_ofs_1 m1); eval_cbn.
      rewrite (sem_cast_ptr_tint_to_ptr_tint cb pc_ofs_2); eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      fold pc_ofs_2. rewrite Hstore_pc2; eval_cbn.
      reflexivity. }

    (* nvars = *t'2 *)
    assert (Hexec_read_nvars : exec_stmt function_entry1 clight_ge e le_t2 m2
        (Sset _nvars (Ederef (Etempvar _t'2 (tptr tint)) tint))
        E0 le_nvars m2 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le_t2.
      rewrite PTree.gss; eval_cbn.
      rewrite Hcode_nvars_m2; eval_cbn.
      reflexivity. }

    (* Phase B combined *)
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      - replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1; eauto.
      - exact Hexec_read_nvars. }

    (* Phase C: Compute envofs and blksize *)
    (* envofs = (tulong)(nfuncs * 3 - 1) *)
    assert (Hexec_set_envofs : exec_stmt function_entry1 clight_ge e le_nvars m2
        (Sset _envofs
          (Ecast
            (Ebinop Osub
              (Ebinop Omul (Etempvar _nfuncs tint)
                (Econst_int (Int.repr 3) tint) tint)
              (Econst_int (Int.repr 1) tint) tint) tulong))
        E0 le_envofs m2 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le_nvars, le_t2, le_nfuncs.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite sem_mul_int_int; eval_cbn.
      rewrite sem_sub_int_int; eval_cbn.
      rewrite sem_cast_int_to_tulong; eval_cbn.
      reflexivity. }

    (* blksize = envofs + nvars *)
    assert (Hexec_set_blksize : exec_stmt function_entry1 clight_ge e le_envofs m2
        (Sset _blksize
          (Ebinop Oadd (Etempvar _envofs tulong) (Etempvar _nvars tint) tulong))
        E0 le_blksize m2 Out_normal).
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le_envofs. rewrite PTree.gss; eval_cbn.
      unfold le_envofs, le_nvars.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite sem_add_ulong_int; eval_cbn.
      reflexivity. }

    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { exact Hexec_set_envofs. }

    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { exact Hexec_set_blksize. }

    (* Phase D: if (nvars > 0) -- false, take Sskip *)
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { eapply exec_Sifthenelse with (b := false).
      - eapply eval_Ebinop.
        + eapply eval_Etempvar.
          unfold le_blksize, le_envofs, le_nvars.
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gss. reflexivity.
        + eapply eval_Econst_int.
        + apply sem_cmp_gt_int_0.
      - rewrite int_lt_0_0. simpl. reflexivity.
      - constructor. }

    (* Phase E: heap_alloc(s, blksize=2, tag=247) *)
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { (* Scall heap_alloc; Sset _block *)
      replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      - eapply exec_Scall with
          (tyargs := (tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
          (tyres := tlong)
          (cconv := cc_default)
          (vf := Vptr b_ha Ptrofs.zero)
          (vargs := Vptr sb so :: Vlong (Int64.repr 2) :: Vlong (Int64.repr 247) :: nil)
          (f := heap_alloc_fundef)
          (vres := Vptr new_b new_ofs).
        + reflexivity.
        + eapply eval_Elvalue.
          * eapply eval_Evar_global.
            -- exact He_heap_alloc.
            -- exact Hfind_symbol.
          * apply deref_loc_reference. simpl. reflexivity.
        + econstructor.
          * econstructor.
            unfold le_blksize, le_envofs, le_nvars, le_t2, le_nfuncs, le_t1.
            repeat (rewrite PTree.gso by (compute; congruence)).
            exact Hle_s.
          * simpl. reflexivity.
          * econstructor.
            -- econstructor.
               unfold le_blksize. rewrite PTree.gss. reflexivity.
            -- simpl. rewrite sem_cast_ulong_to_tlong. reflexivity.
            -- econstructor.
               ++ econstructor.
               ++ simpl. reflexivity.
               ++ constructor.
        + exact Hfind_funct.
        + reflexivity.
        + eapply eval_funcall_external. exact Hext_call.
      - (* Sset _block *)
        apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le_t4. rewrite PTree.gss; eval_cbn.
        reflexivity. }

    (* Phase F: p = (tptr tlong)(block) + envofs *)
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le_block, le_t4.
      rewrite PTree.gss; eval_cbn.
      fold block_v.
      unfold block_v at 1; rewrite sem_cast_vptr_tlong_to_ptr_tlong; eval_cbn; fold block_v.
      unfold le_block, le_t4, le_blksize, le_envofs.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      unfold block_v.
      rewrite sem_add_ptr_tlong_ulong; eval_cbn.
      (* sem_cast: Vptr to (tptr tlong) *)
      unfold sem_cast; simpl classify_cast; eval_cbn.
      reflexivity. }

    (* Phase G: for-loop, 0 iterations (nvars=0) *)
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      - (* Sset _i 0 *)
        apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn. reflexivity.
      - (* Sloop: condition 0 < 0 is false, break immediately *)
        eapply exec_Sloop_stop1.
        + replace E0 with (E0 ** E0) by reflexivity.
          eapply exec_Sseq_2.
          * eapply exec_Sifthenelse with (b := false).
            -- eapply eval_Ebinop.
               ++ eapply eval_Etempvar. unfold le_i. rewrite PTree.gss. reflexivity.
               ++ eapply eval_Etempvar.
                  unfold le_i, le_p, le_block, le_t4, le_blksize, le_envofs, le_nvars.
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gss. reflexivity.
               ++ apply sem_cmp_lt_int.
            -- rewrite int_lt_0_0. simpl. reflexivity.
            -- constructor.
          * discriminate.
        + constructor. }

    (* Phase H: sp += nvars = sp += 0 *)
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      - (* Sset _t'21 (s->sp) *)
        apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le_i, le_p, le_block, le_t4, le_blksize, le_envofs, le_nvars, le_t2, le_nfuncs, le_t1.
        repeat (rewrite PTree.gso by (compute; congruence)).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hsp_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
        rewrite Hsp_load_alloc; eval_cbn.
        reflexivity.
      - (* Sassign s->sp (t'21 + nvars) *)
        apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le_t21, le_i, le_p, le_block, le_t4, le_blksize, le_envofs, le_nvars, le_t2, le_nfuncs, le_t1.
        repeat (rewrite PTree.gso by (compute; congruence)).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hsp_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite PTree.gss; eval_cbn.
        unfold le_t21, le_i, le_p, le_block, le_t4, le_blksize, le_envofs, le_nvars.
        repeat (rewrite PTree.gso by (compute; congruence)).
        rewrite PTree.gss; eval_cbn.
        rewrite sem_add_ptr_tlong_int; eval_cbn.
        change (Ptrofs.add sp_ofs (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr 0))))
          with (Ptrofs.add sp_ofs Ptrofs.zero).
        rewrite Ptrofs.add_zero.
        unfold sem_cast at 1; simpl classify_cast; eval_cbn.
        rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
        rewrite Hstore_sp_adj; eval_cbn.
        reflexivity. }

    (* Phase I: sp--, *sp = block *)
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { (* Ssequence (Ssequence (Ssequence (Sset _t'20 ...) (Sset _t'5 ...)) (Sassign s->sp ...)) (Sassign *t'5 block) *)
      replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      { (* sp20 = s->sp; t'5 = sp20 - 1; s->sp = t'5 *)
        replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1.
        { replace E0 with (E0 ** E0) by reflexivity.
          eapply exec_Sseq_1.
          - (* Sset _t'20 (s->sp) *)
            apply (eval_stmt_to_exec clight_ge 10).
            eval_cbn.
            unfold le_t21, le_i, le_p, le_block, le_t4, le_blksize, le_envofs, le_nvars, le_t2, le_nfuncs, le_t1.
            repeat (rewrite PTree.gso by (compute; congruence)).
            rewrite Hle_s; eval_cbn.
            rewrite Hco; eval_cbn.
            rewrite Hsp_offset; eval_cbn.
            rewrite Mptr_Mint64; eval_cbn.
            rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
            rewrite Hsp_load_sp_adj; eval_cbn.
            reflexivity.
          - (* Sset _t'5 (cast (t'20 - 1) (tptr tlong)) *)
            apply (eval_stmt_to_exec clight_ge 10).
            eval_cbn.
            unfold le_t20. rewrite PTree.gss; eval_cbn.
            rewrite sem_sub_sp_1; eval_cbn.
            unfold sem_cast; simpl classify_cast; eval_cbn.
            reflexivity. }
        (* Sassign s->sp t'5 *)
        apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le_t5, le_t20, le_t21, le_i, le_p, le_block, le_t4, le_blksize, le_envofs, le_nvars, le_t2, le_nfuncs, le_t1.
        repeat (rewrite PTree.gso by (compute; congruence)).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hsp_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite PTree.gss; eval_cbn.
        rewrite sem_cast_ptr_to_ptr.
        eval_cbn.
        fold sp_push_ofs.
        rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
        rewrite Hstore_sp_dec.
        eval_cbn.
        reflexivity. }
      (* Sassign *t'5 block *)
      eapply exec_Sassign with (v := block_v).
      - eapply eval_Ederef.
        eapply eval_Etempvar.
        unfold le_t5, le_t20, le_t21, le_i, le_p, le_block, le_t4.
        repeat (rewrite PTree.gso by (compute; congruence)).
        rewrite PTree.gss. reflexivity.
      - eapply eval_Etempvar.
        unfold le_t5, le_t20, le_t21, le_i, le_p, le_block, le_t4.
        repeat (rewrite PTree.gso by (compute; congruence)).
        rewrite PTree.gss. reflexivity.
      - unfold block_v. apply (sem_cast_long_vptr new_b new_ofs).
      - eapply assign_loc_value.
        + reflexivity.
        + simpl Mem.storev. fold sp_push_ofs.
          exact Hstore_push. }

    (* Phase J: s->accu = block *)
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { eapply exec_Sassign with (v := block_v).
      - (* LHS: s->accu as lvalue *)
        eapply eval_Efield_struct.
        + eapply eval_Elvalue.
          * eapply eval_Ederef.
            eapply eval_Etempvar.
            unfold le_t5, le_t20, le_t21, le_i, le_p, le_block, le_t4, le_blksize, le_envofs, le_nvars, le_t2, le_nfuncs, le_t1.
            repeat (rewrite PTree.gso by (compute; congruence)).
            exact Hle_s.
          * apply deref_loc_copy. simpl. reflexivity.
        + simpl. reflexivity.
        + exact Hco.
        + exact Haccu_offset.
      - (* RHS: block *)
        eapply eval_Etempvar.
        unfold le_t5, le_t20, le_t21, le_i, le_p, le_block.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gss. reflexivity.
      - (* sem_cast *)
        unfold block_v. apply (sem_cast_long_vptr new_b new_ofs).
      - eapply assign_loc_value.
        + reflexivity.
        + simpl Mem.storev.
          rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
          exact Hstore_accu. }

    (* Phase K: p = (tptr tlong)(block) + 0 *)
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.
      unfold le_t5, le_t20, le_t21, le_i, le_p, le_block.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      fold block_v.
      unfold block_v at 1; rewrite sem_cast_vptr_tlong_to_ptr_tlong; eval_cbn; fold block_v.
      unfold block_v.
      rewrite sem_add_ptr_tlong_int; eval_cbn.
      unfold sem_cast; simpl classify_cast; eval_cbn.
      change (Ptrofs.add new_ofs (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr 0))))
        with (Ptrofs.add new_ofs Ptrofs.zero).
      rewrite Ptrofs.add_zero.
      reflexivity. }

    (* Phase L: t'6 = p; p = t'6 + 1; read code_ofs; store code ptr at block[0] *)
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      { (* t'6 = p; p = t'6 + 1 *)
        replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1.
        - (* Sset _t'6 p *)
          apply (eval_stmt_to_exec clight_ge 10).
          eval_cbn.
          unfold le_p2. rewrite PTree.gss; eval_cbn.
          reflexivity.
        - (* Sset _p (t'6 + 1) *)
          apply (eval_stmt_to_exec clight_ge 10).
          eval_cbn.
          unfold le_t6. rewrite PTree.gss; eval_cbn.
          unfold p_base.
          rewrite sem_add_ptr_tlong_int; eval_cbn.
          unfold sem_cast; simpl classify_cast; eval_cbn.
          reflexivity. }
      { (* t'17 = s->pc; t'18 = s->pc; t'19 = *(t'18 + 0); *t'6 = (tlong)(t'17 + t'19) *)
        replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1.
        { (* Sset _t'17 (s->pc) *)
          apply (eval_stmt_to_exec clight_ge 10).
          eval_cbn.
          unfold le_p3, le_t6, le_p2, le_t5, le_t20, le_t21, le_i, le_p, le_block, le_t4, le_blksize, le_envofs, le_nvars, le_t2, le_nfuncs, le_t1.
          repeat (rewrite PTree.gso by (compute; congruence)).
          rewrite Hle_s; eval_cbn.
          rewrite Hco; eval_cbn.
          rewrite Hpc_offset; eval_cbn.
          rewrite Mptr_Mint64; eval_cbn.
          rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
          rewrite Hpc_load_accu; eval_cbn.
          reflexivity. }
        replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1.
        { (* Sset _t'18 (s->pc) *)
          apply (eval_stmt_to_exec clight_ge 10).
          eval_cbn.
          unfold le_t17, le_p3, le_t6, le_p2, le_t5, le_t20, le_t21, le_i, le_p, le_block, le_t4, le_blksize, le_envofs, le_nvars, le_t2, le_nfuncs, le_t1.
          repeat (rewrite PTree.gso by (compute; congruence)).
          rewrite Hle_s; eval_cbn.
          rewrite Hco; eval_cbn.
          rewrite Hpc_offset; eval_cbn.
          rewrite Mptr_Mint64; eval_cbn.
          rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
          rewrite Hpc_load_accu; eval_cbn.
          reflexivity. }
        replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1.
        { (* Sset _t'19 deref(t'18 + 0) *)
          apply (eval_stmt_to_exec clight_ge 10).
          eval_cbn.
          unfold le_t18. rewrite PTree.gss; eval_cbn.
          rewrite sem_add_ptr_tint_int; eval_cbn.
          change (Ptrofs.add pc_ofs_2 (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr 0))))
            with (Ptrofs.add pc_ofs_2 Ptrofs.zero).
          rewrite Ptrofs.add_zero.
          rewrite Hcode_ofs_load_accu; eval_cbn.
          reflexivity. }
        { (* Sassign *t'6 (tlong)(t'17 + t'19) *)
          eapply exec_Sassign with (v := code_ptr_val).
          - eapply eval_Ederef.
            eapply eval_Etempvar.
            unfold le_t19, le_t18, le_t17, le_p3, le_t6.
            rewrite PTree.gso by (compute; congruence).
            rewrite PTree.gso by (compute; congruence).
            rewrite PTree.gso by (compute; congruence).
            rewrite PTree.gso by (compute; congruence).
            rewrite PTree.gss. reflexivity.
          - eapply eval_Ecast.
            + eapply eval_Ebinop.
              * eapply eval_Etempvar.
                unfold le_t19, le_t18, le_t17.
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gss. reflexivity.
              * eapply eval_Etempvar.
                unfold le_t19. rewrite PTree.gss. reflexivity.
              * apply sem_add_ptr_tint_int.
            + apply sem_cast_vptr_ptr_tint_to_tlong.
          - unfold sem_cast. simpl classify_cast. rewrite ptr64_true. reflexivity.
          - eapply assign_loc_value.
            + reflexivity.
            + unfold Mem.storev. unfold p_base.
              exact Hstore_f0'. } } }

    (* Phase M: t'7 = p; p = t'7 + 1; *t'7 = closinfo *)
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      { (* t'7 = p; p = t'7 + 1 *)
        replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1.
        - (* Sset _t'7 p *)
          apply (eval_stmt_to_exec clight_ge 10).
          eval_cbn.
          unfold le_t19, le_t18, le_t17, le_p3.
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gss; eval_cbn.
          reflexivity.
        - (* Sset _p (t'7 + 1) *)
          apply (eval_stmt_to_exec clight_ge 10).
          eval_cbn.
          unfold le_t7. rewrite PTree.gss; eval_cbn.
          unfold p_base_plus1.
          rewrite sem_add_ptr_tlong_int; eval_cbn.
          unfold sem_cast; simpl classify_cast; eval_cbn.
          reflexivity. }
      { (* Sassign *t'7 ((envofs << 1) | 1) *)
        eapply exec_Sassign with (v := closinfo_val).
        - eapply eval_Ederef.
          eapply eval_Etempvar.
          unfold le_p4, le_t7.
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gss. reflexivity.
        - eapply eval_Ebinop.
          + eapply eval_Ecast.
            * eapply eval_Ebinop.
              -- eapply eval_Etempvar.
                 unfold le_p4, le_t7, le_t19, le_t18, le_t17, le_p3, le_t6, le_p2, le_t5, le_t20, le_t21, le_i, le_p, le_block, le_t4, le_blksize, le_envofs.
                 repeat (rewrite PTree.gso by (compute; congruence)).
                 rewrite PTree.gss. reflexivity.
              -- eapply eval_Econst_int.
              -- apply (sem_shl_ulong_int envofs_val (Int.repr 1) m_f0).
                 reflexivity.
            * apply sem_cast_ulong_to_tlong.
          + eapply eval_Econst_int.
          + apply sem_or_long_int.
        - (* Cast closinfo to tlong *)
          unfold sem_cast. simpl classify_cast. rewrite ptr64_true. reflexivity.
        - eapply assign_loc_value.
          + reflexivity.
          + unfold Mem.storev.
            unfold p_base_plus1.
            exact Hstore_f1'. } }

    (* Phase N: for-loop i=1; i<nfuncs=1 (0 iterations) *)
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      - (* Sset _i 1 *)
        apply exec_Sset. eapply eval_Econst_int.
      - (* Sloop: condition 1 < 1 is false, break immediately *)
        eapply exec_Sloop_stop1.
        + replace E0 with (E0 ** E0) by reflexivity.
          eapply exec_Sseq_2.
          * eapply exec_Sifthenelse with (b := false).
            -- eapply eval_Ebinop.
               ++ eapply eval_Etempvar. unfold le_i2.
                  rewrite PTree.gss. reflexivity.
               ++ eapply eval_Etempvar.
                  unfold le_i2, le_p4, le_t7, le_t19, le_t18, le_t17, le_p3, le_t6, le_p2, le_t5, le_t20, le_t21, le_i, le_p, le_block, le_t4, le_blksize, le_envofs, le_nvars, le_t2, le_nfuncs.
                  repeat (rewrite PTree.gso by (compute; congruence)).
                  rewrite PTree.gss. reflexivity.
               ++ apply sem_cmp_lt_int.
            -- rewrite int_lt_1_1. simpl. reflexivity.
            -- constructor.
          * discriminate.
        + constructor. }

    (* Phase O: t'12 = s->pc; s->pc = t'12 + nfuncs *)
    replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    { (* Sset _t'12 (s->pc) *)
      apply exec_Sset.
      eapply eval_Elvalue.
      - eapply eval_Efield_struct.
        + eapply eval_Elvalue.
          * eapply eval_Ederef.
            eapply eval_Etempvar.
            unfold le_i2, le_p4, le_t7, le_t19, le_t18, le_t17, le_p3, le_t6, le_p2, le_t5, le_t20, le_t21, le_i, le_p, le_block, le_t4, le_blksize, le_envofs, le_nvars, le_t2, le_nfuncs, le_t1.
            repeat (rewrite PTree.gso by (compute; congruence)).
            exact Hle_s.
          * apply deref_loc_copy. simpl. reflexivity.
        + simpl. reflexivity.
        + exact Hco.
        + exact Hpc_offset.
      - apply deref_loc_value with (chunk := Mptr).
        + simpl. reflexivity.
        + simpl. rewrite Mptr_Mint64.
          rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
          exact Hpc_load_f1. }

    (* Sassign s->pc (t'12 + nfuncs) *)
    eapply exec_Sassign with (v := Vptr cb pc_ofs_3).
    - (* LHS: s->pc as lvalue *)
      eapply eval_Efield_struct.
      + eapply eval_Elvalue.
        * eapply eval_Ederef.
          eapply eval_Etempvar.
          repeat (rewrite PTree.gso by (compute; congruence)).
          exact Hle_s.
        * apply deref_loc_copy. simpl. reflexivity.
      + simpl. reflexivity.
      + exact Hco.
      + exact Hpc_offset.
    - (* RHS: t'12 + nfuncs *)
      eapply eval_Ebinop.
      + eapply eval_Etempvar.
        rewrite PTree.gss. reflexivity.
      + eapply eval_Etempvar.
        repeat (rewrite PTree.gso by (compute; congruence)).
        rewrite PTree.gss. reflexivity.
      + rewrite sem_add_ptr_tint_int.
        change (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr 1)))
          with (Ptrofs.repr 4).
        fold pc_ofs_3. reflexivity.
    - (* sem_cast *)
      apply sem_cast_ptr_tint_to_ptr_tint.
    - (* assign_loc *)
      eapply assign_loc_value.
      + reflexivity.
      + simpl Mem.storev. rewrite Mptr_Mint64.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        exact Hstore_pc3.
  }

  (* ============================================================== *)
  (* Part 2: abs_rel for post-state                                  *)
  (* ============================================================== *)
  {
    set (new_co := Ptrofs.add (Ptrofs.add (Ptrofs.add co (Ptrofs.repr sizeof_code_t)) (Ptrofs.repr sizeof_code_t)) (Ptrofs.repr sizeof_code_t)).
    set (ard' := mk_abs_rel
      sb so hm'
      cb new_co
      gb go0
      (ar_stack_block ard) (ar_stack_base_ofs ard)
      (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
    exists ard'.

    set (uso := Ptrofs.unsigned so) in *.

    (* pc field in m_final *)
    assert (Hpc_load_final : Mem.load Mint64 m_final sb (uso + 0) =
      Some (Vptr cb pc_ofs_3)).
    { pose proof (load_after_store_same m_f1 m_final sb (uso + 0) (Vptr cb pc_ofs_3) Hstore_pc3) as Htmp.
      rewrite load_result_vptr in Htmp. exact Htmp. }

    (* accu field in m_final *)
    assert (Haccu_load_final : Mem.load Mint64 m_final sb (uso + 8) = Some block_v).
    { apply (load_after_store_other m_f1 m_final sb (uso + 0) (uso + 8)
               (Vptr cb pc_ofs_3) block_v Hstore_pc3).
      - erewrite Mem.load_store_other.
        + erewrite Mem.load_store_other.
          * pose proof (load_after_store_same m_push m_accu sb (uso + 8) block_v Hstore_accu) as Htmp.
            unfold block_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp.
          * exact Hstore_f0'.
          * left. intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq).
        + exact Hstore_f1'.
        + left. intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq).
      - right. lia. }

    (* Helper: struct fields at offsets >= 24 survive through all stores from m *)
    assert (Hfield_survive : forall field_ofs v,
      field_ofs >= 24 ->
      Mem.load Mint64 m sb (uso + field_ofs) = Some v ->
      Mem.load Mint64 m_final sb (uso + field_ofs) = Some v).
    { intros fo v Hfo Hload.
      (* m -> m1: store at uso+0 *)
      assert (H1 : Mem.load Mint64 m1 sb (uso + fo) = Some v).
      { apply (load_after_store_other m m1 sb (uso + 0) (uso + fo)
                 (Vptr cb pc_ofs_1) v Hstore_pc1 Hload). right. lia. }
      (* m1 -> m2: store at uso+0 *)
      assert (H2 : Mem.load Mint64 m2 sb (uso + fo) = Some v).
      { apply (load_after_store_other m1 m2 sb (uso + 0) (uso + fo)
                 (Vptr cb pc_ofs_2) v Hstore_pc2 H1). right. lia. }
      (* m2 -> m_alloc *)
      assert (H3 : Mem.load Mint64 m_alloc sb (uso + fo) = Some v).
      { apply Hstruct_preserved. exact H2. }
      (* m_alloc -> m_sp_adj: store at uso+16, fo >= 24 so no overlap *)
      assert (H4 : Mem.load Mint64 m_sp_adj sb (uso + fo) = Some v).
      { apply (load_after_store_other m_alloc m_sp_adj sb (uso + 16) (uso + fo)
                 (Vptr sp_b sp_ofs) v Hstore_sp_adj H3). right. lia. }
      (* m_sp_adj -> m_sp_dec: store at uso+16, fo >= 24 so no overlap *)
      assert (H5 : Mem.load Mint64 m_sp_dec sb (uso + fo) = Some v).
      { apply (load_after_store_other m_sp_adj m_sp_dec sb (uso + 16) (uso + fo)
                 (Vptr sp_b sp_push_ofs) v Hstore_sp_dec H4). right. lia. }
      (* m_sp_dec -> m_push: store at sp_b *)
      assert (H6 : Mem.load Mint64 m_push sb (uso + fo) = Some v).
      { erewrite Mem.load_store_other.
        - exact H5.
        - exact Hstore_push.
        - left. intro Heq; symmetry in Heq; exact (Hsp_ne_sb Heq). }
      (* m_push -> m_accu: store at uso+8 *)
      assert (H7 : Mem.load Mint64 m_accu sb (uso + fo) = Some v).
      { apply (load_after_store_other m_push m_accu sb (uso + 8) (uso + fo)
                 block_v v Hstore_accu H6). right. lia. }
      (* m_accu -> m_f0: store at new_b *)
      assert (H8 : Mem.load Mint64 m_f0 sb (uso + fo) = Some v).
      { erewrite Mem.load_store_other.
        - exact H7.
        - exact Hstore_f0'.
        - left. intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq). }
      (* m_f0 -> m_f1: store at new_b *)
      assert (H9 : Mem.load Mint64 m_f1 sb (uso + fo) = Some v).
      { erewrite Mem.load_store_other.
        - exact H8.
        - exact Hstore_f1'.
        - left. intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq). }
      (* m_f1 -> m_final: store at uso+0 *)
      apply (load_after_store_other m_f1 m_final sb (uso + 0) (uso + fo)
               (Vptr cb pc_ofs_3) v Hstore_pc3 H9). right. lia. }

    (* sp field in m_final: sp was decremented to sp_push_ofs *)
    assert (Hsp_load_final : Mem.load Mint64 m_final sb (uso + 16) =
      Some (Vptr sp_b sp_push_ofs)).
    { apply (load_after_store_other m_f1 m_final sb (uso + 0) (uso + 16)
               (Vptr cb pc_ofs_3) (Vptr sp_b sp_push_ofs) Hstore_pc3).
      - erewrite Mem.load_store_other.
        + erewrite Mem.load_store_other.
          * erewrite Mem.load_store_other.
            -- erewrite Mem.load_store_other.
               ++ pose proof (load_after_store_same m_sp_adj m_sp_dec sb (uso + 16) (Vptr sp_b sp_push_ofs) Hstore_sp_dec) as Htmp.
                  rewrite load_result_vptr in Htmp. exact Htmp.
               ++ exact Hstore_push.
               ++ left. intro Heq; symmetry in Heq; exact (Hsp_ne_sb Heq).
            -- exact Hstore_accu.
            -- right. right. simpl. lia.
          * exact Hstore_f0'.
          * left. intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq).
        + exact Hstore_f1'.
        + left. intro Heq; symmetry in Heq; exact (Hnew_ne_sb Heq).
      - right. lia. }

    assert (Henv_load_final : Mem.load Mint64 m_final sb (uso + 24) = Some env_v).
    { apply Hfield_survive; [lia | exact Henv_load]. }

    assert (Hextra_load_final : Mem.load Mint64 m_final sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply Hfield_survive; [lia | exact Hextra_load]. }

    assert (Hgd_load_final : Mem.load Mint64 m_final sb (uso + 40) = Some (Vptr gb go0)).
    { apply Hfield_survive; [lia | exact Hgd_load]. }

    assert (Hts_load_final : Mem.load Mint64 m_final sb (uso + 48) = Some ts_ptr).
    { apply Hfield_survive; [lia | exact Hts_load]. }

    (* Stack repr: new stack = Val_closure addr 0 :: stack s *)
    (* The stack at sp_push_ofs starts with block_v (the closure), then the old stack *)
    assert (Hsp_ne_new : sp_b <> new_b).
    { intro Heq; symmetry in Heq; exact (Hnew_ne_sp Heq). }
    assert (Hgb_ne_new : gb <> new_b).
    { intro Heq; symmetry in Heq; exact (Hnew_ne_gb Heq). }

    (* block_v is loadable at sp_push_ofs in m_final *)
    assert (Hblock_load_final : Mem.load Mint64 m_final sp_b (Ptrofs.unsigned sp_push_ofs) = Some block_v).
    { erewrite Mem.load_store_other.
      - erewrite Mem.load_store_other.
        + erewrite Mem.load_store_other.
          * erewrite Mem.load_store_other.
            -- pose proof (load_after_store_same m_sp_dec m_push sp_b (Ptrofs.unsigned sp_push_ofs) block_v Hstore_push) as Htmp.
               unfold block_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp.
            -- exact Hstore_accu.
            -- left. exact Hsp_ne_sb.
          * exact Hstore_f0'.
          * left. exact Hsp_ne_new.
        + exact Hstore_f1'.
        + left. exact Hsp_ne_new.
      - exact Hstore_pc3.
      - left. exact Hsp_ne_sb. }

    (* Old stack preserved in m_final *)
    assert (Hstack_final : stack_repr hm cb co m_final (Machine.stack s) sp_b sp_ofs).
    { (* Thread stack through all stores *)
      assert (Hs1 : stack_repr hm cb co m1 (Machine.stack s) sp_b sp_ofs).
      { eapply (stack_repr_store_other_block hm cb co); eauto. }
      assert (Hs2 : stack_repr hm cb co m2 (Machine.stack s) sp_b sp_ofs).
      { eapply (stack_repr_store_other_block hm cb co); eauto. }
      assert (Hs_alloc : stack_repr hm cb co m_alloc (Machine.stack s) sp_b sp_ofs).
      { clear -Hs2 Halloc_load_pres Hsp_ne_new.
        induction Hs2 as [| v vs sp_b0 sp_ofs0 cv Hld Hvr Htl IH].
        - constructor.
        - econstructor.
          + apply Halloc_load_pres. exact Hld. exact Hsp_ne_new.
          + exact Hvr.
          + apply IH. exact Hsp_ne_new. }
      assert (Hs_spadj : stack_repr hm cb co m_sp_adj (Machine.stack s) sp_b sp_ofs).
      { eapply (stack_repr_store_other_block hm cb co); eauto. }
      assert (Hs_spdec : stack_repr hm cb co m_sp_dec (Machine.stack s) sp_b sp_ofs).
      { eapply (stack_repr_store_other_block hm cb co); eauto. }
      (* m_sp_dec -> m_push: store at sp_b[sp_push_ofs] which is BELOW sp_ofs *)
      assert (Hs_push : stack_repr hm cb co m_push (Machine.stack s) sp_b sp_ofs).
      { eapply stack_repr_store_same_block_lower.
        - exact Hs_spdec.
        - exact Hstore_push.
        - rewrite Hsp_push_unsigned. lia.
        - exact Hsp_rep. }
      assert (Hs_accu : stack_repr hm cb co m_accu (Machine.stack s) sp_b sp_ofs).
      { eapply (stack_repr_store_other_block hm cb co); eauto. }
      assert (Hs_f0 : stack_repr hm cb co m_f0 (Machine.stack s) sp_b sp_ofs).
      { clear -Hs_accu Hstore_f0' Hsp_ne_new.
        induction Hs_accu as [| v vs sp_b0 sp_ofs0 cv Hld Hvr Htl IH].
        - constructor.
        - econstructor.
          + erewrite Mem.load_store_other.
            * exact Hld.
            * exact Hstore_f0'.
            * left. exact Hsp_ne_new.
          + exact Hvr.
          + apply IH. exact Hsp_ne_new. }
      assert (Hs_f1 : stack_repr hm cb co m_f1 (Machine.stack s) sp_b sp_ofs).
      { clear -Hs_f0 Hstore_f1' Hsp_ne_new.
        induction Hs_f0 as [| v vs sp_b0 sp_ofs0 cv Hld Hvr Htl IH].
        - constructor.
        - econstructor.
          + erewrite Mem.load_store_other.
            * exact Hld.
            * exact Hstore_f1'.
            * left. exact Hsp_ne_new.
          + exact Hvr.
          + apply IH. exact Hsp_ne_new. }
      eapply (stack_repr_store_other_block hm cb co); eauto. }

    (* New stack: Val_closure addr 0 :: stack s at sp_push_ofs *)
    assert (Hsp_push_ofs_step : Ptrofs.add sp_push_ofs (Ptrofs.repr 8) = sp_ofs).
    { unfold sp_push_ofs.
      rewrite Ptrofs.sub_add_opp.
      rewrite Ptrofs.add_assoc.
      rewrite (Ptrofs.add_commut (Ptrofs.neg (Ptrofs.repr 8)) (Ptrofs.repr 8)).
      rewrite Ptrofs.add_neg_zero.
      rewrite Ptrofs.add_zero. reflexivity. }

    assert (Hnew_stack_repr : stack_repr hm' cb co m_final
      (Val_closure addr 0 :: Machine.stack s) sp_b sp_push_ofs).
    { econstructor.
      - exact Hblock_load_final.
      - exact Hval_repr_new.
      - rewrite Hsp_push_ofs_step.
        apply Hstack_repr_ext. exact Hstack_final. }

    (* Global repr in m_final *)
    assert (Hglobal_final : global_repr hm cb co m_final (Machine.global s) gb go0).
    { (* Thread through all stores *)
      assert (Hg1 : global_repr hm cb co m1 (Machine.global s) gb go0).
      { eapply (global_repr_store_other_block hm cb co); eauto. }
      assert (Hg2 : global_repr hm cb co m2 (Machine.global s) gb go0).
      { eapply (global_repr_store_other_block hm cb co); eauto. }
      assert (Hg_alloc : global_repr hm cb co m_alloc (Machine.global s) gb go0).
      { clear -Hg2 Halloc_load_pres Hgb_ne_new.
        induction Hg2 as [| v vs gb0 gofs0 cv Hld Hvr Htl IH].
        - constructor.
        - econstructor.
          + apply Halloc_load_pres. exact Hld. exact Hgb_ne_new.
          + exact Hvr.
          + apply IH. exact Hgb_ne_new. }
      assert (Hg_spadj : global_repr hm cb co m_sp_adj (Machine.global s) gb go0).
      { eapply (global_repr_store_other_block hm cb co); eauto. }
      assert (Hg_spdec : global_repr hm cb co m_sp_dec (Machine.global s) gb go0).
      { eapply (global_repr_store_other_block hm cb co); eauto. }
      assert (Hg_push : global_repr hm cb co m_push (Machine.global s) gb go0).
      { assert (Hne_sp_gb: gb <> sp_b).
        { intro Heq. apply Hsp_ne_gb. symmetry. exact Heq. }
        clear -Hg_spdec Hstore_push Hne_sp_gb.
        induction Hg_spdec as [| v vs gb0 gofs0 cv Hld Hvr Htl IH].
        - constructor.
        - econstructor.
          + erewrite Mem.load_store_other.
            * exact Hld.
            * exact Hstore_push.
            * left. exact Hne_sp_gb.
          + exact Hvr.
          + apply IH. exact Hne_sp_gb. }
      assert (Hg_accu : global_repr hm cb co m_accu (Machine.global s) gb go0).
      { eapply (global_repr_store_other_block hm cb co); eauto. }
      assert (Hg_f0 : global_repr hm cb co m_f0 (Machine.global s) gb go0).
      { clear -Hg_accu Hstore_f0' Hgb_ne_new.
        induction Hg_accu as [| v vs gb0 gofs0 cv Hld Hvr Htl IH].
        - constructor.
        - econstructor.
          + erewrite Mem.load_store_other.
            * exact Hld.
            * exact Hstore_f0'.
            * left. exact Hgb_ne_new.
          + exact Hvr.
          + apply IH. exact Hgb_ne_new. }
      assert (Hg_f1 : global_repr hm cb co m_f1 (Machine.global s) gb go0).
      { clear -Hg_f0 Hstore_f1' Hgb_ne_new.
        induction Hg_f0 as [| v vs gb0 gofs0 cv Hld Hvr Htl IH].
        - constructor.
        - econstructor.
          + erewrite Mem.load_store_other.
            * exact Hld.
            * exact Hstore_f1'.
            * left. exact Hgb_ne_new.
          + exact Hvr.
          + apply IH. exact Hgb_ne_new. }
      eapply (global_repr_store_other_block hm cb co); eauto. }

    (* Now build abs_rel *)
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s in le' *)
    { repeat (rewrite PTree.gso by (compute; congruence)).
      exact Hle_s. }

    (* 2. pc field -- advanced 3 times (nfuncs, nvars, then +nfuncs=1) *)
    { exists (Vptr cb pc_ofs_3). split.
      - exact Hpc_load_final.
      - unfold pc_rel.
        assert (Hpc_ofs_3_eq : pc_ofs_3 =
          Ptrofs.add new_co (Ptrofs.repr (Machine.pc s * sizeof_code_t))).
        { unfold new_co, pc_ofs_3, pc_ofs_2, pc_ofs_1, pc_ofs, sizeof_code_t.
          change (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr 1)))
            with (Ptrofs.repr 4).
          rewrite !Ptrofs.add_assoc. f_equal.
          change (Ptrofs.add (Ptrofs.repr 4) (Ptrofs.add (Ptrofs.repr 4) (Ptrofs.repr 4)))
            with (Ptrofs.repr 12).
          rewrite (Ptrofs.add_commut (Ptrofs.repr 4) (Ptrofs.repr (Machine.pc s * 4))).
          rewrite <- (Ptrofs.add_assoc (Ptrofs.repr 4) (Ptrofs.repr (Machine.pc s * 4)) (Ptrofs.repr 4)).
          rewrite (Ptrofs.add_commut (Ptrofs.repr 4) (Ptrofs.repr (Machine.pc s * 4))).
          rewrite (Ptrofs.add_assoc (Ptrofs.repr (Machine.pc s * 4)) (Ptrofs.repr 4) (Ptrofs.repr 4)).
          change (Ptrofs.add (Ptrofs.repr 4) (Ptrofs.repr 4)) with (Ptrofs.repr 8).
          rewrite <- (Ptrofs.add_assoc (Ptrofs.repr 4) (Ptrofs.repr (Machine.pc s * 4)) (Ptrofs.repr 8)).
          rewrite (Ptrofs.add_commut (Ptrofs.repr 4) (Ptrofs.repr (Machine.pc s * 4))).
          rewrite (Ptrofs.add_assoc (Ptrofs.repr (Machine.pc s * 4)) (Ptrofs.repr 4) (Ptrofs.repr 8)).
          change (Ptrofs.add (Ptrofs.repr 4) (Ptrofs.repr 8)) with (Ptrofs.repr 12).
          reflexivity. }
        rewrite Hpc_ofs_3_eq.
        unfold ard'. simpl ar_code_base_ofs. simpl Machine.pc.
        reflexivity. }

    (* 3. accu field -- Val_closure addr 0 *)
    { exists block_v. split.
      - exact Haccu_load_final.
      - simpl. eapply val_repr_co_shift. exact Hval_repr_new. }

    (* 4. sp field -- sp_push_ofs, new stack *)
    { exists (Vptr sp_b sp_push_ofs), sp_b, sp_push_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
      - exact Hsp_load_final.
      - reflexivity.
      - simpl. eapply stack_repr_co_shift. exact Hnew_stack_repr.
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - rewrite Hsp_push_unsigned. lia.
      - simpl length. rewrite Hsp_push_unsigned. lia.
      - split.
        + intros ofs0 Hofs0.
          simpl length in Hofs0. rewrite Hsp_push_unsigned in Hofs0.
          eapply Mem.perm_store_1. exact Hstore_pc3.
          eapply Mem.perm_store_1. exact Hstore_f1'.
          eapply Mem.perm_store_1. exact Hstore_f0'.
          eapply Mem.perm_store_1. exact Hstore_accu.
          eapply Mem.perm_store_1. exact Hstore_push.
          eapply Mem.perm_store_1. exact Hstore_sp_dec.
          eapply Mem.perm_store_1. exact Hstore_sp_adj.
          eapply Halloc_perm_pres.
          * eapply Mem.perm_valid_block.
            apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc2).
            apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc1).
            apply (Hsp_writable 0). lia.
          * apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc2).
            apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc1).
            apply Hsp_writable. lia.
        + rewrite Hsp_push_unsigned. exact Hsp_push_align. }

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
      eapply Mem.perm_store_1. exact Hstore_pc3.
      eapply Mem.perm_store_1. exact Hstore_f1'.
      eapply Mem.perm_store_1. exact Hstore_f0'.
      eapply Mem.perm_store_1. exact Hstore_accu.
      eapply Mem.perm_store_1. exact Hstore_push.
      eapply Mem.perm_store_1. exact Hstore_sp_dec.
      eapply Mem.perm_store_1. exact Hstore_sp_adj.
      eapply Halloc_perm_pres.
      - eapply Mem.perm_valid_block.
        apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc2).
        apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc1).
        apply (Hsb_writable (Ptrofs.unsigned so)). lia.
      - apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc2).
        apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore_pc1).
        apply Hsb_writable. exact Hofs0. }
  }
Qed.

Definition CLOSUREREC_correct_for_spec : forall code_ofs,
    Int.min_signed <= code_ofs <= Int.max_signed ->
    handler_correct (handle_CLOSUREREC 1 0 [code_ofs]) f_instr_CLOSUREREC
      (heap_alloc_with_stores 2 247 alloc_store_2
       /\p code_at (Int.repr 1) /\p code_arg_at 1 (Int.repr 0)
       /\p code_arg_at 2 (Int.repr code_ofs) /\p sp_at_least 16)
      (fun msg _ => msg = "CLOSUREREC: no code offsets"%string -> False)
      (fun _ => False) (fun _ _ _ => False).
  Proof.
    intros code_ofs Hrange.
    apply handler_correct_weaken with
      (sp := fun e m s ard => closurerec_step_pre code_ofs e m s ard).
    - exact (verify_CLOSUREREC_correct code_ofs).
    - intros e le m s ard Hrel [Hhaw [Hc0 [Hc1 [Hc2 Hsp16]]]].
      destruct Hhaw as [Hhap Hsu].
      unfold heap_alloc_pre in Hhap.
      destruct Hhap as (He & Hhm & Hvb & Hfs & H5).
      unfold closurerec_step_pre.
      split; [exact He|].
      split; [exact Hc0|].
      split; [exact Hc1|].
      split; [exact Hc2|].
      split; [exact Hrange|].
      split; [exact Hhm|].
      split; [exact Hvb|].
      split; [exact Hfs|].
      split.
      { intros m'. destruct (H5 m') as (ma & nb & no & Hex & Hfr & Hld & Hpm).
        exists ma, nb, no.
        split; [exact Hex|]. split; [exact Hfr|]. split; [exact Hld|].
        split; [exact Hpm|].
        pose proof (Hsu m' ma nb no Hex Hfr Hld Hpm) as Has2.
        intros cv. destruct (Has2 cv) as (ms & Hs & Hl & Hlo & Hinner).
        exists ms. split; [exact Hs|]. split; [exact Hl|]. split; [exact Hlo|].
        intros cv1. destruct (Hinner cv1) as (ms1 & Hs1 & Hl1 & Hf0ld & Hlo1 & Hperm).
        exists ms1. split; [exact Hs1|]. split; [exact Hl1|].
        split; [exact Hf0ld|]. split; [exact Hlo1|].
        intros b ofs k p Hvb_s Hpm_s.
        apply Hperm. eapply Mem.perm_store_2. exact Hs. exact Hpm_s. }
      { intros sp_b sp_ofs Hsp_load.
        destruct Hsp16 as (sp_b' & sp_ofs' & Hsp_load' & Hsp_ge16).
        rewrite Hsp_load in Hsp_load'. inversion Hsp_load'. subst sp_b' sp_ofs'.
        destruct Hrel as (_ & _ & _ & (sp_ptr0 & sp_b0 & sp_ofs0 & Hsp_load0 & Hsp_eq0 & _ & _ & _ & _ & _ & Hsp_bounded0 & _ & Hsp_align0) & _).
        subst sp_ptr0.
        rewrite Hsp_load in Hsp_load0. inversion Hsp_load0. subst sp_b0 sp_ofs0.
        split; [exact Hsp_ge16|].
        split.
        - destruct Hsp_align0 as [k Hk].
          exists (k - 1). simpl align_chunk in *. lia.
        - lia. }
  Qed.
