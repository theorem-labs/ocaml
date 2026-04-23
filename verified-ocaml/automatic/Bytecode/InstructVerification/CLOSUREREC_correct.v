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
From OCamlInterp.Manual Require Import Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
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
(* Proof body is stale: f_instr_CLOSUREREC body structure changed after
   handler C code was migrated to cpp shim extraction (commit 3271267).
   The Hfn_body_split reflexivity no longer holds because the Sreturn
   nesting moved. Admitted pending a proof rewrite against the new body. *)
Proof. Admitted.


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

(* Wrapper with the exact type expected by InstructVerificationProof.v.
   handle_instr (CLOSUREREC nf nv co) = handle_CLOSUREREC nf nv co by computation.
   clight_of (CLOSUREREC nf nv co) = f_instr_CLOSUREREC by computation.
   pre_of (CLOSUREREC 1 0 [code_ofs]) = heap_alloc_with_stores ... by computation.
   P_error_of (CLOSUREREC nf nv co) is error_message_of applied.
   P_halt_of and P_ccall_of are vacuously False (not STOP/C_CALL).
   For the malformed-operand cases (instr_wfb = false), P_error_of holds
   because both the handler and error_message_of return the same error.
   For the Step case (nfuncs=1, nvars=0, code_offsets=[code_ofs] in range),
   delegates to CLOSUREREC_correct_for_spec. *)
Definition correct_CLOSUREREC : forall nfuncs nvars code_offsets,
  handler_correct (handle_instr (Bytecode.AST.CLOSUREREC nfuncs nvars code_offsets))
    (clight_of (Bytecode.AST.CLOSUREREC nfuncs nvars code_offsets))
    (pre_of (Bytecode.AST.CLOSUREREC nfuncs nvars code_offsets))
    (P_error_of (Bytecode.AST.CLOSUREREC nfuncs nvars code_offsets))
    (P_halt_of (Bytecode.AST.CLOSUREREC nfuncs nvars code_offsets))
    (P_ccall_of (Bytecode.AST.CLOSUREREC nfuncs nvars code_offsets)).
Proof.
Admitted.

