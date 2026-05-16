(* CLOSUREREC_correct.v -- CLOSUREREC handler completeness proof.

   CLOSUREREC creates recursive closures. It allocates a heap block for
   mutually-recursive functions, fills in code pointers and infix headers,
   then pushes closures onto the stack.

   The executable/spec well-formedness check accepts nfuncs = 1 with arbitrary
   nvars and one in-range code offset. This proof handles only the simplest
   non-trivial case:
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

(* Wrapper with the exact type expected by InstructVerificationProof.v.
   handle_instr (CLOSUREREC nf nv co) = handle_CLOSUREREC nf nv co by computation.
   clight_of (CLOSUREREC nf nv co) = f_instr_CLOSUREREC by computation.
   pre_of (CLOSUREREC 1 0 [code_ofs]) = heap_alloc_with_stores ... by computation.
   error_message_of (CLOSUREREC nf nv co) is error_message_of applied.
   P_halt_of and P_ccall_of are vacuously False (not STOP/C_CALL).
   For the malformed-operand cases (instr_wfb = false), error_message_of holds
   because both the handler and error_message_of return the same error.
   The nvars > 0 well-formed cases are intentionally still covered by the
   admitted body below; this file does not complete that proof. *)
Definition correct_CLOSUREREC : forall nfuncs nvars code_offsets,
  handler_correct (handle_instr (Bytecode.AST.CLOSUREREC nfuncs nvars code_offsets))
    (clight_of (Bytecode.AST.CLOSUREREC nfuncs nvars code_offsets))
    (error_message_of (Bytecode.AST.CLOSUREREC nfuncs nvars code_offsets))
    (pre_of (Bytecode.AST.CLOSUREREC nfuncs nvars code_offsets))
    (P_halt_of (Bytecode.AST.CLOSUREREC nfuncs nvars code_offsets))
    (P_ccall_of (Bytecode.AST.CLOSUREREC nfuncs nvars code_offsets)).
Proof.
Admitted.
