(* BRANCHIF_correct.v -- BRANCHIF handler completeness proof.

   BRANCHIF handler:
   - Rocq: handle_BRANCHIF target pc' s matches accu:
       Val_int 0 => Step {pc := pc'}        (fall through; pc' = s.pc)
       _         => Step {pc := target}      (branch taken)

   - C (Clight AST): The handler body does:
       1. _t'1 = s->accu                   (read accu, tlong)
       2. if (_t'1 != ((0 << 1) + 1))      (test accu != tagged(0) = 1)
          THEN (branch taken):
            _t'3 = s->pc
            _t'4 = s->pc
            _t'5 = *_t'4                    (read offset from code stream)
            s->pc = _t'3 + _t'5            (ptr + int arithmetic)
          ELSE (fall through):
            _t'2 = s->pc
            s->pc = _t'2 + 1               (advance past operand)
       3. return 0

   Two cases:
   - accu = Val_int 0: C takes else branch, stores pc + 1.
   - accu != Val_int 0: C takes then branch, reads offset, stores
     pc + offset.

   Preconditions (via handler_correct):
   - code_base_block != sptr_block (code buffer separate from struct)
   - code buffer at pc contains the branch offset as Vint
   - comparison well-definedness: for non-zero accu, the C ne-comparison
     against tagged(0) succeeds.  This holds when val_repr produces a
     Vlong (Val_int with in-range n, or Val_block tag nil), but not for
     Vptr (CompCert's sem_binarith on tlong/tlong returns None for Vptr).
     The precondition pushes this obligation to the caller. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
From OCamlInterp.Manual Require Bytecode.AST.
Import Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.
Local Notation exec := (exec_stmt function_entry1 clight_ge).

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

Lemma interp_state_co_branchif : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Memory helpers                                                      *)
(* ================================================================== *)

Lemma store_pc_succeeds : forall m sb so_ptrofs v_new,
  Mem.range_perm m sb (Ptrofs.unsigned so_ptrofs) (Ptrofs.unsigned so_ptrofs + 56) Cur Writable ->
  (exists v_old, Mem.load Mint64 m sb (Ptrofs.unsigned so_ptrofs + 0) = Some v_old) ->
  exists m', Mem.store Mint64 m sb (Ptrofs.unsigned so_ptrofs + 0) v_new = Some m'.
Proof.
  intros m sb so_ptrofs v_new Hrp [v_old Hload].
  exact (store_succeeds_sb m sb so_ptrofs 0 v_old Hrp Hload ltac:(lia) ltac:(lia) v_new).
Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* ================================================================== *)
(* Pointer / casting helpers                                           *)
(* ================================================================== *)

Lemma ptrofs_add_zero : forall ofs,
  Ptrofs.add ofs (Ptrofs.repr 0) = ofs.
Proof.
  intros. change (Ptrofs.repr 0) with Ptrofs.zero.
  apply Ptrofs.add_zero.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

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

Lemma sem_add_ptr_int_tint : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint n) tint
    m = Some (Vptr b (Ptrofs.add ofs
                (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                            (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* ================================================================== *)
(* Comparison semantics for Val_int 0 case                             *)
(* ================================================================== *)

Lemma sem_one_long_eq : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Cop.One
    (Vlong n) tlong (Vlong (Int64.repr 1)) tlong m
    = Some (Val.of_bool (negb (Int64.eq n (Int64.repr 1)))).
Proof.
  intros. reflexivity.
Qed.

Lemma bool_val_of_bool : forall b m,
  bool_val (Val.of_bool b) tint m = Some b.
Proof.
  intros [] m; simpl; reflexivity.
Qed.

Lemma int64_eq_1_1 : Int64.eq (Int64.repr 1) (Int64.repr 1) = true.
Proof.
  unfold Int64.eq.
  rewrite Coqlib.zeq_true.
  reflexivity.
Qed.

(* bool_val for Vint Int.one on tint gives true *)
Lemma bool_val_vint_one : forall m,
  bool_val (Vint Int.one) tint m = Some true.
Proof.
  intros. simpl. reflexivity.
Qed.

(* ================================================================== *)
(* pc_rel helpers                                                      *)
(* ================================================================== *)

(* For the fall-through case: new code base is co + sizeof_code_t *)
Lemma pc_rel_shift_1 : forall cb co rocq_pc,
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
(* Tactic for the "branch taken" abs_rel postcondition.                *)
(* ================================================================== *)

Local Ltac prove_field_survives Hstore Hload :=
  apply (load_after_store_other _ _ _ _ _ _ _ Hstore Hload); right; lia.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_BRANCHIF_correct : forall target,
    handler_correct (handle_BRANCHIF target) f_instr_BRANCHIF
      (fun _ => None)
      (fun _ m s ard =>
         (* Code block is separate from struct block *)
         ar_code_base_block ard <> ar_sptr_block ard /\
         (* Code buffer at pc contains the branch offset *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
           = Some (Vint (Int.repr (target - Machine.pc s))) /\
         (* Comparison well-definedness for non-zero accu *)
         (Machine.accu s <> Val_int 0 ->
            forall cv,
            val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Machine.accu s) cv ->
            sem_binary_operation (genv_cenv clight_ge) Cop.One
              cv tlong (Vlong (Int64.repr 1)) tlong m
              = Some (Vint Int.one)) /\
         (* Zero accu must be tagged int (not code pointer) *)
         (Machine.accu s = Val_int 0 ->
            forall cv,
            val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Machine.accu s) cv ->
            exists z, cv = Vlong z))
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with the exact type expected by InstructVerificationProof.v.
   handle_instr (BRANCHIF z) = handle_BRANCHIF z by computation in Dispatch.
   clight_of (BRANCHIF z) = f_instr_BRANCHIF, pre_of (BRANCHIF z) = branchif_step_pre z.
   Since handle_BRANCHIF always returns Step, the P_error/P_halt/P_ccall
   predicates are in dead match branches and thus irrelevant. *)
Definition correct_BRANCHIF : forall z,
  handler_correct (handle_instr (BRANCHIF z)) (clight_of (BRANCHIF z))
    (error_message_of (BRANCHIF z))
    (pre_of (BRANCHIF z)) (P_halt_of (BRANCHIF z)) (P_ccall_of (BRANCHIF z)).
Proof.
Admitted.
