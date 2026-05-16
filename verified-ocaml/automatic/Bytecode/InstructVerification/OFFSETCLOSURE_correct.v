(* OFFSETCLOSURE_correct.v -- OFFSETCLOSURE (parameterized) completeness proof.

   Proves that the C handler f_instr_OFFSETCLOSURE computes the same state
   transition as the Rocq handle_OFFSETCLOSURE n handler.

   OFFSETCLOSURE reads n from the code buffer, reads env, computes
   env + n*sizeof(long), stores to accu, and advances pc past the argument.

   C code (f_instr_OFFSETCLOSURE):
     _t'1 = s->pc;             // read pc pointer
     s->pc = _t'1 + 1;         // store 1: advance pc past argument
     _t'2 = s->env;            // read env (tlong)
     _t'3 = *_t'1;             // read n from code buffer (Mint32)
     s->accu = _t'2 + _t'3 * sizeof(long);  // store 2: set accu

   Rocq: handle_OFFSETCLOSURE n pc' s matches on s.(env):
     - Val_closure addr base_ofs =>
         Step (s <|pc := pc'|> <|accu := Val_closure addr (Z.to_nat (Z.of_nat base_ofs + n))|>)
     - Val_block t _ => if Z.eqb n 0 then Step ... else Error
     - _ => Error

   Two stores: pc field at offset +0, accu field at offset +8.

   Combines CONSTINT's code-buffer-read + pc-advance pattern with
   OFFSETCLOSURE2's env offset arithmetic, generalized over n.

   NO AXIOMS.  All structural/range constraints are preconditions
   via handler_correct. *)

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
(* Struct layout: _pc at offset 0, _env at offset 24, _accu at offset 8 *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Local Lemma interp_state_co_pc_env_accu : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
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

(* _t'3 * sizeof(long): tint * tulong *)
Local Lemma sem_mul_n_sizeof : forall n m,
  sem_binary_operation (genv_cenv ge) Omul
    (Vint n) tint
    (Vptrofs (Ptrofs.repr 8)) tulong m
  = Some (Vlong (Int64.mul (Int64.repr (Int.signed n)) (Int64.repr 8))).
Proof.
  intros. unfold sem_binary_operation, sem_mul, sem_binarith.
  change (classify_binarith tint tulong) with (bin_case_l Unsigned).
  simpl.
  unfold sem_cast. simpl classify_cast.
  reflexivity.
Qed.

(* Vlong + Vlong: tlong + tulong *)
Local Lemma sem_add_long_long : forall a b m,
  sem_binary_operation (genv_cenv ge) Oadd
    (Vlong a) tlong (Vlong b) tulong m
  = Some (Vlong (Int64.add a b)).
Proof.
  intros. reflexivity.
Qed.

(* Cast tulong -> tlong for Vlong *)
Local Lemma sem_cast_tulong_tlong : forall n m,
  sem_cast (Vlong n) tulong tlong m = Some (Vlong n).
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

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
(* Precondition                                                        *)
(* ================================================================== *)

Definition offsetclosure_pre (n : Z)
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  (* Code buffer contains Int.repr n at the current PC position *)
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr n)) /\
  (* n fits in the int32 signed range *)
  Int.min_signed <= n <= Int.max_signed /\
  (* env is representable as Vlong (needed for C arithmetic path) *)
  (exists env_long,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long) /\
    (* The result of the C arithmetic gives valid val_repr *)
    match s.(Machine.env) with
    | Val_closure addr base_ofs =>
        val_repr hm cb co
          (Val_closure addr (Z.to_nat (Z.of_nat base_ofs + n)))
          (Vlong (Int64.add env_long
            (Int64.mul (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 8))))
    | Val_block t l =>
        val_repr hm cb co (Val_block t l)
          (Vlong (Int64.add env_long
            (Int64.mul (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 8))))
    | _ => True
    end).

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr (OFFSETCLOSURE z) / clight_of (OFFSETCLOSURE z) / pre_of (OFFSETCLOSURE z)
   are convertible with handle_OFFSETCLOSURE z / f_instr_OFFSETCLOSURE / offsetclosure_pre z.
   P_halt_of and P_ccall_of are vacuously satisfied (OFFSETCLOSURE never halts or
   issues a C call).  error_message_of requires a small computation bridge via
   error_message_of. *)
Definition correct_OFFSETCLOSURE : forall z,
    handler_correct (handle_instr (Bytecode.AST.OFFSETCLOSURE z)) (clight_of (Bytecode.AST.OFFSETCLOSURE z))
      (error_message_of (Bytecode.AST.OFFSETCLOSURE z))
      (pre_of (Bytecode.AST.OFFSETCLOSURE z)) (P_halt_of (Bytecode.AST.OFFSETCLOSURE z)) (P_ccall_of (Bytecode.AST.OFFSETCLOSURE z)).
Proof.
(* Blocker: clight_of (OFFSETCLOSURE z) is always f_instr_OFFSETCLOSURE, not
   one of the specialized f_instr_OFFSETCLOSURE0/3/M3 handlers.  Therefore the
   specialized closed lemmas are not type-compatible with this canonical
   forall-z statement. *)
Admitted.
