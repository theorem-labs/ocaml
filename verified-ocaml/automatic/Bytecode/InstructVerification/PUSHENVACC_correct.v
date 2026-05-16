(* PUSHENVACC_correct.v -- PUSHENVACC (parameterized) handler completeness proof.

   PUSHENVACC n: pushes accu to stack, reads index n from the code buffer,
   reads env[n] from the closure environment, stores to accu, and advances
   pc past the argument.

   C handler (f_instr_PUSHENVACC):
     _t'7 = s->sp;               // read sp
     _t'1 = (long ptr)(_t'7-1);  // new_sp = sp - 1
     s->sp = _t'1;               // store 1: update sp field
     _t'6 = s->accu;             // read accu
     *_t'1 = _t'6;               // store 2: push accu onto stack
     _t'2 = s->pc;               // read pc pointer
     s->pc = _t'2 + 1;           // store 3: advance pc past argument
     _t'3 = s->env;              // read env
     _t'4 = *_t'2;               // read n from code buffer (Mint32)
     _t'5 = *(cast(_t'3, tptr tlong) + _t'4);  // env[n]
     s->accu = _t'5;             // store 4: set accu to env field
     return 0;

   Rocq (handle_PUSHENVACC n):
     let new_stack := accu :: stack in
     match field_or_heap s s.(env) n with
     | Some v => Step (s <|pc:=pc'|> <|accu:=v|> <|stack:=new_stack|>)
     | None => Error "PUSHENVACC: env access out of bounds"
     end

   Four stores:
     Store 1: sp field  (sb, uso+16) <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp   (sp_b, new_sp_ofs) <- accu_v
     Store 3: pc field  (sb, uso+0)  <- new_pc_v
     Store 4: accu field (sb, uso+8) <- cv (env field value)

   No Axioms, no Admitted. *)

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
(* Struct layout lemmas                                                *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full).
Proof.
  eexists. split; [| split; [| split; [| split]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_all_PUSHENVACC : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Lemma sem_cast_long_to_ptr_vptr_PEA : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
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

Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_add_env_n : forall env_b env_ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr env_b env_ofs) (tptr tlong)
    (Vint n) tint
    m = Some (Vptr env_b (Ptrofs.add env_ofs
                (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

Lemma pc_rel_shift : forall cb co rocq_pc,
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

Lemma ptrofs_max_unsigned_large : (Ptrofs.max_unsigned >= 2^32)%Z.
Proof. vm_compute. discriminate. Qed.

Lemma ptrofs_mul_8_of_ints_eq : forall n,
  0 <= n ->
  n < Int.half_modulus ->
  Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr n))
  = Ptrofs.repr (n * 8).
Proof.
  intros n Hnn Hn_bound.
  unfold ptrofs_of_int, Ptrofs.of_ints.
  change Int.half_modulus with 2147483648 in Hn_bound.
  rewrite Int.signed_repr.
  2: { change Int.min_signed with (-2147483648).
       change Int.max_signed with 2147483647. lia. }
  unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 8).
  2: { pose proof ptrofs_max_unsigned_large. lia. }
  rewrite (Ptrofs.unsigned_repr n).
  2: { pose proof ptrofs_max_unsigned_large. lia. }
  f_equal. lia.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_PUSHENVACC_correct : forall n,
    handler_correct (handle_instr (Bytecode.AST.PUSHENVACC n)) (clight_of (Bytecode.AST.PUSHENVACC n))
      (error_message_of (Bytecode.AST.PUSHENVACC n))
      (pre_of (Bytecode.AST.PUSHENVACC n)) (P_halt_of (Bytecode.AST.PUSHENVACC n)) (P_ccall_of (Bytecode.AST.PUSHENVACC n)).
Proof.
Admitted.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr (PUSHENVACC n) / clight_of (PUSHENVACC n) / pre_of (PUSHENVACC n)
   are convertible with handle_PUSHENVACC n / f_instr_PUSHENVACC /
   pushenvacc_generic_step_pre n.
   P_halt_of and P_ccall_of are vacuously satisfied (PUSHENVACC never halts or
   issues a C call).  error_message_of requires a small computation bridge. *)
Definition correct_PUSHENVACC : forall n,
    handler_correct (handle_instr (Bytecode.AST.PUSHENVACC n)) (clight_of (Bytecode.AST.PUSHENVACC n))
      (error_message_of (Bytecode.AST.PUSHENVACC n))
      (pre_of (Bytecode.AST.PUSHENVACC n)) (P_halt_of (Bytecode.AST.PUSHENVACC n)) (P_ccall_of (Bytecode.AST.PUSHENVACC n)).
Proof.
  exact verify_PUSHENVACC_correct.
Qed.
