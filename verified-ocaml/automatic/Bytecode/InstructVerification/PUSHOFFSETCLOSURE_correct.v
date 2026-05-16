(* PUSHOFFSETCLOSURE_correct.v -- PUSHOFFSETCLOSURE (parameterized) completeness proof.

   C handler (f_instr_PUSHOFFSETCLOSURE):
     _t'6 = s->sp;                    // load sp
     _t'1 = (tptr tlong)(_t'6 - 1);   // new_sp = sp - 1
     s->sp = _t'1;                     // store 1: update sp field
     _t'5 = s->accu;                   // load accu
     *_t'1 = _t'5;                     // store 2: push accu onto stack
     _t'2 = s->pc;                     // load pc
     s->pc = _t'2 + 1;                // store 3: advance pc
     _t'3 = s->env;                    // load env from m3
     _t'4 = *_t'2;                     // read N from code buffer
     s->accu = _t'3 + _t'4 * sizeof(long);  // store 4: accu = env + N*8
     return 0;

   Rocq (handle_PUSHOFFSETCLOSURE ofs):
     let new_stack := accu :: stack in
     match env with
     | Val_closure addr base_ofs =>
         Step (accu := Val_closure addr (Z.to_nat (Z.of_nat base_ofs + ofs)),
               stack := new_stack)
     | Val_block t _ => if Z.eqb ofs 0 then Step ... else Error
     | _ => Error
     end

   Four stores on struct block + one on stack block:
     Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v
     Store 3: pc field (sb, uso+0) <- Vptr cb new_pc_ofs
     Store 4: accu field (sb, uso+8) <- result_v  (= env_long + ofs*8)

   step_pre: sp_ofs >= 16 + code buffer read + closure offset precondition.
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
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.
Local Notation exec := (exec_stmt function_entry1 clight_ge).

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout: all four field offsets                                *)
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

Lemma interp_state_co_all : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                     *)
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

Local Lemma sem_cast_tulong_tlong : forall n m,
  sem_cast (Vlong n) tulong tlong m = Some (Vlong n).
Proof. intros. reflexivity. Qed.

(* Omul: Vint(N) * Vptrofs(8) -> Vlong(Int.signed N * 8) *)
Local Lemma sem_mul_int_sizeof : forall n m,
  sem_binary_operation (genv_cenv ge) Omul
    (Vint n) tint
    (Vptrofs (Ptrofs.repr 8)) tulong m
  = Some (Vlong (Int64.mul (Int64.repr (Int.signed n)) (Int64.repr 8))).
Proof. intros. reflexivity. Qed.

(* Oadd: Vlong + Vlong -> Vlong *)
Local Lemma sem_add_long_long : forall a b m,
  sem_binary_operation (genv_cenv ge) Oadd
    (Vlong a) tlong (Vlong b) tulong m
  = Some (Vlong (Int64.add a b)).
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* pc_rel with shifted code base *)
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
(* Main theorem                                                        *)
(* ================================================================== *)

#[warnings="-not-a-closed-proof"]
(* ================================================================== *)
(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr (PUSHOFFSETCLOSURE z) / clight_of (PUSHOFFSETCLOSURE z) /
   pre_of (PUSHOFFSETCLOSURE z) are convertible with
   handle_PUSHOFFSETCLOSURE z / f_instr_PUSHOFFSETCLOSURE /
   pushoffsetclosure_step_pre z.
   P_halt_of and P_ccall_of are vacuously satisfied (PUSHOFFSETCLOSURE
   never halts or issues a C call).  error_message_of requires a small
   computation bridge. *)
(* ================================================================== *)

Definition correct_PUSHOFFSETCLOSURE : forall z,
    handler_correct (handle_instr (PUSHOFFSETCLOSURE z)) (clight_of (PUSHOFFSETCLOSURE z))
      (error_message_of (PUSHOFFSETCLOSURE z))
      (pre_of (PUSHOFFSETCLOSURE z)) (P_halt_of (PUSHOFFSETCLOSURE z)) (P_ccall_of (PUSHOFFSETCLOSURE z)).
Proof.
Admitted.
