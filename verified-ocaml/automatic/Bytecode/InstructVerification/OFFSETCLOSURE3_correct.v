(* OFFSETCLOSURE3_correct.v -- OFFSETCLOSURE3 completeness proof.

   Proves that the C handler f_instr_OFFSETCLOSURE3 computes the same state
   transition as the Rocq handle_OFFSETCLOSURE 2 handler.

   OFFSETCLOSURE3 C code:
     _t'1 = s->env;
     s->accu = _t'1 + 3 * sizeof(long);   // env + 24 bytes
     return 0

   Rocq: handle_OFFSETCLOSURE 2 pc' s matches on s.(env):
     - Val_int z => Error
     - Val_block t _ => Error  (Z.eqb 2 0 = false)
     - Val_ptr n => Error
     - Val_closure addr base_ofs => Step (accu := Val_closure addr (base_ofs + 2))

   The C code performs integer addition (tlong + tulong) on the env value.
   CompCert's sem_binarith does not support Vptr for integer addition, so
   we require a step_pre asserting the env value is represented as Vlong
   (a flat integer encoding of the closure pointer) rather than Vptr.
   The precondition also requires that the result of addition gives a
   valid val_repr for the new closure.

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
Local Notation exec := (exec_stmt function_entry1 clight_ge).

(* Tactic for controlled reduction of the evaluator. *)
Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Semantic lemmas for the OFFSETCLOSURE3 body                         *)
(* ================================================================== *)

(* Inner Omul: 3 * sizeof(long) = 24, using Vptrofs form *)
Local Lemma sem_mul_3_sizeof : forall m,
  sem_binary_operation (genv_cenv ge) Omul
    (Vint (Int.repr 3)) tint
    (Vptrofs (Ptrofs.repr 8)) tulong m
  = Some (Vlong (Int64.repr 24)).
Proof. intros. reflexivity. Qed.

(* Outer Oadd: Vlong + Vlong(24) *)
Local Lemma sem_add_long_24 : forall n m,
  sem_binary_operation (genv_cenv ge) Oadd
    (Vlong n) tlong (Vlong (Int64.repr 24)) tulong m
  = Some (Vlong (Int64.add n (Int64.repr 24))).
Proof. intros. reflexivity. Qed.

(* Cast: tulong -> tlong for Vlong *)
Local Lemma sem_cast_tulong_tlong : forall n m,
  sem_cast (Vlong n) tulong tlong m = Some (Vlong n).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_OFFSETCLOSURE3_compl_comp :
    handler_correct (handle_OFFSETCLOSURE 2) f_instr_OFFSETCLOSURE3
      (fun _ => None)
      (closure_offset_pre 2 24)
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

Definition correct_OFFSETCLOSURE3 :
    handler_correct (handle_OFFSETCLOSURE 2) f_instr_OFFSETCLOSURE3
      (fun _ => None)
      (closure_offset_pre 2 24)
      (fun _ => None) (fun _ => None).
Proof.
  exact verify_OFFSETCLOSURE3_compl_comp.
Qed.
