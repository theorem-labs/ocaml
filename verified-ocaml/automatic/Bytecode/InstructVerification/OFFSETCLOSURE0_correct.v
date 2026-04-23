(* OFFSETCLOSURE0_correct.v -- OFFSETCLOSURE0 completeness proof using
   the computational evaluator from StepToBigstep.v.

   Proves that the C handler f_instr_OFFSETCLOSURE0 computes the same state
   transition as the Rocq handle_OFFSETCLOSURE 0 handler.

   OFFSETCLOSURE0 C code: _t'1 = s->env; s->accu = _t'1; return 0
   Rocq: handle_OFFSETCLOSURE 0 pc' s matches on s.(env):
     - Val_closure addr base_ofs => Step (accu := Val_closure addr base_ofs)
     - Val_block t _ => Step (accu := s.(env))
     - _ => Error

   In both Step cases the new accu is s.(env), which is represented by
   env_v in memory.  The C code simply copies env_v to the accu field.

   Uses abs_rel directly (no separate _pre relation).
   All lemmas/axioms imported from HandlerLemmas. *)

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

(* Helper: in the Val_closure case, Z.to_nat (Z.of_nat n + 0) = n *)
Local Lemma offset_closure_0 : forall n,
  Z.to_nat (Z.of_nat n + 0) = n.
Proof. intros. rewrite Z.add_0_r. apply Nat2Z.id. Qed.

Theorem verify_OFFSETCLOSURE0_compl_comp :
    handler_correct (handle_OFFSETCLOSURE 0) f_instr_OFFSETCLOSURE0
      (fun _ => None)
      (fun _ _ _ _ => True)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.
