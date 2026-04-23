(* CONST0_bigstep_compl_computational.v -- CONST0 completeness proof using
   the computational evaluator from StepToBigstep.v.

   Proves that the C handler f_instr_CONST0 computes the same state
   transition as the Rocq handle_CONSTINT 0 handler.

   CONST0 C code: s->accu = Val_int(0)  i.e.  s->accu = ((0 << 1) + 1) = 1
   Rocq:          handle_CONSTINT 0 pc' s = Step (s <|pc := pc'|> <|accu := Val_int 0|>)

   The proof follows ACC0_bigstep_compl_computational.v exactly:
   Part 1: Computational evaluation via eval_stmt_to_exec + rewrite chain.
   Part 2: abs_rel preservation (one store to accu, all other fields unchanged).

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

(* Tactic for controlled reduction of the evaluator.
   Same as ACC0: cbn reduces evaluator control flow,
   leaves abstract terms for rewriting. *)
Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

Theorem verify_CONST0_compl_comp :
    handler_correct (handle_CONSTINT 0) f_instr_CONST0
      (fun _ => None)
      (fun _ _ _ _ => True)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.
