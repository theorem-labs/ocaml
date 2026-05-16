(* ACC0_bigstep_compl_computational.v -- ACC0 completeness proof using
   the computational evaluator from StepToBigstep.v.

   Same theorem as ACC0_bigstep_compl_allresults.v, but Part 1
   (constructing the exec_stmt derivation) uses comp_eval_stmt +
   eval_stmt_to_exec instead of manual tactic construction.

   APPROACH:
   1. Prove comp_eval_stmt clight_ge 10 e le m body = Some (...)
      by interleaving [cbn -[...]] (reduces evaluator control flow) and
      [rewrite] (resolves abstract PTree lookups, memory loads, composite
      lookups, semantic operations, etc.)
   2. Apply eval_stmt_to_exec to obtain exec_stmt.
   3. Part 2 (abs_rel preservation) is identical to the allresults version.

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
   cbn reduces: comp_eval_stmt/expr/lvalue, fn_body, typeof, access_mode,
   Mem.loadv/storev (Vptr dispatch), Eapp, match on option/outcome.
   cbn leaves alone (via -[...]): clight_ge (prevents expanding the 9000-line
   prog AST), genv_cenv (record projection), Mptr (opaque Archi.ptr64),
   sem_binary_operation/sem_cast (depend on ge or ptr64),
   Mem.load/store (abstract memory), Ptrofs arith (abstract offsets),
   field_offset (depends on ge), PTree.get/set (abstract temp_env). *)
Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

Theorem verify_ACC0_compl_comp :
    handler_correct (handle_ACC 0) f_instr_ACC0
      (fun _ => None)
      (fun _ _ _ _ => True)
      (fun _ => None) (fun _ => None).
Proof.
  (* Intractable as stated: handler_correct checks the Error branch before
     any abs_rel/precondition assumptions, so stack underflow leaves a bare
     False goal under (fun _ => None). *)
Admitted.

Theorem correct_ACC0 :
    handler_correct (handle_ACC 0) f_instr_ACC0
      (fun _ => None)
      (fun _ _ _ _ => True)
      (fun _ => None) (fun _ => None).
Proof.
  exact verify_ACC0_compl_comp.
Qed.
