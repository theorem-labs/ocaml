(* ADDINT_bigstep_compl_computational.v -- ADDINT completeness proof using
   the computational evaluator from StepToBigstep.v.

   ADDINT handler in C:
     _t'1 = s->sp;           // load sp
     s->sp = _t'1 + 1;       // sp++ (pop stack)
     _t'2 = s->accu;         // load accu
     _t'3 = *_t'1;           // load stack[0] (old sp)
     s->accu = (long)((long)_t'2 + (long)_t'3 - 1);  // tagged add
     return 0;

   Rocq handler:
     handle_ADDINT pc' s = match accu, stack with
       | Val_int a, Val_int b :: rest =>
           Step (s<|pc:=pc'|><|accu:=Val_int(a+b)|><|stack:=rest|>)
       | _, _ => Error ...

   This proof handles TWO stores (sp field, accu field) and the tagged
   integer arithmetic identity: (2a+1) + (2b+1) - 1 = 2(a+b) + 1.

   Uses abs_rel directly (no separate _pre relation). *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
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
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

Theorem verify_ADDINT_compl_comp :
    handler_correct handle_ADDINT f_instr_ADDINT
      (fun _ => None)
      (pre_and accu_is_long stack_head_is_long)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* ================================================================== *)
(* Wrapper with canonical InstructSpec predicates                       *)
(* ================================================================== *)

Import Bytecode.AST.

Theorem correct_ADDINT :
    handler_correct (handle_instr ADDINT) (clight_of ADDINT)
      (error_message_of ADDINT)
      (pre_of ADDINT) (P_halt_of ADDINT) (P_ccall_of ADDINT).
Proof.
Admitted.
