(* PUSHCONST0_correct.v -- PUSHCONST0 completeness proof.

   PUSHCONST0 = PUSH then CONST0.
   C code:
     sp = sp - 1;          // decrement sp
     *sp = accu;            // push old accu onto stack
     accu = Val_int(0);     // set accu to tagged 0 = (0<<1)+1 = 1
   Rocq:
     handle_PUSHCONSTINT 0 pc' s =
       Step (s <|pc := pc'|> <|accu := Val_int 0|> <|stack := accu :: stack|>)

   Three stores:
     Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v
     Store 3: accu field (sb, uso+8) <- Vlong (Int64.repr 1)

   Follows the patterns of PUSH_correct.v and CONST0_correct.v. *)

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

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

