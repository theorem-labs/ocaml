(* C_CALL1_correct.v -- C_CALL1 handler completeness proof.

   The C body advances pc by 1 and returns 3 (CCall_request signal).
   The Rocq handler is: handle_C_CALL 1 prim_idx pc' s = CCall_request ...
   This wrapper statement is false as stated: handle_C_CALL always returns
   CCall_request, while this theorem passes P_ccall = (fun _ => None). After
   unfolding handler_correct, the first obligation is
     None = Some (prim_idx, [accu s], cont)
   for an arbitrary state s. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat.
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

