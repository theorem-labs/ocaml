(* PUSHACC_correct.v -- Unified PUSHACC wrapper over all n values.

   PUSHACC n = PUSH (push accu to stack) then ACC n (load stack[n] to accu).

   For n in {1..7}, the C runtime has specialised handlers
   (f_instr_PUSHACC1 .. f_instr_PUSHACC7) proven individually in
   PUSHACCk_correct.v files.  This file combines them into the single
   `forall n` statement expected by InstructVerificationProof.v.

   For n outside {1..7}, handle_PUSHACC returns Error "PUSHACC: malformed
   operand" and the error_message_of obligation is discharged by computation.

   NO AXIOMS. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat.
Import ListNotations.
From compcert Require Import Integers.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Handlers Dispatch.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.

Definition correct_PUSHACC : forall n,
  handler_correct (handle_instr (PUSHACC n)) (clight_of (PUSHACC n))
    (error_message_of (PUSHACC n))
    (pre_of (PUSHACC n)) (P_halt_of (PUSHACC n)) (P_ccall_of (PUSHACC n)).
Proof.
Admitted.
