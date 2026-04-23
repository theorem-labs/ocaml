(* PUSH_bigstep_compl_computational.v -- PUSH completeness proof *)

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

Theorem verify_PUSH_correct :
    handler_correct handle_PUSH f_instr_PUSH
      (fun _ => None)
      (fun _ m _ ard =>
         let sb := ar_sptr_block ard in
         let so := ar_sptr_ofs ard in
         exists sp_b sp_ofs,
           Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) /\
           Ptrofs.unsigned sp_ofs >= 16)
      (fun _ => False) (fun _ _ _ => False).

Proof.
Admitted.

(* Wrapper with the exact type expected by InstructVerificationProof.v.
   handle_instr PUSH = handle_PUSH and clight_of PUSH = f_instr_PUSH
   by computation.  pre_of PUSH = sp_at_least 16 which is convertible
   with the lambda above.  Since handle_PUSH always returns Step, the
   P_error/P_halt/P_ccall predicates are dead code in the match. *)
Definition correct_PUSH :
  handler_correct (Dispatch.handle_instr PUSH) (clight_of PUSH)
    (error_message_of PUSH)
    (pre_of PUSH) (P_halt_of PUSH) (P_ccall_of PUSH).
Proof.
Admitted.

