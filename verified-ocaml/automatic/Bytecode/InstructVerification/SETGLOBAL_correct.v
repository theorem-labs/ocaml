(* SETGLOBAL_correct.v -- SETGLOBAL correctness proof.

   SETGLOBAL n reads n from the code buffer, stores accu into
   global_data[n], sets accu to val_unit, and advances pc by 1.

   The C handler (after cpp shim extraction) performs a direct memory
   store to global_data[n] rather than calling caml_modify.

   Rocq handler:
     handle_SETGLOBAL n pc' s =
       let new_global := match set_nth s.(global) n s.(accu) with
                         | Some g => g | None => s.(global) end in
       Step (s <|pc:=pc'|> <|accu:=val_unit|> <|global:=new_global|>)

   C handler (current, direct store):
     _t'2 = s->global_data;
     _t'3 = s->pc;
     _t'4 = *_t'3;
     _t'5 = s->accu;
     global_data[_t'4] = _t'5;     // direct store
     s->accu = ((0 << 1) + 1);     // val_unit = 1
     _t'1 = s->pc;
     s->pc = _t'1 + 1;
     return 0;

   NOTE: The original proof was written against an older C handler that
   called caml_modify.  The regenerated Clight AST (from cpp shim
   extraction) now performs a direct memory store instead.  The proof
   is Admitted pending a rewrite to match the new handler structure. *)

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
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.

(* ================================================================== *)
(* Main theorem (Admitted -- proof needs rewrite for new C handler)    *)
(* ================================================================== *)

Theorem verify_SETGLOBAL_correct : forall n,
    handler_correct (handle_SETGLOBAL n) f_instr_SETGLOBAL
      (setglobal_step_pre n)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* ================================================================== *)
(* Wrapper with the exact type expected by InstructVerificationProof.v *)
(* ================================================================== *)

From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

(* handle_instr (SETGLOBAL n) computes to handle_SETGLOBAL n.
   clight_of (SETGLOBAL n) computes to f_instr_SETGLOBAL.
   pre_of (SETGLOBAL n) computes to setglobal_step_pre n.
   P_error_of (SETGLOBAL n) is vacuously False (error_message_of returns None).
   P_halt_of (SETGLOBAL n) is False (not STOP).
   P_ccall_of (SETGLOBAL n) is False (not C_CALL).
   handle_SETGLOBAL always returns Step, so we delegate directly to
   verify_SETGLOBAL_correct. *)
Definition correct_SETGLOBAL : forall n,
  handler_correct (handle_instr (SETGLOBAL n)) (clight_of (SETGLOBAL n))
    (pre_of (SETGLOBAL n))
    (P_error_of (SETGLOBAL n)) (P_halt_of (SETGLOBAL n)) (P_ccall_of (SETGLOBAL n)).
Proof.
  exact verify_SETGLOBAL_correct.
Qed.
