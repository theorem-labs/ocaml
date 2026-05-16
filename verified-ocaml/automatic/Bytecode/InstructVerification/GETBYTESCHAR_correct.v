(* GETBYTESCHAR_correct.v -- GETBYTESCHAR correctness proof.

   GETBYTESCHAR has an identical C body to GETSTRINGCHAR, and
   both map to handle_GETSTRINGCHAR in Interpret.v.  The proof
   follows from the GETSTRINGCHAR proof plus body equality.

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
From OCamlInterp.Manual Require Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETSTRINGCHAR_correct.

(* The fn_body fields are definitionally equal *)
Local Lemma body_eq :
  fn_body f_instr_GETBYTESCHAR = fn_body f_instr_GETSTRINGCHAR.
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Wrapper with the canonical type for InstructVerificationProof.v     *)
(* ================================================================== *)

Import Bytecode.AST.

Definition correct_GETBYTESCHAR :
    handler_correct (handle_instr GETBYTESCHAR) (clight_of GETBYTESCHAR)
      (error_message_of GETBYTESCHAR)
      (pre_of GETBYTESCHAR) (P_halt_of GETBYTESCHAR) (P_ccall_of GETBYTESCHAR).
Proof.
  exact correct_GETSTRINGCHAR.
Qed.
