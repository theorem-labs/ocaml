(* CHECK_SIGNALS_correct.v -- CHECK_SIGNALS handler correctness proof.

   handle_CHECK_SIGNALS pc' s = Step (s <|pc := pc'|>).
   C body: Sskip; return 0.
   error_message_of CHECK_SIGNALS s = None for all s.

   This is the simplest possible handler proof: the C code does nothing
   but return 0, and the Rocq handler just updates pc to the already-current
   value (pc' = Machine.pc s). *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
From OCamlInterp.Manual Require Import Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.

Definition correct_CHECK_SIGNALS :
  handler_correct (handle_instr CHECK_SIGNALS) (clight_of CHECK_SIGNALS)
    (error_message_of CHECK_SIGNALS)
    (pre_of CHECK_SIGNALS) (P_halt_of CHECK_SIGNALS) (P_ccall_of CHECK_SIGNALS).
Proof.
  unfold handler_correct, handler_correct_gen.
  intros e le m s.
  (* error_message_of CHECK_SIGNALS s computes to None *)
  simpl error_message_of.
  (* handle_instr CHECK_SIGNALS (Machine.pc s) s computes to
     Step (s <|pc := Machine.pc s|>) *)
  simpl handle_instr. unfold handle_CHECK_SIGNALS.
  (* Now in the Step branch. Introduce the abs_rel witness and precondition. *)
  intros w Hrel Hpre.
  (* Provide le' = le, m' = m: the C body doesn't modify temps or memory *)
  exists le, m.
  split.
  - (* clight_returns: exec_stmt for body = Sskip; return 0 *)
    unfold clight_returns. simpl fn_body.
    (* E0 ** E0 is opaque, so we rewrite it first *)
    assert (Hexec :
      exec_stmt function_entry1 clight_ge e le m
        (Ssequence Sskip (Sreturn (Some (Econst_int (Int.repr 0) tint))))
        (E0 ** E0) le m
        (Out_return (Some (Vint (Int.repr 0), tint)))).
    { eapply exec_Sseq_1.
      - exact (exec_Sskip _ _ e le m).
      - eapply exec_Sreturn_some.
        exact (eval_Econst_int _ e le m (Int.repr 0) tint). }
    rewrite E0_left in Hexec.
    exact Hexec.
  - (* R_ex: exists w such that abs_rel_with_ard e le m (s <|pc := pc s|>) w *)
    unfold R_ex.
    exists w.
    (* s <|pc := Machine.pc s|> is propositionally equal to s after destructing *)
    destruct s; exact Hrel.
Qed.
