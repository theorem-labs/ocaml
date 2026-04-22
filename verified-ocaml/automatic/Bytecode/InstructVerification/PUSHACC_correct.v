(* PUSHACC_correct.v -- Unified PUSHACC wrapper over all n values.

   PUSHACC n = PUSH (push accu to stack) then ACC n (load stack[n] to accu).

   For n in {1..7}, the C runtime has specialised handlers
   (f_instr_PUSHACC1 .. f_instr_PUSHACC7) proven individually in
   PUSHACCk_correct.v files.  This file combines them into the single
   `forall n` statement expected by InstructVerificationProof.v.

   For n outside {1..7}, handle_PUSHACC returns Error "PUSHACC: malformed
   operand" and the P_error_of obligation is discharged by computation.

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

(* Individual handler proofs *)
From OCamlInterp.Automatic.Bytecode.InstructVerification Require Import
  PUSHACC1_correct PUSHACC2_correct PUSHACC3_correct PUSHACC4_correct
  PUSHACC5_correct PUSHACC6_correct PUSHACC7_correct.

(* Lift a handler_correct proof to different P_error/P_halt/P_ccall.
   The handler never produces Halt or CCall_request, so those branches are
   vacuous.  P_error is bridged by an implication. *)
Local Lemma handler_correct_lift handler f sp pe pe' ph ph' pcc pcc' :
  handler_correct handler f sp pe ph pcc ->
  (* Error bridge *)
  (forall s msg, handler (Machine.pc s) s = Error msg -> pe' msg s) ->
  (* Halt is vacuous: handler never halts *)
  (forall v, ph v -> ph' v) ->
  (* CCall is vacuous: handler never calls *)
  (forall n args s', pcc n args s' -> pcc' n args s') ->
  handler_correct handler f sp pe' ph' pcc'.
Proof.
  unfold handler_correct. intros Hc Herr Hhalt Hcc e le m s.
  specialize (Hc e le m s).
  destruct (handler (Machine.pc s) s) as [s'|v|msg|nargs args s'] eqn:Heq.
  - exact Hc.
  - apply Hhalt. exact Hc.
  - apply Herr. exact Heq.
  - apply Hcc. exact Hc.
Qed.

(* Error bridges: for k in 1..7, handle_PUSHACC k errors iff
   nth_error (accu :: stack) k = None; error_message_of (PUSHACC k) s
   computes to the same "PUSHACC: stack underflow" message. *)
Local Lemma pushacc_err_1 : forall s msg,
  handle_PUSHACC 1 (Machine.pc s) s = Error msg ->
  P_error_of (PUSHACC 1) msg s.
Proof.
  intros s msg H. unfold P_error_of, error_message_of, handle_PUSHACC in *.
  simpl in *. destruct (Machine.stack s); [|discriminate].
  injection H as ->. reflexivity.
Qed.

Local Lemma pushacc_err_2 : forall s msg,
  handle_PUSHACC 2 (Machine.pc s) s = Error msg ->
  P_error_of (PUSHACC 2) msg s.
Proof.
  intros s msg H. unfold P_error_of, error_message_of, handle_PUSHACC in *.
  simpl in *.
  destruct (Machine.stack s) as [|? []]; try discriminate;
  injection H as ->; reflexivity.
Qed.

Local Lemma pushacc_err_3 : forall s msg,
  handle_PUSHACC 3 (Machine.pc s) s = Error msg ->
  P_error_of (PUSHACC 3) msg s.
Proof.
  intros s msg H. unfold P_error_of, error_message_of, handle_PUSHACC in *.
  simpl in *.
  destruct (Machine.stack s) as [|? [|? []]]; try discriminate;
  injection H as ->; reflexivity.
Qed.

Local Lemma pushacc_err_4 : forall s msg,
  handle_PUSHACC 4 (Machine.pc s) s = Error msg ->
  P_error_of (PUSHACC 4) msg s.
Proof.
  intros s msg H. unfold P_error_of, error_message_of, handle_PUSHACC in *.
  simpl in *.
  destruct (Machine.stack s) as [|? [|? [|? []]]]; try discriminate;
  injection H as ->; reflexivity.
Qed.

Local Lemma pushacc_err_5 : forall s msg,
  handle_PUSHACC 5 (Machine.pc s) s = Error msg ->
  P_error_of (PUSHACC 5) msg s.
Proof.
  intros s msg H. unfold P_error_of, error_message_of, handle_PUSHACC in *.
  simpl in *.
  destruct (Machine.stack s) as [|? [|? [|? [|? []]]]]; try discriminate;
  injection H as ->; reflexivity.
Qed.

Local Lemma pushacc_err_6 : forall s msg,
  handle_PUSHACC 6 (Machine.pc s) s = Error msg ->
  P_error_of (PUSHACC 6) msg s.
Proof.
  intros s msg H. unfold P_error_of, error_message_of, handle_PUSHACC in *.
  simpl in *.
  destruct (Machine.stack s) as [|? [|? [|? [|? [|? []]]]]]; try discriminate;
  injection H as ->; reflexivity.
Qed.

Local Lemma pushacc_err_7 : forall s msg,
  handle_PUSHACC 7 (Machine.pc s) s = Error msg ->
  P_error_of (PUSHACC 7) msg s.
Proof.
  intros s msg H. unfold P_error_of, error_message_of, handle_PUSHACC in *.
  simpl in *.
  destruct (Machine.stack s) as [|? [|? [|? [|? [|? [|? []]]]]]]; try discriminate;
  injection H as ->; reflexivity.
Qed.

Definition correct_PUSHACC : forall n,
  handler_correct (handle_instr (PUSHACC n)) (clight_of (PUSHACC n))
    (pre_of (PUSHACC n))
    (P_error_of (PUSHACC n)) (P_halt_of (PUSHACC n)) (P_ccall_of (PUSHACC n)).
Proof.
  intro n.
  change (handle_instr (PUSHACC n)) with (handle_PUSHACC n).
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]].
  - (* n = 0: malformed operand *)
    unfold handler_correct; intros e le m s; simpl.
    unfold P_error_of, error_message_of. reflexivity.
  - (* n = 1 *)
    apply handler_correct_lift with
      (pe := fun _ s => nth_error (Machine.accu s :: Machine.stack s) 1 = None)
      (ph := fun _ => False) (pcc := fun _ _ _ => False).
    + exact verify_PUSHACC1_correct.
    + exact pushacc_err_1.
    + intros v [].
    + intros n0 args s' [].
  - (* n = 2 *)
    apply handler_correct_lift with
      (pe := fun _ s => nth_error (Machine.accu s :: Machine.stack s) 2 = None)
      (ph := fun _ => False) (pcc := fun _ _ _ => False).
    + exact verify_PUSHACC2_correct.
    + exact pushacc_err_2.
    + intros v [].
    + intros n0 args s' [].
  - (* n = 3 *)
    apply handler_correct_lift with
      (pe := fun _ s => nth_error (Machine.accu s :: Machine.stack s) 3 = None)
      (ph := fun _ => False) (pcc := fun _ _ _ => False).
    + exact verify_PUSHACC3_correct.
    + exact pushacc_err_3.
    + intros v [].
    + intros n0 args s' [].
  - (* n = 4 *)
    apply handler_correct_lift with
      (pe := fun _ s => nth_error (Machine.accu s :: Machine.stack s) 4 = None)
      (ph := fun _ => False) (pcc := fun _ _ _ => False).
    + exact verify_PUSHACC4_correct.
    + exact pushacc_err_4.
    + intros v [].
    + intros n0 args s' [].
  - (* n = 5 *)
    apply handler_correct_lift with
      (pe := fun _ s => nth_error (Machine.accu s :: Machine.stack s) 5 = None)
      (ph := fun _ => False) (pcc := fun _ _ _ => False).
    + exact verify_PUSHACC5_correct.
    + exact pushacc_err_5.
    + intros v [].
    + intros n0 args s' [].
  - (* n = 6 *)
    apply handler_correct_lift with
      (pe := fun _ s => nth_error (Machine.accu s :: Machine.stack s) 6 = None)
      (ph := fun _ => False) (pcc := fun _ _ _ => False).
    + exact verify_PUSHACC6_correct.
    + exact pushacc_err_6.
    + intros v [].
    + intros n0 args s' [].
  - (* n = 7 *)
    apply handler_correct_lift with
      (pe := fun _ s => nth_error (Machine.accu s :: Machine.stack s) 7 = None)
      (ph := fun _ => False) (pcc := fun _ _ _ => False).
    + exact verify_PUSHACC7_correct.
    + exact pushacc_err_7.
    + intros v [].
    + intros n0 args s' [].
  - (* n >= 8: malformed operand *)
    unfold handler_correct; intros e le m s; simpl.
    unfold P_error_of, error_message_of. reflexivity.
Qed.
