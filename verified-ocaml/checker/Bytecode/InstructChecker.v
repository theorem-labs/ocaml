(* InstructChecker.v — Instantiation of InstructVerificationFineGrainedSpec
   and the unified InstructVerificationSpec via the functor. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import AST Integers Ctypes Cop Clight ClightBigstep Events Globalenvs Memory Values.
From RecordUpdate Require Import RecordUpdate.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.InstructSpec.


Module InstructVerification <: InstructVerificationFineGrainedSpec.

  Definition correct_ACC : forall n,
    handler_correct (handle_instr (ACC n)) (clight_of (ACC n))
      (fun e m s ard => instr_wfb (ACC n) = true /\ pre_of (ACC n) e m s ard)
      (P_error_of (ACC n)) (P_halt_of (ACC n)) (P_ccall_of (ACC n)).
  Admitted.

  Definition correct_PUSH :
    handler_correct (handle_instr PUSH) (clight_of PUSH)
      (fun e m s ard => instr_wfb PUSH = true /\ pre_of PUSH e m s ard)
      (P_error_of PUSH) (P_halt_of PUSH) (P_ccall_of PUSH).
  Admitted.

  Definition correct_PUSHACC : forall n,
    handler_correct (handle_instr (PUSHACC n)) (clight_of (PUSHACC n))
      (fun e m s ard => instr_wfb (PUSHACC n) = true /\ pre_of (PUSHACC n) e m s ard)
      (P_error_of (PUSHACC n)) (P_halt_of (PUSHACC n)) (P_ccall_of (PUSHACC n)).
  Admitted.

  Definition correct_POP : forall n,
    handler_correct (handle_instr (POP n)) (clight_of (POP n))
      (fun e m s ard => instr_wfb (POP n) = true /\ pre_of (POP n) e m s ard)
      (P_error_of (POP n)) (P_halt_of (POP n)) (P_ccall_of (POP n)).
  Admitted.

  Definition correct_ASSIGN : forall n,
    handler_correct (handle_instr (ASSIGN n)) (clight_of (ASSIGN n))
      (fun e m s ard => instr_wfb (ASSIGN n) = true /\ pre_of (ASSIGN n) e m s ard)
      (P_error_of (ASSIGN n)) (P_halt_of (ASSIGN n)) (P_ccall_of (ASSIGN n)).
  Admitted.

  Definition correct_ENVACC : forall n,
    handler_correct (handle_instr (ENVACC n)) (clight_of (ENVACC n))
      (fun e m s ard => instr_wfb (ENVACC n) = true /\ pre_of (ENVACC n) e m s ard)
      (P_error_of (ENVACC n)) (P_halt_of (ENVACC n)) (P_ccall_of (ENVACC n)).
  Admitted.

  Definition correct_PUSHENVACC : forall n,
    handler_correct (handle_instr (PUSHENVACC n)) (clight_of (PUSHENVACC n))
      (fun e m s ard => instr_wfb (PUSHENVACC n) = true /\ pre_of (PUSHENVACC n) e m s ard)
      (P_error_of (PUSHENVACC n)) (P_halt_of (PUSHENVACC n)) (P_ccall_of (PUSHENVACC n)).
  Admitted.

  Definition correct_PUSH_RETADDR : forall z,
    handler_correct (handle_instr (PUSH_RETADDR z)) (clight_of (PUSH_RETADDR z))
      (fun e m s ard => instr_wfb (PUSH_RETADDR z) = true /\ pre_of (PUSH_RETADDR z) e m s ard)
      (P_error_of (PUSH_RETADDR z)) (P_halt_of (PUSH_RETADDR z)) (P_ccall_of (PUSH_RETADDR z)).
  Admitted.

  Definition correct_APPLY : forall n,
    handler_correct (handle_instr (APPLY n)) (clight_of (APPLY n))
      (fun e m s ard => instr_wfb (APPLY n) = true /\ pre_of (APPLY n) e m s ard)
      (P_error_of (APPLY n)) (P_halt_of (APPLY n)) (P_ccall_of (APPLY n)).
  Admitted.

  Definition correct_APPLY1 :
    handler_correct (handle_instr APPLY1) (clight_of APPLY1)
      (fun e m s ard => instr_wfb APPLY1 = true /\ pre_of APPLY1 e m s ard)
      (P_error_of APPLY1) (P_halt_of APPLY1) (P_ccall_of APPLY1).
  Admitted.

  Definition correct_APPLY2 :
    handler_correct (handle_instr APPLY2) (clight_of APPLY2)
      (fun e m s ard => instr_wfb APPLY2 = true /\ pre_of APPLY2 e m s ard)
      (P_error_of APPLY2) (P_halt_of APPLY2) (P_ccall_of APPLY2).
  Admitted.

  Definition correct_APPLY3 :
    handler_correct (handle_instr APPLY3) (clight_of APPLY3)
      (fun e m s ard => instr_wfb APPLY3 = true /\ pre_of APPLY3 e m s ard)
      (P_error_of APPLY3) (P_halt_of APPLY3) (P_ccall_of APPLY3).
  Admitted.

  Definition correct_APPTERM : forall nargs slotsize,
    handler_correct (handle_instr (APPTERM nargs slotsize)) (clight_of (APPTERM nargs slotsize))
      (fun e m s ard => instr_wfb (APPTERM nargs slotsize) = true /\ pre_of (APPTERM nargs slotsize) e m s ard)
      (P_error_of (APPTERM nargs slotsize)) (P_halt_of (APPTERM nargs slotsize)) (P_ccall_of (APPTERM nargs slotsize)).
  Admitted.

  Definition correct_APPTERM1 : forall n,
    handler_correct (handle_instr (APPTERM1 n)) (clight_of (APPTERM1 n))
      (fun e m s ard => instr_wfb (APPTERM1 n) = true /\ pre_of (APPTERM1 n) e m s ard)
      (P_error_of (APPTERM1 n)) (P_halt_of (APPTERM1 n)) (P_ccall_of (APPTERM1 n)).
  Admitted.

  Definition correct_APPTERM2 : forall n,
    handler_correct (handle_instr (APPTERM2 n)) (clight_of (APPTERM2 n))
      (fun e m s ard => instr_wfb (APPTERM2 n) = true /\ pre_of (APPTERM2 n) e m s ard)
      (P_error_of (APPTERM2 n)) (P_halt_of (APPTERM2 n)) (P_ccall_of (APPTERM2 n)).
  Admitted.

  Definition correct_APPTERM3 : forall n,
    handler_correct (handle_instr (APPTERM3 n)) (clight_of (APPTERM3 n))
      (fun e m s ard => instr_wfb (APPTERM3 n) = true /\ pre_of (APPTERM3 n) e m s ard)
      (P_error_of (APPTERM3 n)) (P_halt_of (APPTERM3 n)) (P_ccall_of (APPTERM3 n)).
  Admitted.

  Definition correct_RETURN : forall n,
    handler_correct (handle_instr (RETURN n)) (clight_of (RETURN n))
      (fun e m s ard => instr_wfb (RETURN n) = true /\ pre_of (RETURN n) e m s ard)
      (P_error_of (RETURN n)) (P_halt_of (RETURN n)) (P_ccall_of (RETURN n)).
  Admitted.

  Definition correct_RESTART :
    handler_correct (handle_instr RESTART) (clight_of RESTART)
      (fun e m s ard => instr_wfb RESTART = true /\ pre_of RESTART e m s ard)
      (P_error_of RESTART) (P_halt_of RESTART) (P_ccall_of RESTART).
  Admitted.

  Definition correct_GRAB : forall n,
    handler_correct (handle_instr (GRAB n)) (clight_of (GRAB n))
      (fun e m s ard => instr_wfb (GRAB n) = true /\ pre_of (GRAB n) e m s ard)
      (P_error_of (GRAB n)) (P_halt_of (GRAB n)) (P_ccall_of (GRAB n)).
  Admitted.

  Definition correct_CLOSURE : forall n z,
    handler_correct (handle_instr (CLOSURE n z)) (clight_of (CLOSURE n z))
      (fun e m s ard => instr_wfb (CLOSURE n z) = true /\ pre_of (CLOSURE n z) e m s ard)
      (P_error_of (CLOSURE n z)) (P_halt_of (CLOSURE n z)) (P_ccall_of (CLOSURE n z)).
  Admitted.

  Definition correct_CLOSUREREC : forall n1 n2 l,
    handler_correct (handle_instr (CLOSUREREC n1 n2 l)) (clight_of (CLOSUREREC n1 n2 l))
      (fun e m s ard => instr_wfb (CLOSUREREC n1 n2 l) = true /\ pre_of (CLOSUREREC n1 n2 l) e m s ard)
      (P_error_of (CLOSUREREC n1 n2 l)) (P_halt_of (CLOSUREREC n1 n2 l)) (P_ccall_of (CLOSUREREC n1 n2 l)).
  Admitted.

  Definition correct_OFFSETCLOSURE : forall z,
    handler_correct (handle_instr (OFFSETCLOSURE z)) (clight_of (OFFSETCLOSURE z))
      (fun e m s ard => instr_wfb (OFFSETCLOSURE z) = true /\ pre_of (OFFSETCLOSURE z) e m s ard)
      (P_error_of (OFFSETCLOSURE z)) (P_halt_of (OFFSETCLOSURE z)) (P_ccall_of (OFFSETCLOSURE z)).
  Admitted.

  Definition correct_PUSHOFFSETCLOSURE : forall z,
    handler_correct (handle_instr (PUSHOFFSETCLOSURE z)) (clight_of (PUSHOFFSETCLOSURE z))
      (fun e m s ard => instr_wfb (PUSHOFFSETCLOSURE z) = true /\ pre_of (PUSHOFFSETCLOSURE z) e m s ard)
      (P_error_of (PUSHOFFSETCLOSURE z)) (P_halt_of (PUSHOFFSETCLOSURE z)) (P_ccall_of (PUSHOFFSETCLOSURE z)).
  Admitted.

  Definition correct_GETGLOBAL : forall n,
    handler_correct (handle_instr (GETGLOBAL n)) (clight_of (GETGLOBAL n))
      (fun e m s ard => instr_wfb (GETGLOBAL n) = true /\ pre_of (GETGLOBAL n) e m s ard)
      (P_error_of (GETGLOBAL n)) (P_halt_of (GETGLOBAL n)) (P_ccall_of (GETGLOBAL n)).
  Admitted.

  Definition correct_PUSHGETGLOBAL : forall n,
    handler_correct (handle_instr (PUSHGETGLOBAL n)) (clight_of (PUSHGETGLOBAL n))
      (fun e m s ard => instr_wfb (PUSHGETGLOBAL n) = true /\ pre_of (PUSHGETGLOBAL n) e m s ard)
      (P_error_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)).
  Admitted.

  Definition correct_GETGLOBALFIELD : forall n1 n2,
    handler_correct (handle_instr (GETGLOBALFIELD n1 n2)) (clight_of (GETGLOBALFIELD n1 n2))
      (fun e m s ard => instr_wfb (GETGLOBALFIELD n1 n2) = true /\ pre_of (GETGLOBALFIELD n1 n2) e m s ard)
      (P_error_of (GETGLOBALFIELD n1 n2)) (P_halt_of (GETGLOBALFIELD n1 n2)) (P_ccall_of (GETGLOBALFIELD n1 n2)).
  Admitted.

  Definition correct_PUSHGETGLOBALFIELD : forall n1 n2,
    handler_correct (handle_instr (PUSHGETGLOBALFIELD n1 n2)) (clight_of (PUSHGETGLOBALFIELD n1 n2))
      (fun e m s ard => instr_wfb (PUSHGETGLOBALFIELD n1 n2) = true /\ pre_of (PUSHGETGLOBALFIELD n1 n2) e m s ard)
      (P_error_of (PUSHGETGLOBALFIELD n1 n2)) (P_halt_of (PUSHGETGLOBALFIELD n1 n2)) (P_ccall_of (PUSHGETGLOBALFIELD n1 n2)).
  Admitted.

  Definition correct_SETGLOBAL : forall n,
    handler_correct (handle_instr (SETGLOBAL n)) (clight_of (SETGLOBAL n))
      (fun e m s ard => instr_wfb (SETGLOBAL n) = true /\ pre_of (SETGLOBAL n) e m s ard)
      (P_error_of (SETGLOBAL n)) (P_halt_of (SETGLOBAL n)) (P_ccall_of (SETGLOBAL n)).
  Admitted.

  Definition correct_ATOM : forall n,
    handler_correct (handle_instr (ATOM n)) (clight_of (ATOM n))
      (fun e m s ard => instr_wfb (ATOM n) = true /\ pre_of (ATOM n) e m s ard)
      (P_error_of (ATOM n)) (P_halt_of (ATOM n)) (P_ccall_of (ATOM n)).
  Admitted.

  Definition correct_PUSHATOM : forall n,
    handler_correct (handle_instr (PUSHATOM n)) (clight_of (PUSHATOM n))
      (fun e m s ard => instr_wfb (PUSHATOM n) = true /\ pre_of (PUSHATOM n) e m s ard)
      (P_error_of (PUSHATOM n)) (P_halt_of (PUSHATOM n)) (P_ccall_of (PUSHATOM n)).
  Admitted.

  Definition correct_MAKEBLOCK : forall n1 n2,
    handler_correct (handle_instr (MAKEBLOCK n1 n2)) (clight_of (MAKEBLOCK n1 n2))
      (fun e m s ard => instr_wfb (MAKEBLOCK n1 n2) = true /\ pre_of (MAKEBLOCK n1 n2) e m s ard)
      (P_error_of (MAKEBLOCK n1 n2)) (P_halt_of (MAKEBLOCK n1 n2)) (P_ccall_of (MAKEBLOCK n1 n2)).
  Admitted.

  Definition correct_MAKEBLOCK1 : forall n,
    handler_correct (handle_instr (MAKEBLOCK1 n)) (clight_of (MAKEBLOCK1 n))
      (fun e m s ard => instr_wfb (MAKEBLOCK1 n) = true /\ pre_of (MAKEBLOCK1 n) e m s ard)
      (P_error_of (MAKEBLOCK1 n)) (P_halt_of (MAKEBLOCK1 n)) (P_ccall_of (MAKEBLOCK1 n)).
  Admitted.

  Definition correct_MAKEBLOCK2 : forall n,
    handler_correct (handle_instr (MAKEBLOCK2 n)) (clight_of (MAKEBLOCK2 n))
      (fun e m s ard => instr_wfb (MAKEBLOCK2 n) = true /\ pre_of (MAKEBLOCK2 n) e m s ard)
      (P_error_of (MAKEBLOCK2 n)) (P_halt_of (MAKEBLOCK2 n)) (P_ccall_of (MAKEBLOCK2 n)).
  Admitted.

  Definition correct_MAKEBLOCK3 : forall n,
    handler_correct (handle_instr (MAKEBLOCK3 n)) (clight_of (MAKEBLOCK3 n))
      (fun e m s ard => instr_wfb (MAKEBLOCK3 n) = true /\ pre_of (MAKEBLOCK3 n) e m s ard)
      (P_error_of (MAKEBLOCK3 n)) (P_halt_of (MAKEBLOCK3 n)) (P_ccall_of (MAKEBLOCK3 n)).
  Admitted.

  Definition correct_MAKEFLOATBLOCK : forall n,
    handler_correct (handle_instr (MAKEFLOATBLOCK n)) (clight_of (MAKEFLOATBLOCK n))
      (fun e m s ard => instr_wfb (MAKEFLOATBLOCK n) = true /\ pre_of (MAKEFLOATBLOCK n) e m s ard)
      (P_error_of (MAKEFLOATBLOCK n)) (P_halt_of (MAKEFLOATBLOCK n)) (P_ccall_of (MAKEFLOATBLOCK n)).
  Admitted.

  Definition correct_GETFIELD : forall n,
    handler_correct (handle_instr (GETFIELD n)) (clight_of (GETFIELD n))
      (fun e m s ard => instr_wfb (GETFIELD n) = true /\ pre_of (GETFIELD n) e m s ard)
      (P_error_of (GETFIELD n)) (P_halt_of (GETFIELD n)) (P_ccall_of (GETFIELD n)).
  Admitted.

  Definition correct_GETFLOATFIELD : forall n,
    handler_correct (handle_instr (GETFLOATFIELD n)) (clight_of (GETFLOATFIELD n))
      (fun e m s ard => instr_wfb (GETFLOATFIELD n) = true /\ pre_of (GETFLOATFIELD n) e m s ard)
      (P_error_of (GETFLOATFIELD n)) (P_halt_of (GETFLOATFIELD n)) (P_ccall_of (GETFLOATFIELD n)).
  Admitted.

  Definition correct_SETFIELD : forall n,
    handler_correct (handle_instr (SETFIELD n)) (clight_of (SETFIELD n))
      (fun e m s ard => instr_wfb (SETFIELD n) = true /\ pre_of (SETFIELD n) e m s ard)
      (P_error_of (SETFIELD n)) (P_halt_of (SETFIELD n)) (P_ccall_of (SETFIELD n)).
  Admitted.

  Definition correct_SETFLOATFIELD : forall n,
    handler_correct (handle_instr (SETFLOATFIELD n)) (clight_of (SETFLOATFIELD n))
      (fun e m s ard => instr_wfb (SETFLOATFIELD n) = true /\ pre_of (SETFLOATFIELD n) e m s ard)
      (P_error_of (SETFLOATFIELD n)) (P_halt_of (SETFLOATFIELD n)) (P_ccall_of (SETFLOATFIELD n)).
  Admitted.

  Definition correct_VECTLENGTH :
    handler_correct (handle_instr VECTLENGTH) (clight_of VECTLENGTH)
      (fun e m s ard => instr_wfb VECTLENGTH = true /\ pre_of VECTLENGTH e m s ard)
      (P_error_of VECTLENGTH) (P_halt_of VECTLENGTH) (P_ccall_of VECTLENGTH).
  Admitted.

  Definition correct_GETVECTITEM :
    handler_correct (handle_instr GETVECTITEM) (clight_of GETVECTITEM)
      (fun e m s ard => instr_wfb GETVECTITEM = true /\ pre_of GETVECTITEM e m s ard)
      (P_error_of GETVECTITEM) (P_halt_of GETVECTITEM) (P_ccall_of GETVECTITEM).
  Admitted.

  Definition correct_SETVECTITEM :
    handler_correct (handle_instr SETVECTITEM) (clight_of SETVECTITEM)
      (fun e m s ard => instr_wfb SETVECTITEM = true /\ pre_of SETVECTITEM e m s ard)
      (P_error_of SETVECTITEM) (P_halt_of SETVECTITEM) (P_ccall_of SETVECTITEM).
  Admitted.

  Definition correct_GETBYTESCHAR :
    handler_correct (handle_instr GETBYTESCHAR) (clight_of GETBYTESCHAR)
      (fun e m s ard => instr_wfb GETBYTESCHAR = true /\ pre_of GETBYTESCHAR e m s ard)
      (P_error_of GETBYTESCHAR) (P_halt_of GETBYTESCHAR) (P_ccall_of GETBYTESCHAR).
  Admitted.

  Definition correct_SETBYTESCHAR :
    handler_correct (handle_instr SETBYTESCHAR) (clight_of SETBYTESCHAR)
      (fun e m s ard => instr_wfb SETBYTESCHAR = true /\ pre_of SETBYTESCHAR e m s ard)
      (P_error_of SETBYTESCHAR) (P_halt_of SETBYTESCHAR) (P_ccall_of SETBYTESCHAR).
  Admitted.

  Definition correct_GETSTRINGCHAR :
    handler_correct (handle_instr GETSTRINGCHAR) (clight_of GETSTRINGCHAR)
      (fun e m s ard => instr_wfb GETSTRINGCHAR = true /\ pre_of GETSTRINGCHAR e m s ard)
      (P_error_of GETSTRINGCHAR) (P_halt_of GETSTRINGCHAR) (P_ccall_of GETSTRINGCHAR).
  Admitted.

  Definition correct_BRANCH : forall z,
    handler_correct (handle_instr (BRANCH z)) (clight_of (BRANCH z))
      (fun e m s ard => instr_wfb (BRANCH z) = true /\ pre_of (BRANCH z) e m s ard)
      (P_error_of (BRANCH z)) (P_halt_of (BRANCH z)) (P_ccall_of (BRANCH z)).
  Admitted.

  Definition correct_BRANCHIF : forall z,
    handler_correct (handle_instr (BRANCHIF z)) (clight_of (BRANCHIF z))
      (fun e m s ard => instr_wfb (BRANCHIF z) = true /\ pre_of (BRANCHIF z) e m s ard)
      (P_error_of (BRANCHIF z)) (P_halt_of (BRANCHIF z)) (P_ccall_of (BRANCHIF z)).
  Admitted.

  Definition correct_BRANCHIFNOT : forall z,
    handler_correct (handle_instr (BRANCHIFNOT z)) (clight_of (BRANCHIFNOT z))
      (fun e m s ard => instr_wfb (BRANCHIFNOT z) = true /\ pre_of (BRANCHIFNOT z) e m s ard)
      (P_error_of (BRANCHIFNOT z)) (P_halt_of (BRANCHIFNOT z)) (P_ccall_of (BRANCHIFNOT z)).
  Admitted.

  Definition correct_SWITCH : forall n1 n2 l1 l2,
    handler_correct (handle_instr (SWITCH n1 n2 l1 l2)) (clight_of (SWITCH n1 n2 l1 l2))
      (fun e m s ard => instr_wfb (SWITCH n1 n2 l1 l2) = true /\ pre_of (SWITCH n1 n2 l1 l2) e m s ard)
      (P_error_of (SWITCH n1 n2 l1 l2)) (P_halt_of (SWITCH n1 n2 l1 l2)) (P_ccall_of (SWITCH n1 n2 l1 l2)).
  Admitted.

  Definition correct_BOOLNOT :
    handler_correct (handle_instr BOOLNOT) (clight_of BOOLNOT)
      (fun e m s ard => instr_wfb BOOLNOT = true /\ pre_of BOOLNOT e m s ard)
      (P_error_of BOOLNOT) (P_halt_of BOOLNOT) (P_ccall_of BOOLNOT).
  Admitted.

  Definition correct_PUSHTRAP : forall z,
    handler_correct (handle_instr (PUSHTRAP z)) (clight_of (PUSHTRAP z))
      (fun e m s ard => instr_wfb (PUSHTRAP z) = true /\ pre_of (PUSHTRAP z) e m s ard)
      (P_error_of (PUSHTRAP z)) (P_halt_of (PUSHTRAP z)) (P_ccall_of (PUSHTRAP z)).
  Admitted.

  Definition correct_POPTRAP :
    handler_correct (handle_instr POPTRAP) (clight_of POPTRAP)
      (fun e m s ard => instr_wfb POPTRAP = true /\ pre_of POPTRAP e m s ard)
      (P_error_of POPTRAP) (P_halt_of POPTRAP) (P_ccall_of POPTRAP).
  Admitted.

  Definition correct_RAISE :
    handler_correct (handle_instr RAISE) (clight_of RAISE)
      (fun e m s ard => instr_wfb RAISE = true /\ pre_of RAISE e m s ard)
      (P_error_of RAISE) (P_halt_of RAISE) (P_ccall_of RAISE).
  Admitted.

  Definition correct_RERAISE :
    handler_correct (handle_instr RERAISE) (clight_of RERAISE)
      (fun e m s ard => instr_wfb RERAISE = true /\ pre_of RERAISE e m s ard)
      (P_error_of RERAISE) (P_halt_of RERAISE) (P_ccall_of RERAISE).
  Admitted.

  Definition correct_RAISE_NOTRACE :
    handler_correct (handle_instr RAISE_NOTRACE) (clight_of RAISE_NOTRACE)
      (fun e m s ard => instr_wfb RAISE_NOTRACE = true /\ pre_of RAISE_NOTRACE e m s ard)
      (P_error_of RAISE_NOTRACE) (P_halt_of RAISE_NOTRACE) (P_ccall_of RAISE_NOTRACE).
  Admitted.

  Definition correct_CHECK_SIGNALS :
    handler_correct (handle_instr CHECK_SIGNALS) (clight_of CHECK_SIGNALS)
      (fun e m s ard => instr_wfb CHECK_SIGNALS = true /\ pre_of CHECK_SIGNALS e m s ard)
      (P_error_of CHECK_SIGNALS) (P_halt_of CHECK_SIGNALS) (P_ccall_of CHECK_SIGNALS).
  Admitted.

  Definition correct_C_CALL : forall n1 n2,
    handler_correct (handle_instr (C_CALL n1 n2)) (clight_of (C_CALL n1 n2))
      (fun e m s ard => instr_wfb (C_CALL n1 n2) = true /\ pre_of (C_CALL n1 n2) e m s ard)
      (P_error_of (C_CALL n1 n2)) (P_halt_of (C_CALL n1 n2)) (P_ccall_of (C_CALL n1 n2)).
  Admitted.

  Definition correct_CONSTINT : forall z,
    handler_correct (handle_instr (CONSTINT z)) (clight_of (CONSTINT z))
      (fun e m s ard => instr_wfb (CONSTINT z) = true /\ pre_of (CONSTINT z) e m s ard)
      (P_error_of (CONSTINT z)) (P_halt_of (CONSTINT z)) (P_ccall_of (CONSTINT z)).
  Admitted.

  Definition correct_PUSHCONSTINT : forall z,
    handler_correct (handle_instr (PUSHCONSTINT z)) (clight_of (PUSHCONSTINT z))
      (fun e m s ard => instr_wfb (PUSHCONSTINT z) = true /\ pre_of (PUSHCONSTINT z) e m s ard)
      (P_error_of (PUSHCONSTINT z)) (P_halt_of (PUSHCONSTINT z)) (P_ccall_of (PUSHCONSTINT z)).
  Admitted.

  Definition correct_NEGINT :
    handler_correct (handle_instr NEGINT) (clight_of NEGINT)
      (fun e m s ard => instr_wfb NEGINT = true /\ pre_of NEGINT e m s ard)
      (P_error_of NEGINT) (P_halt_of NEGINT) (P_ccall_of NEGINT).
  Admitted.

  Definition correct_ADDINT :
    handler_correct (handle_instr ADDINT) (clight_of ADDINT)
      (fun e m s ard => instr_wfb ADDINT = true /\ pre_of ADDINT e m s ard)
      (P_error_of ADDINT) (P_halt_of ADDINT) (P_ccall_of ADDINT).
  Admitted.

  Definition correct_SUBINT :
    handler_correct (handle_instr SUBINT) (clight_of SUBINT)
      (fun e m s ard => instr_wfb SUBINT = true /\ pre_of SUBINT e m s ard)
      (P_error_of SUBINT) (P_halt_of SUBINT) (P_ccall_of SUBINT).
  Admitted.

  Definition correct_MULINT :
    handler_correct (handle_instr MULINT) (clight_of MULINT)
      (fun e m s ard => instr_wfb MULINT = true /\ pre_of MULINT e m s ard)
      (P_error_of MULINT) (P_halt_of MULINT) (P_ccall_of MULINT).
  Admitted.

  Definition correct_DIVINT :
    handler_correct (handle_instr DIVINT) (clight_of DIVINT)
      (fun e m s ard => instr_wfb DIVINT = true /\ pre_of DIVINT e m s ard)
      (P_error_of DIVINT) (P_halt_of DIVINT) (P_ccall_of DIVINT).
  Admitted.

  Definition correct_MODINT :
    handler_correct (handle_instr MODINT) (clight_of MODINT)
      (fun e m s ard => instr_wfb MODINT = true /\ pre_of MODINT e m s ard)
      (P_error_of MODINT) (P_halt_of MODINT) (P_ccall_of MODINT).
  Admitted.

  Definition correct_ANDINT :
    handler_correct (handle_instr ANDINT) (clight_of ANDINT)
      (fun e m s ard => instr_wfb ANDINT = true /\ pre_of ANDINT e m s ard)
      (P_error_of ANDINT) (P_halt_of ANDINT) (P_ccall_of ANDINT).
  Admitted.

  Definition correct_ORINT :
    handler_correct (handle_instr ORINT) (clight_of ORINT)
      (fun e m s ard => instr_wfb ORINT = true /\ pre_of ORINT e m s ard)
      (P_error_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT).
  Admitted.

  Definition correct_XORINT :
    handler_correct (handle_instr XORINT) (clight_of XORINT)
      (fun e m s ard => instr_wfb XORINT = true /\ pre_of XORINT e m s ard)
      (P_error_of XORINT) (P_halt_of XORINT) (P_ccall_of XORINT).
  Admitted.

  Definition correct_LSLINT :
    handler_correct (handle_instr LSLINT) (clight_of LSLINT)
      (fun e m s ard => instr_wfb LSLINT = true /\ pre_of LSLINT e m s ard)
      (P_error_of LSLINT) (P_halt_of LSLINT) (P_ccall_of LSLINT).
  Admitted.

  Definition correct_LSRINT :
    handler_correct (handle_instr LSRINT) (clight_of LSRINT)
      (fun e m s ard => instr_wfb LSRINT = true /\ pre_of LSRINT e m s ard)
      (P_error_of LSRINT) (P_halt_of LSRINT) (P_ccall_of LSRINT).
  Admitted.

  Definition correct_ASRINT :
    handler_correct (handle_instr ASRINT) (clight_of ASRINT)
      (fun e m s ard => instr_wfb ASRINT = true /\ pre_of ASRINT e m s ard)
      (P_error_of ASRINT) (P_halt_of ASRINT) (P_ccall_of ASRINT).
  Admitted.

  Definition correct_EQ :
    handler_correct (handle_instr EQ) (clight_of EQ)
      (fun e m s ard => instr_wfb EQ = true /\ pre_of EQ e m s ard)
      (P_error_of EQ) (P_halt_of EQ) (P_ccall_of EQ).
  Admitted.

  Definition correct_NEQ :
    handler_correct (handle_instr NEQ) (clight_of NEQ)
      (fun e m s ard => instr_wfb NEQ = true /\ pre_of NEQ e m s ard)
      (P_error_of NEQ) (P_halt_of NEQ) (P_ccall_of NEQ).
  Admitted.

  Definition correct_LTINT :
    handler_correct (handle_instr LTINT) (clight_of LTINT)
      (fun e m s ard => instr_wfb LTINT = true /\ pre_of LTINT e m s ard)
      (P_error_of LTINT) (P_halt_of LTINT) (P_ccall_of LTINT).
  Admitted.

  Definition correct_LEINT :
    handler_correct (handle_instr LEINT) (clight_of LEINT)
      (fun e m s ard => instr_wfb LEINT = true /\ pre_of LEINT e m s ard)
      (P_error_of LEINT) (P_halt_of LEINT) (P_ccall_of LEINT).
  Admitted.

  Definition correct_GTINT :
    handler_correct (handle_instr GTINT) (clight_of GTINT)
      (fun e m s ard => instr_wfb GTINT = true /\ pre_of GTINT e m s ard)
      (P_error_of GTINT) (P_halt_of GTINT) (P_ccall_of GTINT).
  Admitted.

  Definition correct_GEINT :
    handler_correct (handle_instr GEINT) (clight_of GEINT)
      (fun e m s ard => instr_wfb GEINT = true /\ pre_of GEINT e m s ard)
      (P_error_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT).
  Admitted.

  Definition correct_OFFSETINT : forall z,
    handler_correct (handle_instr (OFFSETINT z)) (clight_of (OFFSETINT z))
      (fun e m s ard => instr_wfb (OFFSETINT z) = true /\ pre_of (OFFSETINT z) e m s ard)
      (P_error_of (OFFSETINT z)) (P_halt_of (OFFSETINT z)) (P_ccall_of (OFFSETINT z)).
  Admitted.

  Definition correct_OFFSETREF : forall z,
    handler_correct (handle_instr (OFFSETREF z)) (clight_of (OFFSETREF z))
      (fun e m s ard => instr_wfb (OFFSETREF z) = true /\ pre_of (OFFSETREF z) e m s ard)
      (P_error_of (OFFSETREF z)) (P_halt_of (OFFSETREF z)) (P_ccall_of (OFFSETREF z)).
  Admitted.

  Definition correct_ISINT :
    handler_correct (handle_instr ISINT) (clight_of ISINT)
      (fun e m s ard => instr_wfb ISINT = true /\ pre_of ISINT e m s ard)
      (P_error_of ISINT) (P_halt_of ISINT) (P_ccall_of ISINT).
  Admitted.

  Definition correct_GETMETHOD :
    handler_correct (handle_instr GETMETHOD) (clight_of GETMETHOD)
      (fun e m s ard => instr_wfb GETMETHOD = true /\ pre_of GETMETHOD e m s ard)
      (P_error_of GETMETHOD) (P_halt_of GETMETHOD) (P_ccall_of GETMETHOD).
  Admitted.

  Definition correct_GETPUBMET : forall z,
    handler_correct (handle_instr (GETPUBMET z)) (clight_of (GETPUBMET z))
      (fun e m s ard => instr_wfb (GETPUBMET z) = true /\ pre_of (GETPUBMET z) e m s ard)
      (P_error_of (GETPUBMET z)) (P_halt_of (GETPUBMET z)) (P_ccall_of (GETPUBMET z)).
  Admitted.

  Definition correct_GETDYNMET :
    handler_correct (handle_instr GETDYNMET) (clight_of GETDYNMET)
      (fun e m s ard => instr_wfb GETDYNMET = true /\ pre_of GETDYNMET e m s ard)
      (P_error_of GETDYNMET) (P_halt_of GETDYNMET) (P_ccall_of GETDYNMET).
  Admitted.

  Definition correct_BEQ : forall z1 z2,
    handler_correct (handle_instr (BEQ z1 z2)) (clight_of (BEQ z1 z2))
      (fun e m s ard => instr_wfb (BEQ z1 z2) = true /\ pre_of (BEQ z1 z2) e m s ard)
      (P_error_of (BEQ z1 z2)) (P_halt_of (BEQ z1 z2)) (P_ccall_of (BEQ z1 z2)).
  Admitted.

  Definition correct_BNEQ : forall z1 z2,
    handler_correct (handle_instr (BNEQ z1 z2)) (clight_of (BNEQ z1 z2))
      (fun e m s ard => instr_wfb (BNEQ z1 z2) = true /\ pre_of (BNEQ z1 z2) e m s ard)
      (P_error_of (BNEQ z1 z2)) (P_halt_of (BNEQ z1 z2)) (P_ccall_of (BNEQ z1 z2)).
  Admitted.

  Definition correct_BLTINT : forall z1 z2,
    handler_correct (handle_instr (BLTINT z1 z2)) (clight_of (BLTINT z1 z2))
      (fun e m s ard => instr_wfb (BLTINT z1 z2) = true /\ pre_of (BLTINT z1 z2) e m s ard)
      (P_error_of (BLTINT z1 z2)) (P_halt_of (BLTINT z1 z2)) (P_ccall_of (BLTINT z1 z2)).
  Admitted.

  Definition correct_BLEINT : forall z1 z2,
    handler_correct (handle_instr (BLEINT z1 z2)) (clight_of (BLEINT z1 z2))
      (fun e m s ard => instr_wfb (BLEINT z1 z2) = true /\ pre_of (BLEINT z1 z2) e m s ard)
      (P_error_of (BLEINT z1 z2)) (P_halt_of (BLEINT z1 z2)) (P_ccall_of (BLEINT z1 z2)).
  Admitted.

  Definition correct_BGTINT : forall z1 z2,
    handler_correct (handle_instr (BGTINT z1 z2)) (clight_of (BGTINT z1 z2))
      (fun e m s ard => instr_wfb (BGTINT z1 z2) = true /\ pre_of (BGTINT z1 z2) e m s ard)
      (P_error_of (BGTINT z1 z2)) (P_halt_of (BGTINT z1 z2)) (P_ccall_of (BGTINT z1 z2)).
  Admitted.

  Definition correct_BGEINT : forall z1 z2,
    handler_correct (handle_instr (BGEINT z1 z2)) (clight_of (BGEINT z1 z2))
      (fun e m s ard => instr_wfb (BGEINT z1 z2) = true /\ pre_of (BGEINT z1 z2) e m s ard)
      (P_error_of (BGEINT z1 z2)) (P_halt_of (BGEINT z1 z2)) (P_ccall_of (BGEINT z1 z2)).
  Admitted.

  Definition correct_ULTINT :
    handler_correct (handle_instr ULTINT) (clight_of ULTINT)
      (fun e m s ard => instr_wfb ULTINT = true /\ pre_of ULTINT e m s ard)
      (P_error_of ULTINT) (P_halt_of ULTINT) (P_ccall_of ULTINT).
  Admitted.

  Definition correct_UGEINT :
    handler_correct (handle_instr UGEINT) (clight_of UGEINT)
      (fun e m s ard => instr_wfb UGEINT = true /\ pre_of UGEINT e m s ard)
      (P_error_of UGEINT) (P_halt_of UGEINT) (P_ccall_of UGEINT).
  Admitted.

  Definition correct_BULTINT : forall z1 z2,
    handler_correct (handle_instr (BULTINT z1 z2)) (clight_of (BULTINT z1 z2))
      (fun e m s ard => instr_wfb (BULTINT z1 z2) = true /\ pre_of (BULTINT z1 z2) e m s ard)
      (P_error_of (BULTINT z1 z2)) (P_halt_of (BULTINT z1 z2)) (P_ccall_of (BULTINT z1 z2)).
  Admitted.

  Definition correct_BUGEINT : forall z1 z2,
    handler_correct (handle_instr (BUGEINT z1 z2)) (clight_of (BUGEINT z1 z2))
      (fun e m s ard => instr_wfb (BUGEINT z1 z2) = true /\ pre_of (BUGEINT z1 z2) e m s ard)
      (P_error_of (BUGEINT z1 z2)) (P_halt_of (BUGEINT z1 z2)) (P_ccall_of (BUGEINT z1 z2)).
  Admitted.

  Definition correct_STOP :
    handler_correct (handle_instr STOP) (clight_of STOP)
      (fun e m s ard => instr_wfb STOP = true /\ pre_of STOP e m s ard)
      (P_error_of STOP) (P_halt_of STOP) (P_ccall_of STOP).
  Admitted.

  Section __.
  Set Printing All.
  Set Printing Fully Qualified.
  Set Printing Depth 10000000000.
  Set Printing Width 2000.
  Goal True.
    idtac "<correct_ACC>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ACC.
    idtac "</PrintAssumptions>".
    idtac "</correct_ACC>".
  Abort.
  Goal True.
    idtac "<correct_PUSH>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSH.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSH>".
  Abort.
  Goal True.
    idtac "<correct_PUSHACC>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHACC.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHACC>".
  Abort.
  Goal True.
    idtac "<correct_POP>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_POP.
    idtac "</PrintAssumptions>".
    idtac "</correct_POP>".
  Abort.
  Goal True.
    idtac "<correct_ASSIGN>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ASSIGN.
    idtac "</PrintAssumptions>".
    idtac "</correct_ASSIGN>".
  Abort.
  Goal True.
    idtac "<correct_ENVACC>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ENVACC.
    idtac "</PrintAssumptions>".
    idtac "</correct_ENVACC>".
  Abort.
  Goal True.
    idtac "<correct_PUSHENVACC>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHENVACC.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHENVACC>".
  Abort.
  Goal True.
    idtac "<correct_PUSH_RETADDR>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSH_RETADDR.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSH_RETADDR>".
  Abort.
  Goal True.
    idtac "<correct_APPLY>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_APPLY.
    idtac "</PrintAssumptions>".
    idtac "</correct_APPLY>".
  Abort.
  Goal True.
    idtac "<correct_APPLY1>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_APPLY1.
    idtac "</PrintAssumptions>".
    idtac "</correct_APPLY1>".
  Abort.
  Goal True.
    idtac "<correct_APPLY2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_APPLY2.
    idtac "</PrintAssumptions>".
    idtac "</correct_APPLY2>".
  Abort.
  Goal True.
    idtac "<correct_APPLY3>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_APPLY3.
    idtac "</PrintAssumptions>".
    idtac "</correct_APPLY3>".
  Abort.
  Goal True.
    idtac "<correct_APPTERM>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_APPTERM.
    idtac "</PrintAssumptions>".
    idtac "</correct_APPTERM>".
  Abort.
  Goal True.
    idtac "<correct_APPTERM1>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_APPTERM1.
    idtac "</PrintAssumptions>".
    idtac "</correct_APPTERM1>".
  Abort.
  Goal True.
    idtac "<correct_APPTERM2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_APPTERM2.
    idtac "</PrintAssumptions>".
    idtac "</correct_APPTERM2>".
  Abort.
  Goal True.
    idtac "<correct_APPTERM3>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_APPTERM3.
    idtac "</PrintAssumptions>".
    idtac "</correct_APPTERM3>".
  Abort.
  Goal True.
    idtac "<correct_RETURN>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_RETURN.
    idtac "</PrintAssumptions>".
    idtac "</correct_RETURN>".
  Abort.
  Goal True.
    idtac "<correct_RESTART>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_RESTART.
    idtac "</PrintAssumptions>".
    idtac "</correct_RESTART>".
  Abort.
  Goal True.
    idtac "<correct_GRAB>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GRAB.
    idtac "</PrintAssumptions>".
    idtac "</correct_GRAB>".
  Abort.
  Goal True.
    idtac "<correct_CLOSURE>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_CLOSURE.
    idtac "</PrintAssumptions>".
    idtac "</correct_CLOSURE>".
  Abort.
  Goal True.
    idtac "<correct_CLOSUREREC>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_CLOSUREREC.
    idtac "</PrintAssumptions>".
    idtac "</correct_CLOSUREREC>".
  Abort.
  Goal True.
    idtac "<correct_OFFSETCLOSURE>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_OFFSETCLOSURE.
    idtac "</PrintAssumptions>".
    idtac "</correct_OFFSETCLOSURE>".
  Abort.
  Goal True.
    idtac "<correct_PUSHOFFSETCLOSURE>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHOFFSETCLOSURE.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHOFFSETCLOSURE>".
  Abort.
  Goal True.
    idtac "<correct_GETGLOBAL>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETGLOBAL.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETGLOBAL>".
  Abort.
  Goal True.
    idtac "<correct_PUSHGETGLOBAL>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHGETGLOBAL.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHGETGLOBAL>".
  Abort.
  Goal True.
    idtac "<correct_GETGLOBALFIELD>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETGLOBALFIELD.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETGLOBALFIELD>".
  Abort.
  Goal True.
    idtac "<correct_PUSHGETGLOBALFIELD>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHGETGLOBALFIELD.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHGETGLOBALFIELD>".
  Abort.
  Goal True.
    idtac "<correct_SETGLOBAL>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SETGLOBAL.
    idtac "</PrintAssumptions>".
    idtac "</correct_SETGLOBAL>".
  Abort.
  Goal True.
    idtac "<correct_ATOM>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ATOM.
    idtac "</PrintAssumptions>".
    idtac "</correct_ATOM>".
  Abort.
  Goal True.
    idtac "<correct_PUSHATOM>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHATOM.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHATOM>".
  Abort.
  Goal True.
    idtac "<correct_MAKEBLOCK>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_MAKEBLOCK.
    idtac "</PrintAssumptions>".
    idtac "</correct_MAKEBLOCK>".
  Abort.
  Goal True.
    idtac "<correct_MAKEBLOCK1>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_MAKEBLOCK1.
    idtac "</PrintAssumptions>".
    idtac "</correct_MAKEBLOCK1>".
  Abort.
  Goal True.
    idtac "<correct_MAKEBLOCK2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_MAKEBLOCK2.
    idtac "</PrintAssumptions>".
    idtac "</correct_MAKEBLOCK2>".
  Abort.
  Goal True.
    idtac "<correct_MAKEBLOCK3>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_MAKEBLOCK3.
    idtac "</PrintAssumptions>".
    idtac "</correct_MAKEBLOCK3>".
  Abort.
  Goal True.
    idtac "<correct_MAKEFLOATBLOCK>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_MAKEFLOATBLOCK.
    idtac "</PrintAssumptions>".
    idtac "</correct_MAKEFLOATBLOCK>".
  Abort.
  Goal True.
    idtac "<correct_GETFIELD>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETFIELD.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETFIELD>".
  Abort.
  Goal True.
    idtac "<correct_GETFLOATFIELD>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETFLOATFIELD.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETFLOATFIELD>".
  Abort.
  Goal True.
    idtac "<correct_SETFIELD>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SETFIELD.
    idtac "</PrintAssumptions>".
    idtac "</correct_SETFIELD>".
  Abort.
  Goal True.
    idtac "<correct_SETFLOATFIELD>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SETFLOATFIELD.
    idtac "</PrintAssumptions>".
    idtac "</correct_SETFLOATFIELD>".
  Abort.
  Goal True.
    idtac "<correct_VECTLENGTH>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_VECTLENGTH.
    idtac "</PrintAssumptions>".
    idtac "</correct_VECTLENGTH>".
  Abort.
  Goal True.
    idtac "<correct_GETVECTITEM>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETVECTITEM.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETVECTITEM>".
  Abort.
  Goal True.
    idtac "<correct_SETVECTITEM>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SETVECTITEM.
    idtac "</PrintAssumptions>".
    idtac "</correct_SETVECTITEM>".
  Abort.
  Goal True.
    idtac "<correct_GETBYTESCHAR>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETBYTESCHAR.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETBYTESCHAR>".
  Abort.
  Goal True.
    idtac "<correct_SETBYTESCHAR>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SETBYTESCHAR.
    idtac "</PrintAssumptions>".
    idtac "</correct_SETBYTESCHAR>".
  Abort.
  Goal True.
    idtac "<correct_GETSTRINGCHAR>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETSTRINGCHAR.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETSTRINGCHAR>".
  Abort.
  Goal True.
    idtac "<correct_BRANCH>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BRANCH.
    idtac "</PrintAssumptions>".
    idtac "</correct_BRANCH>".
  Abort.
  Goal True.
    idtac "<correct_BRANCHIF>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BRANCHIF.
    idtac "</PrintAssumptions>".
    idtac "</correct_BRANCHIF>".
  Abort.
  Goal True.
    idtac "<correct_BRANCHIFNOT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BRANCHIFNOT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BRANCHIFNOT>".
  Abort.
  Goal True.
    idtac "<correct_SWITCH>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SWITCH.
    idtac "</PrintAssumptions>".
    idtac "</correct_SWITCH>".
  Abort.
  Goal True.
    idtac "<correct_BOOLNOT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BOOLNOT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BOOLNOT>".
  Abort.
  Goal True.
    idtac "<correct_PUSHTRAP>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHTRAP.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHTRAP>".
  Abort.
  Goal True.
    idtac "<correct_POPTRAP>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_POPTRAP.
    idtac "</PrintAssumptions>".
    idtac "</correct_POPTRAP>".
  Abort.
  Goal True.
    idtac "<correct_RAISE>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_RAISE.
    idtac "</PrintAssumptions>".
    idtac "</correct_RAISE>".
  Abort.
  Goal True.
    idtac "<correct_RERAISE>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_RERAISE.
    idtac "</PrintAssumptions>".
    idtac "</correct_RERAISE>".
  Abort.
  Goal True.
    idtac "<correct_RAISE_NOTRACE>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_RAISE_NOTRACE.
    idtac "</PrintAssumptions>".
    idtac "</correct_RAISE_NOTRACE>".
  Abort.
  Goal True.
    idtac "<correct_CHECK_SIGNALS>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_CHECK_SIGNALS.
    idtac "</PrintAssumptions>".
    idtac "</correct_CHECK_SIGNALS>".
  Abort.
  Goal True.
    idtac "<correct_C_CALL>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_C_CALL.
    idtac "</PrintAssumptions>".
    idtac "</correct_C_CALL>".
  Abort.
  Goal True.
    idtac "<correct_CONSTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_CONSTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_CONSTINT>".
  Abort.
  Goal True.
    idtac "<correct_PUSHCONSTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHCONSTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHCONSTINT>".
  Abort.
  Goal True.
    idtac "<correct_NEGINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_NEGINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_NEGINT>".
  Abort.
  Goal True.
    idtac "<correct_ADDINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ADDINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_ADDINT>".
  Abort.
  Goal True.
    idtac "<correct_SUBINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SUBINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_SUBINT>".
  Abort.
  Goal True.
    idtac "<correct_MULINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_MULINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_MULINT>".
  Abort.
  Goal True.
    idtac "<correct_DIVINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_DIVINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_DIVINT>".
  Abort.
  Goal True.
    idtac "<correct_MODINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_MODINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_MODINT>".
  Abort.
  Goal True.
    idtac "<correct_ANDINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ANDINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_ANDINT>".
  Abort.
  Goal True.
    idtac "<correct_ORINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ORINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_ORINT>".
  Abort.
  Goal True.
    idtac "<correct_XORINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_XORINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_XORINT>".
  Abort.
  Goal True.
    idtac "<correct_LSLINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_LSLINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_LSLINT>".
  Abort.
  Goal True.
    idtac "<correct_LSRINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_LSRINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_LSRINT>".
  Abort.
  Goal True.
    idtac "<correct_ASRINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ASRINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_ASRINT>".
  Abort.
  Goal True.
    idtac "<correct_EQ>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_EQ.
    idtac "</PrintAssumptions>".
    idtac "</correct_EQ>".
  Abort.
  Goal True.
    idtac "<correct_NEQ>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_NEQ.
    idtac "</PrintAssumptions>".
    idtac "</correct_NEQ>".
  Abort.
  Goal True.
    idtac "<correct_LTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_LTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_LTINT>".
  Abort.
  Goal True.
    idtac "<correct_LEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_LEINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_LEINT>".
  Abort.
  Goal True.
    idtac "<correct_GTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_GTINT>".
  Abort.
  Goal True.
    idtac "<correct_GEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GEINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_GEINT>".
  Abort.
  Goal True.
    idtac "<correct_OFFSETINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_OFFSETINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_OFFSETINT>".
  Abort.
  Goal True.
    idtac "<correct_OFFSETREF>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_OFFSETREF.
    idtac "</PrintAssumptions>".
    idtac "</correct_OFFSETREF>".
  Abort.
  Goal True.
    idtac "<correct_ISINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ISINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_ISINT>".
  Abort.
  Goal True.
    idtac "<correct_GETMETHOD>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETMETHOD.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETMETHOD>".
  Abort.
  Goal True.
    idtac "<correct_GETPUBMET>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETPUBMET.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETPUBMET>".
  Abort.
  Goal True.
    idtac "<correct_GETDYNMET>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETDYNMET.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETDYNMET>".
  Abort.
  Goal True.
    idtac "<correct_BEQ>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BEQ.
    idtac "</PrintAssumptions>".
    idtac "</correct_BEQ>".
  Abort.
  Goal True.
    idtac "<correct_BNEQ>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BNEQ.
    idtac "</PrintAssumptions>".
    idtac "</correct_BNEQ>".
  Abort.
  Goal True.
    idtac "<correct_BLTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BLTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BLTINT>".
  Abort.
  Goal True.
    idtac "<correct_BLEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BLEINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BLEINT>".
  Abort.
  Goal True.
    idtac "<correct_BGTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BGTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BGTINT>".
  Abort.
  Goal True.
    idtac "<correct_BGEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BGEINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BGEINT>".
  Abort.
  Goal True.
    idtac "<correct_ULTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ULTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_ULTINT>".
  Abort.
  Goal True.
    idtac "<correct_UGEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_UGEINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_UGEINT>".
  Abort.
  Goal True.
    idtac "<correct_BULTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BULTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BULTINT>".
  Abort.
  Goal True.
    idtac "<correct_BUGEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BUGEINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BUGEINT>".
  Abort.
  Goal True.
    idtac "<correct_STOP>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_STOP.
    idtac "</PrintAssumptions>".
    idtac "</correct_STOP>".
  Abort.
  End __.
End InstructVerification.

Module InstructVerificationUnified :=
  InstructVerificationFromFineGrained InstructVerification.

Section __.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True.
  idtac "<handler_correct_all>".
  idtac "<PrintAssumptions>".
  Print Assumptions InstructVerificationUnified.handler_correct_all.
  idtac "</PrintAssumptions>".
  idtac "</handler_correct_all>".
Abort.
End __.
