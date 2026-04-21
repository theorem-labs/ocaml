(* InstructVerificationProof.v — [UNTRUSTED] Per-constructor handler
   correctness, intentionally Admitted. checker/Bytecode/InstructChecker.v
   ascribes this module against the trusted InstructVerificationFineGrainedSpec. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat.
Import ListNotations.
From compcert Require Import AST Integers Ctypes Cop Clight ClightBigstep Events Globalenvs Memory Values.
From RecordUpdate Require Import RecordUpdate.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import Dispatch.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.

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

Definition correct_CLOSURE : forall nvars code_ofs,
  handler_correct (handle_instr (CLOSURE nvars code_ofs)) (clight_of (CLOSURE nvars code_ofs))
    (fun e m s ard => instr_wfb (CLOSURE nvars code_ofs) = true /\ pre_of (CLOSURE nvars code_ofs) e m s ard)
    (P_error_of (CLOSURE nvars code_ofs)) (P_halt_of (CLOSURE nvars code_ofs)) (P_ccall_of (CLOSURE nvars code_ofs)).
Admitted.

Definition correct_CLOSUREREC : forall nfuncs nvars code_offsets,
  handler_correct (handle_instr (CLOSUREREC nfuncs nvars code_offsets)) (clight_of (CLOSUREREC nfuncs nvars code_offsets))
    (fun e m s ard => instr_wfb (CLOSUREREC nfuncs nvars code_offsets) = true /\ pre_of (CLOSUREREC nfuncs nvars code_offsets) e m s ard)
    (P_error_of (CLOSUREREC nfuncs nvars code_offsets)) (P_halt_of (CLOSUREREC nfuncs nvars code_offsets)) (P_ccall_of (CLOSUREREC nfuncs nvars code_offsets)).
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

Definition correct_GETGLOBALFIELD : forall n p,
  handler_correct (handle_instr (GETGLOBALFIELD n p)) (clight_of (GETGLOBALFIELD n p))
    (fun e m s ard => instr_wfb (GETGLOBALFIELD n p) = true /\ pre_of (GETGLOBALFIELD n p) e m s ard)
    (P_error_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)).
Admitted.

Definition correct_PUSHGETGLOBALFIELD : forall n p,
  handler_correct (handle_instr (PUSHGETGLOBALFIELD n p)) (clight_of (PUSHGETGLOBALFIELD n p))
    (fun e m s ard => instr_wfb (PUSHGETGLOBALFIELD n p) = true /\ pre_of (PUSHGETGLOBALFIELD n p) e m s ard)
    (P_error_of (PUSHGETGLOBALFIELD n p)) (P_halt_of (PUSHGETGLOBALFIELD n p)) (P_ccall_of (PUSHGETGLOBALFIELD n p)).
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

Definition correct_MAKEBLOCK : forall t size,
  handler_correct (handle_instr (MAKEBLOCK t size)) (clight_of (MAKEBLOCK t size))
    (fun e m s ard => instr_wfb (MAKEBLOCK t size) = true /\ pre_of (MAKEBLOCK t size) e m s ard)
    (P_error_of (MAKEBLOCK t size)) (P_halt_of (MAKEBLOCK t size)) (P_ccall_of (MAKEBLOCK t size)).
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

Definition correct_SWITCH : forall nc nb const_targets block_targets,
  handler_correct (handle_instr (SWITCH nc nb const_targets block_targets)) (clight_of (SWITCH nc nb const_targets block_targets))
    (fun e m s ard => instr_wfb (SWITCH nc nb const_targets block_targets) = true /\ pre_of (SWITCH nc nb const_targets block_targets) e m s ard)
    (P_error_of (SWITCH nc nb const_targets block_targets)) (P_halt_of (SWITCH nc nb const_targets block_targets)) (P_ccall_of (SWITCH nc nb const_targets block_targets)).
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

Definition correct_C_CALL : forall nargs prim_idx,
  handler_correct (handle_instr (C_CALL nargs prim_idx)) (clight_of (C_CALL nargs prim_idx))
    (fun e m s ard => instr_wfb (C_CALL nargs prim_idx) = true /\ pre_of (C_CALL nargs prim_idx) e m s ard)
    (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)).
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
