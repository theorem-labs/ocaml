(* InstructVerificationProof.v — [UNTRUSTED] Per-constructor handler
   correctness, intentionally Admitted. checker/Bytecode/InstructChecker.v
   ascribes this module against the trusted InstructVerificationFineGrainedSpec. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat.
From compcert Require Import AST Integers Ctypes Cop Clight ClightBigstep Events Globalenvs Memory Values.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
From OCamlInterp.Manual.Bytecode.Interpret Require Import HandleInstrSpec.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic.Bytecode.InstructVerification Require Import STOP_correct.
From OCamlInterp.Automatic.Bytecode.InstructVerification Require Import CHECK_SIGNALS_correct.
From OCamlInterp.Automatic.Bytecode.InstructVerification Require Import C_CALL_correct.

Module DispatchHI <: HandleInstrSpec.
  Definition handle_instr := Dispatch.handle_instr.
End DispatchHI.

Definition correct_ACC : forall n,
  handler_correct (handle_instr (ACC n)) (clight_of (ACC n))
    (error_message_of (ACC n))
    (pre_of (ACC n)) (P_halt_of (ACC n)) (P_ccall_of (ACC n)).
Proof. Admitted.

Definition correct_PUSH :
  handler_correct (handle_instr PUSH) (clight_of PUSH)
    (error_message_of PUSH)
    (pre_of PUSH) (P_halt_of PUSH) (P_ccall_of PUSH).
Proof. Admitted.

Definition correct_PUSHACC : forall n,
  handler_correct (handle_instr (PUSHACC n)) (clight_of (PUSHACC n))
    (error_message_of (PUSHACC n))
    (pre_of (PUSHACC n)) (P_halt_of (PUSHACC n)) (P_ccall_of (PUSHACC n)).
Proof. Admitted.

Definition correct_POP : forall n,
  handler_correct (handle_instr (POP n)) (clight_of (POP n))
    (error_message_of (POP n))
    (pre_of (POP n)) (P_halt_of (POP n)) (P_ccall_of (POP n)).
Proof. Admitted.

Definition correct_ASSIGN : forall n,
  handler_correct (handle_instr (ASSIGN n)) (clight_of (ASSIGN n))
    (error_message_of (ASSIGN n))
    (pre_of (ASSIGN n)) (P_halt_of (ASSIGN n)) (P_ccall_of (ASSIGN n)).
Proof. Admitted.

Definition correct_ENVACC : forall n,
  handler_correct (handle_instr (ENVACC n)) (clight_of (ENVACC n))
    (error_message_of (ENVACC n))
    (pre_of (ENVACC n)) (P_halt_of (ENVACC n)) (P_ccall_of (ENVACC n)).
Proof. Admitted.

Definition correct_PUSHENVACC : forall n,
  handler_correct (handle_instr (PUSHENVACC n)) (clight_of (PUSHENVACC n))
    (error_message_of (PUSHENVACC n))
    (pre_of (PUSHENVACC n)) (P_halt_of (PUSHENVACC n)) (P_ccall_of (PUSHENVACC n)).
Proof. Admitted.

Definition correct_PUSH_RETADDR : forall z,
  handler_correct (handle_instr (PUSH_RETADDR z)) (clight_of (PUSH_RETADDR z))
    (error_message_of (PUSH_RETADDR z))
    (pre_of (PUSH_RETADDR z)) (P_halt_of (PUSH_RETADDR z)) (P_ccall_of (PUSH_RETADDR z)).
Proof. Admitted.

Definition correct_APPLY : forall n,
  handler_correct (handle_instr (APPLY n)) (clight_of (APPLY n))
    (error_message_of (APPLY n))
    (pre_of (APPLY n)) (P_halt_of (APPLY n)) (P_ccall_of (APPLY n)).
Proof. Admitted.

Definition correct_APPLY1 :
  handler_correct (handle_instr APPLY1) (clight_of APPLY1)
    (error_message_of APPLY1)
    (pre_of APPLY1) (P_halt_of APPLY1) (P_ccall_of APPLY1).
Proof. Admitted.

Definition correct_APPLY2 :
  handler_correct (handle_instr APPLY2) (clight_of APPLY2)
    (error_message_of APPLY2)
    (pre_of APPLY2) (P_halt_of APPLY2) (P_ccall_of APPLY2).
Proof. Admitted.

Definition correct_APPLY3 :
  handler_correct (handle_instr APPLY3) (clight_of APPLY3)
    (error_message_of APPLY3)
    (pre_of APPLY3) (P_halt_of APPLY3) (P_ccall_of APPLY3).
Proof. Admitted.

Definition correct_APPTERM : forall nargs slotsize,
  handler_correct (handle_instr (APPTERM nargs slotsize)) (clight_of (APPTERM nargs slotsize))
    (error_message_of (APPTERM nargs slotsize))
    (pre_of (APPTERM nargs slotsize)) (P_halt_of (APPTERM nargs slotsize)) (P_ccall_of (APPTERM nargs slotsize)).
Proof. Admitted.

Definition correct_APPTERM1 : forall n,
  handler_correct (handle_instr (APPTERM1 n)) (clight_of (APPTERM1 n))
    (error_message_of (APPTERM1 n))
    (pre_of (APPTERM1 n)) (P_halt_of (APPTERM1 n)) (P_ccall_of (APPTERM1 n)).
Proof. Admitted.

Definition correct_APPTERM2 : forall n,
  handler_correct (handle_instr (APPTERM2 n)) (clight_of (APPTERM2 n))
    (error_message_of (APPTERM2 n))
    (pre_of (APPTERM2 n)) (P_halt_of (APPTERM2 n)) (P_ccall_of (APPTERM2 n)).
Proof. Admitted.

Definition correct_APPTERM3 : forall n,
  handler_correct (handle_instr (APPTERM3 n)) (clight_of (APPTERM3 n))
    (error_message_of (APPTERM3 n))
    (pre_of (APPTERM3 n)) (P_halt_of (APPTERM3 n)) (P_ccall_of (APPTERM3 n)).
Proof. Admitted.

Definition correct_RETURN : forall n,
  handler_correct (handle_instr (RETURN n)) (clight_of (RETURN n))
    (error_message_of (RETURN n))
    (pre_of (RETURN n)) (P_halt_of (RETURN n)) (P_ccall_of (RETURN n)).
Proof. Admitted.

Definition correct_RESTART :
  handler_correct (handle_instr RESTART) (clight_of RESTART)
    (error_message_of RESTART)
    (pre_of RESTART) (P_halt_of RESTART) (P_ccall_of RESTART).
Proof. Admitted.

Definition correct_GRAB : forall n,
  handler_correct (handle_instr (GRAB n)) (clight_of (GRAB n))
    (error_message_of (GRAB n))
    (pre_of (GRAB n)) (P_halt_of (GRAB n)) (P_ccall_of (GRAB n)).
Proof. Admitted.

Definition correct_CLOSURE : forall nvars code_ofs,
  handler_correct (handle_instr (CLOSURE nvars code_ofs)) (clight_of (CLOSURE nvars code_ofs))
    (error_message_of (CLOSURE nvars code_ofs))
    (pre_of (CLOSURE nvars code_ofs)) (P_halt_of (CLOSURE nvars code_ofs)) (P_ccall_of (CLOSURE nvars code_ofs)).
Proof. Admitted.

Definition correct_CLOSUREREC : forall nfuncs nvars code_offsets,
  handler_correct (handle_instr (CLOSUREREC nfuncs nvars code_offsets)) (clight_of (CLOSUREREC nfuncs nvars code_offsets))
    (error_message_of (CLOSUREREC nfuncs nvars code_offsets))
    (pre_of (CLOSUREREC nfuncs nvars code_offsets)) (P_halt_of (CLOSUREREC nfuncs nvars code_offsets)) (P_ccall_of (CLOSUREREC nfuncs nvars code_offsets)).
Proof. Admitted.

Definition correct_OFFSETCLOSURE : forall z,
  handler_correct (handle_instr (OFFSETCLOSURE z)) (clight_of (OFFSETCLOSURE z))
    (error_message_of (OFFSETCLOSURE z))
    (pre_of (OFFSETCLOSURE z)) (P_halt_of (OFFSETCLOSURE z)) (P_ccall_of (OFFSETCLOSURE z)).
Proof. Admitted.

Definition correct_PUSHOFFSETCLOSURE : forall z,
  handler_correct (handle_instr (PUSHOFFSETCLOSURE z)) (clight_of (PUSHOFFSETCLOSURE z))
    (error_message_of (PUSHOFFSETCLOSURE z))
    (pre_of (PUSHOFFSETCLOSURE z)) (P_halt_of (PUSHOFFSETCLOSURE z)) (P_ccall_of (PUSHOFFSETCLOSURE z)).
Proof. Admitted.

Definition correct_GETGLOBAL : forall n,
  handler_correct (handle_instr (GETGLOBAL n)) (clight_of (GETGLOBAL n))
    (error_message_of (GETGLOBAL n))
    (pre_of (GETGLOBAL n)) (P_halt_of (GETGLOBAL n)) (P_ccall_of (GETGLOBAL n)).
Proof. Admitted.

Definition correct_PUSHGETGLOBAL : forall n,
  handler_correct (handle_instr (PUSHGETGLOBAL n)) (clight_of (PUSHGETGLOBAL n))
    (error_message_of (PUSHGETGLOBAL n))
    (pre_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)).
Proof. Admitted.

Definition correct_GETGLOBALFIELD : forall n p,
  handler_correct (handle_instr (GETGLOBALFIELD n p)) (clight_of (GETGLOBALFIELD n p))
    (error_message_of (GETGLOBALFIELD n p))
    (pre_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)).
Proof. Admitted.

Definition correct_PUSHGETGLOBALFIELD : forall n p,
  handler_correct (handle_instr (PUSHGETGLOBALFIELD n p)) (clight_of (PUSHGETGLOBALFIELD n p))
    (error_message_of (PUSHGETGLOBALFIELD n p))
    (pre_of (PUSHGETGLOBALFIELD n p)) (P_halt_of (PUSHGETGLOBALFIELD n p)) (P_ccall_of (PUSHGETGLOBALFIELD n p)).
Proof. Admitted.

Definition correct_SETGLOBAL : forall n,
  handler_correct (handle_instr (SETGLOBAL n)) (clight_of (SETGLOBAL n))
    (error_message_of (SETGLOBAL n))
    (pre_of (SETGLOBAL n)) (P_halt_of (SETGLOBAL n)) (P_ccall_of (SETGLOBAL n)).
Proof. Admitted.

Definition correct_ATOM : forall n,
  handler_correct (handle_instr (ATOM n)) (clight_of (ATOM n))
    (error_message_of (ATOM n))
    (pre_of (ATOM n)) (P_halt_of (ATOM n)) (P_ccall_of (ATOM n)).
Proof. Admitted.

Definition correct_PUSHATOM : forall n,
  handler_correct (handle_instr (PUSHATOM n)) (clight_of (PUSHATOM n))
    (error_message_of (PUSHATOM n))
    (pre_of (PUSHATOM n)) (P_halt_of (PUSHATOM n)) (P_ccall_of (PUSHATOM n)).
Proof. Admitted.

Definition correct_MAKEBLOCK : forall t size,
  handler_correct (handle_instr (MAKEBLOCK t size)) (clight_of (MAKEBLOCK t size))
    (error_message_of (MAKEBLOCK t size))
    (pre_of (MAKEBLOCK t size)) (P_halt_of (MAKEBLOCK t size)) (P_ccall_of (MAKEBLOCK t size)).
Proof. Admitted.

Definition correct_MAKEBLOCK1 : forall n,
  handler_correct (handle_instr (MAKEBLOCK1 n)) (clight_of (MAKEBLOCK1 n))
    (error_message_of (MAKEBLOCK1 n))
    (pre_of (MAKEBLOCK1 n)) (P_halt_of (MAKEBLOCK1 n)) (P_ccall_of (MAKEBLOCK1 n)).
Proof. Admitted.

Definition correct_MAKEBLOCK2 : forall n,
  handler_correct (handle_instr (MAKEBLOCK2 n)) (clight_of (MAKEBLOCK2 n))
    (error_message_of (MAKEBLOCK2 n))
    (pre_of (MAKEBLOCK2 n)) (P_halt_of (MAKEBLOCK2 n)) (P_ccall_of (MAKEBLOCK2 n)).
Proof. Admitted.

Definition correct_MAKEBLOCK3 : forall n,
  handler_correct (handle_instr (MAKEBLOCK3 n)) (clight_of (MAKEBLOCK3 n))
    (error_message_of (MAKEBLOCK3 n))
    (pre_of (MAKEBLOCK3 n)) (P_halt_of (MAKEBLOCK3 n)) (P_ccall_of (MAKEBLOCK3 n)).
Proof. Admitted.

Definition correct_MAKEFLOATBLOCK : forall n,
  handler_correct (handle_instr (MAKEFLOATBLOCK n)) (clight_of (MAKEFLOATBLOCK n))
    (error_message_of (MAKEFLOATBLOCK n))
    (pre_of (MAKEFLOATBLOCK n)) (P_halt_of (MAKEFLOATBLOCK n)) (P_ccall_of (MAKEFLOATBLOCK n)).
Proof. Admitted.

Definition correct_GETFIELD : forall n,
  handler_correct (handle_instr (GETFIELD n)) (clight_of (GETFIELD n))
    (error_message_of (GETFIELD n))
    (pre_of (GETFIELD n)) (P_halt_of (GETFIELD n)) (P_ccall_of (GETFIELD n)).
Proof. Admitted.

Definition correct_GETFLOATFIELD : forall n,
  handler_correct (handle_instr (GETFLOATFIELD n)) (clight_of (GETFLOATFIELD n))
    (error_message_of (GETFLOATFIELD n))
    (pre_of (GETFLOATFIELD n)) (P_halt_of (GETFLOATFIELD n)) (P_ccall_of (GETFLOATFIELD n)).
Proof. Admitted.

Definition correct_SETFIELD : forall n,
  handler_correct (handle_instr (SETFIELD n)) (clight_of (SETFIELD n))
    (error_message_of (SETFIELD n))
    (pre_of (SETFIELD n)) (P_halt_of (SETFIELD n)) (P_ccall_of (SETFIELD n)).
Proof. Admitted.

Definition correct_SETFLOATFIELD : forall n,
  handler_correct (handle_instr (SETFLOATFIELD n)) (clight_of (SETFLOATFIELD n))
    (error_message_of (SETFLOATFIELD n))
    (pre_of (SETFLOATFIELD n)) (P_halt_of (SETFLOATFIELD n)) (P_ccall_of (SETFLOATFIELD n)).
Proof. Admitted.

Definition correct_VECTLENGTH :
  handler_correct (handle_instr VECTLENGTH) (clight_of VECTLENGTH)
    (error_message_of VECTLENGTH)
    (pre_of VECTLENGTH) (P_halt_of VECTLENGTH) (P_ccall_of VECTLENGTH).
Proof. Admitted.

Definition correct_GETVECTITEM :
  handler_correct (handle_instr GETVECTITEM) (clight_of GETVECTITEM)
    (error_message_of GETVECTITEM)
    (pre_of GETVECTITEM) (P_halt_of GETVECTITEM) (P_ccall_of GETVECTITEM).
Proof. Admitted.

Definition correct_SETVECTITEM :
  handler_correct (handle_instr SETVECTITEM) (clight_of SETVECTITEM)
    (error_message_of SETVECTITEM)
    (pre_of SETVECTITEM) (P_halt_of SETVECTITEM) (P_ccall_of SETVECTITEM).
Proof. Admitted.

Definition correct_GETBYTESCHAR :
  handler_correct (handle_instr GETBYTESCHAR) (clight_of GETBYTESCHAR)
    (error_message_of GETBYTESCHAR)
    (pre_of GETBYTESCHAR) (P_halt_of GETBYTESCHAR) (P_ccall_of GETBYTESCHAR).
Proof. Admitted.

Definition correct_SETBYTESCHAR :
  handler_correct (handle_instr SETBYTESCHAR) (clight_of SETBYTESCHAR)
    (error_message_of SETBYTESCHAR)
    (pre_of SETBYTESCHAR) (P_halt_of SETBYTESCHAR) (P_ccall_of SETBYTESCHAR).
Proof. Admitted.

Definition correct_GETSTRINGCHAR :
  handler_correct (handle_instr GETSTRINGCHAR) (clight_of GETSTRINGCHAR)
    (error_message_of GETSTRINGCHAR)
    (pre_of GETSTRINGCHAR) (P_halt_of GETSTRINGCHAR) (P_ccall_of GETSTRINGCHAR).
Proof. Admitted.

Definition correct_BRANCH : forall z,
  handler_correct (handle_instr (BRANCH z)) (clight_of (BRANCH z))
    (error_message_of (BRANCH z))
    (pre_of (BRANCH z)) (P_halt_of (BRANCH z)) (P_ccall_of (BRANCH z)).
Proof. Admitted.

Definition correct_BRANCHIF : forall z,
  handler_correct (handle_instr (BRANCHIF z)) (clight_of (BRANCHIF z))
    (error_message_of (BRANCHIF z))
    (pre_of (BRANCHIF z)) (P_halt_of (BRANCHIF z)) (P_ccall_of (BRANCHIF z)).
Proof. Admitted.

Definition correct_BRANCHIFNOT : forall z,
  handler_correct (handle_instr (BRANCHIFNOT z)) (clight_of (BRANCHIFNOT z))
    (error_message_of (BRANCHIFNOT z))
    (pre_of (BRANCHIFNOT z)) (P_halt_of (BRANCHIFNOT z)) (P_ccall_of (BRANCHIFNOT z)).
Proof. Admitted.

Definition correct_SWITCH : forall nc nb const_targets block_targets,
  handler_correct (handle_instr (SWITCH nc nb const_targets block_targets)) (clight_of (SWITCH nc nb const_targets block_targets))
    (error_message_of (SWITCH nc nb const_targets block_targets))
    (pre_of (SWITCH nc nb const_targets block_targets)) (P_halt_of (SWITCH nc nb const_targets block_targets)) (P_ccall_of (SWITCH nc nb const_targets block_targets)).
Proof. Admitted.

Definition correct_BOOLNOT :
  handler_correct (handle_instr BOOLNOT) (clight_of BOOLNOT)
    (error_message_of BOOLNOT)
    (pre_of BOOLNOT) (P_halt_of BOOLNOT) (P_ccall_of BOOLNOT).
Proof. Admitted.

Definition correct_PUSHTRAP : forall z,
  handler_correct (handle_instr (PUSHTRAP z)) (clight_of (PUSHTRAP z))
    (error_message_of (PUSHTRAP z))
    (pre_of (PUSHTRAP z)) (P_halt_of (PUSHTRAP z)) (P_ccall_of (PUSHTRAP z)).
Proof. Admitted.

Definition correct_POPTRAP :
  handler_correct (handle_instr POPTRAP) (clight_of POPTRAP)
    (error_message_of POPTRAP)
    (pre_of POPTRAP) (P_halt_of POPTRAP) (P_ccall_of POPTRAP).
Proof. Admitted.

Definition correct_RAISE :
  handler_correct (handle_instr RAISE) (clight_of RAISE)
    (error_message_of RAISE)
    (pre_of RAISE) (P_halt_of RAISE) (P_ccall_of RAISE).
Proof. Admitted.

Definition correct_RERAISE :
  handler_correct (handle_instr RERAISE) (clight_of RERAISE)
    (error_message_of RERAISE)
    (pre_of RERAISE) (P_halt_of RERAISE) (P_ccall_of RERAISE).
Proof. Admitted.

Definition correct_RAISE_NOTRACE :
  handler_correct (handle_instr RAISE_NOTRACE) (clight_of RAISE_NOTRACE)
    (error_message_of RAISE_NOTRACE)
    (pre_of RAISE_NOTRACE) (P_halt_of RAISE_NOTRACE) (P_ccall_of RAISE_NOTRACE).
Proof. Admitted.

Definition correct_CHECK_SIGNALS :
  handler_correct (handle_instr CHECK_SIGNALS) (clight_of CHECK_SIGNALS)
    (error_message_of CHECK_SIGNALS)
    (pre_of CHECK_SIGNALS) (P_halt_of CHECK_SIGNALS) (P_ccall_of CHECK_SIGNALS)
  := CHECK_SIGNALS_correct.correct_CHECK_SIGNALS.

Definition correct_C_CALL : forall nargs prim_idx,
  handler_correct (handle_instr (C_CALL nargs prim_idx)) (clight_of (C_CALL nargs prim_idx))
    (error_message_of (C_CALL nargs prim_idx))
    (pre_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx))
  := C_CALL_correct.correct_C_CALL.

Definition correct_CONSTINT : forall z,
  handler_correct (handle_instr (CONSTINT z)) (clight_of (CONSTINT z))
    (error_message_of (CONSTINT z))
    (pre_of (CONSTINT z)) (P_halt_of (CONSTINT z)) (P_ccall_of (CONSTINT z)).
Proof. Admitted.

Definition correct_PUSHCONSTINT : forall z,
  handler_correct (handle_instr (PUSHCONSTINT z)) (clight_of (PUSHCONSTINT z))
    (error_message_of (PUSHCONSTINT z))
    (pre_of (PUSHCONSTINT z)) (P_halt_of (PUSHCONSTINT z)) (P_ccall_of (PUSHCONSTINT z)).
Proof. Admitted.

Definition correct_NEGINT :
  handler_correct (handle_instr NEGINT) (clight_of NEGINT)
    (error_message_of NEGINT)
    (pre_of NEGINT) (P_halt_of NEGINT) (P_ccall_of NEGINT).
Proof. Admitted.

Definition correct_ADDINT :
  handler_correct (handle_instr ADDINT) (clight_of ADDINT)
    (error_message_of ADDINT)
    (pre_of ADDINT) (P_halt_of ADDINT) (P_ccall_of ADDINT).
Proof. Admitted.

Definition correct_SUBINT :
  handler_correct (handle_instr SUBINT) (clight_of SUBINT)
    (error_message_of SUBINT)
    (pre_of SUBINT) (P_halt_of SUBINT) (P_ccall_of SUBINT).
Proof. Admitted.

Definition correct_MULINT :
  handler_correct (handle_instr MULINT) (clight_of MULINT)
    (error_message_of MULINT)
    (pre_of MULINT) (P_halt_of MULINT) (P_ccall_of MULINT).
Proof. Admitted.

Definition correct_DIVINT :
  handler_correct (handle_instr DIVINT) (clight_of DIVINT)
    (error_message_of DIVINT)
    (pre_of DIVINT) (P_halt_of DIVINT) (P_ccall_of DIVINT).
Proof. Admitted.

Definition correct_MODINT :
  handler_correct (handle_instr MODINT) (clight_of MODINT)
    (error_message_of MODINT)
    (pre_of MODINT) (P_halt_of MODINT) (P_ccall_of MODINT).
Proof. Admitted.

Definition correct_ANDINT :
  handler_correct (handle_instr ANDINT) (clight_of ANDINT)
    (error_message_of ANDINT)
    (pre_of ANDINT) (P_halt_of ANDINT) (P_ccall_of ANDINT).
Proof. Admitted.

Definition correct_ORINT :
  handler_correct (handle_instr ORINT) (clight_of ORINT)
    (error_message_of ORINT)
    (pre_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT).
Proof. Admitted.

Definition correct_XORINT :
  handler_correct (handle_instr XORINT) (clight_of XORINT)
    (error_message_of XORINT)
    (pre_of XORINT) (P_halt_of XORINT) (P_ccall_of XORINT).
Proof. Admitted.

Definition correct_LSLINT :
  handler_correct (handle_instr LSLINT) (clight_of LSLINT)
    (error_message_of LSLINT)
    (pre_of LSLINT) (P_halt_of LSLINT) (P_ccall_of LSLINT).
Proof. Admitted.

Definition correct_LSRINT :
  handler_correct (handle_instr LSRINT) (clight_of LSRINT)
    (error_message_of LSRINT)
    (pre_of LSRINT) (P_halt_of LSRINT) (P_ccall_of LSRINT).
Proof. Admitted.

Definition correct_ASRINT :
  handler_correct (handle_instr ASRINT) (clight_of ASRINT)
    (error_message_of ASRINT)
    (pre_of ASRINT) (P_halt_of ASRINT) (P_ccall_of ASRINT).
Proof. Admitted.

Definition correct_EQ :
  handler_correct (handle_instr EQ) (clight_of EQ)
    (error_message_of EQ)
    (pre_of EQ) (P_halt_of EQ) (P_ccall_of EQ).
Proof. Admitted.

Definition correct_NEQ :
  handler_correct (handle_instr NEQ) (clight_of NEQ)
    (error_message_of NEQ)
    (pre_of NEQ) (P_halt_of NEQ) (P_ccall_of NEQ).
Proof. Admitted.

Definition correct_LTINT :
  handler_correct (handle_instr LTINT) (clight_of LTINT)
    (error_message_of LTINT)
    (pre_of LTINT) (P_halt_of LTINT) (P_ccall_of LTINT).
Proof. Admitted.

Definition correct_LEINT :
  handler_correct (handle_instr LEINT) (clight_of LEINT)
    (error_message_of LEINT)
    (pre_of LEINT) (P_halt_of LEINT) (P_ccall_of LEINT).
Proof. Admitted.

Definition correct_GTINT :
  handler_correct (handle_instr GTINT) (clight_of GTINT)
    (error_message_of GTINT)
    (pre_of GTINT) (P_halt_of GTINT) (P_ccall_of GTINT).
Proof. Admitted.

Definition correct_GEINT :
  handler_correct (handle_instr GEINT) (clight_of GEINT)
    (error_message_of GEINT)
    (pre_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT).
Proof. Admitted.

Definition correct_OFFSETINT : forall z,
  handler_correct (handle_instr (OFFSETINT z)) (clight_of (OFFSETINT z))
    (error_message_of (OFFSETINT z))
    (pre_of (OFFSETINT z)) (P_halt_of (OFFSETINT z)) (P_ccall_of (OFFSETINT z)).
Proof. Admitted.

Definition correct_OFFSETREF : forall z,
  handler_correct (handle_instr (OFFSETREF z)) (clight_of (OFFSETREF z))
    (error_message_of (OFFSETREF z))
    (pre_of (OFFSETREF z)) (P_halt_of (OFFSETREF z)) (P_ccall_of (OFFSETREF z)).
Proof. Admitted.

Definition correct_ISINT :
  handler_correct (handle_instr ISINT) (clight_of ISINT)
    (error_message_of ISINT)
    (pre_of ISINT) (P_halt_of ISINT) (P_ccall_of ISINT).
Proof. Admitted.

Definition correct_GETMETHOD :
  handler_correct (handle_instr GETMETHOD) (clight_of GETMETHOD)
    (error_message_of GETMETHOD)
    (pre_of GETMETHOD) (P_halt_of GETMETHOD) (P_ccall_of GETMETHOD).
Proof. Admitted.

Definition correct_GETPUBMET : forall z,
  handler_correct (handle_instr (GETPUBMET z)) (clight_of (GETPUBMET z))
    (error_message_of (GETPUBMET z))
    (pre_of (GETPUBMET z)) (P_halt_of (GETPUBMET z)) (P_ccall_of (GETPUBMET z)).
Proof. Admitted.

Definition correct_GETDYNMET :
  handler_correct (handle_instr GETDYNMET) (clight_of GETDYNMET)
    (error_message_of GETDYNMET)
    (pre_of GETDYNMET) (P_halt_of GETDYNMET) (P_ccall_of GETDYNMET).
Proof. Admitted.

Definition correct_BEQ : forall z1 z2,
  handler_correct (handle_instr (BEQ z1 z2)) (clight_of (BEQ z1 z2))
    (error_message_of (BEQ z1 z2))
    (pre_of (BEQ z1 z2)) (P_halt_of (BEQ z1 z2)) (P_ccall_of (BEQ z1 z2)).
Proof. Admitted.

Definition correct_BNEQ : forall z1 z2,
  handler_correct (handle_instr (BNEQ z1 z2)) (clight_of (BNEQ z1 z2))
    (error_message_of (BNEQ z1 z2))
    (pre_of (BNEQ z1 z2)) (P_halt_of (BNEQ z1 z2)) (P_ccall_of (BNEQ z1 z2)).
Proof. Admitted.

Definition correct_BLTINT : forall z1 z2,
  handler_correct (handle_instr (BLTINT z1 z2)) (clight_of (BLTINT z1 z2))
    (error_message_of (BLTINT z1 z2))
    (pre_of (BLTINT z1 z2)) (P_halt_of (BLTINT z1 z2)) (P_ccall_of (BLTINT z1 z2)).
Proof. Admitted.

Definition correct_BLEINT : forall z1 z2,
  handler_correct (handle_instr (BLEINT z1 z2)) (clight_of (BLEINT z1 z2))
    (error_message_of (BLEINT z1 z2))
    (pre_of (BLEINT z1 z2)) (P_halt_of (BLEINT z1 z2)) (P_ccall_of (BLEINT z1 z2)).
Proof. Admitted.

Definition correct_BGTINT : forall z1 z2,
  handler_correct (handle_instr (BGTINT z1 z2)) (clight_of (BGTINT z1 z2))
    (error_message_of (BGTINT z1 z2))
    (pre_of (BGTINT z1 z2)) (P_halt_of (BGTINT z1 z2)) (P_ccall_of (BGTINT z1 z2)).
Proof. Admitted.

Definition correct_BGEINT : forall z1 z2,
  handler_correct (handle_instr (BGEINT z1 z2)) (clight_of (BGEINT z1 z2))
    (error_message_of (BGEINT z1 z2))
    (pre_of (BGEINT z1 z2)) (P_halt_of (BGEINT z1 z2)) (P_ccall_of (BGEINT z1 z2)).
Proof. Admitted.

Definition correct_ULTINT :
  handler_correct (handle_instr ULTINT) (clight_of ULTINT)
    (error_message_of ULTINT)
    (pre_of ULTINT) (P_halt_of ULTINT) (P_ccall_of ULTINT).
Proof. Admitted.

Definition correct_UGEINT :
  handler_correct (handle_instr UGEINT) (clight_of UGEINT)
    (error_message_of UGEINT)
    (pre_of UGEINT) (P_halt_of UGEINT) (P_ccall_of UGEINT).
Proof. Admitted.

Definition correct_BULTINT : forall z1 z2,
  handler_correct (handle_instr (BULTINT z1 z2)) (clight_of (BULTINT z1 z2))
    (error_message_of (BULTINT z1 z2))
    (pre_of (BULTINT z1 z2)) (P_halt_of (BULTINT z1 z2)) (P_ccall_of (BULTINT z1 z2)).
Proof. Admitted.

Definition correct_BUGEINT : forall z1 z2,
  handler_correct (handle_instr (BUGEINT z1 z2)) (clight_of (BUGEINT z1 z2))
    (error_message_of (BUGEINT z1 z2))
    (pre_of (BUGEINT z1 z2)) (P_halt_of (BUGEINT z1 z2)) (P_ccall_of (BUGEINT z1 z2)).
Proof. Admitted.

Definition correct_STOP :
  handler_correct (handle_instr STOP) (clight_of STOP)
    (error_message_of STOP)
    (pre_of STOP) (P_halt_of STOP) (P_ccall_of STOP)
  := STOP_correct.correct_STOP.
