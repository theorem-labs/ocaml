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
    (pre_of (ACC n))
    (P_error_of (ACC n)) (P_halt_of (ACC n)) (P_ccall_of (ACC n)).
Admitted.

Definition correct_PUSH :
  handler_correct (handle_instr PUSH) (clight_of PUSH)
    (pre_of PUSH)
    (P_error_of PUSH) (P_halt_of PUSH) (P_ccall_of PUSH).
Admitted.

Definition correct_PUSHACC : forall n,
  handler_correct (handle_instr (PUSHACC n)) (clight_of (PUSHACC n))
    (pre_of (PUSHACC n))
    (P_error_of (PUSHACC n)) (P_halt_of (PUSHACC n)) (P_ccall_of (PUSHACC n)).
Admitted.

Definition correct_POP : forall n,
  handler_correct (handle_instr (POP n)) (clight_of (POP n))
    (pre_of (POP n))
    (P_error_of (POP n)) (P_halt_of (POP n)) (P_ccall_of (POP n)).
Admitted.

Definition correct_ASSIGN : forall n,
  handler_correct (handle_instr (ASSIGN n)) (clight_of (ASSIGN n))
    (pre_of (ASSIGN n))
    (P_error_of (ASSIGN n)) (P_halt_of (ASSIGN n)) (P_ccall_of (ASSIGN n)).
Admitted.

Definition correct_ENVACC : forall n,
  handler_correct (handle_instr (ENVACC n)) (clight_of (ENVACC n))
    (pre_of (ENVACC n))
    (P_error_of (ENVACC n)) (P_halt_of (ENVACC n)) (P_ccall_of (ENVACC n)).
Admitted.

Definition correct_PUSHENVACC : forall n,
  handler_correct (handle_instr (PUSHENVACC n)) (clight_of (PUSHENVACC n))
    (pre_of (PUSHENVACC n))
    (P_error_of (PUSHENVACC n)) (P_halt_of (PUSHENVACC n)) (P_ccall_of (PUSHENVACC n)).
Admitted.

Definition correct_PUSH_RETADDR : forall z,
  handler_correct (handle_instr (PUSH_RETADDR z)) (clight_of (PUSH_RETADDR z))
    (pre_of (PUSH_RETADDR z))
    (P_error_of (PUSH_RETADDR z)) (P_halt_of (PUSH_RETADDR z)) (P_ccall_of (PUSH_RETADDR z)).
Admitted.

Definition correct_APPLY : forall n,
  handler_correct (handle_instr (APPLY n)) (clight_of (APPLY n))
    (pre_of (APPLY n))
    (P_error_of (APPLY n)) (P_halt_of (APPLY n)) (P_ccall_of (APPLY n)).
Admitted.

Definition correct_APPLY1 :
  handler_correct (handle_instr APPLY1) (clight_of APPLY1)
    (pre_of APPLY1)
    (P_error_of APPLY1) (P_halt_of APPLY1) (P_ccall_of APPLY1).
Admitted.

Definition correct_APPLY2 :
  handler_correct (handle_instr APPLY2) (clight_of APPLY2)
    (pre_of APPLY2)
    (P_error_of APPLY2) (P_halt_of APPLY2) (P_ccall_of APPLY2).
Admitted.

Definition correct_APPLY3 :
  handler_correct (handle_instr APPLY3) (clight_of APPLY3)
    (pre_of APPLY3)
    (P_error_of APPLY3) (P_halt_of APPLY3) (P_ccall_of APPLY3).
Admitted.

Definition correct_APPTERM : forall nargs slotsize,
  handler_correct (handle_instr (APPTERM nargs slotsize)) (clight_of (APPTERM nargs slotsize))
    (pre_of (APPTERM nargs slotsize))
    (P_error_of (APPTERM nargs slotsize)) (P_halt_of (APPTERM nargs slotsize)) (P_ccall_of (APPTERM nargs slotsize)).
Admitted.

Definition correct_APPTERM1 : forall n,
  handler_correct (handle_instr (APPTERM1 n)) (clight_of (APPTERM1 n))
    (pre_of (APPTERM1 n))
    (P_error_of (APPTERM1 n)) (P_halt_of (APPTERM1 n)) (P_ccall_of (APPTERM1 n)).
Admitted.

Definition correct_APPTERM2 : forall n,
  handler_correct (handle_instr (APPTERM2 n)) (clight_of (APPTERM2 n))
    (pre_of (APPTERM2 n))
    (P_error_of (APPTERM2 n)) (P_halt_of (APPTERM2 n)) (P_ccall_of (APPTERM2 n)).
Admitted.

Definition correct_APPTERM3 : forall n,
  handler_correct (handle_instr (APPTERM3 n)) (clight_of (APPTERM3 n))
    (pre_of (APPTERM3 n))
    (P_error_of (APPTERM3 n)) (P_halt_of (APPTERM3 n)) (P_ccall_of (APPTERM3 n)).
Admitted.

Definition correct_RETURN : forall n,
  handler_correct (handle_instr (RETURN n)) (clight_of (RETURN n))
    (pre_of (RETURN n))
    (P_error_of (RETURN n)) (P_halt_of (RETURN n)) (P_ccall_of (RETURN n)).
Admitted.

Definition correct_RESTART :
  handler_correct (handle_instr RESTART) (clight_of RESTART)
    (pre_of RESTART)
    (P_error_of RESTART) (P_halt_of RESTART) (P_ccall_of RESTART).
Admitted.

Definition correct_GRAB : forall n,
  handler_correct (handle_instr (GRAB n)) (clight_of (GRAB n))
    (pre_of (GRAB n))
    (P_error_of (GRAB n)) (P_halt_of (GRAB n)) (P_ccall_of (GRAB n)).
Admitted.

Definition correct_CLOSURE : forall nvars code_ofs,
  handler_correct (handle_instr (CLOSURE nvars code_ofs)) (clight_of (CLOSURE nvars code_ofs))
    (pre_of (CLOSURE nvars code_ofs))
    (P_error_of (CLOSURE nvars code_ofs)) (P_halt_of (CLOSURE nvars code_ofs)) (P_ccall_of (CLOSURE nvars code_ofs)).
Admitted.

Definition correct_CLOSUREREC : forall nfuncs nvars code_offsets,
  handler_correct (handle_instr (CLOSUREREC nfuncs nvars code_offsets)) (clight_of (CLOSUREREC nfuncs nvars code_offsets))
    (pre_of (CLOSUREREC nfuncs nvars code_offsets))
    (P_error_of (CLOSUREREC nfuncs nvars code_offsets)) (P_halt_of (CLOSUREREC nfuncs nvars code_offsets)) (P_ccall_of (CLOSUREREC nfuncs nvars code_offsets)).
Admitted.

Definition correct_OFFSETCLOSURE : forall z,
  handler_correct (handle_instr (OFFSETCLOSURE z)) (clight_of (OFFSETCLOSURE z))
    (pre_of (OFFSETCLOSURE z))
    (P_error_of (OFFSETCLOSURE z)) (P_halt_of (OFFSETCLOSURE z)) (P_ccall_of (OFFSETCLOSURE z)).
Admitted.

Definition correct_PUSHOFFSETCLOSURE : forall z,
  handler_correct (handle_instr (PUSHOFFSETCLOSURE z)) (clight_of (PUSHOFFSETCLOSURE z))
    (pre_of (PUSHOFFSETCLOSURE z))
    (P_error_of (PUSHOFFSETCLOSURE z)) (P_halt_of (PUSHOFFSETCLOSURE z)) (P_ccall_of (PUSHOFFSETCLOSURE z)).
Admitted.

Definition correct_GETGLOBAL : forall n,
  handler_correct (handle_instr (GETGLOBAL n)) (clight_of (GETGLOBAL n))
    (pre_of (GETGLOBAL n))
    (P_error_of (GETGLOBAL n)) (P_halt_of (GETGLOBAL n)) (P_ccall_of (GETGLOBAL n)).
Admitted.

Definition correct_PUSHGETGLOBAL : forall n,
  handler_correct (handle_instr (PUSHGETGLOBAL n)) (clight_of (PUSHGETGLOBAL n))
    (pre_of (PUSHGETGLOBAL n))
    (P_error_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)).
Admitted.

Definition correct_GETGLOBALFIELD : forall n p,
  handler_correct (handle_instr (GETGLOBALFIELD n p)) (clight_of (GETGLOBALFIELD n p))
    (pre_of (GETGLOBALFIELD n p))
    (P_error_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)).
Admitted.

Definition correct_PUSHGETGLOBALFIELD : forall n p,
  handler_correct (handle_instr (PUSHGETGLOBALFIELD n p)) (clight_of (PUSHGETGLOBALFIELD n p))
    (pre_of (PUSHGETGLOBALFIELD n p))
    (P_error_of (PUSHGETGLOBALFIELD n p)) (P_halt_of (PUSHGETGLOBALFIELD n p)) (P_ccall_of (PUSHGETGLOBALFIELD n p)).
Admitted.

Definition correct_SETGLOBAL : forall n,
  handler_correct (handle_instr (SETGLOBAL n)) (clight_of (SETGLOBAL n))
    (pre_of (SETGLOBAL n))
    (P_error_of (SETGLOBAL n)) (P_halt_of (SETGLOBAL n)) (P_ccall_of (SETGLOBAL n)).
Admitted.

Definition correct_ATOM : forall n,
  handler_correct (handle_instr (ATOM n)) (clight_of (ATOM n))
    (pre_of (ATOM n))
    (P_error_of (ATOM n)) (P_halt_of (ATOM n)) (P_ccall_of (ATOM n)).
Admitted.

Definition correct_PUSHATOM : forall n,
  handler_correct (handle_instr (PUSHATOM n)) (clight_of (PUSHATOM n))
    (pre_of (PUSHATOM n))
    (P_error_of (PUSHATOM n)) (P_halt_of (PUSHATOM n)) (P_ccall_of (PUSHATOM n)).
Admitted.

Definition correct_MAKEBLOCK : forall t size,
  handler_correct (handle_instr (MAKEBLOCK t size)) (clight_of (MAKEBLOCK t size))
    (pre_of (MAKEBLOCK t size))
    (P_error_of (MAKEBLOCK t size)) (P_halt_of (MAKEBLOCK t size)) (P_ccall_of (MAKEBLOCK t size)).
Admitted.

Definition correct_MAKEBLOCK1 : forall n,
  handler_correct (handle_instr (MAKEBLOCK1 n)) (clight_of (MAKEBLOCK1 n))
    (pre_of (MAKEBLOCK1 n))
    (P_error_of (MAKEBLOCK1 n)) (P_halt_of (MAKEBLOCK1 n)) (P_ccall_of (MAKEBLOCK1 n)).
Admitted.

Definition correct_MAKEBLOCK2 : forall n,
  handler_correct (handle_instr (MAKEBLOCK2 n)) (clight_of (MAKEBLOCK2 n))
    (pre_of (MAKEBLOCK2 n))
    (P_error_of (MAKEBLOCK2 n)) (P_halt_of (MAKEBLOCK2 n)) (P_ccall_of (MAKEBLOCK2 n)).
Admitted.

Definition correct_MAKEBLOCK3 : forall n,
  handler_correct (handle_instr (MAKEBLOCK3 n)) (clight_of (MAKEBLOCK3 n))
    (pre_of (MAKEBLOCK3 n))
    (P_error_of (MAKEBLOCK3 n)) (P_halt_of (MAKEBLOCK3 n)) (P_ccall_of (MAKEBLOCK3 n)).
Admitted.

Definition correct_MAKEFLOATBLOCK : forall n,
  handler_correct (handle_instr (MAKEFLOATBLOCK n)) (clight_of (MAKEFLOATBLOCK n))
    (pre_of (MAKEFLOATBLOCK n))
    (P_error_of (MAKEFLOATBLOCK n)) (P_halt_of (MAKEFLOATBLOCK n)) (P_ccall_of (MAKEFLOATBLOCK n)).
Admitted.

Definition correct_GETFIELD : forall n,
  handler_correct (handle_instr (GETFIELD n)) (clight_of (GETFIELD n))
    (pre_of (GETFIELD n))
    (P_error_of (GETFIELD n)) (P_halt_of (GETFIELD n)) (P_ccall_of (GETFIELD n)).
Admitted.

Definition correct_GETFLOATFIELD : forall n,
  handler_correct (handle_instr (GETFLOATFIELD n)) (clight_of (GETFLOATFIELD n))
    (pre_of (GETFLOATFIELD n))
    (P_error_of (GETFLOATFIELD n)) (P_halt_of (GETFLOATFIELD n)) (P_ccall_of (GETFLOATFIELD n)).
Admitted.

Definition correct_SETFIELD : forall n,
  handler_correct (handle_instr (SETFIELD n)) (clight_of (SETFIELD n))
    (pre_of (SETFIELD n))
    (P_error_of (SETFIELD n)) (P_halt_of (SETFIELD n)) (P_ccall_of (SETFIELD n)).
Admitted.

Definition correct_SETFLOATFIELD : forall n,
  handler_correct (handle_instr (SETFLOATFIELD n)) (clight_of (SETFLOATFIELD n))
    (pre_of (SETFLOATFIELD n))
    (P_error_of (SETFLOATFIELD n)) (P_halt_of (SETFLOATFIELD n)) (P_ccall_of (SETFLOATFIELD n)).
Admitted.

Definition correct_VECTLENGTH :
  handler_correct (handle_instr VECTLENGTH) (clight_of VECTLENGTH)
    (pre_of VECTLENGTH)
    (P_error_of VECTLENGTH) (P_halt_of VECTLENGTH) (P_ccall_of VECTLENGTH).
Admitted.

Definition correct_GETVECTITEM :
  handler_correct (handle_instr GETVECTITEM) (clight_of GETVECTITEM)
    (pre_of GETVECTITEM)
    (P_error_of GETVECTITEM) (P_halt_of GETVECTITEM) (P_ccall_of GETVECTITEM).
Admitted.

Definition correct_SETVECTITEM :
  handler_correct (handle_instr SETVECTITEM) (clight_of SETVECTITEM)
    (pre_of SETVECTITEM)
    (P_error_of SETVECTITEM) (P_halt_of SETVECTITEM) (P_ccall_of SETVECTITEM).
Admitted.

Definition correct_GETBYTESCHAR :
  handler_correct (handle_instr GETBYTESCHAR) (clight_of GETBYTESCHAR)
    (pre_of GETBYTESCHAR)
    (P_error_of GETBYTESCHAR) (P_halt_of GETBYTESCHAR) (P_ccall_of GETBYTESCHAR).
Admitted.

Definition correct_SETBYTESCHAR :
  handler_correct (handle_instr SETBYTESCHAR) (clight_of SETBYTESCHAR)
    (pre_of SETBYTESCHAR)
    (P_error_of SETBYTESCHAR) (P_halt_of SETBYTESCHAR) (P_ccall_of SETBYTESCHAR).
Admitted.

Definition correct_GETSTRINGCHAR :
  handler_correct (handle_instr GETSTRINGCHAR) (clight_of GETSTRINGCHAR)
    (pre_of GETSTRINGCHAR)
    (P_error_of GETSTRINGCHAR) (P_halt_of GETSTRINGCHAR) (P_ccall_of GETSTRINGCHAR).
Admitted.

Definition correct_BRANCH : forall z,
  handler_correct (handle_instr (BRANCH z)) (clight_of (BRANCH z))
    (pre_of (BRANCH z))
    (P_error_of (BRANCH z)) (P_halt_of (BRANCH z)) (P_ccall_of (BRANCH z)).
Admitted.

Definition correct_BRANCHIF : forall z,
  handler_correct (handle_instr (BRANCHIF z)) (clight_of (BRANCHIF z))
    (pre_of (BRANCHIF z))
    (P_error_of (BRANCHIF z)) (P_halt_of (BRANCHIF z)) (P_ccall_of (BRANCHIF z)).
Admitted.

Definition correct_BRANCHIFNOT : forall z,
  handler_correct (handle_instr (BRANCHIFNOT z)) (clight_of (BRANCHIFNOT z))
    (pre_of (BRANCHIFNOT z))
    (P_error_of (BRANCHIFNOT z)) (P_halt_of (BRANCHIFNOT z)) (P_ccall_of (BRANCHIFNOT z)).
Admitted.

Definition correct_SWITCH : forall nc nb const_targets block_targets,
  handler_correct (handle_instr (SWITCH nc nb const_targets block_targets)) (clight_of (SWITCH nc nb const_targets block_targets))
    (pre_of (SWITCH nc nb const_targets block_targets))
    (P_error_of (SWITCH nc nb const_targets block_targets)) (P_halt_of (SWITCH nc nb const_targets block_targets)) (P_ccall_of (SWITCH nc nb const_targets block_targets)).
Admitted.

Definition correct_BOOLNOT :
  handler_correct (handle_instr BOOLNOT) (clight_of BOOLNOT)
    (pre_of BOOLNOT)
    (P_error_of BOOLNOT) (P_halt_of BOOLNOT) (P_ccall_of BOOLNOT).
Admitted.

Definition correct_PUSHTRAP : forall z,
  handler_correct (handle_instr (PUSHTRAP z)) (clight_of (PUSHTRAP z))
    (pre_of (PUSHTRAP z))
    (P_error_of (PUSHTRAP z)) (P_halt_of (PUSHTRAP z)) (P_ccall_of (PUSHTRAP z)).
Admitted.

Definition correct_POPTRAP :
  handler_correct (handle_instr POPTRAP) (clight_of POPTRAP)
    (pre_of POPTRAP)
    (P_error_of POPTRAP) (P_halt_of POPTRAP) (P_ccall_of POPTRAP).
Admitted.

Definition correct_RAISE :
  handler_correct (handle_instr RAISE) (clight_of RAISE)
    (pre_of RAISE)
    (P_error_of RAISE) (P_halt_of RAISE) (P_ccall_of RAISE).
Admitted.

Definition correct_RERAISE :
  handler_correct (handle_instr RERAISE) (clight_of RERAISE)
    (pre_of RERAISE)
    (P_error_of RERAISE) (P_halt_of RERAISE) (P_ccall_of RERAISE).
Admitted.

Definition correct_RAISE_NOTRACE :
  handler_correct (handle_instr RAISE_NOTRACE) (clight_of RAISE_NOTRACE)
    (pre_of RAISE_NOTRACE)
    (P_error_of RAISE_NOTRACE) (P_halt_of RAISE_NOTRACE) (P_ccall_of RAISE_NOTRACE).
Admitted.

Definition correct_CHECK_SIGNALS :
  handler_correct (handle_instr CHECK_SIGNALS) (clight_of CHECK_SIGNALS)
    (pre_of CHECK_SIGNALS)
    (P_error_of CHECK_SIGNALS) (P_halt_of CHECK_SIGNALS) (P_ccall_of CHECK_SIGNALS).
Admitted.

Definition correct_C_CALL : forall nargs prim_idx,
  handler_correct (handle_instr (C_CALL nargs prim_idx)) (clight_of (C_CALL nargs prim_idx))
    (pre_of (C_CALL nargs prim_idx))
    (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)).
Admitted.

Definition correct_CONSTINT : forall z,
  handler_correct (handle_instr (CONSTINT z)) (clight_of (CONSTINT z))
    (pre_of (CONSTINT z))
    (P_error_of (CONSTINT z)) (P_halt_of (CONSTINT z)) (P_ccall_of (CONSTINT z)).
Admitted.

Definition correct_PUSHCONSTINT : forall z,
  handler_correct (handle_instr (PUSHCONSTINT z)) (clight_of (PUSHCONSTINT z))
    (pre_of (PUSHCONSTINT z))
    (P_error_of (PUSHCONSTINT z)) (P_halt_of (PUSHCONSTINT z)) (P_ccall_of (PUSHCONSTINT z)).
Admitted.

Definition correct_NEGINT :
  handler_correct (handle_instr NEGINT) (clight_of NEGINT)
    (pre_of NEGINT)
    (P_error_of NEGINT) (P_halt_of NEGINT) (P_ccall_of NEGINT).
Admitted.

Definition correct_ADDINT :
  handler_correct (handle_instr ADDINT) (clight_of ADDINT)
    (pre_of ADDINT)
    (P_error_of ADDINT) (P_halt_of ADDINT) (P_ccall_of ADDINT).
Admitted.

Definition correct_SUBINT :
  handler_correct (handle_instr SUBINT) (clight_of SUBINT)
    (pre_of SUBINT)
    (P_error_of SUBINT) (P_halt_of SUBINT) (P_ccall_of SUBINT).
Admitted.

Definition correct_MULINT :
  handler_correct (handle_instr MULINT) (clight_of MULINT)
    (pre_of MULINT)
    (P_error_of MULINT) (P_halt_of MULINT) (P_ccall_of MULINT).
Admitted.

Definition correct_DIVINT :
  handler_correct (handle_instr DIVINT) (clight_of DIVINT)
    (pre_of DIVINT)
    (P_error_of DIVINT) (P_halt_of DIVINT) (P_ccall_of DIVINT).
Admitted.

Definition correct_MODINT :
  handler_correct (handle_instr MODINT) (clight_of MODINT)
    (pre_of MODINT)
    (P_error_of MODINT) (P_halt_of MODINT) (P_ccall_of MODINT).
Admitted.

Definition correct_ANDINT :
  handler_correct (handle_instr ANDINT) (clight_of ANDINT)
    (pre_of ANDINT)
    (P_error_of ANDINT) (P_halt_of ANDINT) (P_ccall_of ANDINT).
Admitted.

Definition correct_ORINT :
  handler_correct (handle_instr ORINT) (clight_of ORINT)
    (pre_of ORINT)
    (P_error_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT).
Admitted.

Definition correct_XORINT :
  handler_correct (handle_instr XORINT) (clight_of XORINT)
    (pre_of XORINT)
    (P_error_of XORINT) (P_halt_of XORINT) (P_ccall_of XORINT).
Admitted.

Definition correct_LSLINT :
  handler_correct (handle_instr LSLINT) (clight_of LSLINT)
    (pre_of LSLINT)
    (P_error_of LSLINT) (P_halt_of LSLINT) (P_ccall_of LSLINT).
Admitted.

Definition correct_LSRINT :
  handler_correct (handle_instr LSRINT) (clight_of LSRINT)
    (pre_of LSRINT)
    (P_error_of LSRINT) (P_halt_of LSRINT) (P_ccall_of LSRINT).
Admitted.

Definition correct_ASRINT :
  handler_correct (handle_instr ASRINT) (clight_of ASRINT)
    (pre_of ASRINT)
    (P_error_of ASRINT) (P_halt_of ASRINT) (P_ccall_of ASRINT).
Admitted.

Definition correct_EQ :
  handler_correct (handle_instr EQ) (clight_of EQ)
    (pre_of EQ)
    (P_error_of EQ) (P_halt_of EQ) (P_ccall_of EQ).
Admitted.

Definition correct_NEQ :
  handler_correct (handle_instr NEQ) (clight_of NEQ)
    (pre_of NEQ)
    (P_error_of NEQ) (P_halt_of NEQ) (P_ccall_of NEQ).
Admitted.

Definition correct_LTINT :
  handler_correct (handle_instr LTINT) (clight_of LTINT)
    (pre_of LTINT)
    (P_error_of LTINT) (P_halt_of LTINT) (P_ccall_of LTINT).
Admitted.

Definition correct_LEINT :
  handler_correct (handle_instr LEINT) (clight_of LEINT)
    (pre_of LEINT)
    (P_error_of LEINT) (P_halt_of LEINT) (P_ccall_of LEINT).
Admitted.

Definition correct_GTINT :
  handler_correct (handle_instr GTINT) (clight_of GTINT)
    (pre_of GTINT)
    (P_error_of GTINT) (P_halt_of GTINT) (P_ccall_of GTINT).
Admitted.

Definition correct_GEINT :
  handler_correct (handle_instr GEINT) (clight_of GEINT)
    (pre_of GEINT)
    (P_error_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT).
Admitted.

Definition correct_OFFSETINT : forall z,
  handler_correct (handle_instr (OFFSETINT z)) (clight_of (OFFSETINT z))
    (pre_of (OFFSETINT z))
    (P_error_of (OFFSETINT z)) (P_halt_of (OFFSETINT z)) (P_ccall_of (OFFSETINT z)).
Admitted.

Definition correct_OFFSETREF : forall z,
  handler_correct (handle_instr (OFFSETREF z)) (clight_of (OFFSETREF z))
    (pre_of (OFFSETREF z))
    (P_error_of (OFFSETREF z)) (P_halt_of (OFFSETREF z)) (P_ccall_of (OFFSETREF z)).
Admitted.

Definition correct_ISINT :
  handler_correct (handle_instr ISINT) (clight_of ISINT)
    (pre_of ISINT)
    (P_error_of ISINT) (P_halt_of ISINT) (P_ccall_of ISINT).
Admitted.

Definition correct_GETMETHOD :
  handler_correct (handle_instr GETMETHOD) (clight_of GETMETHOD)
    (pre_of GETMETHOD)
    (P_error_of GETMETHOD) (P_halt_of GETMETHOD) (P_ccall_of GETMETHOD).
Admitted.

Definition correct_GETPUBMET : forall z,
  handler_correct (handle_instr (GETPUBMET z)) (clight_of (GETPUBMET z))
    (pre_of (GETPUBMET z))
    (P_error_of (GETPUBMET z)) (P_halt_of (GETPUBMET z)) (P_ccall_of (GETPUBMET z)).
Admitted.

Definition correct_GETDYNMET :
  handler_correct (handle_instr GETDYNMET) (clight_of GETDYNMET)
    (pre_of GETDYNMET)
    (P_error_of GETDYNMET) (P_halt_of GETDYNMET) (P_ccall_of GETDYNMET).
Admitted.

Definition correct_BEQ : forall z1 z2,
  handler_correct (handle_instr (BEQ z1 z2)) (clight_of (BEQ z1 z2))
    (pre_of (BEQ z1 z2))
    (P_error_of (BEQ z1 z2)) (P_halt_of (BEQ z1 z2)) (P_ccall_of (BEQ z1 z2)).
Admitted.

Definition correct_BNEQ : forall z1 z2,
  handler_correct (handle_instr (BNEQ z1 z2)) (clight_of (BNEQ z1 z2))
    (pre_of (BNEQ z1 z2))
    (P_error_of (BNEQ z1 z2)) (P_halt_of (BNEQ z1 z2)) (P_ccall_of (BNEQ z1 z2)).
Admitted.

Definition correct_BLTINT : forall z1 z2,
  handler_correct (handle_instr (BLTINT z1 z2)) (clight_of (BLTINT z1 z2))
    (pre_of (BLTINT z1 z2))
    (P_error_of (BLTINT z1 z2)) (P_halt_of (BLTINT z1 z2)) (P_ccall_of (BLTINT z1 z2)).
Admitted.

Definition correct_BLEINT : forall z1 z2,
  handler_correct (handle_instr (BLEINT z1 z2)) (clight_of (BLEINT z1 z2))
    (pre_of (BLEINT z1 z2))
    (P_error_of (BLEINT z1 z2)) (P_halt_of (BLEINT z1 z2)) (P_ccall_of (BLEINT z1 z2)).
Admitted.

Definition correct_BGTINT : forall z1 z2,
  handler_correct (handle_instr (BGTINT z1 z2)) (clight_of (BGTINT z1 z2))
    (pre_of (BGTINT z1 z2))
    (P_error_of (BGTINT z1 z2)) (P_halt_of (BGTINT z1 z2)) (P_ccall_of (BGTINT z1 z2)).
Admitted.

Definition correct_BGEINT : forall z1 z2,
  handler_correct (handle_instr (BGEINT z1 z2)) (clight_of (BGEINT z1 z2))
    (pre_of (BGEINT z1 z2))
    (P_error_of (BGEINT z1 z2)) (P_halt_of (BGEINT z1 z2)) (P_ccall_of (BGEINT z1 z2)).
Admitted.

Definition correct_ULTINT :
  handler_correct (handle_instr ULTINT) (clight_of ULTINT)
    (pre_of ULTINT)
    (P_error_of ULTINT) (P_halt_of ULTINT) (P_ccall_of ULTINT).
Admitted.

Definition correct_UGEINT :
  handler_correct (handle_instr UGEINT) (clight_of UGEINT)
    (pre_of UGEINT)
    (P_error_of UGEINT) (P_halt_of UGEINT) (P_ccall_of UGEINT).
Admitted.

Definition correct_BULTINT : forall z1 z2,
  handler_correct (handle_instr (BULTINT z1 z2)) (clight_of (BULTINT z1 z2))
    (pre_of (BULTINT z1 z2))
    (P_error_of (BULTINT z1 z2)) (P_halt_of (BULTINT z1 z2)) (P_ccall_of (BULTINT z1 z2)).
Admitted.

Definition correct_BUGEINT : forall z1 z2,
  handler_correct (handle_instr (BUGEINT z1 z2)) (clight_of (BUGEINT z1 z2))
    (pre_of (BUGEINT z1 z2))
    (P_error_of (BUGEINT z1 z2)) (P_halt_of (BUGEINT z1 z2)) (P_ccall_of (BUGEINT z1 z2)).
Admitted.

Definition correct_STOP :
  handler_correct (handle_instr STOP) (clight_of STOP)
    (pre_of STOP)
    (P_error_of STOP) (P_halt_of STOP) (P_ccall_of STOP).
Admitted.
