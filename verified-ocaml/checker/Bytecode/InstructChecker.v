(* InstructChecker.v — Thin ascription verifying that the untrusted
   InstructVerificationProof satisfies the trusted
   InstructVerificationFineGrainedSpec, plus the unified
   InstructVerificationSpec via the functor. *)

From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Manual.Bytecode.Interpret Require Import HandleInstrSpec.
From OCamlInterp.Automatic.Bytecode Require InstructVerificationProof.

Module InstructVerification <: InstructVerificationFineGrainedSpec InstructVerificationProof.DispatchHI.

  Definition correct_ACC := InstructVerificationProof.correct_ACC.
  Definition correct_PUSH := InstructVerificationProof.correct_PUSH.
  Definition correct_PUSHACC := InstructVerificationProof.correct_PUSHACC.
  Definition correct_POP := InstructVerificationProof.correct_POP.
  Definition correct_ASSIGN := InstructVerificationProof.correct_ASSIGN.
  Definition correct_ENVACC := InstructVerificationProof.correct_ENVACC.
  Definition correct_PUSHENVACC := InstructVerificationProof.correct_PUSHENVACC.
  Definition correct_PUSH_RETADDR := InstructVerificationProof.correct_PUSH_RETADDR.
  Definition correct_APPLY := InstructVerificationProof.correct_APPLY.
  Definition correct_APPLY1 := InstructVerificationProof.correct_APPLY1.
  Definition correct_APPLY2 := InstructVerificationProof.correct_APPLY2.
  Definition correct_APPLY3 := InstructVerificationProof.correct_APPLY3.
  Definition correct_APPTERM := InstructVerificationProof.correct_APPTERM.
  Definition correct_APPTERM1 := InstructVerificationProof.correct_APPTERM1.
  Definition correct_APPTERM2 := InstructVerificationProof.correct_APPTERM2.
  Definition correct_APPTERM3 := InstructVerificationProof.correct_APPTERM3.
  Definition correct_RETURN := InstructVerificationProof.correct_RETURN.
  Definition correct_RESTART := InstructVerificationProof.correct_RESTART.
  Definition correct_GRAB := InstructVerificationProof.correct_GRAB.
  Definition correct_CLOSURE := InstructVerificationProof.correct_CLOSURE.
  Definition correct_CLOSUREREC := InstructVerificationProof.correct_CLOSUREREC.
  Definition correct_OFFSETCLOSURE := InstructVerificationProof.correct_OFFSETCLOSURE.
  Definition correct_PUSHOFFSETCLOSURE := InstructVerificationProof.correct_PUSHOFFSETCLOSURE.
  Definition correct_GETGLOBAL := InstructVerificationProof.correct_GETGLOBAL.
  Definition correct_PUSHGETGLOBAL := InstructVerificationProof.correct_PUSHGETGLOBAL.
  Definition correct_GETGLOBALFIELD := InstructVerificationProof.correct_GETGLOBALFIELD.
  Definition correct_PUSHGETGLOBALFIELD := InstructVerificationProof.correct_PUSHGETGLOBALFIELD.
  Definition correct_SETGLOBAL := InstructVerificationProof.correct_SETGLOBAL.
  Definition correct_ATOM := InstructVerificationProof.correct_ATOM.
  Definition correct_PUSHATOM := InstructVerificationProof.correct_PUSHATOM.
  Definition correct_MAKEBLOCK := InstructVerificationProof.correct_MAKEBLOCK.
  Definition correct_MAKEBLOCK1 := InstructVerificationProof.correct_MAKEBLOCK1.
  Definition correct_MAKEBLOCK2 := InstructVerificationProof.correct_MAKEBLOCK2.
  Definition correct_MAKEBLOCK3 := InstructVerificationProof.correct_MAKEBLOCK3.
  Definition correct_MAKEFLOATBLOCK := InstructVerificationProof.correct_MAKEFLOATBLOCK.
  Definition correct_GETFIELD := InstructVerificationProof.correct_GETFIELD.
  Definition correct_GETFLOATFIELD := InstructVerificationProof.correct_GETFLOATFIELD.
  Definition correct_SETFIELD := InstructVerificationProof.correct_SETFIELD.
  Definition correct_SETFLOATFIELD := InstructVerificationProof.correct_SETFLOATFIELD.
  Definition correct_VECTLENGTH := InstructVerificationProof.correct_VECTLENGTH.
  Definition correct_GETVECTITEM := InstructVerificationProof.correct_GETVECTITEM.
  Definition correct_SETVECTITEM := InstructVerificationProof.correct_SETVECTITEM.
  Definition correct_GETBYTESCHAR := InstructVerificationProof.correct_GETBYTESCHAR.
  Definition correct_SETBYTESCHAR := InstructVerificationProof.correct_SETBYTESCHAR.
  Definition correct_GETSTRINGCHAR := InstructVerificationProof.correct_GETSTRINGCHAR.
  Definition correct_BRANCH := InstructVerificationProof.correct_BRANCH.
  Definition correct_BRANCHIF := InstructVerificationProof.correct_BRANCHIF.
  Definition correct_BRANCHIFNOT := InstructVerificationProof.correct_BRANCHIFNOT.
  Definition correct_SWITCH := InstructVerificationProof.correct_SWITCH.
  Definition correct_BOOLNOT := InstructVerificationProof.correct_BOOLNOT.
  Definition correct_PUSHTRAP := InstructVerificationProof.correct_PUSHTRAP.
  Definition correct_POPTRAP := InstructVerificationProof.correct_POPTRAP.
  Definition correct_RAISE := InstructVerificationProof.correct_RAISE.
  Definition correct_RERAISE := InstructVerificationProof.correct_RERAISE.
  Definition correct_RAISE_NOTRACE := InstructVerificationProof.correct_RAISE_NOTRACE.
  Definition correct_CHECK_SIGNALS := InstructVerificationProof.correct_CHECK_SIGNALS.
  Definition correct_C_CALL := InstructVerificationProof.correct_C_CALL.
  Definition correct_CONSTINT := InstructVerificationProof.correct_CONSTINT.
  Definition correct_PUSHCONSTINT := InstructVerificationProof.correct_PUSHCONSTINT.
  Definition correct_NEGINT := InstructVerificationProof.correct_NEGINT.
  Definition correct_ADDINT := InstructVerificationProof.correct_ADDINT.
  Definition correct_SUBINT := InstructVerificationProof.correct_SUBINT.
  Definition correct_MULINT := InstructVerificationProof.correct_MULINT.
  Definition correct_DIVINT := InstructVerificationProof.correct_DIVINT.
  Definition correct_MODINT := InstructVerificationProof.correct_MODINT.
  Definition correct_ANDINT := InstructVerificationProof.correct_ANDINT.
  Definition correct_ORINT := InstructVerificationProof.correct_ORINT.
  Definition correct_XORINT := InstructVerificationProof.correct_XORINT.
  Definition correct_LSLINT := InstructVerificationProof.correct_LSLINT.
  Definition correct_LSRINT := InstructVerificationProof.correct_LSRINT.
  Definition correct_ASRINT := InstructVerificationProof.correct_ASRINT.
  Definition correct_EQ := InstructVerificationProof.correct_EQ.
  Definition correct_NEQ := InstructVerificationProof.correct_NEQ.
  Definition correct_LTINT := InstructVerificationProof.correct_LTINT.
  Definition correct_LEINT := InstructVerificationProof.correct_LEINT.
  Definition correct_GTINT := InstructVerificationProof.correct_GTINT.
  Definition correct_GEINT := InstructVerificationProof.correct_GEINT.
  Definition correct_OFFSETINT := InstructVerificationProof.correct_OFFSETINT.
  Definition correct_OFFSETREF := InstructVerificationProof.correct_OFFSETREF.
  Definition correct_ISINT := InstructVerificationProof.correct_ISINT.
  Definition correct_GETMETHOD := InstructVerificationProof.correct_GETMETHOD.
  Definition correct_GETPUBMET := InstructVerificationProof.correct_GETPUBMET.
  Definition correct_GETDYNMET := InstructVerificationProof.correct_GETDYNMET.
  Definition correct_BEQ := InstructVerificationProof.correct_BEQ.
  Definition correct_BNEQ := InstructVerificationProof.correct_BNEQ.
  Definition correct_BLTINT := InstructVerificationProof.correct_BLTINT.
  Definition correct_BLEINT := InstructVerificationProof.correct_BLEINT.
  Definition correct_BGTINT := InstructVerificationProof.correct_BGTINT.
  Definition correct_BGEINT := InstructVerificationProof.correct_BGEINT.
  Definition correct_ULTINT := InstructVerificationProof.correct_ULTINT.
  Definition correct_UGEINT := InstructVerificationProof.correct_UGEINT.
  Definition correct_BULTINT := InstructVerificationProof.correct_BULTINT.
  Definition correct_BUGEINT := InstructVerificationProof.correct_BUGEINT.
  Definition correct_STOP := InstructVerificationProof.correct_STOP.

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
  InstructVerificationFromFineGrained InstructVerificationProof.DispatchHI InstructVerification.

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
