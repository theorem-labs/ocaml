(* MetaSpecChecker.v - Verifies that the untrusted meta-spec proof satisfies
   the trusted MetaSpec and MetaSpecFineGrainedSpec module types. *)

From OCamlInterp.Manual.Bytecode.Interpret Require MetaSpec.
From OCamlInterp.Automatic.Bytecode Require MetaSpecProof.

(* Fine-grained check: each per-instruction uniqueness lemma *)
Module Check <: MetaSpec.MetaSpecFineGrainedSpec.
  Definition unique_ACC :=
    MetaSpecProof.unique_ACC.
  Definition unique_PUSH :=
    MetaSpecProof.unique_PUSH.
  Definition unique_PUSHACC :=
    MetaSpecProof.unique_PUSHACC.
  Definition unique_POP :=
    MetaSpecProof.unique_POP.
  Definition unique_ASSIGN :=
    MetaSpecProof.unique_ASSIGN.
  Definition unique_ENVACC :=
    MetaSpecProof.unique_ENVACC.
  Definition unique_PUSHENVACC :=
    MetaSpecProof.unique_PUSHENVACC.
  Definition unique_PUSH_RETADDR :=
    MetaSpecProof.unique_PUSH_RETADDR.
  Definition unique_APPLY :=
    MetaSpecProof.unique_APPLY.
  Definition unique_APPLY1 :=
    MetaSpecProof.unique_APPLY1.
  Definition unique_APPLY2 :=
    MetaSpecProof.unique_APPLY2.
  Definition unique_APPLY3 :=
    MetaSpecProof.unique_APPLY3.
  Definition unique_APPTERM :=
    MetaSpecProof.unique_APPTERM.
  Definition unique_APPTERM1 :=
    MetaSpecProof.unique_APPTERM1.
  Definition unique_APPTERM2 :=
    MetaSpecProof.unique_APPTERM2.
  Definition unique_APPTERM3 :=
    MetaSpecProof.unique_APPTERM3.
  Definition unique_RETURN :=
    MetaSpecProof.unique_RETURN.
  Definition unique_RESTART :=
    MetaSpecProof.unique_RESTART.
  Definition unique_GRAB :=
    MetaSpecProof.unique_GRAB.
  Definition unique_CLOSURE :=
    MetaSpecProof.unique_CLOSURE.
  Definition unique_CLOSUREREC :=
    MetaSpecProof.unique_CLOSUREREC.
  Definition unique_OFFSETCLOSURE :=
    MetaSpecProof.unique_OFFSETCLOSURE.
  Definition unique_PUSHOFFSETCLOSURE :=
    MetaSpecProof.unique_PUSHOFFSETCLOSURE.
  Definition unique_GETGLOBAL :=
    MetaSpecProof.unique_GETGLOBAL.
  Definition unique_PUSHGETGLOBAL :=
    MetaSpecProof.unique_PUSHGETGLOBAL.
  Definition unique_GETGLOBALFIELD :=
    MetaSpecProof.unique_GETGLOBALFIELD.
  Definition unique_PUSHGETGLOBALFIELD :=
    MetaSpecProof.unique_PUSHGETGLOBALFIELD.
  Definition unique_SETGLOBAL :=
    MetaSpecProof.unique_SETGLOBAL.
  Definition unique_ATOM :=
    MetaSpecProof.unique_ATOM.
  Definition unique_PUSHATOM :=
    MetaSpecProof.unique_PUSHATOM.
  Definition unique_MAKEBLOCK :=
    MetaSpecProof.unique_MAKEBLOCK.
  Definition unique_MAKEBLOCK1 :=
    MetaSpecProof.unique_MAKEBLOCK1.
  Definition unique_MAKEBLOCK2 :=
    MetaSpecProof.unique_MAKEBLOCK2.
  Definition unique_MAKEBLOCK3 :=
    MetaSpecProof.unique_MAKEBLOCK3.
  Definition unique_MAKEFLOATBLOCK :=
    MetaSpecProof.unique_MAKEFLOATBLOCK.
  Definition unique_GETFIELD :=
    MetaSpecProof.unique_GETFIELD.
  Definition unique_GETFLOATFIELD :=
    MetaSpecProof.unique_GETFLOATFIELD.
  Definition unique_SETFIELD :=
    MetaSpecProof.unique_SETFIELD.
  Definition unique_SETFLOATFIELD :=
    MetaSpecProof.unique_SETFLOATFIELD.
  Definition unique_VECTLENGTH :=
    MetaSpecProof.unique_VECTLENGTH.
  Definition unique_GETVECTITEM :=
    MetaSpecProof.unique_GETVECTITEM.
  Definition unique_SETVECTITEM :=
    MetaSpecProof.unique_SETVECTITEM.
  Definition unique_GETBYTESCHAR :=
    MetaSpecProof.unique_GETBYTESCHAR.
  Definition unique_SETBYTESCHAR :=
    MetaSpecProof.unique_SETBYTESCHAR.
  Definition unique_GETSTRINGCHAR :=
    MetaSpecProof.unique_GETSTRINGCHAR.
  Definition unique_BRANCH :=
    MetaSpecProof.unique_BRANCH.
  Definition unique_BRANCHIF :=
    MetaSpecProof.unique_BRANCHIF.
  Definition unique_BRANCHIFNOT :=
    MetaSpecProof.unique_BRANCHIFNOT.
  Definition unique_SWITCH :=
    MetaSpecProof.unique_SWITCH.
  Definition unique_BOOLNOT :=
    MetaSpecProof.unique_BOOLNOT.
  Definition unique_PUSHTRAP :=
    MetaSpecProof.unique_PUSHTRAP.
  Definition unique_POPTRAP :=
    MetaSpecProof.unique_POPTRAP.
  Definition unique_RAISE :=
    MetaSpecProof.unique_RAISE.
  Definition unique_RERAISE :=
    MetaSpecProof.unique_RERAISE.
  Definition unique_RAISE_NOTRACE :=
    MetaSpecProof.unique_RAISE_NOTRACE.
  Definition unique_CHECK_SIGNALS :=
    MetaSpecProof.unique_CHECK_SIGNALS.
  Definition unique_C_CALL :=
    MetaSpecProof.unique_C_CALL.
  Definition unique_CONSTINT :=
    MetaSpecProof.unique_CONSTINT.
  Definition unique_PUSHCONSTINT :=
    MetaSpecProof.unique_PUSHCONSTINT.
  Definition unique_NEGINT :=
    MetaSpecProof.unique_NEGINT.
  Definition unique_ADDINT :=
    MetaSpecProof.unique_ADDINT.
  Definition unique_SUBINT :=
    MetaSpecProof.unique_SUBINT.
  Definition unique_MULINT :=
    MetaSpecProof.unique_MULINT.
  Definition unique_DIVINT :=
    MetaSpecProof.unique_DIVINT.
  Definition unique_MODINT :=
    MetaSpecProof.unique_MODINT.
  Definition unique_ANDINT :=
    MetaSpecProof.unique_ANDINT.
  Definition unique_ORINT :=
    MetaSpecProof.unique_ORINT.
  Definition unique_XORINT :=
    MetaSpecProof.unique_XORINT.
  Definition unique_LSLINT :=
    MetaSpecProof.unique_LSLINT.
  Definition unique_LSRINT :=
    MetaSpecProof.unique_LSRINT.
  Definition unique_ASRINT :=
    MetaSpecProof.unique_ASRINT.
  Definition unique_EQ :=
    MetaSpecProof.unique_EQ.
  Definition unique_NEQ :=
    MetaSpecProof.unique_NEQ.
  Definition unique_LTINT :=
    MetaSpecProof.unique_LTINT.
  Definition unique_LEINT :=
    MetaSpecProof.unique_LEINT.
  Definition unique_GTINT :=
    MetaSpecProof.unique_GTINT.
  Definition unique_GEINT :=
    MetaSpecProof.unique_GEINT.
  Definition unique_OFFSETINT :=
    MetaSpecProof.unique_OFFSETINT.
  Definition unique_OFFSETREF :=
    MetaSpecProof.unique_OFFSETREF.
  Definition unique_ISINT :=
    MetaSpecProof.unique_ISINT.
  Definition unique_GETMETHOD :=
    MetaSpecProof.unique_GETMETHOD.
  Definition unique_GETPUBMET :=
    MetaSpecProof.unique_GETPUBMET.
  Definition unique_GETDYNMET :=
    MetaSpecProof.unique_GETDYNMET.
  Definition unique_BEQ :=
    MetaSpecProof.unique_BEQ.
  Definition unique_BNEQ :=
    MetaSpecProof.unique_BNEQ.
  Definition unique_BLTINT :=
    MetaSpecProof.unique_BLTINT.
  Definition unique_BLEINT :=
    MetaSpecProof.unique_BLEINT.
  Definition unique_BGTINT :=
    MetaSpecProof.unique_BGTINT.
  Definition unique_BGEINT :=
    MetaSpecProof.unique_BGEINT.
  Definition unique_ULTINT :=
    MetaSpecProof.unique_ULTINT.
  Definition unique_UGEINT :=
    MetaSpecProof.unique_UGEINT.
  Definition unique_BULTINT :=
    MetaSpecProof.unique_BULTINT.
  Definition unique_BUGEINT :=
    MetaSpecProof.unique_BUGEINT.
  Definition unique_STOP :=
    MetaSpecProof.unique_STOP.

  Section __.
  Set Printing All.
  Set Printing Fully Qualified.
  Set Printing Depth 10000000000.
  Set Printing Width 2000.
  Goal True.
    idtac "<unique_ACC>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_ACC.
    idtac "</PrintAssumptions>".
    idtac "</unique_ACC>".
  Abort.
  Goal True.
    idtac "<unique_PUSH>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_PUSH.
    idtac "</PrintAssumptions>".
    idtac "</unique_PUSH>".
  Abort.
  Goal True.
    idtac "<unique_PUSHACC>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_PUSHACC.
    idtac "</PrintAssumptions>".
    idtac "</unique_PUSHACC>".
  Abort.
  Goal True.
    idtac "<unique_POP>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_POP.
    idtac "</PrintAssumptions>".
    idtac "</unique_POP>".
  Abort.
  Goal True.
    idtac "<unique_ASSIGN>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_ASSIGN.
    idtac "</PrintAssumptions>".
    idtac "</unique_ASSIGN>".
  Abort.
  Goal True.
    idtac "<unique_ENVACC>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_ENVACC.
    idtac "</PrintAssumptions>".
    idtac "</unique_ENVACC>".
  Abort.
  Goal True.
    idtac "<unique_PUSHENVACC>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_PUSHENVACC.
    idtac "</PrintAssumptions>".
    idtac "</unique_PUSHENVACC>".
  Abort.
  Goal True.
    idtac "<unique_PUSH_RETADDR>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_PUSH_RETADDR.
    idtac "</PrintAssumptions>".
    idtac "</unique_PUSH_RETADDR>".
  Abort.
  Goal True.
    idtac "<unique_APPLY>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_APPLY.
    idtac "</PrintAssumptions>".
    idtac "</unique_APPLY>".
  Abort.
  Goal True.
    idtac "<unique_APPLY1>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_APPLY1.
    idtac "</PrintAssumptions>".
    idtac "</unique_APPLY1>".
  Abort.
  Goal True.
    idtac "<unique_APPLY2>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_APPLY2.
    idtac "</PrintAssumptions>".
    idtac "</unique_APPLY2>".
  Abort.
  Goal True.
    idtac "<unique_APPLY3>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_APPLY3.
    idtac "</PrintAssumptions>".
    idtac "</unique_APPLY3>".
  Abort.
  Goal True.
    idtac "<unique_APPTERM>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_APPTERM.
    idtac "</PrintAssumptions>".
    idtac "</unique_APPTERM>".
  Abort.
  Goal True.
    idtac "<unique_APPTERM1>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_APPTERM1.
    idtac "</PrintAssumptions>".
    idtac "</unique_APPTERM1>".
  Abort.
  Goal True.
    idtac "<unique_APPTERM2>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_APPTERM2.
    idtac "</PrintAssumptions>".
    idtac "</unique_APPTERM2>".
  Abort.
  Goal True.
    idtac "<unique_APPTERM3>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_APPTERM3.
    idtac "</PrintAssumptions>".
    idtac "</unique_APPTERM3>".
  Abort.
  Goal True.
    idtac "<unique_RETURN>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_RETURN.
    idtac "</PrintAssumptions>".
    idtac "</unique_RETURN>".
  Abort.
  Goal True.
    idtac "<unique_RESTART>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_RESTART.
    idtac "</PrintAssumptions>".
    idtac "</unique_RESTART>".
  Abort.
  Goal True.
    idtac "<unique_GRAB>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_GRAB.
    idtac "</PrintAssumptions>".
    idtac "</unique_GRAB>".
  Abort.
  Goal True.
    idtac "<unique_CLOSURE>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_CLOSURE.
    idtac "</PrintAssumptions>".
    idtac "</unique_CLOSURE>".
  Abort.
  Goal True.
    idtac "<unique_CLOSUREREC>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_CLOSUREREC.
    idtac "</PrintAssumptions>".
    idtac "</unique_CLOSUREREC>".
  Abort.
  Goal True.
    idtac "<unique_OFFSETCLOSURE>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_OFFSETCLOSURE.
    idtac "</PrintAssumptions>".
    idtac "</unique_OFFSETCLOSURE>".
  Abort.
  Goal True.
    idtac "<unique_PUSHOFFSETCLOSURE>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_PUSHOFFSETCLOSURE.
    idtac "</PrintAssumptions>".
    idtac "</unique_PUSHOFFSETCLOSURE>".
  Abort.
  Goal True.
    idtac "<unique_GETGLOBAL>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_GETGLOBAL.
    idtac "</PrintAssumptions>".
    idtac "</unique_GETGLOBAL>".
  Abort.
  Goal True.
    idtac "<unique_PUSHGETGLOBAL>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_PUSHGETGLOBAL.
    idtac "</PrintAssumptions>".
    idtac "</unique_PUSHGETGLOBAL>".
  Abort.
  Goal True.
    idtac "<unique_GETGLOBALFIELD>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_GETGLOBALFIELD.
    idtac "</PrintAssumptions>".
    idtac "</unique_GETGLOBALFIELD>".
  Abort.
  Goal True.
    idtac "<unique_PUSHGETGLOBALFIELD>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_PUSHGETGLOBALFIELD.
    idtac "</PrintAssumptions>".
    idtac "</unique_PUSHGETGLOBALFIELD>".
  Abort.
  Goal True.
    idtac "<unique_SETGLOBAL>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_SETGLOBAL.
    idtac "</PrintAssumptions>".
    idtac "</unique_SETGLOBAL>".
  Abort.
  Goal True.
    idtac "<unique_ATOM>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_ATOM.
    idtac "</PrintAssumptions>".
    idtac "</unique_ATOM>".
  Abort.
  Goal True.
    idtac "<unique_PUSHATOM>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_PUSHATOM.
    idtac "</PrintAssumptions>".
    idtac "</unique_PUSHATOM>".
  Abort.
  Goal True.
    idtac "<unique_MAKEBLOCK>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_MAKEBLOCK.
    idtac "</PrintAssumptions>".
    idtac "</unique_MAKEBLOCK>".
  Abort.
  Goal True.
    idtac "<unique_MAKEBLOCK1>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_MAKEBLOCK1.
    idtac "</PrintAssumptions>".
    idtac "</unique_MAKEBLOCK1>".
  Abort.
  Goal True.
    idtac "<unique_MAKEBLOCK2>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_MAKEBLOCK2.
    idtac "</PrintAssumptions>".
    idtac "</unique_MAKEBLOCK2>".
  Abort.
  Goal True.
    idtac "<unique_MAKEBLOCK3>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_MAKEBLOCK3.
    idtac "</PrintAssumptions>".
    idtac "</unique_MAKEBLOCK3>".
  Abort.
  Goal True.
    idtac "<unique_MAKEFLOATBLOCK>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_MAKEFLOATBLOCK.
    idtac "</PrintAssumptions>".
    idtac "</unique_MAKEFLOATBLOCK>".
  Abort.
  Goal True.
    idtac "<unique_GETFIELD>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_GETFIELD.
    idtac "</PrintAssumptions>".
    idtac "</unique_GETFIELD>".
  Abort.
  Goal True.
    idtac "<unique_GETFLOATFIELD>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_GETFLOATFIELD.
    idtac "</PrintAssumptions>".
    idtac "</unique_GETFLOATFIELD>".
  Abort.
  Goal True.
    idtac "<unique_SETFIELD>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_SETFIELD.
    idtac "</PrintAssumptions>".
    idtac "</unique_SETFIELD>".
  Abort.
  Goal True.
    idtac "<unique_SETFLOATFIELD>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_SETFLOATFIELD.
    idtac "</PrintAssumptions>".
    idtac "</unique_SETFLOATFIELD>".
  Abort.
  Goal True.
    idtac "<unique_VECTLENGTH>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_VECTLENGTH.
    idtac "</PrintAssumptions>".
    idtac "</unique_VECTLENGTH>".
  Abort.
  Goal True.
    idtac "<unique_GETVECTITEM>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_GETVECTITEM.
    idtac "</PrintAssumptions>".
    idtac "</unique_GETVECTITEM>".
  Abort.
  Goal True.
    idtac "<unique_SETVECTITEM>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_SETVECTITEM.
    idtac "</PrintAssumptions>".
    idtac "</unique_SETVECTITEM>".
  Abort.
  Goal True.
    idtac "<unique_GETBYTESCHAR>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_GETBYTESCHAR.
    idtac "</PrintAssumptions>".
    idtac "</unique_GETBYTESCHAR>".
  Abort.
  Goal True.
    idtac "<unique_SETBYTESCHAR>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_SETBYTESCHAR.
    idtac "</PrintAssumptions>".
    idtac "</unique_SETBYTESCHAR>".
  Abort.
  Goal True.
    idtac "<unique_GETSTRINGCHAR>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_GETSTRINGCHAR.
    idtac "</PrintAssumptions>".
    idtac "</unique_GETSTRINGCHAR>".
  Abort.
  Goal True.
    idtac "<unique_BRANCH>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_BRANCH.
    idtac "</PrintAssumptions>".
    idtac "</unique_BRANCH>".
  Abort.
  Goal True.
    idtac "<unique_BRANCHIF>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_BRANCHIF.
    idtac "</PrintAssumptions>".
    idtac "</unique_BRANCHIF>".
  Abort.
  Goal True.
    idtac "<unique_BRANCHIFNOT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_BRANCHIFNOT.
    idtac "</PrintAssumptions>".
    idtac "</unique_BRANCHIFNOT>".
  Abort.
  Goal True.
    idtac "<unique_SWITCH>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_SWITCH.
    idtac "</PrintAssumptions>".
    idtac "</unique_SWITCH>".
  Abort.
  Goal True.
    idtac "<unique_BOOLNOT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_BOOLNOT.
    idtac "</PrintAssumptions>".
    idtac "</unique_BOOLNOT>".
  Abort.
  Goal True.
    idtac "<unique_PUSHTRAP>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_PUSHTRAP.
    idtac "</PrintAssumptions>".
    idtac "</unique_PUSHTRAP>".
  Abort.
  Goal True.
    idtac "<unique_POPTRAP>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_POPTRAP.
    idtac "</PrintAssumptions>".
    idtac "</unique_POPTRAP>".
  Abort.
  Goal True.
    idtac "<unique_RAISE>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_RAISE.
    idtac "</PrintAssumptions>".
    idtac "</unique_RAISE>".
  Abort.
  Goal True.
    idtac "<unique_RERAISE>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_RERAISE.
    idtac "</PrintAssumptions>".
    idtac "</unique_RERAISE>".
  Abort.
  Goal True.
    idtac "<unique_RAISE_NOTRACE>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_RAISE_NOTRACE.
    idtac "</PrintAssumptions>".
    idtac "</unique_RAISE_NOTRACE>".
  Abort.
  Goal True.
    idtac "<unique_CHECK_SIGNALS>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_CHECK_SIGNALS.
    idtac "</PrintAssumptions>".
    idtac "</unique_CHECK_SIGNALS>".
  Abort.
  Goal True.
    idtac "<unique_C_CALL>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_C_CALL.
    idtac "</PrintAssumptions>".
    idtac "</unique_C_CALL>".
  Abort.
  Goal True.
    idtac "<unique_CONSTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_CONSTINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_CONSTINT>".
  Abort.
  Goal True.
    idtac "<unique_PUSHCONSTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_PUSHCONSTINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_PUSHCONSTINT>".
  Abort.
  Goal True.
    idtac "<unique_NEGINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_NEGINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_NEGINT>".
  Abort.
  Goal True.
    idtac "<unique_ADDINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_ADDINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_ADDINT>".
  Abort.
  Goal True.
    idtac "<unique_SUBINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_SUBINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_SUBINT>".
  Abort.
  Goal True.
    idtac "<unique_MULINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_MULINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_MULINT>".
  Abort.
  Goal True.
    idtac "<unique_DIVINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_DIVINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_DIVINT>".
  Abort.
  Goal True.
    idtac "<unique_MODINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_MODINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_MODINT>".
  Abort.
  Goal True.
    idtac "<unique_ANDINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_ANDINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_ANDINT>".
  Abort.
  Goal True.
    idtac "<unique_ORINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_ORINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_ORINT>".
  Abort.
  Goal True.
    idtac "<unique_XORINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_XORINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_XORINT>".
  Abort.
  Goal True.
    idtac "<unique_LSLINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_LSLINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_LSLINT>".
  Abort.
  Goal True.
    idtac "<unique_LSRINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_LSRINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_LSRINT>".
  Abort.
  Goal True.
    idtac "<unique_ASRINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_ASRINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_ASRINT>".
  Abort.
  Goal True.
    idtac "<unique_EQ>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_EQ.
    idtac "</PrintAssumptions>".
    idtac "</unique_EQ>".
  Abort.
  Goal True.
    idtac "<unique_NEQ>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_NEQ.
    idtac "</PrintAssumptions>".
    idtac "</unique_NEQ>".
  Abort.
  Goal True.
    idtac "<unique_LTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_LTINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_LTINT>".
  Abort.
  Goal True.
    idtac "<unique_LEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_LEINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_LEINT>".
  Abort.
  Goal True.
    idtac "<unique_GTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_GTINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_GTINT>".
  Abort.
  Goal True.
    idtac "<unique_GEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_GEINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_GEINT>".
  Abort.
  Goal True.
    idtac "<unique_OFFSETINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_OFFSETINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_OFFSETINT>".
  Abort.
  Goal True.
    idtac "<unique_OFFSETREF>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_OFFSETREF.
    idtac "</PrintAssumptions>".
    idtac "</unique_OFFSETREF>".
  Abort.
  Goal True.
    idtac "<unique_ISINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_ISINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_ISINT>".
  Abort.
  Goal True.
    idtac "<unique_GETMETHOD>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_GETMETHOD.
    idtac "</PrintAssumptions>".
    idtac "</unique_GETMETHOD>".
  Abort.
  Goal True.
    idtac "<unique_GETPUBMET>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_GETPUBMET.
    idtac "</PrintAssumptions>".
    idtac "</unique_GETPUBMET>".
  Abort.
  Goal True.
    idtac "<unique_GETDYNMET>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_GETDYNMET.
    idtac "</PrintAssumptions>".
    idtac "</unique_GETDYNMET>".
  Abort.
  Goal True.
    idtac "<unique_BEQ>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_BEQ.
    idtac "</PrintAssumptions>".
    idtac "</unique_BEQ>".
  Abort.
  Goal True.
    idtac "<unique_BNEQ>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_BNEQ.
    idtac "</PrintAssumptions>".
    idtac "</unique_BNEQ>".
  Abort.
  Goal True.
    idtac "<unique_BLTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_BLTINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_BLTINT>".
  Abort.
  Goal True.
    idtac "<unique_BLEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_BLEINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_BLEINT>".
  Abort.
  Goal True.
    idtac "<unique_BGTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_BGTINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_BGTINT>".
  Abort.
  Goal True.
    idtac "<unique_BGEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_BGEINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_BGEINT>".
  Abort.
  Goal True.
    idtac "<unique_ULTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_ULTINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_ULTINT>".
  Abort.
  Goal True.
    idtac "<unique_UGEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_UGEINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_UGEINT>".
  Abort.
  Goal True.
    idtac "<unique_BULTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_BULTINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_BULTINT>".
  Abort.
  Goal True.
    idtac "<unique_BUGEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_BUGEINT.
    idtac "</PrintAssumptions>".
    idtac "</unique_BUGEINT>".
  Abort.
  Goal True.
    idtac "<unique_STOP>".
    idtac "<PrintAssumptions>".
    Print Assumptions unique_STOP.
    idtac "</PrintAssumptions>".
    idtac "</unique_STOP>".
  Abort.
  End __.

End Check.

(* Also verify the assembled unified MetaSpec *)
Module CheckAssembled <: MetaSpec.MetaSpec.
  Definition handler_unique_mod_errors :=
    MetaSpecProof.handler_unique_mod_errors.

  Section __.
  Set Printing All.
  Set Printing Fully Qualified.
  Set Printing Depth 10000000000.
  Set Printing Width 2000.
  Goal True.
    idtac "<handler_unique_mod_errors>".
    idtac "<PrintAssumptions>".
    Print Assumptions handler_unique_mod_errors.
    idtac "</PrintAssumptions>".
    idtac "</handler_unique_mod_errors>".
  Abort.
  End __.

End CheckAssembled.
