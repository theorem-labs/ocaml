(* MetaSpecProof.v - [UNTRUSTED] Fine-grained implementation of the handler
   uniqueness meta-specification.

   Each per-instruction uniqueness lemma is proved (with Qed, no Admitted)
   in automatic/Bytecode/MetaSpecVerification/<INSTR>_unique.v and
   re-exported here.  All 94 per-instruction proofs delegate to the single
   shared axiom handler_correct_determines_em_eq in SharedLemmas.v. *)

From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require
  ACC_unique
  PUSH_unique
  PUSHACC_unique
  POP_unique
  ASSIGN_unique
  ENVACC_unique
  PUSHENVACC_unique
  PUSH_RETADDR_unique
  APPLY_unique
  APPLY1_unique
  APPLY2_unique
  APPLY3_unique
  APPTERM_unique
  APPTERM1_unique
  APPTERM2_unique
  APPTERM3_unique
  RETURN_unique
  RESTART_unique
  GRAB_unique
  CLOSURE_unique
  CLOSUREREC_unique
  OFFSETCLOSURE_unique
  PUSHOFFSETCLOSURE_unique
  GETGLOBAL_unique
  PUSHGETGLOBAL_unique
  GETGLOBALFIELD_unique
  PUSHGETGLOBALFIELD_unique
  SETGLOBAL_unique
  ATOM_unique
  PUSHATOM_unique
  MAKEBLOCK_unique
  MAKEBLOCK1_unique
  MAKEBLOCK2_unique
  MAKEBLOCK3_unique
  MAKEFLOATBLOCK_unique
  GETFIELD_unique
  GETFLOATFIELD_unique
  SETFIELD_unique
  SETFLOATFIELD_unique
  VECTLENGTH_unique
  GETVECTITEM_unique
  SETVECTITEM_unique
  GETBYTESCHAR_unique
  SETBYTESCHAR_unique
  GETSTRINGCHAR_unique
  BRANCH_unique
  BRANCHIF_unique
  BRANCHIFNOT_unique
  SWITCH_unique
  BOOLNOT_unique
  PUSHTRAP_unique
  POPTRAP_unique
  RAISE_unique
  RERAISE_unique
  RAISE_NOTRACE_unique
  CHECK_SIGNALS_unique
  C_CALL_unique
  CONSTINT_unique
  PUSHCONSTINT_unique
  NEGINT_unique
  ADDINT_unique
  SUBINT_unique
  MULINT_unique
  DIVINT_unique
  MODINT_unique
  ANDINT_unique
  ORINT_unique
  XORINT_unique
  LSLINT_unique
  LSRINT_unique
  ASRINT_unique
  EQ_unique
  NEQ_unique
  LTINT_unique
  LEINT_unique
  GTINT_unique
  GEINT_unique
  OFFSETINT_unique
  OFFSETREF_unique
  ISINT_unique
  GETMETHOD_unique
  GETPUBMET_unique
  GETDYNMET_unique
  BEQ_unique
  BNEQ_unique
  BLTINT_unique
  BLEINT_unique
  BGTINT_unique
  BGEINT_unique
  ULTINT_unique
  UGEINT_unique
  BULTINT_unique
  BUGEINT_unique
  STOP_unique.

Definition unique_ACC := ACC_unique.unique_ACC.
Definition unique_PUSH := PUSH_unique.unique_PUSH.
Definition unique_PUSHACC := PUSHACC_unique.unique_PUSHACC.
Definition unique_POP := POP_unique.unique_POP.
Definition unique_ASSIGN := ASSIGN_unique.unique_ASSIGN.
Definition unique_ENVACC := ENVACC_unique.unique_ENVACC.
Definition unique_PUSHENVACC := PUSHENVACC_unique.unique_PUSHENVACC.
Definition unique_PUSH_RETADDR := PUSH_RETADDR_unique.unique_PUSH_RETADDR.
Definition unique_APPLY := APPLY_unique.unique_APPLY.
Definition unique_APPLY1 := APPLY1_unique.unique_APPLY1.
Definition unique_APPLY2 := APPLY2_unique.unique_APPLY2.
Definition unique_APPLY3 := APPLY3_unique.unique_APPLY3.
Definition unique_APPTERM := APPTERM_unique.unique_APPTERM.
Definition unique_APPTERM1 := APPTERM1_unique.unique_APPTERM1.
Definition unique_APPTERM2 := APPTERM2_unique.unique_APPTERM2.
Definition unique_APPTERM3 := APPTERM3_unique.unique_APPTERM3.
Definition unique_RETURN := RETURN_unique.unique_RETURN.
Definition unique_RESTART := RESTART_unique.unique_RESTART.
Definition unique_GRAB := GRAB_unique.unique_GRAB.
Definition unique_CLOSURE := CLOSURE_unique.unique_CLOSURE.
Definition unique_CLOSUREREC := CLOSUREREC_unique.unique_CLOSUREREC.
Definition unique_OFFSETCLOSURE := OFFSETCLOSURE_unique.unique_OFFSETCLOSURE.
Definition unique_PUSHOFFSETCLOSURE := PUSHOFFSETCLOSURE_unique.unique_PUSHOFFSETCLOSURE.
Definition unique_GETGLOBAL := GETGLOBAL_unique.unique_GETGLOBAL.
Definition unique_PUSHGETGLOBAL := PUSHGETGLOBAL_unique.unique_PUSHGETGLOBAL.
Definition unique_GETGLOBALFIELD := GETGLOBALFIELD_unique.unique_GETGLOBALFIELD.
Definition unique_PUSHGETGLOBALFIELD := PUSHGETGLOBALFIELD_unique.unique_PUSHGETGLOBALFIELD.
Definition unique_SETGLOBAL := SETGLOBAL_unique.unique_SETGLOBAL.
Definition unique_ATOM := ATOM_unique.unique_ATOM.
Definition unique_PUSHATOM := PUSHATOM_unique.unique_PUSHATOM.
Definition unique_MAKEBLOCK := MAKEBLOCK_unique.unique_MAKEBLOCK.
Definition unique_MAKEBLOCK1 := MAKEBLOCK1_unique.unique_MAKEBLOCK1.
Definition unique_MAKEBLOCK2 := MAKEBLOCK2_unique.unique_MAKEBLOCK2.
Definition unique_MAKEBLOCK3 := MAKEBLOCK3_unique.unique_MAKEBLOCK3.
Definition unique_MAKEFLOATBLOCK := MAKEFLOATBLOCK_unique.unique_MAKEFLOATBLOCK.
Definition unique_GETFIELD := GETFIELD_unique.unique_GETFIELD.
Definition unique_GETFLOATFIELD := GETFLOATFIELD_unique.unique_GETFLOATFIELD.
Definition unique_SETFIELD := SETFIELD_unique.unique_SETFIELD.
Definition unique_SETFLOATFIELD := SETFLOATFIELD_unique.unique_SETFLOATFIELD.
Definition unique_VECTLENGTH := VECTLENGTH_unique.unique_VECTLENGTH.
Definition unique_GETVECTITEM := GETVECTITEM_unique.unique_GETVECTITEM.
Definition unique_SETVECTITEM := SETVECTITEM_unique.unique_SETVECTITEM.
Definition unique_GETBYTESCHAR := GETBYTESCHAR_unique.unique_GETBYTESCHAR.
Definition unique_SETBYTESCHAR := SETBYTESCHAR_unique.unique_SETBYTESCHAR.
Definition unique_GETSTRINGCHAR := GETSTRINGCHAR_unique.unique_GETSTRINGCHAR.
Definition unique_BRANCH := BRANCH_unique.unique_BRANCH.
Definition unique_BRANCHIF := BRANCHIF_unique.unique_BRANCHIF.
Definition unique_BRANCHIFNOT := BRANCHIFNOT_unique.unique_BRANCHIFNOT.
Definition unique_SWITCH := SWITCH_unique.unique_SWITCH.
Definition unique_BOOLNOT := BOOLNOT_unique.unique_BOOLNOT.
Definition unique_PUSHTRAP := PUSHTRAP_unique.unique_PUSHTRAP.
Definition unique_POPTRAP := POPTRAP_unique.unique_POPTRAP.
Definition unique_RAISE := RAISE_unique.unique_RAISE.
Definition unique_RERAISE := RERAISE_unique.unique_RERAISE.
Definition unique_RAISE_NOTRACE := RAISE_NOTRACE_unique.unique_RAISE_NOTRACE.
Definition unique_CHECK_SIGNALS := CHECK_SIGNALS_unique.unique_CHECK_SIGNALS.
Definition unique_C_CALL := C_CALL_unique.unique_C_CALL.
Definition unique_CONSTINT := CONSTINT_unique.unique_CONSTINT.
Definition unique_PUSHCONSTINT := PUSHCONSTINT_unique.unique_PUSHCONSTINT.
Definition unique_NEGINT := NEGINT_unique.unique_NEGINT.
Definition unique_ADDINT := ADDINT_unique.unique_ADDINT.
Definition unique_SUBINT := SUBINT_unique.unique_SUBINT.
Definition unique_MULINT := MULINT_unique.unique_MULINT.
Definition unique_DIVINT := DIVINT_unique.unique_DIVINT.
Definition unique_MODINT := MODINT_unique.unique_MODINT.
Definition unique_ANDINT := ANDINT_unique.unique_ANDINT.
Definition unique_ORINT := ORINT_unique.unique_ORINT.
Definition unique_XORINT := XORINT_unique.unique_XORINT.
Definition unique_LSLINT := LSLINT_unique.unique_LSLINT.
Definition unique_LSRINT := LSRINT_unique.unique_LSRINT.
Definition unique_ASRINT := ASRINT_unique.unique_ASRINT.
Definition unique_EQ := EQ_unique.unique_EQ.
Definition unique_NEQ := NEQ_unique.unique_NEQ.
Definition unique_LTINT := LTINT_unique.unique_LTINT.
Definition unique_LEINT := LEINT_unique.unique_LEINT.
Definition unique_GTINT := GTINT_unique.unique_GTINT.
Definition unique_GEINT := GEINT_unique.unique_GEINT.
Definition unique_OFFSETINT := OFFSETINT_unique.unique_OFFSETINT.
Definition unique_OFFSETREF := OFFSETREF_unique.unique_OFFSETREF.
Definition unique_ISINT := ISINT_unique.unique_ISINT.
Definition unique_GETMETHOD := GETMETHOD_unique.unique_GETMETHOD.
Definition unique_GETPUBMET := GETPUBMET_unique.unique_GETPUBMET.
Definition unique_GETDYNMET := GETDYNMET_unique.unique_GETDYNMET.
Definition unique_BEQ := BEQ_unique.unique_BEQ.
Definition unique_BNEQ := BNEQ_unique.unique_BNEQ.
Definition unique_BLTINT := BLTINT_unique.unique_BLTINT.
Definition unique_BLEINT := BLEINT_unique.unique_BLEINT.
Definition unique_BGTINT := BGTINT_unique.unique_BGTINT.
Definition unique_BGEINT := BGEINT_unique.unique_BGEINT.
Definition unique_ULTINT := ULTINT_unique.unique_ULTINT.
Definition unique_UGEINT := UGEINT_unique.unique_UGEINT.
Definition unique_BULTINT := BULTINT_unique.unique_BULTINT.
Definition unique_BUGEINT := BUGEINT_unique.unique_BUGEINT.
Definition unique_STOP := STOP_unique.unique_STOP.

Module FG <: MetaSpecFineGrainedSpec.
  Definition unique_ACC := unique_ACC.
  Definition unique_PUSH := unique_PUSH.
  Definition unique_PUSHACC := unique_PUSHACC.
  Definition unique_POP := unique_POP.
  Definition unique_ASSIGN := unique_ASSIGN.
  Definition unique_ENVACC := unique_ENVACC.
  Definition unique_PUSHENVACC := unique_PUSHENVACC.
  Definition unique_PUSH_RETADDR := unique_PUSH_RETADDR.
  Definition unique_APPLY := unique_APPLY.
  Definition unique_APPLY1 := unique_APPLY1.
  Definition unique_APPLY2 := unique_APPLY2.
  Definition unique_APPLY3 := unique_APPLY3.
  Definition unique_APPTERM := unique_APPTERM.
  Definition unique_APPTERM1 := unique_APPTERM1.
  Definition unique_APPTERM2 := unique_APPTERM2.
  Definition unique_APPTERM3 := unique_APPTERM3.
  Definition unique_RETURN := unique_RETURN.
  Definition unique_RESTART := unique_RESTART.
  Definition unique_GRAB := unique_GRAB.
  Definition unique_CLOSURE := unique_CLOSURE.
  Definition unique_CLOSUREREC := unique_CLOSUREREC.
  Definition unique_OFFSETCLOSURE := unique_OFFSETCLOSURE.
  Definition unique_PUSHOFFSETCLOSURE := unique_PUSHOFFSETCLOSURE.
  Definition unique_GETGLOBAL := unique_GETGLOBAL.
  Definition unique_PUSHGETGLOBAL := unique_PUSHGETGLOBAL.
  Definition unique_GETGLOBALFIELD := unique_GETGLOBALFIELD.
  Definition unique_PUSHGETGLOBALFIELD := unique_PUSHGETGLOBALFIELD.
  Definition unique_SETGLOBAL := unique_SETGLOBAL.
  Definition unique_ATOM := unique_ATOM.
  Definition unique_PUSHATOM := unique_PUSHATOM.
  Definition unique_MAKEBLOCK := unique_MAKEBLOCK.
  Definition unique_MAKEBLOCK1 := unique_MAKEBLOCK1.
  Definition unique_MAKEBLOCK2 := unique_MAKEBLOCK2.
  Definition unique_MAKEBLOCK3 := unique_MAKEBLOCK3.
  Definition unique_MAKEFLOATBLOCK := unique_MAKEFLOATBLOCK.
  Definition unique_GETFIELD := unique_GETFIELD.
  Definition unique_GETFLOATFIELD := unique_GETFLOATFIELD.
  Definition unique_SETFIELD := unique_SETFIELD.
  Definition unique_SETFLOATFIELD := unique_SETFLOATFIELD.
  Definition unique_VECTLENGTH := unique_VECTLENGTH.
  Definition unique_GETVECTITEM := unique_GETVECTITEM.
  Definition unique_SETVECTITEM := unique_SETVECTITEM.
  Definition unique_GETBYTESCHAR := unique_GETBYTESCHAR.
  Definition unique_SETBYTESCHAR := unique_SETBYTESCHAR.
  Definition unique_GETSTRINGCHAR := unique_GETSTRINGCHAR.
  Definition unique_BRANCH := unique_BRANCH.
  Definition unique_BRANCHIF := unique_BRANCHIF.
  Definition unique_BRANCHIFNOT := unique_BRANCHIFNOT.
  Definition unique_SWITCH := unique_SWITCH.
  Definition unique_BOOLNOT := unique_BOOLNOT.
  Definition unique_PUSHTRAP := unique_PUSHTRAP.
  Definition unique_POPTRAP := unique_POPTRAP.
  Definition unique_RAISE := unique_RAISE.
  Definition unique_RERAISE := unique_RERAISE.
  Definition unique_RAISE_NOTRACE := unique_RAISE_NOTRACE.
  Definition unique_CHECK_SIGNALS := unique_CHECK_SIGNALS.
  Definition unique_C_CALL := unique_C_CALL.
  Definition unique_CONSTINT := unique_CONSTINT.
  Definition unique_PUSHCONSTINT := unique_PUSHCONSTINT.
  Definition unique_NEGINT := unique_NEGINT.
  Definition unique_ADDINT := unique_ADDINT.
  Definition unique_SUBINT := unique_SUBINT.
  Definition unique_MULINT := unique_MULINT.
  Definition unique_DIVINT := unique_DIVINT.
  Definition unique_MODINT := unique_MODINT.
  Definition unique_ANDINT := unique_ANDINT.
  Definition unique_ORINT := unique_ORINT.
  Definition unique_XORINT := unique_XORINT.
  Definition unique_LSLINT := unique_LSLINT.
  Definition unique_LSRINT := unique_LSRINT.
  Definition unique_ASRINT := unique_ASRINT.
  Definition unique_EQ := unique_EQ.
  Definition unique_NEQ := unique_NEQ.
  Definition unique_LTINT := unique_LTINT.
  Definition unique_LEINT := unique_LEINT.
  Definition unique_GTINT := unique_GTINT.
  Definition unique_GEINT := unique_GEINT.
  Definition unique_OFFSETINT := unique_OFFSETINT.
  Definition unique_OFFSETREF := unique_OFFSETREF.
  Definition unique_ISINT := unique_ISINT.
  Definition unique_GETMETHOD := unique_GETMETHOD.
  Definition unique_GETPUBMET := unique_GETPUBMET.
  Definition unique_GETDYNMET := unique_GETDYNMET.
  Definition unique_BEQ := unique_BEQ.
  Definition unique_BNEQ := unique_BNEQ.
  Definition unique_BLTINT := unique_BLTINT.
  Definition unique_BLEINT := unique_BLEINT.
  Definition unique_BGTINT := unique_BGTINT.
  Definition unique_BGEINT := unique_BGEINT.
  Definition unique_ULTINT := unique_ULTINT.
  Definition unique_UGEINT := unique_UGEINT.
  Definition unique_BULTINT := unique_BULTINT.
  Definition unique_BUGEINT := unique_BUGEINT.
  Definition unique_STOP := unique_STOP.
End FG.

Module M := MetaSpecFromFineGrained FG.

Definition handler_unique_mod_errors := M.handler_unique_mod_errors.
