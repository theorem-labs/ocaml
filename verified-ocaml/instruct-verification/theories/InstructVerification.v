(* InstructVerification.v — Instantiation of InstructVerificationSpec. *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Require Import InstructSpec.

Require Import ACC0_correct.
Require Import ACC1_correct.
Require Import ACC2_correct.
Require Import ACC3_correct.
Require Import ACC4_correct.
Require Import ACC5_correct.
Require Import ACC6_correct.
Require Import ACC7_correct.
Require Import ACC_correct.
Require Import ADDINT_correct.
Require Import ANDINT_correct.
Require Import APPLY1_correct.
Require Import APPLY2_correct.
Require Import APPLY3_correct.
Require Import APPLY_correct.
Require Import APPTERM1_correct.
Require Import APPTERM2_correct.
Require Import APPTERM3_correct.
Require Import APPTERM_correct.
Require Import ASRINT_correct.
Require Import ASSIGN_correct.
Require Import ATOM0_correct.
Require Import ATOM_correct.
Require Import BEQ_correct.
Require Import BGEINT_correct.
Require Import BGTINT_correct.
Require Import BLEINT_correct.
Require Import BLTINT_correct.
Require Import BNEQ_correct.
Require Import BOOLNOT_correct.
Require Import BRANCHIFNOT_correct.
Require Import BRANCHIF_correct.
Require Import BRANCH_correct.
Require Import BREAK_correct.
Require Import BUGEINT_correct.
Require Import BULTINT_correct.
Require Import CHECK_SIGNALS_correct.
Require Import CLOSUREREC_correct.
Require Import CLOSURE_correct.
Require Import CONST0_correct.
Require Import CONST1_correct.
Require Import CONST2_correct.
Require Import CONST3_correct.
Require Import CONSTINT_correct.
Require Import C_CALL1_correct.
Require Import C_CALL2_correct.
Require Import C_CALL3_correct.
Require Import C_CALL4_correct.
Require Import C_CALL5_correct.
Require Import C_CALLN_correct.
Require Import DIVINT_correct.
Require Import ENVACC1_correct.
Require Import ENVACC2_correct.
Require Import ENVACC3_correct.
Require Import ENVACC4_correct.
Require Import ENVACC_correct.
Require Import EQ_correct.
Require Import EVENT_correct.
Require Import GEINT_correct.
Require Import GETBYTESCHAR_correct.
Require Import GETDYNMET_correct.
Require Import GETFIELD0_correct.
Require Import GETFIELD1_correct.
Require Import GETFIELD2_correct.
Require Import GETFIELD3_correct.
Require Import GETFIELD_correct.
Require Import GETFLOATFIELD_correct.
Require Import GETGLOBALFIELD_correct.
Require Import GETGLOBAL_correct.
Require Import GETMETHOD_correct.
Require Import GETPUBMET_correct.
Require Import GETSTRINGCHAR_correct.
Require Import GETVECTITEM_correct.
Require Import GRAB_correct.
Require Import GTINT_correct.
Require Import ISINT_correct.
Require Import LEINT_correct.
Require Import LSLINT_correct.
Require Import LSRINT_correct.
Require Import LTINT_correct.
Require Import MAKEBLOCK1_correct.
Require Import MAKEBLOCK2_correct.
Require Import MAKEBLOCK3_correct.
Require Import MAKEBLOCK_correct.
Require Import MAKEFLOATBLOCK_correct.
Require Import MODINT_correct.
Require Import MULINT_correct.
Require Import NEGINT_correct.
Require Import NEQ_correct.
Require Import OFFSETCLOSURE0_correct.
Require Import OFFSETCLOSURE2_correct.
Require Import OFFSETCLOSUREM2_correct.
Require Import OFFSETCLOSURE_correct.
Require Import OFFSETINT_correct.
Require Import OFFSETREF_correct.
Require Import ORINT_correct.
Require Import PERFORM_correct.
Require Import POPTRAP_correct.
Require Import POP_correct.
Require Import PUSHACC1_correct.
Require Import PUSHACC2_correct.
Require Import PUSHACC3_correct.
Require Import PUSHACC4_correct.
Require Import PUSHACC5_correct.
Require Import PUSHACC6_correct.
Require Import PUSHACC7_correct.
Require Import PUSHATOM0_correct.
Require Import PUSHATOM_correct.
Require Import PUSHCONST0_correct.
Require Import PUSHCONST1_correct.
Require Import PUSHCONST2_correct.
Require Import PUSHCONST3_correct.
Require Import PUSHCONSTINT_correct.
Require Import PUSHENVACC1_correct.
Require Import PUSHENVACC2_correct.
Require Import PUSHENVACC3_correct.
Require Import PUSHENVACC4_correct.
Require Import PUSHENVACC_correct.
Require Import PUSHGETGLOBALFIELD_correct.
Require Import PUSHGETGLOBAL_correct.
Require Import PUSHOFFSETCLOSURE0_correct.
Require Import PUSHOFFSETCLOSURE2_correct.
Require Import PUSHOFFSETCLOSUREM2_correct.
Require Import PUSHOFFSETCLOSURE_correct.
Require Import PUSHTRAP_correct.
Require Import PUSH_RETADDR_correct.
Require Import PUSH_correct.
Require Import RAISE_NOTRACE_correct.
Require Import RAISE_correct.
Require Import REPERFORMTERM_correct.
Require Import RERAISE_correct.
Require Import RESTART_correct.
Require Import RESUMETERM_correct.
Require Import RESUME_correct.
Require Import RETURN_correct.
Require Import SETBYTESCHAR_correct.
Require Import SETFIELD0_correct.
Require Import SETFIELD1_correct.
Require Import SETFIELD2_correct.
Require Import SETFIELD3_correct.
Require Import SETFIELD_correct.
Require Import SETFLOATFIELD_correct.
Require Import SETGLOBAL_correct.
Require Import SETVECTITEM_correct.
Require Import STOP_correct.
Require Import SUBINT_correct.
Require Import SWITCH_correct.
Require Import UGEINT_correct.
Require Import ULTINT_correct.
Require Import VECTLENGTH_correct.
Require Import XORINT_correct.

(* 151 verified handlers *)

Module InstructVerification <: InstructVerificationSpec.

  Definition verified_ACC0 := mk_handler_verified verify_ACC0_compl_comp.
  Definition verified_ACC1 := mk_handler_verified verify_ACC1.
  Definition verified_ACC2 := mk_handler_verified verify_ACC2.
  Definition verified_ACC3 := mk_handler_verified verify_ACC3.
  Definition verified_ACC4 := mk_handler_verified verify_ACC4.
  Definition verified_ACC5 := mk_handler_verified verify_ACC5.
  Definition verified_ACC6 := mk_handler_verified verify_ACC6.
  Definition verified_ACC7 := mk_handler_verified verify_ACC7.
  Definition verified_ACC n := mk_handler_verified (verify_ACC_correct n).
  Definition verified_ADDINT := mk_handler_verified verify_ADDINT_compl_comp.
  Definition verified_ANDINT := mk_handler_verified verify_ANDINT_correct.
  Definition verified_APPLY1 := mk_handler_verified verify_APPLY1_correct.
  Definition verified_APPLY2 := mk_handler_verified verify_APPLY2_correct.
  Definition verified_APPLY3 := mk_handler_verified verify_APPLY3_correct.
  Definition verified_APPLY n := mk_handler_verified (verify_APPLY_correct n).
  Definition verified_APPTERM1 slotsize := mk_handler_verified (verify_APPTERM1_correct slotsize).
  Definition verified_APPTERM2 slotsize := mk_handler_verified (verify_APPTERM2_correct slotsize).
  Definition verified_APPTERM3 slotsize := mk_handler_verified (verify_APPTERM3_correct slotsize).
  Definition verified_APPTERM nargs slotsize := mk_handler_verified (verify_APPTERM_correct nargs slotsize).
  Definition verified_ASRINT := mk_handler_verified verify_ASRINT_correct.
  Definition verified_ASSIGN n := mk_handler_verified (verify_ASSIGN_correct n).
  Definition verified_ATOM0 := mk_handler_verified verify_ATOM0_correct.
  Definition verified_ATOM t H0 := mk_handler_verified (verify_ATOM_correct t H0).
  Definition verified_BEQ n target := mk_handler_verified (verify_BEQ_correct n target).
  Definition verified_BGEINT n target := mk_handler_verified (verify_BGEINT_correct n target).
  Definition verified_BGTINT n target := mk_handler_verified (verify_BGTINT_correct n target).
  Definition verified_BLEINT n target := mk_handler_verified (verify_BLEINT_correct n target).
  Definition verified_BLTINT n target := mk_handler_verified (verify_BLTINT_correct n target).
  Definition verified_BNEQ n target := mk_handler_verified (verify_BNEQ_correct n target).
  Definition verified_BOOLNOT := mk_handler_verified verify_BOOLNOT_handler_correct.
  Definition verified_BRANCHIFNOT target := mk_handler_with_pre_verified (verify_BRANCHIFNOT_correct target).
  Definition verified_BRANCHIF target := mk_handler_with_pre_verified (verify_BRANCHIF_correct target).
  Definition verified_BRANCH target := mk_handler_verified (verify_BRANCH_correct target).
  Definition verified_BREAK := mk_handler_verified verify_BREAK_correct.
  Definition verified_BUGEINT n target := mk_handler_verified (verify_BUGEINT_correct n target).
  Definition verified_BULTINT n target := mk_handler_verified (verify_BULTINT_correct n target).
  Definition verified_CHECK_SIGNALS := mk_handler_verified verify_CHECK_SIGNALS_correct.
  Definition verified_CLOSUREREC code_ofs := mk_handler_verified (verify_CLOSUREREC_correct code_ofs).
  Definition verified_CLOSURE code_ofs := mk_handler_verified (verify_CLOSURE_correct code_ofs).
  Definition verified_CONST0 := mk_handler_verified verify_CONST0_compl_comp.
  Definition verified_CONST1 := mk_handler_verified verify_CONST1_correct.
  Definition verified_CONST2 := mk_handler_verified verify_CONST2_correct.
  Definition verified_CONST3 := mk_handler_verified verify_CONST3_correct.
  Definition verified_CONSTINT n := mk_handler_verified (verify_CONSTINT_correct n).
  Definition verified_C_CALL1 prim_idx := mk_handler_verified (verify_C_CALL1_correct prim_idx).
  Definition verified_C_CALL2 prim_idx := mk_handler_verified (verify_C_CALL2_correct prim_idx).
  Definition verified_C_CALL3 prim_idx := mk_handler_verified (verify_C_CALL3_correct prim_idx).
  Definition verified_C_CALL4 prim_idx := mk_handler_verified (verify_C_CALL4_correct prim_idx).
  Definition verified_C_CALL5 prim_idx := mk_handler_verified (verify_C_CALL5_correct prim_idx).
  Definition verified_C_CALLN nargs prim_idx := mk_handler_verified (verify_C_CALLN_correct nargs prim_idx).
  Definition verified_DIVINT := mk_handler_with_pre_verified verify_DIVINT_correct.
  Definition verified_ENVACC1 := mk_handler_verified verify_ENVACC1_with_pre.
  Definition verified_ENVACC2 := mk_handler_verified verify_ENVACC2_with_pre.
  Definition verified_ENVACC3 := mk_handler_verified verify_ENVACC3_with_pre.
  Definition verified_ENVACC4 := mk_handler_verified verify_ENVACC4_with_pre.
  Definition verified_ENVACC n := mk_handler_verified (verify_ENVACC_correct n).
  Definition verified_EQ := mk_handler_verified verify_EQ_correct.
  Definition verified_EVENT := mk_handler_verified verify_EVENT_correct.
  Definition verified_GEINT := mk_handler_verified verify_GEINT_correct.
  Definition verified_GETBYTESCHAR := mk_handler_verified verify_GETBYTESCHAR_correct.
  Definition verified_GETDYNMET := mk_handler_verified verify_GETDYNMET_correct.
  Definition verified_GETFIELD0 := mk_handler_verified verify_GETFIELD0_with_pre.
  Definition verified_GETFIELD1 := mk_handler_verified verify_GETFIELD1_with_pre.
  Definition verified_GETFIELD2 := mk_handler_verified verify_GETFIELD2_with_pre.
  Definition verified_GETFIELD3 := mk_handler_verified verify_GETFIELD3_with_pre.
  Definition verified_GETFIELD n := mk_handler_verified (verify_GETFIELD_correct n).
  Definition verified_GETFLOATFIELD n := mk_handler_verified (verify_GETFLOATFIELD_correct n).
  Definition verified_GETGLOBALFIELD n p := mk_handler_verified (verify_GETGLOBALFIELD_correct n p).
  Definition verified_GETGLOBAL n := mk_handler_verified (verify_GETGLOBAL_correct n).
  Definition verified_GETMETHOD := mk_handler_verified verify_GETMETHOD_correct.
  Definition verified_GETPUBMET tag := mk_handler_verified (verify_GETPUBMET_correct tag).
  Definition verified_GETSTRINGCHAR := mk_handler_verified verify_GETSTRINGCHAR_correct.
  Definition verified_GETVECTITEM := mk_handler_verified verify_GETVECTITEM_correct.
  Definition verified_GRAB required := mk_handler_verified (verify_GRAB_correct required).
  Definition verified_GTINT := mk_handler_verified verify_GTINT_correct.
  Definition verified_ISINT := mk_handler_verified verify_ISINT_handler_correct.
  Definition verified_LEINT := mk_handler_verified verify_LEINT_correct.
  Definition verified_LSLINT := mk_handler_verified verify_LSLINT_correct.
  Definition verified_LSRINT := mk_handler_verified verify_LSRINT_correct.
  Definition verified_LTINT := mk_handler_verified verify_LTINT_correct.
  Definition verified_MAKEBLOCK1 t := mk_handler_verified (verify_MAKEBLOCK1_correct t).
  Definition verified_MAKEBLOCK2 t := mk_handler_verified (verify_MAKEBLOCK2_correct t).
  Definition verified_MAKEBLOCK3 t := mk_handler_verified (verify_MAKEBLOCK3_correct t).
  Definition verified_MAKEBLOCK (t size : nat) H0 := mk_handler_verified (verify_MAKEBLOCK_correct t size H0).
  Definition verified_MAKEFLOATBLOCK (n : nat) H0 := mk_handler_verified (verify_MAKEFLOATBLOCK_correct n H0).
  Definition verified_MODINT := mk_handler_with_pre_verified verify_MODINT_correct.
  Definition verified_MULINT := mk_handler_verified verify_MULINT_correct.
  Definition verified_NEGINT := mk_handler_verified verify_NEGINT_compl_comp.
  Definition verified_NEQ := mk_handler_verified verify_NEQ_correct.
  Definition verified_OFFSETCLOSURE0 := mk_handler_verified verify_OFFSETCLOSURE0_compl_comp.
  Definition verified_OFFSETCLOSURE2 := mk_handler_verified verify_OFFSETCLOSURE2_compl_comp.
  Definition verified_OFFSETCLOSUREM2 := mk_handler_verified verify_OFFSETCLOSUREM2_compl_comp.
  Definition verified_OFFSETCLOSURE n := mk_handler_verified (verify_OFFSETCLOSURE_correct n).
  Definition verified_OFFSETINT ofs := mk_handler_verified (verify_OFFSETINT_correct ofs).
  Definition verified_OFFSETREF n := mk_handler_verified (verify_OFFSETREF_correct n).
  Definition verified_ORINT := mk_handler_verified verify_ORINT_correct.
  Definition verified_PERFORM := mk_handler_verified verify_PERFORM_correct.
  Definition verified_POPTRAP := mk_handler_verified verify_POPTRAP_correct.
  Definition verified_POP n := mk_handler_verified (verify_POP_correct n).
  Definition verified_PUSHACC1 := mk_handler_verified verify_PUSHACC1_correct.
  Definition verified_PUSHACC2 := mk_handler_verified verify_PUSHACC2_correct.
  Definition verified_PUSHACC3 := mk_handler_verified verify_PUSHACC3_correct.
  Definition verified_PUSHACC4 := mk_handler_verified verify_PUSHACC4_correct.
  Definition verified_PUSHACC5 := mk_handler_verified verify_PUSHACC5_correct.
  Definition verified_PUSHACC6 := mk_handler_verified verify_PUSHACC6_correct.
  Definition verified_PUSHACC7 := mk_handler_verified verify_PUSHACC7_correct.
  Definition verified_PUSHATOM0 := mk_handler_verified verify_PUSHATOM0_correct.
  Definition verified_PUSHATOM t H0 := mk_handler_verified (verify_PUSHATOM_correct t H0).
  Definition verified_PUSHCONST0 := mk_handler_verified verify_PUSHCONST0_correct.
  Definition verified_PUSHCONST1 := mk_handler_verified verify_PUSHCONST1_correct.
  Definition verified_PUSHCONST2 := mk_handler_verified verify_PUSHCONST2_correct.
  Definition verified_PUSHCONST3 := mk_handler_verified verify_PUSHCONST3_correct.
  Definition verified_PUSHCONSTINT n := mk_handler_verified (verify_PUSHCONSTINT_correct n).
  Definition verified_PUSHENVACC1 := mk_handler_verified verify_PUSHENVACC1_correct.
  Definition verified_PUSHENVACC2 := mk_handler_verified verify_PUSHENVACC2_correct.
  Definition verified_PUSHENVACC3 := mk_handler_verified verify_PUSHENVACC3_correct.
  Definition verified_PUSHENVACC4 := mk_handler_verified verify_PUSHENVACC4_correct.
  Definition verified_PUSHENVACC n := mk_handler_verified (verify_PUSHENVACC_correct n).
  Definition verified_PUSHGETGLOBALFIELD n p := mk_handler_verified (verify_PUSHGETGLOBALFIELD_correct n p).
  Definition verified_PUSHGETGLOBAL n := mk_handler_verified (verify_PUSHGETGLOBAL_correct n).
  Definition verified_PUSHOFFSETCLOSURE0 := mk_handler_verified verify_PUSHOFFSETCLOSURE0_correct.
  Definition verified_PUSHOFFSETCLOSURE2 := mk_handler_verified verify_PUSHOFFSETCLOSURE2_correct.
  Definition verified_PUSHOFFSETCLOSUREM2 := mk_handler_verified verify_PUSHOFFSETCLOSUREM2_correct.
  Definition verified_PUSHOFFSETCLOSURE ofs := mk_handler_verified (verify_PUSHOFFSETCLOSURE_correct ofs).
  Definition verified_PUSHTRAP handler_pc := mk_handler_verified (verify_PUSHTRAP_correct handler_pc).
  Definition verified_PUSH_RETADDR ret_addr := mk_handler_verified (verify_PUSH_RETADDR_correct ret_addr).
  Definition verified_PUSH := mk_handler_verified verify_PUSH_correct.
  Definition verified_RAISE_NOTRACE := mk_handler_verified verify_RAISE_NOTRACE_correct.
  Definition verified_RAISE := mk_handler_verified verify_RAISE_correct.
  Definition verified_REPERFORMTERM := mk_handler_verified verify_REPERFORMTERM_correct.
  Definition verified_RERAISE := mk_handler_verified verify_RERAISE_correct.
  Definition verified_RESTART := mk_handler_verified verify_RESTART_correct.
  Definition verified_RESUMETERM := mk_handler_verified verify_RESUMETERM_correct.
  Definition verified_RESUME := mk_handler_verified verify_RESUME_correct.
  Definition verified_RETURN stacksize := mk_handler_verified (verify_RETURN_correct stacksize).
  Definition verified_SETBYTESCHAR := mk_handler_verified verify_SETBYTESCHAR_correct.
  Definition verified_SETFIELD0 := mk_handler_verified verify_SETFIELD0_correct.
  Definition verified_SETFIELD1 := mk_handler_verified verify_SETFIELD1_correct.
  Definition verified_SETFIELD2 := mk_handler_verified verify_SETFIELD2_correct.
  Definition verified_SETFIELD3 := mk_handler_verified verify_SETFIELD3_correct.
  Definition verified_SETFIELD n := mk_handler_verified (verify_SETFIELD_correct n).
  Definition verified_SETFLOATFIELD n := mk_handler_verified (verify_SETFLOATFIELD_correct n).
  Definition verified_SETGLOBAL n := mk_handler_verified (verify_SETGLOBAL_correct n).
  Definition verified_SETVECTITEM := mk_handler_verified verify_SETVECTITEM_correct.
  Definition verified_STOP := mk_handler_verified verify_STOP_correct.
  Definition verified_SUBINT := mk_handler_verified verify_SUBINT_correct.
  Definition verified_SWITCH (_nc _nb : nat) (const_targets block_targets : list Z) := mk_handler_verified (verify_SWITCH_handler_correct _nc _nb const_targets block_targets).
  Definition verified_UGEINT := mk_handler_verified verify_UGEINT_correct.
  Definition verified_ULTINT := mk_handler_verified verify_ULTINT_correct.
  Definition verified_VECTLENGTH := mk_handler_verified verify_VECTLENGTH_correct.
  Definition verified_XORINT := mk_handler_verified verify_XORINT_correct.

End InstructVerification.
