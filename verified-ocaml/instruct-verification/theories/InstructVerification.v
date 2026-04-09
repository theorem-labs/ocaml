(* InstructVerification.v — Instantiation of InstructVerificationSpec. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat.
Import ListNotations.
From compcert Require Import Integers Ctypes Cop Clight Globalenvs Memory Values.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
Require Import instruct_handlers.
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


Module InstructVerification <: InstructVerificationSpec.

  Definition correct_ACC0 := verify_ACC0_compl_comp.
  Definition correct_ACC1 := verify_ACC1.
  Definition correct_ACC2 := verify_ACC2.
  Definition correct_ACC3 := verify_ACC3.
  Definition correct_ACC4 := verify_ACC4.
  Definition correct_ACC5 := verify_ACC5.
  Definition correct_ACC6 := verify_ACC6.
  Definition correct_ACC7 := verify_ACC7.
  Definition correct_ACC :
    forall n,
    Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_ACC n) f_instr_ACC
      (code_at (Int.repr (Z.of_nat n)))
      (fun _ s => nth_error s.(Machine.stack) n = None) (fun _ => False) (fun _ _ _ => False)
    := verify_ACC_handler_correct.
  Definition correct_ADDINT := verify_ADDINT_compl_comp.
  Definition correct_ANDINT := verify_ANDINT_correct.
  Definition correct_APPLY1 := verify_APPLY1_correct.
  Definition correct_APPLY2 := verify_APPLY2_correct.
  Definition correct_APPLY3 := verify_APPLY3_correct.
  Definition correct_APPLY := verify_APPLY_correct.
  Definition correct_APPTERM1 := verify_APPTERM1_correct.
  Definition correct_APPTERM2 := verify_APPTERM2_correct.
  Definition correct_APPTERM3 := verify_APPTERM3_correct.
  Definition correct_APPTERM := verify_APPTERM_correct.
  Definition correct_ASRINT := verify_ASRINT_handler_correct.
  Definition correct_ASSIGN := verify_ASSIGN_correct.
  Definition correct_ATOM0 := verify_ATOM0_correct.
  Definition correct_ATOM := verify_ATOM_correct.
  Definition correct_BEQ :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BEQ n target) f_instr_BEQ
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) (pre_and accu_signed_int accu_is_long))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False)
    := verify_BEQ_handler_correct.
  Definition correct_BGEINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BGEINT n target) f_instr_BGEINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) (pre_and accu_signed_int accu_is_long))
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False)
    := verify_BGEINT_handler_correct.
  Definition correct_BGTINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BGTINT n target) f_instr_BGTINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) (pre_and accu_signed_int accu_is_long))
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False)
    := verify_BGTINT_handler_correct.
  Definition correct_BLEINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BLEINT n target) f_instr_BLEINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) (pre_and accu_signed_int accu_is_long))
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False)
    := verify_BLEINT_handler_correct.
  Definition correct_BLTINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BLTINT n target) f_instr_BLTINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) (pre_and accu_signed_int accu_is_long))
      (fun msg s => msg = "BLTINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False)
    := verify_BLTINT_handler_correct.
  Definition correct_BNEQ :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BNEQ n target) f_instr_BNEQ
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) (pre_and accu_signed_int accu_is_long))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False)
    := verify_BNEQ_handler_correct.
  Definition correct_BOOLNOT := verify_BOOLNOT_handler_correct.
  Definition correct_BRANCHIFNOT := verify_BRANCHIFNOT_correct.
  Definition correct_BRANCHIF := verify_BRANCHIF_correct.
  Definition correct_BRANCH :
    forall target,
    handler_correct (fun _ s => handle_BRANCH target s) f_instr_BRANCH
      code_loadable
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False)
    := verify_BRANCH_handler_correct.
  Definition correct_BREAK := verify_BREAK_correct.
  Definition correct_BUGEINT :
    forall n target,
    0 <= n -> Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BUGEINT n target) f_instr_BUGEINT
      (pre_and (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_unsigned_int) accu_is_long)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False)
    := verify_BUGEINT_handler_correct.
  Definition correct_BULTINT :
    forall n target,
    0 <= n -> Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BULTINT n target) f_instr_BULTINT
      (pre_and (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_unsigned_int) accu_is_long)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False)
    := verify_BULTINT_handler_correct.
  Definition correct_CHECK_SIGNALS := verify_CHECK_SIGNALS_correct.
  Definition correct_CLOSUREREC := verify_CLOSUREREC_correct.
  Definition correct_CLOSURE := verify_CLOSURE_correct.
  Definition correct_CONST0 := verify_CONST0_compl_comp.
  Definition correct_CONST1 := verify_CONST1_correct.
  Definition correct_CONST2 := verify_CONST2_correct.
  Definition correct_CONST3 := verify_CONST3_correct.
  Definition correct_CONSTINT := verify_CONSTINT_handler_correct.
  Definition correct_C_CALL1 prim_idx := verify_C_CALL1_correct prim_idx.
  Definition correct_C_CALL2 prim_idx := verify_C_CALL2_correct prim_idx.
  Definition correct_C_CALL3 prim_idx := verify_C_CALL3_correct prim_idx.
  Definition correct_C_CALL4 prim_idx := verify_C_CALL4_correct prim_idx.
  Definition correct_C_CALL5 prim_idx := verify_C_CALL5_correct prim_idx.
  Definition correct_C_CALLN nargs prim_idx := verify_C_CALLN_correct nargs prim_idx.
  Definition correct_DIVINT := verify_DIVINT_handler_correct.
  Definition correct_ENVACC1 := verify_ENVACC1_with_pre.
  Definition correct_ENVACC2 := verify_ENVACC2_with_pre.
  Definition correct_ENVACC3 := verify_ENVACC3_with_pre.
  Definition correct_ENVACC4 := verify_ENVACC4_with_pre.
  Definition correct_ENVACC := verify_ENVACC_correct.
  Definition correct_EQ := verify_EQ_handler_correct.
  Definition correct_EVENT := verify_EVENT_correct.
  Definition correct_GEINT := verify_GEINT_handler_correct.
  Definition correct_GETBYTESCHAR := verify_GETBYTESCHAR_correct.
  Definition correct_GETDYNMET := verify_GETDYNMET_correct.
  Definition correct_GETFIELD0 := verify_GETFIELD0_with_pre.
  Definition correct_GETFIELD1 := verify_GETFIELD1_with_pre.
  Definition correct_GETFIELD2 := verify_GETFIELD2_with_pre.
  Definition correct_GETFIELD3 := verify_GETFIELD3_with_pre.
  Definition correct_GETFIELD := verify_GETFIELD_correct.
  Definition correct_GETFLOATFIELD := verify_GETFLOATFIELD_correct.
  Definition correct_GETGLOBALFIELD := verify_GETGLOBALFIELD_correct.
  Definition correct_GETGLOBAL :
    forall n,
    0 <= Z.of_nat n <= Int.max_signed ->
    handler_correct (handle_GETGLOBAL n) f_instr_GETGLOBAL
      (pre_and (code_at (Int.repr (Z.of_nat n))) (global_offset_safe n))
      (fun _ s => nth_error s.(Machine.global) n = None) (fun _ => False) (fun _ _ _ => False)
    := verify_GETGLOBAL_handler_correct.
  Definition correct_GETMETHOD := verify_GETMETHOD_correct.
  Definition correct_GETPUBMET := verify_GETPUBMET_correct.
  Definition correct_GETSTRINGCHAR := verify_GETSTRINGCHAR_correct.
  Definition correct_GETVECTITEM := verify_GETVECTITEM_correct.
  Definition correct_GRAB := verify_GRAB_correct.
  Definition correct_GTINT := verify_GTINT_handler_correct.
  Definition correct_ISINT := verify_ISINT_handler_correct.
  Definition correct_LEINT := verify_LEINT_handler_correct.
  Definition correct_LSLINT := verify_LSLINT_handler_correct.
  Definition correct_LSRINT := verify_LSRINT_handler_correct.
  Definition correct_LTINT := verify_LTINT_handler_correct.
  Definition correct_MAKEBLOCK1 := verify_MAKEBLOCK1_correct.
  Definition correct_MAKEBLOCK2 := verify_MAKEBLOCK2_correct.
  Definition correct_MAKEBLOCK3 := verify_MAKEBLOCK3_correct.
  Definition correct_MAKEBLOCK := verify_MAKEBLOCK_correct.
  Definition correct_MAKEFLOATBLOCK := verify_MAKEFLOATBLOCK_correct.
  Definition correct_MODINT := verify_MODINT_handler_correct.
  Definition correct_MULINT := verify_MULINT_correct.
  Definition correct_NEGINT := verify_NEGINT_compl_comp.
  Definition correct_NEQ := verify_NEQ_handler_correct.
  Definition correct_OFFSETCLOSURE0 := verify_OFFSETCLOSURE0_compl_comp.
  Definition correct_OFFSETCLOSURE2 := verify_OFFSETCLOSURE2_compl_comp.
  Definition correct_OFFSETCLOSUREM2 := verify_OFFSETCLOSUREM2_compl_comp.
  Definition correct_OFFSETCLOSURE := verify_OFFSETCLOSURE_correct.
  Definition correct_OFFSETINT := verify_OFFSETINT_handler_correct.
  Definition correct_OFFSETREF := verify_OFFSETREF_correct.
  Definition correct_ORINT := verify_ORINT_correct.
  Definition correct_PERFORM := verify_PERFORM_correct.
  Definition correct_POPTRAP := verify_POPTRAP_correct.
  Definition correct_POP :
    forall n,
    Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_POP n) f_instr_POP
      (pre_and (pre_and (code_at (Int.repr (Z.of_nat n))) code_ne_struct) (stack_length_ge n))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False)
    := verify_POP_handler_correct.
  Definition correct_PUSHACC1 := verify_PUSHACC1_correct.
  Definition correct_PUSHACC2 := verify_PUSHACC2_correct.
  Definition correct_PUSHACC3 := verify_PUSHACC3_correct.
  Definition correct_PUSHACC4 := verify_PUSHACC4_correct.
  Definition correct_PUSHACC5 := verify_PUSHACC5_correct.
  Definition correct_PUSHACC6 := verify_PUSHACC6_correct.
  Definition correct_PUSHACC7 := verify_PUSHACC7_correct.
  Definition correct_PUSHATOM0 := verify_PUSHATOM0_correct.
  Definition correct_PUSHATOM :
    forall t, Z.of_nat t <= 2097151 ->
    handler_correct (handle_PUSHATOM t) f_instr_PUSHATOM
      (pre_and (sp_at_least 16) (code_at (Int.repr (Z.of_nat t))))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False)
    := verify_PUSHATOM_handler_correct.
  Definition correct_PUSHCONST0 := verify_PUSHCONST0_correct.
  Definition correct_PUSHCONST1 := verify_PUSHCONST1_correct.
  Definition correct_PUSHCONST2 := verify_PUSHCONST2_correct.
  Definition correct_PUSHCONST3 := verify_PUSHCONST3_correct.
  Definition correct_PUSHCONSTINT := verify_PUSHCONSTINT_correct.
  Definition correct_PUSHENVACC1 := verify_PUSHENVACC1_correct.
  Definition correct_PUSHENVACC2 := verify_PUSHENVACC2_correct.
  Definition correct_PUSHENVACC3 := verify_PUSHENVACC3_correct.
  Definition correct_PUSHENVACC4 := verify_PUSHENVACC4_correct.
  Definition correct_PUSHENVACC := verify_PUSHENVACC_correct.
  Definition correct_PUSHGETGLOBALFIELD := verify_PUSHGETGLOBALFIELD_correct.
  Definition correct_PUSHGETGLOBAL :
    forall n,
    0 <= Z.of_nat n <= Int.max_signed ->
    handler_correct (handle_PUSHGETGLOBAL n) f_instr_PUSHGETGLOBAL
      (pre_and (pre_and (code_at (Int.repr (Z.of_nat n))) (global_offset_safe n)) (sp_at_least 16))
      (fun _ s => nth_error s.(Machine.global) n = None) (fun _ => False) (fun _ _ _ => False)
    := verify_PUSHGETGLOBAL_handler_correct.
  Definition correct_PUSHOFFSETCLOSURE0 := verify_PUSHOFFSETCLOSURE0_correct.
  Definition correct_PUSHOFFSETCLOSURE2 := verify_PUSHOFFSETCLOSURE2_correct.
  Definition correct_PUSHOFFSETCLOSUREM2 := verify_PUSHOFFSETCLOSUREM2_correct.
  Definition correct_PUSHOFFSETCLOSURE := verify_PUSHOFFSETCLOSURE_correct.
  Definition correct_PUSHTRAP := verify_PUSHTRAP_correct.
  Definition correct_PUSH_RETADDR := verify_PUSH_RETADDR_correct.
  Definition correct_PUSH := verify_PUSH_correct.
  Definition correct_RAISE_NOTRACE := verify_RAISE_NOTRACE_correct.
  Definition correct_RAISE := verify_RAISE_correct.
  Definition correct_REPERFORMTERM := verify_REPERFORMTERM_correct.
  Definition correct_RERAISE := verify_RERAISE_correct.
  Definition correct_RESTART := verify_RESTART_correct.
  Definition correct_RESUMETERM := verify_RESUMETERM_correct.
  Definition correct_RESUME := verify_RESUME_correct.
  Definition correct_RETURN := verify_RETURN_correct.
  Definition correct_SETBYTESCHAR := verify_SETBYTESCHAR_correct.
  Definition correct_SETFIELD0 := verify_SETFIELD0_correct.
  Definition correct_SETFIELD1 := verify_SETFIELD1_correct.
  Definition correct_SETFIELD2 := verify_SETFIELD2_correct.
  Definition correct_SETFIELD3 := verify_SETFIELD3_correct.
  Definition correct_SETFIELD := verify_SETFIELD_correct.
  Definition correct_SETFLOATFIELD := verify_SETFLOATFIELD_correct.
  Definition correct_SETGLOBAL := verify_SETGLOBAL_correct.
  Definition correct_SETVECTITEM := verify_SETVECTITEM_correct.
  Definition correct_STOP := verify_STOP_correct.
  Definition correct_SUBINT := verify_SUBINT_correct.
  Definition correct_SWITCH := verify_SWITCH_handler_correct.
  Definition correct_UGEINT := verify_UGEINT_handler_correct.
  Definition correct_ULTINT := verify_ULTINT_handler_correct.
  Definition correct_VECTLENGTH := verify_VECTLENGTH_correct.
  Definition correct_XORINT := verify_XORINT_correct.
End InstructVerification.
