(* InstructVerification.v — Instantiation of InstructVerificationSpec. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import AST Integers Ctypes Cop Clight ClightBigstep Events Globalenvs Memory Values.
From RecordUpdate Require Import RecordUpdate.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.InstructSpec.

From OCamlInterp.Automatic Require Bytecode.InstructVerification.ACC0_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ACC1_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ACC2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ACC3_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ACC4_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ACC5_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ACC6_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ACC7_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ACC_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ADDINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ANDINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.APPLY1_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.APPLY2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.APPLY3_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.APPLY_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.APPTERM1_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.APPTERM2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.APPTERM3_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.APPTERM_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ASRINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ASSIGN_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ATOM0_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ATOM_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.BEQ_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.BGEINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.BGTINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.BLEINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.BLTINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.BNEQ_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.BOOLNOT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.BRANCHIFNOT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.BRANCHIF_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.BRANCH_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.BREAK_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.BUGEINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.BULTINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.CHECK_SIGNALS_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.CLOSUREREC_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.CLOSURE_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.CONST0_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.CONST1_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.CONST2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.CONST3_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.CONSTINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.C_CALL1_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.C_CALL2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.C_CALL3_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.C_CALL4_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.C_CALL5_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.C_CALLN_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.DIVINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ENVACC1_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ENVACC2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ENVACC3_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ENVACC4_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ENVACC_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.EQ_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.EVENT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GEINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GETBYTESCHAR_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GETDYNMET_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GETFIELD0_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GETFIELD1_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GETFIELD2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GETFIELD3_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GETFIELD_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GETFLOATFIELD_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GETGLOBALFIELD_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GETGLOBAL_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GETMETHOD_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GETPUBMET_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GETSTRINGCHAR_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GETVECTITEM_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GRAB_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.GTINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ISINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.LEINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.LSLINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.LSRINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.LTINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.MAKEBLOCK1_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.MAKEBLOCK2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.MAKEBLOCK3_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.MAKEBLOCK_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.MAKEFLOATBLOCK_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.MODINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.MULINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.NEGINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.NEQ_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.OFFSETCLOSURE0_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.OFFSETCLOSURE2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.OFFSETCLOSUREM2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.OFFSETCLOSURE_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.OFFSETINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.OFFSETREF_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ORINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PERFORM_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.POPTRAP_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.POP_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHACC1_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHACC2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHACC3_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHACC4_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHACC5_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHACC6_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHACC7_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHATOM0_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHATOM_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHCONST0_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHCONST1_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHCONST2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHCONST3_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHCONSTINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHENVACC1_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHENVACC2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHENVACC3_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHENVACC4_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHENVACC_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHGETGLOBALFIELD_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHGETGLOBAL_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHOFFSETCLOSURE0_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHOFFSETCLOSURE2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHOFFSETCLOSUREM2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHOFFSETCLOSURE_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSHTRAP_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSH_RETADDR_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.PUSH_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.RAISE_NOTRACE_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.RAISE_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.REPERFORMTERM_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.RERAISE_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.RESTART_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.RESUMETERM_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.RESUME_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.RETURN_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.SETBYTESCHAR_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.SETFIELD0_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.SETFIELD1_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.SETFIELD2_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.SETFIELD3_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.SETFIELD_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.SETFLOATFIELD_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.SETGLOBAL_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.SETVECTITEM_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.STOP_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.SUBINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.SWITCH_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.UGEINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.ULTINT_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.VECTLENGTH_correct.
From OCamlInterp.Automatic Require Bytecode.InstructVerification.XORINT_correct.


Module InstructVerification <: InstructVerificationSpec.

  Definition correct_ACC0 := ACC0_correct.verify_ACC0_compl_comp.
  Definition correct_ACC1 := ACC1_correct.verify_ACC1.
  Definition correct_ACC2 := ACC2_correct.verify_ACC2.
  Definition correct_ACC3 := ACC3_correct.verify_ACC3.
  Definition correct_ACC4 := ACC4_correct.verify_ACC4.
  Definition correct_ACC5 := ACC5_correct.verify_ACC5.
  Definition correct_ACC6 := ACC6_correct.verify_ACC6.
  Definition correct_ACC7 := ACC7_correct.verify_ACC7.
  Definition correct_ACC :
    forall n,
    Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_ACC n) f_instr_ACC
      (code_at (Int.repr (Z.of_nat n)))
      (fun _ s => nth_error s.(Machine.stack) n = None) (fun _ => False) (fun _ _ _ => False)
    := ACC_correct.verify_ACC_handler_correct.
  Definition correct_ADDINT := ADDINT_correct.verify_ADDINT_compl_comp.
  Definition correct_ANDINT := ANDINT_correct.verify_ANDINT_correct.
  Definition correct_APPLY1 := APPLY1_correct.verify_APPLY1_correct.
  Definition correct_APPLY2 := APPLY2_correct.verify_APPLY2_correct.
  Definition correct_APPLY3 := APPLY3_correct.verify_APPLY3_correct.
  Definition correct_APPLY := APPLY_correct.verify_APPLY_correct.
  Definition correct_APPTERM1 := APPTERM1_correct.verify_APPTERM1_correct.
  Definition correct_APPTERM2 := APPTERM2_correct.verify_APPTERM2_correct.
  Definition correct_APPTERM3 := APPTERM3_correct.verify_APPTERM3_correct.
  Definition correct_APPTERM := APPTERM_correct.verify_APPTERM_correct.
  Definition correct_ASRINT := ASRINT_correct.verify_ASRINT_handler_correct.
  Definition correct_ASSIGN := ASSIGN_correct.verify_ASSIGN_correct.
  Definition correct_ATOM0 := ATOM0_correct.verify_ATOM0_correct.
  Definition correct_ATOM := ATOM_correct.verify_ATOM_correct.
  Definition correct_BEQ :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BEQ n target) f_instr_BEQ
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) (pre_and accu_signed_int accu_is_long))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False)
    := BEQ_correct.verify_BEQ_handler_correct.
  Definition correct_BGEINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BGEINT n target) f_instr_BGEINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) (pre_and accu_signed_int accu_is_long))
      (fun msg s => msg = "BGEINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False)
    := BGEINT_correct.verify_BGEINT_handler_correct.
  Definition correct_BGTINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BGTINT n target) f_instr_BGTINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) (pre_and accu_signed_int accu_is_long))
      (fun msg s => msg = "BGTINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False)
    := BGTINT_correct.verify_BGTINT_handler_correct.
  Definition correct_BLEINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BLEINT n target) f_instr_BLEINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) (pre_and accu_signed_int accu_is_long))
      (fun msg s => msg = "BLEINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False)
    := BLEINT_correct.verify_BLEINT_handler_correct.
  Definition correct_BLTINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BLTINT n target) f_instr_BLTINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) (pre_and accu_signed_int accu_is_long))
      (fun msg s => msg = "BLTINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False)
    := BLTINT_correct.verify_BLTINT_handler_correct.
  Definition correct_BNEQ :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BNEQ n target) f_instr_BNEQ
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) (pre_and accu_signed_int accu_is_long))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False)
    := BNEQ_correct.verify_BNEQ_handler_correct.
  Definition correct_BOOLNOT := BOOLNOT_correct.verify_BOOLNOT_handler_correct.
  Definition correct_BRANCHIFNOT := BRANCHIFNOT_correct.verify_BRANCHIFNOT_correct.
  Definition correct_BRANCHIF := BRANCHIF_correct.verify_BRANCHIF_correct.
  Definition correct_BRANCH :
    forall target,
    handler_correct (fun _ s => handle_BRANCH target s) f_instr_BRANCH
      code_loadable
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False)
    := BRANCH_correct.verify_BRANCH_handler_correct.
  Definition correct_BREAK := BREAK_correct.verify_BREAK_correct.
  Definition correct_BUGEINT :
    forall n target,
    0 <= n -> Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BUGEINT n target) f_instr_BUGEINT
      (pre_and (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_unsigned_int) accu_is_long)
      (fun msg s => msg = "BUGEINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False)
    := BUGEINT_correct.verify_BUGEINT_handler_correct.
  Definition correct_BULTINT :
    forall n target,
    0 <= n -> Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BULTINT n target) f_instr_BULTINT
      (pre_and (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_unsigned_int) accu_is_long)
      (fun msg s => msg = "BULTINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False)
    := BULTINT_correct.verify_BULTINT_handler_correct.
  Definition correct_CHECK_SIGNALS := CHECK_SIGNALS_correct.verify_CHECK_SIGNALS_correct.
  Definition correct_CLOSUREREC := CLOSUREREC_correct.CLOSUREREC_correct_for_spec.
  Definition correct_CLOSURE := CLOSURE_correct.CLOSURE_correct_for_spec.
  Definition correct_CONST0 := CONST0_correct.verify_CONST0_compl_comp.
  Definition correct_CONST1 := CONST1_correct.verify_CONST1_correct.
  Definition correct_CONST2 := CONST2_correct.verify_CONST2_correct.
  Definition correct_CONST3 := CONST3_correct.verify_CONST3_correct.
  Definition correct_CONSTINT := CONSTINT_correct.verify_CONSTINT_handler_correct.
  Definition correct_C_CALL1 prim_idx := C_CALL1_correct.verify_C_CALL1_correct prim_idx.
  Definition correct_C_CALL2 prim_idx := C_CALL2_correct.verify_C_CALL2_correct prim_idx.
  Definition correct_C_CALL3 prim_idx := C_CALL3_correct.verify_C_CALL3_correct prim_idx.
  Definition correct_C_CALL4 prim_idx := C_CALL4_correct.verify_C_CALL4_correct prim_idx.
  Definition correct_C_CALL5 prim_idx := C_CALL5_correct.verify_C_CALL5_correct prim_idx.
  Definition correct_C_CALLN nargs prim_idx := C_CALLN_correct.verify_C_CALLN_correct nargs prim_idx.
  Definition correct_DIVINT := DIVINT_correct.verify_DIVINT_handler_correct.
  Definition correct_ENVACC1 := ENVACC1_correct.verify_ENVACC1_with_pre.
  Definition correct_ENVACC2 := ENVACC2_correct.verify_ENVACC2_with_pre.
  Definition correct_ENVACC3 := ENVACC3_correct.verify_ENVACC3_with_pre.
  Definition correct_ENVACC4 := ENVACC4_correct.verify_ENVACC4_with_pre.
  Definition correct_ENVACC := ENVACC_correct.ENVACC_correct_for_spec.
  Definition correct_EQ := EQ_correct.verify_EQ_handler_correct.
  Definition correct_EVENT := EVENT_correct.verify_EVENT_correct.
  Definition correct_GEINT := GEINT_correct.verify_GEINT_handler_correct.
  Definition correct_GETBYTESCHAR := GETBYTESCHAR_correct.verify_GETBYTESCHAR_correct.
  Definition correct_GETDYNMET := GETDYNMET_correct.verify_GETDYNMET_correct.
  Definition correct_GETFIELD0 := GETFIELD0_correct.verify_GETFIELD0_with_pre.
  Definition correct_GETFIELD1 := GETFIELD1_correct.verify_GETFIELD1_with_pre.
  Definition correct_GETFIELD2 := GETFIELD2_correct.verify_GETFIELD2_with_pre.
  Definition correct_GETFIELD3 := GETFIELD3_correct.verify_GETFIELD3_with_pre.
  Definition correct_GETFIELD := GETFIELD_correct.GETFIELD_correct_for_spec.
  Definition correct_GETFLOATFIELD := GETFLOATFIELD_correct.verify_GETFLOATFIELD_correct.
  Definition correct_GETGLOBALFIELD := GETGLOBALFIELD_correct.verify_GETGLOBALFIELD_correct.
  Definition correct_GETGLOBAL :
    forall n,
    0 <= Z.of_nat n <= Int.max_signed ->
    handler_correct (handle_GETGLOBAL n) f_instr_GETGLOBAL
      (pre_and (code_at (Int.repr (Z.of_nat n))) (global_offset_safe n))
      (fun _ s => nth_error s.(Machine.global) n = None) (fun _ => False) (fun _ _ _ => False)
    := GETGLOBAL_correct.verify_GETGLOBAL_handler_correct.
  Definition correct_GETMETHOD := GETMETHOD_correct.verify_GETMETHOD_correct.
  Definition correct_GETPUBMET := GETPUBMET_correct.verify_GETPUBMET_correct.
  Definition correct_GETSTRINGCHAR := GETSTRINGCHAR_correct.verify_GETSTRINGCHAR_correct.
  Definition correct_GETVECTITEM := GETVECTITEM_correct.verify_GETVECTITEM_correct.
  Definition correct_GRAB := GRAB_correct.verify_GRAB_correct.
  Definition correct_GTINT := GTINT_correct.verify_GTINT_handler_correct.
  Definition correct_ISINT := ISINT_correct.verify_ISINT_handler_correct.
  Definition correct_LEINT := LEINT_correct.verify_LEINT_handler_correct.
  Definition correct_LSLINT := LSLINT_correct.verify_LSLINT_handler_correct.
  Definition correct_LSRINT := LSRINT_correct.verify_LSRINT_handler_correct.
  Definition correct_LTINT := LTINT_correct.verify_LTINT_handler_correct.
  Definition correct_MAKEBLOCK1 := MAKEBLOCK1_correct.MAKEBLOCK1_correct_for_spec.
  Definition correct_MAKEBLOCK2 := MAKEBLOCK2_correct.MAKEBLOCK2_correct_for_spec.
  Definition correct_MAKEBLOCK3 := MAKEBLOCK3_correct.MAKEBLOCK3_correct_for_spec.
  Definition correct_MAKEBLOCK := MAKEBLOCK_correct.verify_MAKEBLOCK_correct.
  Definition correct_MAKEFLOATBLOCK := MAKEFLOATBLOCK_correct.verify_MAKEFLOATBLOCK_correct.
  Definition correct_MODINT := MODINT_correct.verify_MODINT_handler_correct.
  Definition correct_MULINT := MULINT_correct.verify_MULINT_correct.
  Definition correct_NEGINT := NEGINT_correct.verify_NEGINT_compl_comp.
  Definition correct_NEQ := NEQ_correct.verify_NEQ_handler_correct.
  Definition correct_OFFSETCLOSURE0 := OFFSETCLOSURE0_correct.verify_OFFSETCLOSURE0_compl_comp.
  Definition correct_OFFSETCLOSURE2 := OFFSETCLOSURE2_correct.verify_OFFSETCLOSURE2_compl_comp.
  Definition correct_OFFSETCLOSUREM2 := OFFSETCLOSUREM2_correct.verify_OFFSETCLOSUREM2_compl_comp.
  Definition correct_OFFSETCLOSURE := OFFSETCLOSURE_correct.verify_OFFSETCLOSURE_correct.
  Definition correct_OFFSETINT := OFFSETINT_correct.verify_OFFSETINT_handler_correct.
  Definition correct_OFFSETREF := OFFSETREF_correct.verify_OFFSETREF_correct.
  Definition correct_ORINT := ORINT_correct.verify_ORINT_correct.
  Definition correct_PERFORM := PERFORM_correct.verify_PERFORM_correct.
  Definition correct_POPTRAP := POPTRAP_correct.verify_POPTRAP_correct.
  Definition correct_POP :
    forall n,
    Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_POP n) f_instr_POP
      (pre_and (pre_and (code_at (Int.repr (Z.of_nat n))) code_ne_struct) (stack_length_ge n))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False)
    := POP_correct.verify_POP_handler_correct.
  Definition correct_PUSHACC1 := PUSHACC1_correct.verify_PUSHACC1_correct.
  Definition correct_PUSHACC2 := PUSHACC2_correct.verify_PUSHACC2_correct.
  Definition correct_PUSHACC3 := PUSHACC3_correct.verify_PUSHACC3_correct.
  Definition correct_PUSHACC4 := PUSHACC4_correct.verify_PUSHACC4_correct.
  Definition correct_PUSHACC5 := PUSHACC5_correct.verify_PUSHACC5_correct.
  Definition correct_PUSHACC6 := PUSHACC6_correct.verify_PUSHACC6_correct.
  Definition correct_PUSHACC7 := PUSHACC7_correct.verify_PUSHACC7_correct.
  Definition correct_PUSHATOM0 := PUSHATOM0_correct.verify_PUSHATOM0_correct.
  Definition correct_PUSHATOM :
    forall t, Z.of_nat t <= 2097151 ->
    handler_correct (handle_PUSHATOM t) f_instr_PUSHATOM
      (pre_and (sp_at_least 16) (code_at (Int.repr (Z.of_nat t))))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False)
    := PUSHATOM_correct.verify_PUSHATOM_handler_correct.
  Definition correct_PUSHCONST0 := PUSHCONST0_correct.verify_PUSHCONST0_correct.
  Definition correct_PUSHCONST1 := PUSHCONST1_correct.verify_PUSHCONST1_correct.
  Definition correct_PUSHCONST2 := PUSHCONST2_correct.verify_PUSHCONST2_correct.
  Definition correct_PUSHCONST3 := PUSHCONST3_correct.verify_PUSHCONST3_correct.
  Definition correct_PUSHCONSTINT := PUSHCONSTINT_correct.verify_PUSHCONSTINT_correct.
  Definition correct_PUSHENVACC1 := PUSHENVACC1_correct.verify_PUSHENVACC1_correct.
  Definition correct_PUSHENVACC2 := PUSHENVACC2_correct.verify_PUSHENVACC2_correct.
  Definition correct_PUSHENVACC3 := PUSHENVACC3_correct.verify_PUSHENVACC3_correct.
  Definition correct_PUSHENVACC4 := PUSHENVACC4_correct.verify_PUSHENVACC4_correct.
  Definition correct_PUSHENVACC := PUSHENVACC_correct.verify_PUSHENVACC_correct.
  Definition correct_PUSHGETGLOBALFIELD := PUSHGETGLOBALFIELD_correct.verify_PUSHGETGLOBALFIELD_correct.
  Definition correct_PUSHGETGLOBAL :
    forall n,
    0 <= Z.of_nat n <= Int.max_signed ->
    handler_correct (handle_PUSHGETGLOBAL n) f_instr_PUSHGETGLOBAL
      (pre_and (pre_and (code_at (Int.repr (Z.of_nat n))) (global_offset_safe n)) (sp_at_least 16))
      (fun _ s => nth_error s.(Machine.global) n = None) (fun _ => False) (fun _ _ _ => False)
    := PUSHGETGLOBAL_correct.verify_PUSHGETGLOBAL_handler_correct.
  Definition correct_PUSHOFFSETCLOSURE0 := PUSHOFFSETCLOSURE0_correct.verify_PUSHOFFSETCLOSURE0_correct.
  Definition correct_PUSHOFFSETCLOSURE2 := PUSHOFFSETCLOSURE2_correct.verify_PUSHOFFSETCLOSURE2_correct.
  Definition correct_PUSHOFFSETCLOSUREM2 := PUSHOFFSETCLOSUREM2_correct.verify_PUSHOFFSETCLOSUREM2_correct.
  Definition correct_PUSHOFFSETCLOSURE := PUSHOFFSETCLOSURE_correct.verify_PUSHOFFSETCLOSURE_correct.
  Definition correct_PUSHTRAP := PUSHTRAP_correct.verify_PUSHTRAP_correct.
  Definition correct_PUSH_RETADDR := PUSH_RETADDR_correct.verify_PUSH_RETADDR_correct.
  Definition correct_PUSH := PUSH_correct.verify_PUSH_correct.
  Definition correct_RAISE_NOTRACE := RAISE_NOTRACE_correct.verify_RAISE_NOTRACE_correct.
  Definition correct_RAISE := RAISE_correct.verify_RAISE_correct.
  Definition correct_REPERFORMTERM := REPERFORMTERM_correct.verify_REPERFORMTERM_correct.
  Definition correct_RERAISE := RERAISE_correct.verify_RERAISE_correct.
  Definition correct_RESTART := RESTART_correct.verify_RESTART_correct.
  Definition correct_RESUMETERM := RESUMETERM_correct.verify_RESUMETERM_correct.
  Definition correct_RESUME := RESUME_correct.verify_RESUME_correct.
  Definition correct_RETURN := RETURN_correct.verify_RETURN_correct.
  Definition correct_SETBYTESCHAR := SETBYTESCHAR_correct.verify_SETBYTESCHAR_correct.
  Definition correct_SETFIELD0 := SETFIELD0_correct.verify_SETFIELD0_correct.
  Definition correct_SETFIELD1 := SETFIELD1_correct.verify_SETFIELD1_correct.
  Definition correct_SETFIELD2 := SETFIELD2_correct.verify_SETFIELD2_correct.
  Definition correct_SETFIELD3 := SETFIELD3_correct.verify_SETFIELD3_correct.
  Definition correct_SETFIELD := SETFIELD_correct.verify_SETFIELD_correct.
  Definition correct_SETFLOATFIELD := SETFLOATFIELD_correct.verify_SETFLOATFIELD_correct.
  Definition correct_SETGLOBAL := SETGLOBAL_correct.verify_SETGLOBAL_correct.
  Definition correct_SETVECTITEM := SETVECTITEM_correct.verify_SETVECTITEM_correct.
  Definition correct_STOP := STOP_correct.verify_STOP_correct.
  Definition correct_SUBINT := SUBINT_correct.verify_SUBINT_correct.
  Definition correct_SWITCH := SWITCH_correct.verify_SWITCH_handler_correct.
  Definition correct_UGEINT := UGEINT_correct.verify_UGEINT_handler_correct.
  Definition correct_ULTINT := ULTINT_correct.verify_ULTINT_handler_correct.
  Definition correct_VECTLENGTH := VECTLENGTH_correct.verify_VECTLENGTH_correct.
  Definition correct_XORINT := XORINT_correct.verify_XORINT_correct.

  Section __.
  Set Printing All.
  Set Printing Fully Qualified.
  Set Printing Depth 10000000000.
  Set Printing Width 2000.
  Goal True.
    idtac "<correct_ACC0>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ACC0.
    idtac "</PrintAssumptions>".
    idtac "</correct_ACC0>".
  Abort.
  Goal True.
    idtac "<correct_ACC1>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ACC1.
    idtac "</PrintAssumptions>".
    idtac "</correct_ACC1>".
  Abort.
  Goal True.
    idtac "<correct_ACC2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ACC2.
    idtac "</PrintAssumptions>".
    idtac "</correct_ACC2>".
  Abort.
  Goal True.
    idtac "<correct_ACC3>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ACC3.
    idtac "</PrintAssumptions>".
    idtac "</correct_ACC3>".
  Abort.
  Goal True.
    idtac "<correct_ACC4>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ACC4.
    idtac "</PrintAssumptions>".
    idtac "</correct_ACC4>".
  Abort.
  Goal True.
    idtac "<correct_ACC5>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ACC5.
    idtac "</PrintAssumptions>".
    idtac "</correct_ACC5>".
  Abort.
  Goal True.
    idtac "<correct_ACC6>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ACC6.
    idtac "</PrintAssumptions>".
    idtac "</correct_ACC6>".
  Abort.
  Goal True.
    idtac "<correct_ACC7>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ACC7.
    idtac "</PrintAssumptions>".
    idtac "</correct_ACC7>".
  Abort.
  Goal True.
    idtac "<correct_ACC>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ACC.
    idtac "</PrintAssumptions>".
    idtac "</correct_ACC>".
  Abort.
  Goal True.
    idtac "<correct_ADDINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ADDINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_ADDINT>".
  Abort.
  Goal True.
    idtac "<correct_ANDINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ANDINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_ANDINT>".
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
    idtac "<correct_APPLY>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_APPLY.
    idtac "</PrintAssumptions>".
    idtac "</correct_APPLY>".
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
    idtac "<correct_APPTERM>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_APPTERM.
    idtac "</PrintAssumptions>".
    idtac "</correct_APPTERM>".
  Abort.
  Goal True.
    idtac "<correct_ASRINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ASRINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_ASRINT>".
  Abort.
  Goal True.
    idtac "<correct_ASSIGN>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ASSIGN.
    idtac "</PrintAssumptions>".
    idtac "</correct_ASSIGN>".
  Abort.
  Goal True.
    idtac "<correct_ATOM0>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ATOM0.
    idtac "</PrintAssumptions>".
    idtac "</correct_ATOM0>".
  Abort.
  Goal True.
    idtac "<correct_ATOM>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ATOM.
    idtac "</PrintAssumptions>".
    idtac "</correct_ATOM>".
  Abort.
  Goal True.
    idtac "<correct_BEQ>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BEQ.
    idtac "</PrintAssumptions>".
    idtac "</correct_BEQ>".
  Abort.
  Goal True.
    idtac "<correct_BGEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BGEINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BGEINT>".
  Abort.
  Goal True.
    idtac "<correct_BGTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BGTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BGTINT>".
  Abort.
  Goal True.
    idtac "<correct_BLEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BLEINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BLEINT>".
  Abort.
  Goal True.
    idtac "<correct_BLTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BLTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BLTINT>".
  Abort.
  Goal True.
    idtac "<correct_BNEQ>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BNEQ.
    idtac "</PrintAssumptions>".
    idtac "</correct_BNEQ>".
  Abort.
  Goal True.
    idtac "<correct_BOOLNOT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BOOLNOT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BOOLNOT>".
  Abort.
  Goal True.
    idtac "<correct_BRANCHIFNOT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BRANCHIFNOT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BRANCHIFNOT>".
  Abort.
  Goal True.
    idtac "<correct_BRANCHIF>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BRANCHIF.
    idtac "</PrintAssumptions>".
    idtac "</correct_BRANCHIF>".
  Abort.
  Goal True.
    idtac "<correct_BRANCH>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BRANCH.
    idtac "</PrintAssumptions>".
    idtac "</correct_BRANCH>".
  Abort.
  Goal True.
    idtac "<correct_BREAK>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BREAK.
    idtac "</PrintAssumptions>".
    idtac "</correct_BREAK>".
  Abort.
  Goal True.
    idtac "<correct_BUGEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BUGEINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BUGEINT>".
  Abort.
  Goal True.
    idtac "<correct_BULTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_BULTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_BULTINT>".
  Abort.
  Goal True.
    idtac "<correct_CHECK_SIGNALS>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_CHECK_SIGNALS.
    idtac "</PrintAssumptions>".
    idtac "</correct_CHECK_SIGNALS>".
  Abort.
  Goal True.
    idtac "<correct_CLOSUREREC>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_CLOSUREREC.
    idtac "</PrintAssumptions>".
    idtac "</correct_CLOSUREREC>".
  Abort.
  Goal True.
    idtac "<correct_CLOSURE>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_CLOSURE.
    idtac "</PrintAssumptions>".
    idtac "</correct_CLOSURE>".
  Abort.
  Goal True.
    idtac "<correct_CONST0>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_CONST0.
    idtac "</PrintAssumptions>".
    idtac "</correct_CONST0>".
  Abort.
  Goal True.
    idtac "<correct_CONST1>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_CONST1.
    idtac "</PrintAssumptions>".
    idtac "</correct_CONST1>".
  Abort.
  Goal True.
    idtac "<correct_CONST2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_CONST2.
    idtac "</PrintAssumptions>".
    idtac "</correct_CONST2>".
  Abort.
  Goal True.
    idtac "<correct_CONST3>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_CONST3.
    idtac "</PrintAssumptions>".
    idtac "</correct_CONST3>".
  Abort.
  Goal True.
    idtac "<correct_CONSTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_CONSTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_CONSTINT>".
  Abort.
  Goal True.
    idtac "<correct_C_CALL1>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_C_CALL1.
    idtac "</PrintAssumptions>".
    idtac "</correct_C_CALL1>".
  Abort.
  Goal True.
    idtac "<correct_C_CALL2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_C_CALL2.
    idtac "</PrintAssumptions>".
    idtac "</correct_C_CALL2>".
  Abort.
  Goal True.
    idtac "<correct_C_CALL3>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_C_CALL3.
    idtac "</PrintAssumptions>".
    idtac "</correct_C_CALL3>".
  Abort.
  Goal True.
    idtac "<correct_C_CALL4>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_C_CALL4.
    idtac "</PrintAssumptions>".
    idtac "</correct_C_CALL4>".
  Abort.
  Goal True.
    idtac "<correct_C_CALL5>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_C_CALL5.
    idtac "</PrintAssumptions>".
    idtac "</correct_C_CALL5>".
  Abort.
  Goal True.
    idtac "<correct_C_CALLN>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_C_CALLN.
    idtac "</PrintAssumptions>".
    idtac "</correct_C_CALLN>".
  Abort.
  Goal True.
    idtac "<correct_DIVINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_DIVINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_DIVINT>".
  Abort.
  Goal True.
    idtac "<correct_ENVACC1>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ENVACC1.
    idtac "</PrintAssumptions>".
    idtac "</correct_ENVACC1>".
  Abort.
  Goal True.
    idtac "<correct_ENVACC2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ENVACC2.
    idtac "</PrintAssumptions>".
    idtac "</correct_ENVACC2>".
  Abort.
  Goal True.
    idtac "<correct_ENVACC3>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ENVACC3.
    idtac "</PrintAssumptions>".
    idtac "</correct_ENVACC3>".
  Abort.
  Goal True.
    idtac "<correct_ENVACC4>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ENVACC4.
    idtac "</PrintAssumptions>".
    idtac "</correct_ENVACC4>".
  Abort.
  Goal True.
    idtac "<correct_ENVACC>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ENVACC.
    idtac "</PrintAssumptions>".
    idtac "</correct_ENVACC>".
  Abort.
  Goal True.
    idtac "<correct_EQ>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_EQ.
    idtac "</PrintAssumptions>".
    idtac "</correct_EQ>".
  Abort.
  Goal True.
    idtac "<correct_EVENT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_EVENT.
    idtac "</PrintAssumptions>".
    idtac "</correct_EVENT>".
  Abort.
  Goal True.
    idtac "<correct_GEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GEINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_GEINT>".
  Abort.
  Goal True.
    idtac "<correct_GETBYTESCHAR>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETBYTESCHAR.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETBYTESCHAR>".
  Abort.
  Goal True.
    idtac "<correct_GETDYNMET>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETDYNMET.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETDYNMET>".
  Abort.
  Goal True.
    idtac "<correct_GETFIELD0>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETFIELD0.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETFIELD0>".
  Abort.
  Goal True.
    idtac "<correct_GETFIELD1>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETFIELD1.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETFIELD1>".
  Abort.
  Goal True.
    idtac "<correct_GETFIELD2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETFIELD2.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETFIELD2>".
  Abort.
  Goal True.
    idtac "<correct_GETFIELD3>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETFIELD3.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETFIELD3>".
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
    idtac "<correct_GETGLOBALFIELD>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETGLOBALFIELD.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETGLOBALFIELD>".
  Abort.
  Goal True.
    idtac "<correct_GETGLOBAL>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETGLOBAL.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETGLOBAL>".
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
    idtac "<correct_GETSTRINGCHAR>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETSTRINGCHAR.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETSTRINGCHAR>".
  Abort.
  Goal True.
    idtac "<correct_GETVECTITEM>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GETVECTITEM.
    idtac "</PrintAssumptions>".
    idtac "</correct_GETVECTITEM>".
  Abort.
  Goal True.
    idtac "<correct_GRAB>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GRAB.
    idtac "</PrintAssumptions>".
    idtac "</correct_GRAB>".
  Abort.
  Goal True.
    idtac "<correct_GTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_GTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_GTINT>".
  Abort.
  Goal True.
    idtac "<correct_ISINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ISINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_ISINT>".
  Abort.
  Goal True.
    idtac "<correct_LEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_LEINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_LEINT>".
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
    idtac "<correct_LTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_LTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_LTINT>".
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
    idtac "<correct_MAKEBLOCK>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_MAKEBLOCK.
    idtac "</PrintAssumptions>".
    idtac "</correct_MAKEBLOCK>".
  Abort.
  Goal True.
    idtac "<correct_MAKEFLOATBLOCK>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_MAKEFLOATBLOCK.
    idtac "</PrintAssumptions>".
    idtac "</correct_MAKEFLOATBLOCK>".
  Abort.
  Goal True.
    idtac "<correct_MODINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_MODINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_MODINT>".
  Abort.
  Goal True.
    idtac "<correct_MULINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_MULINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_MULINT>".
  Abort.
  Goal True.
    idtac "<correct_NEGINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_NEGINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_NEGINT>".
  Abort.
  Goal True.
    idtac "<correct_NEQ>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_NEQ.
    idtac "</PrintAssumptions>".
    idtac "</correct_NEQ>".
  Abort.
  Goal True.
    idtac "<correct_OFFSETCLOSURE0>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_OFFSETCLOSURE0.
    idtac "</PrintAssumptions>".
    idtac "</correct_OFFSETCLOSURE0>".
  Abort.
  Goal True.
    idtac "<correct_OFFSETCLOSURE2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_OFFSETCLOSURE2.
    idtac "</PrintAssumptions>".
    idtac "</correct_OFFSETCLOSURE2>".
  Abort.
  Goal True.
    idtac "<correct_OFFSETCLOSUREM2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_OFFSETCLOSUREM2.
    idtac "</PrintAssumptions>".
    idtac "</correct_OFFSETCLOSUREM2>".
  Abort.
  Goal True.
    idtac "<correct_OFFSETCLOSURE>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_OFFSETCLOSURE.
    idtac "</PrintAssumptions>".
    idtac "</correct_OFFSETCLOSURE>".
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
    idtac "<correct_ORINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ORINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_ORINT>".
  Abort.
  Goal True.
    idtac "<correct_PERFORM>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PERFORM.
    idtac "</PrintAssumptions>".
    idtac "</correct_PERFORM>".
  Abort.
  Goal True.
    idtac "<correct_POPTRAP>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_POPTRAP.
    idtac "</PrintAssumptions>".
    idtac "</correct_POPTRAP>".
  Abort.
  Goal True.
    idtac "<correct_POP>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_POP.
    idtac "</PrintAssumptions>".
    idtac "</correct_POP>".
  Abort.
  Goal True.
    idtac "<correct_PUSHACC1>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHACC1.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHACC1>".
  Abort.
  Goal True.
    idtac "<correct_PUSHACC2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHACC2.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHACC2>".
  Abort.
  Goal True.
    idtac "<correct_PUSHACC3>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHACC3.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHACC3>".
  Abort.
  Goal True.
    idtac "<correct_PUSHACC4>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHACC4.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHACC4>".
  Abort.
  Goal True.
    idtac "<correct_PUSHACC5>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHACC5.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHACC5>".
  Abort.
  Goal True.
    idtac "<correct_PUSHACC6>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHACC6.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHACC6>".
  Abort.
  Goal True.
    idtac "<correct_PUSHACC7>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHACC7.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHACC7>".
  Abort.
  Goal True.
    idtac "<correct_PUSHATOM0>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHATOM0.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHATOM0>".
  Abort.
  Goal True.
    idtac "<correct_PUSHATOM>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHATOM.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHATOM>".
  Abort.
  Goal True.
    idtac "<correct_PUSHCONST0>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHCONST0.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHCONST0>".
  Abort.
  Goal True.
    idtac "<correct_PUSHCONST1>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHCONST1.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHCONST1>".
  Abort.
  Goal True.
    idtac "<correct_PUSHCONST2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHCONST2.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHCONST2>".
  Abort.
  Goal True.
    idtac "<correct_PUSHCONST3>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHCONST3.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHCONST3>".
  Abort.
  Goal True.
    idtac "<correct_PUSHCONSTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHCONSTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHCONSTINT>".
  Abort.
  Goal True.
    idtac "<correct_PUSHENVACC1>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHENVACC1.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHENVACC1>".
  Abort.
  Goal True.
    idtac "<correct_PUSHENVACC2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHENVACC2.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHENVACC2>".
  Abort.
  Goal True.
    idtac "<correct_PUSHENVACC3>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHENVACC3.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHENVACC3>".
  Abort.
  Goal True.
    idtac "<correct_PUSHENVACC4>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHENVACC4.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHENVACC4>".
  Abort.
  Goal True.
    idtac "<correct_PUSHENVACC>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHENVACC.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHENVACC>".
  Abort.
  Goal True.
    idtac "<correct_PUSHGETGLOBALFIELD>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHGETGLOBALFIELD.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHGETGLOBALFIELD>".
  Abort.
  Goal True.
    idtac "<correct_PUSHGETGLOBAL>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHGETGLOBAL.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHGETGLOBAL>".
  Abort.
  Goal True.
    idtac "<correct_PUSHOFFSETCLOSURE0>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHOFFSETCLOSURE0.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHOFFSETCLOSURE0>".
  Abort.
  Goal True.
    idtac "<correct_PUSHOFFSETCLOSURE2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHOFFSETCLOSURE2.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHOFFSETCLOSURE2>".
  Abort.
  Goal True.
    idtac "<correct_PUSHOFFSETCLOSUREM2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHOFFSETCLOSUREM2.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHOFFSETCLOSUREM2>".
  Abort.
  Goal True.
    idtac "<correct_PUSHOFFSETCLOSURE>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHOFFSETCLOSURE.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHOFFSETCLOSURE>".
  Abort.
  Goal True.
    idtac "<correct_PUSHTRAP>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSHTRAP.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSHTRAP>".
  Abort.
  Goal True.
    idtac "<correct_PUSH_RETADDR>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSH_RETADDR.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSH_RETADDR>".
  Abort.
  Goal True.
    idtac "<correct_PUSH>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_PUSH.
    idtac "</PrintAssumptions>".
    idtac "</correct_PUSH>".
  Abort.
  Goal True.
    idtac "<correct_RAISE_NOTRACE>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_RAISE_NOTRACE.
    idtac "</PrintAssumptions>".
    idtac "</correct_RAISE_NOTRACE>".
  Abort.
  Goal True.
    idtac "<correct_RAISE>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_RAISE.
    idtac "</PrintAssumptions>".
    idtac "</correct_RAISE>".
  Abort.
  Goal True.
    idtac "<correct_REPERFORMTERM>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_REPERFORMTERM.
    idtac "</PrintAssumptions>".
    idtac "</correct_REPERFORMTERM>".
  Abort.
  Goal True.
    idtac "<correct_RERAISE>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_RERAISE.
    idtac "</PrintAssumptions>".
    idtac "</correct_RERAISE>".
  Abort.
  Goal True.
    idtac "<correct_RESTART>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_RESTART.
    idtac "</PrintAssumptions>".
    idtac "</correct_RESTART>".
  Abort.
  Goal True.
    idtac "<correct_RESUMETERM>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_RESUMETERM.
    idtac "</PrintAssumptions>".
    idtac "</correct_RESUMETERM>".
  Abort.
  Goal True.
    idtac "<correct_RESUME>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_RESUME.
    idtac "</PrintAssumptions>".
    idtac "</correct_RESUME>".
  Abort.
  Goal True.
    idtac "<correct_RETURN>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_RETURN.
    idtac "</PrintAssumptions>".
    idtac "</correct_RETURN>".
  Abort.
  Goal True.
    idtac "<correct_SETBYTESCHAR>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SETBYTESCHAR.
    idtac "</PrintAssumptions>".
    idtac "</correct_SETBYTESCHAR>".
  Abort.
  Goal True.
    idtac "<correct_SETFIELD0>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SETFIELD0.
    idtac "</PrintAssumptions>".
    idtac "</correct_SETFIELD0>".
  Abort.
  Goal True.
    idtac "<correct_SETFIELD1>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SETFIELD1.
    idtac "</PrintAssumptions>".
    idtac "</correct_SETFIELD1>".
  Abort.
  Goal True.
    idtac "<correct_SETFIELD2>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SETFIELD2.
    idtac "</PrintAssumptions>".
    idtac "</correct_SETFIELD2>".
  Abort.
  Goal True.
    idtac "<correct_SETFIELD3>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SETFIELD3.
    idtac "</PrintAssumptions>".
    idtac "</correct_SETFIELD3>".
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
    idtac "<correct_SETGLOBAL>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SETGLOBAL.
    idtac "</PrintAssumptions>".
    idtac "</correct_SETGLOBAL>".
  Abort.
  Goal True.
    idtac "<correct_SETVECTITEM>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SETVECTITEM.
    idtac "</PrintAssumptions>".
    idtac "</correct_SETVECTITEM>".
  Abort.
  Goal True.
    idtac "<correct_STOP>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_STOP.
    idtac "</PrintAssumptions>".
    idtac "</correct_STOP>".
  Abort.
  Goal True.
    idtac "<correct_SUBINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SUBINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_SUBINT>".
  Abort.
  Goal True.
    idtac "<correct_SWITCH>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_SWITCH.
    idtac "</PrintAssumptions>".
    idtac "</correct_SWITCH>".
  Abort.
  Goal True.
    idtac "<correct_UGEINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_UGEINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_UGEINT>".
  Abort.
  Goal True.
    idtac "<correct_ULTINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_ULTINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_ULTINT>".
  Abort.
  Goal True.
    idtac "<correct_VECTLENGTH>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_VECTLENGTH.
    idtac "</PrintAssumptions>".
    idtac "</correct_VECTLENGTH>".
  Abort.
  Goal True.
    idtac "<correct_XORINT>".
    idtac "<PrintAssumptions>".
    Print Assumptions correct_XORINT.
    idtac "</PrintAssumptions>".
    idtac "</correct_XORINT>".
  Abort.
  End __.
End InstructVerification.
