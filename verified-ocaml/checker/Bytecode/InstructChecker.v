(* InstructVerification.v — Instantiation of InstructVerificationSpec. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import AST Integers Ctypes Cop Clight ClightBigstep Events Globalenvs Memory Values.
From RecordUpdate Require Import RecordUpdate.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.InstructSpec.

From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ACC0_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ACC1_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ACC2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ACC3_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ACC4_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ACC5_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ACC6_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ACC7_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ACC_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ADDINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ANDINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.APPLY1_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.APPLY2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.APPLY3_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.APPLY_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.APPTERM1_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.APPTERM2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.APPTERM3_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.APPTERM_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ASRINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ASSIGN_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ATOM0_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ATOM_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.BEQ_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.BGEINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.BGTINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.BLEINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.BLTINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.BNEQ_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.BOOLNOT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.BRANCHIFNOT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.BRANCHIF_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.BRANCH_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.BREAK_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.BUGEINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.BULTINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.CHECK_SIGNALS_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.CLOSUREREC_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.CLOSURE_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.CONST0_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.CONST1_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.CONST2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.CONST3_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.CONSTINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.C_CALL1_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.C_CALL2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.C_CALL3_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.C_CALL4_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.C_CALL5_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.C_CALLN_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.DIVINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ENVACC1_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ENVACC2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ENVACC3_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ENVACC4_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ENVACC_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.EQ_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.EVENT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GEINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETBYTESCHAR_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETDYNMET_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETFIELD0_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETFIELD1_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETFIELD2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETFIELD3_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETFIELD_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETFLOATFIELD_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETGLOBALFIELD_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETGLOBAL_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETMETHOD_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETPUBMET_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETSTRINGCHAR_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETVECTITEM_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GRAB_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GTINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ISINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.LEINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.LSLINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.LSRINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.LTINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.MAKEBLOCK1_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.MAKEBLOCK2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.MAKEBLOCK3_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.MAKEBLOCK_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.MAKEFLOATBLOCK_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.MODINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.MULINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.NEGINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.NEQ_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.OFFSETCLOSURE0_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.OFFSETCLOSURE2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.OFFSETCLOSUREM2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.OFFSETCLOSURE_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.OFFSETINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.OFFSETREF_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ORINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PERFORM_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.POPTRAP_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.POP_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHACC1_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHACC2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHACC3_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHACC4_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHACC5_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHACC6_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHACC7_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHATOM0_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHATOM_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHCONST0_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHCONST1_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHCONST2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHCONST3_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHCONSTINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHENVACC1_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHENVACC2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHENVACC3_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHENVACC4_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHENVACC_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHGETGLOBALFIELD_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHGETGLOBAL_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHOFFSETCLOSURE0_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHOFFSETCLOSURE2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHOFFSETCLOSUREM2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHOFFSETCLOSURE_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSHTRAP_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSH_RETADDR_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.PUSH_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.RAISE_NOTRACE_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.RAISE_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.REPERFORMTERM_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.RERAISE_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.RESTART_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.RESUMETERM_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.RESUME_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.RETURN_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.SETBYTESCHAR_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.SETFIELD0_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.SETFIELD1_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.SETFIELD2_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.SETFIELD3_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.SETFIELD_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.SETFLOATFIELD_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.SETGLOBAL_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.SETVECTITEM_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.STOP_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.SUBINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.SWITCH_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.UGEINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.ULTINT_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.VECTLENGTH_correct.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.XORINT_correct.


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
      (fun msg s => msg = "BGEINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False)
    := verify_BGEINT_handler_correct.
  Definition correct_BGTINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BGTINT n target) f_instr_BGTINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) (pre_and accu_signed_int accu_is_long))
      (fun msg s => msg = "BGTINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False)
    := verify_BGTINT_handler_correct.
  Definition correct_BLEINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BLEINT n target) f_instr_BLEINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) (pre_and accu_signed_int accu_is_long))
      (fun msg s => msg = "BLEINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False)
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
      (fun msg s => msg = "BUGEINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False)
    := verify_BUGEINT_handler_correct.
  Definition correct_BULTINT :
    forall n target,
    0 <= n -> Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BULTINT n target) f_instr_BULTINT
      (pre_and (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_unsigned_int) accu_is_long)
      (fun msg s => msg = "BULTINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False)
    := verify_BULTINT_handler_correct.
  Definition correct_CHECK_SIGNALS := verify_CHECK_SIGNALS_correct.
  Definition correct_CLOSUREREC := CLOSUREREC_correct_for_spec.
  Definition correct_CLOSURE := CLOSURE_correct_for_spec.
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
  Definition correct_ENVACC := ENVACC_correct_for_spec.
  Definition correct_EQ := verify_EQ_handler_correct.
  Definition correct_EVENT := verify_EVENT_correct.
  Definition correct_GEINT := verify_GEINT_handler_correct.
  Definition correct_GETBYTESCHAR := verify_GETBYTESCHAR_correct.
  Definition correct_GETDYNMET := verify_GETDYNMET_correct.
  Definition correct_GETFIELD0 := verify_GETFIELD0_with_pre.
  Definition correct_GETFIELD1 := verify_GETFIELD1_with_pre.
  Definition correct_GETFIELD2 := verify_GETFIELD2_with_pre.
  Definition correct_GETFIELD3 := verify_GETFIELD3_with_pre.
  Definition correct_GETFIELD := GETFIELD_correct_for_spec.
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
  Definition correct_MAKEBLOCK1 := MAKEBLOCK1_correct_for_spec.
  Definition correct_MAKEBLOCK2 := MAKEBLOCK2_correct_for_spec.
  Definition correct_MAKEBLOCK3 := MAKEBLOCK3_correct_for_spec.
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
