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
  Lemma correct_APPLY1 :
    handler_correct (fun pc' s => handle_APPLY1 pc' s) f_instr_APPLY1
      no_pre
      (fun msg s => (msg = "APPLY1: accu is not a closure"%string /\ get_code_ptr_s s s.(Machine.accu) = None) \/ (msg = "APPLY1: stack underflow"%string)) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_APPLY2 :
    handler_correct (fun pc' s => handle_APPLY2 pc' s) f_instr_APPLY2
      no_pre
      (fun msg s => (msg = "APPLY2: accu is not a closure"%string /\ get_code_ptr_s s s.(Machine.accu) = None) \/ (msg = "APPLY2: stack underflow"%string)) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_APPLY3 :
    handler_correct (fun pc' s => handle_APPLY3 pc' s) f_instr_APPLY3
      no_pre
      (fun msg s => match s.(Machine.stack) with | _ :: _ :: _ :: _ => get_code_ptr_s s s.(Machine.accu) = None | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_APPLY :
    forall n,
    handler_correct (fun _ s => handle_APPLY n s) f_instr_APPLY
      no_pre
      (fun msg s => get_code_ptr_s s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_APPTERM1 :
    forall slotsize,
    handler_correct (fun _ s => handle_APPTERM1 slotsize s) f_instr_APPTERM1
      no_pre
      (fun msg s => s.(Machine.stack) = nil \/ get_code_ptr_s s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_APPTERM2 :
    forall slotsize,
    handler_correct (fun _ s => handle_APPTERM2 slotsize s) f_instr_APPTERM2
      no_pre
      (fun msg s => s.(Machine.stack) = nil \/ (exists a, s.(Machine.stack) = a :: nil) \/ get_code_ptr_s s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_APPTERM3 :
    forall slotsize,
    handler_correct (fun _ s => handle_APPTERM3 slotsize s) f_instr_APPTERM3
      no_pre
      (fun msg s => match s.(Machine.stack) with | _ :: _ :: _ :: _ => False | _ => True end \/ get_code_ptr_s s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_APPTERM :
    forall nargs slotsize,
    handler_correct (fun _ s => handle_APPTERM nargs slotsize s) f_instr_APPTERM
      no_pre
      (fun msg s => get_code_ptr_s s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Definition correct_ASRINT := verify_ASRINT_handler_correct.
  Lemma correct_ASSIGN :
    forall n,
    handler_correct (handle_ASSIGN n) f_instr_ASSIGN
      no_pre
      (fun _ s => set_nth s.(Machine.stack) n s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Definition correct_ATOM0 := verify_ATOM0_correct.
  Definition correct_ATOM := verify_ATOM_correct.
  Definition correct_BEQ :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BEQ n target) f_instr_BEQ
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_signed_int)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False)
    := verify_BEQ_handler_correct.
  Definition correct_BGEINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BGEINT n target) f_instr_BGEINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_signed_int)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False)
    := verify_BGEINT_handler_correct.
  Definition correct_BGTINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BGTINT n target) f_instr_BGTINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_signed_int)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False)
    := verify_BGTINT_handler_correct.
  Definition correct_BLEINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BLEINT n target) f_instr_BLEINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_signed_int)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False)
    := verify_BLEINT_handler_correct.
  Definition correct_BLTINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BLTINT n target) f_instr_BLTINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_signed_int)
      (fun msg s => msg = "BLTINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False)
    := verify_BLTINT_handler_correct.
  Definition correct_BNEQ :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BNEQ n target) f_instr_BNEQ
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_signed_int)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False)
    := verify_BNEQ_handler_correct.
  Definition correct_BOOLNOT := verify_BOOLNOT_handler_correct.
  Lemma correct_BRANCHIFNOT :
    forall target,
    handler_correct (handle_BRANCHIFNOT target) f_instr_BRANCHIFNOT
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_BRANCHIF :
    forall target,
    handler_correct (handle_BRANCHIF target) f_instr_BRANCHIF
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
  Admitted.
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
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_unsigned_int)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False)
    := verify_BUGEINT_handler_correct.
  Definition correct_BULTINT :
    forall n target,
    0 <= n -> Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BULTINT n target) f_instr_BULTINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_unsigned_int)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False)
    := verify_BULTINT_handler_correct.
  Definition correct_CHECK_SIGNALS := verify_CHECK_SIGNALS_correct.
  Lemma correct_CLOSUREREC :
    forall code_ofs,
    handler_correct (handle_CLOSUREREC 1 0 [code_ofs]) f_instr_CLOSUREREC
      no_pre
      (fun msg _ => msg = "CLOSUREREC: no code offsets"%string -> False) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_CLOSURE :
    forall code_ofs,
    handler_correct (handle_CLOSURE 0 code_ofs) f_instr_CLOSURE
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
  Admitted.
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
  Lemma correct_ENVACC1 :
    handler_correct (handle_ENVACC 1) f_instr_ENVACC1
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 1 = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_ENVACC2 :
    handler_correct (handle_ENVACC 2) f_instr_ENVACC2
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 2 = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_ENVACC3 :
    handler_correct (handle_ENVACC 3) f_instr_ENVACC3
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 3 = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_ENVACC4 :
    handler_correct (handle_ENVACC 4) f_instr_ENVACC4
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 4 = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_ENVACC :
    forall n,
    handler_correct (handle_ENVACC n) f_instr_ENVACC
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) n = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Definition correct_EQ := verify_EQ_handler_correct.
  Definition correct_EVENT := verify_EVENT_correct.
  Definition correct_GEINT := verify_GEINT_handler_correct.
  Lemma correct_GETBYTESCHAR :
    handler_correct handle_GETSTRINGCHAR f_instr_GETBYTESCHAR
      no_pre
      (fun msg s => match s.(Machine.stack) with | Val_int idx :: _ => match field_or_heap s s.(Machine.accu) (Z.to_nat idx) with | Some (Val_int _) => False | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_GETDYNMET :
    handler_correct handle_GETDYNMET f_instr_GETDYNMET
      no_pre
      (fun msg s => True) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_GETFIELD0 :
    handler_correct (handle_GETFIELD 0) f_instr_GETFIELD0
      no_pre
      (fun _ s => field_or_heap s s.(Machine.accu) 0 = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_GETFIELD1 :
    handler_correct (handle_GETFIELD 1) f_instr_GETFIELD1
      no_pre
      (fun _ s => field_or_heap s s.(Machine.accu) 1 = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_GETFIELD2 :
    handler_correct (handle_GETFIELD 2) f_instr_GETFIELD2
      no_pre
      (fun _ s => field_or_heap s s.(Machine.accu) 2 = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_GETFIELD3 :
    handler_correct (handle_GETFIELD 3) f_instr_GETFIELD3
      no_pre
      (fun _ s => field_or_heap s s.(Machine.accu) 3 = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_GETFIELD :
    forall n,
    handler_correct (handle_GETFIELD n) f_instr_GETFIELD
      no_pre
      (fun _ s => field_or_heap s s.(Machine.accu) n = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_GETFLOATFIELD :
    forall n,
    handler_correct (handle_GETFLOATFIELD n) f_instr_GETFLOATFIELD
      no_pre
      (fun _ s => field_or_heap s s.(Machine.accu) n = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_GETGLOBALFIELD :
    forall n p,
    handler_correct (handle_GETGLOBALFIELD n p) f_instr_GETGLOBALFIELD
      no_pre
      (fun msg s => (nth_error s.(Machine.global) n = None /\ msg = "GETGLOBALFIELD: index out of bounds"%string) \/ (exists glob, nth_error s.(Machine.global) n = Some glob /\ field_or_heap s glob p = None /\ msg = "GETGLOBALFIELD: field access failed"%string)) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Definition correct_GETGLOBAL :
    forall n,
    0 <= Z.of_nat n <= Int.max_signed ->
    handler_correct (handle_GETGLOBAL n) f_instr_GETGLOBAL
      (pre_and (code_at (Int.repr (Z.of_nat n))) (global_offset_safe n))
      (fun _ s => nth_error s.(Machine.global) n = None) (fun _ => False) (fun _ _ _ => False)
    := verify_GETGLOBAL_handler_correct.
  Lemma correct_GETMETHOD :
    handler_correct handle_GETMETHOD f_instr_GETMETHOD
      no_pre
      (fun msg s => match msg with | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_GETPUBMET :
    forall tag,
    handler_correct (handle_GETPUBMET tag) f_instr_GETPUBMET
      no_pre
      (fun msg s => True) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_GETSTRINGCHAR :
    handler_correct handle_GETSTRINGCHAR f_instr_GETSTRINGCHAR
      no_pre
      (fun msg s => match s.(Machine.stack) with | Val_int idx :: _ => match field_or_heap s s.(Machine.accu) (Z.to_nat idx) with | Some (Val_int _) => False | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_GETVECTITEM :
    handler_correct handle_GETVECTITEM f_instr_GETVECTITEM
      no_pre
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | _, Val_int idx :: _ => field_or_heap s s.(Machine.accu) (Z.to_nat idx) = None | _, _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_GRAB :
    forall required,
    handler_correct (handle_GRAB required) f_instr_GRAB
      no_pre
      (fun msg s => msg = "GRAB: malformed return frame"%string /\ Nat.leb required (extra_args s) = false /\ match skipn (S (extra_args s)) (Machine.stack s) with | Val_int _ :: _ :: Val_int _ :: _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Definition correct_GTINT := verify_GTINT_handler_correct.
  Definition correct_ISINT := verify_ISINT_handler_correct.
  Definition correct_LEINT := verify_LEINT_handler_correct.
  Definition correct_LSLINT := verify_LSLINT_handler_correct.
  Definition correct_LSRINT := verify_LSRINT_handler_correct.
  Definition correct_LTINT := verify_LTINT_handler_correct.
  Lemma correct_MAKEBLOCK1 :
    forall t,
    handler_correct (handle_MAKEBLOCK1 t) f_instr_MAKEBLOCK1
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_MAKEBLOCK2 :
    forall t,
    handler_correct (handle_MAKEBLOCK2 t) f_instr_MAKEBLOCK2
      no_pre
      (fun _ s => match s.(Machine.stack) with _ :: _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_MAKEBLOCK3 :
    forall t,
    handler_correct (handle_MAKEBLOCK3 t) f_instr_MAKEBLOCK3
      no_pre
      (fun _ s => match s.(Machine.stack) with _ :: _ :: _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_MAKEBLOCK :
    forall (t size : nat), (size >= 1)%nat ->
    handler_correct (handle_MAKEBLOCK t size) f_instr_MAKEBLOCK
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_MAKEFLOATBLOCK :
    forall (n : nat), (n >= 1)%nat ->
    handler_correct (handle_MAKEFLOATBLOCK n) f_instr_MAKEFLOATBLOCK
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Definition correct_MODINT := verify_MODINT_handler_correct.
  Definition correct_MULINT := verify_MULINT_correct.
  Definition correct_NEGINT := verify_NEGINT_compl_comp.
  Definition correct_NEQ := verify_NEQ_handler_correct.
  Definition correct_OFFSETCLOSURE0 := verify_OFFSETCLOSURE0_compl_comp.
  Lemma correct_OFFSETCLOSURE2 :
    handler_correct (handle_OFFSETCLOSURE 2) f_instr_OFFSETCLOSURE2
      no_pre
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_OFFSETCLOSUREM2 :
    handler_correct (handle_OFFSETCLOSURE (-2)) f_instr_OFFSETCLOSUREM2
      no_pre
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_OFFSETCLOSURE :
    forall n,
    handler_correct (handle_OFFSETCLOSURE n) f_instr_OFFSETCLOSURE
      no_pre
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Definition correct_OFFSETINT := verify_OFFSETINT_handler_correct.
  Lemma correct_OFFSETREF :
    forall n,
    handler_correct (handle_OFFSETREF n) f_instr_OFFSETREF
      no_pre
      (fun _ s => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, Val_int _ :: _) => False | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Definition correct_ORINT := verify_ORINT_correct.
  Definition correct_PERFORM := verify_PERFORM_correct.
  Lemma correct_POPTRAP :
    handler_correct (handle_POPTRAP) f_instr_POPTRAP
      no_pre
      (fun msg _ => msg = "POPTRAP: malformed trap frame"%string) (fun _ => False) (fun _ _ _ => False).
  Admitted.
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
  Lemma correct_PUSHCONSTINT :
    forall n,
    handler_correct (handle_PUSHCONSTINT n) f_instr_PUSHCONSTINT
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_PUSHENVACC1 :
    handler_correct (handle_PUSHENVACC 1) f_instr_PUSHENVACC1
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 1 = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_PUSHENVACC2 :
    handler_correct (handle_PUSHENVACC 2) f_instr_PUSHENVACC2
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 2 = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_PUSHENVACC3 :
    handler_correct (handle_PUSHENVACC 3) f_instr_PUSHENVACC3
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 3 = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_PUSHENVACC4 :
    handler_correct (handle_PUSHENVACC 4) f_instr_PUSHENVACC4
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 4 = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_PUSHENVACC :
    forall n,
    handler_correct (handle_PUSHENVACC n) f_instr_PUSHENVACC
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) n = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_PUSHGETGLOBALFIELD :
    forall n p,
    handler_correct (handle_PUSHGETGLOBALFIELD n p) f_instr_PUSHGETGLOBALFIELD
      no_pre
      (fun msg s => nth_error s.(Machine.global) n = None \/ (exists glob, nth_error s.(Machine.global) n = Some glob /\ field_or_heap s glob p = None)) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Definition correct_PUSHGETGLOBAL :
    forall n,
    0 <= Z.of_nat n <= Int.max_signed ->
    handler_correct (handle_PUSHGETGLOBAL n) f_instr_PUSHGETGLOBAL
      (pre_and (pre_and (code_at (Int.repr (Z.of_nat n))) (global_offset_safe n)) (sp_at_least 16))
      (fun _ s => nth_error s.(Machine.global) n = None) (fun _ => False) (fun _ _ _ => False)
    := verify_PUSHGETGLOBAL_handler_correct.
  Definition correct_PUSHOFFSETCLOSURE0 := verify_PUSHOFFSETCLOSURE0_correct.
  Lemma correct_PUSHOFFSETCLOSURE2 :
    handler_correct (handle_PUSHOFFSETCLOSURE 2) f_instr_PUSHOFFSETCLOSURE2
      no_pre
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_PUSHOFFSETCLOSUREM2 :
    handler_correct (handle_PUSHOFFSETCLOSURE (-2)) f_instr_PUSHOFFSETCLOSUREM2
      no_pre
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_PUSHOFFSETCLOSURE :
    forall ofs,
    handler_correct (handle_PUSHOFFSETCLOSURE ofs) f_instr_PUSHOFFSETCLOSURE
      no_pre
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_PUSHTRAP :
    forall handler_pc,
    handler_correct (handle_PUSHTRAP handler_pc) f_instr_PUSHTRAP
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_PUSH_RETADDR :
    forall ret_addr,
    handler_correct (handle_PUSH_RETADDR ret_addr) f_instr_PUSH_RETADDR
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Definition correct_PUSH := verify_PUSH_correct.
  Lemma correct_RAISE_NOTRACE :
    handler_correct (fun _pc s => do_raise s.(accu) s) f_instr_RAISE_NOTRACE
      no_pre
      (fun msg _ => msg = "unhandled exception"%string \/ msg = "RAISE: malformed trap frame"%string) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_RAISE :
    handler_correct (fun _pc s => do_raise s.(accu) s) f_instr_RAISE
      no_pre
      (fun msg _ => msg = "unhandled exception"%string \/ msg = "RAISE: malformed trap frame"%string) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Definition correct_REPERFORMTERM := verify_REPERFORMTERM_correct.
  Lemma correct_RERAISE :
    handler_correct (fun _pc s => do_raise s.(accu) s) f_instr_RERAISE
      no_pre
      (fun msg _ => msg = "unhandled exception"%string \/ msg = "RAISE: malformed trap frame"%string) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_RESTART :
    handler_correct handle_RESTART f_instr_RESTART
      no_pre
      (fun msg s => (msg = "RESTART: env is not a block"%string /\ match Machine.env s with | Val_int _ | Val_ptr _ => True | _ => False end) \/ (msg = "RESTART: dangling pointer"%string /\ exists addr ofs, Machine.env s = Val_closure addr ofs /\ heap_lookup s.(Machine.hp) addr = None) \/ (msg = "RESTART: env is not a closure"%string /\ ((exists addr ofs t fs, Machine.env s = Val_closure addr ofs /\ heap_lookup s.(Machine.hp) addr = Some (t, fs) /\ Nat.eqb t Closure_tag = false) \/ (exists t fs, Machine.env s = Val_block t fs /\ Nat.eqb t Closure_tag = false))) \/ (msg = "RESTART: malformed closure"%string /\ ((exists addr ofs t all_fields, Machine.env s = Val_closure addr ofs /\ heap_lookup s.(Machine.hp) addr = Some (t, all_fields) /\ Nat.eqb t Closure_tag = true /\ nth_error (skipn ofs all_fields) 2 = None) \/ (exists t fs, Machine.env s = Val_block t fs /\ Nat.eqb t Closure_tag = true /\ nth_error fs 2 = None)))) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Definition correct_RESUMETERM := verify_RESUMETERM_correct.
  Definition correct_RESUME := verify_RESUME_correct.
  Lemma correct_RETURN :
    forall stacksize,
    handler_correct (fun _ => handle_RETURN stacksize) f_instr_RETURN
      no_pre
      (fun msg _ => msg = "RETURN: accu is not a closure"%string \/ msg = "RETURN: malformed return frame"%string) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_SETBYTESCHAR :
    handler_correct handle_SETBYTESCHAR f_instr_SETBYTESCHAR
      no_pre
      (fun _ s => match s.(Machine.stack) with | Val_int idx :: Val_int newchar :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields (Z.to_nat idx) (Val_int newchar) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_SETFIELD0 :
    handler_correct (handle_SETFIELD 0) f_instr_SETFIELD0
      no_pre
      (fun _ s => match s.(Machine.stack) with | _ :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields 0 (hd (Val_int 0) s.(Machine.stack)) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_SETFIELD1 :
    handler_correct (handle_SETFIELD 1) f_instr_SETFIELD1
      no_pre
      (fun _ s => match s.(Machine.stack) with | _ :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields 1 (hd (Val_int 0) s.(Machine.stack)) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_SETFIELD2 :
    handler_correct (handle_SETFIELD 2) f_instr_SETFIELD2
      no_pre
      (fun _ s => match s.(Machine.stack) with | _ :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields 2 (hd (Val_int 0) s.(Machine.stack)) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_SETFIELD3 :
    handler_correct (handle_SETFIELD 3) f_instr_SETFIELD3
      no_pre
      (fun _ s => match s.(Machine.stack) with | _ :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields 3 (hd (Val_int 0) s.(Machine.stack)) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_SETFIELD :
    forall n,
    handler_correct (handle_SETFIELD n) f_instr_SETFIELD
      no_pre
      (fun _ s => match s.(Machine.stack) with | newval :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields n newval = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_SETFLOATFIELD :
    forall n,
    handler_correct (handle_SETFLOATFIELD n) f_instr_SETFLOATFIELD
      no_pre
      (fun _ s => match s.(Machine.stack) with | _ :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields n (hd (Val_int 0) s.(Machine.stack)) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_SETGLOBAL :
    forall n,
    handler_correct (handle_SETGLOBAL n) f_instr_SETGLOBAL
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Lemma correct_SETVECTITEM :
    handler_correct handle_SETVECTITEM f_instr_SETVECTITEM
      no_pre
      (fun _ s => match s.(Machine.stack) with | Val_int idx :: newval :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields (Z.to_nat idx) newval = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Definition correct_STOP := verify_STOP_correct.
  Definition correct_SUBINT := verify_SUBINT_correct.
  Lemma correct_SWITCH :
    forall (_nc _nb : nat) (const_targets block_targets : list Z),
    handler_correct (fun _ s => handle_SWITCH _nc _nb const_targets block_targets s) f_instr_SWITCH
      no_pre
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Definition correct_UGEINT := verify_UGEINT_handler_correct.
  Definition correct_ULTINT := verify_ULTINT_handler_correct.
  Lemma correct_VECTLENGTH :
    handler_correct handle_VECTLENGTH f_instr_VECTLENGTH
      no_pre
      (fun _ s => size_or_heap s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).
  Admitted.
  Definition correct_XORINT := verify_XORINT_correct.
End InstructVerification.
