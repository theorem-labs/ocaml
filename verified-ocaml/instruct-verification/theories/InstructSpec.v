(* InstructSpec.v -- Module Type relating C instruction handlers to Rocq handlers.
   The C handlers are extracted from OCaml's runtime/interp.c by extract_handlers.sh
   and compiled to Clight AST by clightgen. Each axiom states that the C handler
   produces the same abstract state transition as the corresponding Rocq handle_X.

   For handlers that Step to a new state, the axiom requires the abstraction relation
   to be preserved. For handlers that return Error, the axiom requires the C handler
   to also signal an error. For Halt, the C handler must produce the same value. *)

From Stdlib Require Import ZArith List Strings.String.
Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine Interpret.

(* Abstract C state representation. This will be instantiated with the
   Clight memory/local-environment pair when the Clight AST is available. *)
Parameter c_state : Type.

(* Abstraction relation: a C state corresponds to a Rocq machine state. *)
Parameter abs_rel : c_state -> state -> Prop.

(* C-level error indicator. *)
Parameter c_error : c_state -> Prop.

(* C-level halt with a value. *)
Parameter c_halt : c_state -> value -> Prop.

(* C-level CCall request. *)
Parameter c_ccall : c_state -> nat -> list value -> c_state -> Prop.

Module Type InstructSpec.

  (* ================================================================== *)
  (* Stack operations                                                    *)
  (* ================================================================== *)

  Axiom verify_ACC : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_ACC n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_ACC_err : forall n pc' cs rs msg,
    abs_rel cs rs ->
    handle_ACC n pc' rs = Error msg ->
    c_error cs.

  Axiom verify_PUSH : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_PUSH pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_PUSHACC : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_PUSHACC n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_PUSHACC_err : forall n pc' cs rs msg,
    abs_rel cs rs ->
    handle_PUSHACC n pc' rs = Error msg ->
    c_error cs.

  Axiom verify_POP : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_POP n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_ASSIGN : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_ASSIGN n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_ASSIGN_err : forall n pc' cs rs msg,
    abs_rel cs rs ->
    handle_ASSIGN n pc' rs = Error msg ->
    c_error cs.

  (* ================================================================== *)
  (* Environment access                                                  *)
  (* ================================================================== *)

  Axiom verify_ENVACC : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_ENVACC n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_ENVACC_err : forall n pc' cs rs msg,
    abs_rel cs rs ->
    handle_ENVACC n pc' rs = Error msg ->
    c_error cs.

  Axiom verify_PUSHENVACC : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_PUSHENVACC n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_PUSHENVACC_err : forall n pc' cs rs msg,
    abs_rel cs rs ->
    handle_PUSHENVACC n pc' rs = Error msg ->
    c_error cs.

  (* ================================================================== *)
  (* Function application                                                *)
  (* ================================================================== *)

  Axiom verify_PUSH_RETADDR : forall ret_addr pc' cs rs rs',
    abs_rel cs rs ->
    handle_PUSH_RETADDR ret_addr pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_APPLY : forall n cs rs rs',
    abs_rel cs rs ->
    handle_APPLY n rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_APPLY_err : forall n cs rs msg,
    abs_rel cs rs ->
    handle_APPLY n rs = Error msg ->
    c_error cs.

  Axiom verify_APPLY1 : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_APPLY1 pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_APPLY1_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_APPLY1 pc' rs = Error msg ->
    c_error cs.

  Axiom verify_APPLY2 : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_APPLY2 pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_APPLY2_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_APPLY2 pc' rs = Error msg ->
    c_error cs.

  Axiom verify_APPLY3 : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_APPLY3 pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_APPLY3_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_APPLY3 pc' rs = Error msg ->
    c_error cs.

  (* ================================================================== *)
  (* Tail application                                                    *)
  (* ================================================================== *)

  Axiom verify_APPTERM : forall nargs slotsize cs rs rs',
    abs_rel cs rs ->
    handle_APPTERM nargs slotsize rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_APPTERM_err : forall nargs slotsize cs rs msg,
    abs_rel cs rs ->
    handle_APPTERM nargs slotsize rs = Error msg ->
    c_error cs.

  Axiom verify_APPTERM1 : forall slotsize cs rs rs',
    abs_rel cs rs ->
    handle_APPTERM1 slotsize rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_APPTERM1_err : forall slotsize cs rs msg,
    abs_rel cs rs ->
    handle_APPTERM1 slotsize rs = Error msg ->
    c_error cs.

  Axiom verify_APPTERM2 : forall slotsize cs rs rs',
    abs_rel cs rs ->
    handle_APPTERM2 slotsize rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_APPTERM2_err : forall slotsize cs rs msg,
    abs_rel cs rs ->
    handle_APPTERM2 slotsize rs = Error msg ->
    c_error cs.

  Axiom verify_APPTERM3 : forall slotsize cs rs rs',
    abs_rel cs rs ->
    handle_APPTERM3 slotsize rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_APPTERM3_err : forall slotsize cs rs msg,
    abs_rel cs rs ->
    handle_APPTERM3 slotsize rs = Error msg ->
    c_error cs.

  (* ================================================================== *)
  (* Return, restart, grab                                               *)
  (* ================================================================== *)

  Axiom verify_RETURN : forall stacksize cs rs rs',
    abs_rel cs rs ->
    handle_RETURN stacksize rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_RETURN_err : forall stacksize cs rs msg,
    abs_rel cs rs ->
    handle_RETURN stacksize rs = Error msg ->
    c_error cs.

  Axiom verify_RESTART : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_RESTART pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_RESTART_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_RESTART pc' rs = Error msg ->
    c_error cs.

  Axiom verify_GRAB : forall required pc' cs rs rs',
    abs_rel cs rs ->
    handle_GRAB required pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_GRAB_err : forall required pc' cs rs msg,
    abs_rel cs rs ->
    handle_GRAB required pc' rs = Error msg ->
    c_error cs.

  (* ================================================================== *)
  (* Closures                                                            *)
  (* ================================================================== *)

  Axiom verify_CLOSURE : forall nvars code_ofs pc' cs rs rs',
    abs_rel cs rs ->
    handle_CLOSURE nvars code_ofs pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_CLOSUREREC : forall nfuncs nvars code_offsets pc' cs rs rs',
    abs_rel cs rs ->
    handle_CLOSUREREC nfuncs nvars code_offsets pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_CLOSUREREC_err : forall nfuncs nvars code_offsets pc' cs rs msg,
    abs_rel cs rs ->
    handle_CLOSUREREC nfuncs nvars code_offsets pc' rs = Error msg ->
    c_error cs.

  Axiom verify_OFFSETCLOSURE : forall ofs pc' cs rs rs',
    abs_rel cs rs ->
    handle_OFFSETCLOSURE ofs pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_OFFSETCLOSURE_err : forall ofs pc' cs rs msg,
    abs_rel cs rs ->
    handle_OFFSETCLOSURE ofs pc' rs = Error msg ->
    c_error cs.

  Axiom verify_PUSHOFFSETCLOSURE : forall ofs pc' cs rs rs',
    abs_rel cs rs ->
    handle_PUSHOFFSETCLOSURE ofs pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_PUSHOFFSETCLOSURE_err : forall ofs pc' cs rs msg,
    abs_rel cs rs ->
    handle_PUSHOFFSETCLOSURE ofs pc' rs = Error msg ->
    c_error cs.

  (* ================================================================== *)
  (* Global access                                                       *)
  (* ================================================================== *)

  Axiom verify_GETGLOBAL : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_GETGLOBAL n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_GETGLOBAL_err : forall n pc' cs rs msg,
    abs_rel cs rs ->
    handle_GETGLOBAL n pc' rs = Error msg ->
    c_error cs.

  Axiom verify_PUSHGETGLOBAL : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_PUSHGETGLOBAL n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_PUSHGETGLOBAL_err : forall n pc' cs rs msg,
    abs_rel cs rs ->
    handle_PUSHGETGLOBAL n pc' rs = Error msg ->
    c_error cs.

  Axiom verify_GETGLOBALFIELD : forall n p pc' cs rs rs',
    abs_rel cs rs ->
    handle_GETGLOBALFIELD n p pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_GETGLOBALFIELD_err : forall n p pc' cs rs msg,
    abs_rel cs rs ->
    handle_GETGLOBALFIELD n p pc' rs = Error msg ->
    c_error cs.

  Axiom verify_PUSHGETGLOBALFIELD : forall n p pc' cs rs rs',
    abs_rel cs rs ->
    handle_PUSHGETGLOBALFIELD n p pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_PUSHGETGLOBALFIELD_err : forall n p pc' cs rs msg,
    abs_rel cs rs ->
    handle_PUSHGETGLOBALFIELD n p pc' rs = Error msg ->
    c_error cs.

  Axiom verify_SETGLOBAL : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_SETGLOBAL n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  (* ================================================================== *)
  (* Allocation: atoms and blocks                                        *)
  (* ================================================================== *)

  Axiom verify_ATOM : forall t pc' cs rs rs',
    abs_rel cs rs ->
    handle_ATOM t pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_PUSHATOM : forall t pc' cs rs rs',
    abs_rel cs rs ->
    handle_PUSHATOM t pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_MAKEBLOCK : forall t size pc' cs rs rs',
    abs_rel cs rs ->
    handle_MAKEBLOCK t size pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_MAKEBLOCK1 : forall t pc' cs rs rs',
    abs_rel cs rs ->
    handle_MAKEBLOCK1 t pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_MAKEBLOCK2 : forall t pc' cs rs rs',
    abs_rel cs rs ->
    handle_MAKEBLOCK2 t pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_MAKEBLOCK2_err : forall t pc' cs rs msg,
    abs_rel cs rs ->
    handle_MAKEBLOCK2 t pc' rs = Error msg ->
    c_error cs.

  Axiom verify_MAKEBLOCK3 : forall t pc' cs rs rs',
    abs_rel cs rs ->
    handle_MAKEBLOCK3 t pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_MAKEBLOCK3_err : forall t pc' cs rs msg,
    abs_rel cs rs ->
    handle_MAKEBLOCK3 t pc' rs = Error msg ->
    c_error cs.

  Axiom verify_MAKEFLOATBLOCK : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_MAKEFLOATBLOCK n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  (* ================================================================== *)
  (* Field access                                                        *)
  (* ================================================================== *)

  Axiom verify_GETFIELD : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_GETFIELD n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_GETFIELD_err : forall n pc' cs rs msg,
    abs_rel cs rs ->
    handle_GETFIELD n pc' rs = Error msg ->
    c_error cs.

  Axiom verify_GETFLOATFIELD : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_GETFLOATFIELD n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_GETFLOATFIELD_err : forall n pc' cs rs msg,
    abs_rel cs rs ->
    handle_GETFLOATFIELD n pc' rs = Error msg ->
    c_error cs.

  Axiom verify_SETFIELD : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_SETFIELD n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_SETFIELD_err : forall n pc' cs rs msg,
    abs_rel cs rs ->
    handle_SETFIELD n pc' rs = Error msg ->
    c_error cs.

  Axiom verify_SETFLOATFIELD : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_SETFLOATFIELD n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_SETFLOATFIELD_err : forall n pc' cs rs msg,
    abs_rel cs rs ->
    handle_SETFLOATFIELD n pc' rs = Error msg ->
    c_error cs.

  (* ================================================================== *)
  (* Vector and string/bytes operations                                  *)
  (* ================================================================== *)

  Axiom verify_VECTLENGTH : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_VECTLENGTH pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_VECTLENGTH_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_VECTLENGTH pc' rs = Error msg ->
    c_error cs.

  Axiom verify_GETVECTITEM : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_GETVECTITEM pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_GETVECTITEM_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_GETVECTITEM pc' rs = Error msg ->
    c_error cs.

  Axiom verify_SETVECTITEM : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_SETVECTITEM pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_SETVECTITEM_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_SETVECTITEM pc' rs = Error msg ->
    c_error cs.

  Axiom verify_GETSTRINGCHAR : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_GETSTRINGCHAR pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_GETSTRINGCHAR_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_GETSTRINGCHAR pc' rs = Error msg ->
    c_error cs.

  Axiom verify_SETBYTESCHAR : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_SETBYTESCHAR pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_SETBYTESCHAR_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_SETBYTESCHAR pc' rs = Error msg ->
    c_error cs.

  (* ================================================================== *)
  (* Branches                                                            *)
  (* ================================================================== *)

  Axiom verify_BRANCH : forall target cs rs rs',
    abs_rel cs rs ->
    handle_BRANCH target rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_BRANCHIF : forall target pc' cs rs rs',
    abs_rel cs rs ->
    handle_BRANCHIF target pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_BRANCHIFNOT : forall target pc' cs rs rs',
    abs_rel cs rs ->
    handle_BRANCHIFNOT target pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_SWITCH : forall nc nb const_targets block_targets cs rs rs',
    abs_rel cs rs ->
    handle_SWITCH nc nb const_targets block_targets rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_SWITCH_err : forall nc nb const_targets block_targets cs rs msg,
    abs_rel cs rs ->
    handle_SWITCH nc nb const_targets block_targets rs = Error msg ->
    c_error cs.

  Axiom verify_BOOLNOT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_BOOLNOT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  (* ================================================================== *)
  (* Exception handling                                                  *)
  (* ================================================================== *)

  Axiom verify_PUSHTRAP : forall handler_pc pc' cs rs rs',
    abs_rel cs rs ->
    handle_PUSHTRAP handler_pc pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_POPTRAP : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_POPTRAP pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_POPTRAP_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_POPTRAP pc' rs = Error msg ->
    c_error cs.

  Axiom verify_RAISE : forall exn cs rs rs',
    abs_rel cs rs ->
    do_raise exn rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_RAISE_err : forall exn cs rs msg,
    abs_rel cs rs ->
    do_raise exn rs = Error msg ->
    c_error cs.

  (* ================================================================== *)
  (* Signals and C calls                                                 *)
  (* ================================================================== *)

  Axiom verify_CHECK_SIGNALS : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_CHECK_SIGNALS pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_C_CALL : forall nargs prim_idx pc' cs rs cont args,
    abs_rel cs rs ->
    handle_C_CALL nargs prim_idx pc' rs = CCall_request prim_idx args cont ->
    exists cs', c_ccall cs prim_idx args cs'.

  (* ================================================================== *)
  (* Integer constants                                                   *)
  (* ================================================================== *)

  Axiom verify_CONSTINT : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_CONSTINT n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_PUSHCONSTINT : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_PUSHCONSTINT n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  (* ================================================================== *)
  (* Arithmetic                                                          *)
  (* ================================================================== *)

  Axiom verify_NEGINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_NEGINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_NEGINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_NEGINT pc' rs = Error msg ->
    c_error cs.

  Axiom verify_ADDINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_ADDINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_ADDINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_ADDINT pc' rs = Error msg ->
    c_error cs.

  Axiom verify_SUBINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_SUBINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_SUBINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_SUBINT pc' rs = Error msg ->
    c_error cs.

  Axiom verify_MULINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_MULINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_MULINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_MULINT pc' rs = Error msg ->
    c_error cs.

  Axiom verify_DIVINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_DIVINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_DIVINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_DIVINT pc' rs = Error msg ->
    c_error cs.

  Axiom verify_MODINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_MODINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_MODINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_MODINT pc' rs = Error msg ->
    c_error cs.

  (* ================================================================== *)
  (* Bitwise operations                                                  *)
  (* ================================================================== *)

  Axiom verify_ANDINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_ANDINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_ANDINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_ANDINT pc' rs = Error msg ->
    c_error cs.

  Axiom verify_ORINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_ORINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_ORINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_ORINT pc' rs = Error msg ->
    c_error cs.

  Axiom verify_XORINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_XORINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_XORINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_XORINT pc' rs = Error msg ->
    c_error cs.

  Axiom verify_LSLINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_LSLINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_LSLINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_LSLINT pc' rs = Error msg ->
    c_error cs.

  Axiom verify_LSRINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_LSRINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_LSRINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_LSRINT pc' rs = Error msg ->
    c_error cs.

  Axiom verify_ASRINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_ASRINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_ASRINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_ASRINT pc' rs = Error msg ->
    c_error cs.

  (* ================================================================== *)
  (* Comparison                                                          *)
  (* ================================================================== *)

  Axiom verify_EQ : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_EQ pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_EQ_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_EQ pc' rs = Error msg ->
    c_error cs.

  Axiom verify_NEQ : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_NEQ pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_NEQ_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_NEQ pc' rs = Error msg ->
    c_error cs.

  Axiom verify_LTINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_LTINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_LTINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_LTINT pc' rs = Error msg ->
    c_error cs.

  Axiom verify_LEINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_LEINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_LEINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_LEINT pc' rs = Error msg ->
    c_error cs.

  Axiom verify_GTINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_GTINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_GTINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_GTINT pc' rs = Error msg ->
    c_error cs.

  Axiom verify_GEINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_GEINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_GEINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_GEINT pc' rs = Error msg ->
    c_error cs.

  (* ================================================================== *)
  (* Integer offset and misc                                             *)
  (* ================================================================== *)

  Axiom verify_OFFSETINT : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_OFFSETINT n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_OFFSETINT_err : forall n pc' cs rs msg,
    abs_rel cs rs ->
    handle_OFFSETINT n pc' rs = Error msg ->
    c_error cs.

  Axiom verify_OFFSETREF : forall n pc' cs rs rs',
    abs_rel cs rs ->
    handle_OFFSETREF n pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_OFFSETREF_err : forall n pc' cs rs msg,
    abs_rel cs rs ->
    handle_OFFSETREF n pc' rs = Error msg ->
    c_error cs.

  Axiom verify_ISINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_ISINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  (* ================================================================== *)
  (* Object-oriented operations                                          *)
  (* ================================================================== *)

  Axiom verify_GETMETHOD : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_GETMETHOD pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_GETMETHOD_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_GETMETHOD pc' rs = Error msg ->
    c_error cs.

  Axiom verify_GETPUBMET : forall tag pc' cs rs rs',
    abs_rel cs rs ->
    handle_GETPUBMET tag pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_GETPUBMET_err : forall tag pc' cs rs msg,
    abs_rel cs rs ->
    handle_GETPUBMET tag pc' rs = Error msg ->
    c_error cs.

  Axiom verify_GETDYNMET : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_GETDYNMET pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_GETDYNMET_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_GETDYNMET pc' rs = Error msg ->
    c_error cs.

  (* ================================================================== *)
  (* Conditional branches (B-comparison instructions)                    *)
  (* ================================================================== *)

  Axiom verify_BEQ : forall n target pc' cs rs rs',
    abs_rel cs rs ->
    handle_BEQ n target pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_BNEQ : forall n target pc' cs rs rs',
    abs_rel cs rs ->
    handle_BNEQ n target pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_BLTINT : forall n target pc' cs rs rs',
    abs_rel cs rs ->
    handle_BLTINT n target pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_BLTINT_err : forall n target pc' cs rs msg,
    abs_rel cs rs ->
    handle_BLTINT n target pc' rs = Error msg ->
    c_error cs.

  Axiom verify_BLEINT : forall n target pc' cs rs rs',
    abs_rel cs rs ->
    handle_BLEINT n target pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_BLEINT_err : forall n target pc' cs rs msg,
    abs_rel cs rs ->
    handle_BLEINT n target pc' rs = Error msg ->
    c_error cs.

  Axiom verify_BGTINT : forall n target pc' cs rs rs',
    abs_rel cs rs ->
    handle_BGTINT n target pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_BGTINT_err : forall n target pc' cs rs msg,
    abs_rel cs rs ->
    handle_BGTINT n target pc' rs = Error msg ->
    c_error cs.

  Axiom verify_BGEINT : forall n target pc' cs rs rs',
    abs_rel cs rs ->
    handle_BGEINT n target pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_BGEINT_err : forall n target pc' cs rs msg,
    abs_rel cs rs ->
    handle_BGEINT n target pc' rs = Error msg ->
    c_error cs.

  (* ================================================================== *)
  (* Unsigned comparison                                                 *)
  (* ================================================================== *)

  Axiom verify_ULTINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_ULTINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_ULTINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_ULTINT pc' rs = Error msg ->
    c_error cs.

  Axiom verify_UGEINT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_UGEINT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_UGEINT_err : forall pc' cs rs msg,
    abs_rel cs rs ->
    handle_UGEINT pc' rs = Error msg ->
    c_error cs.

  Axiom verify_BULTINT : forall n target pc' cs rs rs',
    abs_rel cs rs ->
    handle_BULTINT n target pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_BULTINT_err : forall n target pc' cs rs msg,
    abs_rel cs rs ->
    handle_BULTINT n target pc' rs = Error msg ->
    c_error cs.

  Axiom verify_BUGEINT : forall n target pc' cs rs rs',
    abs_rel cs rs ->
    handle_BUGEINT n target pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_BUGEINT_err : forall n target pc' cs rs msg,
    abs_rel cs rs ->
    handle_BUGEINT n target pc' rs = Error msg ->
    c_error cs.

  (* ================================================================== *)
  (* Halt and debug                                                      *)
  (* ================================================================== *)

  Axiom verify_STOP : forall cs rs v,
    abs_rel cs rs ->
    handle_STOP rs = Halt v ->
    c_halt cs v.

  Axiom verify_EVENT : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_EVENT pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

  Axiom verify_BREAK : forall pc' cs rs rs',
    abs_rel cs rs ->
    handle_BREAK pc' rs = Step rs' ->
    exists cs', abs_rel cs' rs'.

End InstructSpec.
