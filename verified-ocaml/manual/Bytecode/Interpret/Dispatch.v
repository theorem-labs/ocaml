(* Dispatch.v - [TRUSTED] Concrete per-instruction dispatcher.  Ascribed to
   HandleInstrSpec inside checker/Bytecode/InterpretChecker.v.  Currently
   lives in manual/ because InstructSpec.v references each handle_<OP> by
   name as a Module Type Parameter; a future refactor can move this (and
   Handlers.v) into automatic/ once InstructSpec is restructured. *)

From Stdlib Require Import ZArith.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import Handlers.
Open Scope Z_scope.

Definition handle_instr (instr : instruction) (pc' : Z) (s : state) : step_result :=
  match instr with

  | ACC n => handle_ACC n pc' s
  | PUSH => handle_PUSH pc' s
  | PUSHACC n => handle_PUSHACC n pc' s
  | POP n => handle_POP n pc' s
  | ASSIGN n => handle_ASSIGN n pc' s
  | ENVACC n => handle_ENVACC n pc' s
  | PUSHENVACC n => handle_PUSHENVACC n pc' s
  | PUSH_RETADDR ret_addr => handle_PUSH_RETADDR ret_addr pc' s
  | APPLY n => handle_APPLY n s
  | APPLY1 => handle_APPLY1 pc' s
  | APPLY2 => handle_APPLY2 pc' s
  | APPLY3 => handle_APPLY3 pc' s
  | APPTERM nargs slotsize => handle_APPTERM nargs slotsize s
  | APPTERM1 slotsize => handle_APPTERM1 slotsize s
  | APPTERM2 slotsize => handle_APPTERM2 slotsize s
  | APPTERM3 slotsize => handle_APPTERM3 slotsize s
  | RETURN stacksize => handle_RETURN stacksize s
  | RESTART => handle_RESTART pc' s
  | GRAB required => handle_GRAB required pc' s
  | CLOSURE nvars code_ofs => handle_CLOSURE nvars code_ofs pc' s
  | CLOSUREREC nfuncs nvars code_offsets => handle_CLOSUREREC nfuncs nvars code_offsets pc' s
  | OFFSETCLOSURE ofs => handle_OFFSETCLOSURE ofs pc' s
  | PUSHOFFSETCLOSURE ofs => handle_PUSHOFFSETCLOSURE ofs pc' s
  | GETGLOBAL n => handle_GETGLOBAL n pc' s
  | PUSHGETGLOBAL n => handle_PUSHGETGLOBAL n pc' s
  | GETGLOBALFIELD n p => handle_GETGLOBALFIELD n p pc' s
  | PUSHGETGLOBALFIELD n p => handle_PUSHGETGLOBALFIELD n p pc' s
  | SETGLOBAL n => handle_SETGLOBAL n pc' s
  | ATOM t => handle_ATOM t pc' s
  | PUSHATOM t => handle_PUSHATOM t pc' s
  | MAKEBLOCK t size => handle_MAKEBLOCK t size pc' s
  | MAKEBLOCK1 t => handle_MAKEBLOCK1 t pc' s
  | MAKEBLOCK2 t => handle_MAKEBLOCK2 t pc' s
  | MAKEBLOCK3 t => handle_MAKEBLOCK3 t pc' s
  | MAKEFLOATBLOCK n => handle_MAKEFLOATBLOCK n pc' s
  | GETFIELD n => handle_GETFIELD n pc' s
  | GETFLOATFIELD n => handle_GETFLOATFIELD n pc' s
  | SETFIELD n => handle_SETFIELD n pc' s
  | SETFLOATFIELD n => handle_SETFLOATFIELD n pc' s
  | VECTLENGTH => handle_VECTLENGTH pc' s
  | GETVECTITEM => handle_GETVECTITEM pc' s
  | SETVECTITEM => handle_SETVECTITEM pc' s
  | GETBYTESCHAR | GETSTRINGCHAR => handle_GETSTRINGCHAR pc' s
  | SETBYTESCHAR => handle_SETBYTESCHAR pc' s
  | BRANCH target => handle_BRANCH target s
  | BRANCHIF target => handle_BRANCHIF target pc' s
  | BRANCHIFNOT target => handle_BRANCHIFNOT target pc' s
  | SWITCH _nc _nb const_targets block_targets => handle_SWITCH _nc _nb const_targets block_targets s
  | BOOLNOT => handle_BOOLNOT pc' s
  | PUSHTRAP handler_pc => handle_PUSHTRAP handler_pc pc' s
  | POPTRAP => handle_POPTRAP pc' s
  | RAISE | RERAISE | RAISE_NOTRACE => do_raise s.(accu) s
  | CHECK_SIGNALS => handle_CHECK_SIGNALS pc' s
  | C_CALL nargs prim_idx => handle_C_CALL nargs prim_idx pc' s
  | CONSTINT n => handle_CONSTINT n pc' s
  | PUSHCONSTINT n => handle_PUSHCONSTINT n pc' s
  | NEGINT => handle_NEGINT pc' s
  | ADDINT => handle_ADDINT pc' s
  | SUBINT => handle_SUBINT pc' s
  | MULINT => handle_MULINT pc' s
  | DIVINT => handle_DIVINT pc' s
  | MODINT => handle_MODINT pc' s
  | ANDINT => handle_ANDINT pc' s
  | ORINT => handle_ORINT pc' s
  | XORINT => handle_XORINT pc' s
  | LSLINT => handle_LSLINT pc' s
  | LSRINT => handle_LSRINT pc' s
  | ASRINT => handle_ASRINT pc' s
  | EQ => handle_EQ pc' s
  | NEQ => handle_NEQ pc' s
  | LTINT => handle_LTINT pc' s
  | LEINT => handle_LEINT pc' s
  | GTINT => handle_GTINT pc' s
  | GEINT => handle_GEINT pc' s
  | OFFSETINT n => handle_OFFSETINT n pc' s
  | OFFSETREF n => handle_OFFSETREF n pc' s
  | ISINT => handle_ISINT pc' s
  | GETMETHOD => handle_GETMETHOD pc' s
  | GETPUBMET tag => handle_GETPUBMET tag pc' s
  | GETDYNMET => handle_GETDYNMET pc' s
  | BEQ n target => handle_BEQ n target pc' s
  | BNEQ n target => handle_BNEQ n target pc' s
  | BLTINT n target => handle_BLTINT n target pc' s
  | BLEINT n target => handle_BLEINT n target pc' s
  | BGTINT n target => handle_BGTINT n target pc' s
  | BGEINT n target => handle_BGEINT n target pc' s
  | ULTINT => handle_ULTINT pc' s
  | UGEINT => handle_UGEINT pc' s
  | BULTINT n target => handle_BULTINT n target pc' s
  | BUGEINT n target => handle_BUGEINT n target pc' s
  | STOP => handle_STOP s
  | EVENT => handle_EVENT pc' s
  | BREAK => handle_BREAK pc' s
  | PERFORM => handle_PERFORM pc' s
  | RESUME => handle_RESUME pc' s
  | RESUMETERM _ => handle_RESUMETERM pc' s
  | REPERFORMTERM _ => handle_REPERFORMTERM pc' s

  end.
