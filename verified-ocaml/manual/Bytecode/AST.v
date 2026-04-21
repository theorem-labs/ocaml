(* Bytecode.v - [TRUSTED] OCaml bytecode instruction set.
   One-to-one with opcodes.h. Specialized variants folded into general forms. *)

From Stdlib Require Import ZArith List.
Import ListNotations.

Inductive instruction : Type :=
  | ACC    : nat -> instruction
  | PUSH   : instruction
  | PUSHACC : nat -> instruction
  | POP    : nat -> instruction
  | ASSIGN : nat -> instruction
  | ENVACC     : nat -> instruction
  | PUSHENVACC : nat -> instruction
  | PUSH_RETADDR : Z -> instruction
  | APPLY  : nat -> instruction
  | APPLY1 : instruction
  | APPLY2 : instruction
  | APPLY3 : instruction
  | APPTERM  : nat -> nat -> instruction
  | APPTERM1 : nat -> instruction
  | APPTERM2 : nat -> instruction
  | APPTERM3 : nat -> instruction
  | RETURN : nat -> instruction
  | RESTART : instruction
  | GRAB   : nat -> instruction
  | CLOSURE     : nat -> Z -> instruction
  | CLOSUREREC  : nat -> nat -> list Z -> instruction
  | OFFSETCLOSURE : Z -> instruction
  | PUSHOFFSETCLOSURE : Z -> instruction
  | GETGLOBAL      : nat -> instruction
  | PUSHGETGLOBAL  : nat -> instruction
  | GETGLOBALFIELD : nat -> nat -> instruction
  | PUSHGETGLOBALFIELD : nat -> nat -> instruction
  | SETGLOBAL      : nat -> instruction
  | ATOM     : nat -> instruction
  | PUSHATOM : nat -> instruction
  | MAKEBLOCK  : nat -> nat -> instruction
  | MAKEBLOCK1 : nat -> instruction
  | MAKEBLOCK2 : nat -> instruction
  | MAKEBLOCK3 : nat -> instruction
  | MAKEFLOATBLOCK : nat -> instruction
  | GETFIELD  : nat -> instruction
  | GETFLOATFIELD : nat -> instruction
  | SETFIELD  : nat -> instruction
  | SETFLOATFIELD : nat -> instruction
  | VECTLENGTH  : instruction
  | GETVECTITEM : instruction
  | SETVECTITEM : instruction
  | GETBYTESCHAR : instruction
  | SETBYTESCHAR : instruction
  | GETSTRINGCHAR : instruction
  | BRANCH      : Z -> instruction
  | BRANCHIF    : Z -> instruction
  | BRANCHIFNOT : Z -> instruction
  | SWITCH      : nat -> nat -> list Z -> list Z -> instruction
  | BOOLNOT     : instruction
  | PUSHTRAP  : Z -> instruction
  | POPTRAP   : instruction
  | RAISE     : instruction
  | RERAISE   : instruction
  | RAISE_NOTRACE : instruction
  | CHECK_SIGNALS : instruction
  | C_CALL : nat -> nat -> instruction
  | CONSTINT     : Z -> instruction
  | PUSHCONSTINT : Z -> instruction
  | NEGINT  : instruction
  | ADDINT  : instruction
  | SUBINT  : instruction
  | MULINT  : instruction
  | DIVINT  : instruction
  | MODINT  : instruction
  | ANDINT  : instruction
  | ORINT   : instruction
  | XORINT  : instruction
  | LSLINT  : instruction
  | LSRINT  : instruction
  | ASRINT  : instruction
  | EQ     : instruction
  | NEQ    : instruction
  | LTINT  : instruction
  | LEINT  : instruction
  | GTINT  : instruction
  | GEINT  : instruction
  | OFFSETINT : Z -> instruction
  | OFFSETREF : Z -> instruction
  | ISINT     : instruction
  | GETMETHOD  : instruction
  | GETPUBMET  : Z -> instruction
  | GETDYNMET  : instruction
  | BEQ    : Z -> Z -> instruction
  | BNEQ   : Z -> Z -> instruction
  | BLTINT : Z -> Z -> instruction
  | BLEINT : Z -> Z -> instruction
  | BGTINT : Z -> Z -> instruction
  | BGEINT : Z -> Z -> instruction
  | ULTINT : instruction
  | UGEINT : instruction
  | BULTINT : Z -> Z -> instruction
  | BUGEINT : Z -> Z -> instruction
  | STOP   : instruction.
