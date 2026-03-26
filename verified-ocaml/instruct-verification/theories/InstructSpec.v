(* InstructSpec.v — Specification relating Clight instruction handlers
   (from clightgen) to Rocq handle_X functions (from Interpret.v).

   For each instruction X with an extracted C handler f_instr_X, we state:
     "Executing the Clight function body of f_instr_X on a C state
      that abstracts Rocq state s produces a C state that abstracts
      handle_X ... s."

   The Clight functions come from instruct_handlers.v (clightgen output).
   The Rocq handlers come from Interpret.v.
   All theorems are Admitted — they are proof obligations for Phase 1+. *)

From Stdlib Require Import ZArith List Strings.String.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Events.
From compcert Require Import ClightBigstep.
From compcert Require AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
Require Import instruct_handlers.

(* ================================================================== *)
(* Setup                                                               *)
(* ================================================================== *)

Definition clight_ge : Clight.genv :=
  {| genv_genv := Globalenvs.Genv.globalenv prog;
     genv_cenv := prog_comp_env prog |}.

(* Abstraction: (Clight env, temp_env, mem) represents a Rocq state. *)
Parameter abs_rel : Clight.env -> temp_env -> mem -> Machine.state -> Prop.

(* Shorthand for the exec_stmt used throughout. *)
Local Notation exec := (exec_stmt function_entry1 clight_ge).

(* ================================================================== *)
(* Stack operations                                                    *)
(* ================================================================== *)

Theorem verify_ACC0 : forall e le m le' m' out s,
  abs_rel e le m s ->
  exec e le m f_instr_ACC0.(fn_body) E0 le' m' out ->
  exists s', handle_ACC 0 (s.(pc) + 1) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

Theorem verify_ACC : forall e le m le' m' out s n,
  abs_rel e le m s ->
  exec e le m f_instr_ACC.(fn_body) E0 le' m' out ->
  exists s', handle_ACC n (s.(pc) + 2) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

Theorem verify_PUSH : forall e le m le' m' out s,
  abs_rel e le m s ->
  exec e le m f_instr_PUSH.(fn_body) E0 le' m' out ->
  exists s', handle_PUSH (s.(pc) + 1) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

Theorem verify_POP : forall e le m le' m' out s n,
  abs_rel e le m s ->
  exec e le m f_instr_POP.(fn_body) E0 le' m' out ->
  exists s', handle_POP n (s.(pc) + 2) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

Theorem verify_ASSIGN : forall e le m le' m' out s n,
  abs_rel e le m s ->
  exec e le m f_instr_ASSIGN.(fn_body) E0 le' m' out ->
  exists s', handle_ASSIGN n (s.(pc) + 2) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

(* ================================================================== *)
(* Constants                                                           *)
(* ================================================================== *)

Theorem verify_CONSTINT : forall e le m le' m' out s n,
  abs_rel e le m s ->
  exec e le m f_instr_CONSTINT.(fn_body) E0 le' m' out ->
  exists s', handle_CONSTINT n (s.(pc) + 2) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

Theorem verify_PUSHCONSTINT : forall e le m le' m' out s n,
  abs_rel e le m s ->
  exec e le m f_instr_PUSHCONSTINT.(fn_body) E0 le' m' out ->
  exists s', handle_PUSHCONSTINT n (s.(pc) + 2) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

(* ================================================================== *)
(* Arithmetic (only DIVINT/MODINT extracted; others use macros)        *)
(* ================================================================== *)

Theorem verify_DIVINT : forall e le m le' m' out s,
  abs_rel e le m s ->
  exec e le m f_instr_DIVINT.(fn_body) E0 le' m' out ->
  exists s', handle_DIVINT (s.(pc) + 1) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

Theorem verify_MODINT : forall e le m le' m' out s,
  abs_rel e le m s ->
  exec e le m f_instr_MODINT.(fn_body) E0 le' m' out ->
  exists s', handle_MODINT (s.(pc) + 1) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

(* ================================================================== *)
(* Boolean / misc                                                      *)
(* ================================================================== *)

Theorem verify_BOOLNOT : forall e le m le' m' out s,
  abs_rel e le m s ->
  exec e le m f_instr_BOOLNOT.(fn_body) E0 le' m' out ->
  exists s', handle_BOOLNOT (s.(pc) + 1) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

Theorem verify_ISINT : forall e le m le' m' out s,
  abs_rel e le m s ->
  exec e le m f_instr_ISINT.(fn_body) E0 le' m' out ->
  exists s', handle_ISINT (s.(pc) + 1) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

Theorem verify_OFFSETINT : forall e le m le' m' out s ofs,
  abs_rel e le m s ->
  exec e le m f_instr_OFFSETINT.(fn_body) E0 le' m' out ->
  exists s', handle_OFFSETINT ofs (s.(pc) + 2) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

(* ================================================================== *)
(* Branches                                                            *)
(* ================================================================== *)

Theorem verify_BRANCH : forall e le m le' m' out s target,
  abs_rel e le m s ->
  exec e le m f_instr_BRANCH.(fn_body) E0 le' m' out ->
  exists s', handle_BRANCH target s = Step s' /\ abs_rel e le' m' s'.
Admitted.

Theorem verify_BRANCHIF : forall e le m le' m' out s target,
  abs_rel e le m s ->
  exec e le m f_instr_BRANCHIF.(fn_body) E0 le' m' out ->
  exists s', handle_BRANCHIF target (s.(pc) + 2) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

Theorem verify_BRANCHIFNOT : forall e le m le' m' out s target,
  abs_rel e le m s ->
  exec e le m f_instr_BRANCHIFNOT.(fn_body) E0 le' m' out ->
  exists s', handle_BRANCHIFNOT target (s.(pc) + 2) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

(* ================================================================== *)
(* Blocks                                                              *)
(* ================================================================== *)

Theorem verify_MAKEBLOCK1 : forall e le m le' m' out s t,
  abs_rel e le m s ->
  exec e le m f_instr_MAKEBLOCK1.(fn_body) E0 le' m' out ->
  exists s', handle_MAKEBLOCK1 t (s.(pc) + 2) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

Theorem verify_MAKEBLOCK2 : forall e le m le' m' out s t,
  abs_rel e le m s ->
  exec e le m f_instr_MAKEBLOCK2.(fn_body) E0 le' m' out ->
  exists s', handle_MAKEBLOCK2 t (s.(pc) + 2) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

Theorem verify_MAKEBLOCK3 : forall e le m le' m' out s t,
  abs_rel e le m s ->
  exec e le m f_instr_MAKEBLOCK3.(fn_body) E0 le' m' out ->
  exists s', handle_MAKEBLOCK3 t (s.(pc) + 2) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

(* ================================================================== *)
(* Fields                                                              *)
(* ================================================================== *)

Theorem verify_GETFIELD0 : forall e le m le' m' out s,
  abs_rel e le m s ->
  exec e le m f_instr_GETFIELD0.(fn_body) E0 le' m' out ->
  exists s', handle_GETFIELD 0 (s.(pc) + 1) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

Theorem verify_SETFIELD : forall e le m le' m' out s n,
  abs_rel e le m s ->
  exec e le m f_instr_SETFIELD.(fn_body) E0 le' m' out ->
  exists s', handle_SETFIELD n (s.(pc) + 2) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

(* ================================================================== *)
(* Globals                                                             *)
(* ================================================================== *)

Theorem verify_GETGLOBAL : forall e le m le' m' out s n,
  abs_rel e le m s ->
  exec e le m f_instr_GETGLOBAL.(fn_body) E0 le' m' out ->
  exists s', handle_GETGLOBAL n (s.(pc) + 2) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

Theorem verify_SETGLOBAL : forall e le m le' m' out s n,
  abs_rel e le m s ->
  exec e le m f_instr_SETGLOBAL.(fn_body) E0 le' m' out ->
  exists s', handle_SETGLOBAL n (s.(pc) + 2) s = Step s' /\ abs_rel e le' m' s'.
Admitted.

(* ================================================================== *)
(* Halt                                                                *)
(* ================================================================== *)

Theorem verify_STOP : forall e le m le' m' out s,
  abs_rel e le m s ->
  exec e le m f_instr_STOP.(fn_body) E0 le' m' out ->
  handle_STOP s = Halt s.(accu).
Admitted.

(* ================================================================== *)
(* TODO: Add theorems for remaining 59 extracted handlers.             *)
(* Missing from extraction (use C macros): ADDINT, SUBINT, MULINT,    *)
(* NEGINT, ANDINT, ORINT, XORINT, LSLINT, LSRINT, ASRINT,            *)
(* EQ, NEQ, LTINT, LEINT, GTINT, GEINT, GETFIELD (generic).          *)
(* These need extract_handlers.sh to expand the macros.                *)
(* ================================================================== *)
