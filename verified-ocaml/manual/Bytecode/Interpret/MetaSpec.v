(* MetaSpec.v - [TRUSTED] Module Type stating the uniqueness meta-theorem
   for bytecode instruction handlers.

   The meta-theorem says: any two handlers satisfying the per-instruction
   correctness obligation (packaged by the dispatch functions clight_of,
   pre_of, error_message_of, P_halt_of, P_ccall_of) agree on every input state
   up to error-message strings.

   This file declares the interface only.  Concrete proofs live under
   automatic/Bytecode/MetaSpecVerification/ and are checked by the thin
   checker/Bytecode/MetaSpecChecker.v ascription. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Globalenvs Maps Memory Values.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec.

(* ================================================================== *)
(* Generic error-message equivalence on step_result_gen                *)
(* ================================================================== *)

Inductive em_eq_gen {S : Type} : step_result_gen S -> step_result_gen S -> Prop :=
  | em_Step_gen  : forall s, em_eq_gen (Step s) (Step s)
  | em_Halt_gen  : forall v, em_eq_gen (Halt v) (Halt v)
  | em_CCall_gen : forall n args s',
      em_eq_gen (CCall_request n args s') (CCall_request n args s')
  | em_Error_gen : forall msg msg', em_eq_gen (Error msg) (Error msg').

(* Concrete error-message equivalence on step_result (backward compat). *)

Inductive em_eq : step_result -> step_result -> Prop :=
  | em_Step  : forall s, em_eq (Step s) (Step s)
  | em_Halt  : forall v, em_eq (Halt v) (Halt v)
  | em_CCall : forall n args s',
      em_eq (CCall_request n args s') (CCall_request n args s')
  | em_Error : forall msg msg', em_eq (Error msg) (Error msg').

(* ================================================================== *)
(* Generic MetaSpec                                                    *)
(*                                                                      *)
(* Quantified over abstract state S, witness W, abstraction relation R  *)
(* (with Clight env/le/m arguments) and two hypotheses:                *)
(*   R_total      : forall s, exists e le m w, R e le m s w            *)
(*   R_functional : forall e le m s1 s2 w1 w2,                        *)
(*                    R e le m s1 w1 -> R e le m s2 w2 -> s1 = s2     *)
(* These appear ONLY in the MetaSpec module type, not in the Generic    *)
(* section of InstructSpec.v.                                           *)
(* ================================================================== *)

Module Type MetaSpecGen.

  Parameter handler_unique_mod_errors_gen :
    forall (S : Type) (W : Type) (pc_of_S : S -> Z)
           (R : Clight.env -> temp_env -> mem -> S -> W -> Prop),
      (forall s, exists e le m w, R e le m s w) ->
      (forall e le m s1 s2 w1 w2, R e le m s1 w1 -> R e le m s2 w2 -> s1 = s2) ->
      forall (f : function)
             (h1 h2 : Z -> S -> step_result_gen S)
             (err : S -> option string)
             (step_pre : Clight.env -> mem -> S -> W -> Prop)
              (P_halt : S -> option value)
              (P_ccall : S -> option (nat * list value * S)),
        (forall s e le m w, R e le m s w -> step_pre e m s w) ->
        handler_correct_gen S W pc_of_S R h1 f err step_pre P_halt P_ccall ->
        handler_correct_gen S W pc_of_S R h2 f err step_pre P_halt P_ccall ->
        forall s, em_eq_gen (h1 (pc_of_S s) s) (h2 (pc_of_S s) s).

End MetaSpecGen.

(* ================================================================== *)
(* Concrete MetaSpec (backward compat)                                 *)
(* ================================================================== *)

(* Concrete uniqueness needs the same relation-side hypotheses as the
   generic MetaSpec: totality, functionality, and the fact that the chosen
   step precondition holds for related states. *)
Record handler_unique_hyps (i : instruction) : Prop := {
  hu_abs_rel_total :
    forall s, exists e le m w, abs_rel_with_ard e le m s w;
  hu_abs_rel_functional :
    forall e le m s1 s2 w1 w2,
      abs_rel_with_ard e le m s1 w1 ->
      abs_rel_with_ard e le m s2 w2 ->
      s1 = s2;
  hu_step_pre_holds :
    forall s e le m w,
      abs_rel_with_ard e le m s w -> pre_of i e m s w;
}.

Module Type MetaSpec.

  Parameter handler_unique_mod_errors :
    forall (i : instruction)
           (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps i ->
      handler_correct h1 (clight_of i)
        (error_message_of i) (pre_of i) (P_halt_of i) (P_ccall_of i) ->
      handler_correct h2 (clight_of i)
        (error_message_of i) (pre_of i) (P_halt_of i) (P_ccall_of i) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

End MetaSpec.

(* Fine-grained per-instruction uniqueness specification. *)
Module Type MetaSpecFineGrainedSpec.

  Parameter unique_ACC : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (ACC n) ->
      handler_correct h1 (clight_of (ACC n))
        (error_message_of (ACC n))
        (pre_of (ACC n)) (P_halt_of (ACC n)) (P_ccall_of (ACC n)) ->
      handler_correct h2 (clight_of (ACC n))
        (error_message_of (ACC n))
        (pre_of (ACC n)) (P_halt_of (ACC n)) (P_ccall_of (ACC n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_PUSH :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps PUSH ->
      handler_correct h1 (clight_of PUSH)
        (error_message_of PUSH)
        (pre_of PUSH) (P_halt_of PUSH) (P_ccall_of PUSH) ->
      handler_correct h2 (clight_of PUSH)
        (error_message_of PUSH)
        (pre_of PUSH) (P_halt_of PUSH) (P_ccall_of PUSH) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_PUSHACC : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (PUSHACC n) ->
      handler_correct h1 (clight_of (PUSHACC n))
        (error_message_of (PUSHACC n))
        (pre_of (PUSHACC n)) (P_halt_of (PUSHACC n)) (P_ccall_of (PUSHACC n)) ->
      handler_correct h2 (clight_of (PUSHACC n))
        (error_message_of (PUSHACC n))
        (pre_of (PUSHACC n)) (P_halt_of (PUSHACC n)) (P_ccall_of (PUSHACC n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_POP : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (POP n) ->
      handler_correct h1 (clight_of (POP n))
        (error_message_of (POP n))
        (pre_of (POP n)) (P_halt_of (POP n)) (P_ccall_of (POP n)) ->
      handler_correct h2 (clight_of (POP n))
        (error_message_of (POP n))
        (pre_of (POP n)) (P_halt_of (POP n)) (P_ccall_of (POP n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_ASSIGN : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (ASSIGN n) ->
      handler_correct h1 (clight_of (ASSIGN n))
        (error_message_of (ASSIGN n))
        (pre_of (ASSIGN n)) (P_halt_of (ASSIGN n)) (P_ccall_of (ASSIGN n)) ->
      handler_correct h2 (clight_of (ASSIGN n))
        (error_message_of (ASSIGN n))
        (pre_of (ASSIGN n)) (P_halt_of (ASSIGN n)) (P_ccall_of (ASSIGN n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_ENVACC : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (ENVACC n) ->
      handler_correct h1 (clight_of (ENVACC n))
        (error_message_of (ENVACC n))
        (pre_of (ENVACC n)) (P_halt_of (ENVACC n)) (P_ccall_of (ENVACC n)) ->
      handler_correct h2 (clight_of (ENVACC n))
        (error_message_of (ENVACC n))
        (pre_of (ENVACC n)) (P_halt_of (ENVACC n)) (P_ccall_of (ENVACC n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_PUSHENVACC : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (PUSHENVACC n) ->
      handler_correct h1 (clight_of (PUSHENVACC n))
        (error_message_of (PUSHENVACC n))
        (pre_of (PUSHENVACC n)) (P_halt_of (PUSHENVACC n)) (P_ccall_of (PUSHENVACC n)) ->
      handler_correct h2 (clight_of (PUSHENVACC n))
        (error_message_of (PUSHENVACC n))
        (pre_of (PUSHENVACC n)) (P_halt_of (PUSHENVACC n)) (P_ccall_of (PUSHENVACC n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_PUSH_RETADDR : forall z,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (PUSH_RETADDR z) ->
      handler_correct h1 (clight_of (PUSH_RETADDR z))
        (error_message_of (PUSH_RETADDR z))
        (pre_of (PUSH_RETADDR z)) (P_halt_of (PUSH_RETADDR z)) (P_ccall_of (PUSH_RETADDR z)) ->
      handler_correct h2 (clight_of (PUSH_RETADDR z))
        (error_message_of (PUSH_RETADDR z))
        (pre_of (PUSH_RETADDR z)) (P_halt_of (PUSH_RETADDR z)) (P_ccall_of (PUSH_RETADDR z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_APPLY : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (APPLY n) ->
      handler_correct h1 (clight_of (APPLY n))
        (error_message_of (APPLY n))
        (pre_of (APPLY n)) (P_halt_of (APPLY n)) (P_ccall_of (APPLY n)) ->
      handler_correct h2 (clight_of (APPLY n))
        (error_message_of (APPLY n))
        (pre_of (APPLY n)) (P_halt_of (APPLY n)) (P_ccall_of (APPLY n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_APPLY1 :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps APPLY1 ->
      handler_correct h1 (clight_of APPLY1)
        (error_message_of APPLY1)
        (pre_of APPLY1) (P_halt_of APPLY1) (P_ccall_of APPLY1) ->
      handler_correct h2 (clight_of APPLY1)
        (error_message_of APPLY1)
        (pre_of APPLY1) (P_halt_of APPLY1) (P_ccall_of APPLY1) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_APPLY2 :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps APPLY2 ->
      handler_correct h1 (clight_of APPLY2)
        (error_message_of APPLY2)
        (pre_of APPLY2) (P_halt_of APPLY2) (P_ccall_of APPLY2) ->
      handler_correct h2 (clight_of APPLY2)
        (error_message_of APPLY2)
        (pre_of APPLY2) (P_halt_of APPLY2) (P_ccall_of APPLY2) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_APPLY3 :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps APPLY3 ->
      handler_correct h1 (clight_of APPLY3)
        (error_message_of APPLY3)
        (pre_of APPLY3) (P_halt_of APPLY3) (P_ccall_of APPLY3) ->
      handler_correct h2 (clight_of APPLY3)
        (error_message_of APPLY3)
        (pre_of APPLY3) (P_halt_of APPLY3) (P_ccall_of APPLY3) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_APPTERM : forall nargs slotsize,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (APPTERM nargs slotsize) ->
      handler_correct h1 (clight_of (APPTERM nargs slotsize))
        (error_message_of (APPTERM nargs slotsize))
        (pre_of (APPTERM nargs slotsize)) (P_halt_of (APPTERM nargs slotsize)) (P_ccall_of (APPTERM nargs slotsize)) ->
      handler_correct h2 (clight_of (APPTERM nargs slotsize))
        (error_message_of (APPTERM nargs slotsize))
        (pre_of (APPTERM nargs slotsize)) (P_halt_of (APPTERM nargs slotsize)) (P_ccall_of (APPTERM nargs slotsize)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_APPTERM1 : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (APPTERM1 n) ->
      handler_correct h1 (clight_of (APPTERM1 n))
        (error_message_of (APPTERM1 n))
        (pre_of (APPTERM1 n)) (P_halt_of (APPTERM1 n)) (P_ccall_of (APPTERM1 n)) ->
      handler_correct h2 (clight_of (APPTERM1 n))
        (error_message_of (APPTERM1 n))
        (pre_of (APPTERM1 n)) (P_halt_of (APPTERM1 n)) (P_ccall_of (APPTERM1 n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_APPTERM2 : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (APPTERM2 n) ->
      handler_correct h1 (clight_of (APPTERM2 n))
        (error_message_of (APPTERM2 n))
        (pre_of (APPTERM2 n)) (P_halt_of (APPTERM2 n)) (P_ccall_of (APPTERM2 n)) ->
      handler_correct h2 (clight_of (APPTERM2 n))
        (error_message_of (APPTERM2 n))
        (pre_of (APPTERM2 n)) (P_halt_of (APPTERM2 n)) (P_ccall_of (APPTERM2 n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_APPTERM3 : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (APPTERM3 n) ->
      handler_correct h1 (clight_of (APPTERM3 n))
        (error_message_of (APPTERM3 n))
        (pre_of (APPTERM3 n)) (P_halt_of (APPTERM3 n)) (P_ccall_of (APPTERM3 n)) ->
      handler_correct h2 (clight_of (APPTERM3 n))
        (error_message_of (APPTERM3 n))
        (pre_of (APPTERM3 n)) (P_halt_of (APPTERM3 n)) (P_ccall_of (APPTERM3 n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_RETURN : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (RETURN n) ->
      handler_correct h1 (clight_of (RETURN n))
        (error_message_of (RETURN n))
        (pre_of (RETURN n)) (P_halt_of (RETURN n)) (P_ccall_of (RETURN n)) ->
      handler_correct h2 (clight_of (RETURN n))
        (error_message_of (RETURN n))
        (pre_of (RETURN n)) (P_halt_of (RETURN n)) (P_ccall_of (RETURN n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_RESTART :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps RESTART ->
      handler_correct h1 (clight_of RESTART)
        (error_message_of RESTART)
        (pre_of RESTART) (P_halt_of RESTART) (P_ccall_of RESTART) ->
      handler_correct h2 (clight_of RESTART)
        (error_message_of RESTART)
        (pre_of RESTART) (P_halt_of RESTART) (P_ccall_of RESTART) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_GRAB : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (GRAB n) ->
      handler_correct h1 (clight_of (GRAB n))
        (error_message_of (GRAB n))
        (pre_of (GRAB n)) (P_halt_of (GRAB n)) (P_ccall_of (GRAB n)) ->
      handler_correct h2 (clight_of (GRAB n))
        (error_message_of (GRAB n))
        (pre_of (GRAB n)) (P_halt_of (GRAB n)) (P_ccall_of (GRAB n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_CLOSURE : forall nvars code_ofs,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (CLOSURE nvars code_ofs) ->
      handler_correct h1 (clight_of (CLOSURE nvars code_ofs))
        (error_message_of (CLOSURE nvars code_ofs))
        (pre_of (CLOSURE nvars code_ofs)) (P_halt_of (CLOSURE nvars code_ofs)) (P_ccall_of (CLOSURE nvars code_ofs)) ->
      handler_correct h2 (clight_of (CLOSURE nvars code_ofs))
        (error_message_of (CLOSURE nvars code_ofs))
        (pre_of (CLOSURE nvars code_ofs)) (P_halt_of (CLOSURE nvars code_ofs)) (P_ccall_of (CLOSURE nvars code_ofs)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_CLOSUREREC : forall nfuncs nvars code_offsets,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (CLOSUREREC nfuncs nvars code_offsets) ->
      handler_correct h1 (clight_of (CLOSUREREC nfuncs nvars code_offsets))
        (error_message_of (CLOSUREREC nfuncs nvars code_offsets))
        (pre_of (CLOSUREREC nfuncs nvars code_offsets)) (P_halt_of (CLOSUREREC nfuncs nvars code_offsets)) (P_ccall_of (CLOSUREREC nfuncs nvars code_offsets)) ->
      handler_correct h2 (clight_of (CLOSUREREC nfuncs nvars code_offsets))
        (error_message_of (CLOSUREREC nfuncs nvars code_offsets))
        (pre_of (CLOSUREREC nfuncs nvars code_offsets)) (P_halt_of (CLOSUREREC nfuncs nvars code_offsets)) (P_ccall_of (CLOSUREREC nfuncs nvars code_offsets)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_OFFSETCLOSURE : forall z,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (OFFSETCLOSURE z) ->
      handler_correct h1 (clight_of (OFFSETCLOSURE z))
        (error_message_of (OFFSETCLOSURE z))
        (pre_of (OFFSETCLOSURE z)) (P_halt_of (OFFSETCLOSURE z)) (P_ccall_of (OFFSETCLOSURE z)) ->
      handler_correct h2 (clight_of (OFFSETCLOSURE z))
        (error_message_of (OFFSETCLOSURE z))
        (pre_of (OFFSETCLOSURE z)) (P_halt_of (OFFSETCLOSURE z)) (P_ccall_of (OFFSETCLOSURE z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_PUSHOFFSETCLOSURE : forall z,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (PUSHOFFSETCLOSURE z) ->
      handler_correct h1 (clight_of (PUSHOFFSETCLOSURE z))
        (error_message_of (PUSHOFFSETCLOSURE z))
        (pre_of (PUSHOFFSETCLOSURE z)) (P_halt_of (PUSHOFFSETCLOSURE z)) (P_ccall_of (PUSHOFFSETCLOSURE z)) ->
      handler_correct h2 (clight_of (PUSHOFFSETCLOSURE z))
        (error_message_of (PUSHOFFSETCLOSURE z))
        (pre_of (PUSHOFFSETCLOSURE z)) (P_halt_of (PUSHOFFSETCLOSURE z)) (P_ccall_of (PUSHOFFSETCLOSURE z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_GETGLOBAL : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (GETGLOBAL n) ->
      handler_correct h1 (clight_of (GETGLOBAL n))
        (error_message_of (GETGLOBAL n))
        (pre_of (GETGLOBAL n)) (P_halt_of (GETGLOBAL n)) (P_ccall_of (GETGLOBAL n)) ->
      handler_correct h2 (clight_of (GETGLOBAL n))
        (error_message_of (GETGLOBAL n))
        (pre_of (GETGLOBAL n)) (P_halt_of (GETGLOBAL n)) (P_ccall_of (GETGLOBAL n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_PUSHGETGLOBAL : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (PUSHGETGLOBAL n) ->
      handler_correct h1 (clight_of (PUSHGETGLOBAL n))
        (error_message_of (PUSHGETGLOBAL n))
        (pre_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)) ->
      handler_correct h2 (clight_of (PUSHGETGLOBAL n))
        (error_message_of (PUSHGETGLOBAL n))
        (pre_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_GETGLOBALFIELD : forall n p,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (GETGLOBALFIELD n p) ->
      handler_correct h1 (clight_of (GETGLOBALFIELD n p))
        (error_message_of (GETGLOBALFIELD n p))
        (pre_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)) ->
      handler_correct h2 (clight_of (GETGLOBALFIELD n p))
        (error_message_of (GETGLOBALFIELD n p))
        (pre_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_PUSHGETGLOBALFIELD : forall n p,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (PUSHGETGLOBALFIELD n p) ->
      handler_correct h1 (clight_of (PUSHGETGLOBALFIELD n p))
        (error_message_of (PUSHGETGLOBALFIELD n p))
        (pre_of (PUSHGETGLOBALFIELD n p)) (P_halt_of (PUSHGETGLOBALFIELD n p)) (P_ccall_of (PUSHGETGLOBALFIELD n p)) ->
      handler_correct h2 (clight_of (PUSHGETGLOBALFIELD n p))
        (error_message_of (PUSHGETGLOBALFIELD n p))
        (pre_of (PUSHGETGLOBALFIELD n p)) (P_halt_of (PUSHGETGLOBALFIELD n p)) (P_ccall_of (PUSHGETGLOBALFIELD n p)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_SETGLOBAL : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (SETGLOBAL n) ->
      handler_correct h1 (clight_of (SETGLOBAL n))
        (error_message_of (SETGLOBAL n))
        (pre_of (SETGLOBAL n)) (P_halt_of (SETGLOBAL n)) (P_ccall_of (SETGLOBAL n)) ->
      handler_correct h2 (clight_of (SETGLOBAL n))
        (error_message_of (SETGLOBAL n))
        (pre_of (SETGLOBAL n)) (P_halt_of (SETGLOBAL n)) (P_ccall_of (SETGLOBAL n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_ATOM : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (ATOM n) ->
      handler_correct h1 (clight_of (ATOM n))
        (error_message_of (ATOM n))
        (pre_of (ATOM n)) (P_halt_of (ATOM n)) (P_ccall_of (ATOM n)) ->
      handler_correct h2 (clight_of (ATOM n))
        (error_message_of (ATOM n))
        (pre_of (ATOM n)) (P_halt_of (ATOM n)) (P_ccall_of (ATOM n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_PUSHATOM : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (PUSHATOM n) ->
      handler_correct h1 (clight_of (PUSHATOM n))
        (error_message_of (PUSHATOM n))
        (pre_of (PUSHATOM n)) (P_halt_of (PUSHATOM n)) (P_ccall_of (PUSHATOM n)) ->
      handler_correct h2 (clight_of (PUSHATOM n))
        (error_message_of (PUSHATOM n))
        (pre_of (PUSHATOM n)) (P_halt_of (PUSHATOM n)) (P_ccall_of (PUSHATOM n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_MAKEBLOCK : forall t size,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (MAKEBLOCK t size) ->
      handler_correct h1 (clight_of (MAKEBLOCK t size))
        (error_message_of (MAKEBLOCK t size))
        (pre_of (MAKEBLOCK t size)) (P_halt_of (MAKEBLOCK t size)) (P_ccall_of (MAKEBLOCK t size)) ->
      handler_correct h2 (clight_of (MAKEBLOCK t size))
        (error_message_of (MAKEBLOCK t size))
        (pre_of (MAKEBLOCK t size)) (P_halt_of (MAKEBLOCK t size)) (P_ccall_of (MAKEBLOCK t size)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_MAKEBLOCK1 : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (MAKEBLOCK1 n) ->
      handler_correct h1 (clight_of (MAKEBLOCK1 n))
        (error_message_of (MAKEBLOCK1 n))
        (pre_of (MAKEBLOCK1 n)) (P_halt_of (MAKEBLOCK1 n)) (P_ccall_of (MAKEBLOCK1 n)) ->
      handler_correct h2 (clight_of (MAKEBLOCK1 n))
        (error_message_of (MAKEBLOCK1 n))
        (pre_of (MAKEBLOCK1 n)) (P_halt_of (MAKEBLOCK1 n)) (P_ccall_of (MAKEBLOCK1 n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_MAKEBLOCK2 : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (MAKEBLOCK2 n) ->
      handler_correct h1 (clight_of (MAKEBLOCK2 n))
        (error_message_of (MAKEBLOCK2 n))
        (pre_of (MAKEBLOCK2 n)) (P_halt_of (MAKEBLOCK2 n)) (P_ccall_of (MAKEBLOCK2 n)) ->
      handler_correct h2 (clight_of (MAKEBLOCK2 n))
        (error_message_of (MAKEBLOCK2 n))
        (pre_of (MAKEBLOCK2 n)) (P_halt_of (MAKEBLOCK2 n)) (P_ccall_of (MAKEBLOCK2 n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_MAKEBLOCK3 : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (MAKEBLOCK3 n) ->
      handler_correct h1 (clight_of (MAKEBLOCK3 n))
        (error_message_of (MAKEBLOCK3 n))
        (pre_of (MAKEBLOCK3 n)) (P_halt_of (MAKEBLOCK3 n)) (P_ccall_of (MAKEBLOCK3 n)) ->
      handler_correct h2 (clight_of (MAKEBLOCK3 n))
        (error_message_of (MAKEBLOCK3 n))
        (pre_of (MAKEBLOCK3 n)) (P_halt_of (MAKEBLOCK3 n)) (P_ccall_of (MAKEBLOCK3 n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_MAKEFLOATBLOCK : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (MAKEFLOATBLOCK n) ->
      handler_correct h1 (clight_of (MAKEFLOATBLOCK n))
        (error_message_of (MAKEFLOATBLOCK n))
        (pre_of (MAKEFLOATBLOCK n)) (P_halt_of (MAKEFLOATBLOCK n)) (P_ccall_of (MAKEFLOATBLOCK n)) ->
      handler_correct h2 (clight_of (MAKEFLOATBLOCK n))
        (error_message_of (MAKEFLOATBLOCK n))
        (pre_of (MAKEFLOATBLOCK n)) (P_halt_of (MAKEFLOATBLOCK n)) (P_ccall_of (MAKEFLOATBLOCK n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_GETFIELD : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (GETFIELD n) ->
      handler_correct h1 (clight_of (GETFIELD n))
        (error_message_of (GETFIELD n))
        (pre_of (GETFIELD n)) (P_halt_of (GETFIELD n)) (P_ccall_of (GETFIELD n)) ->
      handler_correct h2 (clight_of (GETFIELD n))
        (error_message_of (GETFIELD n))
        (pre_of (GETFIELD n)) (P_halt_of (GETFIELD n)) (P_ccall_of (GETFIELD n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_GETFLOATFIELD : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (GETFLOATFIELD n) ->
      handler_correct h1 (clight_of (GETFLOATFIELD n))
        (error_message_of (GETFLOATFIELD n))
        (pre_of (GETFLOATFIELD n)) (P_halt_of (GETFLOATFIELD n)) (P_ccall_of (GETFLOATFIELD n)) ->
      handler_correct h2 (clight_of (GETFLOATFIELD n))
        (error_message_of (GETFLOATFIELD n))
        (pre_of (GETFLOATFIELD n)) (P_halt_of (GETFLOATFIELD n)) (P_ccall_of (GETFLOATFIELD n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_SETFIELD : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (SETFIELD n) ->
      handler_correct h1 (clight_of (SETFIELD n))
        (error_message_of (SETFIELD n))
        (pre_of (SETFIELD n)) (P_halt_of (SETFIELD n)) (P_ccall_of (SETFIELD n)) ->
      handler_correct h2 (clight_of (SETFIELD n))
        (error_message_of (SETFIELD n))
        (pre_of (SETFIELD n)) (P_halt_of (SETFIELD n)) (P_ccall_of (SETFIELD n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_SETFLOATFIELD : forall n,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (SETFLOATFIELD n) ->
      handler_correct h1 (clight_of (SETFLOATFIELD n))
        (error_message_of (SETFLOATFIELD n))
        (pre_of (SETFLOATFIELD n)) (P_halt_of (SETFLOATFIELD n)) (P_ccall_of (SETFLOATFIELD n)) ->
      handler_correct h2 (clight_of (SETFLOATFIELD n))
        (error_message_of (SETFLOATFIELD n))
        (pre_of (SETFLOATFIELD n)) (P_halt_of (SETFLOATFIELD n)) (P_ccall_of (SETFLOATFIELD n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_VECTLENGTH :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps VECTLENGTH ->
      handler_correct h1 (clight_of VECTLENGTH)
        (error_message_of VECTLENGTH)
        (pre_of VECTLENGTH) (P_halt_of VECTLENGTH) (P_ccall_of VECTLENGTH) ->
      handler_correct h2 (clight_of VECTLENGTH)
        (error_message_of VECTLENGTH)
        (pre_of VECTLENGTH) (P_halt_of VECTLENGTH) (P_ccall_of VECTLENGTH) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_GETVECTITEM :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps GETVECTITEM ->
      handler_correct h1 (clight_of GETVECTITEM)
        (error_message_of GETVECTITEM)
        (pre_of GETVECTITEM) (P_halt_of GETVECTITEM) (P_ccall_of GETVECTITEM) ->
      handler_correct h2 (clight_of GETVECTITEM)
        (error_message_of GETVECTITEM)
        (pre_of GETVECTITEM) (P_halt_of GETVECTITEM) (P_ccall_of GETVECTITEM) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_SETVECTITEM :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps SETVECTITEM ->
      handler_correct h1 (clight_of SETVECTITEM)
        (error_message_of SETVECTITEM)
        (pre_of SETVECTITEM) (P_halt_of SETVECTITEM) (P_ccall_of SETVECTITEM) ->
      handler_correct h2 (clight_of SETVECTITEM)
        (error_message_of SETVECTITEM)
        (pre_of SETVECTITEM) (P_halt_of SETVECTITEM) (P_ccall_of SETVECTITEM) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_GETBYTESCHAR :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps GETBYTESCHAR ->
      handler_correct h1 (clight_of GETBYTESCHAR)
        (error_message_of GETBYTESCHAR)
        (pre_of GETBYTESCHAR) (P_halt_of GETBYTESCHAR) (P_ccall_of GETBYTESCHAR) ->
      handler_correct h2 (clight_of GETBYTESCHAR)
        (error_message_of GETBYTESCHAR)
        (pre_of GETBYTESCHAR) (P_halt_of GETBYTESCHAR) (P_ccall_of GETBYTESCHAR) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_SETBYTESCHAR :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps SETBYTESCHAR ->
      handler_correct h1 (clight_of SETBYTESCHAR)
        (error_message_of SETBYTESCHAR)
        (pre_of SETBYTESCHAR) (P_halt_of SETBYTESCHAR) (P_ccall_of SETBYTESCHAR) ->
      handler_correct h2 (clight_of SETBYTESCHAR)
        (error_message_of SETBYTESCHAR)
        (pre_of SETBYTESCHAR) (P_halt_of SETBYTESCHAR) (P_ccall_of SETBYTESCHAR) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_GETSTRINGCHAR :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps GETSTRINGCHAR ->
      handler_correct h1 (clight_of GETSTRINGCHAR)
        (error_message_of GETSTRINGCHAR)
        (pre_of GETSTRINGCHAR) (P_halt_of GETSTRINGCHAR) (P_ccall_of GETSTRINGCHAR) ->
      handler_correct h2 (clight_of GETSTRINGCHAR)
        (error_message_of GETSTRINGCHAR)
        (pre_of GETSTRINGCHAR) (P_halt_of GETSTRINGCHAR) (P_ccall_of GETSTRINGCHAR) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_BRANCH : forall z,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (BRANCH z) ->
      handler_correct h1 (clight_of (BRANCH z))
        (error_message_of (BRANCH z))
        (pre_of (BRANCH z)) (P_halt_of (BRANCH z)) (P_ccall_of (BRANCH z)) ->
      handler_correct h2 (clight_of (BRANCH z))
        (error_message_of (BRANCH z))
        (pre_of (BRANCH z)) (P_halt_of (BRANCH z)) (P_ccall_of (BRANCH z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_BRANCHIF : forall z,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (BRANCHIF z) ->
      handler_correct h1 (clight_of (BRANCHIF z))
        (error_message_of (BRANCHIF z))
        (pre_of (BRANCHIF z)) (P_halt_of (BRANCHIF z)) (P_ccall_of (BRANCHIF z)) ->
      handler_correct h2 (clight_of (BRANCHIF z))
        (error_message_of (BRANCHIF z))
        (pre_of (BRANCHIF z)) (P_halt_of (BRANCHIF z)) (P_ccall_of (BRANCHIF z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_BRANCHIFNOT : forall z,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (BRANCHIFNOT z) ->
      handler_correct h1 (clight_of (BRANCHIFNOT z))
        (error_message_of (BRANCHIFNOT z))
        (pre_of (BRANCHIFNOT z)) (P_halt_of (BRANCHIFNOT z)) (P_ccall_of (BRANCHIFNOT z)) ->
      handler_correct h2 (clight_of (BRANCHIFNOT z))
        (error_message_of (BRANCHIFNOT z))
        (pre_of (BRANCHIFNOT z)) (P_halt_of (BRANCHIFNOT z)) (P_ccall_of (BRANCHIFNOT z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_SWITCH : forall nc nb const_targets block_targets,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (SWITCH nc nb const_targets block_targets) ->
      handler_correct h1 (clight_of (SWITCH nc nb const_targets block_targets))
        (error_message_of (SWITCH nc nb const_targets block_targets))
        (pre_of (SWITCH nc nb const_targets block_targets)) (P_halt_of (SWITCH nc nb const_targets block_targets)) (P_ccall_of (SWITCH nc nb const_targets block_targets)) ->
      handler_correct h2 (clight_of (SWITCH nc nb const_targets block_targets))
        (error_message_of (SWITCH nc nb const_targets block_targets))
        (pre_of (SWITCH nc nb const_targets block_targets)) (P_halt_of (SWITCH nc nb const_targets block_targets)) (P_ccall_of (SWITCH nc nb const_targets block_targets)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_BOOLNOT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps BOOLNOT ->
      handler_correct h1 (clight_of BOOLNOT)
        (error_message_of BOOLNOT)
        (pre_of BOOLNOT) (P_halt_of BOOLNOT) (P_ccall_of BOOLNOT) ->
      handler_correct h2 (clight_of BOOLNOT)
        (error_message_of BOOLNOT)
        (pre_of BOOLNOT) (P_halt_of BOOLNOT) (P_ccall_of BOOLNOT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_PUSHTRAP : forall z,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (PUSHTRAP z) ->
      handler_correct h1 (clight_of (PUSHTRAP z))
        (error_message_of (PUSHTRAP z))
        (pre_of (PUSHTRAP z)) (P_halt_of (PUSHTRAP z)) (P_ccall_of (PUSHTRAP z)) ->
      handler_correct h2 (clight_of (PUSHTRAP z))
        (error_message_of (PUSHTRAP z))
        (pre_of (PUSHTRAP z)) (P_halt_of (PUSHTRAP z)) (P_ccall_of (PUSHTRAP z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_POPTRAP :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps POPTRAP ->
      handler_correct h1 (clight_of POPTRAP)
        (error_message_of POPTRAP)
        (pre_of POPTRAP) (P_halt_of POPTRAP) (P_ccall_of POPTRAP) ->
      handler_correct h2 (clight_of POPTRAP)
        (error_message_of POPTRAP)
        (pre_of POPTRAP) (P_halt_of POPTRAP) (P_ccall_of POPTRAP) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_RAISE :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps RAISE ->
      handler_correct h1 (clight_of RAISE)
        (error_message_of RAISE)
        (pre_of RAISE) (P_halt_of RAISE) (P_ccall_of RAISE) ->
      handler_correct h2 (clight_of RAISE)
        (error_message_of RAISE)
        (pre_of RAISE) (P_halt_of RAISE) (P_ccall_of RAISE) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_RERAISE :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps RERAISE ->
      handler_correct h1 (clight_of RERAISE)
        (error_message_of RERAISE)
        (pre_of RERAISE) (P_halt_of RERAISE) (P_ccall_of RERAISE) ->
      handler_correct h2 (clight_of RERAISE)
        (error_message_of RERAISE)
        (pre_of RERAISE) (P_halt_of RERAISE) (P_ccall_of RERAISE) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_RAISE_NOTRACE :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps RAISE_NOTRACE ->
      handler_correct h1 (clight_of RAISE_NOTRACE)
        (error_message_of RAISE_NOTRACE)
        (pre_of RAISE_NOTRACE) (P_halt_of RAISE_NOTRACE) (P_ccall_of RAISE_NOTRACE) ->
      handler_correct h2 (clight_of RAISE_NOTRACE)
        (error_message_of RAISE_NOTRACE)
        (pre_of RAISE_NOTRACE) (P_halt_of RAISE_NOTRACE) (P_ccall_of RAISE_NOTRACE) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_CHECK_SIGNALS :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps CHECK_SIGNALS ->
      handler_correct h1 (clight_of CHECK_SIGNALS)
        (error_message_of CHECK_SIGNALS)
        (pre_of CHECK_SIGNALS) (P_halt_of CHECK_SIGNALS) (P_ccall_of CHECK_SIGNALS) ->
      handler_correct h2 (clight_of CHECK_SIGNALS)
        (error_message_of CHECK_SIGNALS)
        (pre_of CHECK_SIGNALS) (P_halt_of CHECK_SIGNALS) (P_ccall_of CHECK_SIGNALS) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_C_CALL : forall nargs prim_idx,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (C_CALL nargs prim_idx) ->
      handler_correct h1 (clight_of (C_CALL nargs prim_idx))
        (error_message_of (C_CALL nargs prim_idx))
        (pre_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
      handler_correct h2 (clight_of (C_CALL nargs prim_idx))
        (error_message_of (C_CALL nargs prim_idx))
        (pre_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_CONSTINT : forall z,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (CONSTINT z) ->
      handler_correct h1 (clight_of (CONSTINT z))
        (error_message_of (CONSTINT z))
        (pre_of (CONSTINT z)) (P_halt_of (CONSTINT z)) (P_ccall_of (CONSTINT z)) ->
      handler_correct h2 (clight_of (CONSTINT z))
        (error_message_of (CONSTINT z))
        (pre_of (CONSTINT z)) (P_halt_of (CONSTINT z)) (P_ccall_of (CONSTINT z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_PUSHCONSTINT : forall z,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (PUSHCONSTINT z) ->
      handler_correct h1 (clight_of (PUSHCONSTINT z))
        (error_message_of (PUSHCONSTINT z))
        (pre_of (PUSHCONSTINT z)) (P_halt_of (PUSHCONSTINT z)) (P_ccall_of (PUSHCONSTINT z)) ->
      handler_correct h2 (clight_of (PUSHCONSTINT z))
        (error_message_of (PUSHCONSTINT z))
        (pre_of (PUSHCONSTINT z)) (P_halt_of (PUSHCONSTINT z)) (P_ccall_of (PUSHCONSTINT z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_NEGINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps NEGINT ->
      handler_correct h1 (clight_of NEGINT)
        (error_message_of NEGINT)
        (pre_of NEGINT) (P_halt_of NEGINT) (P_ccall_of NEGINT) ->
      handler_correct h2 (clight_of NEGINT)
        (error_message_of NEGINT)
        (pre_of NEGINT) (P_halt_of NEGINT) (P_ccall_of NEGINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_ADDINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps ADDINT ->
      handler_correct h1 (clight_of ADDINT)
        (error_message_of ADDINT)
        (pre_of ADDINT) (P_halt_of ADDINT) (P_ccall_of ADDINT) ->
      handler_correct h2 (clight_of ADDINT)
        (error_message_of ADDINT)
        (pre_of ADDINT) (P_halt_of ADDINT) (P_ccall_of ADDINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_SUBINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps SUBINT ->
      handler_correct h1 (clight_of SUBINT)
        (error_message_of SUBINT)
        (pre_of SUBINT) (P_halt_of SUBINT) (P_ccall_of SUBINT) ->
      handler_correct h2 (clight_of SUBINT)
        (error_message_of SUBINT)
        (pre_of SUBINT) (P_halt_of SUBINT) (P_ccall_of SUBINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_MULINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps MULINT ->
      handler_correct h1 (clight_of MULINT)
        (error_message_of MULINT)
        (pre_of MULINT) (P_halt_of MULINT) (P_ccall_of MULINT) ->
      handler_correct h2 (clight_of MULINT)
        (error_message_of MULINT)
        (pre_of MULINT) (P_halt_of MULINT) (P_ccall_of MULINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_DIVINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps DIVINT ->
      handler_correct h1 (clight_of DIVINT)
        (error_message_of DIVINT)
        (pre_of DIVINT) (P_halt_of DIVINT) (P_ccall_of DIVINT) ->
      handler_correct h2 (clight_of DIVINT)
        (error_message_of DIVINT)
        (pre_of DIVINT) (P_halt_of DIVINT) (P_ccall_of DIVINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_MODINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps MODINT ->
      handler_correct h1 (clight_of MODINT)
        (error_message_of MODINT)
        (pre_of MODINT) (P_halt_of MODINT) (P_ccall_of MODINT) ->
      handler_correct h2 (clight_of MODINT)
        (error_message_of MODINT)
        (pre_of MODINT) (P_halt_of MODINT) (P_ccall_of MODINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_ANDINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps ANDINT ->
      handler_correct h1 (clight_of ANDINT)
        (error_message_of ANDINT)
        (pre_of ANDINT) (P_halt_of ANDINT) (P_ccall_of ANDINT) ->
      handler_correct h2 (clight_of ANDINT)
        (error_message_of ANDINT)
        (pre_of ANDINT) (P_halt_of ANDINT) (P_ccall_of ANDINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_ORINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps ORINT ->
      handler_correct h1 (clight_of ORINT)
        (error_message_of ORINT)
        (pre_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT) ->
      handler_correct h2 (clight_of ORINT)
        (error_message_of ORINT)
        (pre_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_XORINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps XORINT ->
      handler_correct h1 (clight_of XORINT)
        (error_message_of XORINT)
        (pre_of XORINT) (P_halt_of XORINT) (P_ccall_of XORINT) ->
      handler_correct h2 (clight_of XORINT)
        (error_message_of XORINT)
        (pre_of XORINT) (P_halt_of XORINT) (P_ccall_of XORINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_LSLINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps LSLINT ->
      handler_correct h1 (clight_of LSLINT)
        (error_message_of LSLINT)
        (pre_of LSLINT) (P_halt_of LSLINT) (P_ccall_of LSLINT) ->
      handler_correct h2 (clight_of LSLINT)
        (error_message_of LSLINT)
        (pre_of LSLINT) (P_halt_of LSLINT) (P_ccall_of LSLINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_LSRINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps LSRINT ->
      handler_correct h1 (clight_of LSRINT)
        (error_message_of LSRINT)
        (pre_of LSRINT) (P_halt_of LSRINT) (P_ccall_of LSRINT) ->
      handler_correct h2 (clight_of LSRINT)
        (error_message_of LSRINT)
        (pre_of LSRINT) (P_halt_of LSRINT) (P_ccall_of LSRINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_ASRINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps ASRINT ->
      handler_correct h1 (clight_of ASRINT)
        (error_message_of ASRINT)
        (pre_of ASRINT) (P_halt_of ASRINT) (P_ccall_of ASRINT) ->
      handler_correct h2 (clight_of ASRINT)
        (error_message_of ASRINT)
        (pre_of ASRINT) (P_halt_of ASRINT) (P_ccall_of ASRINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_EQ :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps EQ ->
      handler_correct h1 (clight_of EQ)
        (error_message_of EQ)
        (pre_of EQ) (P_halt_of EQ) (P_ccall_of EQ) ->
      handler_correct h2 (clight_of EQ)
        (error_message_of EQ)
        (pre_of EQ) (P_halt_of EQ) (P_ccall_of EQ) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_NEQ :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps NEQ ->
      handler_correct h1 (clight_of NEQ)
        (error_message_of NEQ)
        (pre_of NEQ) (P_halt_of NEQ) (P_ccall_of NEQ) ->
      handler_correct h2 (clight_of NEQ)
        (error_message_of NEQ)
        (pre_of NEQ) (P_halt_of NEQ) (P_ccall_of NEQ) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_LTINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps LTINT ->
      handler_correct h1 (clight_of LTINT)
        (error_message_of LTINT)
        (pre_of LTINT) (P_halt_of LTINT) (P_ccall_of LTINT) ->
      handler_correct h2 (clight_of LTINT)
        (error_message_of LTINT)
        (pre_of LTINT) (P_halt_of LTINT) (P_ccall_of LTINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_LEINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps LEINT ->
      handler_correct h1 (clight_of LEINT)
        (error_message_of LEINT)
        (pre_of LEINT) (P_halt_of LEINT) (P_ccall_of LEINT) ->
      handler_correct h2 (clight_of LEINT)
        (error_message_of LEINT)
        (pre_of LEINT) (P_halt_of LEINT) (P_ccall_of LEINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_GTINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps GTINT ->
      handler_correct h1 (clight_of GTINT)
        (error_message_of GTINT)
        (pre_of GTINT) (P_halt_of GTINT) (P_ccall_of GTINT) ->
      handler_correct h2 (clight_of GTINT)
        (error_message_of GTINT)
        (pre_of GTINT) (P_halt_of GTINT) (P_ccall_of GTINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_GEINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps GEINT ->
      handler_correct h1 (clight_of GEINT)
        (error_message_of GEINT)
        (pre_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT) ->
      handler_correct h2 (clight_of GEINT)
        (error_message_of GEINT)
        (pre_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_OFFSETINT : forall z,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (OFFSETINT z) ->
      handler_correct h1 (clight_of (OFFSETINT z))
        (error_message_of (OFFSETINT z))
        (pre_of (OFFSETINT z)) (P_halt_of (OFFSETINT z)) (P_ccall_of (OFFSETINT z)) ->
      handler_correct h2 (clight_of (OFFSETINT z))
        (error_message_of (OFFSETINT z))
        (pre_of (OFFSETINT z)) (P_halt_of (OFFSETINT z)) (P_ccall_of (OFFSETINT z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_OFFSETREF : forall z,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (OFFSETREF z) ->
      handler_correct h1 (clight_of (OFFSETREF z))
        (error_message_of (OFFSETREF z))
        (pre_of (OFFSETREF z)) (P_halt_of (OFFSETREF z)) (P_ccall_of (OFFSETREF z)) ->
      handler_correct h2 (clight_of (OFFSETREF z))
        (error_message_of (OFFSETREF z))
        (pre_of (OFFSETREF z)) (P_halt_of (OFFSETREF z)) (P_ccall_of (OFFSETREF z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_ISINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps ISINT ->
      handler_correct h1 (clight_of ISINT)
        (error_message_of ISINT)
        (pre_of ISINT) (P_halt_of ISINT) (P_ccall_of ISINT) ->
      handler_correct h2 (clight_of ISINT)
        (error_message_of ISINT)
        (pre_of ISINT) (P_halt_of ISINT) (P_ccall_of ISINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_GETMETHOD :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps GETMETHOD ->
      handler_correct h1 (clight_of GETMETHOD)
        (error_message_of GETMETHOD)
        (pre_of GETMETHOD) (P_halt_of GETMETHOD) (P_ccall_of GETMETHOD) ->
      handler_correct h2 (clight_of GETMETHOD)
        (error_message_of GETMETHOD)
        (pre_of GETMETHOD) (P_halt_of GETMETHOD) (P_ccall_of GETMETHOD) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_GETPUBMET : forall z,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (GETPUBMET z) ->
      handler_correct h1 (clight_of (GETPUBMET z))
        (error_message_of (GETPUBMET z))
        (pre_of (GETPUBMET z)) (P_halt_of (GETPUBMET z)) (P_ccall_of (GETPUBMET z)) ->
      handler_correct h2 (clight_of (GETPUBMET z))
        (error_message_of (GETPUBMET z))
        (pre_of (GETPUBMET z)) (P_halt_of (GETPUBMET z)) (P_ccall_of (GETPUBMET z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_GETDYNMET :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps GETDYNMET ->
      handler_correct h1 (clight_of GETDYNMET)
        (error_message_of GETDYNMET)
        (pre_of GETDYNMET) (P_halt_of GETDYNMET) (P_ccall_of GETDYNMET) ->
      handler_correct h2 (clight_of GETDYNMET)
        (error_message_of GETDYNMET)
        (pre_of GETDYNMET) (P_halt_of GETDYNMET) (P_ccall_of GETDYNMET) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_BEQ : forall z1 z2,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (BEQ z1 z2) ->
      handler_correct h1 (clight_of (BEQ z1 z2))
        (error_message_of (BEQ z1 z2))
        (pre_of (BEQ z1 z2)) (P_halt_of (BEQ z1 z2)) (P_ccall_of (BEQ z1 z2)) ->
      handler_correct h2 (clight_of (BEQ z1 z2))
        (error_message_of (BEQ z1 z2))
        (pre_of (BEQ z1 z2)) (P_halt_of (BEQ z1 z2)) (P_ccall_of (BEQ z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_BNEQ : forall z1 z2,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (BNEQ z1 z2) ->
      handler_correct h1 (clight_of (BNEQ z1 z2))
        (error_message_of (BNEQ z1 z2))
        (pre_of (BNEQ z1 z2)) (P_halt_of (BNEQ z1 z2)) (P_ccall_of (BNEQ z1 z2)) ->
      handler_correct h2 (clight_of (BNEQ z1 z2))
        (error_message_of (BNEQ z1 z2))
        (pre_of (BNEQ z1 z2)) (P_halt_of (BNEQ z1 z2)) (P_ccall_of (BNEQ z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_BLTINT : forall z1 z2,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (BLTINT z1 z2) ->
      handler_correct h1 (clight_of (BLTINT z1 z2))
        (error_message_of (BLTINT z1 z2))
        (pre_of (BLTINT z1 z2)) (P_halt_of (BLTINT z1 z2)) (P_ccall_of (BLTINT z1 z2)) ->
      handler_correct h2 (clight_of (BLTINT z1 z2))
        (error_message_of (BLTINT z1 z2))
        (pre_of (BLTINT z1 z2)) (P_halt_of (BLTINT z1 z2)) (P_ccall_of (BLTINT z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_BLEINT : forall z1 z2,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (BLEINT z1 z2) ->
      handler_correct h1 (clight_of (BLEINT z1 z2))
        (error_message_of (BLEINT z1 z2))
        (pre_of (BLEINT z1 z2)) (P_halt_of (BLEINT z1 z2)) (P_ccall_of (BLEINT z1 z2)) ->
      handler_correct h2 (clight_of (BLEINT z1 z2))
        (error_message_of (BLEINT z1 z2))
        (pre_of (BLEINT z1 z2)) (P_halt_of (BLEINT z1 z2)) (P_ccall_of (BLEINT z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_BGTINT : forall z1 z2,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (BGTINT z1 z2) ->
      handler_correct h1 (clight_of (BGTINT z1 z2))
        (error_message_of (BGTINT z1 z2))
        (pre_of (BGTINT z1 z2)) (P_halt_of (BGTINT z1 z2)) (P_ccall_of (BGTINT z1 z2)) ->
      handler_correct h2 (clight_of (BGTINT z1 z2))
        (error_message_of (BGTINT z1 z2))
        (pre_of (BGTINT z1 z2)) (P_halt_of (BGTINT z1 z2)) (P_ccall_of (BGTINT z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_BGEINT : forall z1 z2,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (BGEINT z1 z2) ->
      handler_correct h1 (clight_of (BGEINT z1 z2))
        (error_message_of (BGEINT z1 z2))
        (pre_of (BGEINT z1 z2)) (P_halt_of (BGEINT z1 z2)) (P_ccall_of (BGEINT z1 z2)) ->
      handler_correct h2 (clight_of (BGEINT z1 z2))
        (error_message_of (BGEINT z1 z2))
        (pre_of (BGEINT z1 z2)) (P_halt_of (BGEINT z1 z2)) (P_ccall_of (BGEINT z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_ULTINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps ULTINT ->
      handler_correct h1 (clight_of ULTINT)
        (error_message_of ULTINT)
        (pre_of ULTINT) (P_halt_of ULTINT) (P_ccall_of ULTINT) ->
      handler_correct h2 (clight_of ULTINT)
        (error_message_of ULTINT)
        (pre_of ULTINT) (P_halt_of ULTINT) (P_ccall_of ULTINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_UGEINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps UGEINT ->
      handler_correct h1 (clight_of UGEINT)
        (error_message_of UGEINT)
        (pre_of UGEINT) (P_halt_of UGEINT) (P_ccall_of UGEINT) ->
      handler_correct h2 (clight_of UGEINT)
        (error_message_of UGEINT)
        (pre_of UGEINT) (P_halt_of UGEINT) (P_ccall_of UGEINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_BULTINT : forall z1 z2,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (BULTINT z1 z2) ->
      handler_correct h1 (clight_of (BULTINT z1 z2))
        (error_message_of (BULTINT z1 z2))
        (pre_of (BULTINT z1 z2)) (P_halt_of (BULTINT z1 z2)) (P_ccall_of (BULTINT z1 z2)) ->
      handler_correct h2 (clight_of (BULTINT z1 z2))
        (error_message_of (BULTINT z1 z2))
        (pre_of (BULTINT z1 z2)) (P_halt_of (BULTINT z1 z2)) (P_ccall_of (BULTINT z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_BUGEINT : forall z1 z2,
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps (BUGEINT z1 z2) ->
      handler_correct h1 (clight_of (BUGEINT z1 z2))
        (error_message_of (BUGEINT z1 z2))
        (pre_of (BUGEINT z1 z2)) (P_halt_of (BUGEINT z1 z2)) (P_ccall_of (BUGEINT z1 z2)) ->
      handler_correct h2 (clight_of (BUGEINT z1 z2))
        (error_message_of (BUGEINT z1 z2))
        (pre_of (BUGEINT z1 z2)) (P_halt_of (BUGEINT z1 z2)) (P_ccall_of (BUGEINT z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

  Parameter unique_STOP :
    forall (h1 h2 : Z -> state -> step_result),
      handler_unique_hyps STOP ->
      handler_correct h1 (clight_of STOP)
        (error_message_of STOP)
        (pre_of STOP) (P_halt_of STOP) (P_ccall_of STOP) ->
      handler_correct h2 (clight_of STOP)
        (error_message_of STOP)
        (pre_of STOP) (P_halt_of STOP) (P_ccall_of STOP) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).

End MetaSpecFineGrainedSpec.

(* Assembling fine-grained uniqueness into the unified MetaSpec. *)
Module MetaSpecFromFineGrained
       (Import FG : MetaSpecFineGrainedSpec) <: MetaSpec.

    Lemma handler_unique_mod_errors :
      forall (i : instruction)
             (h1 h2 : Z -> state -> step_result),
        handler_unique_hyps i ->
        handler_correct h1 (clight_of i)
          (error_message_of i) (pre_of i) (P_halt_of i) (P_ccall_of i) ->
        handler_correct h2 (clight_of i)
          (error_message_of i) (pre_of i) (P_halt_of i) (P_ccall_of i) ->
        forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
    Proof.
      intro i; destruct i;
      [ apply unique_ACC | apply unique_PUSH | apply unique_PUSHACC | apply unique_POP
      | apply unique_ASSIGN | apply unique_ENVACC | apply unique_PUSHENVACC | apply unique_PUSH_RETADDR
      | apply unique_APPLY | apply unique_APPLY1 | apply unique_APPLY2 | apply unique_APPLY3
      | apply unique_APPTERM | apply unique_APPTERM1 | apply unique_APPTERM2 | apply unique_APPTERM3
      | apply unique_RETURN | apply unique_RESTART | apply unique_GRAB | apply unique_CLOSURE
      | apply unique_CLOSUREREC | apply unique_OFFSETCLOSURE | apply unique_PUSHOFFSETCLOSURE | apply unique_GETGLOBAL
      | apply unique_PUSHGETGLOBAL | apply unique_GETGLOBALFIELD | apply unique_PUSHGETGLOBALFIELD | apply unique_SETGLOBAL
      | apply unique_ATOM | apply unique_PUSHATOM | apply unique_MAKEBLOCK | apply unique_MAKEBLOCK1
      | apply unique_MAKEBLOCK2 | apply unique_MAKEBLOCK3 | apply unique_MAKEFLOATBLOCK | apply unique_GETFIELD
      | apply unique_GETFLOATFIELD | apply unique_SETFIELD | apply unique_SETFLOATFIELD | apply unique_VECTLENGTH
      | apply unique_GETVECTITEM | apply unique_SETVECTITEM | apply unique_GETBYTESCHAR | apply unique_SETBYTESCHAR
      | apply unique_GETSTRINGCHAR | apply unique_BRANCH | apply unique_BRANCHIF | apply unique_BRANCHIFNOT
      | apply unique_SWITCH | apply unique_BOOLNOT | apply unique_PUSHTRAP | apply unique_POPTRAP
      | apply unique_RAISE | apply unique_RERAISE | apply unique_RAISE_NOTRACE | apply unique_CHECK_SIGNALS
      | apply unique_C_CALL | apply unique_CONSTINT | apply unique_PUSHCONSTINT | apply unique_NEGINT
      | apply unique_ADDINT | apply unique_SUBINT | apply unique_MULINT | apply unique_DIVINT
      | apply unique_MODINT | apply unique_ANDINT | apply unique_ORINT | apply unique_XORINT
      | apply unique_LSLINT | apply unique_LSRINT | apply unique_ASRINT | apply unique_EQ
      | apply unique_NEQ | apply unique_LTINT | apply unique_LEINT | apply unique_GTINT
      | apply unique_GEINT | apply unique_OFFSETINT | apply unique_OFFSETREF | apply unique_ISINT
      | apply unique_GETMETHOD | apply unique_GETPUBMET | apply unique_GETDYNMET | apply unique_BEQ
      | apply unique_BNEQ | apply unique_BLTINT | apply unique_BLEINT | apply unique_BGTINT
      | apply unique_BGEINT | apply unique_ULTINT | apply unique_UGEINT | apply unique_BULTINT
      | apply unique_BUGEINT | apply unique_STOP ].
    Qed.
End MetaSpecFromFineGrained.
