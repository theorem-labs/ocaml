(* MetaSpecProof.v - [UNTRUSTED] Fine-grained implementation of the handler
   uniqueness meta-specification.

   Each per-instruction uniqueness lemma is Admitted here; the proofs will
   be filled in by per-instruction subagents in
   automatic/Bytecode/MetaSpecVerification/. *)

From Stdlib Require Import ZArith List Strings.String.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

(* Per-instruction uniqueness lemmas -- all Admitted *)

Lemma unique_ACC : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (ACC n))
        (pre_of (ACC n)) (P_error_of (ACC n)) (P_halt_of (ACC n)) (P_ccall_of (ACC n)) ->
      handler_correct h2 (clight_of (ACC n))
        (pre_of (ACC n)) (P_error_of (ACC n)) (P_halt_of (ACC n)) (P_ccall_of (ACC n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_PUSH :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of PUSH)
        (pre_of PUSH) (P_error_of PUSH) (P_halt_of PUSH) (P_ccall_of PUSH) ->
      handler_correct h2 (clight_of PUSH)
        (pre_of PUSH) (P_error_of PUSH) (P_halt_of PUSH) (P_ccall_of PUSH) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_PUSHACC : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (PUSHACC n))
        (pre_of (PUSHACC n)) (P_error_of (PUSHACC n)) (P_halt_of (PUSHACC n)) (P_ccall_of (PUSHACC n)) ->
      handler_correct h2 (clight_of (PUSHACC n))
        (pre_of (PUSHACC n)) (P_error_of (PUSHACC n)) (P_halt_of (PUSHACC n)) (P_ccall_of (PUSHACC n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_POP : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (POP n))
        (pre_of (POP n)) (P_error_of (POP n)) (P_halt_of (POP n)) (P_ccall_of (POP n)) ->
      handler_correct h2 (clight_of (POP n))
        (pre_of (POP n)) (P_error_of (POP n)) (P_halt_of (POP n)) (P_ccall_of (POP n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_ASSIGN : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (ASSIGN n))
        (pre_of (ASSIGN n)) (P_error_of (ASSIGN n)) (P_halt_of (ASSIGN n)) (P_ccall_of (ASSIGN n)) ->
      handler_correct h2 (clight_of (ASSIGN n))
        (pre_of (ASSIGN n)) (P_error_of (ASSIGN n)) (P_halt_of (ASSIGN n)) (P_ccall_of (ASSIGN n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_ENVACC : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (ENVACC n))
        (pre_of (ENVACC n)) (P_error_of (ENVACC n)) (P_halt_of (ENVACC n)) (P_ccall_of (ENVACC n)) ->
      handler_correct h2 (clight_of (ENVACC n))
        (pre_of (ENVACC n)) (P_error_of (ENVACC n)) (P_halt_of (ENVACC n)) (P_ccall_of (ENVACC n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_PUSHENVACC : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (PUSHENVACC n))
        (pre_of (PUSHENVACC n)) (P_error_of (PUSHENVACC n)) (P_halt_of (PUSHENVACC n)) (P_ccall_of (PUSHENVACC n)) ->
      handler_correct h2 (clight_of (PUSHENVACC n))
        (pre_of (PUSHENVACC n)) (P_error_of (PUSHENVACC n)) (P_halt_of (PUSHENVACC n)) (P_ccall_of (PUSHENVACC n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_PUSH_RETADDR : forall z, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (PUSH_RETADDR z))
        (pre_of (PUSH_RETADDR z)) (P_error_of (PUSH_RETADDR z)) (P_halt_of (PUSH_RETADDR z)) (P_ccall_of (PUSH_RETADDR z)) ->
      handler_correct h2 (clight_of (PUSH_RETADDR z))
        (pre_of (PUSH_RETADDR z)) (P_error_of (PUSH_RETADDR z)) (P_halt_of (PUSH_RETADDR z)) (P_ccall_of (PUSH_RETADDR z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_APPLY : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (APPLY n))
        (pre_of (APPLY n)) (P_error_of (APPLY n)) (P_halt_of (APPLY n)) (P_ccall_of (APPLY n)) ->
      handler_correct h2 (clight_of (APPLY n))
        (pre_of (APPLY n)) (P_error_of (APPLY n)) (P_halt_of (APPLY n)) (P_ccall_of (APPLY n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_APPLY1 :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of APPLY1)
        (pre_of APPLY1) (P_error_of APPLY1) (P_halt_of APPLY1) (P_ccall_of APPLY1) ->
      handler_correct h2 (clight_of APPLY1)
        (pre_of APPLY1) (P_error_of APPLY1) (P_halt_of APPLY1) (P_ccall_of APPLY1) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_APPLY2 :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of APPLY2)
        (pre_of APPLY2) (P_error_of APPLY2) (P_halt_of APPLY2) (P_ccall_of APPLY2) ->
      handler_correct h2 (clight_of APPLY2)
        (pre_of APPLY2) (P_error_of APPLY2) (P_halt_of APPLY2) (P_ccall_of APPLY2) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_APPLY3 :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of APPLY3)
        (pre_of APPLY3) (P_error_of APPLY3) (P_halt_of APPLY3) (P_ccall_of APPLY3) ->
      handler_correct h2 (clight_of APPLY3)
        (pre_of APPLY3) (P_error_of APPLY3) (P_halt_of APPLY3) (P_ccall_of APPLY3) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_APPTERM : forall nargs slotsize, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (APPTERM nargs slotsize))
        (pre_of (APPTERM nargs slotsize)) (P_error_of (APPTERM nargs slotsize)) (P_halt_of (APPTERM nargs slotsize)) (P_ccall_of (APPTERM nargs slotsize)) ->
      handler_correct h2 (clight_of (APPTERM nargs slotsize))
        (pre_of (APPTERM nargs slotsize)) (P_error_of (APPTERM nargs slotsize)) (P_halt_of (APPTERM nargs slotsize)) (P_ccall_of (APPTERM nargs slotsize)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_APPTERM1 : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (APPTERM1 n))
        (pre_of (APPTERM1 n)) (P_error_of (APPTERM1 n)) (P_halt_of (APPTERM1 n)) (P_ccall_of (APPTERM1 n)) ->
      handler_correct h2 (clight_of (APPTERM1 n))
        (pre_of (APPTERM1 n)) (P_error_of (APPTERM1 n)) (P_halt_of (APPTERM1 n)) (P_ccall_of (APPTERM1 n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_APPTERM2 : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (APPTERM2 n))
        (pre_of (APPTERM2 n)) (P_error_of (APPTERM2 n)) (P_halt_of (APPTERM2 n)) (P_ccall_of (APPTERM2 n)) ->
      handler_correct h2 (clight_of (APPTERM2 n))
        (pre_of (APPTERM2 n)) (P_error_of (APPTERM2 n)) (P_halt_of (APPTERM2 n)) (P_ccall_of (APPTERM2 n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_APPTERM3 : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (APPTERM3 n))
        (pre_of (APPTERM3 n)) (P_error_of (APPTERM3 n)) (P_halt_of (APPTERM3 n)) (P_ccall_of (APPTERM3 n)) ->
      handler_correct h2 (clight_of (APPTERM3 n))
        (pre_of (APPTERM3 n)) (P_error_of (APPTERM3 n)) (P_halt_of (APPTERM3 n)) (P_ccall_of (APPTERM3 n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_RETURN : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (RETURN n))
        (pre_of (RETURN n)) (P_error_of (RETURN n)) (P_halt_of (RETURN n)) (P_ccall_of (RETURN n)) ->
      handler_correct h2 (clight_of (RETURN n))
        (pre_of (RETURN n)) (P_error_of (RETURN n)) (P_halt_of (RETURN n)) (P_ccall_of (RETURN n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_RESTART :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of RESTART)
        (pre_of RESTART) (P_error_of RESTART) (P_halt_of RESTART) (P_ccall_of RESTART) ->
      handler_correct h2 (clight_of RESTART)
        (pre_of RESTART) (P_error_of RESTART) (P_halt_of RESTART) (P_ccall_of RESTART) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_GRAB : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (GRAB n))
        (pre_of (GRAB n)) (P_error_of (GRAB n)) (P_halt_of (GRAB n)) (P_ccall_of (GRAB n)) ->
      handler_correct h2 (clight_of (GRAB n))
        (pre_of (GRAB n)) (P_error_of (GRAB n)) (P_halt_of (GRAB n)) (P_ccall_of (GRAB n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_CLOSURE : forall nvars code_ofs, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (CLOSURE nvars code_ofs))
        (pre_of (CLOSURE nvars code_ofs)) (P_error_of (CLOSURE nvars code_ofs)) (P_halt_of (CLOSURE nvars code_ofs)) (P_ccall_of (CLOSURE nvars code_ofs)) ->
      handler_correct h2 (clight_of (CLOSURE nvars code_ofs))
        (pre_of (CLOSURE nvars code_ofs)) (P_error_of (CLOSURE nvars code_ofs)) (P_halt_of (CLOSURE nvars code_ofs)) (P_ccall_of (CLOSURE nvars code_ofs)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_CLOSUREREC : forall nfuncs nvars code_offsets, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (CLOSUREREC nfuncs nvars code_offsets))
        (pre_of (CLOSUREREC nfuncs nvars code_offsets)) (P_error_of (CLOSUREREC nfuncs nvars code_offsets)) (P_halt_of (CLOSUREREC nfuncs nvars code_offsets)) (P_ccall_of (CLOSUREREC nfuncs nvars code_offsets)) ->
      handler_correct h2 (clight_of (CLOSUREREC nfuncs nvars code_offsets))
        (pre_of (CLOSUREREC nfuncs nvars code_offsets)) (P_error_of (CLOSUREREC nfuncs nvars code_offsets)) (P_halt_of (CLOSUREREC nfuncs nvars code_offsets)) (P_ccall_of (CLOSUREREC nfuncs nvars code_offsets)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_OFFSETCLOSURE : forall z, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (OFFSETCLOSURE z))
        (pre_of (OFFSETCLOSURE z)) (P_error_of (OFFSETCLOSURE z)) (P_halt_of (OFFSETCLOSURE z)) (P_ccall_of (OFFSETCLOSURE z)) ->
      handler_correct h2 (clight_of (OFFSETCLOSURE z))
        (pre_of (OFFSETCLOSURE z)) (P_error_of (OFFSETCLOSURE z)) (P_halt_of (OFFSETCLOSURE z)) (P_ccall_of (OFFSETCLOSURE z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_PUSHOFFSETCLOSURE : forall z, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (PUSHOFFSETCLOSURE z))
        (pre_of (PUSHOFFSETCLOSURE z)) (P_error_of (PUSHOFFSETCLOSURE z)) (P_halt_of (PUSHOFFSETCLOSURE z)) (P_ccall_of (PUSHOFFSETCLOSURE z)) ->
      handler_correct h2 (clight_of (PUSHOFFSETCLOSURE z))
        (pre_of (PUSHOFFSETCLOSURE z)) (P_error_of (PUSHOFFSETCLOSURE z)) (P_halt_of (PUSHOFFSETCLOSURE z)) (P_ccall_of (PUSHOFFSETCLOSURE z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_GETGLOBAL : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (GETGLOBAL n))
        (pre_of (GETGLOBAL n)) (P_error_of (GETGLOBAL n)) (P_halt_of (GETGLOBAL n)) (P_ccall_of (GETGLOBAL n)) ->
      handler_correct h2 (clight_of (GETGLOBAL n))
        (pre_of (GETGLOBAL n)) (P_error_of (GETGLOBAL n)) (P_halt_of (GETGLOBAL n)) (P_ccall_of (GETGLOBAL n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_PUSHGETGLOBAL : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (PUSHGETGLOBAL n))
        (pre_of (PUSHGETGLOBAL n)) (P_error_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)) ->
      handler_correct h2 (clight_of (PUSHGETGLOBAL n))
        (pre_of (PUSHGETGLOBAL n)) (P_error_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_GETGLOBALFIELD : forall n p, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (GETGLOBALFIELD n p))
        (pre_of (GETGLOBALFIELD n p)) (P_error_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)) ->
      handler_correct h2 (clight_of (GETGLOBALFIELD n p))
        (pre_of (GETGLOBALFIELD n p)) (P_error_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_PUSHGETGLOBALFIELD : forall n p, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (PUSHGETGLOBALFIELD n p))
        (pre_of (PUSHGETGLOBALFIELD n p)) (P_error_of (PUSHGETGLOBALFIELD n p)) (P_halt_of (PUSHGETGLOBALFIELD n p)) (P_ccall_of (PUSHGETGLOBALFIELD n p)) ->
      handler_correct h2 (clight_of (PUSHGETGLOBALFIELD n p))
        (pre_of (PUSHGETGLOBALFIELD n p)) (P_error_of (PUSHGETGLOBALFIELD n p)) (P_halt_of (PUSHGETGLOBALFIELD n p)) (P_ccall_of (PUSHGETGLOBALFIELD n p)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_SETGLOBAL : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (SETGLOBAL n))
        (pre_of (SETGLOBAL n)) (P_error_of (SETGLOBAL n)) (P_halt_of (SETGLOBAL n)) (P_ccall_of (SETGLOBAL n)) ->
      handler_correct h2 (clight_of (SETGLOBAL n))
        (pre_of (SETGLOBAL n)) (P_error_of (SETGLOBAL n)) (P_halt_of (SETGLOBAL n)) (P_ccall_of (SETGLOBAL n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_ATOM : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (ATOM n))
        (pre_of (ATOM n)) (P_error_of (ATOM n)) (P_halt_of (ATOM n)) (P_ccall_of (ATOM n)) ->
      handler_correct h2 (clight_of (ATOM n))
        (pre_of (ATOM n)) (P_error_of (ATOM n)) (P_halt_of (ATOM n)) (P_ccall_of (ATOM n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_PUSHATOM : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (PUSHATOM n))
        (pre_of (PUSHATOM n)) (P_error_of (PUSHATOM n)) (P_halt_of (PUSHATOM n)) (P_ccall_of (PUSHATOM n)) ->
      handler_correct h2 (clight_of (PUSHATOM n))
        (pre_of (PUSHATOM n)) (P_error_of (PUSHATOM n)) (P_halt_of (PUSHATOM n)) (P_ccall_of (PUSHATOM n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_MAKEBLOCK : forall t size, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (MAKEBLOCK t size))
        (pre_of (MAKEBLOCK t size)) (P_error_of (MAKEBLOCK t size)) (P_halt_of (MAKEBLOCK t size)) (P_ccall_of (MAKEBLOCK t size)) ->
      handler_correct h2 (clight_of (MAKEBLOCK t size))
        (pre_of (MAKEBLOCK t size)) (P_error_of (MAKEBLOCK t size)) (P_halt_of (MAKEBLOCK t size)) (P_ccall_of (MAKEBLOCK t size)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_MAKEBLOCK1 : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (MAKEBLOCK1 n))
        (pre_of (MAKEBLOCK1 n)) (P_error_of (MAKEBLOCK1 n)) (P_halt_of (MAKEBLOCK1 n)) (P_ccall_of (MAKEBLOCK1 n)) ->
      handler_correct h2 (clight_of (MAKEBLOCK1 n))
        (pre_of (MAKEBLOCK1 n)) (P_error_of (MAKEBLOCK1 n)) (P_halt_of (MAKEBLOCK1 n)) (P_ccall_of (MAKEBLOCK1 n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_MAKEBLOCK2 : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (MAKEBLOCK2 n))
        (pre_of (MAKEBLOCK2 n)) (P_error_of (MAKEBLOCK2 n)) (P_halt_of (MAKEBLOCK2 n)) (P_ccall_of (MAKEBLOCK2 n)) ->
      handler_correct h2 (clight_of (MAKEBLOCK2 n))
        (pre_of (MAKEBLOCK2 n)) (P_error_of (MAKEBLOCK2 n)) (P_halt_of (MAKEBLOCK2 n)) (P_ccall_of (MAKEBLOCK2 n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_MAKEBLOCK3 : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (MAKEBLOCK3 n))
        (pre_of (MAKEBLOCK3 n)) (P_error_of (MAKEBLOCK3 n)) (P_halt_of (MAKEBLOCK3 n)) (P_ccall_of (MAKEBLOCK3 n)) ->
      handler_correct h2 (clight_of (MAKEBLOCK3 n))
        (pre_of (MAKEBLOCK3 n)) (P_error_of (MAKEBLOCK3 n)) (P_halt_of (MAKEBLOCK3 n)) (P_ccall_of (MAKEBLOCK3 n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_MAKEFLOATBLOCK : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (MAKEFLOATBLOCK n))
        (pre_of (MAKEFLOATBLOCK n)) (P_error_of (MAKEFLOATBLOCK n)) (P_halt_of (MAKEFLOATBLOCK n)) (P_ccall_of (MAKEFLOATBLOCK n)) ->
      handler_correct h2 (clight_of (MAKEFLOATBLOCK n))
        (pre_of (MAKEFLOATBLOCK n)) (P_error_of (MAKEFLOATBLOCK n)) (P_halt_of (MAKEFLOATBLOCK n)) (P_ccall_of (MAKEFLOATBLOCK n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_GETFIELD : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (GETFIELD n))
        (pre_of (GETFIELD n)) (P_error_of (GETFIELD n)) (P_halt_of (GETFIELD n)) (P_ccall_of (GETFIELD n)) ->
      handler_correct h2 (clight_of (GETFIELD n))
        (pre_of (GETFIELD n)) (P_error_of (GETFIELD n)) (P_halt_of (GETFIELD n)) (P_ccall_of (GETFIELD n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_GETFLOATFIELD : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (GETFLOATFIELD n))
        (pre_of (GETFLOATFIELD n)) (P_error_of (GETFLOATFIELD n)) (P_halt_of (GETFLOATFIELD n)) (P_ccall_of (GETFLOATFIELD n)) ->
      handler_correct h2 (clight_of (GETFLOATFIELD n))
        (pre_of (GETFLOATFIELD n)) (P_error_of (GETFLOATFIELD n)) (P_halt_of (GETFLOATFIELD n)) (P_ccall_of (GETFLOATFIELD n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_SETFIELD : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (SETFIELD n))
        (pre_of (SETFIELD n)) (P_error_of (SETFIELD n)) (P_halt_of (SETFIELD n)) (P_ccall_of (SETFIELD n)) ->
      handler_correct h2 (clight_of (SETFIELD n))
        (pre_of (SETFIELD n)) (P_error_of (SETFIELD n)) (P_halt_of (SETFIELD n)) (P_ccall_of (SETFIELD n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_SETFLOATFIELD : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (SETFLOATFIELD n))
        (pre_of (SETFLOATFIELD n)) (P_error_of (SETFLOATFIELD n)) (P_halt_of (SETFLOATFIELD n)) (P_ccall_of (SETFLOATFIELD n)) ->
      handler_correct h2 (clight_of (SETFLOATFIELD n))
        (pre_of (SETFLOATFIELD n)) (P_error_of (SETFLOATFIELD n)) (P_halt_of (SETFLOATFIELD n)) (P_ccall_of (SETFLOATFIELD n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_VECTLENGTH :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of VECTLENGTH)
        (pre_of VECTLENGTH) (P_error_of VECTLENGTH) (P_halt_of VECTLENGTH) (P_ccall_of VECTLENGTH) ->
      handler_correct h2 (clight_of VECTLENGTH)
        (pre_of VECTLENGTH) (P_error_of VECTLENGTH) (P_halt_of VECTLENGTH) (P_ccall_of VECTLENGTH) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_GETVECTITEM :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of GETVECTITEM)
        (pre_of GETVECTITEM) (P_error_of GETVECTITEM) (P_halt_of GETVECTITEM) (P_ccall_of GETVECTITEM) ->
      handler_correct h2 (clight_of GETVECTITEM)
        (pre_of GETVECTITEM) (P_error_of GETVECTITEM) (P_halt_of GETVECTITEM) (P_ccall_of GETVECTITEM) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_SETVECTITEM :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of SETVECTITEM)
        (pre_of SETVECTITEM) (P_error_of SETVECTITEM) (P_halt_of SETVECTITEM) (P_ccall_of SETVECTITEM) ->
      handler_correct h2 (clight_of SETVECTITEM)
        (pre_of SETVECTITEM) (P_error_of SETVECTITEM) (P_halt_of SETVECTITEM) (P_ccall_of SETVECTITEM) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_GETBYTESCHAR :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of GETBYTESCHAR)
        (pre_of GETBYTESCHAR) (P_error_of GETBYTESCHAR) (P_halt_of GETBYTESCHAR) (P_ccall_of GETBYTESCHAR) ->
      handler_correct h2 (clight_of GETBYTESCHAR)
        (pre_of GETBYTESCHAR) (P_error_of GETBYTESCHAR) (P_halt_of GETBYTESCHAR) (P_ccall_of GETBYTESCHAR) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_SETBYTESCHAR :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of SETBYTESCHAR)
        (pre_of SETBYTESCHAR) (P_error_of SETBYTESCHAR) (P_halt_of SETBYTESCHAR) (P_ccall_of SETBYTESCHAR) ->
      handler_correct h2 (clight_of SETBYTESCHAR)
        (pre_of SETBYTESCHAR) (P_error_of SETBYTESCHAR) (P_halt_of SETBYTESCHAR) (P_ccall_of SETBYTESCHAR) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_GETSTRINGCHAR :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of GETSTRINGCHAR)
        (pre_of GETSTRINGCHAR) (P_error_of GETSTRINGCHAR) (P_halt_of GETSTRINGCHAR) (P_ccall_of GETSTRINGCHAR) ->
      handler_correct h2 (clight_of GETSTRINGCHAR)
        (pre_of GETSTRINGCHAR) (P_error_of GETSTRINGCHAR) (P_halt_of GETSTRINGCHAR) (P_ccall_of GETSTRINGCHAR) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_BRANCH : forall z, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (BRANCH z))
        (pre_of (BRANCH z)) (P_error_of (BRANCH z)) (P_halt_of (BRANCH z)) (P_ccall_of (BRANCH z)) ->
      handler_correct h2 (clight_of (BRANCH z))
        (pre_of (BRANCH z)) (P_error_of (BRANCH z)) (P_halt_of (BRANCH z)) (P_ccall_of (BRANCH z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_BRANCHIF : forall z, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (BRANCHIF z))
        (pre_of (BRANCHIF z)) (P_error_of (BRANCHIF z)) (P_halt_of (BRANCHIF z)) (P_ccall_of (BRANCHIF z)) ->
      handler_correct h2 (clight_of (BRANCHIF z))
        (pre_of (BRANCHIF z)) (P_error_of (BRANCHIF z)) (P_halt_of (BRANCHIF z)) (P_ccall_of (BRANCHIF z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_BRANCHIFNOT : forall z, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (BRANCHIFNOT z))
        (pre_of (BRANCHIFNOT z)) (P_error_of (BRANCHIFNOT z)) (P_halt_of (BRANCHIFNOT z)) (P_ccall_of (BRANCHIFNOT z)) ->
      handler_correct h2 (clight_of (BRANCHIFNOT z))
        (pre_of (BRANCHIFNOT z)) (P_error_of (BRANCHIFNOT z)) (P_halt_of (BRANCHIFNOT z)) (P_ccall_of (BRANCHIFNOT z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_SWITCH : forall nc nb const_targets block_targets, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (SWITCH nc nb const_targets block_targets))
        (pre_of (SWITCH nc nb const_targets block_targets)) (P_error_of (SWITCH nc nb const_targets block_targets)) (P_halt_of (SWITCH nc nb const_targets block_targets)) (P_ccall_of (SWITCH nc nb const_targets block_targets)) ->
      handler_correct h2 (clight_of (SWITCH nc nb const_targets block_targets))
        (pre_of (SWITCH nc nb const_targets block_targets)) (P_error_of (SWITCH nc nb const_targets block_targets)) (P_halt_of (SWITCH nc nb const_targets block_targets)) (P_ccall_of (SWITCH nc nb const_targets block_targets)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_BOOLNOT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of BOOLNOT)
        (pre_of BOOLNOT) (P_error_of BOOLNOT) (P_halt_of BOOLNOT) (P_ccall_of BOOLNOT) ->
      handler_correct h2 (clight_of BOOLNOT)
        (pre_of BOOLNOT) (P_error_of BOOLNOT) (P_halt_of BOOLNOT) (P_ccall_of BOOLNOT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_PUSHTRAP : forall z, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (PUSHTRAP z))
        (pre_of (PUSHTRAP z)) (P_error_of (PUSHTRAP z)) (P_halt_of (PUSHTRAP z)) (P_ccall_of (PUSHTRAP z)) ->
      handler_correct h2 (clight_of (PUSHTRAP z))
        (pre_of (PUSHTRAP z)) (P_error_of (PUSHTRAP z)) (P_halt_of (PUSHTRAP z)) (P_ccall_of (PUSHTRAP z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_POPTRAP :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of POPTRAP)
        (pre_of POPTRAP) (P_error_of POPTRAP) (P_halt_of POPTRAP) (P_ccall_of POPTRAP) ->
      handler_correct h2 (clight_of POPTRAP)
        (pre_of POPTRAP) (P_error_of POPTRAP) (P_halt_of POPTRAP) (P_ccall_of POPTRAP) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_RAISE :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of RAISE)
        (pre_of RAISE) (P_error_of RAISE) (P_halt_of RAISE) (P_ccall_of RAISE) ->
      handler_correct h2 (clight_of RAISE)
        (pre_of RAISE) (P_error_of RAISE) (P_halt_of RAISE) (P_ccall_of RAISE) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_RERAISE :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of RERAISE)
        (pre_of RERAISE) (P_error_of RERAISE) (P_halt_of RERAISE) (P_ccall_of RERAISE) ->
      handler_correct h2 (clight_of RERAISE)
        (pre_of RERAISE) (P_error_of RERAISE) (P_halt_of RERAISE) (P_ccall_of RERAISE) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_RAISE_NOTRACE :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of RAISE_NOTRACE)
        (pre_of RAISE_NOTRACE) (P_error_of RAISE_NOTRACE) (P_halt_of RAISE_NOTRACE) (P_ccall_of RAISE_NOTRACE) ->
      handler_correct h2 (clight_of RAISE_NOTRACE)
        (pre_of RAISE_NOTRACE) (P_error_of RAISE_NOTRACE) (P_halt_of RAISE_NOTRACE) (P_ccall_of RAISE_NOTRACE) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_CHECK_SIGNALS :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of CHECK_SIGNALS)
        (pre_of CHECK_SIGNALS) (P_error_of CHECK_SIGNALS) (P_halt_of CHECK_SIGNALS) (P_ccall_of CHECK_SIGNALS) ->
      handler_correct h2 (clight_of CHECK_SIGNALS)
        (pre_of CHECK_SIGNALS) (P_error_of CHECK_SIGNALS) (P_halt_of CHECK_SIGNALS) (P_ccall_of CHECK_SIGNALS) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_C_CALL : forall nargs prim_idx, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (C_CALL nargs prim_idx))
        (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
      handler_correct h2 (clight_of (C_CALL nargs prim_idx))
        (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_CONSTINT : forall z, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (CONSTINT z))
        (pre_of (CONSTINT z)) (P_error_of (CONSTINT z)) (P_halt_of (CONSTINT z)) (P_ccall_of (CONSTINT z)) ->
      handler_correct h2 (clight_of (CONSTINT z))
        (pre_of (CONSTINT z)) (P_error_of (CONSTINT z)) (P_halt_of (CONSTINT z)) (P_ccall_of (CONSTINT z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_PUSHCONSTINT : forall z, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (PUSHCONSTINT z))
        (pre_of (PUSHCONSTINT z)) (P_error_of (PUSHCONSTINT z)) (P_halt_of (PUSHCONSTINT z)) (P_ccall_of (PUSHCONSTINT z)) ->
      handler_correct h2 (clight_of (PUSHCONSTINT z))
        (pre_of (PUSHCONSTINT z)) (P_error_of (PUSHCONSTINT z)) (P_halt_of (PUSHCONSTINT z)) (P_ccall_of (PUSHCONSTINT z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_NEGINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of NEGINT)
        (pre_of NEGINT) (P_error_of NEGINT) (P_halt_of NEGINT) (P_ccall_of NEGINT) ->
      handler_correct h2 (clight_of NEGINT)
        (pre_of NEGINT) (P_error_of NEGINT) (P_halt_of NEGINT) (P_ccall_of NEGINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_ADDINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of ADDINT)
        (pre_of ADDINT) (P_error_of ADDINT) (P_halt_of ADDINT) (P_ccall_of ADDINT) ->
      handler_correct h2 (clight_of ADDINT)
        (pre_of ADDINT) (P_error_of ADDINT) (P_halt_of ADDINT) (P_ccall_of ADDINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_SUBINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of SUBINT)
        (pre_of SUBINT) (P_error_of SUBINT) (P_halt_of SUBINT) (P_ccall_of SUBINT) ->
      handler_correct h2 (clight_of SUBINT)
        (pre_of SUBINT) (P_error_of SUBINT) (P_halt_of SUBINT) (P_ccall_of SUBINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_MULINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of MULINT)
        (pre_of MULINT) (P_error_of MULINT) (P_halt_of MULINT) (P_ccall_of MULINT) ->
      handler_correct h2 (clight_of MULINT)
        (pre_of MULINT) (P_error_of MULINT) (P_halt_of MULINT) (P_ccall_of MULINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_DIVINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of DIVINT)
        (pre_of DIVINT) (P_error_of DIVINT) (P_halt_of DIVINT) (P_ccall_of DIVINT) ->
      handler_correct h2 (clight_of DIVINT)
        (pre_of DIVINT) (P_error_of DIVINT) (P_halt_of DIVINT) (P_ccall_of DIVINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_MODINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of MODINT)
        (pre_of MODINT) (P_error_of MODINT) (P_halt_of MODINT) (P_ccall_of MODINT) ->
      handler_correct h2 (clight_of MODINT)
        (pre_of MODINT) (P_error_of MODINT) (P_halt_of MODINT) (P_ccall_of MODINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_ANDINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of ANDINT)
        (pre_of ANDINT) (P_error_of ANDINT) (P_halt_of ANDINT) (P_ccall_of ANDINT) ->
      handler_correct h2 (clight_of ANDINT)
        (pre_of ANDINT) (P_error_of ANDINT) (P_halt_of ANDINT) (P_ccall_of ANDINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_ORINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of ORINT)
        (pre_of ORINT) (P_error_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT) ->
      handler_correct h2 (clight_of ORINT)
        (pre_of ORINT) (P_error_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_XORINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of XORINT)
        (pre_of XORINT) (P_error_of XORINT) (P_halt_of XORINT) (P_ccall_of XORINT) ->
      handler_correct h2 (clight_of XORINT)
        (pre_of XORINT) (P_error_of XORINT) (P_halt_of XORINT) (P_ccall_of XORINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_LSLINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of LSLINT)
        (pre_of LSLINT) (P_error_of LSLINT) (P_halt_of LSLINT) (P_ccall_of LSLINT) ->
      handler_correct h2 (clight_of LSLINT)
        (pre_of LSLINT) (P_error_of LSLINT) (P_halt_of LSLINT) (P_ccall_of LSLINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_LSRINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of LSRINT)
        (pre_of LSRINT) (P_error_of LSRINT) (P_halt_of LSRINT) (P_ccall_of LSRINT) ->
      handler_correct h2 (clight_of LSRINT)
        (pre_of LSRINT) (P_error_of LSRINT) (P_halt_of LSRINT) (P_ccall_of LSRINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_ASRINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of ASRINT)
        (pre_of ASRINT) (P_error_of ASRINT) (P_halt_of ASRINT) (P_ccall_of ASRINT) ->
      handler_correct h2 (clight_of ASRINT)
        (pre_of ASRINT) (P_error_of ASRINT) (P_halt_of ASRINT) (P_ccall_of ASRINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_EQ :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of EQ)
        (pre_of EQ) (P_error_of EQ) (P_halt_of EQ) (P_ccall_of EQ) ->
      handler_correct h2 (clight_of EQ)
        (pre_of EQ) (P_error_of EQ) (P_halt_of EQ) (P_ccall_of EQ) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_NEQ :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of NEQ)
        (pre_of NEQ) (P_error_of NEQ) (P_halt_of NEQ) (P_ccall_of NEQ) ->
      handler_correct h2 (clight_of NEQ)
        (pre_of NEQ) (P_error_of NEQ) (P_halt_of NEQ) (P_ccall_of NEQ) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_LTINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of LTINT)
        (pre_of LTINT) (P_error_of LTINT) (P_halt_of LTINT) (P_ccall_of LTINT) ->
      handler_correct h2 (clight_of LTINT)
        (pre_of LTINT) (P_error_of LTINT) (P_halt_of LTINT) (P_ccall_of LTINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_LEINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of LEINT)
        (pre_of LEINT) (P_error_of LEINT) (P_halt_of LEINT) (P_ccall_of LEINT) ->
      handler_correct h2 (clight_of LEINT)
        (pre_of LEINT) (P_error_of LEINT) (P_halt_of LEINT) (P_ccall_of LEINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_GTINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of GTINT)
        (pre_of GTINT) (P_error_of GTINT) (P_halt_of GTINT) (P_ccall_of GTINT) ->
      handler_correct h2 (clight_of GTINT)
        (pre_of GTINT) (P_error_of GTINT) (P_halt_of GTINT) (P_ccall_of GTINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_GEINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of GEINT)
        (pre_of GEINT) (P_error_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT) ->
      handler_correct h2 (clight_of GEINT)
        (pre_of GEINT) (P_error_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_OFFSETINT : forall z, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (OFFSETINT z))
        (pre_of (OFFSETINT z)) (P_error_of (OFFSETINT z)) (P_halt_of (OFFSETINT z)) (P_ccall_of (OFFSETINT z)) ->
      handler_correct h2 (clight_of (OFFSETINT z))
        (pre_of (OFFSETINT z)) (P_error_of (OFFSETINT z)) (P_halt_of (OFFSETINT z)) (P_ccall_of (OFFSETINT z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_OFFSETREF : forall z, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (OFFSETREF z))
        (pre_of (OFFSETREF z)) (P_error_of (OFFSETREF z)) (P_halt_of (OFFSETREF z)) (P_ccall_of (OFFSETREF z)) ->
      handler_correct h2 (clight_of (OFFSETREF z))
        (pre_of (OFFSETREF z)) (P_error_of (OFFSETREF z)) (P_halt_of (OFFSETREF z)) (P_ccall_of (OFFSETREF z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_ISINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of ISINT)
        (pre_of ISINT) (P_error_of ISINT) (P_halt_of ISINT) (P_ccall_of ISINT) ->
      handler_correct h2 (clight_of ISINT)
        (pre_of ISINT) (P_error_of ISINT) (P_halt_of ISINT) (P_ccall_of ISINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_GETMETHOD :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of GETMETHOD)
        (pre_of GETMETHOD) (P_error_of GETMETHOD) (P_halt_of GETMETHOD) (P_ccall_of GETMETHOD) ->
      handler_correct h2 (clight_of GETMETHOD)
        (pre_of GETMETHOD) (P_error_of GETMETHOD) (P_halt_of GETMETHOD) (P_ccall_of GETMETHOD) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_GETPUBMET : forall z, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (GETPUBMET z))
        (pre_of (GETPUBMET z)) (P_error_of (GETPUBMET z)) (P_halt_of (GETPUBMET z)) (P_ccall_of (GETPUBMET z)) ->
      handler_correct h2 (clight_of (GETPUBMET z))
        (pre_of (GETPUBMET z)) (P_error_of (GETPUBMET z)) (P_halt_of (GETPUBMET z)) (P_ccall_of (GETPUBMET z)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_GETDYNMET :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of GETDYNMET)
        (pre_of GETDYNMET) (P_error_of GETDYNMET) (P_halt_of GETDYNMET) (P_ccall_of GETDYNMET) ->
      handler_correct h2 (clight_of GETDYNMET)
        (pre_of GETDYNMET) (P_error_of GETDYNMET) (P_halt_of GETDYNMET) (P_ccall_of GETDYNMET) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_BEQ : forall z1 z2, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (BEQ z1 z2))
        (pre_of (BEQ z1 z2)) (P_error_of (BEQ z1 z2)) (P_halt_of (BEQ z1 z2)) (P_ccall_of (BEQ z1 z2)) ->
      handler_correct h2 (clight_of (BEQ z1 z2))
        (pre_of (BEQ z1 z2)) (P_error_of (BEQ z1 z2)) (P_halt_of (BEQ z1 z2)) (P_ccall_of (BEQ z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_BNEQ : forall z1 z2, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (BNEQ z1 z2))
        (pre_of (BNEQ z1 z2)) (P_error_of (BNEQ z1 z2)) (P_halt_of (BNEQ z1 z2)) (P_ccall_of (BNEQ z1 z2)) ->
      handler_correct h2 (clight_of (BNEQ z1 z2))
        (pre_of (BNEQ z1 z2)) (P_error_of (BNEQ z1 z2)) (P_halt_of (BNEQ z1 z2)) (P_ccall_of (BNEQ z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_BLTINT : forall z1 z2, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (BLTINT z1 z2))
        (pre_of (BLTINT z1 z2)) (P_error_of (BLTINT z1 z2)) (P_halt_of (BLTINT z1 z2)) (P_ccall_of (BLTINT z1 z2)) ->
      handler_correct h2 (clight_of (BLTINT z1 z2))
        (pre_of (BLTINT z1 z2)) (P_error_of (BLTINT z1 z2)) (P_halt_of (BLTINT z1 z2)) (P_ccall_of (BLTINT z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_BLEINT : forall z1 z2, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (BLEINT z1 z2))
        (pre_of (BLEINT z1 z2)) (P_error_of (BLEINT z1 z2)) (P_halt_of (BLEINT z1 z2)) (P_ccall_of (BLEINT z1 z2)) ->
      handler_correct h2 (clight_of (BLEINT z1 z2))
        (pre_of (BLEINT z1 z2)) (P_error_of (BLEINT z1 z2)) (P_halt_of (BLEINT z1 z2)) (P_ccall_of (BLEINT z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_BGTINT : forall z1 z2, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (BGTINT z1 z2))
        (pre_of (BGTINT z1 z2)) (P_error_of (BGTINT z1 z2)) (P_halt_of (BGTINT z1 z2)) (P_ccall_of (BGTINT z1 z2)) ->
      handler_correct h2 (clight_of (BGTINT z1 z2))
        (pre_of (BGTINT z1 z2)) (P_error_of (BGTINT z1 z2)) (P_halt_of (BGTINT z1 z2)) (P_ccall_of (BGTINT z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_BGEINT : forall z1 z2, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (BGEINT z1 z2))
        (pre_of (BGEINT z1 z2)) (P_error_of (BGEINT z1 z2)) (P_halt_of (BGEINT z1 z2)) (P_ccall_of (BGEINT z1 z2)) ->
      handler_correct h2 (clight_of (BGEINT z1 z2))
        (pre_of (BGEINT z1 z2)) (P_error_of (BGEINT z1 z2)) (P_halt_of (BGEINT z1 z2)) (P_ccall_of (BGEINT z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_ULTINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of ULTINT)
        (pre_of ULTINT) (P_error_of ULTINT) (P_halt_of ULTINT) (P_ccall_of ULTINT) ->
      handler_correct h2 (clight_of ULTINT)
        (pre_of ULTINT) (P_error_of ULTINT) (P_halt_of ULTINT) (P_ccall_of ULTINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_UGEINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of UGEINT)
        (pre_of UGEINT) (P_error_of UGEINT) (P_halt_of UGEINT) (P_ccall_of UGEINT) ->
      handler_correct h2 (clight_of UGEINT)
        (pre_of UGEINT) (P_error_of UGEINT) (P_halt_of UGEINT) (P_ccall_of UGEINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_BULTINT : forall z1 z2, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (BULTINT z1 z2))
        (pre_of (BULTINT z1 z2)) (P_error_of (BULTINT z1 z2)) (P_halt_of (BULTINT z1 z2)) (P_ccall_of (BULTINT z1 z2)) ->
      handler_correct h2 (clight_of (BULTINT z1 z2))
        (pre_of (BULTINT z1 z2)) (P_error_of (BULTINT z1 z2)) (P_halt_of (BULTINT z1 z2)) (P_ccall_of (BULTINT z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_BUGEINT : forall z1 z2, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (BUGEINT z1 z2))
        (pre_of (BUGEINT z1 z2)) (P_error_of (BUGEINT z1 z2)) (P_halt_of (BUGEINT z1 z2)) (P_ccall_of (BUGEINT z1 z2)) ->
      handler_correct h2 (clight_of (BUGEINT z1 z2))
        (pre_of (BUGEINT z1 z2)) (P_error_of (BUGEINT z1 z2)) (P_halt_of (BUGEINT z1 z2)) (P_ccall_of (BUGEINT z1 z2)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

Lemma unique_STOP :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of STOP)
        (pre_of STOP) (P_error_of STOP) (P_halt_of STOP) (P_ccall_of STOP) ->
      handler_correct h2 (clight_of STOP)
        (pre_of STOP) (P_error_of STOP) (P_halt_of STOP) (P_ccall_of STOP) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
Admitted.

(* Assemble into MetaSpec via fine-grained approach *)
Module FineGrained <: MetaSpecFineGrainedSpec.
  Definition unique_ACC := unique_ACC.
  Definition unique_PUSH := unique_PUSH.
  Definition unique_PUSHACC := unique_PUSHACC.
  Definition unique_POP := unique_POP.
  Definition unique_ASSIGN := unique_ASSIGN.
  Definition unique_ENVACC := unique_ENVACC.
  Definition unique_PUSHENVACC := unique_PUSHENVACC.
  Definition unique_PUSH_RETADDR := unique_PUSH_RETADDR.
  Definition unique_APPLY := unique_APPLY.
  Definition unique_APPLY1 := unique_APPLY1.
  Definition unique_APPLY2 := unique_APPLY2.
  Definition unique_APPLY3 := unique_APPLY3.
  Definition unique_APPTERM := unique_APPTERM.
  Definition unique_APPTERM1 := unique_APPTERM1.
  Definition unique_APPTERM2 := unique_APPTERM2.
  Definition unique_APPTERM3 := unique_APPTERM3.
  Definition unique_RETURN := unique_RETURN.
  Definition unique_RESTART := unique_RESTART.
  Definition unique_GRAB := unique_GRAB.
  Definition unique_CLOSURE := unique_CLOSURE.
  Definition unique_CLOSUREREC := unique_CLOSUREREC.
  Definition unique_OFFSETCLOSURE := unique_OFFSETCLOSURE.
  Definition unique_PUSHOFFSETCLOSURE := unique_PUSHOFFSETCLOSURE.
  Definition unique_GETGLOBAL := unique_GETGLOBAL.
  Definition unique_PUSHGETGLOBAL := unique_PUSHGETGLOBAL.
  Definition unique_GETGLOBALFIELD := unique_GETGLOBALFIELD.
  Definition unique_PUSHGETGLOBALFIELD := unique_PUSHGETGLOBALFIELD.
  Definition unique_SETGLOBAL := unique_SETGLOBAL.
  Definition unique_ATOM := unique_ATOM.
  Definition unique_PUSHATOM := unique_PUSHATOM.
  Definition unique_MAKEBLOCK := unique_MAKEBLOCK.
  Definition unique_MAKEBLOCK1 := unique_MAKEBLOCK1.
  Definition unique_MAKEBLOCK2 := unique_MAKEBLOCK2.
  Definition unique_MAKEBLOCK3 := unique_MAKEBLOCK3.
  Definition unique_MAKEFLOATBLOCK := unique_MAKEFLOATBLOCK.
  Definition unique_GETFIELD := unique_GETFIELD.
  Definition unique_GETFLOATFIELD := unique_GETFLOATFIELD.
  Definition unique_SETFIELD := unique_SETFIELD.
  Definition unique_SETFLOATFIELD := unique_SETFLOATFIELD.
  Definition unique_VECTLENGTH := unique_VECTLENGTH.
  Definition unique_GETVECTITEM := unique_GETVECTITEM.
  Definition unique_SETVECTITEM := unique_SETVECTITEM.
  Definition unique_GETBYTESCHAR := unique_GETBYTESCHAR.
  Definition unique_SETBYTESCHAR := unique_SETBYTESCHAR.
  Definition unique_GETSTRINGCHAR := unique_GETSTRINGCHAR.
  Definition unique_BRANCH := unique_BRANCH.
  Definition unique_BRANCHIF := unique_BRANCHIF.
  Definition unique_BRANCHIFNOT := unique_BRANCHIFNOT.
  Definition unique_SWITCH := unique_SWITCH.
  Definition unique_BOOLNOT := unique_BOOLNOT.
  Definition unique_PUSHTRAP := unique_PUSHTRAP.
  Definition unique_POPTRAP := unique_POPTRAP.
  Definition unique_RAISE := unique_RAISE.
  Definition unique_RERAISE := unique_RERAISE.
  Definition unique_RAISE_NOTRACE := unique_RAISE_NOTRACE.
  Definition unique_CHECK_SIGNALS := unique_CHECK_SIGNALS.
  Definition unique_C_CALL := unique_C_CALL.
  Definition unique_CONSTINT := unique_CONSTINT.
  Definition unique_PUSHCONSTINT := unique_PUSHCONSTINT.
  Definition unique_NEGINT := unique_NEGINT.
  Definition unique_ADDINT := unique_ADDINT.
  Definition unique_SUBINT := unique_SUBINT.
  Definition unique_MULINT := unique_MULINT.
  Definition unique_DIVINT := unique_DIVINT.
  Definition unique_MODINT := unique_MODINT.
  Definition unique_ANDINT := unique_ANDINT.
  Definition unique_ORINT := unique_ORINT.
  Definition unique_XORINT := unique_XORINT.
  Definition unique_LSLINT := unique_LSLINT.
  Definition unique_LSRINT := unique_LSRINT.
  Definition unique_ASRINT := unique_ASRINT.
  Definition unique_EQ := unique_EQ.
  Definition unique_NEQ := unique_NEQ.
  Definition unique_LTINT := unique_LTINT.
  Definition unique_LEINT := unique_LEINT.
  Definition unique_GTINT := unique_GTINT.
  Definition unique_GEINT := unique_GEINT.
  Definition unique_OFFSETINT := unique_OFFSETINT.
  Definition unique_OFFSETREF := unique_OFFSETREF.
  Definition unique_ISINT := unique_ISINT.
  Definition unique_GETMETHOD := unique_GETMETHOD.
  Definition unique_GETPUBMET := unique_GETPUBMET.
  Definition unique_GETDYNMET := unique_GETDYNMET.
  Definition unique_BEQ := unique_BEQ.
  Definition unique_BNEQ := unique_BNEQ.
  Definition unique_BLTINT := unique_BLTINT.
  Definition unique_BLEINT := unique_BLEINT.
  Definition unique_BGTINT := unique_BGTINT.
  Definition unique_BGEINT := unique_BGEINT.
  Definition unique_ULTINT := unique_ULTINT.
  Definition unique_UGEINT := unique_UGEINT.
  Definition unique_BULTINT := unique_BULTINT.
  Definition unique_BUGEINT := unique_BUGEINT.
  Definition unique_STOP := unique_STOP.
End FineGrained.

Module Assembled := MetaSpecFromFineGrained FineGrained.

(* Re-export for backward compatibility *)
Definition handler_unique_mod_errors := Assembled.handler_unique_mod_errors.