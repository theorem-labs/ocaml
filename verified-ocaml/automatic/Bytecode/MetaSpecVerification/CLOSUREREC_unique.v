(* CLOSUREREC_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for CLOSUREREC. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.

Lemma unique_CLOSUREREC :
  forall nfuncs nvars code_offsets,
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (CLOSUREREC nfuncs nvars code_offsets))
        (error_message_of (CLOSUREREC nfuncs nvars code_offsets))
        (pre_of (CLOSUREREC nfuncs nvars code_offsets)) (P_halt_of (CLOSUREREC nfuncs nvars code_offsets)) (P_ccall_of (CLOSUREREC nfuncs nvars code_offsets)) ->
      handler_correct h2 (clight_of (CLOSUREREC nfuncs nvars code_offsets))
        (error_message_of (CLOSUREREC nfuncs nvars code_offsets))
        (pre_of (CLOSUREREC nfuncs nvars code_offsets)) (P_halt_of (CLOSUREREC nfuncs nvars code_offsets)) (P_ccall_of (CLOSUREREC nfuncs nvars code_offsets)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof. Admitted.
