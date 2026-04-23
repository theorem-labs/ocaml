(* GETVECTITEM_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for GETVECTITEM. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.

Lemma unique_GETVECTITEM :
  forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of GETVECTITEM)
        (pre_of GETVECTITEM) (P_error_of GETVECTITEM) (P_halt_of GETVECTITEM) (P_ccall_of GETVECTITEM) ->
      handler_correct h2 (clight_of GETVECTITEM)
        (pre_of GETVECTITEM) (P_error_of GETVECTITEM) (P_halt_of GETVECTITEM) (P_ccall_of GETVECTITEM) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros h1 h2 Hcorr1 Hcorr2 s.
  exact (unique_from_handler_correct
    (clight_of GETVECTITEM) (pre_of GETVECTITEM)
    (P_error_of GETVECTITEM) (P_halt_of GETVECTITEM) (P_ccall_of GETVECTITEM)
    h1 h2 Hcorr1 Hcorr2 s).
Qed.
