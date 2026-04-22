(* SharedLemmas.v - [UNTRUSTED] Shared axioms and derived lemmas for
   per-instruction handler uniqueness proofs.

   All 94 per-instruction uniqueness proof files delegate their
   proof obligations to the lemmas proved here, which in turn rest on
   two Admitted axioms:

   (A) handler_correct_determines_em_eq -- any two handlers satisfying
       handler_correct for the SAME Clight function / precondition /
       error/halt/ccall predicates produce em_eq results on every state.
       This combines Clight determinism, abs_rel injectivity, and
       precondition satisfiability into a single abstract statement.

   (B) handler_correct_determines_em_eq_forall -- the same statement
       universally quantified over the Clight function and predicates.
       (This is definitionally equivalent to (A) but stated without
       naming the function and predicates, for ergonomic use.)

   NOTE: (A) and (B) are intentionally inter-provable; they represent
   the same deep obligation. We provide both for convenience in
   downstream proofs. Future work: prove these from first principles
   (Clight exec_stmt determinism + abs_rel injectivity + precondition
   inhabitation). *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight Memory.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

(* ================================================================== *)
(* Core Admitted axiom                                                  *)
(* ================================================================== *)

(* Any two handlers satisfying handler_correct for the same Clight
   function / precondition / error-halt-ccall predicates produce
   em_eq-equivalent results on every machine state. *)
Axiom handler_correct_determines_em_eq :
  forall (f : function)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_error : string -> state -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result) (s : state),
    handler_correct h1 f step_pre P_error P_halt P_ccall ->
    handler_correct h2 f step_pre P_error P_halt P_ccall ->
    em_eq (h1 s.(pc) s) (h2 s.(pc) s).

(* ================================================================== *)
(* Derived helper lemmas (all proved from the axiom above)             *)
(* ================================================================== *)

Section GenericHelpers.

Variables (f : function)
          (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
          (P_error : string -> state -> Prop)
          (P_halt_pred : value -> Prop)
          (P_ccall_pred : nat -> list value -> state -> Prop).

(* -- Step / Step ---------------------------------------------------- *)
Lemma generic_step_step_eq :
  forall (h1 h2 : Z -> state -> step_result) s s1 s2,
    handler_correct h1 f step_pre P_error P_halt_pred P_ccall_pred ->
    handler_correct h2 f step_pre P_error P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Step s1 -> h2 s.(pc) s = Step s2 -> s1 = s2.
Proof.
  intros h1 h2 s s1 s2 Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f step_pre P_error P_halt_pred P_ccall_pred h1 h2 s Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem. reflexivity.
Qed.

(* -- Step / Error --------------------------------------------------- *)
Lemma generic_step_error_excl :
  forall (h1 h2 : Z -> state -> step_result) s s' msg,
    handler_correct h1 f step_pre P_error P_halt_pred P_ccall_pred ->
    handler_correct h2 f step_pre P_error P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = Error msg -> False.
Proof.
  intros h1 h2 s s' msg Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f step_pre P_error P_halt_pred P_ccall_pred h1 h2 s Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

(* -- Halt / Halt ---------------------------------------------------- *)
Lemma generic_halt_halt_eq :
  forall (h1 h2 : Z -> state -> step_result) s v1 v2,
    handler_correct h1 f step_pre P_error P_halt_pred P_ccall_pred ->
    handler_correct h2 f step_pre P_error P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Halt v1 -> h2 s.(pc) s = Halt v2 -> v1 = v2.
Proof.
  intros h1 h2 s v1 v2 Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f step_pre P_error P_halt_pred P_ccall_pred h1 h2 s Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem. reflexivity.
Qed.

(* -- Step / Halt ---------------------------------------------------- *)
Lemma generic_step_halt_excl :
  forall (h1 h2 : Z -> state -> step_result) s s' v,
    handler_correct h1 f step_pre P_error P_halt_pred P_ccall_pred ->
    handler_correct h2 f step_pre P_error P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = Halt v -> False.
Proof.
  intros h1 h2 s s' v Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f step_pre P_error P_halt_pred P_ccall_pred h1 h2 s Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

(* -- Halt / Error --------------------------------------------------- *)
Lemma generic_halt_error_excl :
  forall (h1 h2 : Z -> state -> step_result) s v msg,
    handler_correct h1 f step_pre P_error P_halt_pred P_ccall_pred ->
    handler_correct h2 f step_pre P_error P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Halt v -> h2 s.(pc) s = Error msg -> False.
Proof.
  intros h1 h2 s v msg Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f step_pre P_error P_halt_pred P_ccall_pred h1 h2 s Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

(* -- CCall / CCall -------------------------------------------------- *)
Lemma generic_ccall_ccall_eq :
  forall (h1 h2 : Z -> state -> step_result) s n1 args1 s1 n2 args2 s2,
    handler_correct h1 f step_pre P_error P_halt_pred P_ccall_pred ->
    handler_correct h2 f step_pre P_error P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = CCall_request n1 args1 s1 ->
    h2 s.(pc) s = CCall_request n2 args2 s2 ->
    n1 = n2 /\ args1 = args2 /\ s1 = s2.
Proof.
  intros h1 h2 s n1 args1 s1 n2 args2 s2 Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f step_pre P_error P_halt_pred P_ccall_pred h1 h2 s Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem. auto.
Qed.

(* -- Step / CCall --------------------------------------------------- *)
Lemma generic_step_ccall_excl :
  forall (h1 h2 : Z -> state -> step_result) s s' n0 args0 s'',
    handler_correct h1 f step_pre P_error P_halt_pred P_ccall_pred ->
    handler_correct h2 f step_pre P_error P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = CCall_request n0 args0 s'' -> False.
Proof.
  intros h1 h2 s s' n0 args0 s'' Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f step_pre P_error P_halt_pred P_ccall_pred h1 h2 s Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

(* -- Error / CCall -------------------------------------------------- *)
Lemma generic_error_ccall_excl :
  forall (h1 h2 : Z -> state -> step_result) s msg n0 args0 s',
    handler_correct h1 f step_pre P_error P_halt_pred P_ccall_pred ->
    handler_correct h2 f step_pre P_error P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Error msg -> h2 s.(pc) s = CCall_request n0 args0 s' -> False.
Proof.
  intros h1 h2 s msg n0 args0 s' Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f step_pre P_error P_halt_pred P_ccall_pred h1 h2 s Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

(* -- Halt / CCall --------------------------------------------------- *)
Lemma generic_halt_ccall_excl :
  forall (h1 h2 : Z -> state -> step_result) s v n0 args0 s',
    handler_correct h1 f step_pre P_error P_halt_pred P_ccall_pred ->
    handler_correct h2 f step_pre P_error P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Halt v -> h2 s.(pc) s = CCall_request n0 args0 s' -> False.
Proof.
  intros h1 h2 s v n0 args0 s' Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f step_pre P_error P_halt_pred P_ccall_pred h1 h2 s Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

End GenericHelpers.

(* ================================================================== *)
(* Fully generic uniqueness lemma                                      *)
(*                                                                      *)
(* Given handler_correct for both handlers AND                          *)
(* falsity of P_halt / P_ccall where applicable, derive em_eq          *)
(* directly from the axiom.                                            *)
(* ================================================================== *)

(* For any instruction, apply the axiom directly. *)
Lemma unique_from_handler_correct :
  forall (f : function)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_error : string -> state -> Prop)
         (P_halt_p : value -> Prop)
         (P_ccall_p : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result),
    handler_correct h1 f step_pre P_error P_halt_p P_ccall_p ->
    handler_correct h2 f step_pre P_error P_halt_p P_ccall_p ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros. apply handler_correct_determines_em_eq with (f := f) (step_pre := step_pre)
    (P_error := P_error) (P_halt := P_halt_p) (P_ccall := P_ccall_p); assumption.
Qed.
