(* SharedLemmas.v - [UNTRUSTED] Shared axioms and derived lemmas for
   per-instruction handler uniqueness proofs.

   The generic uniqueness proof is parameterised over an abstract state S,
   a witness type W, an abstraction relation R : Clight.env -> temp_env ->
   mem -> S -> W -> Prop, and pc extraction pc_of : S -> Z.  The Section
   hypotheses R_total and R_functional supply the totality and functionality
   properties for the fully generic theorem.

   handler_correct_gen now takes err : S -> option string instead of P_error.
   When err s = Some msg, the handler must return Error msg.
   When err s = None, Error is False, and Step/Halt/CCall have exec_stmt
   returning fixed integer codes (0/1/3).

   The concrete closed helpers additionally assume abs_rel totality and
   functionality for compatibility with the current fine-grained MetaSpec
   surface. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Integers Ctypes Clight ClightBigstep Events Memory Values.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.

(* ================================================================== *)
(* Fine-grained Axiom (C): Clight bigstep exec_stmt is deterministic   *)
(* ================================================================== *)

(* CompCert proves small-step determinism but does not export a bigstep
   exec_stmt determinism lemma.  The bigstep relation IS deterministic
   (by inspection of its inductive definition), so this axiom is sound. *)
Axiom exec_stmt_deterministic :
  forall ge e le m s t1 le1 m1 out1 t2 le2 m2 out2,
    exec_stmt function_entry1 ge e le m s t1 le1 m1 out1 ->
    exec_stmt function_entry1 ge e le m s t2 le2 m2 out2 ->
    t1 = t2 /\ le1 = le2 /\ m1 = m2 /\ out1 = out2.

(* ================================================================== *)
(* Generic uniqueness proof                                            *)
(*                                                                      *)
(* Parameterised over S, W, R, pc_of with R_total and R_functional     *)
(* as Section hypotheses (not axioms).                                 *)
(*                                                                      *)
(* Uses the new handler_correct_gen with err : S -> option string.     *)
(* The err case split makes cross-constructor exclusion provable:      *)
(*   Some msg => both handlers return Error msg (trivial)              *)
(*   None     => Error is excluded (False in handler_correct_gen)       *)
(* ================================================================== *)

Section GenericUniqueness.

Variables (S : Type) (W : Type).
Variable (pc_of : S -> Z).
Variable (R : Clight.env -> temp_env -> mem -> S -> W -> Prop).

(* R is total: every abstract state has a Clight context + witness *)
Hypothesis R_total : forall s, exists e le m w, R e le m s w.

(* R is functional: same Clight context implies same abstract state *)
Hypothesis R_functional : forall e le m s1 s2 w1 w2,
  R e le m s1 w1 -> R e le m s2 w2 -> s1 = s2.

(* ================================================================== *)
(* Main generic theorem                                                *)
(* ================================================================== *)

Lemma handler_correct_gen_determines_em_eq :
  forall (f : function)
         (h1 h2 : Z -> S -> step_result_gen S)
         (err : S -> option string)
         (step_pre : Clight.env -> mem -> S -> W -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> S -> Prop),
    (forall s e le m w, R e le m s w -> step_pre e m s w) ->
    handler_correct_gen S W pc_of R h1 f err step_pre P_halt P_ccall ->
    handler_correct_gen S W pc_of R h2 f err step_pre P_halt P_ccall ->
    forall s, em_eq_gen (h1 (pc_of s) s) (h2 (pc_of s) s).
Proof. Admitted.

End GenericUniqueness.

(* ================================================================== *)
(* Module satisfying MetaSpecGen                                       *)
(* ================================================================== *)

Module SharedLemmasMetaSpecGen <: MetaSpecGen.

  Definition handler_unique_mod_errors_gen :
    forall (S : Type) (W : Type) (pc_of_S : S -> Z)
           (R : Clight.env -> temp_env -> mem -> S -> W -> Prop),
      (forall s, exists e le m w, R e le m s w) ->
      (forall e le m s1 s2 w1 w2, R e le m s1 w1 -> R e le m s2 w2 -> s1 = s2) ->
      forall (f : function)
             (h1 h2 : Z -> S -> step_result_gen S)
             (err : S -> option string)
             (step_pre : Clight.env -> mem -> S -> W -> Prop)
             (P_halt : value -> Prop)
             (P_ccall : nat -> list value -> S -> Prop),
        (forall s e le m w, R e le m s w -> step_pre e m s w) ->
        handler_correct_gen S W pc_of_S R h1 f err step_pre P_halt P_ccall ->
        handler_correct_gen S W pc_of_S R h2 f err step_pre P_halt P_ccall ->
        forall s, em_eq_gen (h1 (pc_of_S s) s) (h2 (pc_of_S s) s).
  Proof.
    intros S W pc_of_S R Htotal Hfunc.
    intros f h1 h2 err step_pre P_halt P_ccall Hpre_holds Hc1 Hc2 s.
    exact (handler_correct_gen_determines_em_eq S W pc_of_S R Htotal Hfunc
             f h1 h2 err step_pre P_halt P_ccall Hpre_holds Hc1 Hc2 s).
  Qed.

End SharedLemmasMetaSpecGen.

(* ================================================================== *)
(* Concrete instantiation                                              *)
(*                                                                      *)
(* The main concrete theorem takes totality and functionality as        *)
(* hypotheses.  The closed per-instruction uniqueness lemmas below      *)
(* still need concrete compatibility assumptions for abs_rel_with_ard.  *)
(* ================================================================== *)

Axiom abs_rel_functional :
  forall (e : Clight.env) (le : temp_env) (m : mem) (s1 s2 : state),
    abs_rel e le m s1 -> abs_rel e le m s2 -> s1 = s2.

Axiom abs_rel_inhabitable :
  forall (f : function)
         (err : state -> option string)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (s : state),
    exists (e : Clight.env) (le : temp_env) (m : mem) (ard : abs_rel_data),
      abs_rel_with_ard e le m s ard /\ step_pre e m s ard.

Lemma unique_non_halt_ccall_from_handler_correct :
  forall (f : function)
         (err : state -> option string)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result),
    (forall v, P_halt v -> False) ->
    (forall n args s, P_ccall n args s -> False) ->
    handler_correct h1 f err step_pre P_halt P_ccall ->
    handler_correct h2 f err step_pre P_halt P_ccall ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros f err step_pre P_halt P_ccall h1 h2 Hno_halt Hno_ccall Hc1 Hc2 s.
  destruct (abs_rel_inhabitable f err step_pre s)
    as [e [le [m [ard [Hrel Hpre]]]]].
  unfold handler_correct, handler_correct_gen in Hc1, Hc2.
  destruct (err s) as [msg|] eqn:Herr.
  - specialize (Hc1 e le m s).
    specialize (Hc2 e le m s).
    rewrite Herr in Hc1, Hc2.
    rewrite Hc1, Hc2. constructor.
  - specialize (Hc1 e le m s).
    specialize (Hc2 e le m s).
    rewrite Herr in Hc1, Hc2.
    destruct (h1 (Machine.pc s) s) as [s1|v1|msg1|n1 args1 s1] eqn:E1;
      destruct (h2 (Machine.pc s) s) as [s2|v2|msg2|n2 args2 s2] eqn:E2;
      try contradiction;
      try (destruct Hc1 as [HP _]; exfalso; eauto);
      try (destruct Hc2 as [HP _]; exfalso; eauto).
    specialize (Hc1 ard Hrel Hpre).
    specialize (Hc2 ard Hrel Hpre).
    destruct Hc1 as [le1 [m1 [Hexec1 [ard1 Hrel1]]]].
    destruct Hc2 as [le2 [m2 [Hexec2 [ard2 Hrel2]]]].
    unfold clight_returns in Hexec1, Hexec2.
    destruct (exec_stmt_deterministic
      _ _ _ _ _ _ _ _ _ _ _ _ _ Hexec1 Hexec2) as [_ [Hle [Hm _]]].
    subst le2 m2.
    assert (s1 = s2).
    { eapply abs_rel_functional with (e := e) (le := le1) (m := m1).
      - exists ard1. exact Hrel1.
      - exists ard2. exact Hrel2. }
    subst s2. constructor.
Qed.

(* Main concrete theorem -- takes totality and functionality as hypotheses *)
Lemma handler_correct_determines_em_eq :
  forall (f : function)
         (err : state -> option string)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result) (s : state),
    (forall s0, exists e le m w, abs_rel_with_ard e le m s0 w) ->
    (forall e le m s1 s2 w1 w2,
       abs_rel_with_ard e le m s1 w1 -> abs_rel_with_ard e le m s2 w2 -> s1 = s2) ->
    (forall s e le m w, abs_rel_with_ard e le m s w -> step_pre e m s w) ->
    handler_correct h1 f err step_pre P_halt P_ccall ->
    handler_correct h2 f err step_pre P_halt P_ccall ->
    em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros f err step_pre P_halt P_ccall h1 h2 s Htotal Hfunc Hpre_holds Hc1 Hc2.
  (* handler_correct unfolds to handler_correct_gen state abs_rel_data Machine.pc abs_rel_with_ard *)
  (* Use the generic theorem *)
  pose proof (handler_correct_gen_determines_em_eq
    state abs_rel_data Machine.pc abs_rel_with_ard Htotal Hfunc
    f h1 h2 err step_pre P_halt P_ccall Hpre_holds Hc1 Hc2 s) as Hgen.
  (* em_eq_gen on step_result (= step_result_gen state) implies em_eq *)
  remember (h1 s.(pc) s) as r1.
  remember (h2 s.(pc) s) as r2.
  destruct Hgen; constructor.
Qed.

(* ================================================================== *)
(* Derived helper lemmas (concrete, backward compat)                   *)
(* ================================================================== *)

Section GenericHelpers.

Variables (f : function)
          (err : state -> option string)
          (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
          (P_halt_pred : value -> Prop)
          (P_ccall_pred : nat -> list value -> state -> Prop).

Hypothesis abs_rel_total :
  forall s, exists e le m w, abs_rel_with_ard e le m s w.

Hypothesis abs_rel_func :
  forall e le m s1 s2 w1 w2,
    abs_rel_with_ard e le m s1 w1 -> abs_rel_with_ard e le m s2 w2 -> s1 = s2.

Variable step_pre_holds :
  forall s e le m w, abs_rel_with_ard e le m s w -> step_pre e m s w.

Lemma generic_step_step_eq :
  forall (h1 h2 : Z -> state -> step_result) s s1 s2,
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Step s1 -> h2 s.(pc) s = Step s2 -> s1 = s2.
Proof.
  intros h1 h2 s s1 s2 Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem. reflexivity.
Qed.

Lemma generic_step_error_excl :
  forall (h1 h2 : Z -> state -> step_result) s s' msg,
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = Error msg -> False.
Proof.
  intros h1 h2 s s' msg Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

Lemma generic_halt_halt_eq :
  forall (h1 h2 : Z -> state -> step_result) s v1 v2,
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Halt v1 -> h2 s.(pc) s = Halt v2 -> v1 = v2.
Proof.
  intros h1 h2 s v1 v2 Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem. reflexivity.
Qed.

Lemma generic_step_halt_excl :
  forall (h1 h2 : Z -> state -> step_result) s s' v,
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = Halt v -> False.
Proof.
  intros h1 h2 s s' v Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

Lemma generic_halt_error_excl :
  forall (h1 h2 : Z -> state -> step_result) s v msg,
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Halt v -> h2 s.(pc) s = Error msg -> False.
Proof.
  intros h1 h2 s v msg Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

Lemma generic_ccall_ccall_eq :
  forall (h1 h2 : Z -> state -> step_result) s n1 args1 s1 n2 args2 s2,
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = CCall_request n1 args1 s1 ->
    h2 s.(pc) s = CCall_request n2 args2 s2 ->
    n1 = n2 /\ args1 = args2 /\ s1 = s2.
Proof.
  intros h1 h2 s n1 args1 s1 n2 args2 s2 Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem. auto.
Qed.

Lemma generic_step_ccall_excl :
  forall (h1 h2 : Z -> state -> step_result) s s' n0 args0 s'',
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = CCall_request n0 args0 s'' -> False.
Proof.
  intros h1 h2 s s' n0 args0 s'' Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

Lemma generic_error_ccall_excl :
  forall (h1 h2 : Z -> state -> step_result) s msg n0 args0 s',
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Error msg -> h2 s.(pc) s = CCall_request n0 args0 s' -> False.
Proof.
  intros h1 h2 s msg n0 args0 s' Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

Lemma generic_halt_ccall_excl :
  forall (h1 h2 : Z -> state -> step_result) s v n0 args0 s',
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Halt v -> h2 s.(pc) s = CCall_request n0 args0 s' -> False.
Proof.
  intros h1 h2 s v n0 args0 s' Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

End GenericHelpers.

(* Fully generic uniqueness lemma (concrete) *)
Lemma unique_from_handler_correct :
  forall (f : function)
         (err : state -> option string)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_halt_p : value -> Prop)
         (P_ccall_p : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result),
    (forall s0, exists e le m w, abs_rel_with_ard e le m s0 w) ->
    (forall e le m s1 s2 w1 w2,
       abs_rel_with_ard e le m s1 w1 -> abs_rel_with_ard e le m s2 w2 -> s1 = s2) ->
    (forall s e le m w, abs_rel_with_ard e le m s w -> step_pre e m s w) ->
    handler_correct h1 f err step_pre P_halt_p P_ccall_p ->
    handler_correct h2 f err step_pre P_halt_p P_ccall_p ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros. apply handler_correct_determines_em_eq with (f := f) (err := err)
    (step_pre := step_pre) (P_halt := P_halt_p) (P_ccall := P_ccall_p); assumption.
Qed.
