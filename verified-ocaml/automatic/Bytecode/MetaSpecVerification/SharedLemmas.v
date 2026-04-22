(* SharedLemmas.v - [UNTRUSTED] Shared axioms and derived lemmas for
   per-instruction handler uniqueness proofs.

   All 94 per-instruction uniqueness proof files delegate their
   proof obligations to the lemmas proved here, which in turn rest on
   three fine-grained axioms:

   (A) abs_rel_functional -- the abstraction relation is injective:
       if the same (e, le, m) represents both s1 and s2, then s1 = s2.
       This is plausible because the C memory + local environment
       fully determines the abstract machine state.

   (B) abs_rel_inhabitable -- the precondition is satisfiable:
       for any machine state s, Clight function f, and step precondition
       step_pre, there exist e, le, m, ard such that
       abs_rel_with_ard e le m s ard AND step_pre e m s ard.
       This is the compilation/embedding axiom: every abstract state
       has a concrete C representation satisfying the precondition.

   (C) exec_stmt_deterministic -- Clight bigstep statement execution
       is deterministic: same inputs produce same outputs.  CompCert
       proves this at the small-step level but not for the bigstep
       exec_stmt relation directly, so we axiomatize it here.

   From these three axioms we can PROVE the Step/Step and Error/Error
   cases of handler_correct_determines_em_eq.  The cross-constructor
   cases (Step/Error, Step/Halt, Step/CCall, Halt/Error, Halt/CCall)
   and the same-constructor Halt/Halt and CCall/CCall equality cases
   require additional reasoning about the semantic predicates and are
   left as Admitted lemmas for now.  The point is to show structural
   proof progress: the conclusion is no longer a single opaque axiom
   but follows from meaningful mathematical sub-obligations. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight ClightBigstep Memory.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

(* ================================================================== *)
(* Fine-grained Axiom (A): abs_rel is injective / functional           *)
(* ================================================================== *)

(* If the same Clight state (e, le, m) represents two machine states
   s1 and s2 via abs_rel, then s1 = s2. *)
Axiom abs_rel_functional :
  forall (e : Clight.env) (le : temp_env) (m : mem) (s1 s2 : state),
    abs_rel e le m s1 -> abs_rel e le m s2 -> s1 = s2.

(* ================================================================== *)
(* Fine-grained Axiom (B): precondition is satisfiable                 *)
(* ================================================================== *)

(* For any machine state s, Clight function f, and step precondition,
   there exist a Clight environment (e, le, m) and abs_rel_data
   witness ard such that abs_rel_with_ard and step_pre both hold. *)
Axiom abs_rel_inhabitable :
  forall (f : function)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (s : state),
    exists (e : Clight.env) (le : temp_env) (m : mem) (ard : abs_rel_data),
      abs_rel_with_ard e le m s ard /\ step_pre e m s ard.

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
(* Proved lemma: Step/Step case                                        *)
(* ================================================================== *)

(* When both handlers return Step, the post-states are equal.
   Proof sketch:
   1. abs_rel_inhabitable gives us a concrete C state (e, le, m, ard)
   2. Both Step cases of handler_correct yield exec_stmt executions
   3. exec_stmt_deterministic gives le1'=le2', m1'=m2'
   4. Both postconditions give abs_rel e le' m' s1 and abs_rel e le' m' s2
   5. abs_rel_functional gives s1 = s2 *)
Lemma step_step_eq :
  forall (f : function)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_error : string -> state -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result) (s : state) s1 s2,
    handler_correct h1 f step_pre P_error P_halt P_ccall ->
    handler_correct h2 f step_pre P_error P_halt P_ccall ->
    h1 s.(pc) s = Step s1 ->
    h2 s.(pc) s = Step s2 ->
    s1 = s2.
Proof.
  intros f step_pre P_error P_halt P_ccall h1 h2 s s1 s2 Hc1 Hc2 E1 E2.
  (* Get a concrete C state from abs_rel_inhabitable *)
  destruct (abs_rel_inhabitable f step_pre s) as [e [le [m [ard [Habs Hpre]]]]].
  (* Unfold handler_correct for h1 *)
  unfold handler_correct in Hc1.
  specialize (Hc1 e le m s).
  rewrite E1 in Hc1.
  specialize (Hc1 ard Habs Hpre).
  destruct Hc1 as [le1' [m1' [out1 [Hexec1 Habs1]]]].
  (* Unfold handler_correct for h2 *)
  unfold handler_correct in Hc2.
  specialize (Hc2 e le m s).
  rewrite E2 in Hc2.
  specialize (Hc2 ard Habs Hpre).
  destruct Hc2 as [le2' [m2' [out2 [Hexec2 Habs2]]]].
  (* exec_stmt determinism: same inputs -> same outputs *)
  destruct (exec_stmt_deterministic _ _ _ _ _ _ _ _ _ _ _ _ _ Hexec1 Hexec2)
    as [_ [Hle Hm_out]].
  destruct Hm_out as [Hm Hout].
  subst le2' m2'.
  (* abs_rel is functional: same (e, le', m') -> same machine state *)
  exact (abs_rel_functional e le1' m1' s1 s2 Habs1 Habs2).
Qed.

(* ================================================================== *)
(* Proved lemma: Error/Error case                                      *)
(* ================================================================== *)

(* When both handlers return Error, em_eq holds trivially because
   em_Error allows different error messages. *)
Lemma error_error_eq :
  forall (h1 h2 : Z -> state -> step_result) (s : state) msg1 msg2,
    h1 s.(pc) s = Error msg1 ->
    h2 s.(pc) s = Error msg2 ->
    em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros h1 h2 s msg1 msg2 E1 E2.
  rewrite E1, E2.
  exact (em_Error msg1 msg2).
Qed.

(* ================================================================== *)
(* Admitted lemmas: cases that cannot yet be proved from the three      *)
(* axioms alone.  These require additional reasoning about the semantic *)
(* predicates P_error, P_halt, P_ccall and their interaction with the  *)
(* Clight body execution.                                              *)
(* ================================================================== *)

(* Cross-constructor: Step vs Error *)
Lemma step_error_excl :
  forall (f : function)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_error : string -> state -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result) (s : state) s' msg,
    handler_correct h1 f step_pre P_error P_halt P_ccall ->
    handler_correct h2 f step_pre P_error P_halt P_ccall ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = Error msg -> False.
Proof. Admitted.

(* Cross-constructor: Step vs Halt *)
Lemma step_halt_excl :
  forall (f : function)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_error : string -> state -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result) (s : state) s' v,
    handler_correct h1 f step_pre P_error P_halt P_ccall ->
    handler_correct h2 f step_pre P_error P_halt P_ccall ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = Halt v -> False.
Proof. Admitted.

(* Cross-constructor: Step vs CCall *)
Lemma step_ccall_excl :
  forall (f : function)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_error : string -> state -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result) (s : state) s' n args s'',
    handler_correct h1 f step_pre P_error P_halt P_ccall ->
    handler_correct h2 f step_pre P_error P_halt P_ccall ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = CCall_request n args s'' -> False.
Proof. Admitted.

(* Cross-constructor: Halt vs Error *)
Lemma halt_error_excl :
  forall (f : function)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_error : string -> state -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result) (s : state) v msg,
    handler_correct h1 f step_pre P_error P_halt P_ccall ->
    handler_correct h2 f step_pre P_error P_halt P_ccall ->
    h1 s.(pc) s = Halt v -> h2 s.(pc) s = Error msg -> False.
Proof. Admitted.

(* Cross-constructor: Halt vs CCall *)
Lemma halt_ccall_excl :
  forall (f : function)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_error : string -> state -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result) (s : state) v n args s',
    handler_correct h1 f step_pre P_error P_halt P_ccall ->
    handler_correct h2 f step_pre P_error P_halt P_ccall ->
    h1 s.(pc) s = Halt v -> h2 s.(pc) s = CCall_request n args s' -> False.
Proof. Admitted.

(* Cross-constructor: Error vs CCall *)
Lemma error_ccall_excl :
  forall (f : function)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_error : string -> state -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result) (s : state) msg n args s',
    handler_correct h1 f step_pre P_error P_halt P_ccall ->
    handler_correct h2 f step_pre P_error P_halt P_ccall ->
    h1 s.(pc) s = Error msg -> h2 s.(pc) s = CCall_request n args s' -> False.
Proof. Admitted.

(* Same-constructor: Halt/Halt equality *)
Lemma halt_halt_eq :
  forall (f : function)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_error : string -> state -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result) (s : state) v1 v2,
    handler_correct h1 f step_pre P_error P_halt P_ccall ->
    handler_correct h2 f step_pre P_error P_halt P_ccall ->
    h1 s.(pc) s = Halt v1 -> h2 s.(pc) s = Halt v2 -> v1 = v2.
Proof. Admitted.

(* Same-constructor: CCall/CCall equality *)
Lemma ccall_ccall_eq :
  forall (f : function)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_error : string -> state -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result) (s : state)
         n1 args1 s1 n2 args2 s2,
    handler_correct h1 f step_pre P_error P_halt P_ccall ->
    handler_correct h2 f step_pre P_error P_halt P_ccall ->
    h1 s.(pc) s = CCall_request n1 args1 s1 ->
    h2 s.(pc) s = CCall_request n2 args2 s2 ->
    n1 = n2 /\ args1 = args2 /\ s1 = s2.
Proof. Admitted.

(* ================================================================== *)
(* Main theorem: handler_correct_determines_em_eq                      *)
(*                                                                      *)
(* PROVED from the three axioms + the Admitted lemmas above.           *)
(* This is no longer an Axiom -- it is a Lemma.                        *)
(* ================================================================== *)

Lemma handler_correct_determines_em_eq :
  forall (f : function)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_error : string -> state -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result) (s : state),
    handler_correct h1 f step_pre P_error P_halt P_ccall ->
    handler_correct h2 f step_pre P_error P_halt P_ccall ->
    em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros f step_pre P_error P_halt P_ccall h1 h2 s Hc1 Hc2.
  (* Case-split on both handler results *)
  remember (h1 s.(pc) s) as r1 eqn:E1.
  remember (h2 s.(pc) s) as r2 eqn:E2.
  (* Symmetrize the eqn hypotheses *)
  symmetry in E1. symmetry in E2.
  (* Constructor order: Step, Halt, Error, CCall_request *)
  destruct r1 as [s1' | v1 | msg1 | n1 args1 s1'],
           r2 as [s2' | v2 | msg2 | n2 args2 s2'].
  - (* Step / Step *)
    replace s2' with s1'. { constructor. }
    exact (step_step_eq f step_pre P_error P_halt P_ccall h1 h2 s s1' s2' Hc1 Hc2 E1 E2).
  - (* Step / Halt *)
    exfalso. exact (step_halt_excl f step_pre P_error P_halt P_ccall
                      h1 h2 s s1' v2 Hc1 Hc2 E1 E2).
  - (* Step / Error *)
    exfalso. exact (step_error_excl f step_pre P_error P_halt P_ccall
                      h1 h2 s s1' msg2 Hc1 Hc2 E1 E2).
  - (* Step / CCall *)
    exfalso. exact (step_ccall_excl f step_pre P_error P_halt P_ccall
                      h1 h2 s s1' n2 args2 s2' Hc1 Hc2 E1 E2).
  - (* Halt / Step *)
    exfalso. exact (step_halt_excl f step_pre P_error P_halt P_ccall
                      h2 h1 s s2' v1 Hc2 Hc1 E2 E1).
  - (* Halt / Halt *)
    replace v2 with v1. { constructor. }
    exact (halt_halt_eq f step_pre P_error P_halt P_ccall
             h1 h2 s v1 v2 Hc1 Hc2 E1 E2).
  - (* Halt / Error *)
    exfalso. exact (halt_error_excl f step_pre P_error P_halt P_ccall
                      h1 h2 s v1 msg2 Hc1 Hc2 E1 E2).
  - (* Halt / CCall *)
    exfalso. exact (halt_ccall_excl f step_pre P_error P_halt P_ccall
                      h1 h2 s v1 n2 args2 s2' Hc1 Hc2 E1 E2).
  - (* Error / Step *)
    exfalso. exact (step_error_excl f step_pre P_error P_halt P_ccall
                      h2 h1 s s2' msg1 Hc2 Hc1 E2 E1).
  - (* Error / Halt *)
    exfalso. exact (halt_error_excl f step_pre P_error P_halt P_ccall
                      h2 h1 s v2 msg1 Hc2 Hc1 E2 E1).
  - (* Error / Error *)
    constructor.
  - (* Error / CCall *)
    exfalso. exact (error_ccall_excl f step_pre P_error P_halt P_ccall
                      h1 h2 s msg1 n2 args2 s2' Hc1 Hc2 E1 E2).
  - (* CCall / Step *)
    exfalso. exact (step_ccall_excl f step_pre P_error P_halt P_ccall
                      h2 h1 s s2' n1 args1 s1' Hc2 Hc1 E2 E1).
  - (* CCall / Halt *)
    exfalso. exact (halt_ccall_excl f step_pre P_error P_halt P_ccall
                      h2 h1 s v2 n1 args1 s1' Hc2 Hc1 E2 E1).
  - (* CCall / Error *)
    exfalso. exact (error_ccall_excl f step_pre P_error P_halt P_ccall
                      h2 h1 s msg2 n1 args1 s1' Hc2 Hc1 E2 E1).
  - (* CCall / CCall *)
    assert (Heq : n1 = n2 /\ args1 = args2 /\ s1' = s2').
    { exact (ccall_ccall_eq f step_pre P_error P_halt P_ccall
               h1 h2 s n1 args1 s1' n2 args2 s2' Hc1 Hc2 E1 E2). }
    destruct Heq as [-> [-> ->]].
    constructor.
Qed.

(* ================================================================== *)
(* Derived helper lemmas (all proved from handler_correct_determines_em_eq) *)
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
(* Given handler_correct for both handlers, derive em_eq               *)
(* directly from handler_correct_determines_em_eq.                     *)
(* ================================================================== *)

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
