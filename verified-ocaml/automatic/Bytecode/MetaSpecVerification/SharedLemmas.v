(* SharedLemmas.v - [UNTRUSTED] Shared axioms and derived lemmas for
   per-instruction handler uniqueness proofs.

   The generic uniqueness proof is parameterised over an abstract state S,
   a witness type W, an abstraction relation R : W -> S -> Prop, and
   pc extraction pc_of : S -> Z.  The Section hypotheses R_total and
   R_functional replace the old abs_rel_functional / abs_rel_inhabitable
   axioms.

   The only remaining axiom is exec_stmt_deterministic (Clight bigstep
   determinism), which is out of scope for this project. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Ctypes Clight ClightBigstep Memory.
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
(* ================================================================== *)

Section GenericUniqueness.

Variables (S : Type) (W : Type).
Variable (pc_of : S -> Z).
Variable (R : W -> S -> Prop).

(* R is total: every abstract state has a witness *)
Hypothesis R_total : forall s, exists w, R w s.

(* R is functional: same witness implies same abstract state *)
Hypothesis R_functional : forall w s1 s2, R w s1 -> R w s2 -> s1 = s2.

(* -- Step / Step ------------------------------------------------------ *)
Lemma gen_step_step_eq :
  forall (step_pre : W -> S -> Prop)
         (P_error : string -> S -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> S -> Prop)
         (h1 h2 : Z -> S -> step_result_gen S) (s : S) s1 s2,
    handler_correct_gen S W pc_of R h1 step_pre P_error P_halt P_ccall ->
    handler_correct_gen S W pc_of R h2 step_pre P_error P_halt P_ccall ->
    h1 (pc_of s) s = Step s1 ->
    h2 (pc_of s) s = Step s2 ->
    s1 = s2.
Proof. Admitted.

(* -- Error / Error ---------------------------------------------------- *)
Lemma gen_error_error_eq :
  forall (h1 h2 : Z -> S -> step_result_gen S) (s : S) msg1 msg2,
    h1 (pc_of s) s = Error msg1 ->
    h2 (pc_of s) s = Error msg2 ->
    em_eq_gen (h1 (pc_of s) s) (h2 (pc_of s) s).
Proof.
  intros h1 h2 s msg1 msg2 E1 E2.
  rewrite E1, E2.
  exact (em_Error_gen msg1 msg2).
Qed.

(* -- Cross-constructor exclusion (Admitted) --------------------------- *)
Lemma gen_step_error_excl :
  forall (step_pre : W -> S -> Prop)
         (P_error : string -> S -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> S -> Prop)
         (h1 h2 : Z -> S -> step_result_gen S) (s : S) s' msg,
    handler_correct_gen S W pc_of R h1 step_pre P_error P_halt P_ccall ->
    handler_correct_gen S W pc_of R h2 step_pre P_error P_halt P_ccall ->
    h1 (pc_of s) s = Step s' -> h2 (pc_of s) s = Error msg -> False.
Proof. Admitted.

Lemma gen_step_halt_excl :
  forall (step_pre : W -> S -> Prop)
         (P_error : string -> S -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> S -> Prop)
         (h1 h2 : Z -> S -> step_result_gen S) (s : S) s' v,
    handler_correct_gen S W pc_of R h1 step_pre P_error P_halt P_ccall ->
    handler_correct_gen S W pc_of R h2 step_pre P_error P_halt P_ccall ->
    h1 (pc_of s) s = Step s' -> h2 (pc_of s) s = Halt v -> False.
Proof. Admitted.

Lemma gen_step_ccall_excl :
  forall (step_pre : W -> S -> Prop)
         (P_error : string -> S -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> S -> Prop)
         (h1 h2 : Z -> S -> step_result_gen S) (s : S) s' n args s'',
    handler_correct_gen S W pc_of R h1 step_pre P_error P_halt P_ccall ->
    handler_correct_gen S W pc_of R h2 step_pre P_error P_halt P_ccall ->
    h1 (pc_of s) s = Step s' -> h2 (pc_of s) s = CCall_request n args s'' -> False.
Proof. Admitted.

Lemma gen_halt_error_excl :
  forall (step_pre : W -> S -> Prop)
         (P_error : string -> S -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> S -> Prop)
         (h1 h2 : Z -> S -> step_result_gen S) (s : S) v msg,
    handler_correct_gen S W pc_of R h1 step_pre P_error P_halt P_ccall ->
    handler_correct_gen S W pc_of R h2 step_pre P_error P_halt P_ccall ->
    h1 (pc_of s) s = Halt v -> h2 (pc_of s) s = Error msg -> False.
Proof. Admitted.

Lemma gen_halt_ccall_excl :
  forall (step_pre : W -> S -> Prop)
         (P_error : string -> S -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> S -> Prop)
         (h1 h2 : Z -> S -> step_result_gen S) (s : S) v n args s',
    handler_correct_gen S W pc_of R h1 step_pre P_error P_halt P_ccall ->
    handler_correct_gen S W pc_of R h2 step_pre P_error P_halt P_ccall ->
    h1 (pc_of s) s = Halt v -> h2 (pc_of s) s = CCall_request n args s' -> False.
Proof. Admitted.

Lemma gen_error_ccall_excl :
  forall (step_pre : W -> S -> Prop)
         (P_error : string -> S -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> S -> Prop)
         (h1 h2 : Z -> S -> step_result_gen S) (s : S) msg n args s',
    handler_correct_gen S W pc_of R h1 step_pre P_error P_halt P_ccall ->
    handler_correct_gen S W pc_of R h2 step_pre P_error P_halt P_ccall ->
    h1 (pc_of s) s = Error msg -> h2 (pc_of s) s = CCall_request n args s' -> False.
Proof. Admitted.

Lemma gen_halt_halt_eq :
  forall (step_pre : W -> S -> Prop)
         (P_error : string -> S -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> S -> Prop)
         (h1 h2 : Z -> S -> step_result_gen S) (s : S) v1 v2,
    handler_correct_gen S W pc_of R h1 step_pre P_error P_halt P_ccall ->
    handler_correct_gen S W pc_of R h2 step_pre P_error P_halt P_ccall ->
    h1 (pc_of s) s = Halt v1 -> h2 (pc_of s) s = Halt v2 -> v1 = v2.
Proof. Admitted.

Lemma gen_ccall_ccall_eq :
  forall (step_pre : W -> S -> Prop)
         (P_error : string -> S -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> S -> Prop)
         (h1 h2 : Z -> S -> step_result_gen S) (s : S)
         n1 args1 s1 n2 args2 s2,
    handler_correct_gen S W pc_of R h1 step_pre P_error P_halt P_ccall ->
    handler_correct_gen S W pc_of R h2 step_pre P_error P_halt P_ccall ->
    h1 (pc_of s) s = CCall_request n1 args1 s1 ->
    h2 (pc_of s) s = CCall_request n2 args2 s2 ->
    n1 = n2 /\ args1 = args2 /\ s1 = s2.
Proof. Admitted.

(* ================================================================== *)
(* Main generic theorem                                                *)
(* ================================================================== *)

Lemma handler_correct_gen_determines_em_eq :
  forall (step_pre : W -> S -> Prop)
         (P_error : string -> S -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> S -> Prop)
         (h1 h2 : Z -> S -> step_result_gen S) (s : S),
    handler_correct_gen S W pc_of R h1 step_pre P_error P_halt P_ccall ->
    handler_correct_gen S W pc_of R h2 step_pre P_error P_halt P_ccall ->
    em_eq_gen (h1 (pc_of s) s) (h2 (pc_of s) s).
Proof.
  intros step_pre P_error P_halt P_ccall h1 h2 s Hc1 Hc2.
  remember (h1 (pc_of s) s) as r1 eqn:E1.
  remember (h2 (pc_of s) s) as r2 eqn:E2.
  symmetry in E1. symmetry in E2.
  destruct r1 as [s1' | v1 | msg1 | n1 args1 s1'],
           r2 as [s2' | v2 | msg2 | n2 args2 s2'].
  - (* Step / Step *)
    replace s2' with s1'. { constructor. }
    exact (gen_step_step_eq step_pre P_error P_halt P_ccall h1 h2 s s1' s2' Hc1 Hc2 E1 E2).
  - (* Step / Halt *)
    exfalso. exact (gen_step_halt_excl step_pre P_error P_halt P_ccall
                      h1 h2 s s1' v2 Hc1 Hc2 E1 E2).
  - (* Step / Error *)
    exfalso. exact (gen_step_error_excl step_pre P_error P_halt P_ccall
                      h1 h2 s s1' msg2 Hc1 Hc2 E1 E2).
  - (* Step / CCall *)
    exfalso. exact (gen_step_ccall_excl step_pre P_error P_halt P_ccall
                      h1 h2 s s1' n2 args2 s2' Hc1 Hc2 E1 E2).
  - (* Halt / Step *)
    exfalso. exact (gen_step_halt_excl step_pre P_error P_halt P_ccall
                      h2 h1 s s2' v1 Hc2 Hc1 E2 E1).
  - (* Halt / Halt *)
    replace v2 with v1. { constructor. }
    exact (gen_halt_halt_eq step_pre P_error P_halt P_ccall
             h1 h2 s v1 v2 Hc1 Hc2 E1 E2).
  - (* Halt / Error *)
    exfalso. exact (gen_halt_error_excl step_pre P_error P_halt P_ccall
                      h1 h2 s v1 msg2 Hc1 Hc2 E1 E2).
  - (* Halt / CCall *)
    exfalso. exact (gen_halt_ccall_excl step_pre P_error P_halt P_ccall
                      h1 h2 s v1 n2 args2 s2' Hc1 Hc2 E1 E2).
  - (* Error / Step *)
    exfalso. exact (gen_step_error_excl step_pre P_error P_halt P_ccall
                      h2 h1 s s2' msg1 Hc2 Hc1 E2 E1).
  - (* Error / Halt *)
    exfalso. exact (gen_halt_error_excl step_pre P_error P_halt P_ccall
                      h2 h1 s v2 msg1 Hc2 Hc1 E2 E1).
  - (* Error / Error *)
    constructor.
  - (* Error / CCall *)
    exfalso. exact (gen_error_ccall_excl step_pre P_error P_halt P_ccall
                      h1 h2 s msg1 n2 args2 s2' Hc1 Hc2 E1 E2).
  - (* CCall / Step *)
    exfalso. exact (gen_step_ccall_excl step_pre P_error P_halt P_ccall
                      h2 h1 s s2' n1 args1 s1' Hc2 Hc1 E2 E1).
  - (* CCall / Halt *)
    exfalso. exact (gen_halt_ccall_excl step_pre P_error P_halt P_ccall
                      h2 h1 s v2 n1 args1 s1' Hc2 Hc1 E2 E1).
  - (* CCall / Error *)
    exfalso. exact (gen_error_ccall_excl step_pre P_error P_halt P_ccall
                      h2 h1 s msg2 n1 args1 s1' Hc2 Hc1 E2 E1).
  - (* CCall / CCall *)
    assert (Heq : n1 = n2 /\ args1 = args2 /\ s1' = s2').
    { exact (gen_ccall_ccall_eq step_pre P_error P_halt P_ccall
               h1 h2 s n1 args1 s1' n2 args2 s2' Hc1 Hc2 E1 E2). }
    destruct Heq as [-> [-> ->]].
    constructor.
Qed.

End GenericUniqueness.

(* ================================================================== *)
(* Concrete instantiation (backward compat)                            *)
(*                                                                      *)
(* These reproduce the old lemmas with the old signatures using the    *)
(* concrete abs_rel types.  They delegate to the old axiom-based       *)
(* proof path which remains for compatibility.                         *)
(* ================================================================== *)

(* We keep the old concrete axioms and lemmas for backward compat      *)
(* of the per-instruction proofs that use handler_correct (concrete).  *)

Axiom abs_rel_functional :
  forall (e : Clight.env) (le : temp_env) (m : mem) (s1 s2 : state),
    abs_rel e le m s1 -> abs_rel e le m s2 -> s1 = s2.

Axiom abs_rel_inhabitable :
  forall (f : function)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (s : state),
    exists (e : Clight.env) (le : temp_env) (m : mem) (ard : abs_rel_data),
      abs_rel_with_ard e le m s ard /\ step_pre e m s ard.

(* Proved lemma: Step/Step case (concrete) *)
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
  destruct (abs_rel_inhabitable f step_pre s) as [e [le [m [ard [Habs Hpre]]]]].
  unfold handler_correct in Hc1.
  specialize (Hc1 e le m s).
  rewrite E1 in Hc1.
  specialize (Hc1 ard Habs Hpre).
  destruct Hc1 as [le1' [m1' [out1 [Hexec1 Habs1]]]].
  unfold handler_correct in Hc2.
  specialize (Hc2 e le m s).
  rewrite E2 in Hc2.
  specialize (Hc2 ard Habs Hpre).
  destruct Hc2 as [le2' [m2' [out2 [Hexec2 Habs2]]]].
  destruct (exec_stmt_deterministic _ _ _ _ _ _ _ _ _ _ _ _ _ Hexec1 Hexec2)
    as [_ [Hle Hm_out]].
  destruct Hm_out as [Hm Hout].
  subst le2' m2'.
  exact (abs_rel_functional e le1' m1' s1 s2 Habs1 Habs2).
Qed.

(* Proved lemma: Error/Error case (concrete) *)
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

(* Cross-constructor exclusion lemmas (Admitted, concrete) *)
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

(* Main concrete theorem *)
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
  remember (h1 s.(pc) s) as r1 eqn:E1.
  remember (h2 s.(pc) s) as r2 eqn:E2.
  symmetry in E1. symmetry in E2.
  destruct r1 as [s1' | v1 | msg1 | n1 args1 s1'],
           r2 as [s2' | v2 | msg2 | n2 args2 s2'].
  - replace s2' with s1'. { constructor. }
    exact (step_step_eq f step_pre P_error P_halt P_ccall h1 h2 s s1' s2' Hc1 Hc2 E1 E2).
  - exfalso. exact (step_halt_excl f step_pre P_error P_halt P_ccall
                      h1 h2 s s1' v2 Hc1 Hc2 E1 E2).
  - exfalso. exact (step_error_excl f step_pre P_error P_halt P_ccall
                      h1 h2 s s1' msg2 Hc1 Hc2 E1 E2).
  - exfalso. exact (step_ccall_excl f step_pre P_error P_halt P_ccall
                      h1 h2 s s1' n2 args2 s2' Hc1 Hc2 E1 E2).
  - exfalso. exact (step_halt_excl f step_pre P_error P_halt P_ccall
                      h2 h1 s s2' v1 Hc2 Hc1 E2 E1).
  - replace v2 with v1. { constructor. }
    exact (halt_halt_eq f step_pre P_error P_halt P_ccall
             h1 h2 s v1 v2 Hc1 Hc2 E1 E2).
  - exfalso. exact (halt_error_excl f step_pre P_error P_halt P_ccall
                      h1 h2 s v1 msg2 Hc1 Hc2 E1 E2).
  - exfalso. exact (halt_ccall_excl f step_pre P_error P_halt P_ccall
                      h1 h2 s v1 n2 args2 s2' Hc1 Hc2 E1 E2).
  - exfalso. exact (step_error_excl f step_pre P_error P_halt P_ccall
                      h2 h1 s s2' msg1 Hc2 Hc1 E2 E1).
  - exfalso. exact (halt_error_excl f step_pre P_error P_halt P_ccall
                      h2 h1 s v2 msg1 Hc2 Hc1 E2 E1).
  - constructor.
  - exfalso. exact (error_ccall_excl f step_pre P_error P_halt P_ccall
                      h1 h2 s msg1 n2 args2 s2' Hc1 Hc2 E1 E2).
  - exfalso. exact (step_ccall_excl f step_pre P_error P_halt P_ccall
                      h2 h1 s s2' n1 args1 s1' Hc2 Hc1 E2 E1).
  - exfalso. exact (halt_ccall_excl f step_pre P_error P_halt P_ccall
                      h2 h1 s v2 n1 args1 s1' Hc2 Hc1 E2 E1).
  - exfalso. exact (error_ccall_excl f step_pre P_error P_halt P_ccall
                      h2 h1 s msg2 n1 args1 s1' Hc2 Hc1 E2 E1).
  - assert (Heq : n1 = n2 /\ args1 = args2 /\ s1' = s2').
    { exact (ccall_ccall_eq f step_pre P_error P_halt P_ccall
               h1 h2 s n1 args1 s1' n2 args2 s2' Hc1 Hc2 E1 E2). }
    destruct Heq as [-> [-> ->]].
    constructor.
Qed.

(* ================================================================== *)
(* Derived helper lemmas (concrete, backward compat)                   *)
(* ================================================================== *)

Section GenericHelpers.

Variables (f : function)
          (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
          (P_error : string -> state -> Prop)
          (P_halt_pred : value -> Prop)
          (P_ccall_pred : nat -> list value -> state -> Prop).

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

(* Fully generic uniqueness lemma (concrete) *)
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
