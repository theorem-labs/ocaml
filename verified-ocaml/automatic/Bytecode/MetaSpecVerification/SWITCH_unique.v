(* SWITCH_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for SWITCH. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Maps Ctypes Clight Globalenvs Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma SWITCH_P_halt_False : forall nc nb const_targets block_targets,
  forall v, P_halt_of (SWITCH nc nb const_targets block_targets) v -> False.
Proof. intros nc nb const_targets block_targets v [_ H]. exact H. Qed.

Lemma SWITCH_P_ccall_False : forall nc nb const_targets block_targets,
  forall n0 args0 s0, P_ccall_of (SWITCH nc nb const_targets block_targets) n0 args0 s0 -> False.
Proof. intros nc nb const_targets block_targets n0 args0 s0 [_ H]. exact H. Qed.

Lemma SWITCH_step_step_eq :
  forall nc nb const_targets block_targets,
  forall (h1 h2 : Z -> state -> step_result) s s1 s2,
    handler_correct h1 (clight_of (SWITCH nc nb const_targets block_targets))
      (pre_of (SWITCH nc nb const_targets block_targets)) (P_error_of (SWITCH nc nb const_targets block_targets)) (P_halt_of (SWITCH nc nb const_targets block_targets)) (P_ccall_of (SWITCH nc nb const_targets block_targets)) ->
    handler_correct h2 (clight_of (SWITCH nc nb const_targets block_targets))
      (pre_of (SWITCH nc nb const_targets block_targets)) (P_error_of (SWITCH nc nb const_targets block_targets)) (P_halt_of (SWITCH nc nb const_targets block_targets)) (P_ccall_of (SWITCH nc nb const_targets block_targets)) ->
    h1 s.(pc) s = Step s1 -> h2 s.(pc) s = Step s2 -> s1 = s2.
Proof. Admitted.

Lemma SWITCH_step_error_excl :
  forall nc nb const_targets block_targets,
  forall (h1 h2 : Z -> state -> step_result) s s' msg,
    handler_correct h1 (clight_of (SWITCH nc nb const_targets block_targets))
      (pre_of (SWITCH nc nb const_targets block_targets)) (P_error_of (SWITCH nc nb const_targets block_targets)) (P_halt_of (SWITCH nc nb const_targets block_targets)) (P_ccall_of (SWITCH nc nb const_targets block_targets)) ->
    handler_correct h2 (clight_of (SWITCH nc nb const_targets block_targets))
      (pre_of (SWITCH nc nb const_targets block_targets)) (P_error_of (SWITCH nc nb const_targets block_targets)) (P_halt_of (SWITCH nc nb const_targets block_targets)) (P_ccall_of (SWITCH nc nb const_targets block_targets)) ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = Error msg -> False.
Proof. Admitted.

Lemma unique_SWITCH : forall nc nb const_targets block_targets, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (SWITCH nc nb const_targets block_targets))
        (pre_of (SWITCH nc nb const_targets block_targets)) (P_error_of (SWITCH nc nb const_targets block_targets)) (P_halt_of (SWITCH nc nb const_targets block_targets)) (P_ccall_of (SWITCH nc nb const_targets block_targets)) ->
      handler_correct h2 (clight_of (SWITCH nc nb const_targets block_targets))
        (pre_of (SWITCH nc nb const_targets block_targets)) (P_error_of (SWITCH nc nb const_targets block_targets)) (P_halt_of (SWITCH nc nb const_targets block_targets)) (P_ccall_of (SWITCH nc nb const_targets block_targets)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros nc nb const_targets block_targets h1 h2 Hcorr1 Hcorr2 s.
  pose proof (Hcorr1 empty_env (PTree.empty _) Mem.empty s) as Hs1.
  pose proof (Hcorr2 empty_env (PTree.empty _) Mem.empty s) as Hs2.
  destruct (h1 s.(pc) s) eqn:E1; destruct (h2 s.(pc) s) eqn:E2.
  all: try (exfalso; exact (SWITCH_P_halt_False _ _ _ _ _ Hs1)).
  all: try (exfalso; exact (SWITCH_P_halt_False _ _ _ _ _ Hs2)).
  all: try (exfalso; exact (SWITCH_P_ccall_False _ _ _ _ _ _ _ Hs1)).
  all: try (exfalso; exact (SWITCH_P_ccall_False _ _ _ _ _ _ _ Hs2)).
  - (* Step/Step *)
    assert (s0 = s1) by (eapply SWITCH_step_step_eq; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2]). subst. constructor.
  - (* Step/Error *)
    exfalso. eapply SWITCH_step_error_excl; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2].
  - (* Error/Step *)
    exfalso. eapply SWITCH_step_error_excl; [exact Hcorr2 | exact Hcorr1 | exact E2 | exact E1].
  - (* Error/Error *) constructor.
Qed.
