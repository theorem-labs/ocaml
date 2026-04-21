(* GETGLOBALFIELD_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for GETGLOBALFIELD. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Maps Ctypes Clight Globalenvs Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma GETGLOBALFIELD_P_halt_False : forall n p,
  forall v, P_halt_of (GETGLOBALFIELD n p) v -> False.
Proof. intros n p v [_ H]. exact H. Qed.

Lemma GETGLOBALFIELD_P_ccall_False : forall n p,
  forall n0 args0 s0, P_ccall_of (GETGLOBALFIELD n p) n0 args0 s0 -> False.
Proof. intros n p n0 args0 s0 [_ H]. exact H. Qed.

Lemma GETGLOBALFIELD_step_step_eq :
  forall n p,
  forall (h1 h2 : Z -> state -> step_result) s s1 s2,
    handler_correct h1 (clight_of (GETGLOBALFIELD n p))
      (pre_of (GETGLOBALFIELD n p)) (P_error_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)) ->
    handler_correct h2 (clight_of (GETGLOBALFIELD n p))
      (pre_of (GETGLOBALFIELD n p)) (P_error_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)) ->
    h1 s.(pc) s = Step s1 -> h2 s.(pc) s = Step s2 -> s1 = s2.
Proof. Admitted.

Lemma GETGLOBALFIELD_step_error_excl :
  forall n p,
  forall (h1 h2 : Z -> state -> step_result) s s' msg,
    handler_correct h1 (clight_of (GETGLOBALFIELD n p))
      (pre_of (GETGLOBALFIELD n p)) (P_error_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)) ->
    handler_correct h2 (clight_of (GETGLOBALFIELD n p))
      (pre_of (GETGLOBALFIELD n p)) (P_error_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)) ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = Error msg -> False.
Proof. Admitted.

Lemma unique_GETGLOBALFIELD : forall n p, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (GETGLOBALFIELD n p))
        (pre_of (GETGLOBALFIELD n p)) (P_error_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)) ->
      handler_correct h2 (clight_of (GETGLOBALFIELD n p))
        (pre_of (GETGLOBALFIELD n p)) (P_error_of (GETGLOBALFIELD n p)) (P_halt_of (GETGLOBALFIELD n p)) (P_ccall_of (GETGLOBALFIELD n p)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros n p h1 h2 Hcorr1 Hcorr2 s.
  pose proof (Hcorr1 empty_env (PTree.empty _) Mem.empty s) as Hs1.
  pose proof (Hcorr2 empty_env (PTree.empty _) Mem.empty s) as Hs2.
  destruct (h1 s.(pc) s) eqn:E1; destruct (h2 s.(pc) s) eqn:E2.
  all: try (exfalso; exact (GETGLOBALFIELD_P_halt_False _ _ _ Hs1)).
  all: try (exfalso; exact (GETGLOBALFIELD_P_halt_False _ _ _ Hs2)).
  all: try (exfalso; exact (GETGLOBALFIELD_P_ccall_False _ _ _ _ _ Hs1)).
  all: try (exfalso; exact (GETGLOBALFIELD_P_ccall_False _ _ _ _ _ Hs2)).
  - (* Step/Step *)
    assert (s0 = s1) by (eapply GETGLOBALFIELD_step_step_eq; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2]). subst. constructor.
  - (* Step/Error *)
    exfalso. eapply GETGLOBALFIELD_step_error_excl; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2].
  - (* Error/Step *)
    exfalso. eapply GETGLOBALFIELD_step_error_excl; [exact Hcorr2 | exact Hcorr1 | exact E2 | exact E1].
  - (* Error/Error *) constructor.
Qed.
