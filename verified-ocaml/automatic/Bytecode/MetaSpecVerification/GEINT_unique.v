(* GEINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for GEINT. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Maps Ctypes Clight Globalenvs Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma GEINT_P_halt_False : forall v, P_halt_of GEINT v -> False.
Proof. intros v [_ H]. exact H. Qed.

Lemma GEINT_P_ccall_False : forall n0 args0 s0, P_ccall_of GEINT n0 args0 s0 -> False.
Proof. intros n0 args0 s0 [_ H]. exact H. Qed.

Lemma GEINT_step_step_eq :
  forall (h1 h2 : Z -> state -> step_result) s s1 s2,
    handler_correct h1 (clight_of GEINT)
      (pre_of GEINT) (P_error_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT) ->
    handler_correct h2 (clight_of GEINT)
      (pre_of GEINT) (P_error_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT) ->
    h1 s.(pc) s = Step s1 -> h2 s.(pc) s = Step s2 -> s1 = s2.
Proof. Admitted.

Lemma GEINT_step_error_excl :
  forall (h1 h2 : Z -> state -> step_result) s s' msg,
    handler_correct h1 (clight_of GEINT)
      (pre_of GEINT) (P_error_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT) ->
    handler_correct h2 (clight_of GEINT)
      (pre_of GEINT) (P_error_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT) ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = Error msg -> False.
Proof. Admitted.

Lemma unique_GEINT :
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of GEINT)
        (pre_of GEINT) (P_error_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT) ->
      handler_correct h2 (clight_of GEINT)
        (pre_of GEINT) (P_error_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros h1 h2 Hcorr1 Hcorr2 s.
  pose proof (Hcorr1 empty_env (PTree.empty _) Mem.empty s) as Hs1.
  pose proof (Hcorr2 empty_env (PTree.empty _) Mem.empty s) as Hs2.
  destruct (h1 s.(pc) s) eqn:E1; destruct (h2 s.(pc) s) eqn:E2.
  all: try (exfalso; exact (GEINT_P_halt_False _ Hs1)).
  all: try (exfalso; exact (GEINT_P_halt_False _ Hs2)).
  all: try (exfalso; exact (GEINT_P_ccall_False _ _ _ Hs1)).
  all: try (exfalso; exact (GEINT_P_ccall_False _ _ _ Hs2)).
  - (* Step/Step *)
    assert (s0 = s1) by (eapply GEINT_step_step_eq; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2]). subst. constructor.
  - (* Step/Error *)
    exfalso. eapply GEINT_step_error_excl; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2].
  - (* Error/Step *)
    exfalso. eapply GEINT_step_error_excl; [exact Hcorr2 | exact Hcorr1 | exact E2 | exact E1].
  - (* Error/Error *) constructor.
Qed.
