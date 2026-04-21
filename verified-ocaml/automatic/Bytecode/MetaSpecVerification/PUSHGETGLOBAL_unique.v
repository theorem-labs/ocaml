(* PUSHGETGLOBAL_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for PUSHGETGLOBAL. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Maps Ctypes Clight Globalenvs Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma PUSHGETGLOBAL_P_halt_False : forall n,
  forall v, P_halt_of (PUSHGETGLOBAL n) v -> False.
Proof. intros n v [_ H]. exact H. Qed.

Lemma PUSHGETGLOBAL_P_ccall_False : forall n,
  forall n0 args0 s0, P_ccall_of (PUSHGETGLOBAL n) n0 args0 s0 -> False.
Proof. intros n n0 args0 s0 [_ H]. exact H. Qed.

Lemma PUSHGETGLOBAL_step_step_eq :
  forall n,
  forall (h1 h2 : Z -> state -> step_result) s s1 s2,
    handler_correct h1 (clight_of (PUSHGETGLOBAL n))
      (pre_of (PUSHGETGLOBAL n)) (P_error_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)) ->
    handler_correct h2 (clight_of (PUSHGETGLOBAL n))
      (pre_of (PUSHGETGLOBAL n)) (P_error_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)) ->
    h1 s.(pc) s = Step s1 -> h2 s.(pc) s = Step s2 -> s1 = s2.
Proof. Admitted.

Lemma PUSHGETGLOBAL_step_error_excl :
  forall n,
  forall (h1 h2 : Z -> state -> step_result) s s' msg,
    handler_correct h1 (clight_of (PUSHGETGLOBAL n))
      (pre_of (PUSHGETGLOBAL n)) (P_error_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)) ->
    handler_correct h2 (clight_of (PUSHGETGLOBAL n))
      (pre_of (PUSHGETGLOBAL n)) (P_error_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)) ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = Error msg -> False.
Proof. Admitted.

Lemma unique_PUSHGETGLOBAL : forall n, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (PUSHGETGLOBAL n))
        (pre_of (PUSHGETGLOBAL n)) (P_error_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)) ->
      handler_correct h2 (clight_of (PUSHGETGLOBAL n))
        (pre_of (PUSHGETGLOBAL n)) (P_error_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros n h1 h2 Hcorr1 Hcorr2 s.
  pose proof (Hcorr1 empty_env (PTree.empty _) Mem.empty s) as Hs1.
  pose proof (Hcorr2 empty_env (PTree.empty _) Mem.empty s) as Hs2.
  destruct (h1 s.(pc) s) eqn:E1; destruct (h2 s.(pc) s) eqn:E2.
  all: try (exfalso; exact (PUSHGETGLOBAL_P_halt_False _ _ Hs1)).
  all: try (exfalso; exact (PUSHGETGLOBAL_P_halt_False _ _ Hs2)).
  all: try (exfalso; exact (PUSHGETGLOBAL_P_ccall_False _ _ _ _ Hs1)).
  all: try (exfalso; exact (PUSHGETGLOBAL_P_ccall_False _ _ _ _ Hs2)).
  - (* Step/Step *)
    assert (s0 = s1) by (eapply PUSHGETGLOBAL_step_step_eq; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2]). subst. constructor.
  - (* Step/Error *)
    exfalso. eapply PUSHGETGLOBAL_step_error_excl; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2].
  - (* Error/Step *)
    exfalso. eapply PUSHGETGLOBAL_step_error_excl; [exact Hcorr2 | exact Hcorr1 | exact E2 | exact E1].
  - (* Error/Error *) constructor.
Qed.
