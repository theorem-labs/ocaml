(* C_CALL_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for C_CALL. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Maps Ctypes Clight Globalenvs Memory Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

Lemma C_CALL_P_halt_False : forall nargs prim_idx,
  forall v, P_halt_of (C_CALL nargs prim_idx) v -> False.
Proof. intros nargs prim_idx v [_ H]. exact H. Qed.

Lemma C_CALL_step_step_eq :
  forall nargs prim_idx,
  forall (h1 h2 : Z -> state -> step_result) s s1 s2,
    handler_correct h1 (clight_of (C_CALL nargs prim_idx))
      (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
    handler_correct h2 (clight_of (C_CALL nargs prim_idx))
      (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
    h1 s.(pc) s = Step s1 -> h2 s.(pc) s = Step s2 -> s1 = s2.
Proof. Admitted.

Lemma C_CALL_step_error_excl :
  forall nargs prim_idx,
  forall (h1 h2 : Z -> state -> step_result) s s' msg,
    handler_correct h1 (clight_of (C_CALL nargs prim_idx))
      (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
    handler_correct h2 (clight_of (C_CALL nargs prim_idx))
      (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = Error msg -> False.
Proof. Admitted.

Lemma C_CALL_ccall_ccall_eq :
  forall nargs prim_idx,
  forall (h1 h2 : Z -> state -> step_result) s n1 args1 s1 n2 args2 s2,
    handler_correct h1 (clight_of (C_CALL nargs prim_idx))
      (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
    handler_correct h2 (clight_of (C_CALL nargs prim_idx))
      (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
    h1 s.(pc) s = CCall_request n1 args1 s1 ->
    h2 s.(pc) s = CCall_request n2 args2 s2 ->
    n1 = n2 /\ args1 = args2 /\ s1 = s2.
Proof. Admitted.

Lemma C_CALL_step_ccall_excl :
  forall nargs prim_idx,
  forall (h1 h2 : Z -> state -> step_result) s s' n0 args0 s'',
    handler_correct h1 (clight_of (C_CALL nargs prim_idx))
      (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
    handler_correct h2 (clight_of (C_CALL nargs prim_idx))
      (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = CCall_request n0 args0 s'' -> False.
Proof. Admitted.

Lemma C_CALL_error_ccall_excl :
  forall nargs prim_idx,
  forall (h1 h2 : Z -> state -> step_result) s msg n0 args0 s',
    handler_correct h1 (clight_of (C_CALL nargs prim_idx))
      (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
    handler_correct h2 (clight_of (C_CALL nargs prim_idx))
      (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
    h1 s.(pc) s = Error msg -> h2 s.(pc) s = CCall_request n0 args0 s' -> False.
Proof. Admitted.

Lemma unique_C_CALL : forall nargs prim_idx, 
    forall (h1 h2 : Z -> state -> step_result),
      handler_correct h1 (clight_of (C_CALL nargs prim_idx))
        (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
      handler_correct h2 (clight_of (C_CALL nargs prim_idx))
        (pre_of (C_CALL nargs prim_idx)) (P_error_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)) ->
      forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros nargs prim_idx h1 h2 Hcorr1 Hcorr2 s.
  pose proof (Hcorr1 empty_env (PTree.empty _) Mem.empty s) as Hs1.
  pose proof (Hcorr2 empty_env (PTree.empty _) Mem.empty s) as Hs2.
  destruct (h1 s.(pc) s) eqn:E1; destruct (h2 s.(pc) s) eqn:E2.
  all: try (exfalso; exact (C_CALL_P_halt_False _ _ _ Hs1)).
  all: try (exfalso; exact (C_CALL_P_halt_False _ _ _ Hs2)).
  - (* Step/Step *)
    assert (s0 = s1) by (eapply C_CALL_step_step_eq; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2]). subst. constructor.
  - (* Step/Error *)
    exfalso. eapply C_CALL_step_error_excl; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2].
  - (* Step/CCall *)
    exfalso. eapply C_CALL_step_ccall_excl; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2].
  - (* Error/Step *)
    exfalso. eapply C_CALL_step_error_excl; [exact Hcorr2 | exact Hcorr1 | exact E2 | exact E1].
  - (* Error/Error *) constructor.
  - (* Error/CCall *)
    exfalso. eapply C_CALL_error_ccall_excl; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2].
  - (* CCall/Step *)
    exfalso. eapply C_CALL_step_ccall_excl; [exact Hcorr2 | exact Hcorr1 | exact E2 | exact E1].
  - (* CCall/Error *)
    exfalso. eapply C_CALL_error_ccall_excl; [exact Hcorr2 | exact Hcorr1 | exact E2 | exact E1].
  - (* CCall/CCall *)
    pose proof (C_CALL_ccall_ccall_eq nargs prim_idx h1 h2 s _ _ _ _ _ _ Hcorr1 Hcorr2 E1 E2) as [? [? ?]].
    subst. constructor.
Qed.
