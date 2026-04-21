(* STOP_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for STOP. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Maps Memory Clight Values.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

(* For STOP:
   - error_message_of STOP s = None, so P_error_of STOP msg s is absurd
   - P_ccall_of STOP requires False (from the match arm)
   - P_halt_of STOP v iff instr_wfb STOP = true (which is True)
   - pre_of STOP = no_pre = fun _ _ _ _ => True

   Therefore any handler satisfying handler_correct for STOP can only
   produce Step or Halt results (never Error or CCall_request). *)

Lemma unique_STOP :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of STOP)
      (pre_of STOP) (P_error_of STOP) (P_halt_of STOP) (P_ccall_of STOP) ->
    handler_correct h2 (clight_of STOP)
      (pre_of STOP) (P_error_of STOP) (P_halt_of STOP) (P_ccall_of STOP) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros h1 h2 H1 H2 s.
  (* handler_correct unfolds to:
       forall e le m s, match h s.(pc) s with
       | Step s'            => forall ard, abs_rel_with_ard ... -> pre_of ... -> exists ...
       | Error msg          => P_error_of STOP msg s
       | Halt v             => P_halt_of STOP v
       | CCall_request n args s' => P_ccall_of STOP n args s'
       end
     The match target h s.(pc) s does not depend on e, le, m, so we can
     extract the Error / CCall predicates by specializing with any
     inhabitants (PTree.empty, Mem.empty). *)
  unfold handler_correct in H1, H2.
  (* Specialize with dummy e, le, m *)
  specialize (H1 (PTree.empty _) (PTree.empty _) Mem.empty s).
  specialize (H2 (PTree.empty _) (PTree.empty _) Mem.empty s).
  (* Case-split on both handler results *)
  destruct (h1 s.(pc) s) eqn:Eq1;
  destruct (h2 s.(pc) s) eqn:Eq2.
  - (* Step s0 / Step s1 — need Clight determinism to show s0 = s1 *)
    admit.
  - (* Step / Halt — need to derive contradiction or admit *)
    admit.
  - (* Step / Error msg — H2 gives P_error_of STOP msg s, which is absurd *)
    unfold P_error_of, error_message_of in H2. discriminate.
  - (* Step / CCall_request — H2 gives P_ccall_of STOP ..., which has False *)
    unfold P_ccall_of in H2. destruct H2 as [_ []].
  - (* Halt / Step *)
    admit.
  - (* Halt v / Halt v0 — P_halt_of STOP is True so we can't deduce v = v0 *)
    admit.
  - (* Halt / Error — H2 absurd *)
    unfold P_error_of, error_message_of in H2. discriminate.
  - (* Halt / CCall — H2 absurd *)
    unfold P_ccall_of in H2. destruct H2 as [_ []].
  - (* Error / Step — H1 absurd *)
    unfold P_error_of, error_message_of in H1. discriminate.
  - (* Error / Halt — H1 absurd *)
    unfold P_error_of, error_message_of in H1. discriminate.
  - (* Error / Error — both absurd *)
    unfold P_error_of, error_message_of in H1. discriminate.
  - (* Error / CCall — H1 absurd *)
    unfold P_error_of, error_message_of in H1. discriminate.
  - (* CCall / Step — H1 absurd *)
    unfold P_ccall_of in H1. destruct H1 as [_ []].
  - (* CCall / Halt — H1 absurd *)
    unfold P_ccall_of in H1. destruct H1 as [_ []].
  - (* CCall / Error — H1 absurd *)
    unfold P_ccall_of in H1. destruct H1 as [_ []].
  - (* CCall / CCall — H1 absurd *)
    unfold P_ccall_of in H1. destruct H1 as [_ []].
Admitted.
