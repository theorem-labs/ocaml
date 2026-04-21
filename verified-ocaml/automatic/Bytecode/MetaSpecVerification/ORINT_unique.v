(* ORINT_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for ORINT.

   ORINT is a binary integer operation (bitwise OR on the top two stack
   values).  Its handler_correct contract:
   - Step s' => Clight execution reaches abs_rel on s'
   - Error msg => error_message_of ORINT s = Some msg
   - Halt v => False  (ORINT is not STOP)
   - CCall_request => False  (ORINT is not C_CALL)

   The error_message_of ORINT s is:
     None                                    when accu = Val_int _ /\ stack = Val_int _ :: _
     Some "ORINT: type error or stack underflow"  otherwise

   step_result constructors (in order): Step, Halt, Error, CCall_request.

   Strategy: case-split on (h1 pc s) and (h2 pc s), eliminating Halt and
   CCall_request immediately.  Error/Error is trivial (em_Error).
   Step/Step requires abs_rel functional (Admitted sub-lemma).
   Step/Error and Error/Step require showing mutual exclusivity of
   step-able and error states (Admitted sub-lemma). *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Maps Memory Clight.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.

(* Sub-lemma: P_halt_of ORINT is False for any value. *)
Local Lemma P_halt_ORINT_false : forall v, P_halt_of ORINT v -> False.
Proof.
  unfold P_halt_of. simpl. intros v [_ H]. exact H.
Qed.

(* Sub-lemma: P_ccall_of ORINT is False for any arguments. *)
Local Lemma P_ccall_ORINT_false : forall n args s',
  P_ccall_of ORINT n args s' -> False.
Proof.
  unfold P_ccall_of. simpl. intros n args s' [_ H]. exact H.
Qed.

(* Sub-lemma: if handler_correct h for ORINT and h returns Step s',
   then error_message_of ORINT s = None, i.e., the state s is in the
   "steppable" configuration (accu = Val_int, top of stack = Val_int). *)
Local Lemma ORINT_step_implies_no_error :
  forall h s s',
    handler_correct h (clight_of ORINT)
      (pre_of ORINT) (P_error_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT) ->
    h s.(pc) s = Step s' ->
    error_message_of ORINT s = None.
Proof.
Admitted.

(* Sub-lemma: if handler_correct h for ORINT and h returns Error msg,
   then error_message_of ORINT s = Some msg. This follows directly
   from the Error branch of handler_correct. *)
Local Lemma ORINT_error_characterizes :
  forall h s msg,
    handler_correct h (clight_of ORINT)
      (pre_of ORINT) (P_error_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT) ->
    h s.(pc) s = Error msg ->
    error_message_of ORINT s = Some msg.
Proof.
  intros h s msg Hcorr Hret.
  unfold handler_correct in Hcorr.
  specialize (Hcorr (PTree.empty _) (PTree.empty _) Mem.empty s).
  rewrite Hret in Hcorr.
  unfold P_error_of in Hcorr. exact Hcorr.
Qed.

(* Sub-lemma: Step s' from one handler and Error from another is
   contradictory — the error condition and step condition are mutually
   exclusive for ORINT. *)
Local Lemma ORINT_step_error_exclusive :
  forall h1 h2 s s' msg,
    handler_correct h1 (clight_of ORINT)
      (pre_of ORINT) (P_error_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT) ->
    handler_correct h2 (clight_of ORINT)
      (pre_of ORINT) (P_error_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT) ->
    h1 s.(pc) s = Step s' ->
    h2 s.(pc) s = Error msg ->
    False.
Proof.
  intros h1 h2 s s' msg H1 H2 Hstep Herr.
  pose proof (ORINT_step_implies_no_error h1 s s' H1 Hstep) as Hno_err.
  pose proof (ORINT_error_characterizes h2 s msg H2 Herr) as Herr_eq.
  rewrite Hno_err in Herr_eq. discriminate.
Qed.

(* Sub-lemma: when both handlers return Step, they agree on the
   post-state. Requires abs_rel_functional + Clight determinism. *)
Local Lemma ORINT_step_step_agree :
  forall h1 h2 s s1' s2',
    handler_correct h1 (clight_of ORINT)
      (pre_of ORINT) (P_error_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT) ->
    handler_correct h2 (clight_of ORINT)
      (pre_of ORINT) (P_error_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT) ->
    h1 s.(pc) s = Step s1' ->
    h2 s.(pc) s = Step s2' ->
    s1' = s2'.
Proof.
Admitted.

(* Helper: extract P_halt or P_ccall from handler_correct by
   specializing with dummy environment values. *)
Local Ltac specialize_hc H s :=
  let Hspec := fresh "Hspec" in
  unfold handler_correct in H;
  specialize (H (PTree.empty _) (PTree.empty _) Mem.empty s).

Lemma unique_ORINT :
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of ORINT)
      (pre_of ORINT) (P_error_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT) ->
    handler_correct h2 (clight_of ORINT)
      (pre_of ORINT) (P_error_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros h1 h2 H1 H2 s.
  (* step_result constructors: Step, Halt, Error, CCall_request *)
  destruct (h1 s.(pc) s) as [s1' | v1 | msg1 | n1 args1 ccall_s1] eqn:E1;
  destruct (h2 s.(pc) s) as [s2' | v2 | msg2 | n2 args2 ccall_s2] eqn:E2.
  (* --- h1 = Step --- *)
  - (* Step/Step *)
    replace s2' with s1'.
    + constructor.
    + eapply ORINT_step_step_agree; [exact H1 | exact H2 | exact E1 | exact E2].
  - (* Step/Halt: impossible — P_halt_of ORINT is False *)
    exfalso. pose proof H2 as H2'. specialize_hc H2' s. rewrite E2 in H2'.
    eapply P_halt_ORINT_false. exact H2'.
  - (* Step/Error: contradictory *)
    exfalso. eapply ORINT_step_error_exclusive;
      [exact H1 | exact H2 | exact E1 | exact E2].
  - (* Step/CCall: impossible — P_ccall_of ORINT is False *)
    exfalso. pose proof H2 as H2'. specialize_hc H2' s. rewrite E2 in H2'.
    eapply P_ccall_ORINT_false. exact H2'.
  (* --- h1 = Halt --- *)
  - (* Halt/Step: impossible — P_halt_of ORINT is False *)
    exfalso. pose proof H1 as H1'. specialize_hc H1' s. rewrite E1 in H1'.
    eapply P_halt_ORINT_false. exact H1'.
  - (* Halt/Halt: impossible *)
    exfalso. pose proof H1 as H1'. specialize_hc H1' s. rewrite E1 in H1'.
    eapply P_halt_ORINT_false. exact H1'.
  - (* Halt/Error: impossible *)
    exfalso. pose proof H1 as H1'. specialize_hc H1' s. rewrite E1 in H1'.
    eapply P_halt_ORINT_false. exact H1'.
  - (* Halt/CCall: impossible *)
    exfalso. pose proof H1 as H1'. specialize_hc H1' s. rewrite E1 in H1'.
    eapply P_halt_ORINT_false. exact H1'.
  (* --- h1 = Error --- *)
  - (* Error/Step: contradictory (symmetric of Step/Error) *)
    exfalso. eapply ORINT_step_error_exclusive with (h1 := h2) (h2 := h1);
      [exact H2 | exact H1 | exact E2 | exact E1].
  - (* Error/Halt: impossible — P_halt_of ORINT is False *)
    exfalso. pose proof H2 as H2'. specialize_hc H2' s. rewrite E2 in H2'.
    eapply P_halt_ORINT_false. exact H2'.
  - (* Error/Error: em_Error applies regardless of messages *)
    constructor.
  - (* Error/CCall: impossible — P_ccall_of ORINT is False *)
    exfalso. pose proof H2 as H2'. specialize_hc H2' s. rewrite E2 in H2'.
    eapply P_ccall_ORINT_false. exact H2'.
  (* --- h1 = CCall_request --- *)
  - (* CCall/Step: impossible — P_ccall_of ORINT is False *)
    exfalso. pose proof H1 as H1'. specialize_hc H1' s. rewrite E1 in H1'.
    eapply P_ccall_ORINT_false. exact H1'.
  - (* CCall/Halt: impossible *)
    exfalso. pose proof H1 as H1'. specialize_hc H1' s. rewrite E1 in H1'.
    eapply P_ccall_ORINT_false. exact H1'.
  - (* CCall/Error: impossible *)
    exfalso. pose proof H1 as H1'. specialize_hc H1' s. rewrite E1 in H1'.
    eapply P_ccall_ORINT_false. exact H1'.
  - (* CCall/CCall: impossible *)
    exfalso. pose proof H1 as H1'. specialize_hc H1' s. rewrite E1 in H1'.
    eapply P_ccall_ORINT_false. exact H1'.
Qed.
