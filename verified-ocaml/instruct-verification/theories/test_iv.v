Require Import instruct_handlers.
Require Import InstructSpec.
Require Import PUSH_RETADDR_correct.

(* Check if verify_PUSH_RETADDR_correct can be used as correct_PUSH_RETADDR *)
(* The types must match: use InstructSpec's push_retaddr_step_pre *)
Lemma test : forall ret_addr,
    handler_correct (Interpret.handle_PUSH_RETADDR ret_addr) f_instr_PUSH_RETADDR
      (fun _ m s ard => InstructSpec.push_retaddr_step_pre ret_addr m s ard)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  exact verify_PUSH_RETADDR_correct.
Qed.
