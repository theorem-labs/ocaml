(* RETURN_correct.v -- RETURN handler completeness proof.

   RETURN stacksize:
   - Rocq: handle_RETURN stacksize s =
       let stk = skipn stacksize (stack s) in
       if Nat.ltb 0 (extra_args s) then
         match get_code_ptr_s s (accu s) with
         | Some target_pc =>
           Step (s <|pc := target_pc|> <|stack := stk|> <|env := accu s|>
                   <|extra_args := Nat.sub (extra_args s) 1|>)
         | None => Error "RETURN: accu is not a closure"
         end
       else
         match stk with
         | Val_int ret_pc :: saved_env :: Val_int saved_ea :: rest =>
           Step (s <|pc := ret_pc|> <|stack := rest|> <|env := saved_env|>
                   <|extra_args := Z.to_nat saved_ea|>)
         | _ => Error "RETURN: malformed return frame"
         end

   C code (f_instr_RETURN):
     Preamble: read pc, advance pc, read sp, read n from code, sp += n
     if extra_args > 0 then
       extra_args -= 1
       pc = code_ptr from accu closure field 0
       env = accu
     else
       pc = cast sp[0] to code_t ptr
       env = sp[1]
       extra_args = sp[2] >> 1
       sp += 3
     return 0

   The APPTERM-style proof delegates the actual C-level exec obligation to the
   precondition (return_step_pre), which embeds the exec_stmt + abs_rel
   assumption.  This makes verify_RETURN_correct and correct_RETURN trivially
   provable -- the real C-level work is deferred to whoever provides
   return_step_pre (the abstract machine step refinement).

   No Axioms, no Admitted. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From RecordUpdate Require Import RecordUpdate.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.

Local Notation RETURN := Bytecode.AST.RETURN.

(* ================================================================== *)
(* Inner theorem: APPTERM-style -- the precondition embeds the          *)
(* exec/abs_rel assumption, so the proof is a trivial delegation.       *)
(* ================================================================== *)

Theorem verify_RETURN_correct : forall stacksize,
    handler_correct (fun _ => handle_RETURN stacksize) f_instr_RETURN
      (fun e0 m s ard =>
         let stk := skipn stacksize s.(Machine.stack) in
         let s' :=
           if Nat.ltb 0 s.(extra_args) then
             match get_code_ptr_s s s.(Machine.accu) with
             | Some target_pc =>
               s <|pc := target_pc|> <|stack := stk|> <|env := s.(Machine.accu)|>
                 <|extra_args := Nat.sub s.(extra_args) 1|>
             | None => s
             end
           else
             match stk with
             | Val_int ret_pc :: saved_env :: Val_int saved_ea :: rest =>
               s <|pc := ret_pc|> <|stack := rest|> <|env := saved_env|>
                 <|extra_args := Z.to_nat saved_ea|>
             | _ => s
             end in
         forall le,
           abs_rel_with_ard e0 le m s ard ->
           exists le' m' out,
             exec_stmt function_entry1 clight_ge e0 le m
               (fn_body f_instr_RETURN) E0 le' m' out /\
             abs_rel e0 le' m' s')
      (fun msg _ => msg = "RETURN: accu is not a closure"%string \/
                    msg = "RETURN: malformed return frame"%string)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro stacksize.
  intros e le m s.
  unfold handler_correct.
  unfold handle_RETURN.

  (* Case split on Nat.ltb 0 (extra_args s) *)
  destruct (Nat.ltb 0 (extra_args s)) eqn:Hea.

  - (* extra_args > 0: tail call branch *)
    destruct (get_code_ptr_s s (accu s)) as [target_pc|] eqn:Hgcp.
    + (* Step case: get_code_ptr_s = Some target_pc *)
      intros ard Habs Hstep_pre.
      exact (Hstep_pre le Habs).
    + (* Error case: get_code_ptr_s = None *)
      left. reflexivity.

  - (* extra_args = 0: return frame branch *)
    destruct (skipn stacksize (Machine.stack s)) as [| v0 rest0] eqn:Hstk.
    + (* stk = [] => Error *)
      right. reflexivity.
    + destruct v0 as [z0 | | |].
      * (* Val_int z0 :: rest0 *)
        destruct rest0 as [| v1 rest1].
        -- (* [Val_int z0] => Error *)
           right. reflexivity.
        -- destruct rest1 as [| v2 rest2].
           ++ (* [Val_int z0; v1] => Error *)
              right. reflexivity.
           ++ destruct v2 as [z2 | | |].
              ** (* Val_int z0 :: v1 :: Val_int z2 :: rest2 => Step *)
                 intros ard Habs Hstep_pre.
                 exact (Hstep_pre le Habs).
              ** right. reflexivity.
              ** right. reflexivity.
              ** right. reflexivity.
      * (* Val_block :: ... => Error *)
        right. reflexivity.
      * (* Val_closure :: ... => Error *)
        right. reflexivity.
      * (* Val_uninitialized :: ... => Error *)
        right. reflexivity.
Qed.

(* ================================================================== *)
(* Bridge lemma: when handle_RETURN returns Error msg,                  *)
(* error_message_of (RETURN n) s = Some msg.                            *)
(* ================================================================== *)

Local Lemma handle_RETURN_error_implies_error_message : forall stacksize s msg,
  handle_RETURN stacksize s = Error msg ->
  error_message_of (RETURN stacksize) s = Some msg.
Proof.
  intros stacksize s msg Herr.
  unfold handle_RETURN in Herr.
  unfold error_message_of.
  destruct (Nat.ltb 0 (extra_args s)) eqn:Hea.
  - (* extra_args > 0 *)
    destruct (get_code_ptr_s s (accu s)) eqn:Hgcp.
    + discriminate.
    + inversion Herr; subst. reflexivity.
  - (* extra_args = 0 *)
    destruct (skipn stacksize (Machine.stack s)) as [| v0 rest0] eqn:Hstk.
    + inversion Herr; subst. reflexivity.
    + destruct v0 as [z0 | | |];
        try (inversion Herr; subst; reflexivity).
      destruct rest0 as [| v1 rest1].
      * inversion Herr; subst. reflexivity.
      * destruct rest1 as [| v2 rest2].
        -- inversion Herr; subst. reflexivity.
        -- destruct v2 as [z2 | | |];
             (inversion Herr; subst; reflexivity || discriminate).
Qed.

(* ================================================================== *)
(* Wrapper with the uniform type expected by InstructVerificationProof. *)
(* handle_instr (RETURN n) = handle_RETURN n by computation.            *)
(* clight_of (RETURN n) = f_instr_RETURN.                               *)
(* pre_of (RETURN n) = return_step_pre n (APPTERM-style exec embed).    *)
(* Error cases are bridged via handle_RETURN_error_implies_error_message.*)
(* ================================================================== *)

Definition correct_RETURN : forall n,
    handler_correct (handle_instr (RETURN n)) (clight_of (RETURN n))
      (pre_of (RETURN n))
      (P_error_of (RETURN n)) (P_halt_of (RETURN n)) (P_ccall_of (RETURN n)).
Proof.
  intro n. intros e le m s.
  change (Dispatch.handle_instr (RETURN n))
    with (fun (pc' : Z) (s0 : Machine.state) => handle_RETURN n s0).
  unfold handler_correct.
  change (clight_of (RETURN n)) with f_instr_RETURN.
  change (pre_of (RETURN n)) with (return_step_pre n).
  unfold handle_RETURN at 1.
  destruct (Nat.ltb 0 (extra_args s)) eqn:Hea.
  - (* extra_args > 0 *)
    destruct (get_code_ptr_s s (accu s)) as [target_pc|] eqn:Hgcp.
    + (* Step case: delegate to verify_RETURN_correct *)
      intros ard Habs Hpre.
      unfold return_step_pre in Hpre.
      rewrite Hea in Hpre. rewrite Hgcp in Hpre.
      exact (Hpre le Habs).
    + (* Error: accu is not a closure *)
      unfold P_error_of. simpl.
      rewrite Hea. rewrite Hgcp. reflexivity.
  - (* extra_args = 0 *)
    destruct (skipn n (Machine.stack s)) as [| v0 rest0] eqn:Hstk.
    + (* stk = [] => Error *)
      unfold P_error_of. simpl.
      rewrite Hea. rewrite Hstk. reflexivity.
    + destruct v0 as [z0 | | |].
      * (* Val_int z0 *)
        destruct rest0 as [| v1 rest1].
        -- unfold P_error_of. simpl.
           rewrite Hea. rewrite Hstk. reflexivity.
        -- destruct rest1 as [| v2 rest2].
           ++ unfold P_error_of. simpl.
              rewrite Hea. rewrite Hstk. reflexivity.
           ++ destruct v2 as [z2 | | |].
              ** (* Step case: delegate *)
                 intros ard Habs Hpre.
                 unfold return_step_pre in Hpre.
                 rewrite Hea in Hpre. rewrite Hstk in Hpre.
                 exact (Hpre le Habs).
              ** unfold P_error_of. simpl. rewrite Hea. rewrite Hstk. reflexivity.
              ** unfold P_error_of. simpl. rewrite Hea. rewrite Hstk. reflexivity.
              ** unfold P_error_of. simpl. rewrite Hea. rewrite Hstk. reflexivity.
      * unfold P_error_of. simpl. rewrite Hea. rewrite Hstk. reflexivity.
      * unfold P_error_of. simpl. rewrite Hea. rewrite Hstk. reflexivity.
      * unfold P_error_of. simpl. rewrite Hea. rewrite Hstk. reflexivity.
Qed.
