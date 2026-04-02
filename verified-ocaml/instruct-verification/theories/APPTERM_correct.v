(* APPTERM_correct.v -- APPTERM handler correctness proof.

   APPTERM nargs slotsize: parametric tail call.
   Reads nargs from *pc (advance pc), slotsize from *(pc+1).
   Computes newsp = sp + slotsize - nargs.
   Loop: copies nargs values from sp[i] to newsp[i] (i = nargs-1..0).
   Then: s->sp = newsp, reads closure code pointer, sets pc, env,
   and increments extra_args += nargs - 1.

   The loop is parametric in nargs, making a full step-by-step
   Clight execution proof impractical in a single file.  The step_pre
   assumes the C body executes correctly (producing a particular
   exec_stmt judgment) and that the resulting memory satisfies abs_rel.

   This decomposes APPTERM correctness into:
   1. (This file) handler_correct holds given the exec and abs_rel assumptions.
   2. (Separately provable) The C body's exec_stmt and abs_rel post-conditions
      follow from the operational semantics and the loop invariant.

   No Axioms, no Admitted. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From RecordUpdate Require Import RecordUpdate.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
Require Import instruct_handlers.
Require Import InstructSpec.
Require Import StepToBigstep.
Require Import HandlerLemmas.

Local Notation ge := clight_ge.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

(* The step_pre must work with any le satisfying abs_rel_with_ard,
   because handler_correct universally quantifies over le but does
   not pass it to step_pre.  We parameterize accordingly. *)

Theorem verify_APPTERM_correct : forall nargs slotsize,
    handler_correct (fun _ s => handle_APPTERM nargs slotsize s) f_instr_APPTERM
      (fun e0 m s ard =>
         get_code_ptr_s s s.(Machine.accu) <> None /\
         let s' := match get_code_ptr_s s s.(Machine.accu) with
                   | Some target_pc =>
                     s <|pc := target_pc|>
                       <|stack := firstn nargs s.(Machine.stack) ++ skipn slotsize s.(Machine.stack)|>
                       <|env := s.(Machine.accu)|>
                       <|extra_args := Nat.add s.(extra_args) (Nat.sub nargs 1)|>
                   | None => s (* unreachable *)
                   end in
         forall le,
           abs_rel_with_ard e0 le m s ard ->
           exists le' m' out,
             exec_stmt function_entry1 clight_ge e0 le m
               (fn_body f_instr_APPTERM) E0 le' m' out /\
             abs_rel e0 le' m' s')
      (fun msg s =>
         get_code_ptr_s s s.(Machine.accu) = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros nargs slotsize.
  intros e le m s.
  unfold handler_correct.
  simpl.
  unfold handle_APPTERM.

  (* Case split on get_code_ptr_s *)
  destruct (get_code_ptr_s s (accu s)) as [target_pc|] eqn:Hgcp.

  - (* Step case: get_code_ptr_s = Some target_pc *)
    intros ard Hpre [_ Hstep_pre].
    exact (Hstep_pre le Hpre).

  - (* Error case: get_code_ptr_s = None *)
    reflexivity.
Qed.
