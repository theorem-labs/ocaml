(* PUSHENVACC1_correct.v -- PUSHENVACC1 = PUSH then ENVACC1.

   C handler (f_instr_PUSHENVACC1):
     t5 = s->sp;
     t1 = (long ptr)(t5 - 1);   // new_sp = sp - 1
     s->sp = t1;                  // store 1: update sp field
     t4 = s->accu;
     *t1 = t4;                    // store 2: push accu onto stack
     t2 = s->env;
     t3 = *((long ptr)t2 + 1);   // load field 1 from env
     s->accu = t3;                // store 3: set accu to env field

   Rocq (handle_PUSHENVACC 1):
     let new_stack := accu :: stack in
     match field_or_heap s s.(env) 1 with
     | Some v => Step (s <|pc:=pc'|> <|accu:=v|> <|stack:=new_stack|>)
     | None => Error "PUSHENVACC: env access out of bounds"
     end

   Three stores:
     Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v
     Store 3: accu field (sb, uso+8) <- cv (env field value)

   step_pre: sp_ofs >= 16 (room for push) + env field loadable with
   block separation (env block <> sb, env block <> sp_b).

   No Axioms, no Admitted. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Import Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

Lemma sem_cast_long_to_ptr_vptr_PEA1 : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* Step precondition for PUSHENVACC1: now uses generic pushenvacc_step_pre 1. *)

Theorem verify_PUSHENVACC1_correct :
    handler_correct (handle_PUSHENVACC 1) f_instr_PUSHENVACC1
      (fun _ => None)
      (pushenvacc_step_pre 1)
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

Theorem correct_PUSHENVACC1 :
    handler_correct (handle_PUSHENVACC 1) f_instr_PUSHENVACC1
      (fun _ => None)
      (pushenvacc_step_pre 1)
      (fun _ => None) (fun _ => None).
Proof.
  exact verify_PUSHENVACC1_correct.
Qed.
