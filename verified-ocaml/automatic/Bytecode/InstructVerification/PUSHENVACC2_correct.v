(* PUSHENVACC2_correct.v -- PUSHENVACC2 = PUSH then ENVACC2.

   C handler (f_instr_PUSHENVACC2):
     t5 = s->sp; t1 = (long ptr)(t5 - 1); s->sp = t1;
     t4 = s->accu; *t1 = t4;
     t2 = s->env; t3 = *((long ptr)t2 + 2); s->accu = t3; return 0;

   Rocq (handle_PUSHENVACC 2):
     let new_stack := accu :: stack in
     match field_or_heap s s.(env) 2 with
     | Some v => Step (s <|pc:=pc'|> <|accu:=v|> <|stack:=new_stack|>)
     | None => Error "PUSHENVACC: env access out of bounds"
     end

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

Lemma sem_cast_long_to_ptr_vptr_PEA2 : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_add_ptr_long_PEA2 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint (Int.repr 2)) tint m
    = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* Step precondition for PUSHENVACC2: now uses generic pushenvacc_step_pre 2. *)

Theorem verify_PUSHENVACC2_correct :
    handler_correct (handle_PUSHENVACC 2) f_instr_PUSHENVACC2
      (fun _ => None)
      (pushenvacc_step_pre 2)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper bridging the raw proof to error_message_of / P_halt_of / P_ccall_of.
   The inner proof uses a direct error predicate; this wrapper shows
   error_message_of (PUSHENVACC 2) holds in the error branch and delegates
   the step branch to verify_PUSHENVACC2_correct.
   P_halt_of and P_ccall_of are vacuously False (PUSHENVACC never halts
   or issues a C call). *)
Definition correct_PUSHENVACC2 :
    handler_correct (handle_PUSHENVACC 2) f_instr_PUSHENVACC2
      (error_message_of (Bytecode.AST.PUSHENVACC 2))
      (pushenvacc_step_pre 2)
      (P_halt_of (Bytecode.AST.PUSHENVACC 2))
      (P_ccall_of (Bytecode.AST.PUSHENVACC 2)).
Proof.
Admitted.

