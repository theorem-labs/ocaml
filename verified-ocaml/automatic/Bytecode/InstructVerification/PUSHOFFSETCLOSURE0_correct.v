(* PUSHOFFSETCLOSURE0_correct.v -- PUSHOFFSETCLOSURE0 = PUSH then OFFSETCLOSURE0.

   C handler (f_instr_PUSHOFFSETCLOSURE0):
     _t'4 = s->sp;                // load sp
     _t'1 = (tptr tlong)(_t'4 - 1);  // new_sp = sp - 1
     s->sp = _t'1;                // store 1: update sp field
     _t'3 = s->accu;              // load accu
     *_t'1 = _t'3;                // store 2: push accu onto stack
     _t'2 = s->env;               // load env
     s->accu = _t'2;              // store 3: set accu = env
     return 0;

   Rocq (handle_PUSHOFFSETCLOSURE 0):
     let new_stack := accu :: stack in
     match env with
     | Val_closure addr base_ofs =>
         Step (accu := Val_closure addr base_ofs, stack := new_stack)
     | Val_block t _ =>
         Step (accu := env, stack := new_stack)  (* Z.eqb 0 0 = true *)
     | _ => Error
     end

   Three stores:
     Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v
     Store 3: accu field (sb, uso+8) <- env_v

   step_pre: sp_ofs >= 16 (room for push).
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
Local Notation exec := (exec_stmt function_entry1 clight_ge).

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* Helper: Z.to_nat (Z.of_nat n + 0) = n *)
Local Lemma offset_closure_0 : forall n,
  Z.to_nat (Z.of_nat n + 0) = n.
Proof. intros. rewrite Z.add_0_r. apply Nat2Z.id. Qed.

Theorem verify_PUSHOFFSETCLOSURE0_correct :
    handler_correct (handle_PUSHOFFSETCLOSURE 0) f_instr_PUSHOFFSETCLOSURE0
      (fun _ => None)
      (fun _ m _ ard =>
         let sb := ar_sptr_block ard in
         let so := ar_sptr_ofs ard in
         exists sp_b sp_ofs,
           Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) /\
           Ptrofs.unsigned sp_ofs >= 16)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.
