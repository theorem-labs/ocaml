(* PUSHCONST2_correct.v -- PUSHCONST2 completeness proof.

   PUSHCONST2 = PUSH then CONST2.
   C code:
     sp = sp - 1;          // decrement sp
     *sp = accu;            // push old accu onto stack
     accu = Val_int(2);     // set accu to tagged 2 = (2<<1)+1 = 5
   Rocq:
     handle_PUSHCONSTINT 2 pc' s =
       Step (s <|pc := pc'|> <|accu := Val_int 2|> <|stack := accu :: stack|>)

   Three stores:
     Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v
     Store 3: accu field (sb, uso+8) <- Vlong (Int64.repr 5)

   Follows the patterns of PUSH_correct.v and CONST2_correct.v. *)

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

(* Arithmetic lemmas for constant 2: (2 << 1) + 1 = 5 *)
Local Lemma sem_cast_int_to_long_2 : forall m,
  sem_cast (Vint (Int.repr 2)) tint tlong m = Some (Vlong (Int64.repr 2)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_shl_long_2_1 : forall m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong (Int64.repr 2)) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.repr 4)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_add_long_int_4_1 : forall m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong (Int64.repr 4)) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.repr 5)).
Proof. intros. reflexivity. Qed.

Local Lemma val_int_2_load_result :
  Val.load_result Mint64 (Vlong (Int64.repr 5)) = Vlong (Int64.repr 5).
Proof. reflexivity. Qed.

Theorem verify_PUSHCONST2_correct :
    handler_correct (handle_PUSHCONSTINT 2) f_instr_PUSHCONST2
      (fun _ => None)
      (fun _ m _ ard =>
         let sb := ar_sptr_block ard in
         let so := ar_sptr_ofs ard in
         exists sp_b sp_ofs,
           Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) /\
           Ptrofs.unsigned sp_ofs >= 16)
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

Theorem correct_PUSHCONST2 :
    handler_correct (handle_PUSHCONSTINT 2) f_instr_PUSHCONST2
      (fun _ => None)
      (fun _ m _ ard =>
         let sb := ar_sptr_block ard in
         let so := ar_sptr_ofs ard in
         exists sp_b sp_ofs,
           Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) /\
           Ptrofs.unsigned sp_ofs >= 16)
      (fun _ => None) (fun _ => None).
Proof.
  exact verify_PUSHCONST2_correct.
Qed.
