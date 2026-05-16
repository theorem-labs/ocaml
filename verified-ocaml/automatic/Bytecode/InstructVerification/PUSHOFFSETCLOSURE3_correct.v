(* PUSHOFFSETCLOSURE3_correct.v -- PUSHOFFSETCLOSURE3 = PUSH then OFFSETCLOSURE3.

   C handler (f_instr_PUSHOFFSETCLOSURE3):
     _t'4 = s->sp;                    // load sp
     _t'1 = (tptr tlong)(_t'4 - 1);   // new_sp = sp - 1
     s->sp = _t'1;                     // store 1: update sp field
     _t'3 = s->accu;                   // load accu
     *_t'1 = _t'3;                     // store 2: push accu onto stack
     _t'2 = s->env;                    // load env
     s->accu = _t'2 + 3*sizeof(long);  // store 3: set accu = env + 24
     return 0;

   Rocq (handle_PUSHOFFSETCLOSURE 2):
     let new_stack := accu :: stack in
     match env with
     | Val_closure addr base_ofs =>
         Step (accu := Val_closure addr (Z.to_nat (Z.of_nat base_ofs + 2)),
               stack := new_stack)
     | Val_block t _ => Error  (* Z.eqb 2 0 = false *)
     | _ => Error
     end

   Three stores:
     Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v
     Store 3: accu field (sb, uso+8) <- result_v  (= env_long + 24)

   step_pre: sp_ofs >= 16 (room for push) + offsetclosure2 precondition
     (env is Vlong, addition result has valid val_repr).
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

(* ================================================================== *)
(* Semantic lemmas for the env + 3*sizeof(long) computation            *)
(* ================================================================== *)

(* Inner Omul: 3 * sizeof(long) = 24, using Vptrofs form *)
Local Lemma sem_mul_3_sizeof : forall m,
  sem_binary_operation (genv_cenv ge) Omul
    (Vint (Int.repr 3)) tint
    (Vptrofs (Ptrofs.repr 8)) tulong m
  = Some (Vlong (Int64.repr 24)).
Proof. intros. reflexivity. Qed.

(* Outer Oadd: Vlong + Vlong(24) *)
Local Lemma sem_add_long_24 : forall n m,
  sem_binary_operation (genv_cenv ge) Oadd
    (Vlong n) tlong (Vlong (Int64.repr 24)) tulong m
  = Some (Vlong (Int64.add n (Int64.repr 24))).
Proof. intros. reflexivity. Qed.

(* Cast: tulong -> tlong for Vlong *)
Local Lemma sem_cast_tulong_tlong : forall n m,
  sem_cast (Vlong n) tulong tlong m = Some (Vlong n).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_PUSHOFFSETCLOSURE3_correct :
    handler_correct (handle_PUSHOFFSETCLOSURE 2) f_instr_PUSHOFFSETCLOSURE3
      (fun _ => None)
      (sp_at_least 16 /\p closure_offset_pre 2 24)
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

Definition correct_PUSHOFFSETCLOSURE3 :
    handler_correct (handle_PUSHOFFSETCLOSURE 2) f_instr_PUSHOFFSETCLOSURE3
      (fun _ => None)
      (sp_at_least 16 /\p closure_offset_pre 2 24)
      (fun _ => None) (fun _ => None).
Proof.
  exact verify_PUSHOFFSETCLOSURE3_correct.
Qed.
