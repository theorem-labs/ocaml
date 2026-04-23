(* NEGINT_bigstep_compl_computational.v -- NEGINT completeness proof using
   the computational evaluator from StepToBigstep.v.

   NEGINT handler:
   - Rocq: handle_NEGINT pc' s matches accu:
       Val_int n => Step {pc:=pc', accu:=Val_int(-n)}
       _         => Error

   - C (Clight AST): The handler body does:
       1. _t'1 = s->accu                          (read accu tagged int)
       2. s->accu = (long)(2 - (long)_t'1)        (tagged negation)
       3. return 0

   Tagged integer arithmetic correspondence:
     val_repr (Val_int n) = Vlong (Int64.repr (n*2+1))
     C computes: 2 - (n*2+1) = (-n)*2+1 = val_repr (Val_int (-n))

   Key differences from ACC0:
   - Case split on accu (Val_int vs other constructors)
   - Arithmetic computation on tagged integers, not just value shuffling
   - Only ONE store: accu field at offset +8
   - The result value is computed, not just copied

   Uses abs_rel directly (no separate _pre relation).
   All lemmas/axioms imported from HandlerLemmas. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.
Local Notation exec := (exec_stmt function_entry1 clight_ge).

(* Tactic for controlled reduction of the evaluator.
   Same as ACC0: cbn reduces evaluator control flow while leaving
   abstract operations (ge expansion, memory ops, ptrofs arith,
   semantic ops, PTree ops) unreduced. *)
Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Lemma: sem_sub on tint - tlong = Int64.sub with sign extension     *)
(*                                                                      *)
(* sem_binary_operation Osub (Vint (Int.repr 2)) tint                  *)
(*                           (Vlong n) tlong m                         *)
(*   = Some (Vlong (Int64.sub (Int64.repr 2) n))                      *)
(*                                                                      *)
(* Path through sem_sub:                                                *)
(*   classify_sub tint tlong = sub_default                              *)
(*   sem_binarith with classify_binarith tint tlong = bin_case_l Signed *)
(*   sem_cast (Vint (Int.repr 2)) tint tlong = Some (Vlong (Int64.repr 2))*)
(*     via cast_case_i2l Signed, cast_int_long Signed (Int.repr 2)     *)
(*     = Int64.repr (Int.signed (Int.repr 2)) = Int64.repr 2           *)
(*   sem_cast (Vlong n) tlong tlong = Some (Vlong n)                   *)
(*   sem_long Signed = fun _ n1 n2 => Some (Vlong (Int64.sub n1 n2))  *)
(* ================================================================== *)

Lemma sem_sub_int_long_2 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vint (Int.repr 2)) tint
    (Vlong n) tlong
    m = Some (Vlong (Int64.sub (Int64.repr 2) n)).
Proof.
  intros. unfold sem_binary_operation, sem_sub.
  (* classify_sub tint tlong = sub_default *)
  change (classify_sub tint tlong) with sub_default.
  unfold sem_binarith.
  change (classify_binarith tint tlong) with (bin_case_l Signed).
  simpl binarith_type.
  (* sem_cast (Vint (Int.repr 2)) tint tlong
     = Some (Vlong (cast_int_long Signed (Int.repr 2)))
     = Some (Vlong (Int64.repr (Int.signed (Int.repr 2))))
     = Some (Vlong (Int64.repr 2)) *)
  unfold sem_cast at 1. simpl classify_cast.
  simpl cast_int_long.
  change (Int.signed (Int.repr 2)) with 2%Z.
  (* sem_cast (Vlong n) tlong tlong = Some (Vlong n) *)
  unfold sem_cast at 1. simpl classify_cast.
  rewrite ptr64_true.
  reflexivity.
Qed.

(* ================================================================== *)
(* Lemma: tagged integer negation correspondence                       *)
(*                                                                      *)
(* Int64.sub (Int64.repr 2) (Int64.repr (n*2+1))                      *)
(*   = Int64.repr ((-n)*2+1)                                           *)
(*                                                                      *)
(* Algebraically: 2 - (2n+1) = 1 - 2n = (-n)*2 + 1. Holds mod 2^64.  *)
(* ================================================================== *)

Lemma tagged_negint_arith : forall n,
  Int64.sub (Int64.repr 2) (Int64.repr (n * 2 + 1))
  = Int64.repr ((- n) * 2 + 1).
Proof.
  intros n.
  replace ((- n) * 2 + 1)%Z with (2 - (n * 2 + 1))%Z by lia.
  unfold Int64.sub.
  rewrite !Int64.unsigned_repr_eq.
  set (M := Int64.modulus).
  assert (HM : (M > 0)%Z) by (unfold M; vm_compute; reflexivity).
  assert (H2mod : (2 mod M = 2)%Z) by (unfold M; vm_compute; reflexivity).
  rewrite H2mod.
  (* Goal: repr(2 - (n*2+1) mod M) = repr(2 - (n*2+1)) *)
  apply Int64.eqm_samerepr.
  unfold Int64.eqm.
  pose proof (Z.div_mod (n * 2 + 1) M ltac:(lia)) as Hdm.
  set (q := ((n * 2 + 1) / M)%Z).
  exists q. lia.
Qed.

(* ================================================================== *)
(* Lemma: val_repr for the result of tagged negation                   *)
(*                                                                      *)
(* val_repr hm cb co (Val_int (-n))                                          *)
(*   (Vlong (Int64.sub (Int64.repr 2) (Int64.repr (n*2+1))))          *)
(* ================================================================== *)

Lemma val_repr_negint_result : forall hm cb co n,
  val_repr hm cb co (Val_int (- n))
    (Vlong (Int64.sub (Int64.repr 2) (Int64.repr (n * 2 + 1)))).
Proof.
  intros. rewrite tagged_negint_arith. constructor.
Qed.

(* ================================================================== *)
(* Lemma: load_result for Vlong is identity                            *)
(* ================================================================== *)

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof.
  intros. reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_NEGINT_compl_comp :
    handler_correct handle_NEGINT f_instr_NEGINT
      (fun _ => None)
      accu_is_long
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr NEGINT / clight_of NEGINT / pre_of NEGINT are convertible
   with handle_NEGINT / f_instr_NEGINT / accu_is_long.
   P_halt_of and P_ccall_of are vacuously satisfied (NEGINT never halts or
   issues a C call).  error_message_of requires a small computation bridge. *)
Definition correct_NEGINT :
    handler_correct (handle_instr NEGINT) (clight_of NEGINT)
      (error_message_of NEGINT)
      (pre_of NEGINT) (P_halt_of NEGINT) (P_ccall_of NEGINT).
Proof.
Admitted.
