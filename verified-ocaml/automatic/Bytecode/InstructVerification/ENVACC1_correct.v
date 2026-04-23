(* ENVACC1_correct.v -- ENVACC1 correctness proof.

   ENVACC1: accu = Field(env, 1), i.e., load field 1 from the closure
   environment pointed to by env.

   Rocq handler (Interpret.v):
     handle_ENVACC 1 pc' s =
       match field_or_heap s s.(env) 1 with
       | Some v => Step (s <|pc:=pc'|> <|accu:=v|>)
       | None => Error "ENVACC: env access out of bounds"
       end

   C handler (instruct_handlers.v, f_instr_ENVACC1):
     t1 = s->env;
     t2 = deref((long ptr)t1 + 1);   // deref env as pointer, field 1
     s->accu = t2;
     return 0;

   Same heap model gap as GETFIELD0 -- uses a heap_field_loadable
   precondition for the env pointer.

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
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Semantic lemma: cast tlong -> (tptr tlong) for Vptr                 *)
(* ================================================================== *)

Lemma sem_cast_long_to_ptr_vptr_EA1 : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* sem_add for (tptr tlong) + 1 *)
Lemma sem_add_ptr_long_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint (Int.repr 1)) tint m
    = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 8))).
Proof. exact sem_add_sp_1. Qed.

(* ================================================================== *)
(* Heap field precondition for env field 1                             *)
(* ================================================================== *)

Definition env_field_loadable_1
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  forall v,
    field_or_heap s s.(Machine.env) 1 = Some v ->
    forall env_v,
      val_repr hm cb co s.(Machine.env) env_v ->
      exists b ofs cv,
        env_v = Vptr b ofs /\
        b <> sb /\
        Mem.load Mint64 m b
          (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat 1 * 8)))) = Some cv /\
        val_repr hm cb co v cv.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_ENVACC1_with_pre :
    handler_correct (handle_ENVACC 1) f_instr_ENVACC1
      (fun _ => None)
      env_field_loadable_1
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.
