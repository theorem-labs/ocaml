(* ENVACC2_correct.v -- ENVACC2 correctness proof.

   ENVACC2: accu = Field(env, 2), i.e., load field 2 from the closure
   environment pointed to by env.

   C handler: t1 = s->env; t2 = deref((long ptr)t1 + 2); s->accu = t2; return 0;

    Still admitted: the raw theorem uses an always-None error predicate,
    but ENVACC2 can error when env field 2 is unavailable. *)

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

Lemma sem_cast_long_to_ptr_vptr_EA2 : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_add_ptr_long_2 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint (Int.repr 2)) tint m
    = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Definition env_field_loadable_2
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  forall v,
    field_or_heap s s.(Machine.env) 2 = Some v ->
    forall env_v,
      val_repr hm cb co s.(Machine.env) env_v ->
      exists b ofs cv,
        env_v = Vptr b ofs /\
        b <> sb /\
        Mem.load Mint64 m b
          (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat 2 * 8)))) = Some cv /\
        val_repr hm cb co v cv.
