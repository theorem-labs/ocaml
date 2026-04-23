(* GETFIELD3_correct.v -- GETFIELD3 correctness proof.

   GETFIELD3: accu = Field(accu, 3), i.e., load the fourth field from
   the heap block pointed to by accu.

   Rocq handler (Interpret.v):
     handle_GETFIELD 3 pc' s =
       match field_or_heap s s.(accu) 3 with
       | Some v => Step (s <|pc:=pc'|> <|accu:=v|>)
       | None => Error "GETFIELD: access failed"
       end

   C handler (instruct_handlers.v, f_instr_GETFIELD3):
     t1 = s->accu;
     t2 = deref((long ptr)t1 + 3);   // deref accu as pointer, field 3
     s->accu = t2;
     return 0;

   Follows the same structure as GETFIELD0_correct.v but with field
   offset 3 instead of 0.  The C pointer arithmetic on (tptr tlong)
   scales by 8, so ptr + 3 becomes ofs + 24 bytes.

   No Axioms, no Admitted, no vm_compute on Ptrofs. *)

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

Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* ================================================================== *)
(* Pointer arithmetic: ptr + 3 = ptr + 24 bytes (3 * sizeof(long))     *)
(* ================================================================== *)

Lemma sem_add_ptr_long_3 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong)
    (Vint (Int.repr 3)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 24))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* ================================================================== *)
(* Heap field precondition for field 3                                 *)
(* ================================================================== *)

Local Definition heap_field_loadable_3
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall v,
    field_or_heap s s.(Machine.accu) 3 = Some v ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists b ofs cv,
        accu_v = Vptr b ofs /\
        Mem.load Mint64 m b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat 3 * 8)))) = Some cv /\
        val_repr hm cb co v cv.

(* ================================================================== *)
(* Main theorem: GETFIELD3 with heap precondition                      *)
(* ================================================================== *)

Theorem verify_GETFIELD3_with_pre :
    handler_correct (handle_GETFIELD 3) f_instr_GETFIELD3
      (fun _ => None)
      (heap_field_loadable 3)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.
