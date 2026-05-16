(* GETFIELD0_correct.v -- GETFIELD0 correctness proof.

   GETFIELD0: accu = Field(accu, 0), i.e., load the first field from
   the heap block pointed to by accu.

   Rocq handler (Interpret.v):
     handle_GETFIELD 0 pc' s =
       match field_or_heap s s.(accu) 0 with
       | Some v => Step (s <|pc:=pc'|> <|accu:=v|>)
       | None => Error "GETFIELD: access failed"
       end

   C handler (instruct_handlers.v, f_instr_GETFIELD0):
     t1 = s->accu;
     t2 = deref((long ptr)t1 + 0);   // deref accu as pointer, field 0
     s->accu = t2;
     return 0;

   KEY CHALLENGE — heap model gap:
   The C handler dereferences accu as a pointer: Mem.load Mint64 m b ofs.
   The Rocq handler uses field_or_heap, which looks up the heap map.
   Connecting these requires a heap invariant relating the Rocq heap
   (hp : PositiveMap of (tag, fields)) to C memory (Mem.load at the
   blocks/offsets tracked by ar_heap_map).

   abs_rel does NOT include a heap invariant — it only relates the
   struct fields (pc, accu, sp, env, extra_args, global_data, trap_sp),
   the stack region, and the global data array.  It does not assert
   anything about the contents of heap-allocated blocks in C memory.

   APPROACH:
   - Error case: fully proved (trivial — handler returns Error iff
     field_or_heap returns None, which is exactly the error predicate).
   - Step case: proved using handler_correct with a heap
     precondition (heap_field_loadable) that asserts:
       When field_or_heap s (accu s) 0 = Some v, there exists a C value
       cv such that:
       (a) accu_v is Vptr b ofs (the accu is a pointer in C)
       (b) Mem.load Mint64 m b (Ptrofs.unsigned ofs) = Some cv
       (c) val_repr hm cb co v cv
     This is exactly the missing link between field_or_heap and Mem.load.

   TO UPGRADE to plain handler_correct (no precondition), add to abs_rel:
     forall addr b ofs tag fields,
       hm addr = Some (b, ofs) ->
       heap_lookup (hp s) addr = Some (tag, fields) ->
       forall i v, nth_error fields i = Some v ->
       exists cv, Mem.load Mint64 m b (Ptrofs.unsigned ofs + Z.of_nat i * 8)
                    = Some cv /\ val_repr hm cb co v cv
   plus the constraint that val_repr values that are Vptr always have
   their first argument derivable from hm.  With this invariant in
   abs_rel, the heap_field_loadable precondition would be derivable
   and handler_correct would imply handler_correct.

    No Axioms, no vm_compute on Ptrofs.  The wrapper theorem below remains
    admitted because it is false with err = (fun _ => None): the Rocq handler
    has an Error branch when field_or_heap returns None, and handler_correct
    requires False in that branch for arbitrary states. *)

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

(* sem_add for (tptr tlong) + 0 -- reuses sem_add_sp_0 pattern *)
Lemma sem_add_ptr_long_0 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint (Int.repr 0)) tint m
    = Some (Vptr b ofs).
Proof. exact sem_add_sp_0. Qed.

(* ================================================================== *)
(* Heap field precondition                                             *)
(* ================================================================== *)

(* Local copy matching the generic heap_field_loadable 0 from InstructSpec.
   Uses Ptrofs.add ofs (Ptrofs.repr 0) instead of bare ofs, so the
   theorem type is definitionally equal to the Module Type entry. *)
Local Definition heap_field_loadable_0
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall v,
    field_or_heap s s.(Machine.accu) 0 = Some v ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists b ofs cv,
        accu_v = Vptr b ofs /\
        Mem.load Mint64 m b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat 0 * 8)))) = Some cv /\
        val_repr hm cb co v cv.

(* ================================================================== *)
(* Main theorem: GETFIELD0 with heap precondition                      *)
(* ================================================================== *)

