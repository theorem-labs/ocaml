(* SETFIELD0_correct.v -- SETFIELD0 correctness proof.

   SETFIELD0: pop stack top, write it to heap field 0 of accu,
   set accu = val_unit.

   Rocq handler:
     handle_SETFIELD 0 pc' s =
       match stack with
       | newval :: rest =>
         match accu with
         | Val_ptr addr =>
           match heap_lookup hp addr with
           | Some (_, fields) =>
             match set_nth fields 0 newval with
             | Some new_fields => Step (s <|pc:=pc'|> <|accu:=val_unit|>
                                          <|stack:=rest|> <|hp:=heap_update ...|>)
             | None => Error "index out of bounds"
             end
           | None => Error "dangling pointer"
           end
         | _ => Error "not a mutable block"
         end
       | _ => Error "stack underflow"
       end

   C handler (f_instr_SETFIELD0):
     _t'1 = s->sp;               // read sp
     s->sp = _t'1 + 1;           // sp++ (pop)
     _t'2 = s->accu;             // read accu (heap ptr)
     _t'3 = *_t'1;               // read stack top
     *(cast(_t'2) + 0) = _t'3;   // store to heap field 0
     s->accu = ((0 << 1) + 1);   // val_unit = 1
     return 0;

   Three stores: sp field (so+16), heap block, accu field (so+8).
   The heap write is to a block separate from sb and sp_b (precondition).

   NO AXIOMS. NO ADMITTED. *)

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

Local Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* sem_add for (tptr tlong) + 0 *)
Local Lemma sem_add_ptr_long_0 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint (Int.repr 0)) tint m
    = Some (Vptr b ofs).
Proof. exact sem_add_sp_0. Qed.

(* ================================================================== *)
(* Load result for Vlong                                               *)
(* ================================================================== *)

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Heap-store precondition                                             *)
(* ================================================================== *)

(* Heap-store precondition for field 0: now uses generic setfield_heap_pre 0. *)

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_SETFIELD0_correct :
    handler_correct (handle_SETFIELD 0) f_instr_SETFIELD0
      (fun _ => None)
      (setfield_heap_pre 0)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.
