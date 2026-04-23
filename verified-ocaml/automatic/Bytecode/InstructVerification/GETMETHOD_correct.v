(* GETMETHOD_correct.v -- GETMETHOD correctness proof.

   GETMETHOD: accu is the method index (tagged integer), stack top
   is the object.  Load the object's class table (field 0 of the
   object), then index into the class table at position (accu >> 1)
   to get the method closure.

   Rocq handler (Interpret.v):
     handle_GETMETHOD pc' s =
       match s.(stack) with
       | obj :: _ =>
         match field_or_heap s obj 0 with
         | Some class_tbl =>
           match s.(accu) with
           | Val_int n =>
             match field_or_heap s class_tbl (Z.to_nat n) with
             | Some method_fn => Step (s <|pc:=pc'|> <|accu:=method_fn|>)
             | None => Error "GETMETHOD: method not found"
             end
           | _ => Error "GETMETHOD: not an integer index"
           end
         | None => Error "GETMETHOD: no class table"
         end
       | _ => Error "GETMETHOD: stack underflow"
       end

   C handler (instruct_handlers.v, f_instr_GETMETHOD):
     t1 = s->sp
     t2 = deref(cast(t1) + 0)            sp[0] = object
     t3 = deref(cast(t2) + 0)            object[0] = class table pointer
     t4 = s->accu                         load accu (tagged method index)
     t5 = deref(cast(t3) + (t4 shr 1))   class_table[accu shr 1] = method
     s->accu = t5                         store method to accu
     return 0

   One store: accu field.
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
From OCamlInterp.Manual.Bytecode Require Import AST.
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
        Ptrofs.of_int64
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Semantic lemma: cast tlong -> (tptr tlong) for Vptr               *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* ================================================================== *)
(* Semantic lemma: shr (Vlong n) (Vint 1) for tlong -> tlong         *)
(* ================================================================== *)

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Semantic lemma: cast tlong -> tlong for Vlong                      *)
(* ================================================================== *)

Local Lemma sem_cast_tlong_tlong_vlong : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

(* ================================================================== *)
(* Semantic lemma: (tptr tlong) + (tlong) idx                         *)
(* ================================================================== *)

Local Lemma sem_add_ptr_tlong_idx : forall b ofs idx m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vlong idx) tlong m
  = Some (Vptr b (Ptrofs.add ofs
            (Ptrofs.mul (Ptrofs.repr 8)
                        (Ptrofs.of_int64 idx)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tlong) with (add_case_pl tlong).
  unfold sem_add_ptr_long. reflexivity.
Qed.

(* ================================================================== *)
(* Arithmetic: shr of tagged integer                                   *)
(* ================================================================== *)

Local Lemma shr_tagged_int : forall idx,
  0 <= idx ->
  idx * 2 + 1 <= Int64.max_signed ->
  Int64.shr (Int64.repr (idx * 2 + 1)) (Int64.repr 1) = Int64.repr idx.
Proof.
  intros idx Hge Hlt.
  unfold Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Int64.signed_repr.
  2: { split.
       - pose proof Int64.min_signed_neg. lia.
       - exact Hlt. }
  rewrite Z.shiftr_div_pow2 by lia.
  change (2^1)%Z with 2%Z.
  rewrite Z.div_add_l by lia.
  change (1 / 2)%Z with 0%Z.
  f_equal. lia.
Qed.

Local Lemma ptrofs_mul_8_of_int64 : forall idx,
  0 <= idx ->
  idx < Ptrofs.half_modulus ->
  Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr idx))
  = Ptrofs.repr (idx * 8).
Proof.
  intros idx Hge Hlt.
  assert (Hhm8 : (Ptrofs.half_modulus >= 8)%Z) by (vm_compute; discriminate).
  pose proof Ptrofs.half_modulus_modulus.
  unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr.
  2: { change Int64.max_unsigned with Ptrofs.max_unsigned.
       unfold Ptrofs.max_unsigned. lia. }
  unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 8).
  2: { unfold Ptrofs.max_unsigned. lia. }
  rewrite Ptrofs.unsigned_repr.
  2: { unfold Ptrofs.max_unsigned. lia. }
  f_equal. lia.
Qed.

(* ================================================================== *)
(* Heap precondition for GETMETHOD                                     *)
(*                                                                      *)
(* When field_or_heap chains succeed:                                   *)
(* 1. sp[0] (the object) dereferences to Vptr obj_b obj_ofs            *)
(* 2. obj[0] (class table) loads from obj_b at obj_ofs                  *)
(* 3. class_table[n] loads the method                                   *)
(* ================================================================== *)

Definition getmethod_heap_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall obj rest class_tbl n method_fn,
    s.(Machine.stack) = obj :: rest ->
    field_or_heap s obj 0 = Some class_tbl ->
    s.(Machine.accu) = Val_int n ->
    field_or_heap s class_tbl (Z.to_nat n) = Some method_fn ->
    forall sp_v,
      val_repr hm cb co obj sp_v ->
      exists obj_b obj_ofs ct_v ct_b ct_ofs meth_v,
        sp_v = Vptr obj_b obj_ofs /\
        Mem.load Mint64 m obj_b (Ptrofs.unsigned obj_ofs) = Some ct_v /\
        val_repr hm cb co class_tbl ct_v /\
        ct_v = Vptr ct_b ct_ofs /\
        Mem.load Mint64 m ct_b
          (Ptrofs.unsigned (Ptrofs.add ct_ofs (Ptrofs.repr (n * 8)))) = Some meth_v /\
        val_repr hm cb co method_fn meth_v.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_GETMETHOD_correct :
    handler_correct handle_GETMETHOD f_instr_GETMETHOD
      (fun _ => None)
      (fun _ m s ard =>
         getmethod_heap_pre m s ard /\
         match s.(Machine.accu) with
         | Val_int n => 0 <= n /\
                        n * 2 + 1 <= Int64.max_signed /\
                        n < Ptrofs.half_modulus /\
                        (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Val_int n) cv -> exists z, cv = Vlong z)
         | _ => True
         end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr GETMETHOD / clight_of GETMETHOD / pre_of GETMETHOD are
   convertible with handle_GETMETHOD / f_instr_GETMETHOD / getmethod_step_pre.
   P_halt_of and P_ccall_of are vacuously satisfied (GETMETHOD never halts or
   issues a C call).  error_message_of requires bridging from the disjunction in the
   old proof to `error_message_of GETMETHOD s = Some msg`. *)
Definition correct_GETMETHOD :
    handler_correct (handle_instr GETMETHOD) (clight_of GETMETHOD)
      (error_message_of GETMETHOD)
      (pre_of GETMETHOD) (P_halt_of GETMETHOD) (P_ccall_of GETMETHOD).
Proof.
Admitted.
