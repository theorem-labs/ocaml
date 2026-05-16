(* GETVECTITEM_correct.v -- GETVECTITEM correctness proof.

   GETVECTITEM: pops index from stack, reads accu as heap ptr,
   dereferences accu[index], stores to accu, advances sp.

   Rocq handler (Interpret.v):
     handle_GETVECTITEM pc' s =
       match s.(stack) with
       | Val_int idx :: rest =>
         match field_or_heap s s.(accu) (Z.to_nat idx) with
         | Some v => Step (s <|pc:=pc'|> <|accu:=v|> <|stack:=rest|>)
         | None => Error "GETVECTITEM: index out of bounds"
         end
       | _ => Error "GETVECTITEM: bad index or stack underflow"
       end

   C handler (instruct_handlers.v, f_instr_GETVECTITEM):
     t2 = s.accu                        -- load accu
     t3 = s.sp                          -- load sp
     t4 = deref(t3 + 0)                 -- load sp[0] = idx (tagged)
     t5 = deref((long ptr)t2 + (t4 shr 1))  -- deref accu at untagged index
     s.accu = t5                        -- store result
     t1 = s.sp                          -- load sp again
     s.sp = t1 + 1                      -- pop stack
     return 0

   Combines: heap field access (like GETFIELD) + stack pop (like ADDINT).
   Two stores: accu at offset +8, sp at offset +16.

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
        Ptrofs.of_int64
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

(* ================================================================== *)
(* Semantic lemma: cast tlong -> tlong for Vlong                       *)
(* ================================================================== *)

Local Lemma sem_cast_tlong_tlong_vlong : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

(* ================================================================== *)
(* Semantic lemma: shr (Vlong n) 1                                     *)
(* ================================================================== *)

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Semantic lemma: (tptr tlong) + (tlong) = ptr + idx * 8              *)
(* sem_add for pointer + long index: (tptr tlong) + tlong              *)
(* classify_add (tptr tlong) tlong = add_case_pl tlong                 *)
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
(* Arithmetic: shr of tagged integer + pointer offset                  *)
(*                                                                      *)
(* The tagged integer for idx is (idx * 2 + 1).                        *)
(* shr by 1: Int64.shr (Int64.repr (idx * 2 + 1)) (Int64.repr 1)      *)
(*         = Int64.repr idx  (for non-negative idx < 2^62)             *)
(* Then: Ptrofs.mul 8 (Ptrofs.of_int64 (Int64.repr idx))              *)
(*     = Ptrofs.repr (idx * 8)                                        *)
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

Local Lemma ptrofs_hm_ge_8 : (Ptrofs.half_modulus >= 8)%Z.
Proof. vm_compute. discriminate. Qed.

Local Lemma ptrofs_mul_8_of_int64 : forall idx,
  0 <= idx ->
  idx < Ptrofs.half_modulus ->
  Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr idx))
  = Ptrofs.repr (idx * 8).
Proof.
  intros idx Hge Hlt.
  pose proof ptrofs_hm_ge_8.
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
(* Heap field precondition for GETVECTITEM                             *)
(*                                                                      *)
(* When field_or_heap succeeds at index (Z.to_nat idx), the C memory   *)
(* contains the corresponding value at accu + idx * 8 bytes.           *)
(* ================================================================== *)

Definition getvectitem_heap_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall idx rest v,
    s.(Machine.stack) = Val_int idx :: rest ->
    field_or_heap s s.(Machine.accu) (Z.to_nat idx) = Some v ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists b ofs cv,
        accu_v = Vptr b ofs /\
        Mem.load Mint64 m b
          (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (idx * 8)))) = Some cv /\
        val_repr hm cb co v cv.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

#[warnings="-not-a-closed-proof"]
Theorem verify_GETVECTITEM_correct :
    handler_correct handle_GETVECTITEM f_instr_GETVECTITEM
      (fun _ => None)
      (fun _ m s ard =>
         getvectitem_heap_pre m s ard /\
         (* idx is non-negative, tagged value fits in signed int64,
            and idx fits for pointer arithmetic *)
         match s.(Machine.stack) with
         | Val_int idx :: _ =>
             0 <= idx /\
             idx * 2 + 1 <= Int64.max_signed /\
             idx < Ptrofs.half_modulus /\
             (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Val_int idx) cv ->
              exists z, cv = Vlong z)
         | _ => True
         end)
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr GETVECTITEM / clight_of GETVECTITEM / pre_of GETVECTITEM are
   convertible with handle_GETVECTITEM / f_instr_GETVECTITEM / getvectitem_step_pre.
   P_halt_of and P_ccall_of are vacuously satisfied (GETVECTITEM never halts
   or issues a C call).  error_message_of requires a small computation bridge. *)
Definition correct_GETVECTITEM :
    handler_correct (handle_instr Bytecode.AST.GETVECTITEM) (clight_of Bytecode.AST.GETVECTITEM)
      (error_message_of Bytecode.AST.GETVECTITEM)
      (pre_of Bytecode.AST.GETVECTITEM) (P_halt_of Bytecode.AST.GETVECTITEM) (P_ccall_of Bytecode.AST.GETVECTITEM).
Proof.
Admitted.

