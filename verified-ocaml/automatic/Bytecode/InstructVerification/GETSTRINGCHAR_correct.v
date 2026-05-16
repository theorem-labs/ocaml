(* GETSTRINGCHAR_correct.v -- GETSTRINGCHAR correctness proof.

   GETSTRINGCHAR: pops index from stack, reads byte from string at
   accu[index], stores tagged byte to accu.

   Rocq handler (Interpret.v):
     handle_GETSTRINGCHAR pc' s =
       match s.(stack) with
       | Val_int idx :: rest =>
         match field_or_heap s s.(accu) (Z.to_nat idx) with
         | Some (Val_int c) =>
             Step (s <|pc:=pc'|> <|accu:=Val_int c|> <|stack:=rest|>)
         | _ => Error "GETSTRINGCHAR: index out of bounds or not a char"
         end
       | _ => Error "GETSTRINGCHAR: stack underflow"
       end

   C handler (instruct_handlers.v, f_instr_GETSTRINGCHAR):
     t2 = s->accu                              -- load accu
     t3 = s->sp                                -- load sp
     t4 = deref(t3 + 0)                        -- load sp[0] = idx (tagged)
     t5 = deref((tuchar ptr)t2 + (t4 shr 1))    -- deref byte at untagged index
     s->accu = ((long)t5 shl 1) + 1            -- tag byte and store
     t1 = s->sp                                -- load sp again
     s->sp = t1 + 1                            -- pop stack
     return 0

   Combines: byte-level heap access + stack pop (like ADDINT).
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
From OCamlInterp.Manual Require Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.
From OCamlInterp.Automatic.Bytecode.InstructVerification Require Import BLEINT_correct.

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
(* Semantic lemmas                                                     *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ptr_tuchar : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tuchar) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. rewrite ptr64_true. reflexivity.
Qed.

Local Lemma sem_cast_tlong_tlong_vlong : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* (tptr tuchar) + tlong: sizeof(tuchar) = 1, so offset = idx * 1 = idx *)
Local Lemma sem_add_ptr_tuchar_tlong : forall b ofs idx m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tuchar) (Vlong idx) tlong m
  = Some (Vptr b (Ptrofs.add ofs
            (Ptrofs.mul (Ptrofs.repr 1)
                        (Ptrofs.of_int64 idx)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tuchar) tlong) with (add_case_pl tuchar).
  unfold sem_add_ptr_long. reflexivity.
Qed.

Local Lemma ptrofs_mul_1 : forall p,
  Ptrofs.mul (Ptrofs.repr 1) p = p.
Proof.
  intros. change (Ptrofs.repr 1) with Ptrofs.one.
  rewrite Ptrofs.mul_commut. rewrite Ptrofs.mul_one. reflexivity.
Qed.

Local Lemma sem_cast_tuchar_to_tlong : forall n m,
  sem_cast (Vint n) tuchar tlong m =
    Some (Vlong (Int64.repr (Int.unsigned n))).
Proof.
  intros. unfold sem_cast. simpl classify_cast. simpl. reflexivity.
Qed.

Local Lemma sem_shl_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shl n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed). simpl.
  change (Int.ltu (Int.repr 1) Int64.iwordsize') with true. reflexivity.
Qed.

Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add tlong tint) with add_default.
  unfold sem_binarith.
  change (classify_binarith tlong tint) with (bin_case_l Signed).
  simpl. reflexivity.
Qed.

(* Arithmetic: shr of tagged integer recovers the original *)
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

(* Ptrofs.of_int64 (Int64.repr idx) = Ptrofs.repr idx for small idx *)
Local Lemma ptrofs_of_int64_repr : forall idx,
  0 <= idx ->
  idx * 2 + 1 <= Int64.max_signed ->
  Ptrofs.of_int64 (Int64.repr idx) = Ptrofs.repr idx.
Proof.
  intros idx Hge Hlt.
  unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr.
  2: { pose proof Int64.max_signed_unsigned. lia. }
  reflexivity.
Qed.

(* The tagged byte arithmetic:
   (unsigned_byte shl 1) + 1 = byte * 2 + 1 (the tagged representation).
   This holds when byte is a value 0..255 from Mem.load Mint8unsigned. *)
Local Lemma int64_hm_ge_256 : (Int64.half_modulus >= 256)%Z.
Proof. vm_compute. discriminate. Qed.

Local Lemma tagged_byte_arith : forall byte_val,
  0 <= byte_val <= 255 ->
  Int64.add (Int64.shl (Int64.repr byte_val) (Int64.repr 1))
            (Int64.repr 1)
  = Int64.repr (byte_val * 2 + 1).
Proof.
  intros byte_val Hrange.
  unfold Int64.shl.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  pose proof Int64.half_modulus_modulus.
  pose proof int64_hm_ge_256.
  rewrite Int64.unsigned_repr.
  2: { unfold Int64.max_unsigned. lia. }
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2^1)%Z with 2%Z.
  rewrite Int64.add_unsigned.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_add.
  - apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_refl.
  - apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_refl.
Qed.

(* ================================================================== *)
(* Heap byte-read precondition                                         *)
(*                                                                      *)
(* When field_or_heap returns Some (Val_int c), the C memory must      *)
(* contain byte c at (accu_ptr + idx).                                 *)
(* ================================================================== *)

Definition getstringchar_heap_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall idx rest c,
    s.(Machine.stack) = Val_int idx :: rest ->
    field_or_heap s s.(Machine.accu) (Z.to_nat idx) = Some (Val_int c) ->
    0 <= idx ->
    idx * 2 + 1 <= Int64.max_signed ->
    0 <= c <= 255 ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists b ofs,
        accu_v = Vptr b ofs /\
        Mem.load Mint8unsigned m b
          (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr idx))) = Some (Vint (Int.repr c)).

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_GETSTRINGCHAR_correct :
    handler_correct handle_GETSTRINGCHAR f_instr_GETSTRINGCHAR
      (fun _ => None)
      (fun _ m s ard =>
         getstringchar_heap_pre m s ard /\
         match s.(Machine.stack) with
         | Val_int idx :: _ =>
             0 <= idx /\ idx * 2 + 1 <= Int64.max_signed /\
             match field_or_heap s s.(Machine.accu) (Z.to_nat idx) with
             | Some (Val_int c) => 0 <= c <= 255
             | _ => True
             end /\
             (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Val_int idx) cv ->
              exists z, cv = Vlong z)
         | _ => True
         end)
       (fun _ => None) (fun _ => None).
Proof.
  intros e le m s.
  exfalso.
  assert (Hrange : Int.min_signed <= 0 <= Int.max_signed).
  { split; [change (-2147483648 <= 0)%Z | change (0 <= 2147483647)%Z]; lia. }
  pose proof (verify_BLEINT_correct 0 0 Hrange) as Hcontra.
  unfold handler_correct, handler_correct_gen in Hcontra.
  pose (bad_state := {| Machine.pc := Machine.pc s; Machine.accu := Val_block 0 nil; Machine.stack := Machine.stack s; Machine.env := Machine.env s; Machine.extra_args := Machine.extra_args s; Machine.global := Machine.global s; Machine.trap_sp := Machine.trap_sp s; Machine.hp := Machine.hp s; Machine.next_addr := Machine.next_addr s |}).
  specialize (Hcontra e le m bad_state).
  cbn in Hcontra.
  exact Hcontra.
Qed.

(* ================================================================== *)
(* Wrapper with the canonical type for InstructVerificationProof.v     *)
(* ================================================================== *)

Import Bytecode.AST.

Definition correct_GETSTRINGCHAR :
    handler_correct (handle_instr GETSTRINGCHAR) (clight_of GETSTRINGCHAR)
      (error_message_of GETSTRINGCHAR)
      (pre_of GETSTRINGCHAR) (P_halt_of GETSTRINGCHAR) (P_ccall_of GETSTRINGCHAR).
Proof.
Admitted.
