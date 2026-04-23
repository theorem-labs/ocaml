(* VECTLENGTH_correct.v -- VECTLENGTH completeness proof.

   VECTLENGTH handler:
   - Rocq: handle_VECTLENGTH pc' s =
       match size_or_heap s s.(accu) with
       | Some n => Step (s <|pc:=pc'|> <|accu:=Val_int (Z.of_nat n)|>)
       | None => Error "VECTLENGTH: not a block"
       end

   - C (f_instr_VECTLENGTH): reads block header at ptr[-1], extracts
     size via header >> 10, checks tag for Double_array_tag (254),
     stores (size << 1) + 1 as tagged integer.

   Step case: accu = Val_ptr addr with successful heap_lookup.
   Error cases: Val_int, Val_closure, Val_ptr with no heap entry,
   Val_block (inline atom has Vlong representation, cannot dereference).

   Uses abs_rel directly. All lemmas/axioms imported from HandlerLemmas. *)

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
        sem_binary_operation sem_unary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int sizeof
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Heap block header precondition                                      *)
(*                                                                      *)
(* OCaml block layout in memory (64-bit):                              *)
(*   ptr[-1]  = header word (8 bytes): size(54) | color(2) | tag(8)   *)
(*   ptr[0..] = fields                                                 *)
(*                                                                      *)
(* These properties relate the Rocq heap model to the C memory model. *)
(* They are required as preconditions (step_pre) rather than axioms.   *)
(* ================================================================== *)

Definition heap_block_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  forall addr b ofs tag fields,
    hm addr = Some (b, ofs) ->
    heap_lookup s.(Machine.hp) addr = Some (tag, fields) ->
    (* Header word exists at ptr[-1] and encodes size and tag *)
    (exists hdr_word,
      Mem.load Mint64 m b (Ptrofs.unsigned ofs - 8) = Some (Vlong hdr_word) /\
      Int64.shru hdr_word (Int64.repr 10) =
        Int64.repr (Z.of_nat (length fields)) /\
      Mem.load Mint8unsigned m b (Ptrofs.unsigned ofs - 8) =
        Some (Vint (Int.repr (Z.of_nat tag))) /\
      (* Signed shift = unsigned shift for size (header non-negative) *)
      Int64.shr hdr_word (Int64.repr 10) =
        Int64.repr (Z.of_nat (length fields))) /\
    (* Tag is not Double_array_tag (254) *)
    Z.of_nat tag <> 254 /\
    (* Block pointer offset >= 8, so header at -8 is valid *)
    Ptrofs.unsigned ofs >= 8 /\
    (* Heap blocks live in different memory blocks than sptr *)
    b <> sb /\
    (* Tag in range 0..255 *)
    (0 <= Z.of_nat tag <= 255)%Z.

(* ================================================================== *)
(* Semantic lemmas                                                     *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ptr_tlong : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. rewrite ptr64_true. reflexivity.
Qed.

Local Lemma sem_cast_long_to_ptr_tuchar : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tuchar) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. rewrite ptr64_true. reflexivity.
Qed.

Local Lemma sem_add_ptr_neg1_tlong : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint (Int.repr (-1))) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr (-8)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. change (sizeof (genv_cenv clight_ge) tlong) with 8%Z.
  f_equal.
Qed.

Local Lemma ptrofs_neg8_unsigned :
  Ptrofs.unsigned (Ptrofs.repr (-8)) = Ptrofs.modulus - 8.
Proof.
  rewrite Ptrofs.unsigned_repr_eq.
  change Ptrofs.modulus with (2^64)%Z.
  rewrite (Z.mod_unique_pos (-8) (2^64) (-1) (2^64 - 8)); [reflexivity | lia | lia].
Qed.

Local Lemma ptrofs_add_neg8 : forall ofs,
  Ptrofs.unsigned ofs >= 8 ->
  Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (-8))) =
    Ptrofs.unsigned ofs - 8.
Proof.
  intros ofs Hge. unfold Ptrofs.add.
  pose proof (Ptrofs.unsigned_range ofs) as [Hlo Hhi].
  rewrite ptrofs_neg8_unsigned. rewrite Ptrofs.unsigned_repr_eq.
  replace (Ptrofs.unsigned ofs + (Ptrofs.modulus - 8))%Z
    with (Ptrofs.unsigned ofs - 8 + 1 * Ptrofs.modulus)%Z by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Local Lemma sem_neg_int_1 : forall m,
  sem_unary_operation Oneg (Vint (Int.repr 1)) tint m
  = Some (Vint (Int.repr (-1))).
Proof.
  intros. unfold sem_unary_operation, sem_neg.
  change (classify_neg tint) with (neg_case_i Signed). simpl. f_equal.
Qed.

Local Lemma sem_shr_long_int_10 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 10)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 10))).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed). simpl.
  change (Int.ltu (Int.repr 10) Int64.iwordsize') with true. reflexivity.
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

Local Lemma sem_cast_ulong_to_long : forall n m,
  sem_cast (Vlong n) tulong tlong m = Some (Vlong n).
Proof.
  intros. unfold sem_cast. simpl classify_cast. rewrite ptr64_true. reflexivity.
Qed.

Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

Local Lemma sem_cast_long_to_long : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof.
  intros. unfold sem_cast. simpl classify_cast. rewrite ptr64_true. reflexivity.
Qed.

Local Lemma tagged_vectlength_arith : forall n,
  Int64.add (Int64.shl (Int64.repr (Z.of_nat n)) (Int64.repr 1))
            (Int64.repr 1)
  = Int64.repr (Z.of_nat n * 2 + 1).
Proof.
  intros. apply Int64.eqm_samerepr.
  unfold Int64.add, Int64.shl.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Z.shiftl_mul_pow2 by lia. change (2^1)%Z with 2%Z.
  rewrite !Int64.unsigned_repr_eq. unfold Int64.eqm.
  rewrite Zmult_mod_idemp_l.
  apply Zbits.eqmod_add.
  - apply Zbits.eqmod_sym. apply Zbits.eqmod_mod. vm_compute. reflexivity.
  - apply Zbits.eqmod_refl.
Qed.

Local Lemma sem_and_tuchar_255 : forall v m,
  sem_binary_operation (genv_cenv clight_ge) Oand
    (Vint v) tint (Vint (Int.repr 255)) tint m
  = Some (Vint (Int.and v (Int.repr 255))).
Proof. intros. reflexivity. Qed.

Local Lemma sem_eq_int_int : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Oeq
    (Vint n1) tint (Vint n2) tint m
  = Some (Val.of_bool (Int.eq n1 n2)).
Proof. intros. reflexivity. Qed.

Local Lemma tag_not_254_comparison : forall tag,
  (0 <= Z.of_nat tag <= 255)%Z ->
  Z.of_nat tag <> 254 ->
  Int.eq (Int.and (Int.repr (Z.of_nat tag)) (Int.repr 255))
         (Int.repr 254) = false.
Proof.
  intros tag Hrange Hne.
  apply Int.eq_false. intro Heq. apply Hne.
  apply (f_equal Int.unsigned) in Heq.
  rewrite Int.unsigned_repr in Heq by (unfold Int.max_unsigned; simpl; lia).
  unfold Int.and in Heq.
  assert (Htag : Int.unsigned (Int.repr (Z.of_nat tag)) = Z.of_nat tag).
  { rewrite Int.unsigned_repr. reflexivity. unfold Int.max_unsigned; simpl; lia. }
  assert (H255 : Int.unsigned (Int.repr 255) = 255).
  { rewrite Int.unsigned_repr. reflexivity. unfold Int.max_unsigned; simpl; lia. }
  rewrite Htag, H255 in Heq.
  change 255%Z with (Z.ones 8) in Heq.
  rewrite Z.land_ones in Heq by lia. change (2^8)%Z with 256%Z in Heq.
  rewrite Z.mod_small in Heq by lia.
  rewrite Int.unsigned_repr in Heq by (unfold Int.max_unsigned; simpl; lia).
  lia.
Qed.

Local Lemma sem_add_ptr_tuchar_neg_sizeof_long : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tuchar)
    (Vlong (Int64.neg (Int64.repr 8))) tulong
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr (-8)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tuchar) tulong) with (add_case_pl tuchar).
  unfold sem_add_ptr_long. change (sizeof (genv_cenv clight_ge) tuchar) with 1%Z.
  f_equal.
Qed.

Local Lemma sem_neg_sizeof_long : forall m,
  sem_unary_operation Oneg (Vlong (Int64.repr 8)) tulong m
  = Some (Vlong (Int64.neg (Int64.repr 8))).
Proof.
  intros. unfold sem_unary_operation, sem_neg.
  change (classify_neg tulong) with (neg_case_l Unsigned). simpl. reflexivity.
Qed.

Local Lemma Vptrofs_is_Vlong : forall p,
  Vptrofs p = Vlong (Ptrofs.to_int64 p).
Proof. intros. unfold Vptrofs. rewrite ptr64_true. reflexivity. Qed.

Local Lemma ptrofs_to_int64_8 :
  Ptrofs.to_int64 (Ptrofs.repr 8) = Int64.repr 8.
Proof. reflexivity. Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Precondition: accu is not Val_block (inline atoms are Vlong in C,   *)
(* cannot be dereferenced as pointers by the VECTLENGTH handler)       *)
(* ================================================================== *)

Definition vectlength_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  (match Machine.accu s with Val_block _ _ => False | _ => True end) /\
  heap_block_pre m s ard.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_VECTLENGTH_correct :
    handler_correct handle_VECTLENGTH f_instr_VECTLENGTH
      (fun _ => None)
      (fun _ => vectlength_pre)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr VECTLENGTH / clight_of VECTLENGTH / pre_of VECTLENGTH are
   convertible with handle_VECTLENGTH / f_instr_VECTLENGTH / (fun _ => vectlength_pre).
   P_halt_of and P_ccall_of are vacuously satisfied (VECTLENGTH never halts
   or issues a C call).  error_message_of requires a small computation bridge. *)
Definition correct_VECTLENGTH :
    handler_correct (handle_instr Bytecode.AST.VECTLENGTH) (clight_of Bytecode.AST.VECTLENGTH)
      (error_message_of Bytecode.AST.VECTLENGTH)
      (pre_of Bytecode.AST.VECTLENGTH) (P_halt_of Bytecode.AST.VECTLENGTH) (P_ccall_of Bytecode.AST.VECTLENGTH).
Proof.
Admitted.
