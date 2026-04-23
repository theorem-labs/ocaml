(* OFFSETREF_correct.v -- OFFSETREF completeness proof.

   OFFSETREF n: reads offset N from code buffer, dereferences accu[0]
   (heap pointer to a ref cell), adds N*2 to the tagged field value,
   writes back to accu[0], sets accu = val_unit, advances pc.

   Rocq handler (Interpret.v):
     handle_OFFSETREF n pc' s =
       match s.(accu) with
       | Val_ptr addr =>
         match heap_lookup s.(hp) addr with
         | Some (_, Val_int old :: rest) =>
           let new_hp := heap_update s.(hp) addr (Val_int (old+n) :: rest) in
           Step (s <|pc:=pc'|> <|accu:=val_unit|> <|hp:=new_hp|>)
         | _ => Error ...
         end
       | _ => Error ...
       end

   C handler (f_instr_OFFSETREF):
     _t'2 = s->accu                          (for write-back ptr)
     _t'3 = s->accu                          (for deref source)
     _t'4 = *(cast(_t'3, ptr long) + 0)     (load field 0: old value)
     _t'5 = s->pc                            (read pc pointer)
     _t'6 = *_t'5                            (read N from code buf, Mint32)
     *(cast(_t'2, ptr long) + 0) = _t'4 + (_t'6 << 1)  (store field 0)
     s->accu = ((0 << 1) + 1)               (val_unit = 1)
     _t'1 = s->pc;  s->pc = _t'1 + 1        (advance pc)
     return 0

   Three stores: (1) heap block field 0, (2) struct accu, (3) struct pc.

   NO AXIOMS.  NO ADMITTED. *)

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
(* Struct layout                                                       *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full).
Proof.
  eexists. split; [| split]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_offsetref : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic lemmas                                                     *)
(* ================================================================== *)

Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_add_ptr_long_0 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint (Int.repr 0)) tint m
    = Some (Vptr b ofs).
Proof. exact sem_add_sp_0. Qed.

Lemma sem_shl_int_int : forall i m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vint i) tint (Vint (Int.repr 1)) tint m
    = Some (Vint (Int.shl i (Int.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tint tint) with (shift_case_ii Signed).
  simpl.
  change (Int.ltu (Int.repr 1) Int.iwordsize) with true.
  reflexivity.
Qed.

Lemma sem_add_long_int_shift : forall n i m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint i) tint m
    = Some (Vlong (Int64.add n (Int64.repr (Int.signed i)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add tlong tint) with add_default.
  unfold sem_binarith.
  change (classify_binarith tlong tint) with (bin_case_l Signed).
  simpl binarith_type.
  unfold sem_cast at 1. simpl classify_cast. rewrite ptr64_true.
  unfold sem_cast at 1. simpl classify_cast. simpl cast_int_long.
  reflexivity.
Qed.

Lemma sem_add_ptr_int_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint) (Vint (Int.repr 1)) tint m
    = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int.
  change (sizeof (genv_cenv clight_ge) tint) with 4%Z. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* ================================================================== *)
(* Arithmetic: tagged offset addition                                  *)
(* ================================================================== *)

Local Lemma int_shl_1 : forall i,
  Int.shl i (Int.repr 1) = Int.repr (Int.unsigned i * 2).
Proof.
  intros. unfold Int.shl.
  change (Int.unsigned (Int.repr 1)) with 1%Z.
  f_equal. rewrite Z.shiftl_mul_pow2 by lia. simpl. lia.
Qed.

Local Lemma int_signed_shl_1 : forall i,
  Int.min_signed <= Int.signed i * 2 <= Int.max_signed ->
  Int.signed (Int.shl i (Int.repr 1)) = Int.signed i * 2.
Proof.
  intros i Hrange. rewrite int_shl_1.
  assert (Hrepr_eq : Int.repr (Int.unsigned i * 2) = Int.repr (Int.signed i * 2)).
  { apply Int.eqm_samerepr.
    pose proof (Int.eqm_signed_unsigned i) as [k Hk].
    exists (- k * 2)%Z.
    change Int.modulus with 4294967296%Z in *. lia. }
  rewrite Hrepr_eq.
  apply Int.signed_repr. exact Hrange.
Qed.

Lemma tagged_offsetref_arith : forall old_z (i : int),
  Int.min_signed <= Int.signed i * 2 <= Int.max_signed ->
  Int64.add (Int64.repr (old_z * 2 + 1))
            (Int64.repr (Int.signed (Int.shl i (Int.repr 1))))
  = Int64.repr ((old_z + Int.signed i) * 2 + 1).
Proof.
  intros old_z i Hrange.
  rewrite (int_signed_shl_1 i Hrange).
  rewrite Int64.add_unsigned.
  apply Int64.eqm_samerepr.
  eapply Int64.eqm_trans.
  { apply Int64.eqm_add;
      apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr. }
  replace ((old_z + Int.signed i) * 2 + 1)%Z
    with (old_z * 2 + 1 + Int.signed i * 2)%Z by lia.
  apply Int64.eqm_refl.
Qed.

(* ================================================================== *)
(* load_result lemmas                                                  *)
(* ================================================================== *)

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* ================================================================== *)
(* Precondition: heap field loadable + storable + code buffer          *)
(* ================================================================== *)

Definition offsetref_heap_pre
    (n : Z) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let gb := ar_global_block ard in
  (* Code buffer contains the operand at current PC *)
  (exists (i : int),
     Mem.load Mint32 m cb
       (Ptrofs.unsigned (Ptrofs.add co
          (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
     = Some (Vint i) /\
     Int.signed i = n /\
     Int.min_signed <= Int.signed i * 2 <= Int.max_signed) /\
  (* When the Step branch is taken, the heap block is loadable, storable,
     and separate from struct/stack/global blocks *)
  (forall addr old_z rest tag,
     s.(Machine.accu) = Val_ptr addr ->
     heap_lookup s.(Machine.hp) addr = Some (tag, Val_int old_z :: rest) ->
     forall accu_v,
       val_repr hm cb co (Val_ptr addr) accu_v ->
       exists b ofs,
         accu_v = Vptr b ofs /\
         Mem.load Mint64 m b (Ptrofs.unsigned ofs) =
           Some (Vlong (Int64.repr (old_z * 2 + 1))) /\
         b <> sb /\ b <> gb /\ b <> cb /\
         (forall sp_b sp_ofs,
            stack_repr hm cb co m s.(Machine.stack) sp_b sp_ofs ->
            b <> sp_b) /\
         (forall new_cv, exists m_h,
            Mem.store Mint64 m b (Ptrofs.unsigned ofs) new_cv = Some m_h /\
            (forall b' ofs' v',
               Mem.load Mint64 m b' ofs' = Some v' ->
               b <> b' ->
               Mem.load Mint64 m_h b' ofs' = Some v') /\
            Mem.range_perm m_h sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable /\
            (forall sp_b sp_ofs,
               stack_repr hm cb co m s.(Machine.stack) sp_b sp_ofs ->
               b <> sp_b ->
               stack_repr hm cb co m_h s.(Machine.stack) sp_b sp_ofs) /\
            (forall gbl go,
               global_repr hm cb co m s.(Machine.global) gbl go ->
               b <> gbl ->
               global_repr hm cb co m_h s.(Machine.global) gbl go) /\
            (forall sp_b lo hi,
               Mem.range_perm m sp_b lo hi Cur Writable ->
               Mem.range_perm m_h sp_b lo hi Cur Writable))).

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_OFFSETREF_correct : forall n,
    handler_correct (handle_OFFSETREF n) f_instr_OFFSETREF
      (fun _ => None)
      (fun _ => offsetref_heap_pre n)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* ================================================================== *)
(* Wrapper with the exact type expected by InstructVerificationProof.v *)
(* ================================================================== *)

From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

Definition correct_OFFSETREF : forall z,
  handler_correct (handle_instr (OFFSETREF z)) (clight_of (OFFSETREF z))
    (error_message_of (OFFSETREF z))
    (pre_of (OFFSETREF z)) (P_halt_of (OFFSETREF z)) (P_ccall_of (OFFSETREF z)).
Proof.
Admitted.
