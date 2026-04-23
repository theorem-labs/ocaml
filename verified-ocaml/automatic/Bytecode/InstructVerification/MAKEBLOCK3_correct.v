(* MAKEBLOCK3_correct.v -- MAKEBLOCK3 completeness proof.

   MAKEBLOCK3 reads tag from *pc, calls heap_alloc(s, 3, tag), stores
   accu as field 0, stack[0] as field 1, stack[1] as field 2,
   advances sp by 2, and sets accu to the block ptr.

   C code (f_instr_MAKEBLOCK3):
     t1 = s.pc; s.pc = t1+1; t9 = deref t1; tag = (uchar)t9;
     t2 = heap_alloc(s, 3, tag); block = t2;
     t8 = s.accu; deref(block+0) = t8;
     t6 = s.sp; t7 = deref(t6+0); deref(block+1) = t7;
     t4 = s.sp; t5 = deref(t4+1); deref(block+2) = t5;
     t3 = s.sp; s.sp = t3+2;
     s.accu = block;
     return 0;

   Rocq:
     handle_MAKEBLOCK3 t pc' s =
       match s.(stack) with
       | v1 :: v2 :: rest =>
         let '(s', ptr) := heap_alloc s t [s.(accu); v1; v2] in
         Step (s' <|pc:=pc'|> <|accu:=ptr|> <|stack:=rest|>)
       | _ => Error "MAKEBLOCK3: stack underflow"
       end.

   Extends MAKEBLOCK2 pattern with an additional field store (field 2
   from stack[1]) and sp advancement by 2 instead of 1. *)

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
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
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
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_pc_accu_sp_mk3 : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Lemma sem_add_pc_1_mk3 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint_mk3 : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_cast_int_to_tuchar_mk3 : forall n m,
  sem_cast (Vint n) tint tuchar m = Some (Vint (Int.zero_ext 8 n)).
Proof.
  intros. unfold sem_cast. simpl classify_cast. simpl. reflexivity.
Qed.

Lemma sem_cast_tuchar_to_tlong_mk3 : forall n m,
  sem_cast (Vint n) tuchar tlong m =
    Some (Vlong (Int64.repr (Int.unsigned n))).
Proof.
  intros. unfold sem_cast. simpl classify_cast. simpl. reflexivity.
Qed.

Lemma int_zero_ext_8_small_mk3 : forall z,
  0 <= z <= 255 ->
  Int.zero_ext 8 (Int.repr z) = Int.repr z.
Proof.
  intros z Hz.
  apply Int.same_bits_eq; intros i Hi.
  rewrite Int.bits_zero_ext by lia.
  destruct (Coqlib.zlt i 8); auto.
  rewrite Int.testbit_repr by lia.
  symmetry.
  apply Zbits.Ztestbit_above with (n := 8%nat). simpl.
  change (two_power_nat 8) with 256%Z. lia. lia.
Qed.

Lemma int_unsigned_repr_small_mk3 : forall z,
  0 <= z <= 255 ->
  Int.unsigned (Int.repr z) = z.
Proof.
  intros z Hz.
  apply Int.unsigned_repr.
  unfold Int.max_unsigned. change Int.modulus with 4294967296%Z. lia.
Qed.

Lemma pc_rel_shift_mk3 : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr 4)))
         cb (Ptrofs.add co (Ptrofs.repr sizeof_code_t)) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal. rewrite Ptrofs.add_assoc. rewrite Ptrofs.add_assoc.
  f_equal. rewrite Ptrofs.add_commut. reflexivity.
Qed.

Lemma load_result_vlong_mk3 : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr_mk3 : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* sem_add for sp + 2 on tptr tlong *)
Lemma sem_add_sp_2 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 2)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_MAKEBLOCK3_correct : forall t,
    handler_correct (handle_MAKEBLOCK3 t) f_instr_MAKEBLOCK3
      (fun _ => None)
      (fun e m s ard =>
         let sb := ar_sptr_block ard in
         let so := ar_sptr_ofs ard in
         let cb := ar_code_base_block ard in
         let co := ar_code_base_ofs ard in
         let gb := ar_global_block ard in
         let sp_b := ar_stack_block ard in
         (* 0. e does not bind _heap_alloc *)
         e ! _heap_alloc = None /\
         (* 1. The code buffer contains Int.repr (Z.of_nat t) at the current PC *)
         Mem.load Mint32 m cb
           (Ptrofs.unsigned (Ptrofs.add co
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat t))) /\
         (* 2. t fits in unsigned char range *)
         (0 <= Z.of_nat t <= 255) /\
         (* 3. Heap map freshness: next_addr is not yet mapped *)
         (ar_heap_map ard) (next_addr s) = None /\
         (* 3a. Global block is valid *)
         Mem.valid_block m gb /\
         (* 4. Genv lookup for heap_alloc *)
         (exists b_ha,
            Genv.find_symbol (genv_genv ge) _heap_alloc = Some b_ha /\
            Genv.find_funct (genv_genv ge) (Vptr b_ha Ptrofs.zero) =
              Some heap_alloc_fundef) /\
         (* 5. heap_alloc: for any memory m', allocation succeeds *)
         (forall m',
            exists m_alloc new_b new_ofs,
              external_call heap_alloc_ef
                (Genv.to_senv (genv_genv ge))
                (Vptr sb so :: Vlong (Int64.repr 3) :: Vlong (Int64.repr (Z.of_nat t)) :: nil)
                m' E0 (Vptr new_b new_ofs) m_alloc /\
              (* Freshness: new block is fresh *)
              (forall b, Mem.valid_block m' b -> new_b <> b) /\
              (* Load preservation on existing blocks *)
              (forall b ofs chunk v,
                 Mem.load chunk m' b ofs = Some v -> b <> new_b ->
                 Mem.load chunk m_alloc b ofs = Some v) /\
              (* Permission preservation *)
              (forall b ofs k p,
                 Mem.valid_block m' b -> Mem.perm m' b ofs k p ->
                 Mem.perm m_alloc b ofs k p) /\
              (* Field 0 storable + load-back + other-block preservation *)
              (forall cv, exists m_store,
                 Mem.store Mint64 m_alloc new_b (Ptrofs.unsigned new_ofs) cv = Some m_store /\
                 Mem.load Mint64 m_store new_b (Ptrofs.unsigned new_ofs) =
                   Some (Val.load_result Mint64 cv) /\
                 (forall b ofs chunk v, b <> new_b ->
                    Mem.load chunk m_alloc b ofs = Some v ->
                    Mem.load chunk m_store b ofs = Some v) /\
                 (* Field 1 storable + load-back + other-block preservation *)
                 (forall cv1, exists m_store1,
                    Mem.store Mint64 m_store new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) cv1 = Some m_store1 /\
                    Mem.load Mint64 m_store1 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) =
                      Some (Val.load_result Mint64 cv1) /\
                    (forall b ofs chunk v, b <> new_b ->
                       Mem.load chunk m_store b ofs = Some v ->
                       Mem.load chunk m_store1 b ofs = Some v) /\
                    (* Field 2 storable + load-back + other-block preservation *)
                    (forall cv2, exists m_store2,
                       Mem.store Mint64 m_store1 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 16))) cv2 = Some m_store2 /\
                       Mem.load Mint64 m_store2 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 16))) =
                         Some (Val.load_result Mint64 cv2) /\
                       (forall b ofs chunk v, b <> new_b ->
                          Mem.load chunk m_store1 b ofs = Some v ->
                          Mem.load chunk m_store2 b ofs = Some v) /\
                       (* Permission preservation through all field stores *)
                       (forall b ofs k p,
                          Mem.perm m_alloc b ofs k p ->
                          Mem.perm m_store2 b ofs k p))))))
      (fun _ => False) (fun _ _ _ => False).
Proof. Admitted.

Definition MAKEBLOCK3_correct_for_spec : forall t, 0 <= Z.of_nat t <= 255 ->
    handler_correct (handle_MAKEBLOCK3 t) f_instr_MAKEBLOCK3
      (fun _ => None)
      (heap_alloc_with_stores 3 (Z.of_nat t) alloc_store_3
       /\p code_at (Int.repr (Z.of_nat t)))
      (fun _ => False) (fun _ _ _ => False).
  Proof.
Admitted.


(* Canonical wrapper: bridge from the per-instruction spec
   (handle_instr (MAKEBLOCK3 n), clight_of, pre_of, error_message_of,
   P_halt_of, P_ccall_of) to the existing proof.

   Admitted because the underlying verify_MAKEBLOCK3_correct proof
   needs updating after handler body regeneration (cpp shim migration),
   and because the canonical pre_of does not include the 0 <= tag <= 255
   range guard that the C handler requires. *)
Definition correct_MAKEBLOCK3 : forall n,
    handler_correct (handle_instr (Bytecode.AST.MAKEBLOCK3 n)) (clight_of (Bytecode.AST.MAKEBLOCK3 n))
      (error_message_of (Bytecode.AST.MAKEBLOCK3 n))
      (pre_of (Bytecode.AST.MAKEBLOCK3 n)) (P_halt_of (Bytecode.AST.MAKEBLOCK3 n)) (P_ccall_of (Bytecode.AST.MAKEBLOCK3 n)).
Proof. Admitted.
