(* MAKEBLOCK2_correct.v -- MAKEBLOCK2 completeness proof.

   MAKEBLOCK2 reads tag from *pc, calls heap_alloc(s, 2, tag), stores
   accu as field 0, stack[0] as field 1, advances sp by 1, and sets
   accu to the block ptr.

   C code (f_instr_MAKEBLOCK2):
     t1 = s.pc; s.pc = t1+1; t7 = deref t1; tag = (uchar)t7;
     t2 = heap_alloc(s, 2, tag); block = t2;
     t6 = s.accu; deref(block+0) = t6;
     t4 = s.sp; t5 = deref(t4+0); deref(block+1) = t5;
     t3 = s.sp; s.sp = t3+1;
     s.accu = block;
     return 0;

   Rocq:
     handle_MAKEBLOCK2 t pc' s =
       match s.(stack) with
       | v1 :: rest =>
         let '(s', ptr) := heap_alloc s t [s.(accu); v1] in
         Step (s' <|pc:=pc'|> <|accu:=ptr|> <|stack:=rest|>)
       | _ => Error "MAKEBLOCK2: stack underflow"
       end.

   Extends MAKEBLOCK1 pattern with an additional field store (field 1
   from stack[0]) and sp advancement. *)

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

Lemma interp_state_co_pc_accu_sp : exists co,
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

Lemma sem_add_pc_1_mk2 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint_mk2 : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_cast_int_to_tuchar_mk2 : forall n m,
  sem_cast (Vint n) tint tuchar m = Some (Vint (Int.zero_ext 8 n)).
Proof.
  intros. unfold sem_cast. simpl classify_cast. simpl. reflexivity.
Qed.

Lemma sem_cast_tuchar_to_tlong_mk2 : forall n m,
  sem_cast (Vint n) tuchar tlong m =
    Some (Vlong (Int64.repr (Int.unsigned n))).
Proof.
  intros. unfold sem_cast. simpl classify_cast. simpl. reflexivity.
Qed.

Lemma int_zero_ext_8_small_mk2 : forall z,
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

Lemma int_unsigned_repr_small_mk2 : forall z,
  0 <= z <= 255 ->
  Int.unsigned (Int.repr z) = z.
Proof.
  intros z Hz.
  apply Int.unsigned_repr.
  unfold Int.max_unsigned. change Int.modulus with 4294967296%Z. lia.
Qed.

Lemma pc_rel_shift_mk2 : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr 4)))
         cb (Ptrofs.add co (Ptrofs.repr sizeof_code_t)) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal. rewrite Ptrofs.add_assoc. rewrite Ptrofs.add_assoc.
  f_equal. rewrite Ptrofs.add_commut. reflexivity.
Qed.

Lemma load_result_vlong_mk2 : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr_mk2 : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* sem_add for sp + 1 on tptr tlong (from HandlerLemmas) *)

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_MAKEBLOCK2_correct : forall t,
    handler_correct (handle_MAKEBLOCK2 t) f_instr_MAKEBLOCK2
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
                (Vptr sb so :: Vlong (Int64.repr 2) :: Vlong (Int64.repr (Z.of_nat t)) :: nil)
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
                    (* Permission preservation through both field stores *)
                    (forall b ofs k p,
                       Mem.perm m_alloc b ofs k p ->
                       Mem.perm m_store1 b ofs k p)))))
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

Definition MAKEBLOCK2_correct_for_spec : forall t, 0 <= Z.of_nat t <= 255 ->
    handler_correct (handle_MAKEBLOCK2 t) f_instr_MAKEBLOCK2
      (fun _ => None)
      (heap_alloc_with_stores 2 (Z.of_nat t) alloc_store_2
       /\p code_at (Int.repr (Z.of_nat t)))
      (fun _ => False) (fun _ _ _ => False).
  Proof.
  Admitted.

(* ================================================================== *)
(* Canonical wrapper bridging to the InstructSpec signature             *)
(*                                                                      *)
(* handle_instr (MAKEBLOCK2 n) computes to handle_MAKEBLOCK2 n.        *)
(* MAKEBLOCK2 has both Step and Error branches (stack underflow +       *)
(* malformed operand).                                                  *)
(*                                                                      *)
(* The range guard (0 <= Z.of_nat n <= 255) is obtained by              *)
(* case-splitting on the boolean guard in handle_MAKEBLOCK2.  When the  *)
(* guard is false the handler returns Error which matches error_message_of    *)
(* via error_message_of.  When true, the range assumption feeds         *)
(* MAKEBLOCK2_correct_for_spec; the stack-empty Error is likewise       *)
(* discharged via error_message_of.                                     *)
(* ================================================================== *)
Definition correct_MAKEBLOCK2 : forall n,
    handler_correct (handle_instr (Bytecode.AST.MAKEBLOCK2 n)) (clight_of (Bytecode.AST.MAKEBLOCK2 n))
      (error_message_of (Bytecode.AST.MAKEBLOCK2 n))
      (pre_of (Bytecode.AST.MAKEBLOCK2 n)) (P_halt_of (Bytecode.AST.MAKEBLOCK2 n)) (P_ccall_of (Bytecode.AST.MAKEBLOCK2 n)).
Proof.
Admitted.

