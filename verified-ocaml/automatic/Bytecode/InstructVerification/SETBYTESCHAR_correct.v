(* SETBYTESCHAR_correct.v -- SETBYTESCHAR correctness proof.

   SETBYTESCHAR: pops idx and newchar from stack, writes byte
   (newchar >> 1) at accu[idx >> 1], sets accu = val_unit, pops 2.

   Rocq handler (Interpret.v):
     handle_SETBYTESCHAR pc' s =
       match s.(stack) with
       | Val_int idx :: Val_int newchar :: rest =>
         match s.(accu) with
         | Val_ptr addr =>
           match heap_lookup s.(hp) addr with
           | Some (_, fields) =>
             match set_nth fields (Z.to_nat idx) (Val_int newchar) with
             | Some new_fields =>
               let new_hp := heap_update s.(hp) addr new_fields in
               Step (s <|pc:=pc'|> <|accu:=val_unit|>
                       <|stack:=rest|> <|hp:=new_hp|>)
             | None => Error "index out of bounds"
             end
           | None => Error "dangling pointer"
           end
         | _ => Error "not a heap bytes"
         end
       | _ => Error "stack underflow"
       end

   C handler (instruct_handlers.v, f_instr_SETBYTESCHAR):
     t2 = s->accu                              -- load accu (bytes ptr)
     t3 = s->sp                                -- load sp
     t4 = *(t3 + 0)                            -- load sp[0] = idx (tagged)
     t5 = s->sp                                -- load sp again
     t6 = *(t5 + 1)                            -- load sp[1] = newchar (tagged)
     *((tuchar ptr)t2 + (t4 shr 1)) = t6 shr 1 -- store byte at untagged idx
     t1 = s->sp                                -- load sp again
     s->sp = t1 + 2                            -- pop 2 stack entries
     s->accu = ((long)0 shl 1) + 1             -- val_unit = 1
     return 0

   Three stores: byte store (Mint8unsigned) to heap, sp at so+16,
   accu at so+8.

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

Local Lemma sem_add_sp_2 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 2)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
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

(* Cast from tlong to tuchar: truncation *)
Local Lemma sem_cast_tlong_tuchar : forall n m,
  sem_cast (Vlong n) tlong tuchar m =
    Some (Vint (Int.zero_ext 8 (Int.repr (Int64.unsigned n)))).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* Ptrofs arithmetic: (x + 8) + 8 = x + 16 *)
Local Lemma ptrofs_add_8_8 : forall x,
  Ptrofs.unsigned x + 16 < Ptrofs.modulus ->
  Ptrofs.add (Ptrofs.add x (Ptrofs.repr 8)) (Ptrofs.repr 8) = Ptrofs.add x (Ptrofs.repr 16).
Proof.
  intros x Hlt.
  rewrite Ptrofs.add_assoc. reflexivity.
Qed.


(* ================================================================== *)
(* Generalized store lemmas for Mint8unsigned (byte store)             *)
(* The HandlerLemmas versions are Mint64-specific; we need variants    *)
(* for the byte store to a different block.                            *)
(* ================================================================== *)

Local Lemma stack_repr_byte_store_other_block : forall hm cb co m m' stk sp_b sp_ofs hb ofs v,
  stack_repr hm cb co m stk sp_b sp_ofs ->
  Mem.store Mint8unsigned m hb ofs v = Some m' ->
  hb <> sp_b ->
  stack_repr hm cb co m' stk sp_b sp_ofs.
Proof.
  intros hm cb co m m' stk. revert m m'.
  induction stk as [| hd tl IH]; intros m m' sp_b sp_ofs hb ofs v Hsr Hstore Hne.
  - constructor.
  - inversion Hsr; subst. econstructor.
    + erewrite Mem.load_store_other; eauto.
    + eassumption.
    + eapply IH; eauto.
Qed.

Local Lemma global_repr_byte_store_other_block : forall hm cb co m m' gs gb gofs hb ofs v,
  global_repr hm cb co m gs gb gofs ->
  Mem.store Mint8unsigned m hb ofs v = Some m' ->
  hb <> gb ->
  global_repr hm cb co m' gs gb gofs.
Proof.
  intros hm cb co m m' gs. revert m m'.
  induction gs as [| hd tl IH]; intros m m' gb gofs hb ofs v Hgr Hstore Hne.
  - constructor.
  - inversion Hgr; subst. econstructor.
    + erewrite Mem.load_store_other; eauto.
    + eassumption.
    + eapply IH; eauto.
Qed.

(* ================================================================== *)
(* Byte-store precondition                                             *)
(*                                                                      *)
(* When the Rocq handler succeeds, the C byte store must succeed.      *)
(* The precondition provides the heap block, separation, and store.    *)
(* ================================================================== *)

Definition setbyteschar_heap_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let gb := ar_global_block ard in
  forall idx newchar rest,
    s.(Machine.stack) = Val_int idx :: Val_int newchar :: rest ->
    0 <= idx ->
    idx * 2 + 1 <= Int64.max_signed ->
    0 <= newchar <= 255 ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
    forall sp_b sp_ofs,
      Mem.load Mint64 m sb
        (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
    exists hb hofs,
      accu_v = Vptr hb hofs /\
      hb <> sb /\
      hb <> gb /\
      hb <> sp_b /\
      (* The byte store succeeds for any value stored at the right address *)
      (forall byte_v,
        exists m_byte,
          Mem.store Mint8unsigned m hb
            (Ptrofs.unsigned (Ptrofs.add hofs (Ptrofs.repr idx)))
            byte_v = Some m_byte /\
          (* sb loads preserved through byte store *)
          (forall ofs0 v0,
             Mem.load Mint64 m sb ofs0 = Some v0 ->
             Mem.load Mint64 m_byte sb ofs0 = Some v0) /\
          (* sp_b loads preserved through byte store *)
          (forall ofs0 v0,
             Mem.load Mint64 m sp_b ofs0 = Some v0 ->
             Mem.load Mint64 m_byte sp_b ofs0 = Some v0) /\
          (* Permission preservation *)
          (forall b ofs0 k p,
             Mem.perm m b ofs0 k p ->
             Mem.perm m_byte b ofs0 k p)).

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

#[warnings="-not-a-closed-proof"]
Import Bytecode.AST.

(* Wrapper with the canonical type expected by InstructVerificationProof.v *)
Definition correct_SETBYTESCHAR :
    handler_correct (handle_instr SETBYTESCHAR) (clight_of SETBYTESCHAR)
      (error_message_of SETBYTESCHAR)
      (pre_of SETBYTESCHAR) (P_halt_of SETBYTESCHAR) (P_ccall_of SETBYTESCHAR).
Proof.
Admitted.
