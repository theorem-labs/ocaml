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
    handler_correct_v1 handle_VECTLENGTH f_instr_VECTLENGTH
      (fun _ => vectlength_pre)
      (fun _ s => size_or_heap s s.(Machine.accu) = None)
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct_v1, handle_VECTLENGTH.

  (* Case split on accu -- constructor order: Val_int, Val_block, Val_ptr, Val_closure *)
  destruct (Machine.accu s) as [z | tag0 fields0 | addr | addr0 ofs0] eqn:Haccu_eq.

  (* Case 1: accu = Val_int z => size_or_heap = None => Error *)
  { simpl. reflexivity. }

  (* Case 2: accu = Val_block tag0 fields0 => size_or_heap = Some (length fields0).
     The C code dereferences accu as a pointer, but Val_block maps to Vlong.
     Excluded by vectlength_pre. *)
  { simpl. intros ard _ Hpre. exfalso.
    unfold vectlength_pre in Hpre. destruct Hpre as [Hpre_block _].
    rewrite Haccu_eq in Hpre_block. exact Hpre_block. }

  (* Case 3: accu = Val_ptr addr *)
  {
    simpl.
    destruct (heap_lookup (Machine.hp s) addr) as [[tag fields]|] eqn:Hheap.

    (* Case 2a: heap_lookup = Some => Step *)
    {
      intros ard Hpre Hstep_pre.
      unfold abs_rel_with_ard in Hpre.
      set (sb := ar_sptr_block ard) in *.
      set (so := ar_sptr_ofs ard) in *.
      set (hm := ar_heap_map ard) in *.
      set (cb := ar_code_base_block ard) in *.
      set (co := ar_code_base_ofs ard) in *.
      destruct Hpre as (Hle_s &
        [pc_ptr [Hpc_load Hpc_rel]] &
        [accu_v [Haccu_load Haccu_repr]] &
        [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
        [env_v [Henv_load Henv_repr]] &
        Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
        [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
      subst sp_ptr.

      pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
      pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.

      rewrite Haccu_eq in Haccu_repr.
      (* Protect gd_ptr from bare subst *)
      revert Hgd_load Hgd_eq Hglobal_repr Hgb_ne_sb.
      inversion Haccu_repr; subst.
      intros Hgd_load Hgd_eq Hglobal_repr Hgb_ne_sb.
      (* vr_ptr: b, ofs, and heap map hypothesis are in context *)
      rename b into hb. rename ofs into ho.
      match goal with
      | [ H : hm _ = Some (hb, ho) |- _ ] => rename H into Hhm
      end.

      (* Extract heap block facts from precondition *)
      unfold vectlength_pre in Hstep_pre.
      destruct Hstep_pre as [_ Hheap_pre].
      unfold heap_block_pre in Hheap_pre.
      specialize (Hheap_pre addr hb ho tag fields Hhm Hheap).
      destruct Hheap_pre as
        [[hdr_word [Hhdr_load [Hhdr_size [Htag_byte_load Hhdr_shr]]]]
         [Htag_ne_254 [Hho_ge_8 [Hhb_ne_sb Htag_range]]]].

      destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

      set (n := length fields) in *.
      set (cv_size := Vlong (Int64.shr hdr_word (Int64.repr 10))) in *.
      set (cv_result := Vlong (Int64.add
        (Int64.shl (Int64.shr hdr_word (Int64.repr 10)) (Int64.repr 1))
        (Int64.repr 1))).

      destruct (store_succeeds_sb m sb so 8 (Vptr hb ho) Hsb_writable Haccu_load ltac:(lia) ltac:(lia) cv_result)
        as [m' Hstore].

      set (cv_accu := Vptr hb ho) in *.
      set (cv_hdr := Vlong hdr_word) in *.
      set (cv_tag_byte := Vint (Int.repr (Z.of_nat tag))) in *.

      set (le' := PTree.set _t'2 cv_tag_byte
                    (PTree.set _t'1 cv_accu
                      (PTree.set _size cv_size
                        (PTree.set _t'4 cv_hdr
                          (PTree.set _t'3 cv_accu le))))).

      exists le'. exists m'.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* Part 1: exec -- explicit big-step proof *)
      {
        (* Intermediate local environments *)
        set (le1 := PTree.set _t'3 cv_accu le).
        set (le2 := PTree.set _t'4 cv_hdr le1).
        set (le3 := PTree.set _size cv_size le2).
        set (le4 := PTree.set _t'1 cv_accu le3).
        assert (Hle'_eq : le' = PTree.set _t'2 cv_tag_byte le4).
        { subst le' le4 le3 le2 le1. reflexivity. }

        (* Outer: PartA ; PartB *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le3) (m1 := m).

        (* PartA: (Sset _t'3) ; ((Sset _t'4) ; (Sset _size)) *)
        {
          apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m).

          (* Sset _t'3 = s->accu *)
          { apply exec_Sset.
            eapply eval_Elvalue.
            - eapply eval_Efield_struct.
              + eapply eval_Elvalue.
                * eapply eval_Ederef. eapply eval_Etempvar. exact Hle_s.
                * apply deref_loc_copy. reflexivity.
              + reflexivity.
              + exact Hco.
              + exact Haccu_offset.
            - apply deref_loc_value with (chunk := Mint64).
              + reflexivity.
              + simpl. rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
                exact Haccu_load. }

          (* (Sset _t'4) ; (Sset _size) *)
          {
            apply exec_Sseq_1 with (t1 := E0) (le1 := le2) (m1 := m).

            (* Sset _t'4: load header word *)
            { apply exec_Sset.
              eapply eval_Elvalue.
              - eapply eval_Ederef.
                eapply eval_Ebinop.
                + eapply eval_Ecast.
                  * eapply eval_Etempvar. subst le1. rewrite PTree.gss. reflexivity.
                  * unfold cv_accu. apply sem_cast_long_to_ptr_tlong.
                + eapply eval_Eunop.
                  * eapply eval_Econst_int.
                  * apply sem_neg_int_1.
                + unfold cv_accu. apply sem_add_ptr_neg1_tlong.
              - apply deref_loc_value with (chunk := Mint64).
                + reflexivity.
                + simpl. rewrite ptrofs_add_neg8 by lia. exact Hhdr_load. }

            (* Sset _size = _t'4 >> 10 *)
            { apply exec_Sset.
              eapply eval_Ebinop.
              - eapply eval_Etempvar. subst le2. rewrite PTree.gss. reflexivity.
              - eapply eval_Econst_int.
              - unfold cv_hdr. apply sem_shr_long_int_10. }
          }
        }

        (* PartB: PartB1 ; PartB2 *)
        {
          apply exec_Sseq_1 with (t1 := E0) (le1 := le') (m1 := m).

          (* PartB1: (Sset _t'1) ; ((Sset _t'2) ; Sifthenelse) *)
          {
            apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m).

            (* Sset _t'1 = s->accu (second load) *)
            { apply exec_Sset.
              eapply eval_Elvalue.
              - eapply eval_Efield_struct.
                + eapply eval_Elvalue.
                  * eapply eval_Ederef. eapply eval_Etempvar.
                    subst le3 le2 le1.
                    repeat (rewrite PTree.gso by (compute; congruence)).
                    exact Hle_s.
                  * apply deref_loc_copy. reflexivity.
                + reflexivity.
                + exact Hco.
                + exact Haccu_offset.
              - apply deref_loc_value with (chunk := Mint64).
                + reflexivity.
                + simpl. rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
                  exact Haccu_load. }

            (* (Sset _t'2) ; Sifthenelse *)
            {
              apply exec_Sseq_1 with (t1 := E0) (le1 := le') (m1 := m).

              (* Sset _t'2: load tag byte *)
              { rewrite Hle'_eq. apply exec_Sset.
                eapply eval_Elvalue.
                - eapply eval_Ederef.
                  eapply eval_Ebinop.
                  + eapply eval_Ecast.
                    * eapply eval_Etempvar. subst le4. rewrite PTree.gss. reflexivity.
                    * unfold cv_accu. apply sem_cast_long_to_ptr_tuchar.
                  + eapply eval_Eunop.
                    * eapply eval_Esizeof.
                    * change (sizeof (genv_cenv clight_ge) tlong) with 8%Z.
                      rewrite Vptrofs_is_Vlong, ptrofs_to_int64_8.
                      apply sem_neg_sizeof_long.
                  + unfold cv_accu. apply sem_add_ptr_tuchar_neg_sizeof_long.
                - apply deref_loc_value with (chunk := Mint8unsigned).
                  + reflexivity.
                  + simpl. rewrite ptrofs_add_neg8 by lia. exact Htag_byte_load. }

              (* Sifthenelse: tag & 255 == 254 => false => Sskip *)
              { eapply exec_Sifthenelse.
                - rewrite Hle'_eq.
                  eapply eval_Ebinop.
                  + eapply eval_Ebinop.
                    * eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
                    * eapply eval_Econst_int.
                    * unfold cv_tag_byte. reflexivity.
                  + eapply eval_Econst_int.
                  + apply sem_eq_int_int.
                - unfold cast_int_int.
                  rewrite (tag_not_254_comparison tag Htag_range Htag_ne_254).
                  reflexivity.
                - simpl. apply exec_Sskip. }
            }
          }

          (* PartB2: (Sassign s->accu) ; (Sreturn 0) *)
          {
            apply exec_Sseq_1 with (t1 := E0) (le1 := le') (m1 := m').

            (* Sassign: s->accu = (cast _size tlong << 1) + 1 *)
            { eapply exec_Sassign.
              - eapply eval_Efield_struct.
                + eapply eval_Elvalue.
                  * eapply eval_Ederef. eapply eval_Etempvar.
                    rewrite Hle'_eq. subst le4 le3 le2 le1.
                    repeat (rewrite PTree.gso by (compute; congruence)).
                    exact Hle_s.
                  * apply deref_loc_copy. reflexivity.
                + reflexivity.
                + exact Hco.
                + exact Haccu_offset.
              - eapply eval_Ebinop.
                + eapply eval_Ebinop.
                  * eapply eval_Ecast.
                    { eapply eval_Etempvar.
                      rewrite Hle'_eq. subst le4 le3 le2.
                      repeat (rewrite PTree.gso by (compute; congruence)).
                      rewrite PTree.gss. reflexivity. }
                    { apply sem_cast_ulong_to_long. }
                  * eapply eval_Econst_int.
                  * apply sem_shl_long_int_1.
                + eapply eval_Econst_int.
                + apply sem_add_long_int_1.
              - apply sem_cast_long_to_long.
              - apply assign_loc_value with (chunk := Mint64).
                + reflexivity.
                + simpl. rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
                  fold cv_result. exact Hstore. }

            (* Sreturn (Some 0) *)
            { apply exec_Sreturn_some. eapply eval_Econst_int. }
          }
        }
      }

      (* Part 2: abs_rel for post-state *)
      {
        exists ard.
        set (uso := Ptrofs.unsigned so) in *.

        assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) cv_result pc_ptr
                   Hstore Hpc_load). left. lia. }

        assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) cv_result (Vptr sp_b sp_ofs)
                   Hstore Hsp_load). right. lia. }

        assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) cv_result env_v
                   Hstore Henv_load). right. lia. }

        assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) cv_result _
                   Hstore Hextra_load). right. lia. }

        assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) cv_result gd_ptr
                   Hstore Hgd_load). right. lia. }

        assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) cv_result ts_ptr
                   Hstore Hts_load). right. lia. }

        assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some cv_result).
        { pose proof (load_after_store_same m m' sb (uso + 8) cv_result Hstore) as Htmp.
          subst cv_result. rewrite load_result_vlong in Htmp. exact Htmp. }

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

        { subst le'.
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          exact Hle_s. }

        { exists pc_ptr. split. exact Hpc_load'. simpl. exact Hpc_rel. }

        { exists cv_result. split. exact Haccu_load'.
          simpl. unfold cv_result. rewrite Hhdr_shr.
          rewrite tagged_vectlength_arith. constructor. }

        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
          - exact Hsp_load'.
          - reflexivity.
          - simpl.
            apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) cv_result
                     Hstack_repr Hstore).
            intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          - exact Hsp_ne_sb.
          - exact Hsp_ne_gb.
          - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsp_writable. exact Hofs'.
        - exact Hsp_align. }

        { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }

        { simpl. exact Hextra_load'. }

        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd_load'.
          - simpl. exact Hgd_eq.
          - simpl.
            apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) cv_result
                     Hglobal_repr Hstore).
            intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          - exact Hgb_ne_sb. }

        { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. }

        (* 9. sb_writable -- permission preserved *)
        { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsb_writable. exact Hofs'. }
      }
    }

    (* Case 2b: heap_lookup = None => Error *)
    { reflexivity. }
  }

  (* Case 4: accu = Val_closure => size_or_heap = None => Error *)
  { simpl. reflexivity. }
Qed.

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
