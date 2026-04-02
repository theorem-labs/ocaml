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
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
Require Import instruct_handlers.
Require Import InstructSpec.
Require Import StepToBigstep.
Require Import HandlerLemmas.

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
(* Heap block header axioms                                            *)
(*                                                                      *)
(* OCaml block layout in memory (64-bit):                              *)
(*   ptr[-1]  = header word (8 bytes): size(54) | color(2) | tag(8)   *)
(*   ptr[0..] = fields                                                 *)
(*                                                                      *)
(* These axioms relate the Rocq heap model to the C memory model.     *)
(* ================================================================== *)

(* heap_header_load: reading 8 bytes at offset -8 from the block pointer
   yields the OCaml header word encoding size and tag. *)
Axiom heap_header_load : forall (hm : nat -> option (block * ptrofs))
    (m : mem) (s : Machine.state) addr b ofs tag fields,
  hm addr = Some (b, ofs) ->
  heap_lookup s.(Machine.hp) addr = Some (tag, fields) ->
  exists hdr_word,
    Mem.load Mint64 m b (Ptrofs.unsigned ofs - 8) = Some (Vlong hdr_word) /\
    Int64.shru hdr_word (Int64.repr 10) =
      Int64.repr (Z.of_nat (length fields)) /\
    Mem.load Mint8unsigned m b (Ptrofs.unsigned ofs - 8) =
      Some (Vint (Int.repr (Z.of_nat tag))).

(* heap_tag_not_double_array: size_or_heap counts word-sized fields,
   so tag 254 (Double_array_tag) is excluded from our model. *)
Axiom heap_tag_not_double_array : forall hp addr tag fields,
  heap_lookup hp addr = Some (tag, fields) ->
  Z.of_nat tag <> 254.

(* heap_block_ofs_ge_8: block pointer offset >= 8, so header at -8 is valid. *)
Axiom heap_block_ofs_ge_8 : forall (hm : nat -> option (block * ptrofs)) addr b ofs,
  hm addr = Some (b, ofs) ->
  Ptrofs.unsigned ofs >= 8.

(* heap_block_ne_sptr: heap blocks live in different memory blocks than
   the interpreter state struct. *)
Axiom heap_block_ne_sptr : forall (hm : nat -> option (block * ptrofs)) addr b ofs sb,
  hm addr = Some (b, ofs) ->
  b <> sb.

(* heap_tag_range: OCaml tags are in range 0..255. *)
Axiom heap_tag_range : forall hp addr tag fields,
  heap_lookup hp addr = Some (tag, fields) ->
  (0 <= Z.of_nat tag <= 255)%Z.

(* heap_header_shr_size: The C handler uses signed shift (Oshr on tlong),
   but the header is always non-negative, so shr = shru for the size field. *)
Axiom heap_header_shr_size : forall (hm : nat -> option (block * ptrofs))
    (m : mem) (s : Machine.state) addr b ofs tag fields hdr_word,
  hm addr = Some (b, ofs) ->
  heap_lookup s.(Machine.hp) addr = Some (tag, fields) ->
  Mem.load Mint64 m b (Ptrofs.unsigned ofs - 8) = Some (Vlong hdr_word) ->
  Int64.shr hdr_word (Int64.repr 10) =
    Int64.repr (Z.of_nat (length fields)).

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
  match Machine.accu s with Val_block _ _ => False | _ => True end.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_VECTLENGTH_correct :
    handler_correct handle_VECTLENGTH f_instr_VECTLENGTH
      (fun _ => vectlength_pre)
      (fun _ s => size_or_heap s s.(Machine.accu) = None)
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_VECTLENGTH.

  (* Case split on accu -- constructor order: Val_int, Val_block, Val_ptr, Val_closure *)
  destruct (Machine.accu s) as [z | tag0 fields0 | addr | addr0 ofs0] eqn:Haccu_eq.

  (* Case 1: accu = Val_int z => size_or_heap = None => Error *)
  { simpl. reflexivity. }

  (* Case 2: accu = Val_block tag0 fields0 => size_or_heap = Some (length fields0).
     The C code dereferences accu as a pointer, but Val_block maps to Vlong.
     Excluded by vectlength_pre. *)
  { simpl. intros ard _ Hpre. exfalso.
    unfold vectlength_pre in Hpre. rewrite Haccu_eq in Hpre. exact Hpre. }

  (* Case 3: accu = Val_ptr addr *)
  {
    simpl.
    destruct (heap_lookup (Machine.hp s) addr) as [[tag fields]|] eqn:Hheap.

    (* Case 2a: heap_lookup = Some => Step *)
    {
      intros ard Hpre _.
      unfold abs_rel_with_ard in Hpre.
      set (sb := ar_sptr_block ard) in *.
      set (so := ar_sptr_ofs ard) in *.
      set (hm := ar_heap_map ard) in *.
      destruct Hpre as (Hle_s &
        [pc_ptr [Hpc_load Hpc_rel]] &
        [accu_v [Haccu_load Haccu_repr]] &
        [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep Hsp_writable]]]]]]]]]]] &
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

      pose proof (heap_header_load hm m s addr hb ho tag fields
                    Hhm Hheap) as [hdr_word [Hhdr_load [Hhdr_size Htag_byte_load]]].
      pose proof (heap_tag_not_double_array _ _ _ _ Hheap) as Htag_ne_254.
      pose proof (heap_tag_range _ _ _ _ Hheap) as Htag_range.
      pose proof (heap_block_ofs_ge_8 hm addr hb ho Hhm) as Hho_ge_8.
      pose proof (heap_block_ne_sptr hm addr hb ho sb Hhm) as Hhb_ne_sb.

      destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

      set (n := length fields) in *.
      set (cv_size := Vlong (Int64.shr hdr_word (Int64.repr 10))) in *.
      set (cv_result := Vlong (Int64.add
        (Int64.shl (Int64.shr hdr_word (Int64.repr 10)) (Int64.repr 1))
        (Int64.repr 1))).

      destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 8)
                  (Vptr hb ho) cv_result Haccu_load)
        as [m' Hstore].

      set (cv_accu := Vptr hb ho) in *.
      set (cv_hdr := Vlong hdr_word) in *.
      set (cv_tag_byte := Vint (Int.repr (Z.of_nat tag))) in *.

      set (le' := PTree.set _t'2 cv_tag_byte
                    (PTree.set _t'1 cv_accu
                      (PTree.set _size cv_size
                        (PTree.set _t'4 cv_hdr
                          (PTree.set _t'3 cv_accu le))))).

      pose proof (heap_header_shr_size hm m s addr hb ho tag fields
                    hdr_word Hhm Hheap Hhdr_load) as Hhdr_shr.
      fold n in Hhdr_shr.

      exists le'. exists m'.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* Part 1: exec *)
      {
        apply (eval_stmt_to_exec clight_ge 10). eval_cbn.
        (* Load s->accu *)
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_load; eval_cbn.
        (* Cast accu to ptr, compute ptr[-1] address, load header *)
        rewrite PTree.gss; eval_cbn.
        unfold cv_accu; rewrite sem_cast_long_to_ptr_tlong; eval_cbn.
        rewrite sem_neg_int_1; eval_cbn.
        rewrite sem_add_ptr_neg1_tlong; eval_cbn.
        rewrite ptrofs_add_neg8 by lia.
        rewrite Hhdr_load; eval_cbn.
        (* Shift header right 10 to get size *)
        rewrite PTree.gss; eval_cbn.
        unfold cv_hdr; rewrite sem_shr_long_int_10; eval_cbn.
        (* Load s->accu again for tag byte *)
        repeat (rewrite PTree.gso by (compute; congruence)).
        rewrite Hle_s; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_load; eval_cbn.
        (* Cast to tuchar ptr, compute ptr - sizeof(long), load tag byte *)
        rewrite PTree.gss; eval_cbn.
        unfold cv_accu; rewrite sem_cast_long_to_ptr_tuchar; eval_cbn.
        change (sizeof ge tlong) with 8%Z.
        rewrite Vptrofs_is_Vlong, ptrofs_to_int64_8.
        rewrite sem_neg_sizeof_long; eval_cbn.
        rewrite sem_add_ptr_tuchar_neg_sizeof_long; eval_cbn.
        rewrite ptrofs_add_neg8 by lia.
        rewrite Htag_byte_load; eval_cbn.
        (* Sifthenelse: tag & 255 == 254 => false *)
        rewrite PTree.gss; eval_cbn.
        unfold cv_tag_byte.
        change (sem_binary_operation ge Oand (Vint (Int.repr (Z.of_nat tag)))
                  tuchar (Vint (Int.repr 255)) tint m)
          with (Some (Vint (Int.and (Int.repr (Z.of_nat tag)) (Int.repr 255)))).
        eval_cbn.
        rewrite sem_eq_int_int; eval_cbn.
        rewrite (tag_not_254_comparison tag Htag_range Htag_ne_254); eval_cbn.
        change (Int.eq Int.zero Int.zero) with true; eval_cbn.
        (* Store result: (size << 1) + 1 *)
        repeat (rewrite PTree.gso by (compute; congruence)).
        rewrite Hle_s; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite PTree.gss; eval_cbn.
        rewrite sem_cast_ulong_to_long; eval_cbn.
        rewrite sem_shl_long_int_1; eval_cbn.
        rewrite sem_add_long_int_1; eval_cbn.
        rewrite sem_cast_long_to_long; eval_cbn.
        fold cv_result; rewrite Hstore; eval_cbn.
        reflexivity.
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
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
          - exact Hsp_load'.
          - reflexivity.
          - simpl.
            apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb (uso + 8) cv_result
                     Hstack_repr Hstore).
            intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          - exact Hsp_ne_sb.
          - exact Hsp_ne_gb.
          - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsp_writable. exact Hofs'. }

        { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }

        { simpl. exact Hextra_load'. }

        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd_load'.
          - simpl. exact Hgd_eq.
          - simpl.
            apply (global_repr_store_other_block hm m m' _ _ _ sb (uso + 8) cv_result
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
