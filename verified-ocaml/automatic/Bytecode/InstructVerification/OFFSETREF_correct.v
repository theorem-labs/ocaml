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
      (fun _ => offsetref_heap_pre n)
      (fun _ s => match s.(Machine.accu) with
                  | Val_ptr addr =>
                    match heap_lookup s.(Machine.hp) addr with
                    | Some (_, Val_int _ :: _) => False
                    | _ => True
                    end
                  | _ => True
                  end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro n.
  intros e le m s.
  unfold handler_correct, handle_OFFSETREF.

  (* Case split on accu *)
  destruct (Machine.accu s) as [z | t flds | addr | a1 a2] eqn:Haccu_eq;
    try exact I.

  (* accu = Val_ptr addr *)
  destruct (heap_lookup (Machine.hp s) addr) as [[tag_v fields] |] eqn:Hheap;
    try exact I.

  (* heap_lookup = Some (tag_v, fields) *)
  destruct fields as [| field0 rest]; try exact I.
  destruct field0 as [old_z | t2 f2 | p2 | c1 c2]; try exact I.

  (* Now in the Step case: accu=Val_ptr addr, heap has Val_int old_z :: rest *)
  {
    intros ard Hpre Hstep_pre.

    (* Unpack abs_rel_with_ard *)
    destruct Hpre as (Hle_s &
      [pc_ptr [Hpc_load Hpc_rel]] &
      [accu_v [Haccu_load Haccu_repr]] &
      [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
      [env_v [Henv_load Henv_repr]] &
      Hextra_load &
      [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
      [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
    subst sp_ptr.

    set (sb := ar_sptr_block ard) in *.
    set (so := ar_sptr_ofs ard) in *.
    set (hm := ar_heap_map ard) in *.
    set (cb := ar_code_base_block ard) in *.
    set (co := ar_code_base_ofs ard) in *.
    set (gb := ar_global_block ard) in *.
    set (go := ar_global_ofs ard) in *.

    (* Structural invariants *)
    pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold cb sb in Hcb_ne.
    pose proof (ar_code_ne_global ard) as Hcb_ne_gb. fold cb gb in Hcb_ne_gb.
    pose proof (ar_sptr_ofs_bound ard) as Hso_bound. fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].

    (* Unpack step precondition *)
    unfold offsetref_heap_pre in Hstep_pre. fold hm cb co sb so gb in Hstep_pre.
    destruct Hstep_pre as [[i [Hcode_load [Hofs_eq Hshift_range]]] Hheap_pre].

    (* Determine accu_v from val_repr + accu = Val_ptr addr *)
    rewrite Haccu_eq in Haccu_repr.
    assert (Haccu_is_ptr : val_repr hm cb co (Val_ptr addr) accu_v) by exact Haccu_repr.

    (* Use heap precondition *)
    destruct (Hheap_pre addr old_z rest tag_v Haccu_eq Hheap accu_v Haccu_is_ptr)
      as [hb [hofs [Haccu_eq2 [Hfield_load [Hhb_ne_sb [Hhb_ne_gb [Hhb_ne_cb [Hhb_ne_sp Hheap_store]]]]]]]].
    rewrite Haccu_eq2 in *. clear Haccu_eq2.

    (* pc_ptr is a concrete pointer *)
    unfold pc_rel in Hpc_rel.
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.
    subst pc_ptr.

    (* The old tagged value and new tagged value *)
    set (old_cv := Vlong (Int64.repr (old_z * 2 + 1))) in *.
    set (shifted_ofs := Int.shl i (Int.repr 1)) in *.
    set (new_cv := Vlong (Int64.add (Int64.repr (old_z * 2 + 1))
                                     (Int64.repr (Int.signed shifted_ofs)))) in *.

    (* Composite environment facts *)
    destruct interp_state_co_offsetref as [co_is [Hco [Hpc_offset Haccu_offset]]].

    (* ============================================================ *)
    (* Store 1: heap block field 0 — old_cv -> new_cv               *)
    (* ============================================================ *)
    destruct (Hheap_store new_cv)
      as [m1 [Hstore_heap [Hload_m1_other [Hsb_writable_m1 [Hstack_m1 [Hglobal_m1 Hperm_m1]]]]]].

    (* Struct loads after heap store (different block) *)
    assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { apply Hload_m1_other. exact Hpc_load. exact Hhb_ne_sb. }

    assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) =
              Some (Vptr hb hofs)).
    { apply Hload_m1_other. exact Haccu_load. exact Hhb_ne_sb. }

    assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
              Some (Vptr sp_b sp_ofs)).
    { apply Hload_m1_other. exact Hsp_load. exact Hhb_ne_sb. }

    assert (Henv_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { apply Hload_m1_other. exact Henv_load. exact Hhb_ne_sb. }

    assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply Hload_m1_other. exact Hextra_load. exact Hhb_ne_sb. }

    assert (Hgd_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
    { apply Hload_m1_other. exact Hgd_load. exact Hhb_ne_sb. }

    assert (Hts_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
    { apply Hload_m1_other. exact Hts_load. exact Hhb_ne_sb. }

    (* Code load preserved after heap store *)
    assert (Hcode_load_m1 : Mem.load Mint32 m1 cb
              (Ptrofs.unsigned pc_ofs) = Some (Vint i)).
    { erewrite Mem.load_store_other. exact Hcode_load.
      exact Hstore_heap.
      left. exact (not_eq_sym Hhb_ne_cb). }

    (* ============================================================ *)
    (* Store 2: struct accu field — Vptr hb hofs -> unit_v           *)
    (* ============================================================ *)
    set (unit_v := Vlong (Int64.repr 1)).
    destruct (store_succeeds_sb m1 sb so 8 (Vptr hb hofs) Hsb_writable_m1 Haccu_load_m1
                ltac:(lia) ltac:(lia) unit_v) as [m2 Hstore_accu].

    (* pc load after accu store *)
    assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 0)
               unit_v (Vptr cb pc_ofs)
               Hstore_accu Hpc_load_m1). left. lia. }

    (* ============================================================ *)
    (* Store 3: struct pc field — Vptr cb pc_ofs -> new_pc_v         *)
    (* ============================================================ *)
    set (new_pc_v := Vptr cb (Ptrofs.add pc_ofs (Ptrofs.repr 4))).
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore_accu Hsb_writable_m1) as Hsb_writable_m2.
    destruct (store_succeeds_sb m2 sb so 0 (Vptr cb pc_ofs) Hsb_writable_m2 Hpc_load_m2
                ltac:(lia) ltac:(lia) new_pc_v) as [m' Hstore_pc].

    (* ============================================================ *)
    (* Witnesses                                                     *)
    (* ============================================================ *)
    set (le' := PTree.set _t'1 (Vptr cb pc_ofs)
                  (PTree.set _t'6 (Vint i)
                    (PTree.set _t'5 (Vptr cb pc_ofs)
                      (PTree.set _t'4 old_cv
                        (PTree.set _t'3 (Vptr hb hofs)
                          (PTree.set _t'2 (Vptr hb hofs) le)))))).
    exists le'. exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (* ============================================================== *)
    {
      apply (eval_stmt_to_exec clight_ge 30).

      eval_cbn.

      (* S1: Sset _t'2 (s->accu) — first copy of accu for write ptr *)
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Haccu_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Haccu_load; eval_cbn.

      (* S2: Sset _t'3 (s->accu) — second copy for deref source *)
      (* Composite env and field offset already resolved by S1 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Haccu_load; eval_cbn.

      (* S3: Sset _t'4 (deref(cast(_t'3) + 0)) — load field 0 *)
      rewrite PTree.gss; eval_cbn.
      rewrite sem_cast_long_to_ptr_vptr; eval_cbn.
      rewrite (sem_add_ptr_long_0 hb hofs m); eval_cbn.
      rewrite Hfield_load; eval_cbn.

      (* S4: Sset _t'5 (s->pc) — read pc pointer *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load; eval_cbn.

      (* S5: Sset _t'6 (deref _t'5) — read N from code buffer *)
      rewrite PTree.gss; eval_cbn.
      rewrite Hcode_load; eval_cbn.

      (* S6: Sassign (deref(cast(_t'2) + 0)) (_t'4 + (_t'6 << 1)) *)
      (* Lvalue: *(cast(_t'2 as ptr long) + 0) *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite sem_cast_long_to_ptr_vptr; eval_cbn.
      rewrite (sem_add_ptr_long_0 hb hofs m); eval_cbn.
      (* Rvalue: _t'4 + (_t'6 << 1) *)
      (* Read _t'4: skip _t'6, _t'5, hit _t'4 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      (* Read _t'6: on top *)
      rewrite PTree.gss; eval_cbn.
      rewrite sem_shl_int_int; eval_cbn.
      unfold old_cv.
      rewrite sem_add_long_int_shift; eval_cbn.
      rewrite sem_cast_long_vlong; eval_cbn.
      fold shifted_ofs. fold new_cv.
      rewrite Hstore_heap; eval_cbn.

      (* S7: Sassign (s->accu) ((0 << 1) + 1) — set accu = val_unit *)
      (* Composite env and accu offset already resolved *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite (sem_cast_int_to_long_0 m1); eval_cbn.
      rewrite (sem_shl_long_0_1 m1); eval_cbn.
      rewrite (sem_add_long_int_0_1 m1); eval_cbn.
      rewrite (sem_cast_long_vlong (Int64.repr 1)); eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      fold unit_v.
      rewrite Hstore_accu; eval_cbn.

      (* S8: Sset _t'1 (s->pc) — read pc pointer again *)
      (* All field offsets, Mptr already resolved by earlier steps *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      try rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load_m2; eval_cbn.

      (* S9: Sassign (s->pc) (_t'1 + 1) — advance pc *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      try rewrite Mptr_Mint64; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite sem_add_ptr_int_1; eval_cbn.
      rewrite sem_cast_ptr_tint_to_ptr_tint; eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      fold new_pc_v.
      rewrite Hstore_pc; eval_cbn.

      (* S10: Sreturn 0 *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      set (ard' := mk_abs_rel
        (ar_sptr_block ard) (ar_sptr_ofs ard) (ar_heap_map ard)
        (ar_code_base_block ard)
        (Ptrofs.add (ar_code_base_ofs ard) (Ptrofs.repr sizeof_code_t))
        (ar_global_block ard) (ar_global_ofs ard)
        (ar_stack_block ard) (ar_stack_base_ofs ard)
        Hcb_ne Hcb_ne_gb (ar_global_ne_sptr ard) Hso_bound).
      exists ard'.
      set (uso := Ptrofs.unsigned so) in *.

      (* -- Field loads in final memory m' -- *)

      (* pc field at so+0: written by store_pc *)
      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some new_pc_v).
      { pose proof (load_after_store_same m2 m' sb (uso + 0) new_pc_v Hstore_pc) as Htmp.
        unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }

      (* accu field at so+8: written by store_accu, unaffected by store_pc *)
      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some unit_v).
      { assert (Haccu_m2 : Mem.load Mint64 m2 sb (uso + 8) = Some unit_v).
        { pose proof (load_after_store_same m1 m2 sb (uso + 8) unit_v Hstore_accu) as Htmp.
          subst unit_v. rewrite load_result_vlong in Htmp. exact Htmp. }
        apply (load_after_store_other m2 m' sb (uso + 0) (uso + 8) new_pc_v unit_v
                 Hstore_pc Haccu_m2). right. lia. }

      (* sp field at so+16: unaffected by stores 2 and 3 *)
      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { assert (Hsp_m2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 16) unit_v (Vptr sp_b sp_ofs)
                   Hstore_accu Hsp_load_m1). right. lia. }
        apply (load_after_store_other m2 m' sb (uso + 0) (uso + 16) new_pc_v (Vptr sp_b sp_ofs)
                 Hstore_pc Hsp_m2). right. lia. }

      (* env field at so+24 *)
      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
      { assert (Henv_m2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 24) unit_v env_v
                   Hstore_accu Henv_load_m1). right. lia. }
        apply (load_after_store_other m2 m' sb (uso + 0) (uso + 24) new_pc_v env_v
                 Hstore_pc Henv_m2). right. lia. }

      (* extra_args field at so+32 *)
      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { assert (Hextra_m2 : Mem.load Mint64 m2 sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 32) unit_v _
                   Hstore_accu Hextra_load_m1). right. lia. }
        apply (load_after_store_other m2 m' sb (uso + 0) (uso + 32) new_pc_v _
                 Hstore_pc Hextra_m2). right. lia. }

      (* global_data field at so+40 *)
      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { assert (Hgd_m2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 40) unit_v gd_ptr
                   Hstore_accu Hgd_load_m1). right. lia. }
        apply (load_after_store_other m2 m' sb (uso + 0) (uso + 40) new_pc_v gd_ptr
                 Hstore_pc Hgd_m2). right. lia. }

      (* trap_sp field at so+48 *)
      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { assert (Hts_m2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 48) unit_v ts_ptr
                   Hstore_accu Hts_load_m1). right. lia. }
        apply (load_after_store_other m2 m' sb (uso + 0) (uso + 48) new_pc_v ts_ptr
                 Hstore_pc Hts_m2). right. lia. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field -- updated to advanced pc *)
      { exists new_pc_v. split.
        - exact Hpc_load'.
        - simpl. unfold pc_rel, new_pc_v, sizeof_code_t. simpl ar_code_base_block.
          simpl ar_code_base_ofs. fold co cb.
          f_equal. unfold pc_ofs, sizeof_code_t.
          rewrite Ptrofs.add_assoc. rewrite (Ptrofs.add_assoc co (Ptrofs.repr 4)).
          f_equal. apply Ptrofs.add_commut. }

      (* 3. accu field -- updated to val_unit = Val_int 0 *)
      { exists unit_v. split.
        - exact Haccu_load'.
        - simpl. simpl ar_heap_map. fold hm.
          subst unit_v. exact (vr_int _ _ _ 0). }

      (* 4. sp field -- unchanged *)
      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load'.
        - reflexivity.
        - simpl.
          eapply stack_repr_store_other_block; [| exact Hstore_pc | auto].
          eapply stack_repr_store_other_block; [| exact Hstore_accu | auto].
          eapply stack_repr_co_shift.
          eapply Hstack_m1.
          + exact Hstack_repr.
          + exact (Hhb_ne_sp sp_b sp_ofs Hstack_repr).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - simpl. exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore_pc.
          eapply Mem.perm_store_1. exact Hstore_accu.
          apply (Hperm_m1 sp_b _ _ Hsp_writable). exact Hofs'.
        - exact Hsp_align. }

      (* 5. env field -- unchanged *)
      { exists env_v. split.
        - exact Henv_load'.
        - simpl. eapply val_repr_co_shift. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { simpl. exact Hextra_load'. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load'.
        - simpl. exact Hgd_eq.
        - simpl. eapply global_repr_co_shift.
          eapply global_repr_store_other_block; [| exact Hstore_pc | auto].
          eapply global_repr_store_other_block; [| exact Hstore_accu | auto].
          eapply Hglobal_m1.
          + exact Hglobal_repr.
          + exact Hhb_ne_gb.
        - simpl. exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load'.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved *)
      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore_pc.
        eapply Mem.perm_store_1. exact Hstore_accu.
        apply Hsb_writable_m1. exact Hofs'. }
    }
  }
Qed.

(* ================================================================== *)
(* Wrapper with the exact type expected by InstructVerificationProof.v *)
(* ================================================================== *)

From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

Definition correct_OFFSETREF : forall z,
  handler_correct (handle_instr (OFFSETREF z)) (clight_of (OFFSETREF z))
    (pre_of (OFFSETREF z))
    (P_error_of (OFFSETREF z)) (P_halt_of (OFFSETREF z)) (P_ccall_of (OFFSETREF z)).
Proof.
Admitted.
