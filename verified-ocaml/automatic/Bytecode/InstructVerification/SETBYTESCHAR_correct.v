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
Theorem verify_SETBYTESCHAR_correct :
    handler_correct handle_SETBYTESCHAR f_instr_SETBYTESCHAR
      (fun _ m s ard =>
         setbyteschar_heap_pre m s ard /\
         match s.(Machine.stack) with
         | Val_int idx :: Val_int newchar :: _ =>
             0 <= idx /\ idx * 2 + 1 <= Int64.max_signed /\
             0 <= newchar <= 255 /\
             (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Val_int idx) cv -> exists z, cv = Vlong z) /\
             (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Val_int newchar) cv -> exists z, cv = Vlong z)
         | _ => True
         end)
      (fun _ s =>
         match s.(Machine.stack) with
         | Val_int idx :: Val_int newchar :: _ =>
             match s.(Machine.accu) with
             | Val_ptr addr =>
               match heap_lookup s.(Machine.hp) addr with
               | Some (_, fields) =>
                   set_nth fields (Z.to_nat idx) (Val_int newchar) = None
               | None => True
               end
             | _ => True
             end
         | _ => True
         end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_SETBYTESCHAR.

  (* Case split on stack *)
  destruct (Machine.stack s) as [| v_hd stk1] eqn:Hstk.
  { (* stack = nil => Error *) simpl. trivial. }
  destruct v_hd as [idx | | |] eqn:Hvhd.
  2-4: simpl; trivial.

  (* stack = Val_int idx :: stk1 *)
  destruct stk1 as [| v_hd2 rest] eqn:Hstk1.
  { (* stack = [Val_int idx] => Error *) simpl. trivial. }
  destruct v_hd2 as [newchar | | |] eqn:Hvhd2.
  2-4: simpl; trivial.

  (* stack = Val_int idx :: Val_int newchar :: rest *)
  destruct (Machine.accu s) as [z_val|blk_tag blk_flds|addr|clo_addr clo_ofs] eqn:Haccu_eq;
    try exact I.

  (* accu = Val_ptr addr *)
  destruct (heap_lookup (Machine.hp s) addr) as [[tag fields]|] eqn:Hlookup.
  2: { (* heap_lookup = None => Error "dangling pointer" *) exact I. }

  destruct (set_nth fields (Z.to_nat idx) (Val_int newchar)) as [new_fields|] eqn:Hset.
  2: { (* set_nth = None => Error "index out of bounds" *) simpl. reflexivity. }

  (* ================================================================ *)
  (* Step case: stack = Val_int idx :: Val_int newchar :: rest,        *)
  (*            accu = Val_ptr addr, heap_lookup ok, set_nth ok        *)
  (* ================================================================ *)
  {
    intros ard Hpre [Hhpre Hidx_bounds].

    destruct Hidx_bounds as [Hidx_ge [Hidx_lt [Hnc_range [Hidx_tagged Hnc_tagged]]]].

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

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound.
    fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne.
    fold sb in Hgb_ne.

    (* Pre-compute stack representation bounds BEFORE inversion *)
    assert (Hsp_mod_orig : Ptrofs.unsigned sp_ofs + 16 < Ptrofs.modulus).
    { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }
    assert (Hsp_rep_tail : Ptrofs.unsigned sp_ofs + 16 + 8 * Z.of_nat (length rest) < Ptrofs.modulus).
    { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }
    assert (Hsp_writable_tail : Mem.range_perm m sp_b 0
              (Ptrofs.unsigned sp_ofs + 16 + 8 * Z.of_nat (length rest)) Cur Writable).
    { intros ofs' Hofs'. apply Hsp_writable. rewrite Hstk. simpl length.
      pose proof (Nat2Z.is_nonneg (length rest)). lia. }

    (* Extract stack head and second element from stack_repr *)
    rewrite Hstk in Hstack_repr.
    inversion Hstack_repr as [| ? ? ? ? cv_idx Hload_sp0 Hval_repr_idx Hstack_repr1].
    (* Protect gd_ptr from bare subst *)
    revert Hgd_load Hgd_eq Hglobal_repr Hgb_ne_sb.
    subst.
    intros Hgd_load Hgd_eq Hglobal_repr Hgb_ne_sb.
    inversion Hstack_repr1 as [| ? ? ? ? cv_nc Hload_sp1 Hval_repr_nc Hstack_repr_rest].
    revert Hgd_load Hgd_eq Hglobal_repr Hgb_ne_sb.
    subst.
    intros Hgd_load Hgd_eq Hglobal_repr Hgb_ne_sb.

    (* Stack heads: Val_int idx -> Vlong, Val_int newchar -> Vlong *)
    pose proof Hval_repr_idx as Hval_repr_idx'.
    inversion Hval_repr_idx; subst cv_idx.
    2: { exfalso. destruct (Hidx_tagged _ Hval_repr_idx') as [z1 Hz1]. discriminate Hz1. }
    rename H0 into Hidx_is_int.
    pose proof Hval_repr_nc as Hval_repr_nc'.
    inversion Hval_repr_nc; subst cv_nc.
    2: { exfalso. destruct (Hnc_tagged _ Hval_repr_nc') as [z2 Hz2]. discriminate Hz2. }
    rename H0 into Hnc_is_int.

    (* Unify Ptrofs.add (Ptrofs.add sp_ofs 8) 8 with Ptrofs.add sp_ofs 16 *)
    rewrite (ptrofs_add_8_8 sp_ofs Hsp_mod_orig) in Hstack_repr_rest.

    (* Use heap precondition *)
    unfold setbyteschar_heap_pre in Hhpre.
    destruct (Hhpre idx newchar rest Hstk Hidx_ge Hidx_lt Hnc_range
                accu_v Haccu_repr sp_b sp_ofs Hsp_load)
      as [hb [hofs [Haccu_is_ptr [Hhb_ne_sb [Hhb_ne_gb [Hhb_ne_sp Hbyte_store_gen]]]]]].
    subst accu_v.

    (* The actual byte value stored by the C code after cast:
       sem_cast (Vlong (shr(newchar*2+1, 1))) tlong tuchar = Vint (zero_ext 8 (...))
       We instantiate the precondition with this value. *)
    set (byte_cv := Vint (Int.zero_ext 8 (Int.repr (Int64.unsigned
      (Int64.shr (Int64.repr (newchar * 2 + 1)) (Int64.repr 1)))))).
    destruct (Hbyte_store_gen byte_cv)
      as [m_byte [Hbyte_store [Hbyte_sb_loads [Hbyte_sp_loads Hbyte_perm]]]].

    (* Composite environment facts *)
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    (* --- Arithmetic: shr of tagged integer --- *)
    assert (Hshr_idx : Int64.shr (Int64.repr (idx * 2 + 1)) (Int64.repr 1) = Int64.repr idx).
    { apply shr_tagged_int; assumption. }

    (* --- Arithmetic: Ptrofs.of_int64 --- *)
    assert (Hptrofs_idx : Ptrofs.of_int64 (Int64.repr idx) = Ptrofs.repr idx).
    { apply ptrofs_of_int64_repr; assumption. }

    (* --- Arithmetic: shr of tagged newchar --- *)
    assert (Hshr_nc : Int64.shr (Int64.repr (newchar * 2 + 1)) (Int64.repr 1) = Int64.repr newchar).
    { apply shr_tagged_int. lia.
      change Int64.max_signed with 9223372036854775807%Z. lia. }

    (* ============================================================ *)
    (* Stores (3 total: byte store, sp update, accu update)         *)
    (* ============================================================ *)

    (* Store 1: byte store to heap -- already given by precondition *)
    (* m_byte is the memory after the byte store *)

    (* --- sb loads after byte store --- *)
    assert (Hpc_load_mb : Mem.load Mint64 m_byte sb (Ptrofs.unsigned so + 0) = Some pc_ptr).
    { apply Hbyte_sb_loads. exact Hpc_load. }
    assert (Haccu_load_mb : Mem.load Mint64 m_byte sb (Ptrofs.unsigned so + 8) = Some (Vptr hb hofs)).
    { apply Hbyte_sb_loads. exact Haccu_load. }
    assert (Hsp_load_mb : Mem.load Mint64 m_byte sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
    { apply Hbyte_sb_loads. exact Hsp_load. }
    assert (Henv_load_mb : Mem.load Mint64 m_byte sb (Ptrofs.unsigned so + 24) = Some env_v).
    { apply Hbyte_sb_loads. exact Henv_load. }
    assert (Hextra_load_mb : Mem.load Mint64 m_byte sb (Ptrofs.unsigned so + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply Hbyte_sb_loads. exact Hextra_load. }
    assert (Hgd_load_mb : Mem.load Mint64 m_byte sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
    { apply Hbyte_sb_loads. exact Hgd_load. }
    assert (Hts_load_mb : Mem.load Mint64 m_byte sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
    { apply Hbyte_sb_loads. exact Hts_load. }

    (* --- sp block loads after byte store --- *)
    assert (Hload_sp0_mb : Mem.load Mint64 m_byte sp_b (Ptrofs.unsigned sp_ofs) =
              Some (Vlong (Int64.repr (idx * 2 + 1)))).
    { apply Hbyte_sp_loads. exact Hload_sp0. }
    assert (Hload_sp1_mb : Mem.load Mint64 m_byte sp_b (Ptrofs.unsigned sp_ofs + 8) =
              Some (Vlong (Int64.repr (newchar * 2 + 1)))).
    { apply Hbyte_sp_loads.
      rewrite <- (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)). exact Hload_sp1. }

    (* --- sb writable after byte store --- *)
    assert (Hsb_writable_mb : Mem.range_perm m_byte sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs' Hofs'. apply Hbyte_perm. apply Hsb_writable. exact Hofs'. }

    (* Store 2: sp field (so+16) <- sp + 16 (pop 2) *)
    set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
    destruct (store_succeeds_sb m_byte sb so 16 (Vptr sp_b sp_ofs) Hsb_writable_mb Hsp_load_mb ltac:(lia) ltac:(lia) new_sp_v)
      as [m1 Hstore_sp].

    (* --- Loads after sp store --- *)
    assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vptr hb hofs)).
    { apply (load_after_store_other m_byte m1 sb
               (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8)
               new_sp_v (Vptr hb hofs) Hstore_sp Haccu_load_mb). left. lia. }

    (* sb writable after sp store *)
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore_sp Hsb_writable_mb) as Hsb_writable_m1.

    (* Store 3: accu field (so+8) <- val_unit = Vlong 1 *)
    set (unit_v := Vlong (Int64.repr 1)).
    destruct (store_succeeds_sb m1 sb so 8 (Vptr hb hofs) Hsb_writable_m1 Haccu_load_m1 ltac:(lia) ltac:(lia) unit_v)
      as [m' Hstore_accu].

    (* ============================================================ *)
    (* Witnesses                                                     *)
    (* ============================================================ *)
    set (le' := PTree.set _t'1 (Vptr sp_b sp_ofs)
                  (PTree.set _t'6 (Vlong (Int64.repr (newchar * 2 + 1)))
                    (PTree.set _t'5 (Vptr sp_b sp_ofs)
                      (PTree.set _t'4 (Vlong (Int64.repr (idx * 2 + 1)))
                        (PTree.set _t'3 (Vptr sp_b sp_ofs)
                          (PTree.set _t'2 (Vptr hb hofs) le)))))).
    exists le'. exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (* ============================================================== *)
    {
      apply (eval_stmt_to_exec clight_ge 20).
      eval_cbn.

      (* S1: Sset _t'2 (s->accu) -- read accu from struct *)
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Haccu_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Haccu_load; eval_cbn.

      (* S2: Sset _t'3 (s->sp) -- read sp from struct *)
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hsp_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      rewrite Hsp_load; eval_cbn.

      (* S3: Sset _t'4 (deref (t3 + 0)) -- load sp[0] = idx *)
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_sp_0 sp_b sp_ofs m); eval_cbn.
      rewrite Hload_sp0; eval_cbn.

      (* S4: Sset _t'5 (s->sp) -- read sp again *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      rewrite Hsp_load; eval_cbn.

      (* S5: Sset _t'6 (deref (t5 + 1)) -- load sp[1] = newchar *)
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_sp_1 sp_b sp_ofs m); eval_cbn.
      rewrite Hload_sp1; eval_cbn.

      (* S6: Sassign *((tuchar ptr)t2 + (t4 >> 1)) = (t6 >> 1) -- byte store *)
      (* Lvalue: (tuchar ptr) cast of _t'2 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_long_to_ptr_tuchar hb hofs m); eval_cbn.
      (* index: _t'4 cast and shr *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_tlong_tlong_vlong (Int64.repr (idx * 2 + 1)) m); eval_cbn.
      rewrite (sem_shr_long_int_1 (Int64.repr (idx * 2 + 1)) m); eval_cbn.
      rewrite Hshr_idx.
      rewrite (sem_add_ptr_tuchar_tlong hb hofs (Int64.repr idx) m); eval_cbn.
      rewrite ptrofs_mul_1.
      rewrite Hptrofs_idx.
      (* Rvalue: _t'6 cast and shr *)
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_tlong_tlong_vlong (Int64.repr (newchar * 2 + 1)) m); eval_cbn.
      rewrite (sem_shr_long_int_1 (Int64.repr (newchar * 2 + 1)) m); eval_cbn.
      (* Cast rvalue from tlong to tuchar for the store *)
      rewrite (sem_cast_tlong_tuchar
        (Int64.shr (Int64.repr (newchar * 2 + 1)) (Int64.repr 1)) m); eval_cbn.
      (* The byte store *)
      fold byte_cv.
      rewrite Hbyte_store; eval_cbn.

      (* S7: Sset _t'1 (s->sp) -- load sp from struct (in m_byte) *)
      repeat (rewrite PTree.gso by (compute; congruence)).
      rewrite Hle_s; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      rewrite Hsp_load_mb; eval_cbn.

      (* S8: Sassign (s->sp = _t'1 + 2) -- pop 2 *)
      rewrite PTree.gso by (compute; congruence).
      repeat (rewrite PTree.gso by (compute; congruence)).
      rewrite Hle_s; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_sp_2 sp_b sp_ofs m_byte); eval_cbn.
      rewrite (sem_cast_ptr_to_ptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))); eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      fold new_sp_v.
      rewrite Hstore_sp; eval_cbn.

      (* S9: Sassign (s->accu = ((long)0 shl 1) + 1) -- val_unit *)
      repeat (rewrite PTree.gso by (compute; congruence)).
      rewrite Hle_s; eval_cbn.
      rewrite (sem_cast_int_to_long_0 m1); eval_cbn.
      rewrite (sem_shl_long_0_1 m1); eval_cbn.
      rewrite (sem_add_long_int_0_1 m1); eval_cbn.
      rewrite (sem_cast_long_vlong (Int64.repr 1)); eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      fold unit_v.
      rewrite Hstore_accu; eval_cbn.

      (* S10: Sreturn 0 *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      exists ard.
      set (uso := Ptrofs.unsigned so) in *.

      (* --- Thread loads through stores --- *)

      (* pc field at uso+0 *)
      assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m_byte m1 sb
                 (uso + 16) (uso + 0) new_sp_v pc_ptr Hstore_sp Hpc_load_mb).
        left. lia. }
      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m1 m' sb
                 (uso + 8) (uso + 0) unit_v pc_ptr Hstore_accu Hpc_load_m1).
        left. lia. }

      (* accu field at uso+8: written by store 3 *)
      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some unit_v).
      { pose proof (load_after_store_same m1 m' sb (uso + 8) unit_v Hstore_accu) as Htmp.
        subst unit_v. simpl Val.load_result in Htmp. exact Htmp. }

      (* sp field at uso+16: written by store 2 *)
      assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some new_sp_v).
      { pose proof (load_after_store_same m_byte m1 sb (uso + 16) new_sp_v Hstore_sp) as Htmp.
        unfold new_sp_v in Htmp |- *. simpl Val.load_result in Htmp.
        rewrite ptr64_true in Htmp. exact Htmp. }
      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some new_sp_v).
      { apply (load_after_store_other m1 m' sb
                 (uso + 8) (uso + 16) unit_v new_sp_v Hstore_accu Hsp_load_m1).
        right. lia. }

      (* env field at uso+24 *)
      assert (Henv_load_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m_byte m1 sb
                 (uso + 16) (uso + 24) new_sp_v env_v Hstore_sp Henv_load_mb).
        right. lia. }
      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m1 m' sb
                 (uso + 8) (uso + 24) unit_v env_v Hstore_accu Henv_load_m1).
        right. lia. }

      (* extra_args field at uso+32 *)
      assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m_byte m1 sb
                 (uso + 16) (uso + 32) new_sp_v _
                 Hstore_sp Hextra_load_mb). right. lia. }
      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m1 m' sb
                 (uso + 8) (uso + 32) unit_v _
                 Hstore_accu Hextra_load_m1). right. lia. }

      (* global_data field at uso+40 *)
      assert (Hgd_load_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m_byte m1 sb
                 (uso + 16) (uso + 40) new_sp_v gd_ptr
                 Hstore_sp Hgd_load_mb). right. lia. }
      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m1 m' sb
                 (uso + 8) (uso + 40) unit_v gd_ptr
                 Hstore_accu Hgd_load_m1). right. lia. }

      (* trap_sp field at uso+48 *)
      assert (Hts_load_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m_byte m1 sb
                 (uso + 16) (uso + 48) new_sp_v ts_ptr
                 Hstore_sp Hts_load_mb). right. lia. }
      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m1 m' sb
                 (uso + 8) (uso + 48) unit_v ts_ptr
                 Hstore_accu Hts_load_m1). right. lia. }

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

      (* 2. pc field -- unchanged *)
      { exists pc_ptr. split.
        - exact Hpc_load'.
        - simpl. exact Hpc_rel. }

      (* 3. accu field -- updated to val_unit = Val_int 0 *)
      { exists unit_v. split.
        - exact Haccu_load'.
        - simpl. subst unit_v. exact (vr_int _ _ _ 0). }

      (* 4. sp field -- updated to sp + 16 (pop 2) *)
      { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 16)).
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load'.
        - reflexivity.
        - simpl.
          (* stack_repr through 3 stores:
             m -> m_byte (byte store, hb <> sp_b),
             m_byte -> m1 (sb store, sb <> sp_b),
             m1 -> m' (sb store, sb <> sp_b) *)
          eapply (stack_repr_store_other_block hm cb co m1 m' _ sp_b
                   (Ptrofs.add sp_ofs (Ptrofs.repr 16)) sb (uso + 8) unit_v).
          + eapply (stack_repr_store_other_block hm cb co m_byte m1 _ sp_b
                     (Ptrofs.add sp_ofs (Ptrofs.repr 16)) sb (uso + 16) new_sp_v).
            * eapply (stack_repr_byte_store_other_block hm cb co m m_byte _ sp_b
                       (Ptrofs.add sp_ofs (Ptrofs.repr 16)) hb
                       (Ptrofs.unsigned (Ptrofs.add hofs (Ptrofs.repr idx)))
                       byte_cv).
              -- exact Hstack_repr_rest.
              -- exact Hbyte_store.
              -- intro Heq. exact (Hhb_ne_sp Heq).
            * exact Hstore_sp.
            * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          + exact Hstore_accu.
          + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - (* sp_ge8 *)
          rewrite (ptrofs_add_unsigned sp_ofs 16 ltac:(lia) ltac:(lia)). lia.
        - (* sp_rep *)
          rewrite (ptrofs_add_unsigned sp_ofs 16 ltac:(lia) ltac:(lia)). exact Hsp_rep_tail.
        - (* sp_writable *)
          intros ofs' Hofs'.
          rewrite (ptrofs_add_unsigned sp_ofs 16 ltac:(lia) ltac:(lia)) in Hofs'.
          eapply Mem.perm_store_1. exact Hstore_accu.
          eapply Mem.perm_store_1. exact Hstore_sp.
          apply Hbyte_perm.
          apply Hsp_writable_tail. exact Hofs'.
        - (* sp_align *)
          simpl.
          rewrite (ptrofs_add_unsigned sp_ofs 16 ltac:(lia) ltac:(lia)).
          apply Z.divide_add_r. exact Hsp_align. exists 2. lia. }

      (* 5. env field -- unchanged *)
      { exists env_v. split.
        - exact Henv_load'.
        - simpl. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { simpl. exact Hextra_load'. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load'.
        - simpl. exact Hgd_eq.
        - simpl.
          eapply (global_repr_store_other_block hm cb co m1 m' _ _ _ sb (uso + 8) unit_v).
          + eapply (global_repr_store_other_block hm cb co m_byte m1 _ _ _ sb (uso + 16) new_sp_v).
            * eapply (global_repr_byte_store_other_block hm cb co m m_byte _ _ _
                       hb (Ptrofs.unsigned (Ptrofs.add hofs (Ptrofs.repr idx)))
                       byte_cv).
              -- exact Hglobal_repr.
              -- exact Hbyte_store.
              -- intro Heq. exact (Hhb_ne_gb Heq).
            * exact Hstore_sp.
            * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          + exact Hstore_accu.
          + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load'.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved through 3 stores *)
      { intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore_accu.
        eapply Mem.perm_store_1. exact Hstore_sp.
        apply Hbyte_perm.
        apply Hsb_writable. exact Hofs'. }
    }
  }
Qed.

Import Bytecode.AST.

(* Wrapper with the canonical type expected by InstructVerificationProof.v *)
Definition correct_SETBYTESCHAR :
    handler_correct (handle_instr SETBYTESCHAR) (clight_of SETBYTESCHAR)
      (pre_of SETBYTESCHAR)
      (P_error_of SETBYTESCHAR) (P_halt_of SETBYTESCHAR) (P_ccall_of SETBYTESCHAR).
Proof.
  intros e le m s.
  change (handle_instr SETBYTESCHAR (Machine.pc s) s)
    with (handle_SETBYTESCHAR (Machine.pc s) s).
  unfold handle_SETBYTESCHAR at 1.
  (* Case split on stack *)
  destruct (Machine.stack s) as [| v_hd stk1] eqn:Hstk.
  { (* stack = [] => Error "stack underflow" *)
    unfold P_error_of, error_message_of. rewrite Hstk. reflexivity. }
  destruct v_hd as [idx | | |].
  2-4: (unfold P_error_of, error_message_of; rewrite Hstk; reflexivity).
  (* stack = Val_int idx :: stk1 *)
  destruct stk1 as [| v_hd2 rest].
  { unfold P_error_of, error_message_of. rewrite Hstk. reflexivity. }
  destruct v_hd2 as [newchar | | |].
  2-4: (unfold P_error_of, error_message_of; rewrite Hstk; reflexivity).
  (* stack = Val_int idx :: Val_int newchar :: rest *)
  destruct (Machine.accu s) as [z_val|blk_tag blk_flds|addr|clo_addr clo_ofs] eqn:Haccu_eq.
  - (* Val_int => Error "not a heap bytes" *)
    unfold P_error_of, error_message_of. rewrite Hstk, Haccu_eq. reflexivity.
  - (* Val_block => Error "not a heap bytes" *)
    unfold P_error_of, error_message_of. rewrite Hstk, Haccu_eq. reflexivity.
  - (* Val_ptr addr => further case split *)
    destruct (heap_lookup (Machine.hp s) addr) as [[tag fields]|] eqn:Hlookup.
    2: { (* heap_lookup = None => Error "dangling pointer" *)
      unfold P_error_of, error_message_of. rewrite Hstk, Haccu_eq, Hlookup. reflexivity. }
    destruct (set_nth fields (Z.to_nat idx) (Val_int newchar)) as [new_fields|] eqn:Hset.
    2: { (* set_nth = None => Error "index out of bounds" *)
      unfold P_error_of, error_message_of. rewrite Hstk, Haccu_eq, Hlookup, Hset. reflexivity. }
    (* Step case: delegate to verify_SETBYTESCHAR_correct *)
    intros ard Harel Hpre.
    unfold pre_of, setbyteschar_step_pre in Hpre.
    rewrite Hstk in Hpre.
    change InstructSpec.setbyteschar_heap_pre with setbyteschar_heap_pre in Hpre.
    pose proof (verify_SETBYTESCHAR_correct e le m s) as H.
    unfold handler_correct, handle_SETBYTESCHAR in H.
    rewrite Hstk, Haccu_eq, Hlookup, Hset in H.
    cbv beta in H.
    exact (H ard Harel Hpre).
  - (* Val_closure => Error "not a heap bytes" *)
    unfold P_error_of, error_message_of. rewrite Hstk, Haccu_eq. reflexivity.
Qed.
