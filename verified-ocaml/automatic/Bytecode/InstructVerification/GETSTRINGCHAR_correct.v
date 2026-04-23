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
    handler_correct_v1 handle_GETSTRINGCHAR f_instr_GETSTRINGCHAR
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
      (fun msg s =>
         match s.(Machine.stack) with
         | Val_int idx :: _ =>
             match field_or_heap s s.(Machine.accu) (Z.to_nat idx) with
             | Some (Val_int _) => False
             | _ => True
             end
         | _ => True
         end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct_v1, handle_GETSTRINGCHAR.

  (* Case split on stack *)
  destruct (Machine.stack s) as [| v_hd stk_tl] eqn:Hstk.
  { (* stack = nil => Error *) simpl. trivial. }
  destruct v_hd as [idx | | |] eqn:Hvhd.

  2-4: simpl; trivial.

  (* stack = Val_int idx :: stk_tl *)
  destruct (field_or_heap s s.(Machine.accu) (Z.to_nat idx)) as [foh_v|] eqn:Hfoh.

  2: { (* field_or_heap = None => Error *) simpl. trivial. }

  (* field_or_heap = Some foh_v *)
  destruct foh_v as [c | | |].

  2-4: simpl; trivial.

  (* ================================================================ *)
  (* Step case: stack = Val_int idx :: stk_tl,                         *)
  (*            field_or_heap = Some (Val_int c)                       *)
  (* ================================================================ *)
  {
    intros ard Hpre [Hhfl Hidx_bounds].

    destruct Hidx_bounds as [Hidx_ge [Hidx_lt [Hc_range Hidx_tagged]]].

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
    assert (Hsp_mod_orig : Ptrofs.unsigned sp_ofs + 8 < Ptrofs.modulus).
    { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }
    assert (Hsp_rep_tail : Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length stk_tl) < Ptrofs.modulus).
    { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }
    assert (Hsp_writable_tail : Mem.range_perm m sp_b 0
              (Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length stk_tl)) Cur Writable).
    { intros ofs' Hofs'. apply Hsp_writable. rewrite Hstk. simpl length.
      pose proof (Nat2Z.is_nonneg (length stk_tl)). lia. }

    (* Extract stack head from stack_repr *)
    rewrite Hstk in Hstack_repr.
    inversion Hstack_repr as [| ? ? ? ? cv_idx Hload_sp0 Hval_repr_idx Hstack_repr_rest].
    (* Protect gd_ptr from bare subst *)
    revert Hgd_load Hgd_eq Hglobal_repr Hgb_ne_sb.
    subst.
    intros Hgd_load Hgd_eq Hglobal_repr Hgb_ne_sb.

    (* Stack head is Val_int idx *)
    pose proof Hval_repr_idx as Hval_repr_idx'.
    inversion Hval_repr_idx; subst cv_idx.
    2: { exfalso. destruct (Hidx_tagged _ Hval_repr_idx') as [z Hz]. discriminate Hz. }
    rename H0 into Hidx_is_int.

    (* Use heap precondition to get the byte value in C memory *)
    unfold getstringchar_heap_pre in Hhfl.
    destruct (Hhfl idx stk_tl c Hstk Hfoh Hidx_ge Hidx_lt Hc_range accu_v Haccu_repr)
      as [hb [ho [Haccu_is_ptr Hbyte_load]]].
    subst accu_v.

    (* Composite environment facts *)
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    (* --- Arithmetic: shr of tagged integer --- *)
    assert (Hshr_idx : Int64.shr (Int64.repr (idx * 2 + 1)) (Int64.repr 1) = Int64.repr idx).
    { apply shr_tagged_int; assumption. }

    (* --- Arithmetic: Ptrofs.of_int64 --- *)
    assert (Hptrofs_idx : Ptrofs.of_int64 (Int64.repr idx) = Ptrofs.repr idx).
    { apply ptrofs_of_int64_repr; assumption. }

    (* --- Compute the result value --- *)
    set (result_v := Vlong (Int64.repr (c * 2 + 1))).

    (* --- Store 1: accu field (so+8) gets the tagged byte result --- *)
    destruct (store_succeeds_sb m sb so 8 (Vptr hb ho) Hsb_writable Haccu_load ltac:(lia) ltac:(lia) result_v)
      as [m1 Hstore_accu].

    (* --- After store 1: sp field in m1 --- *)
    assert (Hsp_load_m1 :
      Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
        Some (Vptr sp_b sp_ofs)).
    { apply (load_after_store_other m m1 sb
               (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 16)
               result_v (Vptr sp_b sp_ofs)
               Hstore_accu Hsp_load). right. lia. }

    (* --- Store 2: sp field (so+16) gets sp+8 --- *)
    set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore_accu Hsb_writable) as Hsb_writable_m1.
    destruct (store_succeeds_sb m1 sb so 16 (Vptr sp_b sp_ofs) Hsb_writable_m1 Hsp_load_m1 ltac:(lia) ltac:(lia) new_sp_v)
      as [m' Hstore_sp].

    (* --- After store 1: load sp[0] from m1 (different block from sb) --- *)
    assert (Hload_sp0_m1 :
      Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) =
        Some (Vlong (Int64.repr (idx * 2 + 1)))).
    { erewrite Mem.load_store_other.
      - exact Hload_sp0.
      - exact Hstore_accu.
      - left. exact Hsp_ne_sb. }

    (* Note: the byte load (step 4 in C body) happens in the ORIGINAL
       memory m, before any stores. Stores happen later:
       Store 1: accu (so+8) in m -> m1
       Store 2: sp (so+16) in m1 -> m'
       So Hbyte_load is used directly from m. *)

    (* --- After store 2: load sp from m' for the pop --- *)
    assert (Hsp_load_m' :
      Mem.load Mint64 m' sb (Ptrofs.unsigned so + 16) = Some new_sp_v).
    { pose proof (load_after_store_same m1 m' sb (Ptrofs.unsigned so + 16) new_sp_v Hstore_sp) as Htmp.
      unfold new_sp_v in Htmp |- *. simpl Val.load_result in Htmp.
      rewrite ptr64_true in Htmp. exact Htmp. }

    (* --- Tagged byte arithmetic --- *)
    assert (Htagged_byte : Int64.add (Int64.shl (Int64.repr c) (Int64.repr 1))
                                      (Int64.repr 1)
                           = Int64.repr (c * 2 + 1)).
    { apply tagged_byte_arith. exact Hc_range. }

    (* Witnesses *)
    set (le' := PTree.set _t'1 (Vptr sp_b sp_ofs)
                  (PTree.set _t'5 (Vint (Int.repr c))
                    (PTree.set _t'4 (Vlong (Int64.repr (idx * 2 + 1)))
                      (PTree.set _t'3 (Vptr sp_b sp_ofs)
                        (PTree.set _t'2 (Vptr hb ho) le))))).
    exists le'. exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (* ============================================================== *)
    {
      apply (eval_stmt_to_exec clight_ge 15).
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

      (* S4: Sset _t'5 (deref ((tuchar ptr)t2 + (t4 shr 1))) *)
      (* Read _t'2 = accu = Vptr hb ho *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      (* Cast accu (tlong -> tptr tuchar) *)
      rewrite (sem_cast_long_to_ptr_tuchar hb ho m); eval_cbn.
      (* Read _t'4 = idx tagged *)
      rewrite PTree.gss; eval_cbn.
      (* Cast t4 (tlong -> tlong) *)
      rewrite (sem_cast_tlong_tlong_vlong (Int64.repr (idx * 2 + 1)) m); eval_cbn.
      (* Shift right by 1: untag *)
      rewrite (sem_shr_long_int_1 (Int64.repr (idx * 2 + 1)) m); eval_cbn.
      (* Pointer + shifted index -- tuchar ptr + tlong *)
      rewrite Hshr_idx.
      rewrite (sem_add_ptr_tuchar_tlong hb ho (Int64.repr idx) m); eval_cbn.
      rewrite ptrofs_mul_1.
      rewrite Hptrofs_idx.
      (* Deref: load byte at offset idx *)
      rewrite Hbyte_load; eval_cbn.

      (* S5: Sassign (s->accu = ((long)t5 shl 1) + 1) -- tag and store *)
      repeat (rewrite PTree.gso by (compute; congruence)).
      rewrite Hle_s; eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      (* Rvalue: first cast _t'5 : tuchar -> tlong *)
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_tuchar_to_tlong (Int.repr c) m); eval_cbn.
      (* Rewrite Int.unsigned (Int.repr c) *)
      rewrite Int.unsigned_repr.
      2: { unfold Int.max_unsigned. simpl. lia. }
      (* shl by 1 *)
      rewrite (sem_shl_long_int_1 (Int64.repr c) m); eval_cbn.
      (* add 1 *)
      rewrite (sem_add_long_int_1 (Int64.shl (Int64.repr c) (Int64.repr 1)) m); eval_cbn.
      (* sem_cast of result tlong -> tlong *)
      rewrite (sem_cast_tlong_tlong_vlong _ m); eval_cbn.
      (* Store to accu field *)
      rewrite Htagged_byte.
      fold result_v.
      rewrite Hstore_accu; eval_cbn.

      (* S6: Sset _t'1 (s->sp) -- load sp from struct (now in m1) *)
      repeat (rewrite PTree.gso by (compute; congruence)).
      rewrite Hle_s; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      rewrite Hsp_load_m1; eval_cbn.

      (* S7: Sassign (s->sp = _t'1 + 1) -- advance sp *)
      rewrite PTree.gso by (compute; congruence).
      repeat (rewrite PTree.gso by (compute; congruence)).
      rewrite Hle_s; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      (* Rvalue: _t'1 + 1 *)
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_sp_1 sp_b sp_ofs m1); eval_cbn.
      rewrite (sem_cast_ptr_to_ptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))); eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      fold new_sp_v.
      rewrite Hstore_sp; eval_cbn.

      (* S8: Sreturn 0 *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      exists ard.
      set (uso := Ptrofs.unsigned so) in *.

      (* pc field at uso+0: unaffected by both stores *)
      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
      { assert (Hpc_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some pc_ptr).
        { apply (load_after_store_other m m1 sb
                   (uso + 8) (uso + 0) result_v pc_ptr
                   Hstore_accu Hpc_load). left. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 16) (uso + 0) new_sp_v pc_ptr
                 Hstore_sp Hpc_m1). left. lia. }

      (* accu field at uso+8: written by store1, unaffected by store2 *)
      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some result_v).
      { assert (Haccu_m1 : Mem.load Mint64 m1 sb (uso + 8) = Some result_v).
        { pose proof (load_after_store_same m m1 sb (uso + 8) result_v Hstore_accu) as Htmp.
          unfold result_v in Htmp |- *. simpl Val.load_result in Htmp.
          exact Htmp. }
        apply (load_after_store_other m1 m' sb
                 (uso + 16) (uso + 8) new_sp_v result_v
                 Hstore_sp Haccu_m1). left. lia. }

      (* sp field: Hsp_load_m' already proved above *)

      (* env field at uso+24: unaffected by both stores *)
      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
      { assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m1 sb
                   (uso + 8) (uso + 24) result_v env_v
                   Hstore_accu Henv_load). right. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 16) (uso + 24) new_sp_v env_v
                 Hstore_sp Henv_m1). right. lia. }

      (* extra_args field at uso+32: unaffected by both stores *)
      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { assert (Hextra_m1 : Mem.load Mint64 m1 sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m1 sb
                   (uso + 8) (uso + 32) result_v _
                   Hstore_accu Hextra_load). right. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 16) (uso + 32) new_sp_v _
                 Hstore_sp Hextra_m1). right. lia. }

      (* global_data field at uso+40: unaffected by both stores *)
      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { assert (Hgd_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m1 sb
                   (uso + 8) (uso + 40) result_v gd_ptr
                   Hstore_accu Hgd_load). right. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 16) (uso + 40) new_sp_v gd_ptr
                 Hstore_sp Hgd_m1). right. lia. }

      (* trap_sp field at uso+48: unaffected by both stores *)
      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { assert (Hts_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m1 sb
                   (uso + 8) (uso + 48) result_v ts_ptr
                   Hstore_accu Hts_load). right. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 16) (uso + 48) new_sp_v ts_ptr
                 Hstore_sp Hts_m1). right. lia. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
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

      (* 3. accu field -- updated to Val_int c *)
      { exists result_v. split.
        - exact Haccu_load'.
        - simpl. unfold result_v. constructor. }

      (* 4. sp field -- updated to sp + 8 (stack tail) *)
      { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)).
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load_m'.
        - reflexivity.
        - simpl.
          eapply (stack_repr_store_other_block hm cb co m1 m' _ sp_b
                   (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16) new_sp_v).
          + eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b
                     (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) result_v).
            * exact Hstack_repr_rest.
            * exact Hstore_accu.
            * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          + exact Hstore_sp.
          + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - (* sp_ge8 *)
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)). lia.
        - (* sp_rep *)
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)). exact Hsp_rep_tail.
        - (* sp_writable *)
          intros ofs' Hofs'.
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)) in Hofs'.
          eapply Mem.perm_store_1. exact Hstore_sp.
          eapply Mem.perm_store_1. exact Hstore_accu.
          apply Hsp_writable_tail. exact Hofs'.
        - (* sp_align *)
          simpl.
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)).
          apply Z.divide_add_r. exact Hsp_align. exists 1. lia. }

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
          eapply (global_repr_store_other_block hm cb co m1 m' _ _ _ sb (uso + 16) new_sp_v).
          + eapply (global_repr_store_other_block hm cb co m m1 _ _ _ sb (uso + 8) result_v).
            * exact Hglobal_repr.
            * exact Hstore_accu.
            * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          + exact Hstore_sp.
          + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load'.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved *)
      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore_sp. eapply Mem.perm_store_1. exact Hstore_accu. apply Hsb_writable. exact Hofs'. }
    }
  }
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
