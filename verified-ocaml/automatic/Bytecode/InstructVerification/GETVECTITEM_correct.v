(* GETVECTITEM_correct.v -- GETVECTITEM correctness proof.

   GETVECTITEM: pops index from stack, reads accu as heap ptr,
   dereferences accu[index], stores to accu, advances sp.

   Rocq handler (Interpret.v):
     handle_GETVECTITEM pc' s =
       match s.(stack) with
       | Val_int idx :: rest =>
         match field_or_heap s s.(accu) (Z.to_nat idx) with
         | Some v => Step (s <|pc:=pc'|> <|accu:=v|> <|stack:=rest|>)
         | None => Error "GETVECTITEM: index out of bounds"
         end
       | _ => Error "GETVECTITEM: bad index or stack underflow"
       end

   C handler (instruct_handlers.v, f_instr_GETVECTITEM):
     t2 = s.accu                        -- load accu
     t3 = s.sp                          -- load sp
     t4 = deref(t3 + 0)                 -- load sp[0] = idx (tagged)
     t5 = deref((long ptr)t2 + (t4 shr 1))  -- deref accu at untagged index
     s.accu = t5                        -- store result
     t1 = s.sp                          -- load sp again
     s.sp = t1 + 1                      -- pop stack
     return 0

   Combines: heap field access (like GETFIELD) + stack pop (like ADDINT).
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
From OCamlInterp.Manual Require Import Bytecode.InstructSpec.
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
(* Semantic lemma: cast tlong -> (tptr tlong) for Vptr                 *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* ================================================================== *)
(* Semantic lemma: cast tlong -> tlong for Vlong                       *)
(* ================================================================== *)

Local Lemma sem_cast_tlong_tlong_vlong : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

(* ================================================================== *)
(* Semantic lemma: shr (Vlong n) 1                                     *)
(* ================================================================== *)

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Semantic lemma: (tptr tlong) + (tlong) = ptr + idx * 8              *)
(* sem_add for pointer + long index: (tptr tlong) + tlong              *)
(* classify_add (tptr tlong) tlong = add_case_pl tlong                 *)
(* ================================================================== *)

Local Lemma sem_add_ptr_tlong_idx : forall b ofs idx m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vlong idx) tlong m
  = Some (Vptr b (Ptrofs.add ofs
            (Ptrofs.mul (Ptrofs.repr 8)
                        (Ptrofs.of_int64 idx)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tlong) with (add_case_pl tlong).
  unfold sem_add_ptr_long. reflexivity.
Qed.

(* ================================================================== *)
(* Arithmetic: shr of tagged integer + pointer offset                  *)
(*                                                                      *)
(* The tagged integer for idx is (idx * 2 + 1).                        *)
(* shr by 1: Int64.shr (Int64.repr (idx * 2 + 1)) (Int64.repr 1)      *)
(*         = Int64.repr idx  (for non-negative idx < 2^62)             *)
(* Then: Ptrofs.mul 8 (Ptrofs.of_int64 (Int64.repr idx))              *)
(*     = Ptrofs.repr (idx * 8)                                        *)
(* ================================================================== *)

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

Local Lemma ptrofs_hm_ge_8 : (Ptrofs.half_modulus >= 8)%Z.
Proof. vm_compute. discriminate. Qed.

Local Lemma ptrofs_mul_8_of_int64 : forall idx,
  0 <= idx ->
  idx < Ptrofs.half_modulus ->
  Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr idx))
  = Ptrofs.repr (idx * 8).
Proof.
  intros idx Hge Hlt.
  pose proof ptrofs_hm_ge_8.
  pose proof Ptrofs.half_modulus_modulus.
  unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr.
  2: { change Int64.max_unsigned with Ptrofs.max_unsigned.
       unfold Ptrofs.max_unsigned. lia. }
  unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 8).
  2: { unfold Ptrofs.max_unsigned. lia. }
  rewrite Ptrofs.unsigned_repr.
  2: { unfold Ptrofs.max_unsigned. lia. }
  f_equal. lia.
Qed.

(* ================================================================== *)
(* Heap field precondition for GETVECTITEM                             *)
(*                                                                      *)
(* When field_or_heap succeeds at index (Z.to_nat idx), the C memory   *)
(* contains the corresponding value at accu + idx * 8 bytes.           *)
(* ================================================================== *)

Definition getvectitem_heap_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall idx rest v,
    s.(Machine.stack) = Val_int idx :: rest ->
    field_or_heap s s.(Machine.accu) (Z.to_nat idx) = Some v ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists b ofs cv,
        accu_v = Vptr b ofs /\
        Mem.load Mint64 m b
          (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (idx * 8)))) = Some cv /\
        val_repr hm cb co v cv.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

#[warnings="-not-a-closed-proof"]
Theorem verify_GETVECTITEM_correct :
    handler_correct handle_GETVECTITEM f_instr_GETVECTITEM
      (fun _ m s ard =>
         getvectitem_heap_pre m s ard /\
         (* idx is non-negative, tagged value fits in signed int64,
            and idx fits for pointer arithmetic *)
         match s.(Machine.stack) with
         | Val_int idx :: _ =>
             0 <= idx /\
             idx * 2 + 1 <= Int64.max_signed /\
             idx < Ptrofs.half_modulus /\
             (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Val_int idx) cv ->
              exists z, cv = Vlong z)
         | _ => True
         end)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | _, Val_int idx :: _ =>
                    field_or_heap s s.(Machine.accu) (Z.to_nat idx) = None
                  | _, _ => True end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_GETVECTITEM.

  (* Case split on stack *)
  destruct (Machine.stack s) as [| v_hd stk_tl] eqn:Hstk.
  { (* stack = nil => Error *) reflexivity. }
  destruct v_hd as [idx | | |] eqn:Hvhd.

  2-4: reflexivity.

  (* stack = Val_int idx :: stk_tl *)
  destruct (field_or_heap s s.(Machine.accu) (Z.to_nat idx)) as [v|] eqn:Hfoh.

  2: { (* field_or_heap = None => Error *) reflexivity. }

  (* ================================================================ *)
  (* Step case: stack = Val_int idx :: stk_tl, field_or_heap = Some v *)
  (* ================================================================ *)
  {
    intros ard Hpre [Hhfl Hidx_bounds].

    destruct Hidx_bounds as [Hidx_ge [Hidx_signed [Hidx_ptrofs Hidx_tagged]]].

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

    (* Use heap precondition to get the field value in C memory *)
    unfold getvectitem_heap_pre in Hhfl.
    destruct (Hhfl idx stk_tl v Hstk Hfoh accu_v Haccu_repr)
      as [hb [ho [cv [Haccu_is_ptr [Hfield_load Hfield_repr]]]]].
    subst accu_v.

    (* Composite environment facts *)
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    (* --- Store 1: accu field (so+8) gets cv --- *)
    destruct (store_succeeds_sb m sb so 8 (Vptr hb ho) Hsb_writable Haccu_load ltac:(lia) ltac:(lia) cv)
      as [m1 Hstore_accu].

    (* --- After store 1: sp field in m1 --- *)
    assert (Hsp_load_m1 :
      Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
        Some (Vptr sp_b sp_ofs)).
    { apply (load_after_store_other m m1 sb
               (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 16)
               cv (Vptr sp_b sp_ofs)
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

    (* --- After store 2: load sp from m' for the pop --- *)
    assert (Hsp_load_m' :
      Mem.load Mint64 m' sb (Ptrofs.unsigned so + 16) = Some new_sp_v).
    { pose proof (load_after_store_same m1 m' sb (Ptrofs.unsigned so + 16) new_sp_v Hstore_sp) as Htmp.
      unfold new_sp_v in Htmp |- *. simpl Val.load_result in Htmp.
      rewrite ptr64_true in Htmp. exact Htmp. }

    (* --- Arithmetic: shr of tagged integer --- *)
    assert (Hshr_idx : Int64.shr (Int64.repr (idx * 2 + 1)) (Int64.repr 1) = Int64.repr idx).
    { apply shr_tagged_int; assumption. }

    (* --- Arithmetic: ptrofs mul --- *)
    assert (Hptrofs_mul : Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr idx))
                          = Ptrofs.repr (idx * 8)).
    { apply ptrofs_mul_8_of_int64; assumption. }

    (* Witnesses *)
    set (le' := PTree.set _t'1 (Vptr sp_b sp_ofs)
                  (PTree.set _t'5 cv
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

      (* S4: Sset _t'5 (deref (cast(t2) + (cast(t4) >> 1))) *)
      (* Read _t'2 = accu = Vptr hb ho *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      (* Cast accu (tlong -> tptr tlong) *)
      rewrite (sem_cast_long_to_ptr_vptr hb ho m); eval_cbn.
      (* Read _t'4 = idx tagged *)
      rewrite PTree.gss; eval_cbn.
      (* Cast t4 (tlong -> tlong) *)
      rewrite (sem_cast_tlong_tlong_vlong (Int64.repr (idx * 2 + 1)) m); eval_cbn.
      (* Shift right by 1: untag *)
      rewrite (sem_shr_long_int_1 (Int64.repr (idx * 2 + 1)) m); eval_cbn.
      (* Pointer + shifted index *)
      rewrite Hshr_idx.
      rewrite (sem_add_ptr_tlong_idx hb ho (Int64.repr idx) m); eval_cbn.
      (* Deref: load field at offset idx *)
      rewrite Hptrofs_mul.
      rewrite Hfield_load; eval_cbn.

      (* S5: Sassign (s->accu = _t'5) -- store field value to accu *)
      repeat (rewrite PTree.gso by (compute; congruence)).
      rewrite Hle_s; eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      (* Rvalue: _t'5 *)
      rewrite PTree.gss; eval_cbn.
      (* sem_cast of result *)
      rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hfield_repr); eval_cbn.
      (* Store to accu field *)
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
                   (uso + 8) (uso + 0) cv pc_ptr
                   Hstore_accu Hpc_load). left. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 16) (uso + 0) new_sp_v pc_ptr
                 Hstore_sp Hpc_m1). left. lia. }

      (* accu field at uso+8: written by store1, unaffected by store2 *)
      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some cv).
      { assert (Haccu_m1 : Mem.load Mint64 m1 sb (uso + 8) = Some cv).
        { pose proof (load_after_store_same m m1 sb (uso + 8) cv Hstore_accu) as Htmp.
          rewrite (val_repr_load_result hm cb co v cv Hfield_repr) in Htmp.
          exact Htmp. }
        apply (load_after_store_other m1 m' sb
                 (uso + 16) (uso + 8) new_sp_v cv
                 Hstore_sp Haccu_m1). left. lia. }

      (* sp field at uso+16: written by store2 *)
      (* Hsp_load_m' already proved above *)

      (* env field at uso+24: unaffected by both stores *)
      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
      { assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m1 sb
                   (uso + 8) (uso + 24) cv env_v
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
                   (uso + 8) (uso + 32) cv _
                   Hstore_accu Hextra_load). right. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 16) (uso + 32) new_sp_v _
                 Hstore_sp Hextra_m1). right. lia. }

      (* global_data field at uso+40: unaffected by both stores *)
      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { assert (Hgd_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m1 sb
                   (uso + 8) (uso + 40) cv gd_ptr
                   Hstore_accu Hgd_load). right. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 16) (uso + 40) new_sp_v gd_ptr
                 Hstore_sp Hgd_m1). right. lia. }

      (* trap_sp field at uso+48: unaffected by both stores *)
      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { assert (Hts_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m1 sb
                   (uso + 8) (uso + 48) cv ts_ptr
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

      (* 3. accu field -- updated to field value v *)
      { exists cv. split.
        - exact Haccu_load'.
        - simpl. exact Hfield_repr. }

      (* 4. sp field -- updated to sp + 8 (stack tail) *)
      { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)).
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load_m'.
        - reflexivity.
        - simpl.
          eapply (stack_repr_store_other_block hm cb co m1 m' _ sp_b
                   (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16) new_sp_v).
          + eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b
                     (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) cv).
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
          + eapply (global_repr_store_other_block hm cb co m m1 _ _ _ sb (uso + 8) cv).
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
