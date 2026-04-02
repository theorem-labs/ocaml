(* GETFIELD_correct.v -- GETFIELD (parameterized) correctness proof.

   GETFIELD: reads field index n from the code buffer, dereferences
   accu as a pointer to get field n, stores result to accu, advances pc.

   Rocq handler (Interpret.v):
     handle_GETFIELD n pc' s =
       match field_or_heap s s.(accu) n with
       | Some v => Step (s <|pc:=pc'|> <|accu:=v|>)
       | None => Error "GETFIELD: access failed"
       end

   C handler (instruct_handlers.v, f_instr_GETFIELD):
     _t'2 = s->accu;                      // load accu from struct
     _t'3 = s->pc;                         // load pc pointer
     _t'4 = *_t'3;                         // read field index from code buffer
     _t'5 = deref((long ptr)_t'2 + _t'4);  // deref accu at field offset
     s->accu = _t'5;                       // store result
     _t'1 = s->pc;                         // load pc again
     s->pc = _t'1 + 1;                     // advance pc past argument
     return 0;

   Combines GETFIELD0 pattern (field dereference with heap precondition)
   with CONSTINT pattern (code buffer read + pc advancement).

   Two stores: accu field at offset +8, pc field at offset +0.

   No Axioms, no Admitted, no vm_compute on Ptrofs. *)

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

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout: _pc at offset 0, _accu at offset 8                   *)
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

Lemma interp_state_co_pc_accu_GF : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Lemma sem_cast_long_to_ptr_vptr_GF : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint_GF : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_add_pc_1_GF : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* sem_add for (tptr tlong) + Vint n — general pointer arithmetic *)
Lemma sem_add_ptr_long_n : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint n) tint m
    = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* pc_rel with shifted code base *)
Lemma pc_rel_shift_GF : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr 4)))
         cb (Ptrofs.add co (Ptrofs.repr sizeof_code_t)) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal.
  rewrite Ptrofs.add_assoc.
  rewrite Ptrofs.add_assoc.
  f_equal.
  rewrite Ptrofs.add_commut. reflexivity.
Qed.

(* ================================================================== *)
(* Heap field precondition (parameterized over n)                      *)
(* ================================================================== *)

(* The precondition for the Step case: when field_or_heap succeeds at
   index n, the C memory must contain the corresponding value at the
   pointer location offset by n * 8 bytes, and the accu must be
   representable as a Vptr.  The offset in the Mem.load uses the
   same ptrofs arithmetic as the C pointer dereference. *)
Definition heap_field_loadable_n (n : nat)
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  forall v,
    field_or_heap s s.(Machine.accu) n = Some v ->
    forall accu_v,
      val_repr hm s.(Machine.accu) accu_v ->
      exists b ofs cv,
        accu_v = Vptr b ofs /\
        Mem.load Mint64 m b
          (Ptrofs.unsigned (Ptrofs.add ofs
             (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat n)))))) = Some cv /\
        val_repr hm v cv.

(* ================================================================== *)
(* Main theorem: GETFIELD with heap + code buffer preconditions        *)
(* ================================================================== *)

Theorem verify_GETFIELD_correct : forall n,
    handler_correct (handle_GETFIELD n) f_instr_GETFIELD
      (fun _ m s ard =>
         heap_field_loadable_n n m s ard /\
         (* The code buffer contains Int.repr n at the current PC position *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* n fits in the int32 signed range *)
         Int.min_signed <= Z.of_nat n <= Int.max_signed)
      (fun _ s => field_or_heap s s.(Machine.accu) n = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro n.
  intros e le m s.
  unfold handler_correct, handle_GETFIELD.
  destruct (field_or_heap s s.(Machine.accu) n) as [v|] eqn:Hfoh.

  (* ================================================================ *)
  (* Case 1: field_or_heap = Some v => Step                            *)
  (* ================================================================ *)
  2: { (* Case 2: field_or_heap = None => Error *)
    reflexivity.
  }
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

    destruct Hstep_pre as (Hhfl & Hcode_load & Hn_range).

    set (sb := ar_sptr_block ard) in *.
    set (so := ar_sptr_ofs ard) in *.
    set (hm := ar_heap_map ard) in *.
    set (cb := ar_code_base_block ard) in *.
    set (co := ar_code_base_ofs ard) in *.

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound.
    fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

    (* Use heap precondition to get the field value in C memory *)
    unfold heap_field_loadable_n in Hhfl.
    destruct (Hhfl v Hfoh accu_v Haccu_repr)
      as [b [ofs [cv [Haccu_is_ptr [Hfield_load Hfield_repr]]]]].
    subst accu_v.

    (* Composite environment facts *)
    destruct interp_state_co_pc_accu_GF as [co_is [Hco [Hpc_offset Haccu_offset]]].

    (* pc_ptr is a concrete Vptr *)
    unfold pc_rel in Hpc_rel. subst pc_ptr.
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

    (* Store 1: accu field at (sb, uso+8) <- cv *)
    destruct (store_succeeds_sb m sb so 8 (Vptr b ofs) Hsb_writable Haccu_load ltac:(lia) ltac:(lia) cv) as [m1 Hstore1].
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

    (* New pc after advancement *)
    set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
    set (new_pc_v := Vptr cb new_pc_ofs).

    (* pc field in m1: unaffected by store1 at offset +8 *)
    assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 8)
               (Ptrofs.unsigned so + 0) cv (Vptr cb pc_ofs)
               Hstore1 Hpc_load).
      left. lia. }

    (* Store 2: pc field at (sb, uso+0) <- new_pc_v *)
    destruct (store_succeeds_sb m1 sb so 0 (Vptr cb pc_ofs) Hsb_writable_m1 Hpc_load_m1 ltac:(lia) ltac:(lia) new_pc_v)
      as [m2 Hstore2].

    (* Code load survives store1 (different block) *)
    assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
              Some (Vint (Int.repr (Z.of_nat n)))).
    { erewrite Mem.load_store_other.
      - exact Hcode_load.
      - exact Hstore1.
      - left. exact Hcb_ne. }

    (* Witnesses *)
    set (le' := PTree.set _t'1 (Vptr cb pc_ofs)
                (PTree.set _t'5 cv
                (PTree.set _t'4 (Vint (Int.repr (Z.of_nat n)))
                (PTree.set _t'3 (Vptr cb pc_ofs)
                (PTree.set _t'2 (Vptr b ofs) le))))).
    exists le'. exists m2.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (*                                                                  *)
    (* The C body executes:                                             *)
    (*   _t'2 = s->accu          (load accu from struct)               *)
    (*   _t'3 = s->pc            (load pc from struct)                 *)
    (*   _t'4 = *_t'3            (read n from code buffer)             *)
    (*   _t'5 = deref(cast(_t'2) + _t'4) (deref field n)              *)
    (*   s->accu = _t'5          (store result)                        *)
    (*   _t'1 = s->pc            (load pc again from m1)               *)
    (*   s->pc = _t'1 + 1        (advance pc)                         *)
    (*   return 0                                                      *)
    (* ============================================================== *)
    {
      apply (eval_stmt_to_exec clight_ge 20).
      eval_cbn.

      (* === S1: Sset _t'2 (s->accu) — load accu from struct === *)
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Haccu_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Haccu_load; eval_cbn.

      (* === S2: Sset _t'3 (s->pc) — load pc pointer from struct === *)
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load; eval_cbn.

      (* === S3: Sset _t'4 (deref _t'3) -- read field index from code buffer === *)
      rewrite PTree.gss; eval_cbn.
      rewrite Hcode_load; eval_cbn.

      (* === S4: Sset _t'5 — deref (cast(_t'2) + _t'4) === *)
      (* Evaluate _t'2 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      (* Cast: tlong -> (tptr tlong) for Vptr *)
      rewrite sem_cast_long_to_ptr_vptr_GF; eval_cbn.
      (* Evaluate _t'4 -- most recent in le, so gss directly *)
      rewrite PTree.gss; eval_cbn.
      (* Add: ptr + n = ptr + n*8 bytes *)
      rewrite (sem_add_ptr_long_n b ofs (Int.repr (Z.of_nat n)) m); eval_cbn.
      (* Deref: load field n from heap block *)
      rewrite Hfield_load; eval_cbn.

      (* === S5: Sassign (s->accu = _t'5) — store field value === *)
      (* Lvalue: s->accu *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.

      (* Rvalue: _t'5 *)
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_long_val_repr _ _ _ _ Hfield_repr); eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Hstore1; eval_cbn.

      (* === S6: Sset _t'1 (s->pc) — load pc pointer again from m1 === *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load_m1; eval_cbn.

      (* === S7: Sassign (s->pc = _t'1 + 1) — advance pc === *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.

      (* Rvalue: _t'1 + 1 *)
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_pc_1_GF cb pc_ofs m1); eval_cbn.
      rewrite (sem_cast_ptr_tint_to_ptr_tint_GF cb new_pc_ofs); eval_cbn.

      (* Store to pc field *)
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      fold new_pc_v.
      rewrite Hstore2; eval_cbn.

      (* === S8: Sreturn 0 === *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
      set (ard' := mk_abs_rel
        (ar_sptr_block ard) (ar_sptr_ofs ard) (ar_heap_map ard)
        (ar_code_base_block ard) new_co
        (ar_global_block ard) (ar_global_ofs ard)
        (ar_stack_block ard) (ar_stack_base_ofs ard)
        (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
      exists ard'.
      set (uso := Ptrofs.unsigned so) in *.

      (* pc field at uso+0: written by store2 *)
      assert (Hpc_load2 : Mem.load Mint64 m2 sb (uso + 0) = Some new_pc_v).
      { pose proof (load_after_store_same m1 m2 sb (uso + 0) new_pc_v Hstore2) as Htmp.
        unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }

      (* accu field at uso+8: written by store1, unaffected by store2 *)
      assert (Haccu_load2 : Mem.load Mint64 m2 sb (uso + 8) = Some cv).
      { assert (Haccu_m1 : Mem.load Mint64 m1 sb (uso + 8) = Some cv).
        { pose proof (load_after_store_same m m1 sb (uso + 8) cv Hstore1) as Htmp.
          rewrite (val_repr_load_result hm v cv Hfield_repr) in Htmp.
          exact Htmp. }
        apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 8)
                 new_pc_v cv Hstore2 Haccu_m1). right. lia. }

      (* sp field at uso+16: unaffected by both stores *)
      assert (Hsp_load2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m1 sb (uso + 8) (uso + 16)
                   cv (Vptr sp_b sp_ofs) Hstore1 Hsp_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 16)
                 new_pc_v (Vptr sp_b sp_ofs) Hstore2 Hsp_m1). right. lia. }

      (* env field at uso+24: unaffected *)
      assert (Henv_load2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
      { assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m1 sb (uso + 8) (uso + 24)
                   cv env_v Hstore1 Henv_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 24)
                 new_pc_v env_v Hstore2 Henv_m1). right. lia. }

      (* extra_args field at uso+32: unaffected *)
      assert (Hextra_load2 : Mem.load Mint64 m2 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { assert (Hextra_m1 : Mem.load Mint64 m1 sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m1 sb (uso + 8) (uso + 32)
                   cv _ Hstore1 Hextra_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 32)
                 new_pc_v _ Hstore2 Hextra_m1). right. lia. }

      (* global_data field at uso+40: unaffected *)
      assert (Hgd_load2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
      { assert (Hgd_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m1 sb (uso + 8) (uso + 40)
                   cv gd_ptr Hstore1 Hgd_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 40)
                 new_pc_v gd_ptr Hstore2 Hgd_m1). right. lia. }

      (* trap_sp field at uso+48: unaffected *)
      assert (Hts_load2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
      { assert (Hts_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m1 sb (uso + 8) (uso + 48)
                   cv ts_ptr Hstore1 Hts_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 48)
                 new_pc_v ts_ptr Hstore2 Hts_m1). right. lia. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field -- updated to new_pc_v *)
      { exists new_pc_v. split.
        - exact Hpc_load2.
        - simpl. subst new_pc_v new_pc_ofs.
          apply pc_rel_shift_GF. }

      (* 3. accu field -- updated to field value *)
      { exists cv. split.
        - exact Haccu_load2.
        - simpl. exact Hfield_repr. }

      (* 4. sp field -- unchanged *)
      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load2.
        - reflexivity.
        - simpl.
          eapply (stack_repr_store_other_block hm m1 m2 _ sp_b sp_ofs sb (uso + 0) new_pc_v).
          + eapply (stack_repr_store_other_block hm m m1 _ sp_b sp_ofs sb (uso + 8) cv).
            * exact Hstack_repr.
            * exact Hstore1.
            * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          + exact Hstore2.
          + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2.
          eapply Mem.perm_store_1. exact Hstore1.
          apply Hsp_writable. exact Hofs'.
        - exact Hsp_align. }

      (* 5. env field -- unchanged *)
      { exists env_v. split.
        - exact Henv_load2.
        - simpl. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { simpl. exact Hextra_load2. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load2.
        - simpl. exact Hgd_eq.
        - simpl.
          eapply (global_repr_store_other_block hm m1 m2 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sb (uso + 0) new_pc_v).
          + eapply (global_repr_store_other_block hm m m1 _
                     (ar_global_block ard) (ar_global_ofs ard)
                     sb (uso + 8) cv).
            * exact Hglobal_repr.
            * exact Hstore1.
            * intro Heq2; exact (Hgb_ne_sb (eq_sym Heq2)).
          + exact Hstore2.
          + intro Heq2; exact (Hgb_ne_sb (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load2.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved *)
      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2.
        eapply Mem.perm_store_1. exact Hstore1.
        apply Hsb_writable. exact Hofs'. }
    }
  }
Qed.
