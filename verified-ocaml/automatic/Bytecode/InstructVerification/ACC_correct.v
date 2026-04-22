(* ACC_correct.v -- ACC (parameterized) handler completeness proof.

   ACC n: reads index n from the code buffer, then reads stack[n],
   stores to accu, and advances pc past the argument.

   C code (f_instr_ACC):
     _t'1 = s->pc;             // read pc pointer (points to n in code buffer)
     s->pc = _t'1 + 1;         // advance pc past argument
     _t'2 = s->sp;             // read sp pointer
     _t'3 = *_t'1;             // read n from code buffer (Mint32)
     _t'4 = *(_t'2 + _t'3);   // stack[n] (pointer arith: each elem = 8 bytes)
     s->accu = _t'4;           // store to accu
     return 0;

   Rocq:
     handle_ACC n pc' s =
       match nth_error s.(stack) n with
       | Some v => Step (s <|pc := pc'|> <|accu := v|>)
       | None => Error "ACC: stack underflow"
       end

   Two stores: pc field at offset +0, accu field at offset +8.

   Combines the CONSTINT code-buffer-read pattern with ACC0's
   stack access pattern, generalized over n.

   NO AXIOMS.  All structural/range constraints are preconditions
   via handler_correct. *)

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
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout: _pc at offset 0, _sp at offset 16, _accu at offset 8 *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_pc_sp_accu : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* sp + n : pointer arithmetic on (tptr tlong), where n is tint.
   sizeof(tlong) = 8, so sp + n = sp + n * 8 bytes. *)
Lemma sem_add_sp_n : forall sp_b sp_ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint n) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs
                (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* pc_rel with shifted code base *)
Lemma pc_rel_shift : forall cb co rocq_pc,
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
(* stack_repr_nth: connect nth_error with stack_repr memory loads.     *)
(* If stack_repr relates the Rocq list to memory at (sp_b, sp_ofs),   *)
(* then nth_error stk n = Some v implies there is a CompCert value    *)
(* cv at sp + n*8 with val_repr hm v cv.                              *)
(* ================================================================== *)

Lemma ptrofs_max_unsigned_large : (Ptrofs.max_unsigned >= 2^32)%Z.
Proof. vm_compute. discriminate. Qed.

Lemma ptrofs_add_repr : forall a b,
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  intros. rewrite Ptrofs.add_unsigned.
  apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add;
    apply Ptrofs.eqm_sym;
    apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma stack_repr_nth : forall n hm cb co m stk sp_b sp_ofs v,
  stack_repr hm cb co m stk sp_b sp_ofs ->
  nth_error stk n = Some v ->
  exists cv,
    Mem.load Mint64 m sp_b
      (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some cv /\
    val_repr hm cb co v cv.
Proof.
  induction n as [| n' IH]; intros hm cb co m stk sp_b sp_ofs v Hsr Hnth.
  - (* n = 0 *)
    destruct stk as [| v0 rest].
    + discriminate.
    + simpl in Hnth. inversion Hnth; subst.
      inversion Hsr as [| xv xvs xb xofs xcv Hload Hvr Hrest].
      subst xv xvs xb xofs.
      exists xcv. split.
      * replace (Z.of_nat 0 * 8)%Z with 0%Z by lia.
        change (Ptrofs.repr 0) with Ptrofs.zero.
        rewrite Ptrofs.add_zero. exact Hload.
      * exact Hvr.
  - (* n = S n' *)
    destruct stk as [| v0 rest].
    + discriminate.
    + simpl in Hnth.
      inversion Hsr as [| xv xvs xb xofs xcv Hload Hvr Hrest].
      subst xv xvs xb xofs.
      specialize (IH hm cb co m rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) v Hrest Hnth).
      destruct IH as [cv' [Hload' Hvr']].
      exists cv'. split.
      * (* Rewrite offset: (sp + 8) + n'*8 = sp + (S n')*8 *)
        replace (Z.of_nat (S n') * 8)%Z with (8 + Z.of_nat n' * 8)%Z by lia.
        rewrite <- ptrofs_add_repr.
        rewrite <- Ptrofs.add_assoc.
        exact Hload'.
      * exact Hvr'.
Qed.

(* ================================================================== *)
(* ptrofs_mul_8_of_ints_eq: relate C pointer arithmetic to logical    *)
(* ================================================================== *)

Lemma ptrofs_mul_8_of_ints_eq : forall n,
  0 <= n ->
  n < Int.half_modulus ->
  Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr n))
  = Ptrofs.repr (n * 8).
Proof.
  intros n Hnn Hn_bound.
  unfold ptrofs_of_int, Ptrofs.of_ints.
  change Int.half_modulus with 2147483648 in Hn_bound.
  rewrite Int.signed_repr.
  2: { change Int.min_signed with (-2147483648).
       change Int.max_signed with 2147483647. lia. }
  unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 8).
  2: { pose proof ptrofs_max_unsigned_large. lia. }
  rewrite (Ptrofs.unsigned_repr n).
  2: { pose proof ptrofs_max_unsigned_large. lia. }
  f_equal. lia.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_ACC_correct : forall n,
    Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_ACC n) f_instr_ACC
      (fun _ m s ard =>
         (* The code buffer contains Int.repr n at the current PC position *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* n fits in the signed int32 range *)
         Z.of_nat n < Int.half_modulus /\
         (* sp + n*8 fits in ptrofs range *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs + Z.of_nat n * 8 < Ptrofs.modulus))
      (fun _ s => nth_error s.(Machine.stack) n = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro n. intro Hn_range_hyp.
  intros e le m s.
  unfold handler_correct, handle_ACC.
  replace (Z.of_nat n <? Int.half_modulus)%Z with true.
  2: { symmetry. apply Z.ltb_lt. exact Hn_range_hyp. }

  (* Case split on nth_error *)
  destruct (nth_error (Machine.stack s) n) as [v|] eqn:Hnth.

  (* ================================================================ *)
  (* Case 1: nth_error stack n = Some v => Step                        *)
  (* ================================================================ *)
  2: { (* Error case: trivially true *)
    reflexivity. }

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

    destruct Hstep_pre as (Hcode_load & Hn_bound & Hsp_fits).

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
    pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

    (* Composite environment *)
    destruct interp_state_co_pc_sp_accu as [co_is [Hco [Hpc_offset [Hsp_offset Haccu_offset]]]].

    (* pc_ptr is a concrete Vptr *)
    unfold pc_rel in Hpc_rel. subst pc_ptr.
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

    (* sp_fits for our concrete sp_ofs *)
    assert (Hsp_fits_concrete : Ptrofs.unsigned sp_ofs + Z.of_nat n * 8 < Ptrofs.modulus).
    { apply (Hsp_fits sp_b sp_ofs). exact Hsp_load. }

    (* nth_error yields a val_repr via stack_repr_nth *)
    destruct (stack_repr_nth n hm cb co m (Machine.stack s) sp_b sp_ofs v
                Hstack_repr Hnth) as [cv [Hload_cv Hval_repr_cv]].

    (* The ptrofs mul simplification *)
    assert (Hsp_n_eq :
      Ptrofs.add sp_ofs (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat n))))
      = Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat n * 8))).
    { f_equal. apply ptrofs_mul_8_of_ints_eq; lia. }

    (* New PC after advancement *)
    set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
    set (new_pc_v := Vptr cb new_pc_ofs).

    (* Store 1: pc field at (sb, uso+0) <- new_pc_v *)
    destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia) new_pc_v)
      as [m1 Hstore_pc].
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore_pc Hsb_writable) as Hsb_writable_m1.

    (* accu field in m1: unaffected by store at offset 0 *)
    assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
               (Ptrofs.unsigned so + 8) new_pc_v accu_v
               Hstore_pc Haccu_load). right. lia. }

    (* sp field in m1: unaffected by store at offset 0 *)
    assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
              Some (Vptr sp_b sp_ofs)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
               (Ptrofs.unsigned so + 16) new_pc_v (Vptr sp_b sp_ofs)
               Hstore_pc Hsp_load). right. lia. }

    (* Code buffer load survives store1 (different block) *)
    assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
              Some (Vint (Int.repr (Z.of_nat n)))).
    { apply (code_buffer_load_at Mint32 Mint64 m m1 cb sb
               (Ptrofs.unsigned pc_ofs) (Ptrofs.unsigned so + 0)
               (Vint (Int.repr (Z.of_nat n))) new_pc_v
               Hcode_load Hstore_pc Hcb_ne). }

    (* Stack load survives store1 (different block: sp_b <> sb) *)
    assert (Hload_cv_m1 : Mem.load Mint64 m1 sp_b
              (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some cv).
    { apply (code_buffer_load_at Mint64 Mint64 m m1 sp_b sb
               (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat n * 8))))
               (Ptrofs.unsigned so + 0) cv new_pc_v
               Hload_cv Hstore_pc Hsp_ne_sb). }

    (* Store 2: accu field at (sb, uso+8) <- cv *)
    destruct (store_succeeds_sb m1 sb so 8 accu_v Hsb_writable_m1 Haccu_load_m1 ltac:(lia) ltac:(lia) cv)
      as [m2 Hstore_accu].

    (* Witnesses *)
    set (le' := PTree.set _t'4 cv
                (PTree.set _t'3 (Vint (Int.repr (Z.of_nat n)))
                (PTree.set _t'2 (Vptr sp_b sp_ofs)
                (PTree.set _t'1 (Vptr cb pc_ofs) le)))).
    exists le'. exists m2.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (* ============================================================== *)
    {
      apply (eval_stmt_to_exec clight_ge 20).
      eval_cbn.

      (* S1: Sset _t'1 (s->pc) -- read pc pointer from struct *)
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load; eval_cbn.

      (* S2: Sassign (s->pc) (_t'1 + 1) -- advance pc *)
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_pc_1 cb pc_ofs m); eval_cbn.
      rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      fold new_pc_v.
      rewrite Hstore_pc; eval_cbn.

      (* S3: Sset _t'2 (s->sp) -- read sp pointer *)
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hsp_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      rewrite Hsp_load_m1; eval_cbn.

      (* S4: Sset _t'3 (deref _t'1) -- read n from code buffer *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite Hcode_load_m1; eval_cbn.

      (* S5: Sset _t'4 (deref (_t'2 + _t'3)) -- read stack[n]
         le = _t'3 -> n, _t'2 -> sp, _t'1 -> pc, le_orig
         Eval order: _t'2 (left), then _t'3 (right) *)
      (* _t'2: skip _t'3 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      (* _t'3: top of env *)
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_sp_n sp_b sp_ofs (Int.repr (Z.of_nat n)) m1); eval_cbn.
      rewrite Hsp_n_eq.
      rewrite Hload_cv_m1; eval_cbn.

      (* S6: Sassign (s->accu) _t'4 -- store to accu *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Haccu_offset; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hval_repr_cv); eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Hstore_accu; eval_cbn.

      (* S7: Sreturn 0 *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      (* Construct ard' with shifted code_base_ofs *)
      set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
      set (ard' := mk_abs_rel sb so hm cb new_co
                     (ar_global_block ard) (ar_global_ofs ard)
                     (ar_stack_block ard) (ar_stack_base_ofs ard)
                     (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard)
                     (ar_sptr_ofs_bound ard)).
      exists ard'.

      set (uso := Ptrofs.unsigned so) in *.

      (* pc field at uso+0: written by store1, unaffected by store2 *)
      assert (Hpc_load2 : Mem.load Mint64 m2 sb (uso + 0) = Some new_pc_v).
      { assert (Hpc_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some new_pc_v).
        { pose proof (load_after_store_same m m1 sb (uso + 0) new_pc_v Hstore_pc) as Htmp.
          unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }
        apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 0)
                 cv new_pc_v Hstore_accu Hpc_m1).
        left. lia. }

      (* accu field at uso+8: written by store2 *)
      assert (Haccu_load2 : Mem.load Mint64 m2 sb (uso + 8) = Some cv).
      { pose proof (load_after_store_same m1 m2 sb (uso + 8) cv Hstore_accu) as Htmp.
        rewrite (val_repr_load_result hm cb co v cv Hval_repr_cv) in Htmp.
        exact Htmp. }

      (* sp field at uso+16: unaffected by both stores *)
      assert (Hsp_load2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m1 sb (uso + 0) (uso + 16)
                   new_pc_v (Vptr sp_b sp_ofs) Hstore_pc Hsp_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 16)
                 cv (Vptr sp_b sp_ofs) Hstore_accu Hsp_m1).
        right. lia. }

      (* env field at uso+24: unaffected *)
      assert (Henv_load2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
      { assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m1 sb (uso + 0) (uso + 24)
                   new_pc_v env_v Hstore_pc Henv_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 24)
                 cv env_v Hstore_accu Henv_m1).
        right. lia. }

      (* extra_args field at uso+32: unaffected *)
      assert (Hextra_load2 : Mem.load Mint64 m2 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { assert (Hextra_m1 : Mem.load Mint64 m1 sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m1 sb (uso + 0) (uso + 32)
                   new_pc_v _ Hstore_pc Hextra_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 32)
                 cv _ Hstore_accu Hextra_m1).
        right. lia. }

      (* global_data field at uso+40: unaffected *)
      assert (Hgd_load2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
      { assert (Hgd_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m1 sb (uso + 0) (uso + 40)
                   new_pc_v gd_ptr Hstore_pc Hgd_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 40)
                 cv gd_ptr Hstore_accu Hgd_m1).
        right. lia. }

      (* trap_sp field at uso+48: unaffected *)
      assert (Hts_load2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
      { assert (Hts_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m1 sb (uso + 0) (uso + 48)
                   new_pc_v ts_ptr Hstore_pc Hts_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 48)
                 cv ts_ptr Hstore_accu Hts_m1).
        right. lia. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field -- updated to new_pc_v *)
      { exists new_pc_v. split.
        - exact Hpc_load2.
        - simpl. subst new_pc_v new_pc_ofs.
          apply pc_rel_shift. }

      (* 3. accu field -- updated to stack[n] *)
      { exists cv. split.
        - exact Haccu_load2.
        - simpl. eapply val_repr_co_shift. exact Hval_repr_cv. }

      (* 4. sp field -- unchanged *)
      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load2.
        - reflexivity.
        - simpl. eapply stack_repr_co_shift.
          eapply (stack_repr_store_other_block hm cb co m1 m2 _ sp_b sp_ofs sb (uso + 8) cv).
          + eapply (stack_repr_store_other_block hm cb co m m1 _ sp_b sp_ofs sb (uso + 0) new_pc_v).
            * exact Hstack_repr.
            * exact Hstore_pc.
            * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          + exact Hstore_accu.
          + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore_accu.
          eapply Mem.perm_store_1. exact Hstore_pc. apply Hsp_writable. exact Hofs'.
        - exact Hsp_align. }

      (* 5. env field -- unchanged *)
      { exists env_v. split.
        - exact Henv_load2.
        - simpl. eapply val_repr_co_shift. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { simpl. exact Hextra_load2. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load2.
        - simpl. exact Hgd_eq.
        - simpl. eapply global_repr_co_shift.
          apply (global_repr_store_other_block hm cb co m1 m2 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sb (uso + 8) cv).
          + apply (global_repr_store_other_block hm cb co m m1 _
                     (ar_global_block ard) (ar_global_ofs ard)
                     sb (uso + 0) new_pc_v
                     Hglobal_repr Hstore_pc).
            intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          + exact Hstore_accu.
          + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load2.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved *)
      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore_accu.
        eapply Mem.perm_store_1. exact Hstore_pc. apply Hsb_writable. exact Hofs'. }
    }
  }
Qed.

(* Wrapper with building-block precondition for Module Type *)
Theorem verify_ACC_handler_correct : forall n,
    Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_ACC n) f_instr_ACC
      (code_at (Int.repr (Z.of_nat n)))
      (fun _ s => nth_error s.(Machine.stack) n = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros n Hn.
  eapply handler_correct_weaken_step.
  - exact (verify_ACC_correct n Hn).
  - intros e le m s s' ard Hstep Hrel Hca.
    split. { exact Hca. }
    split. { exact Hn. }
    (* Derive SP offset constraint from abs_rel + Step case *)
    intros sp_b sp_ofs Hsp_load.
    (* From Step case: n < length stack *)
    unfold handle_ACC in Hstep.
    replace (Z.of_nat n <? Int.half_modulus)%Z with true in Hstep
      by (symmetry; apply Z.ltb_lt; exact Hn).
    destruct (nth_error (Machine.stack s) n) eqn:Hnth; [|discriminate].
    assert (Hn_lt : (n < length (Machine.stack s))%nat).
    { apply nth_error_Some. congruence. }
    (* From abs_rel: extract SP bound *)
    destruct Hrel as (_ & _ & _ & (sp_ptr' & sp_b' & sp_ofs' & Hsp_load' & Heq' & _ & _ & _ & _ & _ & Hsp_bound & _ & _) & _).
    subst sp_ptr'.
    rewrite Hsp_load' in Hsp_load. injection Hsp_load. intros; subst.
    lia.
Qed.

(* Wrapper matching InstructVerificationFineGrainedSpec signature.
   handle_instr (ACC n) reduces to handle_ACC n by computation.
   clight_of (ACC n) = f_instr_ACC, pre_of (ACC n) = code_at (Int.repr (Z.of_nat n)).
   Error case (stack underflow) matches P_error_of exactly.
   Step case delegates to verify_ACC_handler_correct (requires Z.of_nat n < Int.half_modulus). *)
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

Theorem correct_ACC : forall n,
    handler_correct (handle_instr (ACC n)) (clight_of (ACC n))
      (pre_of (ACC n))
      (P_error_of (ACC n)) (P_halt_of (ACC n)) (P_ccall_of (ACC n)).
Proof.
  intro n.
  unfold handler_correct.
  intros e le m s.
  change (handle_instr (ACC n) (Machine.pc s) s)
    with (handle_ACC n (Machine.pc s) s).
  unfold handle_ACC at 1.
  destruct (Z.ltb_spec (Z.of_nat n) Int.half_modulus) as [Hn_bound|Hn_big].
  - (* n < Int.half_modulus *)
    destruct (nth_error (Machine.stack s) n) as [v|] eqn:Hnth.
    + (* Step case: nth_error stack n = Some v *)
      pose proof (verify_ACC_handler_correct n Hn_bound) as H.
      unfold handler_correct, handle_ACC in H. specialize (H e le m s).
      replace (Z.of_nat n <? Int.half_modulus)%Z with true in H
        by (symmetry; apply Z.ltb_lt; exact Hn_bound).
      rewrite Hnth in H.
      change (pre_of (ACC n)) with (code_at (Int.repr (Z.of_nat n))).
      exact H.
    + (* Error case: nth_error stack n = None, stack underflow *)
      unfold P_error_of, error_message_of.
      replace (Z.of_nat n <? Int.half_modulus)%Z with true
        by (symmetry; apply Z.ltb_lt; exact Hn_bound).
      rewrite Hnth. reflexivity.
  - (* n >= Int.half_modulus: handler returns Error, P_error_of satisfied *)
    unfold P_error_of, error_message_of.
    replace (Z.of_nat n <? Int.half_modulus)%Z with false
      by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
Qed.
