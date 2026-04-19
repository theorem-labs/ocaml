(* APPLY_correct.v -- APPLY handler correctness proof.

   APPLY n: tail call with n args already on stack.
   Reads nargs from the code buffer, stores nargs-1 to extra_args,
   reads the closure code pointer from accu[0], stores to pc,
   copies accu to env.

   C body (f_instr_APPLY):
     _t'4 = s->pc;
     _t'5 = *_t'4;                  // read nargs from code buffer
     s->extra_args = (long)(_t'5 - 1);  // store nargs-1
     _t'2 = s->accu;
     _t'3 = deref((code_t ptr ptr)_t'2 + 0); // read code pointer from closure
     s->pc = _t'3;                   // jump to code pointer
     _t'1 = s->accu;
     s->env = _t'1;                  // set env to closure
     return 0;

   Rocq handler (Interpret.v):
     handle_APPLY n s =
       match get_code_ptr_s s s.(accu) with
       | Some target_pc =>
         Step (s <|pc := target_pc|> <|env := s.(accu)|>
                 <|extra_args := Nat.sub n 1|>)
       | None => Error "APPLY: accu is not a closure"
       end

   Three stores: extra_args (offset 32), pc (offset 0), env (offset 24).

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
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout: _pc@0, _accu@8, _extra_args@32, _env@24             *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full).
Proof.
  eexists. split; [| split; [| split; [| split]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_apply : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

(* sem_sub for tint - tint: goes through sem_binarith *)
Local Lemma sem_sub_int_int : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vint n1) tint (Vint n2) tint m
    = Some (Vint (Int.sub n1 n2)).
Proof. intros. reflexivity. Qed.

(* sem_cast for tint -> tlong *)
Local Lemma sem_cast_int_to_long : forall n m,
  sem_cast (Vint n) tint tlong m = Some (Vlong (Int64.repr (Int.signed n))).
Proof.
  intros. unfold sem_cast.
  change (classify_cast tint tlong) with (cast_case_i2l Signed).
  simpl. reflexivity.
Qed.

(* sem_cast for tlong -> (tptr (tptr tint)) when value is Vptr *)
Local Lemma sem_cast_long_to_ptptint_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr (tptr tint)) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* sem_add for (tptr (tptr tint)) + 0 *)
Local Lemma sem_add_ptptint_0 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr (tptr tint)) (Vint (Int.repr 0)) tint m
    = Some (Vptr b ofs).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr (tptr tint)) tint) with (add_case_pi (tptr tint) Signed).
  unfold sem_add_ptr_int.
  change (sizeof (genv_cenv clight_ge) (tptr tint)) with 8%Z.
  f_equal. f_equal.
  unfold ptrofs_of_int.
  change (Ptrofs.of_ints (Int.repr 0)) with Ptrofs.zero.
  rewrite Ptrofs.mul_zero, Ptrofs.add_zero. reflexivity.
Qed.

(* sem_cast for (tptr tint) -> (tptr tint) is identity *)
Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* ================================================================== *)
(* Closure code pointer precondition                                   *)
(* ================================================================== *)

(* When get_code_ptr_s succeeds, the C memory must contain the code
   pointer at the accu's pointer location, the accu block must be
   separate from sb and cb, and the code pointer must satisfy pc_rel. *)
Definition apply_step_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let cb := ar_code_base_block ard in
  forall target_pc,
    get_code_ptr_s s s.(Machine.accu) = Some target_pc ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists accu_b accu_ofs code_b code_ofs,
        accu_v = Vptr accu_b accu_ofs /\
        Mem.load Mptr m accu_b (Ptrofs.unsigned accu_ofs) = Some (Vptr code_b code_ofs) /\
        accu_b <> sb /\
        accu_b <> cb /\
        (exists new_co,
          code_ofs = Ptrofs.add new_co (Ptrofs.repr (target_pc * sizeof_code_t)) /\
          code_b = cb).

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Local Lemma val_repr_co_shift : forall hm cb co co' v cv,
  val_repr hm cb co v cv -> val_repr hm cb co' v cv.
Proof.
  intros. inversion H; subst.
  - constructor. - eapply vr_ptr; eassumption.
  - eapply vr_closure; eauto. - constructor. - eapply vr_code_ptr.
Qed.
Local Lemma stack_repr_co_shift : forall hm cb co co' m stk b ofs,
  stack_repr hm cb co m stk b ofs -> stack_repr hm cb co' m stk b ofs.
Proof.
  intros hm0 cb0 co0 co' m0 stk0 b0 ofs0 H. induction H.
  - constructor. - econstructor; [eassumption | eapply val_repr_co_shift; eassumption | assumption].
Qed.
Local Lemma global_repr_co_shift : forall hm cb co co' m vs b ofs,
  global_repr hm cb co m vs b ofs -> global_repr hm cb co' m vs b ofs.
Proof.
  intros hm0 cb0 co0 co' m0 vs0 b0 ofs0 H. induction H.
  - constructor. - econstructor; [eassumption | eapply val_repr_co_shift; eassumption | assumption].
Qed.

Theorem verify_APPLY_correct : forall n,
    handler_correct (fun _ s => handle_APPLY n s) f_instr_APPLY
      (fun _ m s ard =>
         (* The code buffer contains Int.repr (Z.of_nat n) at the current PC *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* n fits in int32 signed range *)
         Int.min_signed <= Z.of_nat n <= Int.max_signed /\
         (* n >= 1 (APPLY always has at least 1 arg) *)
         (1 <= n)%nat /\
         (* Closure code pointer is loadable *)
         apply_step_pre m s ard)
      (fun msg s => get_code_ptr_s s s.(Machine.accu) = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro n.
  intros e le m s.
  unfold handler_correct.
  simpl.
  unfold handle_APPLY.

  destruct (get_code_ptr_s s s.(Machine.accu)) as [target_pc|] eqn:Hgcp.

  2: { (* Error case *) reflexivity. }

  (* Step case *)
  intros ard Hpre Hstep_pre.

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

  destruct Hstep_pre as (Hcode_load & Hn_range & Hn_ge1 & Hacpl).

  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  destruct interp_state_co_apply as [co_is [Hco [Hpc_offset [Haccu_offset [Hextra_offset Henv_offset]]]]].

  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* Get closure code pointer info *)
  unfold apply_step_pre in Hacpl.
  destruct (Hacpl target_pc Hgcp accu_v Haccu_repr)
    as [accu_b [accu_ofs [code_b [code_ofs
        [Haccu_is_ptr [Hcode_ptr_load [Haccu_ne_sb [Haccu_ne_cb
        [new_co [Hcode_ofs_eq Hcode_b_eq]]]]]]]]]].
  subst accu_v code_b.

  (* Computed values *)
  set (nargs_int := Int.repr (Z.of_nat n)).
  set (nargs_sub1 := Int.sub nargs_int (Int.repr 1)).
  set (ea_long := Int64.repr (Int.signed nargs_sub1)).
  set (ea_val := Vlong ea_long).
  set (new_pc_v := Vptr cb code_ofs).
  set (new_env_v := Vptr accu_b accu_ofs).

  (* Store 1: extra_args at offset 32 *)
  destruct (store_succeeds_sb m sb so 32
              (Vlong (Int64.repr (Z.of_nat (extra_args s))))
              Hsb_writable Hextra_load ltac:(lia) ltac:(lia) ea_val)
    as [m1 Hstore1].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

  (* Store 2: pc at offset 0 *)
  assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 32)
             (Ptrofs.unsigned so + 0) ea_val (Vptr cb pc_ofs)
             Hstore1 Hpc_load). left. lia. }
  destruct (store_succeeds_sb m1 sb so 0 (Vptr cb pc_ofs)
              Hsb_writable_m1 Hpc_load_m1 ltac:(lia) ltac:(lia) new_pc_v)
    as [m2 Hstore2].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore2 Hsb_writable_m1) as Hsb_writable_m2.

  (* Store 3: env at offset 24 *)
  assert (Henv_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 24) = Some env_v).
  { assert (Henv_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 24)
               ea_val env_v Hstore1 Henv_load). left. lia. }
    apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 24)
             new_pc_v env_v Hstore2 Henv_m1). right. lia. }
  destruct (store_succeeds_sb m2 sb so 24 env_v
              Hsb_writable_m2 Henv_load_m2 ltac:(lia) ltac:(lia) new_env_v)
    as [m3 Hstore3].

  (* Loads in intermediate memories *)
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 32)
             (Ptrofs.unsigned so + 8) ea_val (Vptr accu_b accu_ofs)
             Hstore1 Haccu_load). left. lia. }

  assert (Hcode_ptr_load_m1 : Mem.load Mptr m1 accu_b (Ptrofs.unsigned accu_ofs) =
            Some (Vptr cb code_ofs)).
  { erewrite Mem.load_store_other. exact Hcode_ptr_load. exact Hstore1.
    left. exact Haccu_ne_sb. }

  assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 8) new_pc_v (Vptr accu_b accu_ofs)
             Hstore2 Haccu_load_m1). right. lia. }

  (* Code buffer load in m1 (different block) *)
  assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
            Some (Vint nargs_int)).
  { erewrite Mem.load_store_other. exact Hcode_load. exact Hstore1.
    left. exact Hcb_ne. }

  (* Witnesses *)
  set (le1 := PTree.set _t'4 (Vptr cb pc_ofs) le).
  set (le2 := PTree.set _t'5 (Vint nargs_int) le1).
  set (le3 := PTree.set _t'2 (Vptr accu_b accu_ofs) le2).
  set (le4 := PTree.set _t'3 (Vptr cb code_ofs) le3).
  set (le5 := PTree.set _t'1 (Vptr accu_b accu_ofs) le4).
  exists le5. exists m3.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ================================================================ *)
  (* Part 1: exec -- the C body executes                               *)
  (* ================================================================ *)
  {
    apply (eval_stmt_to_exec clight_ge 20).
    eval_cbn.

    (* === S1: Sset _t'4 (s->pc) === *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hpc_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load; eval_cbn.

    (* === S2: Sset _t'5 (deref _t'4) -- read nargs from code buffer === *)
    rewrite PTree.gss; eval_cbn.
    rewrite Hcode_load; eval_cbn.

    (* === S3: Sassign s->extra_args = (long)(_t'5 - 1) === *)
    (* Lvalue: s->extra_args *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'5 *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'4 *)
    rewrite Hle_s; eval_cbn.
    rewrite Hextra_offset; eval_cbn.

    (* Rvalue: _t'5 - 1 then cast to tlong *)
    rewrite PTree.gss; eval_cbn.   (* _t'5 *)
    rewrite (sem_sub_int_int (Int.repr (Z.of_nat n)) (Int.repr 1) m); eval_cbn.
    rewrite (sem_cast_int_to_long (Int.sub (Int.repr (Z.of_nat n)) (Int.repr 1)) m); eval_cbn.

    (* Store extra_args *)
    rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
    unfold ea_val, ea_long, nargs_sub1, nargs_int in Hstore1.
    rewrite Hstore1; eval_cbn.

    (* === S4: Sset _t'2 (s->accu) -- in m1 === *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'5 *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'4 *)
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m1; eval_cbn.

    (* === S5: Sset _t'3 = *((tptr (tptr tint))(_t'2) + 0) === *)
    rewrite PTree.gss; eval_cbn.
    (* Cast: tlong -> (tptr (tptr tint)) for Vptr *)
    rewrite sem_cast_long_to_ptptint_vptr; eval_cbn.
    (* Add: ptr + 0 *)
    rewrite (sem_add_ptptint_0 accu_b accu_ofs m1); eval_cbn.
    (* Deref: load code pointer -- Mptr = Mint64 load *)
    rewrite Mptr_Mint64; eval_cbn.
    rewrite Mptr_Mint64 in Hcode_ptr_load_m1.
    rewrite Hcode_ptr_load_m1; eval_cbn.

    (* === S6: Sassign s->pc = _t'3 === *)
    (* Lvalue: s->pc *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'3 *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'2 *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'5 *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'4 *)
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.

    (* Rvalue: _t'3 *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_ptr_tint_to_ptr_tint; eval_cbn.

    (* Store pc *)
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    fold new_pc_v.
    rewrite Hstore2; eval_cbn.

    (* === S7: Sset _t'1 (s->accu) -- in m2 === *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'3 *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'2 *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'5 *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'4 *)
    rewrite Hle_s; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m2; eval_cbn.

    (* === S8: Sassign s->env = _t'1 === *)
    (* Lvalue: s->env *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'1 *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'3 *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'2 *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'5 *)
    rewrite PTree.gso by (compute; congruence).  (* _s <> _t'4 *)
    rewrite Hle_s; eval_cbn.
    rewrite Henv_offset; eval_cbn.

    (* Rvalue: _t'1 = accu *)
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_vptr accu_b accu_ofs m2); eval_cbn.

    (* Store env *)
    rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
    fold new_env_v.
    rewrite Hstore3; eval_cbn.

    (* === S9: Sreturn 0 === *)
    subst le5 le4 le3 le2 le1. reflexivity.
  }

  (* ================================================================ *)
  (* Part 2: abs_rel for post-state                                    *)
  (* ================================================================ *)
  {
    set (ard' := mk_abs_rel sb so hm cb new_co
                   (ar_global_block ard) (ar_global_ofs ard)
                   (ar_stack_block ard) (ar_stack_base_ofs ard)
                   (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard)
                   (ar_sptr_ofs_bound ard)).
    exists ard'.

    (* pc field at uso+0: written in store2, unaffected by store3 *)
    assert (Hpc_load3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
    { assert (Hpc_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
      { pose proof (load_after_store_same m1 m2 sb (Ptrofs.unsigned so + 0) new_pc_v Hstore2) as Htmp.
        unfold new_pc_v in Htmp. simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp.
        exact Htmp. }
      apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 0)
               new_env_v new_pc_v Hstore3 Hpc_m2). left. lia. }

    (* accu field at uso+8 in m3 *)
    assert (Haccu_load3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 8) =
              Some (Vptr accu_b accu_ofs)).
    { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 24)
               (Ptrofs.unsigned so + 8) new_env_v (Vptr accu_b accu_ofs)
               Hstore3 Haccu_load_m2). left. lia. }

    (* sp field at uso+16 *)
    assert (Hsp_load3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
    { assert (Hsp_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 16)
                 ea_val (Vptr sp_b sp_ofs) Hstore1 Hsp_load). left. lia. }
      assert (Hsp_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
                 new_pc_v (Vptr sp_b sp_ofs) Hstore2 Hsp_m1). right. lia. }
      apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 16)
               new_env_v (Vptr sp_b sp_ofs) Hstore3 Hsp_m2). left. lia. }

    (* env field at uso+24: written in store3 *)
    assert (Henv_load3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 24) = Some new_env_v).
    { pose proof (load_after_store_same m2 m3 sb (Ptrofs.unsigned so + 24) new_env_v Hstore3) as Htmp.
      unfold new_env_v in Htmp. simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp.
      exact Htmp. }

    (* extra_args field at uso+32: written in store1, unaffected by store2 and store3 *)
    assert (Hextra_load3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 32) = Some ea_val).
    { assert (Hextra_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) = Some ea_val).
      { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 32) ea_val Hstore1) as Htmp.
        subst ea_val. simpl Val.load_result in Htmp. exact Htmp. }
      assert (Hextra_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 32) = Some ea_val).
      { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 32)
                 new_pc_v ea_val Hstore2 Hextra_m1). right. lia. }
      apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 32)
               new_env_v ea_val Hstore3 Hextra_m2). right. lia. }

    (* global_data field at uso+40 *)
    assert (Hgd_load3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
    { assert (Hgd_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 40)
                 ea_val gd_ptr Hstore1 Hgd_load). right. lia. }
      assert (Hgd_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
      { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 40)
                 new_pc_v gd_ptr Hstore2 Hgd_m1). right. lia. }
      apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 40)
               new_env_v gd_ptr Hstore3 Hgd_m2). right. lia. }

    (* trap_sp field at uso+48 *)
    assert (Hts_load3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
    { assert (Hts_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 48)
                 ea_val ts_ptr Hstore1 Hts_load). right. lia. }
      assert (Hts_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 48)
                 new_pc_v ts_ptr Hstore2 Hts_m1). right. lia. }
      apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 48)
               new_env_v ts_ptr Hstore3 Hts_m2). right. lia. }

    (* Writable permission after three stores *)
    assert (Hsb_writable_m3 : Mem.range_perm m3 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs' Hofs'.
      eapply Mem.perm_store_1. exact Hstore3.
      eapply Mem.perm_store_1. exact Hstore2.
      eapply Mem.perm_store_1. exact Hstore1.
      apply Hsb_writable. exact Hofs'. }

    (* le5 ! _s *)
    assert (Hle5_s : le5 ! _s = Some (Vptr sb so)).
    { subst le5 le4 le3 le2 le1.
      repeat (rewrite PTree.gso by (compute; congruence)).
      exact Hle_s. }

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le' *)
    { exact Hle5_s. }

    (* 2. pc field -- updated to new_pc_v = Vptr cb code_ofs *)
    { exists new_pc_v. split.
      - exact Hpc_load3.
      - simpl. unfold pc_rel, new_pc_v. f_equal.
        subst code_ofs. reflexivity. }

    (* 3. accu field -- unchanged *)
    { exists (Vptr accu_b accu_ofs). split.
      - exact Haccu_load3.
      - simpl. eapply val_repr_co_shift; exact Haccu_repr. }

    (* 4. sp field -- unchanged *)
    { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load3.
      - reflexivity.
      - simpl.
        eapply stack_repr_co_shift.
        apply (stack_repr_store_other_block hm cb co m2 m3 _ sp_b sp_ofs sb (Ptrofs.unsigned so + 24) new_env_v).
        + apply (stack_repr_store_other_block hm cb co m1 m2 _ sp_b sp_ofs sb (Ptrofs.unsigned so + 0) new_pc_v).
          * apply (stack_repr_store_other_block hm cb co m m1 _ sp_b sp_ofs sb (Ptrofs.unsigned so + 32) ea_val).
            exact Hstack_repr. exact Hstore1.
            intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
          * exact Hstore2.
          * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        + exact Hstore3.
        + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - exact Hsp_ge8.
      - exact Hsp_rep.
      - intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore3.
        eapply Mem.perm_store_1. exact Hstore2.
        eapply Mem.perm_store_1. exact Hstore1.
        apply Hsp_writable. exact Hofs'.
      - exact Hsp_align. }

    (* 5. env field -- updated to accu *)
    { exists new_env_v. split.
      - exact Henv_load3.
      - simpl. eapply val_repr_co_shift; exact Haccu_repr. }

    (* 6. extra_args field -- updated to (n-1) *)
    { simpl. rewrite Hextra_load3.
      (* ea_val may or may not still be set-defined; use enough unfolds *)
      unfold ea_val, ea_long, nargs_sub1, nargs_int.
      do 3 f_equal.
      (* Goal: Int.signed (Int.sub (Int.repr (Z.of_nat n)) (Int.repr 1)) = Z.of_nat (n - 1) *)
      rewrite Int.sub_signed.
      rewrite (Int.signed_repr (Z.of_nat n) Hn_range).
      change (Int.signed (Int.repr 1)) with 1.
      assert (Hn_lo : -2147483648 <= Z.of_nat n) by
        (destruct Hn_range; change Int.min_signed with (-2147483648) in *; lia).
      assert (Hn_hi : Z.of_nat n <= 2147483647) by
        (destruct Hn_range; change Int.max_signed with 2147483647 in *; lia).
      rewrite Int.signed_repr by
        (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
      rewrite Nat2Z.inj_sub by exact Hn_ge1. lia. }

    (* 7. global_data field -- unchanged *)
    { exists gd_ptr. split; [| split; [| split]].
      - exact Hgd_load3.
      - simpl. exact Hgd_eq.
      - simpl.
        eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m2 m3 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (Ptrofs.unsigned so + 24) new_env_v).
        + apply (global_repr_store_other_block hm cb co m1 m2 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sb (Ptrofs.unsigned so + 0) new_pc_v).
          * apply (global_repr_store_other_block hm cb co m m1 _
                     (ar_global_block ard) (ar_global_ofs ard)
                     sb (Ptrofs.unsigned so + 32) ea_val).
            exact Hglobal_repr. exact Hstore1.
            intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
          * exact Hstore2.
          * intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
        + exact Hstore3.
        + intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load3.
      - simpl. exact Htrap_rel. }

    (* 9. sb_writable *)
    { exact Hsb_writable_m3. }
  }
Qed.
