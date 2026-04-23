(* ENVACC_correct.v -- ENVACC (parameterized) handler completeness proof.

   ENVACC n: reads index n from the code buffer, then reads env[n]
   from the closure environment, stores to accu, and advances pc past
   the argument.

   C code (f_instr_ENVACC):
     _t'1 = s->pc;             // read pc pointer (points to n in code buffer)
     s->pc = _t'1 + 1;         // advance pc past argument
     _t'2 = s->env;            // read env (tlong, really a pointer)
     _t'3 = *_t'1;             // read n from code buffer (Mint32)
     _t'4 = *(cast(_t'2, tptr tlong) + _t'3);  // env[n] (pointer arith)
     s->accu = _t'4;           // store to accu
     return 0;

   Rocq:
     handle_ENVACC n pc' s =
       match field_or_heap s s.(env) n with
       | Some v => Step (s <|pc := pc'|> <|accu := v|>)
       | None => Error "ENVACC: env access out of bounds"
       end

   Two stores: pc field at offset +0, accu field at offset +8.

   Combines the ACC code-buffer-read pattern with ENVACC1's
   env field access pattern, generalized over n.

   NO AXIOMS.  All structural/range constraints are preconditions
   via handler_correct_v1. *)

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

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout: _pc at offset 0, _env at offset 24, _accu at offset 8 *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_pc_env_accu : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full) /\
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

Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* env_ptr + n : pointer arithmetic on (tptr tlong), where n is tint.
   sizeof(tlong) = 8, so env_ptr + n = env_ptr + n * 8 bytes. *)
Lemma sem_add_env_n : forall env_b env_ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr env_b env_ofs) (tptr tlong)
    (Vint n) tint
    m = Some (Vptr env_b (Ptrofs.add env_ofs
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
(* ptrofs_mul_8_of_ints_eq: relate C pointer arithmetic to logical    *)
(* ================================================================== *)

Lemma ptrofs_max_unsigned_large : (Ptrofs.max_unsigned >= 2^32)%Z.
Proof. vm_compute. discriminate. Qed.

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

Theorem verify_ENVACC_correct : forall n,
    Z.of_nat n < Int.half_modulus ->
    handler_correct_v1 (handle_ENVACC n) f_instr_ENVACC
      (fun e m s ard =>
         (* The code buffer contains Int.repr (Z.of_nat n) at the current PC position *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* env field n is loadable in C memory *)
         env_field_loadable n e m s ard)
      (fun _ _ => True)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros n Hn_range.
  intros e le m s.
  unfold handler_correct_v1, handle_ENVACC.
  (* Resolve the well-formedness guard using the range hypothesis *)
  replace (Z.of_nat n <? Int.half_modulus)%Z with true
    by (symmetry; apply Z.ltb_lt; lia).

  (* Case split on field_or_heap *)
  destruct (field_or_heap s s.(Machine.env) n) as [v|] eqn:Hfoh.

  (* ================================================================ *)
  (* Case 2: field_or_heap env n = None => Error (trivially True)      *)
  (* ================================================================ *)
  2: { exact I. }

  (* ================================================================ *)
  (* Case 1: field_or_heap env n = Some v => Step                      *)
  (* ================================================================ *)
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

    destruct Hstep_pre as (Hcode_load & Hefl).
    pose proof Hn_range as Hn_bound.

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
    pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

    (* Composite environment: _pc@0, _env@24, _accu@8 *)
    destruct interp_state_co_pc_env_accu as [co_is [Hco [Hpc_offset [Henv_offset Haccu_offset]]]].

    (* pc_ptr is a concrete Vptr *)
    unfold pc_rel in Hpc_rel. subst pc_ptr.
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

    (* Use heap precondition to get the field value in C memory *)
    unfold env_field_loadable in Hefl.
    destruct (Hefl v Hfoh env_v Henv_repr)
      as [env_b [env_ofs [cv [Henv_is_ptr [Henv_b_ne_sb [Hfield_load Hfield_repr]]]]]].
    subst env_v.

    (* The ptrofs mul simplification *)
    assert (Henv_n_eq :
      Ptrofs.add env_ofs (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat n))))
      = Ptrofs.add env_ofs (Ptrofs.repr (Z.of_nat n * 8))).
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

    (* env field in m1: unaffected by store at offset 0 *)
    assert (Henv_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) =
              Some (Vptr env_b env_ofs)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
               (Ptrofs.unsigned so + 24) new_pc_v (Vptr env_b env_ofs)
               Hstore_pc Henv_load). right. lia. }

    (* Code buffer load survives store1 (different block: cb <> sb) *)
    assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
              Some (Vint (Int.repr (Z.of_nat n)))).
    { apply (code_buffer_load_at Mint32 Mint64 m m1 cb sb
               (Ptrofs.unsigned pc_ofs) (Ptrofs.unsigned so + 0)
               (Vint (Int.repr (Z.of_nat n))) new_pc_v
               Hcode_load Hstore_pc Hcb_ne). }

    (* Env field load survives store1 (different block: env_b <> sb) *)
    assert (Hfield_load_m1 : Mem.load Mint64 m1 env_b
              (Ptrofs.unsigned (Ptrofs.add env_ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some cv).
    { erewrite Mem.load_store_other.
      - exact Hfield_load.
      - exact Hstore_pc.
      - left. exact Henv_b_ne_sb. }

    (* Store 2: accu field at (sb, uso+8) <- cv *)
    destruct (store_succeeds_sb m1 sb so 8 accu_v Hsb_writable_m1 Haccu_load_m1 ltac:(lia) ltac:(lia) cv)
      as [m2 Hstore_accu].

    (* Witnesses *)
    set (le' := PTree.set _t'4 cv
                (PTree.set _t'3 (Vint (Int.repr (Z.of_nat n)))
                (PTree.set _t'2 (Vptr env_b env_ofs)
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

      (* S3: Sset _t'2 (s->env) -- read env field *)
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Henv_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
      rewrite Henv_load_m1; eval_cbn.

      (* S4: Sset _t'3 (deref _t'1) -- read n from code buffer *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite Hcode_load_m1; eval_cbn.

      (* S5: Sset _t'4 (deref (cast(_t'2, tptr tlong) + _t'3)) -- env[n] *)
      (* Evaluate Ecast (Etempvar _t'2 tlong) (tptr tlong): _t'2 skip _t'3 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      (* Cast: tlong -> (tptr tlong) for Vptr *)
      rewrite (sem_cast_long_to_ptr_vptr env_b env_ofs m1); eval_cbn.
      (* Evaluate Etempvar _t'3 tint: top of env *)
      rewrite PTree.gss; eval_cbn.
      (* Add: ptr + n = ptr + n * 8 bytes *)
      rewrite (sem_add_env_n env_b env_ofs (Int.repr (Z.of_nat n)) m1); eval_cbn.
      (* Simplify ptrofs mul *)
      rewrite Henv_n_eq.
      (* Deref: load field n from heap block *)
      rewrite Hfield_load_m1; eval_cbn.

      (* S6: Sassign (s->accu = _t'4) -- store to accu *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Haccu_offset; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hfield_repr); eval_cbn.
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
        rewrite (val_repr_load_result hm cb co v cv Hfield_repr) in Htmp.
        exact Htmp. }

      (* sp field at uso+16: unaffected by both stores *)
      assert (Hsp_load2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m1 sb (uso + 0) (uso + 16)
                   new_pc_v (Vptr sp_b sp_ofs) Hstore_pc Hsp_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 16)
                 cv (Vptr sp_b sp_ofs) Hstore_accu Hsp_m1).
        right. lia. }

      (* env field at uso+24: unaffected by both stores *)
      assert (Henv_load2 : Mem.load Mint64 m2 sb (uso + 24) = Some (Vptr env_b env_ofs)).
      { assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some (Vptr env_b env_ofs)).
        { apply (load_after_store_other m m1 sb (uso + 0) (uso + 24)
                   new_pc_v (Vptr env_b env_ofs) Hstore_pc Henv_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 24)
                 cv (Vptr env_b env_ofs) Hstore_accu Henv_m1).
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

      (* 3. accu field -- updated to env field value *)
      { exists cv. split.
        - exact Haccu_load2.
        - simpl. eapply val_repr_co_shift. exact Hfield_repr. }

      (* 4. sp field -- unchanged *)
      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load2.
        - reflexivity.
        - simpl.
          eapply stack_repr_co_shift.
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
      { exists (Vptr env_b env_ofs). split.
        - exact Henv_load2.
        - simpl. eapply val_repr_co_shift. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { simpl. exact Hextra_load2. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load2.
        - simpl. exact Hgd_eq.
        - simpl.
          eapply global_repr_co_shift.
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

Definition ENVACC_correct_for_spec : forall n, Z.of_nat n < Int.half_modulus ->
    handler_correct_v1 (handle_ENVACC n) f_instr_ENVACC
      (code_at (Int.repr (Z.of_nat n)) /\p env_field_loadable n)
      (fun _ _ => True)
      (fun _ => False) (fun _ _ _ => False).
  Proof.
    intros n Hrange.
    eapply handler_correct_v1_weaken.
    - exact (verify_ENVACC_correct n Hrange).
    - intros e le m s ard _ [Hcode Henv]. exact (conj Hcode Henv).
  Qed.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr (ENVACC n) / clight_of (ENVACC n) / pre_of (ENVACC n) are
   convertible with handle_ENVACC n / f_instr_ENVACC /
   (code_at (Int.repr (Z.of_nat n)) /\p env_field_loadable n).
   P_halt_of and P_ccall_of are vacuously satisfied (ENVACC never halts or
   issues a C call).  error_message_of is tautological on the Error branch. *)
Theorem correct_ENVACC : forall n,
    handler_correct (handle_instr (Bytecode.AST.ENVACC n)) (clight_of (Bytecode.AST.ENVACC n))
      (error_message_of (Bytecode.AST.ENVACC n))
      (pre_of (Bytecode.AST.ENVACC n)) (P_halt_of (Bytecode.AST.ENVACC n)) (P_ccall_of (Bytecode.AST.ENVACC n)).
Proof.
Admitted.

