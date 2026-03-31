(* POP_correct.v -- POP handler completeness proof.

   POP n: drops n elements from the stack.

   C code (f_instr_POP):
     _t'1 = s->pc;             // read pc pointer (points to n in code buffer)
     s->pc = _t'1 + 1;         // advance pc past argument
     _t'2 = s->sp;             // read sp pointer
     _t'3 = *_t'1;             // read n from code buffer (Mint32)
     s->sp = _t'2 + _t'3;     // sp += n (pointer arithmetic: each elem = 8 bytes)
     return 0;

   Rocq:
     handle_POP n pc' s = Step (s <|pc := pc'|> <|stack := skipn n s.(stack)|>)

   Two stores: pc field at offset +0, sp field at offset +16.

   Uses handler_correct_with_pre because the C code reads n from the
   code buffer and because the code block must be separate from the
   struct block (for store separation).  NO AXIOMS -- everything is
   either proved or expressed as a precondition. *)

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
(* Struct layout: _pc at offset 0, _sp at offset 16                    *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full).
Proof.
  eexists. split; [| split]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_pc_sp : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full).
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

Lemma sem_cast_ptr_tlong_to_ptr_tlong : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tlong) (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

Lemma ptrofs_add_zero : forall ofs,
  Ptrofs.add ofs (Ptrofs.repr 0) = ofs.
Proof.
  intros. change (Ptrofs.repr 0) with Ptrofs.zero.
  apply Ptrofs.add_zero.
Qed.

(* ================================================================== *)
(* pc_rel with shifted code base                                       *)
(* ================================================================== *)

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
(* stack_repr_skipn: dropping n elements from the front of a stack     *)
(* shifts the stack pointer by n * 8 bytes.                            *)
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

Lemma stack_repr_skipn : forall n hm m stk sp_b sp_ofs,
  stack_repr hm m stk sp_b sp_ofs ->
  stack_repr hm m (skipn n stk) sp_b
    (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat n * 8))).
Proof.
  induction n as [| n' IH]; intros hm m stk sp_b sp_ofs Hsr.
  - (* n = 0: skipn 0 stk = stk, offset + 0 = offset *)
    simpl. rewrite ptrofs_add_zero. exact Hsr.
  - (* n = S n': skipn (S n') stk = skipn n' (tl stk) *)
    destruct stk as [| v vs].
    + (* stk = nil: skipn (S n') [] = [] *)
      simpl. constructor.
    + (* stk = v :: vs: skipn (S n') (v :: vs) = skipn n' vs *)
      simpl skipn. inversion Hsr; subst.
      (* vs has stack_repr at Ptrofs.add sp_ofs (Ptrofs.repr 8) *)
      specialize (IH hm m vs sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) H5).
      (* Show the two offsets are equal *)
      replace (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat (S n') * 8)))
        with (Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr (Z.of_nat n' * 8))).
      { exact IH. }
      { rewrite Ptrofs.add_assoc. f_equal.
        rewrite ptrofs_add_repr.
        f_equal. lia. }
Qed.

(* ================================================================== *)
(* Arithmetic: ptrofs_mul_8_of_ints                                    *)
(* Relates pointer arithmetic sp + n (C) to sp + n*8 (logical).       *)
(* When the C code does (tptr tlong) + (tint)n, CompCert computes     *)
(* sp + mul(8, ptrofs_of_int Signed (Int.repr n)).                    *)
(* We show this equals sp + repr(n * 8) when 0 <= n.                  *)
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

Theorem verify_POP_correct : forall n,
    handler_correct_with_pre (handle_POP n) f_instr_POP
      (fun m s ard =>
         (* The code buffer contains Int.repr n at the current PC position *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* The code block is separate from the struct block *)
         ar_code_base_block ard <> ar_sptr_block ard /\
         (* n fits in the signed int32 range *)
         Z.of_nat n < Int.half_modulus /\
         (* sp + n*8 fits in ptrofs range (needed for pointer arithmetic) *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs + Z.of_nat n * 8 < Ptrofs.modulus))
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).
Proof.
  intro n.
  intros e le m s.
  unfold handler_correct_with_pre, handle_POP. simpl.

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
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq Hstack_repr]]]]] &
    [env_v [Henv_load Henv_repr]] &
    Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq Hglobal_repr]]] &
    [ts_ptr [Hts_load Htrap_rel]]).
  subst sp_ptr.

  destruct Hstep_pre as (Hcode_load & Hcb_ne & Hn_bound & Hsp_fits).

  (* Structural invariants *)
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep. fold sb in Hblock_sep.
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  pose proof (sp_block_ne_global ard sp_b) as Hsp_ne_gb.

  (* Composite environment *)
  destruct interp_state_co_pc_sp as [co_is [Hco [Hpc_offset Hsp_offset]]].

  (* pc_ptr is a concrete Vptr *)
  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* New PC after advancement *)
  set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
  set (new_pc_v := Vptr cb new_pc_ofs).

  (* New SP after popping n elements: sp + n*8 *)
  set (new_sp_ofs := Ptrofs.add sp_ofs
         (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat n))))).

  (* sp_fits for our concrete sp_ofs *)
  assert (Hsp_fits_concrete : Ptrofs.unsigned sp_ofs + Z.of_nat n * 8 < Ptrofs.modulus).
  { apply (Hsp_fits sp_b sp_ofs). exact Hsp_load. }

  (* The ptrofs mul simplification *)
  assert (Hnew_sp_eq : new_sp_ofs = Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat n * 8))).
  { unfold new_sp_ofs.
    f_equal.
    apply ptrofs_mul_8_of_ints_eq.
    - lia.
    - exact Hn_bound. }

  (* Hpc_load without the + 0 *)
  assert (Hpc_load_uso : Mem.load Mint64 m sb (Ptrofs.unsigned so) =
            Some (Vptr cb pc_ofs)).
  { replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia.
    exact Hpc_load. }

  (* Store 1: pc field at (sb, uso+0) <- new_pc_v *)
  destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 0)
              (Vptr cb pc_ofs) new_pc_v Hpc_load)
    as [m1 Hstore_pc].

  (* sp field in m1: unaffected by store at offset 0 *)
  assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b sp_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 16) new_pc_v (Vptr sp_b sp_ofs)
             Hstore_pc Hsp_load). right. lia. }

  (* Store 2: sp field at (sb, uso+16) <- Vptr sp_b new_sp_ofs *)
  destruct (store_succeeds_from_load m1 sb (Ptrofs.unsigned so + 16)
              (Vptr sp_b sp_ofs) (Vptr sp_b new_sp_ofs) Hsp_load_m1)
    as [m2 Hstore_sp].

  (* Witnesses *)
  set (le' := PTree.set _t'3 (Vint (Int.repr (Z.of_nat n)))
              (PTree.set _t'2 (Vptr sp_b sp_ofs)
              (PTree.set _t'1 (Vptr cb pc_ofs) le))).
  exists le'. exists m2.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ============================================================== *)
  (* Part 1: exec via computational evaluator                        *)
  (* ============================================================== *)
  {
    apply (eval_stmt_to_exec clight_ge 15).
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

    (* S3: Sset _t'2 (s->sp) -- read sp pointer from struct.
       After S1's rewrite Hco, eval_cbn resolves the composite lookup.
       After S1's rewrite Hpc_offset, field_offset for _pc is known.
       But field_offset for _sp needs a separate rewrite. *)
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m1; eval_cbn.

    (* S4: Sset _t'3 (deref _t'1) -- read n from code buffer *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
              Some (Vint (Int.repr (Z.of_nat n)))).
    { erewrite Mem.load_store_other.
      - exact Hcode_load.
      - exact Hstore_pc.
      - left. exact Hcb_ne. }
    rewrite Hcode_load_m1; eval_cbn.

    (* S5: Sassign (s->sp) (_t'2 + _t'3) -- sp += n *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    (* Rvalue: _t'2 + _t'3 *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_sp_n sp_b sp_ofs (Int.repr (Z.of_nat n)) m1); eval_cbn.
    rewrite (sem_cast_ptr_tlong_to_ptr_tlong sp_b new_sp_ofs); eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hstore_sp; eval_cbn.

    (* S6: Sreturn 0 *)
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
                   (ar_stack_block ard) (ar_stack_base_ofs ard)).
    exists ard'.

    set (uso := Ptrofs.unsigned so) in *.

    (* Helper: loads on sb survive store 2 at offset +16 when at other offsets *)
    (* pc field at uso+0: written by store1, unaffected by store2 *)
    assert (Hpc_load2 : Mem.load Mint64 m2 sb (uso + 0) = Some new_pc_v).
    { assert (Hpc_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some new_pc_v).
      { pose proof (load_after_store_same m m1 sb (uso + 0) new_pc_v Hstore_pc) as Htmp.
        unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }
      apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 0)
               (Vptr sp_b new_sp_ofs) new_pc_v Hstore_sp Hpc_m1).
      left. lia. }

    (* accu field at uso+8: unaffected by both stores *)
    assert (Haccu_load2 : Mem.load Mint64 m2 sb (uso + 8) = Some accu_v).
    { assert (Haccu_m1 : Mem.load Mint64 m1 sb (uso + 8) = Some accu_v).
      { apply (load_after_store_other m m1 sb (uso + 0) (uso + 8)
                 new_pc_v accu_v Hstore_pc Haccu_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 8)
               (Vptr sp_b new_sp_ofs) accu_v Hstore_sp Haccu_m1).
      left. lia. }

    (* sp field at uso+16: written by store2 *)
    assert (Hsp_load2 : Mem.load Mint64 m2 sb (uso + 16) =
              Some (Vptr sp_b new_sp_ofs)).
    { pose proof (load_after_store_same m1 m2 sb (uso + 16)
                    (Vptr sp_b new_sp_ofs) Hstore_sp) as Htmp.
      rewrite load_result_vptr in Htmp. exact Htmp. }

    (* env field at uso+24: unaffected by both stores *)
    assert (Henv_load2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
    { assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m1 sb (uso + 0) (uso + 24)
                 new_pc_v env_v Hstore_pc Henv_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 24)
               (Vptr sp_b new_sp_ofs) env_v Hstore_sp Henv_m1).
      right. lia. }

    (* extra_args field at uso+32: unaffected *)
    assert (Hextra_load2 : Mem.load Mint64 m2 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { assert (Hextra_m1 : Mem.load Mint64 m1 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m1 sb (uso + 0) (uso + 32)
                 new_pc_v _ Hstore_pc Hextra_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 32)
               (Vptr sp_b new_sp_ofs) _ Hstore_sp Hextra_m1).
      right. lia. }

    (* global_data field at uso+40: unaffected *)
    assert (Hgd_load2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
    { assert (Hgd_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m1 sb (uso + 0) (uso + 40)
                 new_pc_v gd_ptr Hstore_pc Hgd_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 40)
               (Vptr sp_b new_sp_ofs) gd_ptr Hstore_sp Hgd_m1).
      right. lia. }

    (* trap_sp field at uso+48: unaffected *)
    assert (Hts_load2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
    { assert (Hts_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (uso + 0) (uso + 48)
                 new_pc_v ts_ptr Hstore_pc Hts_load). right. lia. }
      apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 48)
               (Vptr sp_b new_sp_ofs) ts_ptr Hstore_sp Hts_m1).
      right. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].

    (* 1. _s is in le' *)
    { subst le'.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      exact Hle_s. }

    (* 2. pc field -- updated to new_pc_v *)
    { exists new_pc_v. split.
      - exact Hpc_load2.
      - simpl. subst new_pc_v new_pc_ofs.
        apply pc_rel_shift. }

    (* 3. accu field -- unchanged *)
    { exists accu_v. split.
      - exact Haccu_load2.
      - simpl. exact Haccu_repr. }

    (* 4. sp field -- updated; stack is skipn n *)
    { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
      split; [| split].
      - exact Hsp_load2.
      - reflexivity.
      - simpl.
        (* We need: stack_repr hm m2 (skipn n (stack s)) sp_b new_sp_ofs *)
        (* new_sp_ofs = sp_ofs + n*8 by Hnew_sp_eq *)
        rewrite Hnew_sp_eq.
        (* stack_repr in m is preserved through stores on sb (different block) *)
        assert (Hstack_m1 : stack_repr hm m1 (Machine.stack s) sp_b sp_ofs).
        { apply (stack_repr_store_other_block hm m m1 _ sp_b sp_ofs sb
                   (uso + 0) new_pc_v Hstack_repr Hstore_pc).
          intro Heq; exact (Hblock_sep (eq_sym Heq)). }
        assert (Hstack_m2 : stack_repr hm m2 (Machine.stack s) sp_b sp_ofs).
        { apply (stack_repr_store_other_block hm m1 m2 _ sp_b sp_ofs sb
                   (uso + 16) (Vptr sp_b new_sp_ofs) Hstack_m1 Hstore_sp).
          intro Heq; exact (Hblock_sep (eq_sym Heq)). }
        (* Now apply stack_repr_skipn *)
        exact (stack_repr_skipn n hm m2 (Machine.stack s) sp_b sp_ofs Hstack_m2). }

    (* 5. env field -- unchanged *)
    { exists env_v. split.
      - exact Henv_load2.
      - simpl. exact Henv_repr. }

    (* 6. extra_args field -- unchanged *)
    { simpl. exact Hextra_load2. }

    (* 7. global_data field -- unchanged *)
    { exists gd_ptr. split; [| split].
      - exact Hgd_load2.
      - simpl. exact Hgd_eq.
      - simpl.
        apply (global_repr_store_other_block hm m1 m2 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (uso + 16) (Vptr sp_b new_sp_ofs)).
        + apply (global_repr_store_other_block hm m m1 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sb (uso + 0) new_pc_v
                   Hglobal_repr Hstore_pc).
          intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        + exact Hstore_sp.
        + intro Heq2; exact (Hgb_ne (eq_sym Heq2)). }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load2.
      - simpl. exact Htrap_rel. }
  }
Qed.
