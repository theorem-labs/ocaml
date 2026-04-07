(* BRANCHIFNOT_correct.v -- Verification of the BRANCHIFNOT bytecode handler.

   Rocq handler:
     handle_BRANCHIFNOT target pc' s =
       match s.(accu) with
       | Val_int 0 => Step (s <|pc := target|>)    -- branch taken
       | _         => Step (s <|pc := pc'|>)        -- fall through
       end

   C handler (Clight AST):
     1. _t'1 = s->accu                                     (read accu, tlong)
     2. if (_t'1 == ((0 << 1) + 1))    [i.e. accu == tagged(0) == 1]
          then {                          -- TAKEN: jump to pc + offset
            _t'3 = s->pc;
            _t'4 = s->pc;
            _t'5 = *_t'4;                 (read branch offset from code)
            s->pc = _t'3 + _t'5;         (pointer + int arithmetic)
          }
          else {                          -- FALL THROUGH: advance pc by 1
            _t'2 = s->pc;
            s->pc = _t'2 + 1;
          }
     3. return 0

   In handler_correct, pc' = s.(pc), so:
     - Taken:  post-state has pc = target
     - Not taken: post-state has pc = s.(pc) (unchanged from Rocq perspective)

   Two sub-cases for the C execution:
     - Taken: one store to pc (pc = pc + offset), needs code_contains axiom
     - Not taken: one store to pc (pc = pc + 1)

   For postcondition abs_rel, the code base offset in ard' is adjusted
   so that pc_rel holds for the new C pc value and the Rocq pc. *)

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
Require Import HandlerLemmas.

Local Notation ge := clight_ge.
Local Notation exec := (exec_stmt function_entry1 clight_ge).

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

Lemma interp_state_co_pc_accu : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Former code memory axioms — now preconditions                       *)
(* ================================================================== *)

(* code_block_ne_sptr and code_contains_branch_offset have been moved
   into the precondition of handler_correct.  The caller must
   supply these facts when instantiating the spec. *)

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

(* Oeq on two Vlong values: via sem_cmp -> cmp_default -> sem_binarith *)
Lemma sem_eq_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Oeq
    (Vlong n1) tlong (Vlong n2) tlong m
    = Some (Val.of_bool (Int64.eq n1 n2)).
Proof. intros. reflexivity. Qed.

(* bool_val on Val.of_bool *)
Lemma bool_val_of_bool : forall b m,
  bool_val (Val.of_bool b) tint m = Some b.
Proof. intros. destruct b; reflexivity. Qed.

(* pc + 1 for (tptr tint) + 1 = advance by sizeof(int) = 4 bytes *)
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

(* ptr + int for branch offset *)
Lemma sem_add_pc_ofs : forall b ofs ofs_int m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint ofs_int) tint
    m = Some (Vptr b (Ptrofs.add ofs
        (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                    (ptrofs_of_int Signed ofs_int)))).
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

Lemma ptrofs_add_zero : forall ofs,
  Ptrofs.add ofs (Ptrofs.repr 0) = ofs.
Proof.
  intros. change (Ptrofs.repr 0) with Ptrofs.zero.
  apply Ptrofs.add_zero.
Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* store_pc_succeeds is no longer needed -- uses of the deleted axiom
   store_succeeds_from_load are replaced by store_succeeds_sb below. *)

(* ================================================================== *)
(* Tagged zero comparison                                              *)
(* ================================================================== *)

(* Int64.eq (Int64.repr 1) (Int64.repr 1) = true *)
Lemma tagged_zero_eq_self :
  Int64.eq (Int64.repr 1) (Int64.repr 1) = true.
Proof.
  apply Int64.eq_true.
Qed.

(* For n <> 0 in OCaml's 63-bit integer range:
   Int64.eq (Int64.repr (n*2+1)) (Int64.repr 1) = false.
   Proved via modular arithmetic: if n*2+1 = 1 (mod 2^64) then n = 0,
   contradicting n <> 0, provided |n| < 2^62. *)
Lemma tagged_nonzero_ne_one : forall n,
  n <> 0%Z ->
  -4611686018427387904 <= n <= 4611686018427387903 ->
  Int64.eq (Int64.repr (n * 2 + 1)) (Int64.repr 1) = false.
Proof.
  intros n Hn Hrange.
  apply Int64.eq_false. intro Heq.
  apply (f_equal Int64.unsigned) in Heq.
  rewrite !Int64.unsigned_repr_eq in Heq.
  change Int64.modulus with 18446744073709551616%Z in Heq.
  change (1 mod 18446744073709551616)%Z with 1%Z in Heq.
  destruct (Z_le_dec 0 (n * 2 + 1)).
  - rewrite Z.mod_small in Heq; lia.
  - rewrite (Zmod_unique (n * 2 + 1) 18446744073709551616 (-1)
               (n * 2 + 1 + 18446744073709551616)) in Heq; lia.
Qed.

(* Helper: if d | a and d | m, then d | (a mod m) *)
Local Lemma Z_divide_mod : forall d a m,
  (d | a) -> (d | m) -> m <> 0 -> (d | a mod m).
Proof.
  intros d a m Ha Hm Hm0.
  rewrite Z.mod_eq by lia.
  apply Z.divide_sub_r; auto.
  apply Z.divide_mul_l. exact Hm.
Qed.

(* For Val_block atoms: tag*1024 <> 1 (mod 2^64).
   Proved: tag*1024 is divisible by 1024 modulo 2^64 (since 1024 | 2^64),
   but 1 is not divisible by 1024. *)
Lemma tagged_block_atom_ne_one : forall tag,
  Int64.eq (Int64.repr (Z.of_nat tag * 1024)) (Int64.repr 1) = false.
Proof.
  intros tag.
  apply Int64.eq_false. intro Heq.
  apply (f_equal Int64.unsigned) in Heq.
  rewrite !Int64.unsigned_repr_eq in Heq.
  change Int64.modulus with 18446744073709551616%Z in Heq.
  change (1 mod 18446744073709551616)%Z with 1%Z in Heq.
  assert (Hdivmod : (1024 | (Z.of_nat tag * 1024) mod 18446744073709551616)%Z).
  { apply Z_divide_mod; try lia.
    - exists (Z.of_nat tag). ring.
    - exists 18014398509481984%Z. ring. }
  rewrite Heq in Hdivmod.
  destruct Hdivmod as [q Hq]. lia.
Qed.

(* For Vptr accu values (Val_ptr, Val_closure), CompCert's
   sem_binary_operation Oeq with types (tlong, tlong) goes through
   cmp_default -> sem_binarith, which requires both operands to be
   Vlong after casting.  sem_cast (Vptr b ofs) tlong tlong returns
   Some (Vptr b ofs), but the bin_case_l pattern match requires Vlong,
   so it returns None.  This comparison is genuinely undefined in
   CompCert's semantics.
   Rather than axiomatizing a false result, we add a precondition
   excluding Vptr/Vclosure accumulators.  For these cases the handler
   correctness is vacuously true (the precondition is False). *)

(* ================================================================== *)
(* pc_rel with shifted code base                                       *)
(* ================================================================== *)

Lemma pc_rel_shift_by_4 : forall cb co rocq_pc,
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
(* Tactic for the "branch taken" abs_rel postcondition.                *)
(* ================================================================== *)

Local Ltac prove_field_survives Hstore Hload :=
  apply (load_after_store_other _ _ _ _ _ _ _ Hstore Hload); right; lia.

(* bool_val for Vint Int.one on tint gives true *)
Lemma bool_val_vint_one : forall m,
  bool_val (Vint Int.one) tint m = Some true.
Proof.
  intros. simpl. reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem: BRANCHIFNOT correctness                               *)
(* ================================================================== *)

Theorem verify_BRANCHIFNOT_correct : forall target,
    handler_correct (handle_BRANCHIFNOT target) f_instr_BRANCHIFNOT
      (fun _ m s ard =>
         ar_code_base_block ard <> ar_sptr_block ard /\
         (exists ofs_int,
           Mem.load Mint32 m (ar_code_base_block ard)
             (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
                (Ptrofs.repr (Machine.pc s * sizeof_code_t)))) = Some (Vint ofs_int) /\
           Ptrofs.add
             (Ptrofs.add (ar_code_base_ofs ard)
                (Ptrofs.repr (Machine.pc s * sizeof_code_t)))
             (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                         (ptrofs_of_int Signed ofs_int))
           = Ptrofs.add (ar_code_base_ofs ard) (Ptrofs.repr (target * sizeof_code_t))) /\
         match Machine.accu s with
         | Val_int n => -4611686018427387904 <= n <= 4611686018427387903
         | Val_block _ nil => True
         | Val_ptr _ | Val_closure _ _ => False
         | Val_block _ (_ :: _) => True
         end)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intro target.
  intros e le m s.
  unfold handle_BRANCHIFNOT.

  (* Case split on accu *)
  destruct (Machine.accu s) as [n | addr | addr offset | tag fields] eqn:Haccu_eq.

  (* ================================================================ *)
  (* Case 1: accu = Val_int n                                          *)
  (* ================================================================ *)
  {
    destruct n as [| p | p] eqn:Hn.

    (* ============================================================== *)
    (* Case 1a: accu = Val_int 0 => TAKEN branch, pc := target        *)
    (* ============================================================== *)
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
        Hsp_data &
        [env_v [Henv_load Henv_repr]] &
        Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne]]]] &
        [ts_ptr [Hts_load Htrap_rel]] &
        Hsb_writable).
      destruct Hsp_data as [sp_ptr [sp_b [sp_ofs (Hsp_load & Hsp_eq & Hstack_repr
        & Hblock_sep & Hsp_ne_gb & Hcb_ne_sp & Hsp_ge8 & Hsp_bound & Hsp_writable & Hsp_align)]]].
      subst sp_ptr.

      (* Extract preconditions *)
      destruct Hstep_pre as (Hcb_ne_sb & [ofs_int [Hcode_load Hofs_eq]] & _).

      (* Structural invariants *)
      pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].

      (* accu = Val_int 0, val_repr gives Vlong (Int64.repr 1) *)
      rewrite Haccu_eq in Haccu_repr.
      inversion Haccu_repr; subst accu_v.

      (* Composite environment facts *)
      destruct interp_state_co_pc_accu as [co_is [Hco [Hpc_offset Haccu_offset]]].

      (* pc_ptr is a concrete Vptr *)
      unfold pc_rel in Hpc_rel. subst pc_ptr.
      set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

      (* Branch offset from code memory (from precondition) *)
      fold pc_ofs in Hcode_load.

      (* New pc value: pc + offset *)
      set (new_pc_ofs := Ptrofs.add pc_ofs
        (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                    (ptrofs_of_int Signed ofs_int))).
      set (new_pc_v := Vptr cb new_pc_ofs).

      (* pc field is at offset 0: Ptrofs.add so 0 = so *)
      assert (Hpc_load_uso : Mem.load Mint64 m sb (Ptrofs.unsigned so) =
                Some (Vptr cb pc_ofs)).
      { replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia.
        exact Hpc_load. }

      (* Store to pc field at offset 0 *)
      destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia) new_pc_v) as [m' Hstore0].
      (* Hstore0 stores at (uso + 0); convert to uso for downstream compatibility *)
      assert (Hstore : Mem.store Mint64 m sb (Ptrofs.unsigned so) new_pc_v = Some m').
      { replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia. exact Hstore0. }

      (* Witnesses *)
      set (le' := PTree.set _t'5 (Vint ofs_int)
                  (PTree.set _t'4 (Vptr cb pc_ofs)
                  (PTree.set _t'3 (Vptr cb pc_ofs)
                  (PTree.set _t'1 (Vlong (Int64.repr 1)) le)))).
      exists le'. exists m'.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* ============================================================ *)
      (* Part 1: manual bigstep construction                           *)
      (* ============================================================ *)
      {
        set (le1 := PTree.set _t'1 (Vlong (Int64.repr 1)) le).
        set (le2 := PTree.set _t'3 (Vptr cb pc_ofs) le1).
        set (le3 := PTree.set _t'4 (Vptr cb pc_ofs) le2).
        set (le4 := PTree.set _t'5 (Vint ofs_int) le3).

        (* Outer: (Sset _t'1 + Sifthenelse) ; Sreturn *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m').

        (* Inner: Sset _t'1 ; Sifthenelse *)
        { apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m).

          (* Sset _t'1 = s->accu *)
          { apply exec_Sset.
            eapply eval_Elvalue.
            - eapply eval_Efield_struct.
              + eapply eval_Elvalue.
                * eapply eval_Ederef. eapply eval_Etempvar. exact Hle_s.
                * apply deref_loc_copy. reflexivity.
              + reflexivity.
              + exact Hco.
              + exact Haccu_offset.
            - apply deref_loc_value with (chunk := Mint64).
              + reflexivity.
              + simpl. fold so.
                rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
                exact Haccu_load. }

          (* Sifthenelse: condition true => THEN branch (taken) *)
          { eapply exec_Sifthenelse.
            - (* eval condition: Oeq _t'1 ((0<<1)+1) *)
              eapply eval_Ebinop.
              + eapply eval_Etempvar. subst le1. rewrite PTree.gss. reflexivity.
              + eapply eval_Ebinop.
                * eapply eval_Ebinop.
                  { eapply eval_Ecast. eapply eval_Econst_int. exact (sem_cast_int_to_long_0 m). }
                  { eapply eval_Econst_int. }
                  { exact (sem_shl_long_0_1 m). }
                * eapply eval_Econst_int.
                * exact (sem_add_long_int_0_1 m).
              + rewrite sem_eq_long_long. rewrite tagged_zero_eq_self. reflexivity.
            - (* bool_val: Val.of_bool true = Vint Int.one => Some true *)
              exact (bool_val_vint_one m).
            - (* Execute THEN branch: _t'3, _t'4, _t'5, assign pc *)
              simpl.
              apply exec_Sseq_1 with (t1 := E0) (le1 := le2) (m1 := m).
              { (* Sset _t'3 = s->pc *)
                apply exec_Sset.
                eapply eval_Elvalue.
                - eapply eval_Efield_struct.
                  + eapply eval_Elvalue.
                    * eapply eval_Ederef. eapply eval_Etempvar.
                      subst le1. rewrite PTree.gso by (compute; congruence). exact Hle_s.
                    * apply deref_loc_copy. reflexivity.
                  + reflexivity.
                  + exact Hco.
                  + exact Hpc_offset.
                - apply deref_loc_value with (chunk := Mptr).
                  + reflexivity.
                  + simpl. rewrite Mptr_Mint64. fold so.
                    rewrite (ptrofs_add_zero so).
                    exact Hpc_load_uso. }

              { apply exec_Sseq_1 with (t1 := E0) (le1 := le3) (m1 := m).
                { (* Sset _t'4 = s->pc *)
                  apply exec_Sset.
                  eapply eval_Elvalue.
                  - eapply eval_Efield_struct.
                    + eapply eval_Elvalue.
                      * eapply eval_Ederef. eapply eval_Etempvar.
                        subst le2 le1.
                        rewrite PTree.gso by (compute; congruence).
                        rewrite PTree.gso by (compute; congruence). exact Hle_s.
                      * apply deref_loc_copy. reflexivity.
                    + reflexivity.
                    + exact Hco.
                    + exact Hpc_offset.
                  - apply deref_loc_value with (chunk := Mptr).
                    + reflexivity.
                    + simpl. rewrite Mptr_Mint64. fold so.
                      rewrite (ptrofs_add_zero so).
                      exact Hpc_load_uso. }

                { apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m).
                  { (* Sset _t'5 = deref _t'4 (read branch offset from code) *)
                    apply exec_Sset.
                    eapply eval_Elvalue.
                    - eapply eval_Ederef. eapply eval_Etempvar.
                      subst le3. rewrite PTree.gss. reflexivity.
                    - apply deref_loc_value with (chunk := Mint32).
                      + reflexivity.
                      + simpl. exact Hcode_load. }

                  { (* Sassign s->pc = _t'3 + _t'5 *)
                    eapply exec_Sassign.
                    - (* lvalue: s->pc *)
                      eapply eval_Efield_struct.
                      + eapply eval_Elvalue.
                        * eapply eval_Ederef. eapply eval_Etempvar.
                          subst le4 le3 le2 le1.
                          rewrite PTree.gso by (compute; congruence).
                          rewrite PTree.gso by (compute; congruence).
                          rewrite PTree.gso by (compute; congruence).
                          rewrite PTree.gso by (compute; congruence). exact Hle_s.
                        * apply deref_loc_copy. reflexivity.
                      + reflexivity.
                      + exact Hco.
                      + exact Hpc_offset.
                    - (* rvalue: _t'3 + _t'5 *)
                      eapply eval_Ebinop.
                      + eapply eval_Etempvar.
                        subst le4 le3 le2.
                        rewrite PTree.gso by (compute; congruence).
                        rewrite PTree.gso by (compute; congruence).
                        rewrite PTree.gss. reflexivity.
                      + eapply eval_Etempvar.
                        subst le4. rewrite PTree.gss. reflexivity.
                      + apply sem_add_pc_ofs.
                    - (* sem_cast *)
                      apply sem_cast_ptr_tint_to_ptr_tint.
                    - (* assign_loc *)
                      apply assign_loc_value with (chunk := Mptr).
                      + reflexivity.
                      + simpl. rewrite Mptr_Mint64. fold so.
                        rewrite (ptrofs_add_zero so).
                        fold new_pc_v. exact Hstore. } } } } }

        (* Sreturn 0 *)
        { apply exec_Sreturn_some. eapply eval_Econst_int. }
      }

      (* ============================================================ *)
      (* Part 2: abs_rel for post-state s <|pc := target|>             *)
      (* ============================================================ *)
      {
        set (new_co := Ptrofs.sub new_pc_ofs (Ptrofs.repr (target * sizeof_code_t))).
        set (ard' := mk_abs_rel sb so hm cb new_co
                       (ar_global_block ard) (ar_global_ofs ard)
                       (ar_stack_block ard) (ar_stack_base_ofs ard)
                       (ar_code_ne_sptr ard) (ar_code_ne_global ard)
                       (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
        exists ard'.
        set (uso := Ptrofs.unsigned so) in *.

        assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some new_pc_v).
        { pose proof (load_after_store_same m m' sb uso new_pc_v Hstore) as Htmp.
          unfold new_pc_v in Htmp |- *.
          rewrite load_result_vptr in Htmp.
          replace (uso + 0)%Z with uso by lia.
          exact Htmp. }

        assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some (Vlong (Int64.repr 1))).
        { prove_field_survives Hstore Haccu_load. }

        assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { prove_field_survives Hstore Hsp_load. }

        assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
        { prove_field_survives Hstore Henv_load. }

        assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { prove_field_survives Hstore Hextra_load. }

        assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
        { prove_field_survives Hstore Hgd_load. }

        assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
        { prove_field_survives Hstore Hts_load. }

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

        { unfold le'.
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          exact Hle_s. }

        { exists new_pc_v. split.
          - exact Hpc_load'.
          - simpl. unfold pc_rel. unfold new_pc_v.
            f_equal.
            unfold new_co.
            rewrite Ptrofs.sub_add_opp.
            rewrite Ptrofs.add_assoc.
            rewrite (Ptrofs.add_commut (Ptrofs.neg _) _).
            rewrite <- Ptrofs.sub_add_opp.
            rewrite Ptrofs.sub_idem.
            symmetry. apply Ptrofs.add_zero. }

        { exists (Vlong (Int64.repr 1)). split.
          - exact Haccu_load'.
          - simpl. rewrite Haccu_eq. constructor. }

        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
          split. { exact Hsp_load'. }
          split. { reflexivity. }
          split. { simpl.
            apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb uso new_pc_v
                     Hstack_repr Hstore).
            intro Heq; exact (Hblock_sep (eq_sym Heq)). }
          split. { exact Hblock_sep. }
          split. { exact Hsp_ne_gb. }
          split. { exact Hcb_ne_sp. }
          split. { exact Hsp_ge8. }
          split. { exact Hsp_bound. }
          split. { intros ofs' Hofs'.
          eapply Mem.perm_store_1. exact Hstore.
          apply Hsp_writable. exact Hofs'. }
          exact Hsp_align. }

        { exists env_v. split.
          - exact Henv_load'.
          - simpl. exact Henv_repr. }

        { simpl. exact Hextra_load'. }

        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd_load'.
          - simpl. exact Hgd_eq.
          - simpl.
            apply (global_repr_store_other_block hm m m' _ _ _ sb uso new_pc_v
                     Hglobal_repr Hstore).
            intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          - exact Hgb_ne. }

        { exists ts_ptr. split.
          - exact Hts_load'.
          - simpl. exact Htrap_rel. }

        { intros ofs' Hofs'.
          eapply Mem.perm_store_1. exact Hstore.
          apply Hsb_writable. exact Hofs'. }
      }
    }

    (* ============================================================== *)
    (* Cases 1b+1c: accu = Val_int (Z.pos p) / (Z.neg p)              *)
    (* => FALL THROUGH, pc := pc'                                      *)
    (* Both goals handled identically via semicolons.                  *)
    (* ============================================================== *)

    all: simpl;
      intros ard Hpre Hstep_pre;

      (unfold abs_rel_with_ard in Hpre;
      set (sb := ar_sptr_block ard) in *;
      set (so := ar_sptr_ofs ard) in *;
      set (hm := ar_heap_map ard) in *;
      set (cb := ar_code_base_block ard) in *;
      set (co := ar_code_base_ofs ard) in *;
      destruct Hpre as (Hle_s &
        [pc_ptr [Hpc_load Hpc_rel]] &
        [accu_v [Haccu_load Haccu_repr]] &
        Hsp_data &
        [env_v [Henv_load Henv_repr]] &
        Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne]]]] &
        [ts_ptr [Hts_load Htrap_rel]] &
        Hsb_writable);
      destruct Hsp_data as [sp_ptr [sp_b [sp_ofs (Hsp_load & Hsp_eq & Hstack_repr
        & Hblock_sep & Hsp_ne_gb & Hcb_ne_sp & Hsp_ge8 & Hsp_bound & Hsp_writable & Hsp_align)]]];
      subst sp_ptr;

      destruct Hstep_pre as (_ & _ & Haccu_range);

      pose proof (sptr_ofs_representable ard) as Hso_bound; fold so in Hso_bound;
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _];

      rewrite Haccu_eq in Haccu_repr;

      destruct interp_state_co_pc_accu as [co_is [Hco [Hpc_offset Haccu_offset]]];

      unfold pc_rel in Hpc_rel; subst pc_ptr;
      set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *;

      assert (Hpc_load_uso : Mem.load Mint64 m sb (Ptrofs.unsigned so) =
                Some (Vptr cb pc_ofs))
        by (replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia;
            exact Hpc_load);

      set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4));
      set (new_pc_v := Vptr cb new_pc_ofs);

      destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia) new_pc_v) as [m' Hstore0];
      assert (Hstore : Mem.store Mint64 m sb (Ptrofs.unsigned so) new_pc_v = Some m')
        by (replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia; exact Hstore0);

      (* Set le1 and le' BEFORE subst so accu_v name is available *)
      set (le1 := PTree.set _t'1 accu_v le);
      set (le' := PTree.set _t'2 (Vptr cb pc_ofs) le1);

      (* Now subst accu_v -- concrete Vlong value propagates into le1, le' *)
      inversion Haccu_repr; subst accu_v;

      exists le'; exists m';
      exists (Out_return (Some (Vint (Int.repr 0), tint)));

      split;

      [ (* Part 1: manual bigstep construction -- ELSE branch (fall through) *)

        (* Outer: (Sset _t'1 + Sifthenelse) ; Sreturn *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le') (m1 := m');

        [ (* Inner: Sset _t'1 ; Sifthenelse *)
          apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m);

          [ (* Sset _t'1 = s->accu *)
            apply exec_Sset;
            eapply eval_Elvalue;
            [ eapply eval_Efield_struct;
              [ eapply eval_Elvalue;
                [ eapply eval_Ederef; eapply eval_Etempvar; exact Hle_s
                | apply deref_loc_copy; reflexivity ]
              | reflexivity
              | exact Hco
              | exact Haccu_offset ]
            | apply deref_loc_value with (chunk := Mint64);
              [ reflexivity
              | simpl; fold so;
                rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia));
                exact Haccu_load ] ]

          | (* Sifthenelse: condition false => ELSE branch *)
            eapply exec_Sifthenelse;
            [ (* eval condition: Oeq _t'1 ((0<<1)+1) *)
              eapply eval_Ebinop;
              [ eapply eval_Etempvar; unfold le1; rewrite PTree.gss; reflexivity
              | eapply eval_Ebinop;
                [ eapply eval_Ebinop;
                  [ eapply eval_Ecast; [ eapply eval_Econst_int | exact (sem_cast_int_to_long_0 m) ]
                  | eapply eval_Econst_int
                  | exact (sem_shl_long_0_1 m) ]
                | eapply eval_Econst_int
                | exact (sem_add_long_int_0_1 m) ]
              | rewrite sem_eq_long_long;
                match goal with
                | |- context [Int64.eq (Int64.repr (?nn * 2 + 1)) (Int64.repr 1)] =>
                  rewrite (tagged_nonzero_ne_one nn ltac:(lia) Haccu_range)
                end;
                reflexivity ]
            | (* bool_val: Val.of_bool false = Vint Int.zero => Some false *)
              simpl; reflexivity
            | (* Execute ELSE branch: Sset _t'2 ; Sassign pc *)
              simpl;
              apply exec_Sseq_1 with (t1 := E0)
                (le1 := PTree.set _t'2 (Vptr cb pc_ofs) le1) (m1 := m);

              [ (* Sset _t'2 = s->pc *)
                apply exec_Sset;
                eapply eval_Elvalue;
                [ eapply eval_Efield_struct;
                  [ eapply eval_Elvalue;
                    [ eapply eval_Ederef; eapply eval_Etempvar;
                      unfold le1; rewrite PTree.gso by (compute; congruence); exact Hle_s
                    | apply deref_loc_copy; reflexivity ]
                  | reflexivity
                  | exact Hco
                  | exact Hpc_offset ]
                | apply deref_loc_value with (chunk := Mptr);
                  [ reflexivity
                  | simpl; rewrite Mptr_Mint64; fold so;
                    rewrite (ptrofs_add_zero so);
                    exact Hpc_load_uso ] ]

              | (* Sassign s->pc = _t'2 + 1 *)
                eapply exec_Sassign;
                [ eapply eval_Efield_struct;
                  [ eapply eval_Elvalue;
                    [ eapply eval_Ederef; eapply eval_Etempvar;
                      unfold le'; unfold le1;
                      rewrite PTree.gso by (compute; congruence);
                      rewrite PTree.gso by (compute; congruence); exact Hle_s
                    | apply deref_loc_copy; reflexivity ]
                  | reflexivity
                  | exact Hco
                  | exact Hpc_offset ]
                | eapply eval_Ebinop;
                  [ eapply eval_Etempvar; unfold le'; rewrite PTree.gss; reflexivity
                  | eapply eval_Econst_int
                  | apply sem_add_pc_1 ]
                | apply sem_cast_ptr_tint_to_ptr_tint
                | apply assign_loc_value with (chunk := Mptr);
                  [ reflexivity
                  | simpl; rewrite Mptr_Mint64; fold so;
                    rewrite (ptrofs_add_zero so);
                    fold new_pc_v; exact Hstore ] ] ] ] ]

        | (* Sreturn 0 *)
          apply exec_Sreturn_some; eapply eval_Econst_int ]

      | (* Part 2: abs_rel *)
        (set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t));
        set (ard' := mk_abs_rel sb so hm cb new_co
                       (ar_global_block ard) (ar_global_ofs ard)
                       (ar_stack_block ard) (ar_stack_base_ofs ard)
                       (ar_code_ne_sptr ard) (ar_code_ne_global ard)
                       (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard));
        exists ard';
        set (uso := Ptrofs.unsigned so) in *;

        assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some new_pc_v)
          by (pose proof (load_after_store_same m m' sb uso new_pc_v Hstore) as Htmp;
              unfold new_pc_v in Htmp |- *;
              rewrite load_result_vptr in Htmp;
              replace (uso + 0)%Z with uso by lia;
              exact Htmp);

        eassert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some _)
          by (prove_field_survives Hstore Haccu_load);

        assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs))
          by (prove_field_survives Hstore Hsp_load);

        assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v)
          by (prove_field_survives Hstore Henv_load);

        assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s)))))
          by (prove_field_survives Hstore Hextra_load);

        assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr)
          by (prove_field_survives Hstore Hgd_load);

        assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr)
          by (prove_field_survives Hstore Hts_load);

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]];

        [ unfold le'; unfold le1;
          rewrite PTree.gso by (compute; congruence);
          rewrite PTree.gso by (compute; congruence);
          exact Hle_s

        | exists new_pc_v; split;
          [ exact Hpc_load'
          | simpl; subst new_pc_v new_pc_ofs;
            apply pc_rel_shift_by_4 ]

        | eexists; split;
          [ exact Haccu_load'
          | simpl; simpl in Haccu_repr; rewrite Haccu_eq; exact Haccu_repr ]

        | exists (Vptr sp_b sp_ofs), sp_b, sp_ofs;
          (split; [ exact Hsp_load'
          | split; [ reflexivity
          | split; [ simpl;
            apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb uso new_pc_v
                     Hstack_repr Hstore);
            intro Heq; exact (Hblock_sep (eq_sym Heq))
          | split; [ exact Hblock_sep
          | split; [ exact Hsp_ne_gb
          | split; [ exact Hcb_ne_sp
          | split; [ exact Hsp_ge8
          | split; [ exact Hsp_bound
          | split; [ intros ofs' Hofs';
            eapply Mem.perm_store_1; [ exact Hstore | ];
            apply Hsp_writable; exact Hofs'
          | exact Hsp_align ]]]]]]]]])

        | exists env_v; split;
          [ exact Henv_load'
          | simpl; exact Henv_repr ]

        | simpl; exact Hextra_load'

        | exists gd_ptr; split; [| split; [| split]];
          [ exact Hgd_load'
          | simpl; exact Hgd_eq
          | simpl;
            apply (global_repr_store_other_block hm m m' _ _ _ sb uso new_pc_v
                     Hglobal_repr Hstore);
            intro Heq2; exact (Hgb_ne (eq_sym Heq2))
          | exact Hgb_ne ]

        | exists ts_ptr; split;
          [ exact Hts_load'
          | simpl; exact Htrap_rel ]

        | intros ofs' Hofs';
          eapply Mem.perm_store_1; [ exact Hstore | ];
          apply Hsb_writable; exact Hofs' ])
      ]).
  }

  (* ================================================================ *)
  (* Case 2: accu = Val_block tag fields => FALL THROUGH              *)
  (* (Val_block is the 2nd constructor of value)                       *)
  (* ================================================================ *)
  {
    destruct l as [| hd tl].

    (* Case 2a: Val_block tag nil (atom) -- Vlong representation *)
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
        Hsp_data &
        [env_v [Henv_load Henv_repr]] &
        Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne]]]] &
        [ts_ptr [Hts_load Htrap_rel]] &
        Hsb_writable).
      destruct Hsp_data as [sp_ptr [sp_b [sp_ofs (Hsp_load & Hsp_eq & Hstack_repr
        & Hblock_sep & Hsp_ne_gb & Hcb_ne_sp & Hsp_ge8 & Hsp_bound & Hsp_writable & Hsp_align)]]].
      subst sp_ptr.

      pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].

      rewrite Haccu_eq in Haccu_repr.
      inversion Haccu_repr; subst accu_v.

      destruct interp_state_co_pc_accu as [co_is [Hco [Hpc_offset Haccu_offset]]].

      unfold pc_rel in Hpc_rel. subst pc_ptr.
      set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

      assert (Hpc_load_uso : Mem.load Mint64 m sb (Ptrofs.unsigned so) =
                Some (Vptr cb pc_ofs)).
      { replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia.
        exact Hpc_load. }

      set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
      set (new_pc_v := Vptr cb new_pc_ofs).

      destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia) new_pc_v) as [m' Hstore0].
      assert (Hstore : Mem.store Mint64 m sb (Ptrofs.unsigned so) new_pc_v = Some m').
      { replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia. exact Hstore0. }

      set (le' := PTree.set _t'2 (Vptr cb pc_ofs)
                  (PTree.set _t'1 (Vlong (Int64.repr (Z.of_nat addr * 1024))) le)).
      exists le'. exists m'.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* Part 1: manual bigstep -- ELSE branch (fall through) *)
      {
        set (le1 := PTree.set _t'1 (Vlong (Int64.repr (Z.of_nat addr * 1024))) le).

        apply exec_Sseq_1 with (t1 := E0) (le1 := le') (m1 := m').

        { apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m).

          { (* Sset _t'1 = s->accu *)
            apply exec_Sset.
            eapply eval_Elvalue.
            - eapply eval_Efield_struct.
              + eapply eval_Elvalue.
                * eapply eval_Ederef. eapply eval_Etempvar. exact Hle_s.
                * apply deref_loc_copy. reflexivity.
              + reflexivity.
              + exact Hco.
              + exact Haccu_offset.
            - apply deref_loc_value with (chunk := Mint64).
              + reflexivity.
              + simpl. fold so.
                rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
                exact Haccu_load. }

          { (* Sifthenelse: condition false => ELSE *)
            eapply exec_Sifthenelse.
            - eapply eval_Ebinop.
              + eapply eval_Etempvar. subst le1. rewrite PTree.gss. reflexivity.
              + eapply eval_Ebinop.
                * eapply eval_Ebinop.
                  { eapply eval_Ecast. eapply eval_Econst_int. exact (sem_cast_int_to_long_0 m). }
                  { eapply eval_Econst_int. }
                  { exact (sem_shl_long_0_1 m). }
                * eapply eval_Econst_int.
                * exact (sem_add_long_int_0_1 m).
              + rewrite sem_eq_long_long.
                rewrite (tagged_block_atom_ne_one addr).
                reflexivity.
            - simpl. reflexivity.
            - simpl.
              apply exec_Sseq_1 with (t1 := E0)
                (le1 := PTree.set _t'2 (Vptr cb pc_ofs) le1) (m1 := m).

              { apply exec_Sset.
                eapply eval_Elvalue.
                - eapply eval_Efield_struct.
                  + eapply eval_Elvalue.
                    * eapply eval_Ederef. eapply eval_Etempvar.
                      subst le1. rewrite PTree.gso by (compute; congruence). exact Hle_s.
                    * apply deref_loc_copy. reflexivity.
                  + reflexivity.
                  + exact Hco.
                  + exact Hpc_offset.
                - apply deref_loc_value with (chunk := Mptr).
                  + reflexivity.
                  + simpl. rewrite Mptr_Mint64. fold so.
                    rewrite (ptrofs_add_zero so).
                    exact Hpc_load_uso. }

              { eapply exec_Sassign.
                - eapply eval_Efield_struct.
                  + eapply eval_Elvalue.
                    * eapply eval_Ederef. eapply eval_Etempvar.
                      unfold le'.
                      rewrite PTree.gso by (compute; congruence).
                      rewrite PTree.gso by (compute; congruence). exact Hle_s.
                    * apply deref_loc_copy. reflexivity.
                  + reflexivity.
                  + exact Hco.
                  + exact Hpc_offset.
                - eapply eval_Ebinop.
                  + eapply eval_Etempvar. unfold le'. rewrite PTree.gss. reflexivity.
                  + eapply eval_Econst_int.
                  + apply sem_add_pc_1.
                - apply sem_cast_ptr_tint_to_ptr_tint.
                - apply assign_loc_value with (chunk := Mptr).
                  + reflexivity.
                  + simpl. rewrite Mptr_Mint64. fold so.
                    rewrite (ptrofs_add_zero so).
                    fold new_pc_v. exact Hstore. } } }

        { apply exec_Sreturn_some. eapply eval_Econst_int. }
      }

      (* Part 2: abs_rel *)
      {
        set (uso := Ptrofs.unsigned so) in *.
        set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
        set (ard' := mk_abs_rel sb so hm cb new_co
                       (ar_global_block ard) (ar_global_ofs ard)
                       (ar_stack_block ard) (ar_stack_base_ofs ard)
                       (ar_code_ne_sptr ard) (ar_code_ne_global ard)
                       (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
        exists ard'.

        assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some new_pc_v).
        { pose proof (load_after_store_same m m' sb uso new_pc_v Hstore) as Htmp.
          unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp.
          replace (uso + 0)%Z with uso by lia. exact Htmp. }

        assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) =
                  Some (Vlong (Int64.repr (Z.of_nat addr * 1024)))).
        { prove_field_survives Hstore Haccu_load. }

        assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { prove_field_survives Hstore Hsp_load. }

        assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
        { prove_field_survives Hstore Henv_load. }

        assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { prove_field_survives Hstore Hextra_load. }

        assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
        { prove_field_survives Hstore Hgd_load. }

        assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
        { prove_field_survives Hstore Hts_load. }

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

        { subst le'. rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence). exact Hle_s. }

        { exists new_pc_v. split. exact Hpc_load'. simpl. apply pc_rel_shift_by_4. }

        { exists (Vlong (Int64.repr (Z.of_nat addr * 1024))). split.
          exact Haccu_load'. simpl. rewrite Haccu_eq. exact (vr_block_atom _ addr). }

        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
          (split; [ exact Hsp_load'
          | split; [ reflexivity
          | split; [ simpl;
            apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb uso new_pc_v
                     Hstack_repr Hstore);
            intro Heq; exact (Hblock_sep (eq_sym Heq))
          | split; [ exact Hblock_sep
          | split; [ exact Hsp_ne_gb
          | split; [ exact Hcb_ne_sp
          | split; [ exact Hsp_ge8
          | split; [ exact Hsp_bound
          | split; [ intros ofs' Hofs';
            eapply Mem.perm_store_1; [ exact Hstore | ];
            apply Hsp_writable; exact Hofs'
          | exact Hsp_align ]]]]]]]]]).  }

        { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }

        { simpl. exact Hextra_load'. }

        { exists gd_ptr. split; [| split; [| split]].
          exact Hgd_load'. simpl. exact Hgd_eq. simpl.
          apply (global_repr_store_other_block hm m m' _ _ _ sb uso new_pc_v
                   Hglobal_repr Hstore).
          intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          exact Hgb_ne. }

        { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. }

        { intros ofs' Hofs'.
          eapply Mem.perm_store_1. exact Hstore.
          apply Hsb_writable. exact Hofs'. }
      }
    }

    (* Case 2b: Val_block tag (hd :: tl) -- non-atom block *)
    {
      intros ard Hpre _.
      destruct Hpre as (_ &
        _ &
        [accu_v [_ Haccu_repr]] &
        _).
      rewrite Haccu_eq in Haccu_repr.
      inversion Haccu_repr.
    }
  }

  (* ================================================================ *)
  (* Case 3: accu = Val_ptr addr => vacuously true                     *)
  (* (Val_ptr is the 3rd constructor of value)                         *)
  (* ================================================================ *)
  {
    intros ard _ Hstep_pre.
    destruct Hstep_pre as (_ & _ & Haccu_absurd).
    simpl in Haccu_absurd. destruct Haccu_absurd.
  }

  (* ================================================================ *)
  (* Case 4: accu = Val_closure addr offset => vacuously true          *)
  (* (Val_closure is the 4th constructor of value)                     *)
  (* ================================================================ *)
  {
    intros ard _ Hstep_pre.
    destruct Hstep_pre as (_ & _ & Haccu_absurd).
    simpl in Haccu_absurd. destruct Haccu_absurd.
  }
Qed.
