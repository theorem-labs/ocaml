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
   into the precondition of handler_correct_with_pre.  The caller must
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

Lemma store_pc_succeeds : forall m sb so v_new,
  (exists v_old, Mem.load Mint64 m sb so = Some v_old) ->
  exists m', Mem.store Mint64 m sb so v_new = Some m'.
Proof.
  intros m sb so v_new [v_old Hload].
  exact (store_succeeds_from_load m sb so v_old v_new Hload).
Qed.

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
(* Main theorem: BRANCHIFNOT correctness                               *)
(* ================================================================== *)

Theorem verify_BRANCHIFNOT_correct : forall target,
    handler_correct_with_pre (handle_BRANCHIFNOT target) f_instr_BRANCHIFNOT
      (fun m s ard =>
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
      set (sb := ar_sptr_block ard) in *.
      set (so := ar_sptr_ofs ard) in *.
      set (hm := ar_heap_map ard) in *.
      set (cb := ar_code_base_block ard) in *.
      set (co := ar_code_base_ofs ard) in *.
      destruct Hpre as (Hle_s &
        [pc_ptr [Hpc_load Hpc_rel]] &
        [accu_v [Haccu_load Haccu_repr]] &
        [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hblock_sep [Hsp_ne_gb Hcb_ne_sp]]]]]]]] &
        [env_v [Henv_load Henv_repr]] &
        Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne]]]] &
        [ts_ptr [Hts_load Htrap_rel]]).
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

      (* Store to pc field *)
      destruct (store_pc_succeeds m sb (Ptrofs.unsigned so) new_pc_v
                  (ex_intro _ _ Hpc_load_uso)) as [m' Hstore].

      (* Witnesses *)
      set (le' := PTree.set _t'5 (Vint ofs_int)
                  (PTree.set _t'4 (Vptr cb pc_ofs)
                  (PTree.set _t'3 (Vptr cb pc_ofs)
                  (PTree.set _t'1 (Vlong (Int64.repr 1)) le)))).
      exists le'. exists m'.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* ============================================================ *)
      (* Part 1: exec via computational evaluator                      *)
      (* ============================================================ *)
      {
        apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.

        (* S1: _t'1 = s->accu *)
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_load; eval_cbn.

        (* Condition: Oeq _t'1 ((0<<1)+1) *)
        rewrite PTree.gss; eval_cbn.
        (* tagged zero: ((cast 0 tlong) << 1) + 1 = Vlong(1) *)
        rewrite (sem_cast_int_to_long_0 m); eval_cbn.
        rewrite (sem_shl_long_0_1 m); eval_cbn.
        rewrite (sem_add_long_int_0_1 m); eval_cbn.
        (* Oeq (Vlong 1) tlong (Vlong 1) tlong = Val.of_bool true *)
        rewrite sem_eq_long_long; eval_cbn.
        rewrite tagged_zero_eq_self; eval_cbn.

        (* TRUE branch: taken *)
        (* _t'3 = s->pc *)
        rewrite PTree.gso by (simpl; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_zero so).
        rewrite Hpc_load_uso; eval_cbn.

        (* _t'4 = s->pc *)
        rewrite PTree.gso by (simpl; congruence).
        rewrite PTree.gso by (simpl; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_zero so).
        rewrite Hpc_load_uso; eval_cbn.

        (* _t'5 = *_t'4 -- dereference pc to read branch offset *)
        rewrite PTree.gss; eval_cbn.
        rewrite Hcode_load; eval_cbn.

        (* Sassign s->pc = _t'3 + _t'5 *)
        (* Lvalue: s->pc *)
        rewrite PTree.gso by (simpl; congruence).
        rewrite PTree.gso by (simpl; congruence).
        rewrite PTree.gso by (simpl; congruence).
        rewrite PTree.gso by (simpl; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.

        (* Rvalue: _t'3 + _t'5 *)
        rewrite PTree.gso by (simpl; congruence).
        rewrite PTree.gso by (simpl; congruence).
        rewrite PTree.gss; eval_cbn.
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_pc_ofs cb pc_ofs ofs_int m); eval_cbn.
        rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.

        (* Store *)
        rewrite (ptrofs_add_zero so).
        fold new_pc_v.
        rewrite Hstore; eval_cbn.

        (* return 0 *)
        subst le'. reflexivity.
      }

      (* ============================================================ *)
      (* Part 2: abs_rel for post-state s <|pc := target|>             *)
      (* ============================================================ *)
      {
        set (uso := Ptrofs.unsigned so) in *.

        (* Construct new ard' with adjusted code base offset *)
        set (ard' := mk_abs_rel sb so hm cb
                       (Ptrofs.sub new_pc_ofs (Ptrofs.repr (target * sizeof_code_t)))
                       (ar_global_block ard) (ar_global_ofs ard)
                       (ar_stack_block ard) (ar_stack_base_ofs ard)).
        exists ard'.

        (* pc field: written by store *)
        assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some new_pc_v).
        { pose proof (load_after_store_same m m' sb uso new_pc_v Hstore) as Htmp.
          unfold new_pc_v in Htmp |- *.
          rewrite load_result_vptr in Htmp.
          replace (uso + 0)%Z with uso by lia.
          exact Htmp. }

        (* Other fields: unaffected by pc store at uso *)
        assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some (Vlong (Int64.repr 1))).
        { apply (load_after_store_other m m' sb uso (uso + 8) new_pc_v
                   (Vlong (Int64.repr 1)) Hstore Haccu_load). right. lia. }

        assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m' sb uso (uso + 16) new_pc_v
                   (Vptr sp_b sp_ofs) Hstore Hsp_load). right. lia. }

        assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m' sb uso (uso + 24) new_pc_v
                   env_v Hstore Henv_load). right. lia. }

        assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m' sb uso (uso + 32) new_pc_v _
                   Hstore Hextra_load). right. lia. }

        assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m' sb uso (uso + 40) new_pc_v
                   gd_ptr Hstore Hgd_load). right. lia. }

        assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m' sb uso (uso + 48) new_pc_v
                   ts_ptr Hstore Hts_load). right. lia. }

        split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].

        (* 1. le' ! _s *)
        { subst le'.
          rewrite PTree.gso by (simpl; congruence).
          rewrite PTree.gso by (simpl; congruence).
          rewrite PTree.gso by (simpl; congruence).
          rewrite PTree.gso by (simpl; congruence).
          exact Hle_s. }

        (* 2. pc field -- updated, pc_rel for target *)
        { exists new_pc_v. split.
          - exact Hpc_load'.
          - simpl. unfold pc_rel, new_pc_v, new_pc_ofs.
            f_equal.
            rewrite Hofs_eq.
            rewrite Ptrofs.sub_add_opp.
            rewrite Ptrofs.add_assoc.
            rewrite (Ptrofs.add_commut (Ptrofs.neg _) _).
            rewrite <- Ptrofs.sub_add_opp.
            rewrite Ptrofs.sub_idem.
            symmetry. apply Ptrofs.add_zero. }

        (* 3. accu field -- unchanged (Val_int 0) *)
        { exists (Vlong (Int64.repr 1)). split.
          - exact Haccu_load'.
          - simpl. exact (vr_int _ 0). }

        (* 4. sp field -- unchanged *)
        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs. split; [| split; [| split; [| split; [| split]]]].
          - exact Hsp_load'.
          - reflexivity.
          - simpl.
            apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb uso new_pc_v
                     Hstack_repr Hstore).
            intro Heq; exact (Hblock_sep (eq_sym Heq)).
          - exact Hblock_sep.
          - exact Hsp_ne_gb.
          - exact Hcb_ne_sp. }

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
            apply (global_repr_store_other_block hm m m' _ _ _ sb uso new_pc_v
                     Hglobal_repr Hstore).
            intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          - exact Hgb_ne. }

        (* 8. trap_sp field -- unchanged *)
        { exists ts_ptr. split.
          - exact Hts_load'.
          - simpl. exact Htrap_rel. }
      }
    }

    (* ============================================================== *)
    (* Case 1b: accu = Val_int (Z.pos p) => FALL THROUGH, pc := pc'   *)
    (* ============================================================== *)
    {
      intros ard Hpre Hstep_pre.
      set (sb := ar_sptr_block ard) in *.
      set (so := ar_sptr_ofs ard) in *.
      set (hm := ar_heap_map ard) in *.
      set (cb := ar_code_base_block ard) in *.
      set (co := ar_code_base_ofs ard) in *.
      destruct Hpre as (Hle_s &
        [pc_ptr [Hpc_load Hpc_rel]] &
        [accu_v [Haccu_load Haccu_repr]] &
        [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hblock_sep [Hsp_ne_gb Hcb_ne_sp]]]]]]]] &
        [env_v [Henv_load Henv_repr]] &
        Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne]]]] &
        [ts_ptr [Hts_load Htrap_rel]]).
      subst sp_ptr.

      (* Extract integer range from precondition *)
      destruct Hstep_pre as (_ & _ & Haccu_range).
      rewrite Haccu_eq in Haccu_range.

      pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].

      (* accu = Val_int (Z.pos p), val_repr gives Vlong (Int64.repr ((Z.pos p)*2+1)) *)
      rewrite Haccu_eq in Haccu_repr.
      inversion Haccu_repr; subst accu_v.

      destruct interp_state_co_pc_accu as [co_is [Hco [Hpc_offset Haccu_offset]]].

      (* pc_ptr is a concrete Vptr *)
      unfold pc_rel in Hpc_rel. subst pc_ptr.
      set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

      assert (Hpc_load_uso : Mem.load Mint64 m sb (Ptrofs.unsigned so) =
                Some (Vptr cb pc_ofs)).
      { replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia.
        exact Hpc_load. }

      (* New pc value: pc + 1 (advance by 4 bytes) *)
      set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
      set (new_pc_v := Vptr cb new_pc_ofs).

      (* Store to pc field *)
      destruct (store_pc_succeeds m sb (Ptrofs.unsigned so) new_pc_v
                  (ex_intro _ _ Hpc_load_uso)) as [m' Hstore].

      (* Witnesses *)
      set (le' := PTree.set _t'2 (Vptr cb pc_ofs)
                  (PTree.set _t'1 (Vlong (Int64.repr (Z.pos p * 2 + 1))) le)).
      exists le'. exists m'.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* Part 1: exec *)
      {
        apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.

        (* S1: _t'1 = s->accu *)
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_load; eval_cbn.

        (* Condition: Oeq _t'1 ((0<<1)+1) *)
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_cast_int_to_long_0 m); eval_cbn.
        rewrite (sem_shl_long_0_1 m); eval_cbn.
        rewrite (sem_add_long_int_0_1 m); eval_cbn.
        rewrite sem_eq_long_long; eval_cbn.
        rewrite (tagged_nonzero_ne_one (Z.pos p) ltac:(lia) Haccu_range); eval_cbn.

        (* FALSE branch: fall through *)
        (* _t'2 = s->pc *)
        rewrite PTree.gso by (simpl; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_zero so).
        rewrite Hpc_load_uso; eval_cbn.

        (* Sassign s->pc = _t'2 + 1 *)
        rewrite PTree.gso by (simpl; congruence).
        rewrite PTree.gso by (simpl; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.

        rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_pc_1 cb pc_ofs m); eval_cbn.
        rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.

        rewrite (ptrofs_add_zero so).
        fold new_pc_v.
        rewrite Hstore; eval_cbn.

        (* return 0 *)
        subst le'. reflexivity.
      }

      (* Part 2: abs_rel for post-state s <|pc := s.(pc)|> *)
      {
        set (uso := Ptrofs.unsigned so) in *.
        set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
        set (ard' := mk_abs_rel sb so hm cb new_co
                       (ar_global_block ard) (ar_global_ofs ard)
                       (ar_stack_block ard) (ar_stack_base_ofs ard)).
        exists ard'.

        assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some new_pc_v).
        { pose proof (load_after_store_same m m' sb uso new_pc_v Hstore) as Htmp.
          unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp.
          replace (uso + 0)%Z with uso by lia. exact Htmp. }

        assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) =
                  Some (Vlong (Int64.repr (Z.pos p * 2 + 1)))).
        { apply (load_after_store_other m m' sb uso (uso + 8) new_pc_v
                   (Vlong (Int64.repr (Z.pos p * 2 + 1))) Hstore Haccu_load). right. lia. }

        assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m' sb uso (uso + 16) new_pc_v
                   (Vptr sp_b sp_ofs) Hstore Hsp_load). right. lia. }

        assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m' sb uso (uso + 24) new_pc_v
                   env_v Hstore Henv_load). right. lia. }

        assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m' sb uso (uso + 32) new_pc_v _
                   Hstore Hextra_load). right. lia. }

        assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m' sb uso (uso + 40) new_pc_v
                   gd_ptr Hstore Hgd_load). right. lia. }

        assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m' sb uso (uso + 48) new_pc_v
                   ts_ptr Hstore Hts_load). right. lia. }

        split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].

        { subst le'.
          rewrite PTree.gso by (simpl; congruence).
          rewrite PTree.gso by (simpl; congruence).
          exact Hle_s. }

        { exists new_pc_v. split.
          - exact Hpc_load'.
          - simpl. apply pc_rel_shift_by_4. }

        { exists (Vlong (Int64.repr (Z.pos p * 2 + 1))). split.
          - exact Haccu_load'.
          - simpl. exact (vr_int _ (Z.pos p)). }

        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs. split; [| split; [| split; [| split; [| split]]]].
          - exact Hsp_load'.
          - reflexivity.
          - simpl.
            apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb uso new_pc_v
                     Hstack_repr Hstore).
            intro Heq; exact (Hblock_sep (eq_sym Heq)).
          - exact Hblock_sep.
          - exact Hsp_ne_gb.
          - exact Hcb_ne_sp. }

        { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }

        { simpl. exact Hextra_load'. }

        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd_load'.
          - simpl. exact Hgd_eq.
          - simpl.
            apply (global_repr_store_other_block hm m m' _ _ _ sb uso new_pc_v
                     Hglobal_repr Hstore).
            intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          - exact Hgb_ne. }

        { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. }
      }
    }

    (* ============================================================== *)
    (* Case 1c: accu = Val_int (Z.neg p) => FALL THROUGH              *)
    (* ============================================================== *)
    {
      intros ard Hpre Hstep_pre.
      set (sb := ar_sptr_block ard) in *.
      set (so := ar_sptr_ofs ard) in *.
      set (hm := ar_heap_map ard) in *.
      set (cb := ar_code_base_block ard) in *.
      set (co := ar_code_base_ofs ard) in *.
      destruct Hpre as (Hle_s &
        [pc_ptr [Hpc_load Hpc_rel]] &
        [accu_v [Haccu_load Haccu_repr]] &
        [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hblock_sep [Hsp_ne_gb Hcb_ne_sp]]]]]]]] &
        [env_v [Henv_load Henv_repr]] &
        Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne]]]] &
        [ts_ptr [Hts_load Htrap_rel]]).
      subst sp_ptr.

      (* Extract integer range from precondition *)
      destruct Hstep_pre as (_ & _ & Haccu_range).
      rewrite Haccu_eq in Haccu_range.

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

      destruct (store_pc_succeeds m sb (Ptrofs.unsigned so) new_pc_v
                  (ex_intro _ _ Hpc_load_uso)) as [m' Hstore].

      set (le' := PTree.set _t'2 (Vptr cb pc_ofs)
                  (PTree.set _t'1 (Vlong (Int64.repr (Z.neg p * 2 + 1))) le)).
      exists le'. exists m'.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* Part 1: exec *)
      {
        apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.

        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_load; eval_cbn.

        rewrite PTree.gss; eval_cbn.
        rewrite (sem_cast_int_to_long_0 m); eval_cbn.
        rewrite (sem_shl_long_0_1 m); eval_cbn.
        rewrite (sem_add_long_int_0_1 m); eval_cbn.
        rewrite sem_eq_long_long; eval_cbn.
        rewrite (tagged_nonzero_ne_one (Z.neg p) ltac:(lia) Haccu_range); eval_cbn.

        (* FALSE branch: fall through *)
        rewrite PTree.gso by (simpl; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_zero so).
        rewrite Hpc_load_uso; eval_cbn.

        rewrite PTree.gso by (simpl; congruence).
        rewrite PTree.gso by (simpl; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.

        rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_pc_1 cb pc_ofs m); eval_cbn.
        rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.

        rewrite (ptrofs_add_zero so).
        fold new_pc_v.
        rewrite Hstore; eval_cbn.

        subst le'. reflexivity.
      }

      (* Part 2: abs_rel *)
      {
        set (uso := Ptrofs.unsigned so) in *.
        set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
        set (ard' := mk_abs_rel sb so hm cb new_co
                       (ar_global_block ard) (ar_global_ofs ard)
                       (ar_stack_block ard) (ar_stack_base_ofs ard)).
        exists ard'.

        assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some new_pc_v).
        { pose proof (load_after_store_same m m' sb uso new_pc_v Hstore) as Htmp.
          unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp.
          replace (uso + 0)%Z with uso by lia. exact Htmp. }

        assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) =
                  Some (Vlong (Int64.repr (Z.neg p * 2 + 1)))).
        { apply (load_after_store_other m m' sb uso (uso + 8) new_pc_v
                   (Vlong (Int64.repr (Z.neg p * 2 + 1))) Hstore Haccu_load). right. lia. }

        assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m' sb uso (uso + 16) new_pc_v
                   (Vptr sp_b sp_ofs) Hstore Hsp_load). right. lia. }

        assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m' sb uso (uso + 24) new_pc_v
                   env_v Hstore Henv_load). right. lia. }

        assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m' sb uso (uso + 32) new_pc_v _
                   Hstore Hextra_load). right. lia. }

        assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m' sb uso (uso + 40) new_pc_v
                   gd_ptr Hstore Hgd_load). right. lia. }

        assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m' sb uso (uso + 48) new_pc_v
                   ts_ptr Hstore Hts_load). right. lia. }

        split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].

        { subst le'. rewrite PTree.gso by (simpl; congruence).
          rewrite PTree.gso by (simpl; congruence). exact Hle_s. }

        { exists new_pc_v. split. exact Hpc_load'. simpl. apply pc_rel_shift_by_4. }

        { exists (Vlong (Int64.repr (Z.neg p * 2 + 1))). split.
          exact Haccu_load'. simpl. exact (vr_int _ (Z.neg p)). }

        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs. split; [| split; [| split; [| split; [| split]]]].
          exact Hsp_load'. reflexivity. simpl.
          apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb uso new_pc_v
                   Hstack_repr Hstore).
          intro Heq; exact (Hblock_sep (eq_sym Heq)).
          exact Hblock_sep. exact Hsp_ne_gb. exact Hcb_ne_sp. }

        { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }

        { simpl. exact Hextra_load'. }

        { exists gd_ptr. split; [| split; [| split]].
          exact Hgd_load'. simpl. exact Hgd_eq. simpl.
          apply (global_repr_store_other_block hm m m' _ _ _ sb uso new_pc_v
                   Hglobal_repr Hstore).
          intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          exact Hgb_ne. }

        { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. }
      }
    }
  }

  (* ================================================================ *)
  (* Case 2: accu = Val_ptr addr => vacuously true                     *)
  (* CompCert's sem_binary_operation Oeq is undefined for Vptr vs      *)
  (* Vlong (both typed tlong), so the precondition excludes this case. *)
  (* ================================================================ *)
  {
    intros ard _ Hstep_pre.
    destruct Hstep_pre as (_ & _ & Haccu_absurd).
    rewrite Haccu_eq in Haccu_absurd. contradiction.
  }

  (* ================================================================ *)
  (* Case 3: accu = Val_closure addr offset => vacuously true          *)
  (* Same as Case 2: Vptr comparison undefined in CompCert.            *)
  (* ================================================================ *)
  {
    intros ard _ Hstep_pre.
    destruct Hstep_pre as (_ & _ & Haccu_absurd).
    rewrite Haccu_eq in Haccu_absurd. contradiction.
  }

  (* ================================================================ *)
  (* Case 4: accu = Val_block tag fields => FALL THROUGH               *)
  (* ================================================================ *)
  {
    destruct fields as [| hd tl].

    (* Case 4a: Val_block tag nil (atom) -- Vlong representation *)
    {
      intros ard Hpre Hstep_pre.
      set (sb := ar_sptr_block ard) in *.
      set (so := ar_sptr_ofs ard) in *.
      set (hm := ar_heap_map ard) in *.
      set (cb := ar_code_base_block ard) in *.
      set (co := ar_code_base_ofs ard) in *.
      destruct Hpre as (Hle_s &
        [pc_ptr [Hpc_load Hpc_rel]] &
        [accu_v [Haccu_load Haccu_repr]] &
        [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hblock_sep [Hsp_ne_gb Hcb_ne_sp]]]]]]]] &
        [env_v [Henv_load Henv_repr]] &
        Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne]]]] &
        [ts_ptr [Hts_load Htrap_rel]]).
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

      destruct (store_pc_succeeds m sb (Ptrofs.unsigned so) new_pc_v
                  (ex_intro _ _ Hpc_load_uso)) as [m' Hstore].

      set (le' := PTree.set _t'2 (Vptr cb pc_ofs)
                  (PTree.set _t'1 (Vlong (Int64.repr (Z.of_nat tag * 1024))) le)).
      exists le'. exists m'.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* Part 1: exec *)
      {
        apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.

        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_load; eval_cbn.

        rewrite PTree.gss; eval_cbn.
        rewrite (sem_cast_int_to_long_0 m); eval_cbn.
        rewrite (sem_shl_long_0_1 m); eval_cbn.
        rewrite (sem_add_long_int_0_1 m); eval_cbn.
        rewrite sem_eq_long_long; eval_cbn.
        rewrite (tagged_block_atom_ne_one tag); eval_cbn.

        (* FALSE branch *)
        rewrite PTree.gso by (simpl; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_zero so).
        rewrite Hpc_load_uso; eval_cbn.

        rewrite PTree.gso by (simpl; congruence).
        rewrite PTree.gso by (simpl; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.

        rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_pc_1 cb pc_ofs m); eval_cbn.
        rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.

        rewrite (ptrofs_add_zero so).
        fold new_pc_v.
        rewrite Hstore; eval_cbn.

        subst le'. reflexivity.
      }

      (* Part 2: abs_rel *)
      {
        set (uso := Ptrofs.unsigned so) in *.
        set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
        set (ard' := mk_abs_rel sb so hm cb new_co
                       (ar_global_block ard) (ar_global_ofs ard)
                       (ar_stack_block ard) (ar_stack_base_ofs ard)).
        exists ard'.

        assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some new_pc_v).
        { pose proof (load_after_store_same m m' sb uso new_pc_v Hstore) as Htmp.
          unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp.
          replace (uso + 0)%Z with uso by lia. exact Htmp. }

        assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) =
                  Some (Vlong (Int64.repr (Z.of_nat tag * 1024)))).
        { apply (load_after_store_other m m' sb uso (uso + 8) new_pc_v
                   (Vlong (Int64.repr (Z.of_nat tag * 1024))) Hstore Haccu_load). right. lia. }

        assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m' sb uso (uso + 16) new_pc_v
                   (Vptr sp_b sp_ofs) Hstore Hsp_load). right. lia. }

        assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m' sb uso (uso + 24) new_pc_v
                   env_v Hstore Henv_load). right. lia. }

        assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m' sb uso (uso + 32) new_pc_v _
                   Hstore Hextra_load). right. lia. }

        assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m' sb uso (uso + 40) new_pc_v
                   gd_ptr Hstore Hgd_load). right. lia. }

        assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m' sb uso (uso + 48) new_pc_v
                   ts_ptr Hstore Hts_load). right. lia. }

        split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].

        { subst le'. rewrite PTree.gso by (simpl; congruence).
          rewrite PTree.gso by (simpl; congruence). exact Hle_s. }

        { exists new_pc_v. split. exact Hpc_load'. simpl. apply pc_rel_shift_by_4. }

        { exists (Vlong (Int64.repr (Z.of_nat tag * 1024))). split.
          exact Haccu_load'. simpl. exact (vr_block_atom _ tag). }

        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs. split; [| split; [| split; [| split; [| split]]]].
          exact Hsp_load'. reflexivity. simpl.
          apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb uso new_pc_v
                   Hstack_repr Hstore).
          intro Heq; exact (Hblock_sep (eq_sym Heq)).
          exact Hblock_sep. exact Hsp_ne_gb. exact Hcb_ne_sp. }

        { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }

        { simpl. exact Hextra_load'. }

        { exists gd_ptr. split; [| split; [| split]].
          exact Hgd_load'. simpl. exact Hgd_eq. simpl.
          apply (global_repr_store_other_block hm m m' _ _ _ sb uso new_pc_v
                   Hglobal_repr Hstore).
          intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          exact Hgb_ne. }

        { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. }
      }
    }

    (* Case 4b: Val_block tag (hd :: tl) -- non-atom block *)
    (* val_repr only covers Val_block tag nil via vr_block_atom.
       For non-empty fields, val_repr has no constructor, so
       Haccu_repr is vacuously contradictory (no inversion applies). *)
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
Qed.
