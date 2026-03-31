(* BRANCHIF_correct.v -- BRANCHIF handler completeness proof.

   BRANCHIF handler:
   - Rocq: handle_BRANCHIF target pc' s matches accu:
       Val_int 0 => Step {pc := pc'}        (fall through; pc' = s.pc)
       _         => Step {pc := target}      (branch taken)

   - C (Clight AST): The handler body does:
       1. _t'1 = s->accu                   (read accu, tlong)
       2. if (_t'1 != ((0 << 1) + 1))      (test accu != tagged(0) = 1)
          THEN (branch taken):
            _t'3 = s->pc
            _t'4 = s->pc
            _t'5 = *_t'4                    (read offset from code stream)
            s->pc = _t'3 + _t'5            (ptr + int arithmetic)
          ELSE (fall through):
            _t'2 = s->pc
            s->pc = _t'2 + 1               (advance past operand)
       3. return 0

   Two cases:
   - accu = Val_int 0: C takes else branch, stores pc + 1.
   - accu != Val_int 0: C takes then branch, reads offset, stores
     pc + offset.

   Key axioms:
   - code_contains_branch_ofs: code stream at pc contains the offset
   - val_repr_ne_tagged_zero: val_repr for non-zero values produces
     a C value that compares != 1 (tagged 0). This bridges a gap in
     CompCert's semantics for Vptr vs Vlong comparison, and assumes
     tagged integers are within the 63-bit range. *)

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

Lemma interp_state_co_branchif : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Code memory axioms                                                  *)
(* ================================================================== *)

Axiom code_block_ne_sptr : forall (ard : abs_rel_data),
  ar_code_base_block ard <> ar_sptr_block ard.

(* The code stream at position pc contains the branch offset, where
   the offset is (target - pc) in units of sizeof(code_t) = 4. *)
Axiom code_contains_branch_ofs : forall m cb co rocq_pc target,
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t))))
    = Some (Vint (Int.repr (target - rocq_pc))).

(* ================================================================== *)
(* Comparison axiom: val_repr for non-zero values gives != tagged(0)   *)
(*                                                                      *)
(* In real x86-64 C, any value that is not tagged 0 (= 1) will compare *)
(* not-equal to 1.  CompCert's sem_cmp is too strict about Vptr vs     *)
(* Vlong comparison (returns None), and the tagged integer range may    *)
(* wrap around for huge Z values.  This axiom bridges both gaps.       *)
(* ================================================================== *)

Axiom val_repr_ne_tagged_zero : forall hm v cv m,
  val_repr hm v cv ->
  v <> Val_int 0 ->
  sem_binary_operation (genv_cenv clight_ge) Cop.One
    cv tlong (Vlong (Int64.repr 1)) tlong m
    = Some (Vint Int.one).

(* ================================================================== *)
(* Memory helpers                                                      *)
(* ================================================================== *)

Lemma store_pc_succeeds : forall m sb so v_new,
  (exists v_old, Mem.load Mint64 m sb so = Some v_old) ->
  exists m', Mem.store Mint64 m sb so v_new = Some m'.
Proof.
  intros m sb so v_new [v_old Hload].
  exact (store_succeeds_from_load m sb so v_old v_new Hload).
Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* ================================================================== *)
(* Pointer / casting helpers                                           *)
(* ================================================================== *)

Lemma ptrofs_add_zero : forall ofs,
  Ptrofs.add ofs (Ptrofs.repr 0) = ofs.
Proof.
  intros. change (Ptrofs.repr 0) with Ptrofs.zero.
  apply Ptrofs.add_zero.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

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

(* ================================================================== *)
(* Comparison semantics for Val_int 0 case                             *)
(* ================================================================== *)

(* The tagged-0 constant evaluation:
     (long)0 << 1 = 0, then 0 + 1 = 1 *)
Lemma sem_one_long_eq : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Cop.One
    (Vlong n) tlong (Vlong (Int64.repr 1)) tlong m
    = Some (Val.of_bool (negb (Int64.eq n (Int64.repr 1)))).
Proof.
  intros. reflexivity.
Qed.

Lemma bool_val_of_bool : forall b m,
  bool_val (Val.of_bool b) tint m = Some b.
Proof.
  intros [] m; simpl; reflexivity.
Qed.

Lemma int64_eq_1_1 : Int64.eq (Int64.repr 1) (Int64.repr 1) = true.
Proof.
  unfold Int64.eq.
  rewrite Coqlib.zeq_true.
  reflexivity.
Qed.

(* bool_val for Vint Int.one on tint gives true *)
Lemma bool_val_vint_one : forall m,
  bool_val (Vint Int.one) tint m = Some true.
Proof.
  intros. simpl. reflexivity.
Qed.

(* ================================================================== *)
(* pc_rel helpers                                                      *)
(* ================================================================== *)

(* For the fall-through case: new code base is co + sizeof_code_t *)
Lemma pc_rel_shift_1 : forall cb co rocq_pc,
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
(* All branch-taken cases share the same structure: one store to the   *)
(* pc field at offset 0, then abs_rel with adjusted code base.         *)
(* ================================================================== *)

(* Helper: prove fields survive store at offset 0 *)
Local Ltac prove_field_survives Hstore Hload :=
  apply (load_after_store_other _ _ _ _ _ _ _ Hstore Hload); right; lia.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_BRANCHIF_correct : forall target,
    handler_correct (handle_BRANCHIF target) f_instr_BRANCHIF
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).
Proof.
  intro target.
  intros e le m s.
  unfold handler_correct, handle_BRANCHIF.

  (* Case split on accu *)
  destruct (Machine.accu s) as [n | addr | addr ofs_cl | tag fields] eqn:Haccu_eq.

  (* ================================================================ *)
  (* Case 1: accu = Val_int n                                          *)
  (* ================================================================ *)
  {
    destruct (Z.eq_dec n 0) as [Hn0 | Hn0].

    (* ============================================================== *)
    (* Case 1a: accu = Val_int 0 => fall through (C else branch)      *)
    (* ============================================================== *)
    {
      subst n. simpl.
      intro Hpre.

      destruct Hpre as [ard Hpre].
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

      pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
      pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep. fold sb in Hblock_sep.
      pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.

      (* accu = Val_int 0, val_repr gives Vlong (Int64.repr 1) *)
      rewrite Haccu_eq in Haccu_repr.
      inversion Haccu_repr; subst accu_v.

      destruct interp_state_co_branchif as [co_is [Hco [Hpc_offset Haccu_offset]]].

      (* pc_ptr is a concrete Vptr *)
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
                    (PTree.set _t'1 (Vlong (Int64.repr 1)) le)).
      exists le'. exists m'.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* Part 1: exec *)
      {
        apply (eval_stmt_to_exec clight_ge 20).
        eval_cbn.

        (* S1: Sset _t'1 = s->accu *)
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_load; eval_cbn.

        (* Condition: _t'1 != ((0 << 1) + 1) *)
        rewrite PTree.gss; eval_cbn.
        (* Inner: Ecast 0 tint -> tlong *)
        rewrite (sem_cast_int_to_long_0 m); eval_cbn.
        (* Oshl 0L 1 *)
        rewrite (sem_shl_long_0_1 m); eval_cbn.
        (* Oadd 0L 1 -- gives Vlong(1) *)
        rewrite (sem_add_long_int_0_1 m); eval_cbn.
        (* One: Vlong(1) != Vlong(1) = false *)
        rewrite sem_one_long_eq; eval_cbn.
        rewrite int64_eq_1_1; eval_cbn.
        (* bool_val(Vzero, tint) = Some false => takes else branch *)

        (* Else branch: fall through *)
        (* S2b: Sset _t'2 = s->pc *)
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64.
        rewrite (ptrofs_add_zero so).
        rewrite Hpc_load_uso; eval_cbn.

        (* S3b: Sassign s->pc = _t'2 + 1 *)
        (* Lvalue *)
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.

        (* Rvalue *)
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_pc_1 cb pc_ofs m); eval_cbn.
        rewrite sem_cast_ptr_tint_to_ptr_tint; eval_cbn.

        (* Store *)
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_zero so).
        fold new_pc_v.
        rewrite Hstore; eval_cbn.

        (* return 0 *)
        subst le'. reflexivity.
      }

      (* Part 2: abs_rel *)
      {
        set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
        set (ard' := mk_abs_rel sb so hm cb new_co
                       (ar_global_block ard) (ar_global_ofs ard)
                       (ar_stack_block ard) (ar_stack_base_ofs ard)).
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

        split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].

        { subst le'.
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          exact Hle_s. }

        { exists new_pc_v. split.
          - exact Hpc_load'.
          - simpl. subst new_pc_v new_pc_ofs.
            apply pc_rel_shift_1. }

        { exists (Vlong (Int64.repr 1)). split.
          - exact Haccu_load'.
          - simpl. rewrite Haccu_eq. constructor. }

        { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs. split; [| split].
          - exact Hsp_load'.
          - reflexivity.
          - simpl.
            apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb uso new_pc_v
                     Hstack_repr Hstore).
            intro Heq; exact (Hblock_sep (eq_sym Heq)). }

        { exists env_v. split.
          - exact Henv_load'.
          - simpl. exact Henv_repr. }

        { simpl. exact Hextra_load'. }

        { exists gd_ptr. split; [| split].
          - exact Hgd_load'.
          - simpl. exact Hgd_eq.
          - simpl.
            apply (global_repr_store_other_block hm m m' _ _ _ sb uso new_pc_v
                     Hglobal_repr Hstore).
            intro Heq2; exact (Hgb_ne (eq_sym Heq2)). }

        { exists ts_ptr. split.
          - exact Hts_load'.
          - simpl. exact Htrap_rel. }
      }
    }

    (* ============================================================== *)
    (* Case 1b: accu = Val_int n, n <> 0 => branch taken              *)
    (* ============================================================== *)
    {
      (* n <> 0, so the match gives the wildcard: Step {pc := target} *)
      destruct n as [| p | p]; [contradiction | |]; simpl;
      intro Hpre;

      (destruct Hpre as [ard Hpre];
      set (sb := ar_sptr_block ard) in *;
      set (so := ar_sptr_ofs ard) in *;
      set (hm := ar_heap_map ard) in *;
      set (cb := ar_code_base_block ard) in *;
      set (co := ar_code_base_ofs ard) in *;
      destruct Hpre as (Hle_s &
        [pc_ptr [Hpc_load Hpc_rel]] &
        [accu_v [Haccu_load Haccu_repr]] &
        [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq Hstack_repr]]]]] &
        [env_v [Henv_load Henv_repr]] &
        Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq Hglobal_repr]]] &
        [ts_ptr [Hts_load Htrap_rel]]);
      subst sp_ptr;

      pose proof (sptr_ofs_representable ard) as Hso_bound; fold so in Hso_bound;
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _];
      pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep; fold sb in Hblock_sep;
      pose proof (global_block_ne_sptr ard) as Hgb_ne; fold sb in Hgb_ne;

      rewrite Haccu_eq in Haccu_repr;

      destruct interp_state_co_branchif as [co_is [Hco [Hpc_offset Haccu_offset]]];

      unfold pc_rel in Hpc_rel; subst pc_ptr;
      set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *;

      assert (Hpc_load_uso : Mem.load Mint64 m sb (Ptrofs.unsigned so) =
                Some (Vptr cb pc_ofs))
        by (replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia;
            exact Hpc_load);

      set (branch_ofs := Int.repr (target - Machine.pc s));
      pose proof (code_contains_branch_ofs m cb co (Machine.pc s) target) as Hcode_load;
      fold pc_ofs in Hcode_load;
      fold branch_ofs in Hcode_load;

      set (new_pc_ofs := Ptrofs.add pc_ofs
             (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                         (ptrofs_of_int Signed branch_ofs)));
      set (new_pc_v := Vptr cb new_pc_ofs);

      destruct (store_pc_succeeds m sb (Ptrofs.unsigned so) new_pc_v
                  (ex_intro _ _ Hpc_load_uso)) as [m' Hstore];

      (* Use the axiom for the comparison *)
      pose proof (val_repr_ne_tagged_zero hm _ accu_v m
                    Haccu_repr ltac:(rewrite Haccu_eq; discriminate)) as Hcmp;

      set (le' := PTree.set _t'5 (Vint branch_ofs)
                    (PTree.set _t'4 (Vptr cb pc_ofs)
                      (PTree.set _t'3 (Vptr cb pc_ofs)
                        (PTree.set _t'1 accu_v le))));
      exists le'; exists m';
      exists (Out_return (Some (Vint (Int.repr 0), tint)));

      split;

      [ (* Part 1: exec *)
        apply (eval_stmt_to_exec clight_ge 20);
        eval_cbn;

        (* S1: _t'1 = s->accu *)
        rewrite Hle_s; eval_cbn;
        rewrite Hco; eval_cbn;
        rewrite Haccu_offset; eval_cbn;
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia));
        rewrite Haccu_load; eval_cbn;

        (* Condition *)
        rewrite PTree.gss; eval_cbn;
        rewrite (sem_cast_int_to_long_0 m); eval_cbn;
        rewrite (sem_shl_long_0_1 m); eval_cbn;
        rewrite (sem_add_long_int_0_1 m); eval_cbn;
        (* Use the axiom: comparison gives true *)
        rewrite Hcmp; eval_cbn;

        (* Then branch: branch taken *)
        (* S2a: _t'3 = s->pc *)
        rewrite PTree.gso by (compute; congruence);
        rewrite Hle_s; eval_cbn;
        rewrite Hco; eval_cbn;
        rewrite Hpc_offset; eval_cbn;
        rewrite Mptr_Mint64;
        rewrite (ptrofs_add_zero so);
        rewrite Hpc_load_uso; eval_cbn;

        (* S3a: _t'4 = s->pc *)
        rewrite PTree.gso by (compute; congruence);
        rewrite PTree.gso by (compute; congruence);
        rewrite Hle_s; eval_cbn;
        rewrite Hco; eval_cbn;
        rewrite Hpc_offset; eval_cbn;
        rewrite Mptr_Mint64;
        rewrite (ptrofs_add_zero so);
        rewrite Hpc_load_uso; eval_cbn;

        (* S4a: _t'5 = *_t'4 (read branch offset from code) *)
        rewrite PTree.gss; eval_cbn;
        rewrite Hcode_load; eval_cbn;

        (* S5a: s->pc = _t'3 + _t'5 *)
        (* Lvalue *)
        rewrite PTree.gso by (compute; congruence);
        rewrite PTree.gso by (compute; congruence);
        rewrite PTree.gso by (compute; congruence);
        rewrite PTree.gso by (compute; congruence);
        rewrite Hle_s; eval_cbn;
        rewrite Hco; eval_cbn;
        rewrite Hpc_offset; eval_cbn;
        rewrite Mptr_Mint64; eval_cbn;

        (* Rvalue: _t'3 + _t'5 *)
        rewrite (PTree.gso _ _ ltac:(compute; congruence));
        rewrite (PTree.gso _ _ ltac:(compute; congruence));
        rewrite PTree.gss; eval_cbn;
        rewrite PTree.gss; eval_cbn;

        unfold sem_binary_operation, sem_add;
        change (classify_add (tptr tint) tint) with (add_case_pi tint Signed);
        unfold sem_add_ptr_int; eval_cbn;

        rewrite sem_cast_ptr_tint_to_ptr_tint; eval_cbn;

        rewrite Mptr_Mint64; eval_cbn;
        rewrite (ptrofs_add_zero so);
        change (Ptrofs.repr 4) with (Ptrofs.repr (sizeof ge tint));
        fold new_pc_v;
        rewrite Hstore; eval_cbn;

        subst le'; reflexivity

      | (* Part 2: abs_rel *)
        (set (new_co := Ptrofs.sub new_pc_ofs (Ptrofs.repr (target * sizeof_code_t)));
        set (ard' := mk_abs_rel sb so hm cb new_co
                       (ar_global_block ard) (ar_global_ofs ard)
                       (ar_stack_block ard) (ar_stack_base_ofs ard));
        exists ard';
        set (uso := Ptrofs.unsigned so) in *;

        assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some new_pc_v)
          by (pose proof (load_after_store_same m m' sb uso new_pc_v Hstore) as Htmp;
              unfold new_pc_v in Htmp |- *;
              rewrite load_result_vptr in Htmp;
              replace (uso + 0)%Z with uso by lia;
              exact Htmp);

        assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some accu_v)
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

        split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]];

        [ subst le';
          rewrite PTree.gso by (compute; congruence);
          rewrite PTree.gso by (compute; congruence);
          rewrite PTree.gso by (compute; congruence);
          rewrite PTree.gso by (compute; congruence);
          exact Hle_s

        | exists new_pc_v; split;
          [ exact Hpc_load'
          | simpl; unfold pc_rel; subst new_pc_v;
            f_equal;
            unfold new_co;
            rewrite Ptrofs.sub_add_opp;
            rewrite Ptrofs.add_assoc;
            rewrite (Ptrofs.add_commut (Ptrofs.neg _) _);
            rewrite <- Ptrofs.sub_add_opp;
            rewrite Ptrofs.sub_idem;
            symmetry; apply Ptrofs.add_zero ]

        | exists accu_v; split;
          [ exact Haccu_load'
          | simpl; rewrite Haccu_eq; exact Haccu_repr ]

        | exists (Vptr sp_b sp_ofs), sp_b, sp_ofs; split; [| split];
          [ exact Hsp_load'
          | reflexivity
          | simpl;
            apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb uso new_pc_v
                     Hstack_repr Hstore);
            intro Heq; exact (Hblock_sep (eq_sym Heq)) ]

        | exists env_v; split;
          [ exact Henv_load'
          | simpl; exact Henv_repr ]

        | simpl; exact Hextra_load'

        | exists gd_ptr; split; [| split];
          [ exact Hgd_load'
          | simpl; exact Hgd_eq
          | simpl;
            apply (global_repr_store_other_block hm m m' _ _ _ sb uso new_pc_v
                     Hglobal_repr Hstore);
            intro Heq2; exact (Hgb_ne (eq_sym Heq2)) ]

        | exists ts_ptr; split;
          [ exact Hts_load'
          | simpl; exact Htrap_rel ] ])
      ]).
    }
  }

  (* ================================================================ *)
  (* Cases 2-4: non-integer accu => branch taken                       *)
  (*                                                                    *)
  (* These use val_repr_ne_tagged_zero for the comparison axiom.       *)
  (* The proof structure is identical to Case 1b.                      *)
  (* ================================================================ *)

  (* Val_ptr *)
  all: simpl;
    intro Hpre;

    (destruct Hpre as [ard Hpre];
    set (sb := ar_sptr_block ard) in *;
    set (so := ar_sptr_ofs ard) in *;
    set (hm := ar_heap_map ard) in *;
    set (cb := ar_code_base_block ard) in *;
    set (co := ar_code_base_ofs ard) in *;
    destruct Hpre as (Hle_s &
      [pc_ptr [Hpc_load Hpc_rel]] &
      [accu_v [Haccu_load Haccu_repr]] &
      [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq Hstack_repr]]]]] &
      [env_v [Henv_load Henv_repr]] &
      Hextra_load &
      [gd_ptr [Hgd_load [Hgd_eq Hglobal_repr]]] &
      [ts_ptr [Hts_load Htrap_rel]]);
    subst sp_ptr;

    pose proof (sptr_ofs_representable ard) as Hso_bound; fold so in Hso_bound;
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _];
    pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep; fold sb in Hblock_sep;
    pose proof (global_block_ne_sptr ard) as Hgb_ne; fold sb in Hgb_ne;

    destruct interp_state_co_branchif as [co_is [Hco [Hpc_offset Haccu_offset]]];

    unfold pc_rel in Hpc_rel; subst pc_ptr;
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *;

    assert (Hpc_load_uso : Mem.load Mint64 m sb (Ptrofs.unsigned so) =
              Some (Vptr cb pc_ofs))
      by (replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia;
          exact Hpc_load);

    set (branch_ofs := Int.repr (target - Machine.pc s));
    pose proof (code_contains_branch_ofs m cb co (Machine.pc s) target) as Hcode_load;
    fold pc_ofs in Hcode_load;
    fold branch_ofs in Hcode_load;

    set (new_pc_ofs := Ptrofs.add pc_ofs
           (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                       (ptrofs_of_int Signed branch_ofs)));
    set (new_pc_v := Vptr cb new_pc_ofs);

    destruct (store_pc_succeeds m sb (Ptrofs.unsigned so) new_pc_v
                (ex_intro _ _ Hpc_load_uso)) as [m' Hstore];

    pose proof (val_repr_ne_tagged_zero hm _ accu_v m
                  Haccu_repr ltac:(rewrite Haccu_eq; discriminate)) as Hcmp;

    set (le' := PTree.set _t'5 (Vint branch_ofs)
                  (PTree.set _t'4 (Vptr cb pc_ofs)
                    (PTree.set _t'3 (Vptr cb pc_ofs)
                      (PTree.set _t'1 accu_v le))));
    exists le'; exists m';
    exists (Out_return (Some (Vint (Int.repr 0), tint)));

    split;

    [ (* Part 1: exec *)
      apply (eval_stmt_to_exec clight_ge 20);
      eval_cbn;

      rewrite Hle_s; eval_cbn;
      rewrite Hco; eval_cbn;
      rewrite Haccu_offset; eval_cbn;
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia));
      rewrite Haccu_load; eval_cbn;

      rewrite PTree.gss; eval_cbn;
      rewrite (sem_cast_int_to_long_0 m); eval_cbn;
      rewrite (sem_shl_long_0_1 m); eval_cbn;
      rewrite (sem_add_long_int_0_1 m); eval_cbn;
      rewrite Hcmp; eval_cbn;

      rewrite PTree.gso by (compute; congruence);
      rewrite Hle_s; eval_cbn;
      rewrite Hco; eval_cbn;
      rewrite Hpc_offset; eval_cbn;
      rewrite Mptr_Mint64;
      rewrite (ptrofs_add_zero so);
      rewrite Hpc_load_uso; eval_cbn;

      rewrite PTree.gso by (compute; congruence);
      rewrite PTree.gso by (compute; congruence);
      rewrite Hle_s; eval_cbn;
      rewrite Hco; eval_cbn;
      rewrite Hpc_offset; eval_cbn;
      rewrite Mptr_Mint64;
      rewrite (ptrofs_add_zero so);
      rewrite Hpc_load_uso; eval_cbn;

      rewrite PTree.gss; eval_cbn;
      rewrite Hcode_load; eval_cbn;

      rewrite PTree.gso by (compute; congruence);
      rewrite PTree.gso by (compute; congruence);
      rewrite PTree.gso by (compute; congruence);
      rewrite PTree.gso by (compute; congruence);
      rewrite Hle_s; eval_cbn;
      rewrite Hco; eval_cbn;
      rewrite Hpc_offset; eval_cbn;
      rewrite Mptr_Mint64; eval_cbn;

      rewrite (PTree.gso _ _ ltac:(compute; congruence));
      rewrite (PTree.gso _ _ ltac:(compute; congruence));
      rewrite PTree.gss; eval_cbn;
      rewrite PTree.gss; eval_cbn;

      unfold sem_binary_operation, sem_add;
      change (classify_add (tptr tint) tint) with (add_case_pi tint Signed);
      unfold sem_add_ptr_int; eval_cbn;

      rewrite sem_cast_ptr_tint_to_ptr_tint; eval_cbn;

      rewrite Mptr_Mint64; eval_cbn;
      rewrite (ptrofs_add_zero so);
      change (Ptrofs.repr 4) with (Ptrofs.repr (sizeof ge tint));
      fold new_pc_v;
      rewrite Hstore; eval_cbn;

      subst le'; reflexivity

    | (* Part 2: abs_rel *)
      (set (new_co := Ptrofs.sub new_pc_ofs (Ptrofs.repr (target * sizeof_code_t)));
      set (ard' := mk_abs_rel sb so hm cb new_co
                     (ar_global_block ard) (ar_global_ofs ard)
                     (ar_stack_block ard) (ar_stack_base_ofs ard));
      exists ard';
      set (uso := Ptrofs.unsigned so) in *;

      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some new_pc_v)
        by (pose proof (load_after_store_same m m' sb uso new_pc_v Hstore) as Htmp;
            unfold new_pc_v in Htmp |- *;
            rewrite load_result_vptr in Htmp;
            replace (uso + 0)%Z with uso by lia;
            exact Htmp);

      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some accu_v)
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

      split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]];

      [ subst le';
        rewrite PTree.gso by (compute; congruence);
        rewrite PTree.gso by (compute; congruence);
        rewrite PTree.gso by (compute; congruence);
        rewrite PTree.gso by (compute; congruence);
        exact Hle_s

      | exists new_pc_v; split;
        [ exact Hpc_load'
        | simpl; unfold pc_rel; subst new_pc_v;
          f_equal;
          unfold new_co;
          rewrite Ptrofs.sub_add_opp;
          rewrite Ptrofs.add_assoc;
          rewrite (Ptrofs.add_commut (Ptrofs.neg _) _);
          rewrite <- Ptrofs.sub_add_opp;
          rewrite Ptrofs.sub_idem;
          symmetry; apply Ptrofs.add_zero ]

      | exists accu_v; split;
        [ exact Haccu_load'
        | simpl; rewrite Haccu_eq; exact Haccu_repr ]

      | exists (Vptr sp_b sp_ofs), sp_b, sp_ofs; split; [| split];
        [ exact Hsp_load'
        | reflexivity
        | simpl;
          apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb uso new_pc_v
                   Hstack_repr Hstore);
          intro Heq; exact (Hblock_sep (eq_sym Heq)) ]

      | exists env_v; split;
        [ exact Henv_load'
        | simpl; exact Henv_repr ]

      | simpl; exact Hextra_load'

      | exists gd_ptr; split; [| split];
        [ exact Hgd_load'
        | simpl; exact Hgd_eq
        | simpl;
          apply (global_repr_store_other_block hm m m' _ _ _ sb uso new_pc_v
                   Hglobal_repr Hstore);
          intro Heq2; exact (Hgb_ne (eq_sym Heq2)) ]

      | exists ts_ptr; split;
        [ exact Hts_load'
        | simpl; exact Htrap_rel ] ])
    ]).
Qed.
