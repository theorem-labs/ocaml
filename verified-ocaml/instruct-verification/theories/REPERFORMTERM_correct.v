(* REPERFORMTERM_correct.v -- C body is pc += 1; return 0. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From RecordUpdate Require Import RecordUpdate.
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
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul Ptrofs.sub
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout: pc field offset                                      *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma pc_field_offset : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full).
Proof.
  eexists. split; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_pc_co_RPT : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full).
Proof.
  rewrite cenv_is_ce. exact pc_field_offset.
Qed.

(* ================================================================== *)
(* Pointer arithmetic helpers                                          *)
(* ================================================================== *)

Lemma ptrofs_add_zero_RPT : forall ofs,
  Ptrofs.add ofs (Ptrofs.repr 0) = ofs.
Proof.
  intros. change (Ptrofs.repr 0) with Ptrofs.zero.
  apply Ptrofs.add_zero.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint_RPT : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_REPERFORMTERM_correct :
    handler_correct handle_REPERFORMTERM f_instr_REPERFORMTERM
      (fun _ _ _ _ => True)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_REPERFORMTERM. simpl.
  intros ard Hpre _.
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
  unfold pc_rel in Hpc_rel.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.
  subst pc_ptr.
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  destruct interp_state_pc_co_RPT as [co_is [Hco Hpc_offset]].
  (* Compute the new PC value: old_pc + 1 (pointer + int) *)
  set (new_pc_ptr := Vptr cb
    (Ptrofs.add pc_ofs
       (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                   (ptrofs_of_int Signed (Int.repr 1))))).
  (* Establish the pc load without the + 0 *)
  assert (Hpc_load_uso : Mem.load Mint64 m sb (Ptrofs.unsigned so) =
            Some (Vptr cb pc_ofs)).
  { replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia.
    exact Hpc_load. }
  (* Store the new PC *)
  assert (Hpc_load_uso0 : Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { replace (Ptrofs.unsigned so + 0)%Z with (Ptrofs.unsigned so) by lia.
    exact Hpc_load_uso. }
  destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load_uso0 ltac:(lia) ltac:(lia) new_pc_ptr) as [m' Hstore0].
  assert (Hstore : Mem.store Mint64 m sb (Ptrofs.unsigned so) new_pc_ptr = Some m').
  { replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia.
    exact Hstore0. }
  (* Ident distinctness facts *)
  assert (Hs_ne_t1 : _s <> _t'1) by (unfold _s, _t'1; congruence).
  (* The C body modifies the temp env *)
  set (le' := PTree.set _t'1 (Vptr cb pc_ofs) le).
  exists le'. exists m'.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).
  split.
  - (* Part 1: exec_stmt -- the C body executes and produces le', m' *)
    apply (eval_stmt_to_exec clight_ge 10).
    eval_cbn.
    (* _s lookup -> struct ptr *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hpc_offset; eval_cbn.
    (* Load of s->pc field *)
    rewrite Mptr_Mint64.
    rewrite (ptrofs_add_zero_RPT so).
    rewrite Hpc_load_uso; eval_cbn.
    (* _s lookup in (set _t'1 ... le) for Sassign lvalue *)
    rewrite (PTree.gso _ _ Hs_ne_t1).
    rewrite Hle_s; eval_cbn.
    (* _t'1 lookup via get-set-same for Sassign rvalue *)
    rewrite (PTree.gss); eval_cbn.
    (* sem_binary_operation: ptr + int *)
    unfold sem_binary_operation, sem_add.
    change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
    unfold sem_add_ptr_int. eval_cbn.
    (* sem_cast (tptr tint) -> (tptr tint) *)
    rewrite sem_cast_ptr_tint_to_ptr_tint_RPT; eval_cbn.
    (* Store to s->pc *)
    rewrite Mptr_Mint64.
    rewrite (ptrofs_add_zero_RPT so).
    change (Ptrofs.repr 4) with (Ptrofs.repr (sizeof ge tint)).
    fold new_pc_ptr.
    rewrite Hstore; eval_cbn.
    subst le'. reflexivity.
  - (* Part 2: abs_rel on post-state (s <|pc := pc s + 1|>) *)
    set (uso := Ptrofs.unsigned so) in *.
    (* Construct new ard' with adjusted code base offset *)
    set (new_pc_ofs := Ptrofs.add pc_ofs
       (Ptrofs.mul (Ptrofs.repr (sizeof ge tint))
                   (ptrofs_of_int Signed (Int.repr 1)))).
    set (new_co := Ptrofs.sub new_pc_ofs (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))).
    set (ard' := mk_abs_rel sb so hm cb new_co
                   (ar_global_block ard) (ar_global_ofs ard)
                   (ar_stack_block ard) (ar_stack_base_ofs ard)
                   (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard)
                   (ar_sptr_ofs_bound ard)).
    exists ard'.
    (* Non-pc field loads survive the store at uso (other fields at uso + 8..48) *)
    assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some accu_v).
    { apply (load_after_store_other m m' sb uso (uso + 8) new_pc_ptr accu_v
               Hstore Haccu_load). right. lia. }
    assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
    { apply (load_after_store_other m m' sb uso (uso + 16) new_pc_ptr (Vptr sp_b sp_ofs)
               Hstore Hsp_load). right. lia. }
    assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m m' sb uso (uso + 24) new_pc_ptr env_v
               Hstore Henv_load). right. lia. }
    assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m m' sb uso (uso + 32) new_pc_ptr _
               Hstore Hextra_load). right. lia. }
    assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
    { apply (load_after_store_other m m' sb uso (uso + 40) new_pc_ptr gd_ptr
               Hstore Hgd_load). right. lia. }
    assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m m' sb uso (uso + 48) new_pc_ptr ts_ptr
               Hstore Hts_load). right. lia. }
    (* New PC field: load the stored value *)
    assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some new_pc_ptr).
    { pose proof (load_after_store_same m m' sb uso new_pc_ptr Hstore) as Htmp.
      unfold new_pc_ptr in Htmp |- *.
      simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp.
      replace (uso + 0)%Z with uso by lia.
      change (Ptrofs.repr (sizeof ge tint)) with (Ptrofs.repr 4).
      change (ptrofs_of_int Signed (Int.repr 1)) with (Ptrofs.of_ints (Int.repr 1)).
      exact Htmp. }
    (* le' ! _s = le ! _s since _s differs from _t'1 *)
    assert (Hle'_s : le' ! _s = Some (Vptr sb so)).
    { subst le'.
      rewrite (PTree.gso _ _ Hs_ne_t1).
      exact Hle_s. }
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
    + (* le' ! _s *) exact Hle'_s.
    + (* pc_rel *)
      exists new_pc_ptr. split. exact Hpc_load'.
      unfold pc_rel. simpl.
      unfold new_pc_ptr, new_co.
      f_equal.
      rewrite Ptrofs.sub_add_opp.
      rewrite Ptrofs.add_assoc.
      rewrite (Ptrofs.add_commut (Ptrofs.neg _) _).
      rewrite <- Ptrofs.sub_add_opp.
      rewrite Ptrofs.sub_idem.
      symmetry. apply Ptrofs.add_zero.
    + (* accu *)
      exists accu_v. split. exact Haccu_load'. simpl. exact Haccu_repr.
    + (* sp *)
      exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
      repeat split.
      * exact Hsp_load'.
      * apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb uso new_pc_ptr
                 Hstack_repr Hstore).
        intro Heq. exact (Hsp_ne_sb (eq_sym Heq)).
      * exact Hsp_ne_sb.
      * exact Hsp_ne_gb.
      * exact Hcb_ne_sp.
      * exact Hsp_ge8.
      * exact Hsp_rep.
      * intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsp_writable. exact Hofs'.
      * exact Hsp_align.
    + (* env *)
      exists env_v. split. exact Henv_load'. simpl. exact Henv_repr.
    + (* extra_args *)
      simpl. exact Hextra_load'.
    + (* global_data *)
      exists gd_ptr. split; [| split; [| split]]. exact Hgd_load'. simpl. exact Hgd_eq. simpl.
      apply (global_repr_store_other_block hm m m' _ _ _ sb uso new_pc_ptr
               Hglobal_repr Hstore).
      intro Heq2. exact (global_block_ne_sptr ard (eq_sym Heq2)).
      exact Hgb_ne_sb.
    + (* trap_sp *)
      exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel.
    + (* sb_writable *)
      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsb_writable. exact Hofs'. }
Qed.
