(* BRANCH_correct.v -- BRANCH handler completeness proof.

   The C body reads the branch offset from *(s->pc), computes
   s->pc = s->pc + offset (pointer arithmetic), and returns 0.
   The Rocq handler is: handle_BRANCH target s = Step (s <|pc := target|>).

   Since BRANCH ignores pc' (it jumps to target), the spec wraps
   the handler: fun _ s => handle_BRANCH target s.

   The postcondition abs_rel for s <|pc := target|> needs pc_rel
   with the new PC.  Since ar_code_base_block/ar_code_base_ofs are
   existentially quantified in abs_rel and no other field depends on
   them, we construct a new ard' for the postcondition with adjusted
   code base so that pc_rel holds for the C-computed new PC and the
   Rocq target. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
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
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul Ptrofs.sub
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* store_pc_succeeds: proved from store_succeeds_sb                    *)
(* ================================================================== *)

(* The struct PC field is writable (needed for the store).
   Proved by calling store_succeeds_sb with offset 0. *)
Lemma store_pc_succeeds : forall m sb so_ptrofs v_new,
  Mem.range_perm m sb (Ptrofs.unsigned so_ptrofs) (Ptrofs.unsigned so_ptrofs + 56) Cur Writable ->
  (exists v_old, Mem.load Mint64 m sb (Ptrofs.unsigned so_ptrofs + 0) = Some v_old) ->
  exists m', Mem.store Mint64 m sb (Ptrofs.unsigned so_ptrofs + 0) v_new = Some m'.
Proof.
  intros m sb so_ptrofs v_new Hrp [v_old Hload].
  exact (store_succeeds_sb m sb so_ptrofs 0 v_old Hrp Hload ltac:(lia) ltac:(lia) v_new).
Qed.

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

Lemma interp_state_pc_co : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full).
Proof.
  rewrite cenv_is_ce. exact pc_field_offset.
Qed.

(* ================================================================== *)
(* Pointer arithmetic helpers                                          *)
(* ================================================================== *)

Lemma ptrofs_add_zero : forall ofs,
  Ptrofs.add ofs (Ptrofs.repr 0) = ofs.
Proof.
  intros. change (Ptrofs.repr 0) with Ptrofs.zero.
  apply Ptrofs.add_zero.
Qed.

(* sem_cast for (tptr tint) -> (tptr tint) is identity for Vptr *)
Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_BRANCH_correct : forall target,
    handler_correct (fun _ s => handle_BRANCH target s) f_instr_BRANCH
      (fun _ m s ard =>
         exists v, Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint v))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intro target.
  intros e le m s.
  unfold handler_correct, handle_BRANCH. simpl.
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
  unfold pc_rel in Hpc_rel.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.
  subst pc_ptr.
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  destruct interp_state_pc_co as [co_is [Hco Hpc_offset]].
  (* Get the code buffer value from the step precondition *)
  destruct Hstep_pre as [branch_ofs Hcode_load].
  (* Compute the new PC value: old_pc + branch_ofs (pointer + int) *)
  set (new_pc_ptr := Vptr cb
    (Ptrofs.add pc_ofs
       (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                   (ptrofs_of_int Signed branch_ofs)))).
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
  assert (Hs_ne_t2 : _s <> _t'2) by (unfold _s, _t'2; congruence).
  assert (Hs_ne_t3 : _s <> _t'3) by (unfold _s, _t'3; congruence).
  assert (Ht1_ne_t3 : _t'1 <> _t'3) by (unfold _t'1, _t'3; congruence).
  assert (Ht1_ne_t2 : _t'1 <> _t'2) by (unfold _t'1, _t'2; congruence).
  (* The C body modifies the temp env *)
  set (le' := PTree.set _t'3 (Vint branch_ofs)
                (PTree.set _t'2 (Vptr cb pc_ofs)
                   (PTree.set _t'1 (Vptr cb pc_ofs) le))).
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
    (* First load of s->pc field *)
    rewrite Mptr_Mint64.
    rewrite (ptrofs_add_zero so).
    rewrite Hpc_load_uso; eval_cbn.
    (* _s lookup in (set _t'1 ... le) *)
    rewrite (PTree.gso _ _ Hs_ne_t1).
    rewrite Hle_s; eval_cbn.
    (* Second load of s->pc from struct *)
    rewrite Mptr_Mint64.
    rewrite (ptrofs_add_zero so).
    rewrite Hpc_load_uso; eval_cbn.
    (* _t'2 lookup via get-set-same *)
    rewrite (PTree.gss); eval_cbn.
    (* Code buffer dereference: Mem.load Mint32 *)
    rewrite Hcode_load; eval_cbn.
    (* _s lookup in (set _t'3 (set _t'2 (set _t'1 le))) for Sassign target *)
    rewrite (PTree.gso _ _ Hs_ne_t3).
    rewrite (PTree.gso _ _ Hs_ne_t2).
    rewrite (PTree.gso _ _ Hs_ne_t1).
    rewrite Hle_s; eval_cbn.
    (* _t'1 lookup *)
    rewrite (PTree.gso _ _ Ht1_ne_t3).
    rewrite (PTree.gso _ _ Ht1_ne_t2).
    rewrite (PTree.gss); eval_cbn.
    (* _t'3 lookup *)
    rewrite (PTree.gss); eval_cbn.
    (* sem_binary_operation: ptr + int *)
    unfold sem_binary_operation, sem_add.
    change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
    unfold sem_add_ptr_int. eval_cbn.
    (* sem_cast (tptr tint) -> (tptr tint) *)
    rewrite sem_cast_ptr_tint_to_ptr_tint; eval_cbn.
    (* Store to s->pc *)
    rewrite Mptr_Mint64.
    rewrite (ptrofs_add_zero so).
    change (Ptrofs.repr 4) with (Ptrofs.repr (sizeof ge tint)).
    fold new_pc_ptr.
    rewrite Hstore; eval_cbn.
    subst le'. reflexivity.
  - (* Part 2: abs_rel on post-state (s <|pc := target|>) *)
    set (uso := Ptrofs.unsigned so) in *.
    (* Construct new ard' with adjusted code base offset *)
    set (new_pc_ofs := Ptrofs.add pc_ofs
       (Ptrofs.mul (Ptrofs.repr (sizeof ge tint))
                   (ptrofs_of_int Signed branch_ofs))).
    set (new_co := Ptrofs.sub new_pc_ofs (Ptrofs.repr (target * sizeof_code_t))).
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
      change (ptrofs_of_int Signed branch_ofs) with (Ptrofs.of_ints branch_ofs).
      exact Htmp. }
    (* le' ! _s = le ! _s since _s differs from _t'1, _t'2, _t'3 *)
    assert (Hle'_s : le' ! _s = Some (Vptr sb so)).
    { subst le'.
      rewrite (PTree.gso _ _ Hs_ne_t3).
      rewrite (PTree.gso _ _ Hs_ne_t2).
      rewrite (PTree.gso _ _ Hs_ne_t1).
      exact Hle_s. }
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
    + (* le' ! _s *) exact Hle'_s.
    + (* pc_rel *)
      exists new_pc_ptr. split. exact Hpc_load'.
      unfold pc_rel. simpl.
      unfold new_pc_ptr, new_co.
      f_equal.
      (* new_co + target * sct = new_pc_ofs - target*sct + target*sct = new_pc_ofs *)
      rewrite Ptrofs.sub_add_opp.
      rewrite Ptrofs.add_assoc.
      rewrite (Ptrofs.add_commut (Ptrofs.neg _) _).
      rewrite <- Ptrofs.sub_add_opp.
      rewrite Ptrofs.sub_idem.
      symmetry. apply Ptrofs.add_zero.
    + (* accu *)
      exists accu_v. split. exact Haccu_load'. simpl. eapply val_repr_co_shift. exact Haccu_repr.
    + (* sp *)
      exists (Vptr sp_b sp_ofs), sp_b, sp_ofs. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      exact Hsp_load'. reflexivity. simpl.
      eapply stack_repr_co_shift.
      apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb uso new_pc_ptr
               Hstack_repr Hstore).
      intro Heq. exact (Hsp_ne_sb (eq_sym Heq)).
      exact Hsp_ne_sb. exact Hsp_ne_gb. exact Hcb_ne_sp.
        exact Hsp_ge8.
        exact Hsp_rep.
        intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsp_writable. exact Hofs'.
        exact Hsp_align.
    + (* env *)
      exists env_v. split. exact Henv_load'. simpl. eapply val_repr_co_shift. exact Henv_repr.
    + (* extra_args *)
      simpl. exact Hextra_load'.
    + (* global_data *)
      exists gd_ptr. split; [| split; [| split]]. exact Hgd_load'. simpl. exact Hgd_eq. simpl.
      eapply global_repr_co_shift.
      apply (global_repr_store_other_block hm cb co m m' _ _ _ sb uso new_pc_ptr
               Hglobal_repr Hstore).
      intro Heq2. exact (global_block_ne_sptr ard (eq_sym Heq2)).
      exact Hgb_ne_sb.
    + (* trap_sp *)
      exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel.
    + (* 9. sb_writable *)
      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsb_writable. exact Hofs'. }
Qed.

(* Wrapper with building-block precondition for Module Type *)
Theorem verify_BRANCH_handler_correct : forall target,
    handler_correct (fun _ s => handle_BRANCH target s) f_instr_BRANCH
      code_loadable
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros target.
  eapply handler_correct_weaken.
  - exact (verify_BRANCH_correct target).
  - intros e le m s ard _ Hcl. exact Hcl.
Qed.
