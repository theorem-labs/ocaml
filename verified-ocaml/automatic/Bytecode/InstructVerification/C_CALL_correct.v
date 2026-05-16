(* C_CALL_correct.v -- C_CALL handler correctness proof. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

(* ================================================================== *)
(* Composite env and struct layout                                     *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

(* Field offset fact for _pc (offset 0), using genv_cenv clight_ge
   directly so rewrites apply globally in the comp_eval_stmt term. *)
Local Lemma interp_state_co_pc : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full).
Proof.
  rewrite cenv_is_ce. eexists. split; reflexivity.
Qed.

(* ================================================================== *)
(* Helpers                                                             *)
(* ================================================================== *)

Local Lemma Mptr_eq : Mptr = Mint64.
Proof. unfold Mptr. rewrite ptr64_true. reflexivity. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

Lemma sem_add_pc_1 : forall cb pc_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr cb pc_ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr cb (Ptrofs.add pc_ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma sem_cast_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* clight_returns with code memory hypothesis                          *)
(* ================================================================== *)

Lemma C_CALLN_clight_returns :
  forall e le m (s : Machine.state) (ard : abs_rel_data),
  abs_rel_with_ard e le m s ard ->
  (exists nargs_val,
    Mem.load Mint32 m (ar_code_base_block ard)
      (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
         (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
    = Some (Vint nargs_val)) ->
  exists le' m',
    clight_returns f_instr_C_CALLN 3 e le m le' m'.
Proof.
  intros e le m s ard Hrel [nargs_val Hcode_load].

  set (sb := ar_sptr_block ard).
  set (so := ar_sptr_ofs ard).
  set (cb := ar_code_base_block ard).
  set (co := ar_code_base_ofs ard).

  unfold abs_rel_with_ard in Hrel.
  fold sb so cb co in Hrel.
  destruct Hrel as (Hle_s &
    [pc_ptr [Hpc_load Hpc_rel]] &
    _ & _ & _ & _ & _ & _ & Hsb_writable).

  unfold pc_rel in Hpc_rel. subst pc_ptr.
  rewrite Z.add_0_r in Hpc_load.

  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (code_block_ne_sptr ard) as Hcb_ne_sb. fold sb cb in Hcb_ne_sb.

  (* Fold ar_ accessors in Hcode_load *)
  fold cb co in Hcode_load.

  (* Abbreviate pc offset expressions *)
  remember (Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) as pc_ofs eqn:Hpc_ofs.
  remember (Ptrofs.add pc_ofs (Ptrofs.repr 4)) as pc_ofs_1 eqn:Hpc_ofs_1.

  (* Store 1: s->pc = _t'1 + 1, storing Vptr cb pc_ofs_1 at sb+0 *)
  assert (Hstore1 : exists m1,
    Mem.store Mint64 m sb (Ptrofs.unsigned so) (Vptr cb pc_ofs_1) = Some m1).
  { destruct (Mem.valid_access_store m Mint64 sb (Ptrofs.unsigned so) (Vptr cb pc_ofs_1)) as [m1 Hst].
    { pose proof (Mem.load_valid_access _ _ _ _ _ Hpc_load) as [? ?]. split; auto.
      intros ofs' Hofs'. apply Hsb_writable. unfold size_chunk in Hofs'. lia. }
    eauto. }
  destruct Hstore1 as [m1 Hstore1].

  (* Code load m1: code memory is in a different block, so load preserved *)
  assert (Hcode_load_m1 :
    Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) = Some (Vint nargs_val)).
  { erewrite Mem.load_store_other; [exact Hcode_load | exact Hstore1 |].
    left. exact Hcb_ne_sb. }

  (* Load s->pc from m1: we just stored pc_ofs_1 at the same location *)
  assert (Hpc_load_m1 :
    Mem.load Mint64 m1 sb (Ptrofs.unsigned so) = Some (Vptr cb pc_ofs_1)).
  { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore1) as H.
    rewrite load_result_vptr in H. exact H. }

  (* range_perm m1: store preserves permissions *)
  assert (Hrp_m1 : Mem.range_perm m1 sb (Ptrofs.unsigned so)
    (Ptrofs.unsigned so + 56) Cur Writable).
  { eapply sb_writable_after_store; eauto. }

  (* Store 2: s->pc = _t'2 + 1, storing Vptr cb pc_ofs_2 at sb+0 *)
  remember (Ptrofs.add pc_ofs_1 (Ptrofs.repr 4)) as pc_ofs_2 eqn:Hpc_ofs_2.
  assert (Hstore2 : exists m2,
    Mem.store Mint64 m1 sb (Ptrofs.unsigned so) (Vptr cb pc_ofs_2) = Some m2).
  { destruct (Mem.valid_access_store m1 Mint64 sb (Ptrofs.unsigned so) (Vptr cb pc_ofs_2)) as [m2 Hst].
    { pose proof (Mem.load_valid_access _ _ _ _ _ Hpc_load_m1) as [? ?]. split; auto.
      intros ofs' Hofs'. apply Hrp_m1. unfold size_chunk in Hofs'. lia. }
    eauto. }
  destruct Hstore2 as [m2 Hstore2].

  (* Build exec_stmt *)
  unfold clight_returns.
  exists (PTree.set _t'2 (Vptr cb pc_ofs_1)
           (PTree.set _nargs (Vint nargs_val)
             (PTree.set _t'1 (Vptr cb pc_ofs) le))).
  exists m2.

  apply (eval_stmt_to_exec clight_ge 20).
  eval_cbn.

  (* Resolve struct field lookups globally for the composite env. *)
  destruct interp_state_co_pc as [co_obj [Hco Hpc_offset]].

  (* S1: _t'1 = s->pc — read _s, resolve struct fields globally, load pc.
     The Hco/Hpc_offset/Mptr_eq/Ptrofs.add_zero rewrites are global and
     resolve ALL s->pc accesses (S1, S2, S4, S5) in one shot. *)
  rewrite Hle_s; eval_cbn.
  rewrite Hco; eval_cbn. rewrite Hpc_offset; eval_cbn.
  rewrite Mptr_eq. change (Ptrofs.repr 0) with Ptrofs.zero. rewrite !Ptrofs.add_zero.
  rewrite Hpc_load; eval_cbn.

  (* S2: s->pc = _t'1 + 1 *)
  rewrite PTree.gso by (compute; congruence).
  rewrite Hle_s; eval_cbn.
  (* Normalize pc field offset 0 in lvalue *)
  change (Ptrofs.repr 0) with Ptrofs.zero. rewrite ?Ptrofs.add_zero.
  (* Resolve rhs *)
  rewrite PTree.gss; eval_cbn.
  rewrite sem_add_pc_1; eval_cbn.
  rewrite sem_cast_ptr_tint; eval_cbn.
  (* comp_assign_loc now reduced, exposing Mem.store with Mptr *)
  rewrite Mptr_eq.
  subst pc_ofs_1.
  rewrite Hstore1; eval_cbn.

  (* S3: _nargs = *_t'1 — deref code memory via _t'1 pointer *)
  rewrite PTree.gss; eval_cbn.
  (* comp_deref_loc for *_t'1 has type tint, access_mode = By_value Mint32 *)
  subst pc_ofs.
  rewrite Hcode_load_m1; eval_cbn.

  (* S4: _t'2 = s->pc (in m1)
     Temp env: PTree.set _nargs ... (PTree.set _t'1 ... le)
     Need gso for _s != _nargs, _s != _t'1, then Hle_s *)
  rewrite PTree.gso by (compute; congruence).
  rewrite PTree.gso by (compute; congruence).
  rewrite Hle_s; eval_cbn.
  (* Normalize pc field offset 0 *)
  change (Ptrofs.repr 0) with Ptrofs.zero. rewrite ?Ptrofs.add_zero.
  (* Mptr from comp_deref_loc for _pc field (type tptr tint) *)
  rewrite Mptr_eq.
  rewrite Hpc_load_m1; eval_cbn.

  (* S5: s->pc = _t'2 + 1
     Temp env: PTree.set _t'2 ... (PTree.set _nargs ... (PTree.set _t'1 ... le))
     Lvalue reads _s: gso for _s != _t'2, _s != _nargs, _s != _t'1 *)
  rewrite PTree.gso by (compute; congruence).
  rewrite PTree.gso by (compute; congruence).
  rewrite PTree.gso by (compute; congruence).
  rewrite Hle_s; eval_cbn.
  (* Normalize pc field offset 0 in lvalue *)
  change (Ptrofs.repr 0) with Ptrofs.zero. rewrite ?Ptrofs.add_zero.
  (* Resolve rhs: _t'2 via gss *)
  rewrite PTree.gss; eval_cbn.
  rewrite sem_add_pc_1; eval_cbn.
  rewrite sem_cast_ptr_tint; eval_cbn.
  rewrite Mptr_eq.
  subst pc_ofs_2.
  rewrite Hstore2; eval_cbn.

  (* S6: return 3 *)
  reflexivity.
Qed.

(* ================================================================== *)
(* Body-outcome inversion: any successful exec_stmt of f_instr_C_CALLN  *)
(* must end with [Out_return (Some (Vint (Int.repr 3), tint))]. The     *)
(* body has no control flow other than the trailing [Sreturn 3], and   *)
(* every other statement is Sset or Sassign (both always [Out_normal]),*)
(* so the Sseq_2 (early-exit) branch is structurally impossible.       *)
(* ================================================================== *)

(* Sset and Sassign always produce [Out_normal]; pinned by inversion. *)
Lemma exec_Sset_is_normal : forall e le m id a t le' m' out,
  exec_stmt function_entry1 clight_ge e le m (Sset id a) t le' m' out ->
  out = Out_normal.
Proof. intros. inversion H; subst; reflexivity. Qed.

Lemma exec_Sassign_is_normal : forall e le m a1 a2 t le' m' out,
  exec_stmt function_entry1 clight_ge e le m (Sassign a1 a2) t le' m' out ->
  out = Out_normal.
Proof. intros. inversion H; subst; reflexivity. Qed.

Lemma eval_expr_Econst_int_inv : forall e le m n ty v,
  eval_expr clight_ge e le m (Econst_int n ty) v ->
  v = Vint n.
Proof.
  intros e le m n ty v Hev.
  inversion Hev; subst; [reflexivity |].
  (* eval_Elvalue case: requires eval_lvalue of Econst_int, which is impossible. *)
  match goal with H : eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ =>
    inversion H end.
Qed.

Lemma exec_Sreturn_const_int : forall e le m n t le' m' out,
  exec_stmt function_entry1 clight_ge e le m
    (Sreturn (Some (Econst_int n tint))) t le' m' out ->
  out = Out_return (Some (Vint n, tint)).
Proof.
  intros. inversion H; subst.
  match goal with He : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply eval_expr_Econst_int_inv in He end.
  subst. reflexivity.
Qed.

(* When [Ssequence s1 s2] succeeds and [s1] is forced into [Out_normal]
   for every successful execution, the overall outcome is the outcome
   of [s2]. *)
Lemma exec_Sseq_normal_first : forall e le m s1 s2 t le' m' out,
  exec_stmt function_entry1 clight_ge e le m (Ssequence s1 s2) t le' m' out ->
  (forall t' le0 m0 out0,
    exec_stmt function_entry1 clight_ge e le m s1 t' le0 m0 out0 ->
    out0 = Out_normal) ->
  exists t1 le1 m1 t2,
    exec_stmt function_entry1 clight_ge e le m s1 t1 le1 m1 Out_normal /\
    exec_stmt function_entry1 clight_ge e le1 m1 s2 t2 le' m' out.
Proof.
  intros e le m s1 s2 t le' m' out Hseq Hs1_normal.
  remember (Ssequence s1 s2) as stmt eqn:Hstmt.
  destruct Hseq; try (inversion Hstmt; fail).
  - (* exec_Sseq_1 *)
    inversion Hstmt; subst. eauto 8.
  - (* exec_Sseq_2 *)
    inversion Hstmt; subst.
    specialize (Hs1_normal _ _ _ _ Hseq).
    contradiction.
Qed.

Lemma C_CALL_body_outcome :
  forall e le m t le' m' out,
    exec_stmt function_entry1 clight_ge e le m (fn_body f_instr_C_CALLN)
      t le' m' out ->
    out = Out_return (Some (Vint (Int.repr 3), tint)).
Proof.
  intros e le m t le' m' out Hexec.
  cbn [fn_body f_instr_C_CALLN] in Hexec.
  (* Body = Ssequence A B
       A = Ssequence (Ssequence (Sset _t'1 _) (Sassign _ _)) (Sset _nargs _)
       B = Ssequence (Ssequence (Sset _t'2 _) (Sassign _ _))
                     (Sreturn (Some (Econst_int 3 tint))) *)
  apply exec_Sseq_normal_first in Hexec.
  2:{ intros t' le0 m0 out0 HA.
      apply exec_Sseq_normal_first in HA.
      2:{ intros t'' le1 m1 out1 HA1.
          apply exec_Sseq_normal_first in HA1.
          2:{ intros. eapply exec_Sset_is_normal; eauto. }
          destruct HA1 as [? [? [? [? [? HA1b]]]]].
          eapply exec_Sassign_is_normal; eauto. }
      destruct HA as [? [? [? [? [? HAb]]]]].
      eapply exec_Sset_is_normal; eauto. }
  destruct Hexec as [? [? [? [? [_ HB]]]]].
  apply exec_Sseq_normal_first in HB.
  2:{ intros t' le0 m0 out0 HBA.
      apply exec_Sseq_normal_first in HBA.
      2:{ intros. eapply exec_Sset_is_normal; eauto. }
      destruct HBA as [? [? [? [? [? HBAb]]]]].
      eapply exec_Sassign_is_normal; eauto. }
  destruct HB as [? [? [? [? [_ HRet]]]]].
  eapply exec_Sreturn_const_int; eauto.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem correct_C_CALL : forall nargs prim_idx,
  handler_correct (handle_instr (C_CALL nargs prim_idx)) (clight_of (C_CALL nargs prim_idx))
    (error_message_of (C_CALL nargs prim_idx))
    (pre_of (C_CALL nargs prim_idx)) (P_halt_of (C_CALL nargs prim_idx)) (P_ccall_of (C_CALL nargs prim_idx)).
Proof.
  intros nargs prim_idx.
  unfold handler_correct, handler_correct_gen.
  intros e le m s.
  simpl error_message_of.
  simpl handle_instr.
  unfold Handlers.handle_C_CALL.
  split.
  - reflexivity.
  - intros w Hrel Hpre.
    (* [Hpre] = [pre_of (C_CALL ...)] gives us an [exec_stmt] of the
       handler body for the specific [le] we received, with R_ex on the
       resulting [le', m'].  [pre_of_gen] pins the trace at [E0], and
       [C_CALL_body_outcome] forces the outcome to
       [Out_return (Vint 3)], so the witness IS already a valid
       [clight_returns f_instr_C_CALLN 3 e le m le' m']. *)
    unfold pre_of, pre_of_gen in Hpre.
    cbn [clight_of] in Hpre.
    specialize (Hpre le Hrel).
    destruct Hpre as [le' [m' [out [s'' [Hexec _]]]]].
    assert (Hout : out = Out_return (Some (Vint (Int.repr 3), tint)))
      by (eapply C_CALL_body_outcome; exact Hexec).
    rewrite Hout in Hexec.
    exists le', m'.
    unfold clight_returns.
    exact Hexec.
Qed.
