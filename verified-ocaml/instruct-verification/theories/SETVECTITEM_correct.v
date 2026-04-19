(* SETVECTITEM_correct.v -- SETVECTITEM correctness proof.

   SETVECTITEM: pops idx and newval from stack, writes newval to
   heap block accu[idx] via caml_modify, sets accu = val_unit,
   pops 2 stack entries.

   C handler calls caml_modify externally. The bigstep proof is
   constructed manually (Scall cannot be handled computationally).

   NO AXIOMS. *)

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

(* ================================================================== *)
(* Semantic lemmas                                                     *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma sem_cast_tlong_tlong_vlong : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof. intros. unfold sem_cast. simpl classify_cast. rewrite ptr64_true. reflexivity. Qed.

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

Local Lemma sem_add_ptr_tlong_idx : forall b ofs idx m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vlong idx) tlong m
  = Some (Vptr b (Ptrofs.add ofs
            (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 idx)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tlong) with (add_case_pl tlong).
  unfold sem_add_ptr_long. reflexivity.
Qed.

Local Lemma sem_add_sp_2 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 2)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma shr_tagged_int : forall idx,
  0 <= idx -> idx * 2 + 1 <= Int64.max_signed ->
  Int64.shr (Int64.repr (idx * 2 + 1)) (Int64.repr 1) = Int64.repr idx.
Proof.
  intros idx Hge Hlt. unfold Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Int64.signed_repr by (split; [pose proof Int64.min_signed_neg; lia | exact Hlt]).
  rewrite Z.shiftr_div_pow2 by lia. change (2^1)%Z with 2%Z.
  rewrite Z.div_add_l by lia. change (1 / 2)%Z with 0%Z. f_equal. lia.
Qed.

Local Lemma ptrofs_mul_8_of_int64 : forall idx,
  0 <= idx -> idx < Ptrofs.half_modulus ->
  Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr idx))
  = Ptrofs.repr (idx * 8).
Proof.
  intros idx Hge Hlt.
  change Ptrofs.half_modulus with (2^63)%Z in Hlt.
  unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr.
  2: { change Int64.max_unsigned with (2^64 - 1)%Z. lia. }
  unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 8).
  2: { change Ptrofs.max_unsigned with (2^64 - 1)%Z. lia. }
  rewrite Ptrofs.unsigned_repr.
  2: { change Ptrofs.max_unsigned with (2^64 - 1)%Z. lia. }
  f_equal. lia.
Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* ================================================================== *)
(* caml_modify definitions                                             *)
(* ================================================================== *)

Local Definition caml_modify_ef : external_function :=
  EF_external "caml_modify"
    (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid cc_default).

Local Definition caml_modify_fundef : Ctypes.fundef function :=
  Ctypes.External caml_modify_ef ((tptr tlong) :: tlong :: nil) tvoid cc_default.

(* ================================================================== *)
(* Precondition                                                        *)
(* ================================================================== *)

Definition setvectitem_pre
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let gb := ar_global_block ard in
  forall idx newval rest,
    s.(Machine.stack) = Val_int idx :: newval :: rest ->
    (* Index bounds *)
    0 <= idx /\
    idx * 2 + 1 <= Int64.max_signed /\
    idx < Ptrofs.half_modulus /\
    (* Index C representation is Vlong (rules out vr_code_ptr) *)
    int_vlong ard idx /\
    (* Genv requirements *)
    e ! _caml_modify = None /\
    (exists b_cm,
       Genv.find_symbol ge _caml_modify = Some b_cm /\
       Genv.find_funct ge (Vptr b_cm Ptrofs.zero) = Some caml_modify_fundef) /\
    (* caml_modify call and its effects *)
    (forall accu_v newval_cv,
       val_repr hm cb co (Machine.accu s) accu_v ->
       val_repr hm cb co newval newval_cv ->
       exists hb hofs,
         accu_v = Vptr hb hofs /\
         hb <> sb /\ hb <> gb /\
         (* hb is also separate from any sp_b obtained from abs_rel *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
            hb <> sp_b) /\
         exists m_cm,
           external_call caml_modify_ef ge
             (Vptr hb (Ptrofs.add hofs (Ptrofs.repr (idx * 8)))
              :: newval_cv :: nil)
             m E0 Vundef m_cm /\
           (* Struct block loads preserved *)
           (forall ofs v,
              Mem.load Mint64 m sb ofs = Some v ->
              Mem.load Mint64 m_cm sb ofs = Some v) /\
           (* Struct block stores succeed *)
           (forall ofs v_old v_new,
              Mem.load Mint64 m sb ofs = Some v_old ->
              exists m', Mem.store Mint64 m_cm sb ofs v_new = Some m') /\
           (* Loads on blocks other than hb are preserved *)
           (forall b ofs v,
              b <> hb ->
              Mem.load Mint64 m b ofs = Some v ->
              Mem.load Mint64 m_cm b ofs = Some v) /\
           (* Permission preservation *)
           (forall b ofs k p,
              Mem.valid_block m b -> Mem.perm m b ofs k p ->
              Mem.perm m_cm b ofs k p) /\
           (* global_repr preserved *)
           (global_repr hm cb co m_cm (Machine.global s) gb (ar_global_ofs ard))).

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_SETVECTITEM_correct :
    handler_correct handle_SETVECTITEM f_instr_SETVECTITEM
      (fun e m s ard => setvectitem_pre e m s ard)
      (fun _ s => match s.(Machine.stack) with
                  | Val_int idx :: newval :: _ =>
                    match s.(Machine.accu) with
                    | Val_ptr addr =>
                      match heap_lookup s.(Machine.hp) addr with
                      | Some (_, fields) => set_nth fields (Z.to_nat idx) newval = None
                      | None => True
                      end
                    | _ => True
                    end
                  | _ => True end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_SETVECTITEM.

  destruct (Machine.stack s) as [| v_hd stk1] eqn:Hstk.
  { reflexivity. }
  destruct v_hd as [idx | | |].
  2-4: reflexivity.
  destruct stk1 as [| newval rest].
  { reflexivity. }
  destruct (Machine.accu s) as [z_val|blk_tag blk_flds|addr|clo_addr clo_ofs] eqn:Haccu_eq;
    try exact I.
  destruct (heap_lookup (Machine.hp s) addr) as [[tag fields]|] eqn:Hlookup.
  2: { exact I. }
  destruct (set_nth fields (Z.to_nat idx) newval) as [new_fields|] eqn:Hset.
  2: { simpl. reflexivity. }

  (* ================================================================ *)
  (* Step case                                                         *)
  (* ================================================================ *)
  intros ard Hpre Hstep_pre.
  unfold abs_rel_with_ard in Hpre.

  set (sb := ar_sptr_block ard) in *.
  set (so := ar_sptr_ofs ard) in *.
  set (hm := ar_heap_map ard) in *.
  set (cb := ar_code_base_block ard) in *.
  set (co := ar_code_base_ofs ard) in *.
  set (gb := ar_global_block ard) in *.
  set (go := ar_global_ofs ard) in *.

  destruct Hpre as (Hle_s &
    [pc_ptr [Hpc_load Hpc_rel]] &
    [accu_v [Haccu_load Haccu_repr]] &
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
    [env_v [Henv_load Henv_repr]] &
    Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
    [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
  subst sp_ptr gd_ptr.

  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  pose proof (code_block_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

  (* Extract stack elements from stack_repr *)
  rewrite Hstk in Hstack_repr.
  inversion Hstack_repr as [| ? ? ? ? cv_idx Hload_sp0 Hval_repr_idx Hstack_repr1].
  subst.
  inversion Hstack_repr1 as [| ? ? ? ? newval_cv Hload_sp1 Hval_repr_newval Hstack_repr_rest].
  revert Hgd_load Hglobal_repr Hgb_ne_sb.
  subst. intros Hgd_load Hglobal_repr Hgb_ne_sb.

  (* Stack bounds *)
  assert (Hsp_mod_orig : Ptrofs.unsigned sp_ofs + 16 < Ptrofs.modulus).
  { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }
  assert (Hsp_rep_tail : Ptrofs.unsigned sp_ofs + 16 + 8 * Z.of_nat (length rest) < Ptrofs.modulus).
  { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }

  (* Use step precondition *)
  unfold setvectitem_pre in Hstep_pre.
  destruct (Hstep_pre idx newval rest Hstk)
    as (Hidx_ge & Hidx_signed & Hidx_ptrofs & Hidx_vlong &
        He_caml & [b_cm [Hfind_symbol Hfind_funct]] & Hcm_pre).

  (* Stack head is Val_int idx *)
  inversion Hval_repr_idx; subst cv_idx.
  2: { (* vr_code_ptr case: Val_int idx represented as Vptr, but int_vlong says Vlong *)
       exfalso.
       unfold int_vlong in Hidx_vlong.
       destruct (Hidx_vlong _ Hval_repr_idx) as [z Hz].
       discriminate Hz. }

  destruct (Hcm_pre accu_v newval_cv Haccu_repr Hval_repr_newval)
    as (hb & hofs & Haccu_is_ptr & Hhb_ne_sb & Hhb_ne_gb &
        Hhb_ne_sp & m_cm & Hext_call & Hcm_sb_loads & Hcm_sb_stores &
        Hcm_other_loads & Hcm_perm_preserved & Hcm_global_repr).
  subst accu_v.

  (* sp_b <> hb from precondition *)
  assert (Hsp_ne_hb : sp_b <> hb).
  { intro Heq. apply (Hhb_ne_sp sp_b sp_ofs Hsp_load). exact (eq_sym Heq). }

  (* Arithmetic *)
  assert (Hshr_idx : Int64.shr (Int64.repr (idx * 2 + 1)) (Int64.repr 1) = Int64.repr idx).
  { apply shr_tagged_int; assumption. }
  assert (Hptrofs_mul : Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr idx))
                        = Ptrofs.repr (idx * 8)).
  { apply ptrofs_mul_8_of_int64; assumption. }

  (* ============================================================ *)
  (* Stores                                                        *)
  (* ============================================================ *)

  (* Store 1: accu field at (sb, uso+8) <- val_unit *)
  set (unit_v := Vlong (Int64.repr 1)).
  destruct (Hcm_sb_stores (Ptrofs.unsigned so + 8) (Vptr hb hofs) unit_v Haccu_load)
    as [m1 Hstore1].

  set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).

  (* sp load in m_cm *)
  assert (Hsp_load_m_cm : Mem.load Mint64 m_cm sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b sp_ofs)).
  { apply Hcm_sb_loads. exact Hsp_load. }

  (* sp load in m1 *)
  assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b sp_ofs)).
  { apply (load_after_store_other m_cm m1 sb
             (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 16)
             unit_v (Vptr sp_b sp_ofs)
             Hstore1 Hsp_load_m_cm). right. lia. }

  (* sb_writable in m_cm *)
  assert (Hsb_writable_m_cm :
    Mem.range_perm m_cm sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs' Hofs'.
    apply Hcm_perm_preserved.
    - eapply Mem.perm_valid_block. apply Hsb_writable. exact Hofs'.
    - apply Hsb_writable. exact Hofs'. }
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable_m_cm) as Hsb_writable_m1.

  (* Store 2: sp field at (sb, uso+16) <- new_sp_v *)
  destruct (store_succeeds_sb m1 sb so 16 (Vptr sp_b sp_ofs)
             Hsb_writable_m1 Hsp_load_m1 ltac:(lia) ltac:(lia) new_sp_v)
    as [m2 Hstore2].

  (* ============================================================ *)
  (* Field loads threaded through stores                           *)
  (* ============================================================ *)
  set (uso := Ptrofs.unsigned so) in *.

  (* pc load in m_cm, m1, m2 *)
  assert (Hpc_load_m_cm : Mem.load Mint64 m_cm sb (uso + 0) = Some pc_ptr).
  { apply Hcm_sb_loads. exact Hpc_load. }
  assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some pc_ptr).
  { apply (load_after_store_other m_cm m1 sb (uso + 8) (uso + 0)
             unit_v pc_ptr Hstore1 Hpc_load_m_cm). left. lia. }
  assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (uso + 0) = Some pc_ptr).
  { apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 0)
             new_sp_v pc_ptr Hstore2 Hpc_load_m1). left. lia. }

  (* accu load in m1 = unit_v (written by store1) *)
  assert (Haccu_m1 : Mem.load Mint64 m1 sb (uso + 8) = Some unit_v).
  { pose proof (load_after_store_same m_cm m1 sb (uso + 8) unit_v Hstore1) as Htmp.
    subst unit_v. rewrite load_result_vlong in Htmp. exact Htmp. }
  assert (Haccu_m2 : Mem.load Mint64 m2 sb (uso + 8) = Some unit_v).
  { apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 8)
             new_sp_v unit_v Hstore2 Haccu_m1). left. lia. }

  (* sp load in m2 (written by store2) *)
  assert (Hsp_m2 : Mem.load Mint64 m2 sb (uso + 16) = Some new_sp_v).
  { pose proof (load_after_store_same m1 m2 sb (uso + 16) new_sp_v Hstore2) as Htmp.
    subst new_sp_v. rewrite load_result_vptr in Htmp. exact Htmp. }

  (* env load threaded through *)
  assert (Henv_m_cm : Mem.load Mint64 m_cm sb (uso + 24) = Some env_v).
  { apply Hcm_sb_loads. exact Henv_load. }
  assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
  { apply (load_after_store_other m_cm m1 sb (uso + 8) (uso + 24)
             unit_v env_v Hstore1 Henv_m_cm). right. lia. }
  assert (Henv_m2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
  { apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 24)
             new_sp_v env_v Hstore2 Henv_m1). right. lia. }

  (* extra_args load threaded through *)
  assert (Hextra_m_cm : Mem.load Mint64 m_cm sb (uso + 32) =
           Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
  { apply Hcm_sb_loads. exact Hextra_load. }
  assert (Hextra_m1 : Mem.load Mint64 m1 sb (uso + 32) =
           Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
  { apply (load_after_store_other m_cm m1 sb (uso + 8) (uso + 32)
             unit_v _ Hstore1 Hextra_m_cm). right. lia. }
  assert (Hextra_m2 : Mem.load Mint64 m2 sb (uso + 32) =
           Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
  { apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 32)
             new_sp_v _ Hstore2 Hextra_m1). right. lia. }

  (* global_data load threaded through *)
  assert (Hgd_m_cm : Mem.load Mint64 m_cm sb (uso + 40) = Some (Vptr gb go)).
  { apply Hcm_sb_loads. exact Hgd_load. }
  assert (Hgd_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some (Vptr gb go)).
  { apply (load_after_store_other m_cm m1 sb (uso + 8) (uso + 40)
             unit_v (Vptr gb go) Hstore1 Hgd_m_cm). right. lia. }
  assert (Hgd_m2 : Mem.load Mint64 m2 sb (uso + 40) = Some (Vptr gb go)).
  { apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 40)
             new_sp_v (Vptr gb go) Hstore2 Hgd_m1). right. lia. }

  (* trap_sp load threaded through *)
  assert (Hts_m_cm : Mem.load Mint64 m_cm sb (uso + 48) = Some ts_ptr).
  { apply Hcm_sb_loads. exact Hts_load. }
  assert (Hts_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
  { apply (load_after_store_other m_cm m1 sb (uso + 8) (uso + 48)
             unit_v ts_ptr Hstore1 Hts_m_cm). right. lia. }
  assert (Hts_m2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
  { apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 48)
             new_sp_v ts_ptr Hstore2 Hts_m1). right. lia. }

  (* accu_load in m_cm (needed for bigstep derivation) *)
  assert (Haccu_load_m_cm : Mem.load Mint64 m_cm sb (uso + 8) = Some (Vptr hb hofs)).
  { apply Hcm_sb_loads. exact Haccu_load. }

  (* sp_b stack loads in m_cm: sp_b <> hb, so loads preserved *)
  assert (Hload_sp0_cm : Mem.load Mint64 m_cm sp_b (Ptrofs.unsigned sp_ofs) =
            Some (Vlong (Int64.repr (idx * 2 + 1)))).
  { apply Hcm_other_loads. exact Hsp_ne_hb. exact Hload_sp0. }
  assert (Hload_sp1_cm : Mem.load Mint64 m_cm sp_b (Ptrofs.unsigned sp_ofs + 8) =
            Some newval_cv).
  { apply Hcm_other_loads. exact Hsp_ne_hb.
    rewrite <- (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)).
    exact Hload_sp1. }

  (* ============================================================ *)
  (* stack_repr preservation through m -> m_cm -> m1 -> m2        *)
  (* ============================================================ *)

  (* First, equate the two offset representations *)
  assert (Hofs_eq : Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8)
                    = Ptrofs.add sp_ofs (Ptrofs.repr 16)).
  { rewrite Ptrofs.add_assoc. f_equal. }

  rewrite Hofs_eq in Hstack_repr_rest.

  assert (Hstack_repr_cm : stack_repr hm cb co m_cm rest sp_b
            (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
  { clear -Hstack_repr_rest Hcm_other_loads Hsp_ne_hb.
    revert Hstack_repr_rest.
    generalize (Ptrofs.add sp_ofs (Ptrofs.repr 16)) as sp_ofs'.
    induction rest as [| v stk IH]; intros sp_ofs' Hsr.
    - constructor.
    - inversion Hsr; subst.
      econstructor.
      + apply Hcm_other_loads. exact Hsp_ne_hb. exact H1.
      + exact H2.
      + apply IH. exact H5. }

  assert (Hstack_repr_m1 : stack_repr hm cb co m1 rest sp_b
            (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
  { apply (stack_repr_store_other_block hm cb co m_cm m1 _ sp_b
             (Ptrofs.add sp_ofs (Ptrofs.repr 16)) sb (uso + 8) unit_v
             Hstack_repr_cm Hstore1).
    intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }

  assert (Hstack_repr_m2 : stack_repr hm cb co m2 rest sp_b
            (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
  { apply (stack_repr_store_other_block hm cb co m1 m2 _ sp_b
             (Ptrofs.add sp_ofs (Ptrofs.repr 16)) sb (uso + 16) new_sp_v
             Hstack_repr_m1 Hstore2).
    intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }

  (* ============================================================ *)
  (* global_repr preservation through m_cm -> m1 -> m2            *)
  (* ============================================================ *)
  assert (Hglobal_m1 : global_repr hm cb co m1 (Machine.global s) gb go).
  { apply (global_repr_store_other_block hm cb co m_cm m1 _ gb go sb (uso + 8) unit_v
             Hcm_global_repr Hstore1).
    intro Heq; exact (Hgb_ne (eq_sym Heq)). }

  assert (Hglobal_m2 : global_repr hm cb co m2 (Machine.global s) gb go).
  { apply (global_repr_store_other_block hm cb co m1 m2 _ gb go sb (uso + 16) new_sp_v
             Hglobal_m1 Hstore2).
    intro Heq; exact (Hgb_ne (eq_sym Heq)). }

  (* ============================================================ *)
  (* sb_writable in m2                                             *)
  (* ============================================================ *)
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore2 Hsb_writable_m1) as Hsb_writable_m2.

  (* ============================================================ *)
  (* Temp env setup                                                *)
  (* ============================================================ *)
  set (le1 := PTree.set _t'2 (Vptr hb hofs) le).
  set (le2 := PTree.set _t'3 (Vptr sp_b sp_ofs) le1).
  set (le3 := PTree.set _t'4 (Vlong (Int64.repr (idx * 2 + 1))) le2).
  set (le4 := PTree.set _t'5 (Vptr sp_b sp_ofs) le3).
  set (le5 := PTree.set _t'6 newval_cv le4).
  set (le6 := le5).  (* Scall with optid=None doesn't change le *)
  set (le7 := PTree.set _t'1 (Vptr sp_b sp_ofs) le6).

  exists le7. exists m2.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ================================================================ *)
  (* Part 1: exec_stmt derivation                                     *)
  (* ================================================================ *)
  {
    (* Body structure from f_instr_SETVECTITEM:
       Ssequence
         (Ssequence                          -- Part A: reads + caml_modify
           (Sset _t'2 s->accu)
           (Ssequence
             (Sset _t'3 s->sp)
             (Ssequence
               (Sset _t'4 deref(_t'3 + 0))
               (Ssequence
                 (Sset _t'5 s->sp)
                 (Ssequence
                   (Sset _t'6 deref(_t'5 + 1))
                   (Scall None caml_modify [cast accu ptr + shr idx 1; newval]))))))
         (Ssequence                          -- Part B: assign accu, sp, return
           (Sassign s->accu val_unit_expr)
           (Ssequence
             (Ssequence
               (Sset _t'1 s->sp)
               (Sassign s->sp (_t'1 + 2)))
             (Sreturn 0))) *)

    apply exec_Sseq_1 with (t1 := E0) (le1 := le6) (m1 := m_cm).

    (* -- Part A: reads + caml_modify call -- *)
    {
      (* Sset _t'2 (s->accu) ; rest *)
      apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m).
      {
        apply exec_Sset.
        eapply eval_Elvalue.
        - eapply eval_Efield_struct.
          + eapply eval_Elvalue.
            * eapply eval_Ederef. eapply eval_Etempvar. exact Hle_s.
            * apply deref_loc_copy. simpl. reflexivity.
          + simpl. reflexivity.
          + exact Hco.
          + exact Haccu_offset.
        - apply deref_loc_value with (chunk := Mint64).
          * simpl. reflexivity.
          * simpl. rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
            exact Haccu_load.
      }

      (* Sset _t'3 (s->sp) ; rest *)
      apply exec_Sseq_1 with (t1 := E0) (le1 := le2) (m1 := m).
      {
        apply exec_Sset.
        eapply eval_Elvalue.
        - eapply eval_Efield_struct.
          + eapply eval_Elvalue.
            * eapply eval_Ederef. eapply eval_Etempvar.
              subst le1. rewrite PTree.gso by (compute; congruence). exact Hle_s.
            * apply deref_loc_copy. simpl. reflexivity.
          + simpl. reflexivity.
          + exact Hco.
          + exact Hsp_offset.
        - apply deref_loc_value with (chunk := Mptr).
          * simpl. reflexivity.
          * simpl. rewrite Mptr_Mint64.
            rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
            exact Hsp_load.
      }

      (* Sset _t'4 deref(_t'3 + 0) ; rest *)
      apply exec_Sseq_1 with (t1 := E0) (le1 := le3) (m1 := m).
      {
        apply exec_Sset.
        eapply eval_Elvalue.
        - eapply eval_Ederef.
          eapply eval_Ebinop.
          + eapply eval_Etempvar.
            subst le2. rewrite PTree.gss. reflexivity.
          + apply eval_Econst_int.
          + apply sem_add_sp_0.
        - apply deref_loc_value with (chunk := Mint64).
          * simpl. reflexivity.
          * simpl. exact Hload_sp0.
      }

      (* Sset _t'5 (s->sp) ; rest *)
      apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m).
      {
        apply exec_Sset.
        eapply eval_Elvalue.
        - eapply eval_Efield_struct.
          + eapply eval_Elvalue.
            * eapply eval_Ederef. eapply eval_Etempvar.
              subst le3 le2 le1.
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gso by (compute; congruence).
              exact Hle_s.
            * apply deref_loc_copy. simpl. reflexivity.
          + simpl. reflexivity.
          + exact Hco.
          + exact Hsp_offset.
        - apply deref_loc_value with (chunk := Mptr).
          * simpl. reflexivity.
          * simpl. rewrite Mptr_Mint64.
            rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
            exact Hsp_load.
      }

      (* Sset _t'6 deref(_t'5 + 1) ; Scall *)
      apply exec_Sseq_1 with (t1 := E0) (le1 := le5) (m1 := m).
      {
        apply exec_Sset.
        eapply eval_Elvalue.
        - eapply eval_Ederef.
          eapply eval_Ebinop.
          + eapply eval_Etempvar.
            subst le4. rewrite PTree.gss. reflexivity.
          + apply eval_Econst_int.
          + apply sem_add_sp_1.
        - apply deref_loc_value with (chunk := Mint64).
          * simpl. reflexivity.
          * simpl. exact Hload_sp1.
      }

      (* Scall None caml_modify [accu_ptr + (idx >> 1); newval] *)
      {
        eapply exec_Scall with
          (tyargs := (tptr tlong) :: tlong :: nil)
          (tyres := tvoid)
          (cconv := cc_default)
          (vargs := Vptr hb (Ptrofs.add hofs (Ptrofs.repr (idx * 8)))
                    :: newval_cv :: nil)
          (vres := Vundef).
        - (* classify_fun *)
          simpl. reflexivity.
        - (* eval_expr for Evar _caml_modify *)
          eapply eval_Elvalue.
          + eapply eval_Evar_global.
            * exact He_caml.
            * exact Hfind_symbol.
          + apply deref_loc_reference. simpl. reflexivity.
        - (* eval_exprlist *)
          econstructor.
          + (* arg1: cast(accu, ptr) + shr(idx, 1) *)
            eapply eval_Ebinop.
            * eapply eval_Ecast.
              eapply eval_Etempvar.
              subst le5 le4 le3 le2 le1.
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gss. reflexivity.
              { apply sem_cast_long_to_ptr_vptr. }
            * eapply eval_Ebinop.
              { eapply eval_Ecast.
                eapply eval_Etempvar.
                subst le5 le4 le3.
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gss. reflexivity.
                { apply sem_cast_tlong_tlong_vlong. } }
              { apply eval_Econst_int. }
              { apply sem_shr_long_int_1. }
            * rewrite Hshr_idx.
              pose proof (sem_add_ptr_tlong_idx hb hofs (Int64.repr idx) m) as Htmp.
              rewrite Hptrofs_mul in Htmp. exact Htmp.
          + (* sem_cast for arg1 *)
            simpl. apply sem_cast_ptr_to_ptr.
          + econstructor.
            * (* arg2: _t'6 = newval_cv *)
              eapply eval_Etempvar.
              subst le5. rewrite PTree.gss. reflexivity.
            * (* sem_cast for arg2: newval_cv tlong -> tlong *)
              apply (sem_cast_long_val_repr hm cb co _ newval_cv m Hval_repr_newval).
            * econstructor.
        - (* Genv.find_funct *)
          exact Hfind_funct.
        - (* type_of_fundef *)
          simpl. reflexivity.
        - (* eval_funcall *)
          apply eval_funcall_external.
          exact Hext_call.
      }
    }

    (* -- Part B: assign accu, advance sp, return 0 -- *)
    {
      simpl. (* set_opttemp None Vundef le5 = le5 *)
      apply exec_Sseq_1 with (t1 := E0) (le1 := le6) (m1 := m1).
      {
        (* Sassign (s->accu) val_unit_expr *)
        apply exec_Sassign with (loc := sb)
          (ofs := Ptrofs.add so (Ptrofs.repr 8))
          (bf := Full) (v2 := unit_v) (v := unit_v).
        - eapply eval_Efield_struct.
          + eapply eval_Elvalue.
            * eapply eval_Ederef.
              eapply eval_Etempvar.
              subst le6 le5 le4 le3 le2 le1.
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gso by (compute; congruence).
              exact Hle_s.
            * apply deref_loc_copy. simpl. reflexivity.
          + simpl. reflexivity.
          + exact Hco.
          + exact Haccu_offset.
        - eapply eval_Ebinop.
          + eapply eval_Ebinop.
            * eapply eval_Ecast.
              apply eval_Econst_int.
              { apply sem_cast_int_to_long_0. }
            * apply eval_Econst_int.
            * apply sem_shl_long_0_1.
          + apply eval_Econst_int.
          + apply sem_add_long_int_0_1.
        - apply sem_cast_long_vlong.
        - apply assign_loc_value with (chunk := Mint64).
          + simpl. reflexivity.
          + simpl.
            rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
            exact Hstore1.
      }

      apply exec_Sseq_1 with (t1 := E0) (le1 := le7) (m1 := m2).
      {
        (* Sset _t'1 (s->sp) ; Sassign (s->sp) (_t'1 + 2) *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le7) (m1 := m1).
        {
          apply exec_Sset.
          eapply eval_Elvalue.
          - eapply eval_Efield_struct.
            + eapply eval_Elvalue.
              * eapply eval_Ederef.
                eapply eval_Etempvar.
                subst le6 le5 le4 le3 le2 le1.
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                exact Hle_s.
              * apply deref_loc_copy. simpl. reflexivity.
            + simpl. reflexivity.
            + exact Hco.
            + exact Hsp_offset.
          - apply deref_loc_value with (chunk := Mptr).
            * simpl. reflexivity.
            * simpl. rewrite Mptr_Mint64.
              rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
              exact Hsp_load_m1.
        }

        {
          apply exec_Sassign with (loc := sb)
            (ofs := Ptrofs.add so (Ptrofs.repr 16))
            (bf := Full) (v2 := new_sp_v) (v := new_sp_v).
          - eapply eval_Efield_struct.
            + eapply eval_Elvalue.
              * eapply eval_Ederef.
                eapply eval_Etempvar.
                subst le7 le6 le5 le4 le3 le2 le1.
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                exact Hle_s.
              * apply deref_loc_copy. simpl. reflexivity.
            + simpl. reflexivity.
            + exact Hco.
            + exact Hsp_offset.
          - eapply eval_Ebinop.
            + eapply eval_Etempvar.
              subst le7. rewrite PTree.gss. reflexivity.
            + apply eval_Econst_int.
            + apply sem_add_sp_2.
          - apply sem_cast_ptr_to_ptr.
          - apply assign_loc_value with (chunk := Mptr).
            + simpl. reflexivity.
            + simpl. rewrite Mptr_Mint64.
              rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
              exact Hstore2.
        }
      }

      (* Sreturn 0 *)
      { apply exec_Sreturn_some.
        apply eval_Econst_int. }
    }
  }

  (* ================================================================ *)
  (* Part 2: abs_rel for post-state                                   *)
  (* ================================================================ *)
  {
    set (ard' := mk_abs_rel
      sb so hm cb co gb go
      (ar_stack_block ard) (ar_stack_base_ofs ard)
      (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
    exists ard'.

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le_final *)
    { subst le7 le6 le5 le4 le3 le2 le1.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      exact Hle_s. }

    (* 2. pc field -- unchanged *)
    { exists pc_ptr. split.
      - exact Hpc_load_m2.
      - simpl. exact Hpc_rel. }

    (* 3. accu field -- val_unit = Val_int 0 *)
    { exists unit_v. split.
      - exact Haccu_m2.
      - simpl. subst unit_v. exact (vr_int _ _ _ 0). }

    (* 4. sp field *)
    { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 16)).
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
      - exact Hsp_m2.
      - reflexivity.
      - simpl. exact Hstack_repr_m2.
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - (* Ptrofs.unsigned (sp_ofs + 16) >= 8 *)
        rewrite ptrofs_add_unsigned by lia. lia.
      - (* sp_rep for rest *)
        rewrite ptrofs_add_unsigned by lia. exact Hsp_rep_tail.
      - split.
        + (* sp_writable: permission preserved through caml_modify + stores *)
          intros ofs' Hofs'.
          eapply Mem.perm_store_1. exact Hstore2.
          eapply Mem.perm_store_1. exact Hstore1.
          apply Hcm_perm_preserved.
          * eapply Mem.perm_valid_block. apply (Hsp_writable 0). lia.
          * { apply Hsp_writable.
              rewrite (ptrofs_add_unsigned sp_ofs 16 ltac:(lia) ltac:(lia)) in Hofs'.
              rewrite Hstk in Hsp_rep |- *. simpl Datatypes.length in Hsp_rep |- *.
              destruct Hofs' as [Hofs_lo Hofs_hi].
              split; [exact Hofs_lo|].
              apply Z.lt_le_trans with
                (m := Ptrofs.unsigned sp_ofs + 16 + 8 * Z.of_nat (Datatypes.length rest)).
              - exact Hofs_hi.
              - pose proof (Nat2Z.is_nonneg (Datatypes.length rest)). lia. }
        + (* sp alignment: unchanged *)
          rewrite ptrofs_add_unsigned by lia.
          unfold align_chunk. simpl.
          destruct Hsp_align as [k Hk].
          clear - Hk. unfold align_chunk in Hk.
          exists (k + 2)%Z. lia. }

    (* 5. env field *)
    { exists env_v. split.
      - exact Henv_m2.
      - simpl. exact Henv_repr. }

    (* 6. extra_args field *)
    { simpl. exact Hextra_m2. }

    (* 7. global_data field *)
    { exists (Vptr gb go). split; [| split; [| split]].
      - exact Hgd_m2.
      - simpl. reflexivity.
      - simpl. exact Hglobal_m2.
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field *)
    { exists ts_ptr. split.
      - exact Hts_m2.
      - simpl. exact Htrap_rel. }

    (* 9. sb_writable *)
    { exact Hsb_writable_m2. }
  }
Qed.
