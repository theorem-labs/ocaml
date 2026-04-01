(* NEQ_correct.v -- Verification of the NEQ bytecode handler.
   C: s->accu = ((long)((long)_t'2 != (long)_t'3) << 1) + 1; sp++.
   If not-equal: ((long)1 << 1) + 1 = 3 = tagged 1 = val_true.
   If equal: ((long)0 << 1) + 1 = 1 = tagged 0 = val_false.

   Structurally identical to EQ but uses One (not-equal) instead of Oeq,
   and the Rocq handler swaps val_true/val_false:
     handle_NEQ: if value_phys_eqb ... then val_false else val_true

   NOTE: The Rocq handler uses value_phys_eqb which works on ANY value
   types, but the Clight code compares as longs via One. The proof only
   covers the case where both accu and stack top are Val_int. The
   precondition neq_int_range_pre is False for other value combinations,
   making those obligations vacuously true. *)
From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
Require Import instruct_handlers InstructSpec StepToBigstep HandlerLemmas.
Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr sem_binary_operation sem_cast
        Mem.load Mem.store Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int field_offset PTree.get PTree.set].

Local Lemma sem_ne_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Cop.One
    (Vlong n1) tlong (Vlong n2) tlong m
    = Some (Val.of_bool (negb (Int64.eq n1 n2))).
Proof. intros. reflexivity. Qed.

Local Lemma sem_cast_bool_int_to_long : forall (cond : bool) m,
  sem_cast (Val.of_bool cond) tint tlong m
    = Some (Vlong (Int64.repr (if cond then 1 else 0))).
Proof. intros. destruct cond; reflexivity. Qed.

Local Lemma sem_shl_bool_long_1 : forall (cond : bool) m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong (Int64.repr (if cond then 1 else 0))) tlong
    (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.repr (if cond then 2 else 0))).
Proof. intros. destruct cond; reflexivity. Qed.

Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

Local Lemma tagged_neq_result : forall (cond : bool),
  Int64.add (Int64.repr (if cond then 2 else 0)) (Int64.repr 1)
    = Int64.repr (if cond then 3 else 1).
Proof. intros. destruct cond; reflexivity. Qed.

(* ================================================================== *)
(* Key arithmetic lemma: tagged integer equality                       *)
(*                                                                      *)
(* Int64.eq (Int64.repr (a*2+1)) (Int64.repr (b*2+1)) = Z.eqb a b    *)
(*                                                                      *)
(* Requires both a*2+1 and b*2+1 to be in [0, Int64.max_unsigned]     *)
(* so that Int64.repr is injective (no modular wrapping).              *)
(* ================================================================== *)

Local Lemma tagged_neq_arith : forall a b,
  0 <= a * 2 + 1 <= Int64.max_unsigned ->
  0 <= b * 2 + 1 <= Int64.max_unsigned ->
  Int64.eq (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1)) = Z.eqb a b.
Proof.
  intros a b Ha Hb.
  unfold Int64.eq.
  rewrite !Int64.unsigned_repr by lia.
  destruct (Z.eqb a b) eqn:Heqb.
  - apply Z.eqb_eq in Heqb. subst b.
    destruct (zeq (a * 2 + 1) (a * 2 + 1)); [reflexivity | congruence].
  - apply Z.eqb_neq in Heqb.
    destruct (zeq (a * 2 + 1) (b * 2 + 1)) as [Heq | Hneq].
    + exfalso. apply Heqb. lia.
    + reflexivity.
Qed.

(* ================================================================== *)
(* The precondition: both integer operands in representable range.     *)
(* For non-(Val_int, Val_int) combinations, the precondition is False, *)
(* making those obligations vacuously true.                            *)
(* ================================================================== *)

Definition neq_int_range_pre (m : mem) (s : state) (_ : abs_rel_data) : Prop :=
  match s.(Machine.accu), s.(Machine.stack) with
  | Val_int a, Val_int b :: _ =>
      0 <= a * 2 + 1 <= Int64.max_unsigned /\
      0 <= b * 2 + 1 <= Int64.max_unsigned
  | _, _ => False
  end.

Theorem verify_NEQ_correct :
    handler_correct handle_NEQ f_instr_NEQ
      (fun _ => neq_int_range_pre)
      (fun _ s => s.(Machine.stack) = nil) (fun _ => False) (fun _ _ _ => False).
Proof.
  unfold handler_correct.
  intros e le m s. unfold handle_NEQ.
  destruct (Machine.stack s) as [|v_hd v_tl] eqn:Hstk; try reflexivity.
  (* Non-empty stack: handle_NEQ returns Step for all accu/v_hd combos. *)
  destruct (Machine.accu s) as [a| | |] eqn:Haccu_eq;
    destruct v_hd as [b| | |] eqn:Hvhd.
  (* Close all 15 non-(Val_int, Val_int) cases *)
  all: try (intros ard0 _ Hpre_false; unfold neq_int_range_pre in Hpre_false;
            rewrite Haccu_eq in Hpre_false;
            first [ exfalso; exact Hpre_false
                  | rewrite Hstk in Hpre_false; exfalso; exact Hpre_false ]).
  intros ard Hpre Hrange.
  unfold abs_rel_with_ard in Hpre.
  set (sb := ar_sptr_block ard) in *. set (so := ar_sptr_ofs ard) in *. set (hm := ar_heap_map ard) in *.
  destruct Hpre as (Hle_s & [pc_ptr [Hpc_load Hpc_rel]] & [accu_v [Haccu_load Haccu_repr]] & [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb Hcb_ne_sp]]]]]]]] & [env_v [Henv_load Henv_repr]] & Hextra_load & [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] & [ts_ptr [Hts_load Htrap_rel]]). subst sp_ptr.
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  rewrite Haccu_eq in Haccu_repr. inversion Haccu_repr; subst accu_v. rename H0 into Haccu_is_int.
  rewrite Hstk in Hstack_repr.
  inversion Hstack_repr as [| ? ? ? ? cv0 Hload_sp0 Hval_repr0 Hstack_repr_rest].
  revert Hgd_load Hgd_eq Hglobal_repr. subst. intros Hgd_load Hgd_eq Hglobal_repr.
  inversion Hval_repr0; subst cv0. rename H0 into Hstk_is_int.
  unfold neq_int_range_pre in Hrange. rewrite Haccu_eq, Hstk in Hrange.
  destruct Hrange as [Ha_range Hb_range].
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
  set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
  destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 16)
              (Vptr sp_b sp_ofs) new_sp_v Hsp_load) as [m1 Hstore1].
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vlong (Int64.repr (a * 2 + 1)))).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8) new_sp_v (Vlong (Int64.repr (a * 2 + 1))) Hstore1 Haccu_load). left. lia. }
  assert (Hload_sp0_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) = Some (Vlong (Int64.repr (b * 2 + 1)))).
  { erewrite Mem.load_store_other. exact Hload_sp0. exact Hstore1. left. exact Hsp_ne_sb. }
  set (neq_bool := negb (Int64.eq (Int64.repr (a * 2 + 1)) (Int64.repr (b * 2 + 1)))).
  set (result_v := Vlong (Int64.add (Int64.repr (if neq_bool then 2 else 0)) (Int64.repr 1))).
  destruct (store_succeeds_from_load m1 sb (Ptrofs.unsigned so + 8) (Vlong (Int64.repr (a * 2 + 1))) result_v Haccu_load_m1) as [m' Hstore2].
  set (le' := PTree.set _t'3 (Vlong (Int64.repr (b * 2 + 1))) (PTree.set _t'2 (Vlong (Int64.repr (a * 2 + 1))) (PTree.set _t'1 (Vptr sp_b sp_ofs) le))).
  exists le'. exists m'. exists (Out_return (Some (Vint (Int.repr 0), tint))). split.
  (* Part 1: Clight execution proof.
     Follow ANDINT_correct pattern exactly: interleave eval_cbn with rewrites. *)
  { apply (eval_stmt_to_exec clight_ge 15). eval_cbn.
    (* Sset _t'1: read sp from struct *)
    rewrite Hle_s; eval_cbn. rewrite Hco; eval_cbn. rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn. rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.
    (* Sassign sp: _s.sp = _t'1 + 1 *)
    rewrite PTree.gso by (compute; congruence). rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn. rewrite sem_add_sp_1; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn. rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    unfold new_sp_v in Hstore1. rewrite Hstore1; eval_cbn.
    (* Sset _t'2: read accu from struct *)
    rewrite PTree.gso by (compute; congruence). rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m1; eval_cbn.
    (* Sset _t'3: read *_t'1 (stack top) *)
    rewrite PTree.gso by (compute; congruence). rewrite PTree.gss; eval_cbn.
    rewrite Hload_sp0_m1; eval_cbn.
    (* Sassign accu: lvalue = _s.accu, rvalue = ((cast(_t'2 != _t'3) << 1) + 1).
       Follow ANDINT pattern: resolve _s lookup, eval_cbn to process lvalue,
       then resolve rvalue PTree lookups with eval_cbn interleaving. *)
    rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence). rewrite Hle_s; eval_cbn.
    (* Now eval_cbn has processed the Sassign lvalue (struct deref + field_offset).
       The rvalue evaluation begins. Resolve PTree lookups for _t'2 and _t'3. *)
    rewrite PTree.gso by (compute; congruence). rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    (* NEQ-specific: One comparison, then cast, shift, add *)
    rewrite sem_ne_long_long; eval_cbn.
    rewrite sem_cast_bool_int_to_long; eval_cbn.
    rewrite (sem_shl_bool_long_1 neq_bool); eval_cbn.
    rewrite sem_add_long_int_1; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    (* Final store *)
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    unfold result_v in Hstore2. rewrite Hstore2; eval_cbn.
    subst le'. reflexivity. }
  (* Part 2: Postcondition -- abs_rel on the output state *)
  { unfold abs_rel. exists ard. set (uso := Ptrofs.unsigned so) in *.
    assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
    { assert (Hpc_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 0) new_sp_v pc_ptr Hstore1 Hpc_load). left. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 0) result_v pc_ptr Hstore2 Hpc_m1). left. lia. }
    assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some new_sp_v).
    { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some new_sp_v).
      { pose proof (load_after_store_same m m1 sb (uso + 16) new_sp_v Hstore1) as Htmp. unfold new_sp_v in Htmp |- *. simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 16) result_v new_sp_v Hstore2 Hsp_m1). right. lia. }
    assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some result_v).
    { pose proof (load_after_store_same m1 m' sb (uso + 8) result_v Hstore2) as Htmp. unfold result_v in Htmp |- *. simpl Val.load_result in Htmp. exact Htmp. }
    assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v). { apply (load_after_store_other m m1 sb (uso + 16) (uso + 24) new_sp_v env_v Hstore1 Henv_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 24) result_v env_v Hstore2 He1). right. lia. }
    assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))). { apply (load_after_store_other m m1 sb (uso + 16) (uso + 32) new_sp_v _ Hstore1 Hextra_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 32) result_v _ Hstore2 He1). right. lia. }
    assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr). { apply (load_after_store_other m m1 sb (uso + 16) (uso + 40) new_sp_v gd_ptr Hstore1 Hgd_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 40) result_v gd_ptr Hstore2 He1). right. lia. }
    assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr). { apply (load_after_store_other m m1 sb (uso + 16) (uso + 48) new_sp_v ts_ptr Hstore1 Hts_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 48) result_v ts_ptr Hstore2 He1). right. lia. }
    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
    { subst le'. rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence). rewrite PTree.gso by (compute; congruence). exact Hle_s. }
    { exists pc_ptr. split. exact Hpc_load'. simpl. exact Hpc_rel. }
    { exists result_v. split. exact Haccu_load'. simpl.
      unfold result_v. rewrite tagged_neq_result.
      unfold neq_bool. rewrite (tagged_neq_arith a b Ha_range Hb_range).
      destruct (Z.eqb a b); constructor. }
    { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)). split; [| split; [| split; [| split; [| split]]]]. exact Hsp_load'. reflexivity.
      { simpl.
        eapply (stack_repr_store_other_block hm m1 m' _ sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) result_v).
        + eapply (stack_repr_store_other_block hm m m1 _ sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16) new_sp_v).
          * exact Hstack_repr_rest. * exact Hstore1. * intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        + exact Hstore2. + intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
      exact Hsp_ne_sb. exact Hsp_ne_gb. exact Hcb_ne_sp. }
    { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }
    { simpl. exact Hextra_load'. }
    { exists gd_ptr. split; [| split; [| split]]. exact Hgd_load'. simpl. exact Hgd_eq.
      { simpl.
        eapply (global_repr_store_other_block hm m1 m' _ _ _ sb (uso + 8) result_v).
        + eapply (global_repr_store_other_block hm m m1 _ _ _ sb (uso + 16) new_sp_v). * exact Hglobal_repr. * exact Hstore1. * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        + exact Hstore2. + intro Heq2; exact (Hgb_ne (eq_sym Heq2)). }
      exact Hgb_ne_sb. }
    { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. } }
Qed.
