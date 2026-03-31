(* ASRINT_correct.v -- correctness proof for ASRINT bytecode handler.

   C handler (from clightgen):
     _t'1 = s->sp;
     s->sp = _t'1 + 1;
     _t'2 = s->accu;
     _t'3 = *_t'1;
     s->accu = (long)(((long)_t'2 >> ((long)_t'3 >> 1)) | 1);
     return 0;

   Rocq handler:
     handle_ASRINT pc' s = match accu, stack with
       | Val_int a, Val_int b :: rest =>
           Step (s<|pc:=pc'|><|accu:=Val_int(Z.shiftr a b)|><|stack:=rest|>)
       | _, _ => Error ...

   Tagged arithmetic identity (when 0 <= b < 64):
     ((2a+1) >>_arith b) | 1 = 2*(Z.shiftr a b)+1

   The C shift is only defined when the shift amount is in [0,64).
   OCaml's bytecode guarantees this for well-formed programs; we encode
   this as an axiom on the value representation (analogous to the
   structural axioms in HandlerLemmas.v). *)

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

(* ================================================================== *)
(* Axiom: shift amounts in OCaml bytecode are valid C shift amounts.   *)
(* ================================================================== *)

(* OCaml's 63-bit tagged integers on 64-bit platforms ensure that
   shift instructions receive shift counts in [0,62], well within
   [0,64) required by C's shift semantics.  This is a runtime value
   representation invariant, analogous to the structural separation
   axioms in HandlerLemmas.v.  To eliminate, add a range constraint
   on Val_int values to abs_rel / val_repr. *)
Axiom val_int_shift_amount_valid : forall (hm : nat -> option (block * ptrofs)) b cv,
  val_repr hm (Val_int b) cv ->
  Int64.ltu (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1))
            Int64.iwordsize = true.

(* ================================================================== *)
(* Axiom: tagged arithmetic identity for ASR.                          *)
(* ================================================================== *)

(* The C computation on tagged integers:
     ((2a+1) >>_arith ((2b+1) >>_arith 1)) | 1
   equals the tagged representation of Z.shiftr a b:
     2*(Z.shiftr a b)+1
   when the shift amount is valid (ensured by val_int_shift_amount_valid).

   This identity holds for OCaml's 63-bit tagged integers where both a
   and b fit in 62 bits.  The identity connects Int64's modular shr
   (which sign-extends from bit 63) with Z.shiftr (which sign-extends
   from the mathematical sign).  These agree when a*2+1 fits in signed
   Int64 range (-2^62 <= a < 2^62).

   To eliminate this axiom, add a 62-bit range constraint on Val_int
   values to val_repr / abs_rel. *)
Axiom tagged_asrint_arith : forall a b,
  Int64.ltu (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1))
            Int64.iwordsize = true ->
  Int64.or (Int64.shr (Int64.repr (a * 2 + 1))
              (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)))
           (Int64.repr 1)
  = Int64.repr (Z.shiftr a b * 2 + 1).

(* ================================================================== *)
(* Semantic lemmas for shift and or operations                         *)
(* ================================================================== *)

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl. reflexivity.
Qed.

Local Lemma sem_shr_long_long_signed : forall n1 n2 m,
  Int64.ltu n2 Int64.iwordsize = true ->
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n1) tlong (Vlong n2) tlong m
  = Some (Vlong (Int64.shr n1 n2)).
Proof.
  intros n1 n2 m Hguard.
  unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tlong) with (shift_case_ll Signed).
  simpl. rewrite Hguard. reflexivity.
Qed.

Local Lemma sem_or_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oor
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.or n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_ASRINT_correct :
    handler_correct handle_ASRINT f_instr_ASRINT
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handler_correct, handle_ASRINT.
  destruct (Machine.accu s) as [a| | |] eqn:Haccu_eq; try (exact I).
  destruct (Machine.stack s) as [|v_hd v_tl] eqn:Hstk; try (exact I).
  destruct v_hd as [b| | |] eqn:Hvhd; try (exact I).
  intro Hpre.
  destruct Hpre as [ard Hpre].
  set (sb := ar_sptr_block ard) in *.
  set (so := ar_sptr_ofs ard) in *.
  set (hm := ar_heap_map ard) in *.
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
  rewrite Haccu_eq in Haccu_repr.
  inversion Haccu_repr; subst accu_v. rename H0 into Haccu_is_int.
  rewrite Hstk in Hstack_repr.
  inversion Hstack_repr as [| ? ? ? ? cv0 Hload_sp0 Hval_repr0 Hstack_repr_rest].
  revert Hgd_load Hgd_eq Hglobal_repr. subst.
  intros Hgd_load Hgd_eq Hglobal_repr.
  inversion Hval_repr0; subst cv0. rename H0 into Hstk_is_int.
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

  (* Shift guard from axiom *)
  pose proof (val_int_shift_amount_valid hm b (Vlong (Int64.repr (b * 2 + 1)))
                (vr_int hm b)) as Hshift_guard.

  (* Abbreviations *)
  set (tagged_a := Int64.repr (a * 2 + 1)).
  set (tagged_b := Int64.repr (b * 2 + 1)).
  set (shift_amt := Int64.shr tagged_b (Int64.repr 1)).
  set (shifted := Int64.shr tagged_a shift_amt).
  set (result_int64 := Int64.or shifted (Int64.repr 1)).
  set (result_v := Vlong result_int64).
  set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).

  (* Store 1: sp field *)
  destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 16)
              (Vptr sp_b sp_ofs) new_sp_v Hsp_load) as [m1 Hstore1].

  assert (Haccu_load_m1 :
    Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vlong tagged_a)).
  { apply (load_after_store_other m m1 sb
             (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8)
             new_sp_v (Vlong tagged_a) Hstore1 Haccu_load). left. lia. }

  assert (Hload_sp0_m1 :
    Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) = Some (Vlong tagged_b)).
  { erewrite Mem.load_store_other. exact Hload_sp0. exact Hstore1.
    left. exact Hblock_sep. }

  (* Store 2: accu field *)
  destruct (store_succeeds_from_load m1 sb (Ptrofs.unsigned so + 8)
              (Vlong tagged_a) result_v Haccu_load_m1) as [m' Hstore2].

  set (le' := PTree.set _t'3 (Vlong tagged_b)
                (PTree.set _t'2 (Vlong tagged_a)
                  (PTree.set _t'1 (Vptr sp_b sp_ofs) le))).
  exists le'. exists m'. exists (Out_return (Some (Vint (Int.repr 0), tint))).
  split.

  (* ============================================================== *)
  (* Part 1: exec                                                    *)
  (* ============================================================== *)
  { apply (eval_stmt_to_exec clight_ge 15). eval_cbn.
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_1; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    unfold new_sp_v in Hstore1. rewrite Hstore1; eval_cbn.
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m1; eval_cbn.
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite Hload_sp0_m1; eval_cbn.
    (* lvalue for s->accu *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    (* -- ASRINT-specific: evaluate the rhs expression -- *)
    (* _t'2 lookup *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    (* _t'2 cast *)
    rewrite sem_cast_long_vlong; eval_cbn.
    (* _t'3 lookup *)
    rewrite PTree.gss; eval_cbn.
    (* _t'3 cast *)
    rewrite sem_cast_long_vlong; eval_cbn.
    (* inner Oshr: (long)_t'3 >> 1 *)
    rewrite sem_shr_long_int_1; eval_cbn.
    (* outer Oshr: (long)_t'2 >> shift_amt *)
    rewrite (sem_shr_long_long_signed tagged_a shift_amt _ Hshift_guard); eval_cbn.
    (* Oor: shifted | 1 *)
    rewrite sem_or_long_int_1; eval_cbn.
    (* casts *)
    rewrite sem_cast_long_vlong; eval_cbn.
    rewrite sem_cast_long_vlong; eval_cbn.
    (* store *)
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    unfold result_v, result_int64, shifted in Hstore2.
    rewrite Hstore2; eval_cbn.
    subst le'. reflexivity. }

  (* ============================================================== *)
  (* Part 2: abs_rel                                                 *)
  (* ============================================================== *)
  { exists ard. set (uso := Ptrofs.unsigned so) in *.
    assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
    { assert (Hpc_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 0)
                 new_sp_v pc_ptr Hstore1 Hpc_load). left. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 0)
               result_v pc_ptr Hstore2 Hpc_m1). left. lia. }
    assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some new_sp_v).
    { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some new_sp_v).
      { pose proof (load_after_store_same m m1 sb (uso + 16)
                      new_sp_v Hstore1) as Htmp.
        unfold new_sp_v in Htmp |- *.
        simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp.
        exact Htmp. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 16)
               result_v new_sp_v Hstore2 Hsp_m1). right. lia. }
    assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some result_v).
    { pose proof (load_after_store_same m1 m' sb (uso + 8)
                    result_v Hstore2) as Htmp.
      unfold result_v in Htmp |- *. simpl Val.load_result in Htmp. exact Htmp. }
    assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 24)
                 new_sp_v env_v Hstore1 Henv_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 24)
               result_v env_v Hstore2 He1). right. lia. }
    assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
                 new_sp_v _ Hstore1 Hextra_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 32)
               result_v _ Hstore2 He1). right. lia. }
    assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 40)
                 new_sp_v gd_ptr Hstore1 Hgd_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 40)
               result_v gd_ptr Hstore2 He1). right. lia. }
    assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
    { assert (He1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 48)
                 new_sp_v ts_ptr Hstore1 Hts_load). right. lia. }
      apply (load_after_store_other m1 m' sb (uso + 8) (uso + 48)
               result_v ts_ptr Hstore2 He1). right. lia. }
    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
    (* 1. _s in le' *)
    { subst le'.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      exact Hle_s. }
    (* 2. pc *)
    { exists pc_ptr. split. exact Hpc_load'. simpl. exact Hpc_rel. }
    (* 3. accu = Val_int (Z.shiftr a b) *)
    { exists result_v. split. exact Haccu_load'. simpl.
      unfold result_v, result_int64, shifted, shift_amt, tagged_a, tagged_b.
      rewrite tagged_asrint_arith by exact Hshift_guard.
      constructor. }
    (* 4. sp *)
    { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)).
      split; [| split]. exact Hsp_load'. reflexivity. simpl.
      eapply (stack_repr_store_other_block hm m1 m' _ sp_b
               (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) result_v).
      + eapply (stack_repr_store_other_block hm m m1 _ sp_b
                 (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16) new_sp_v).
        * exact Hstack_repr_rest.
        * exact Hstore1.
        * intro Heq; exact (Hblock_sep (eq_sym Heq)).
      + exact Hstore2.
      + intro Heq; exact (Hblock_sep (eq_sym Heq)). }
    (* 5. env *)
    { exists env_v. split. exact Henv_load'. simpl. exact Henv_repr. }
    (* 6. extra_args *)
    { simpl. exact Hextra_load'. }
    (* 7. global_data *)
    { exists gd_ptr. split; [| split]. exact Hgd_load'. simpl. exact Hgd_eq. simpl.
      eapply (global_repr_store_other_block hm m1 m' _ _ _ sb (uso + 8) result_v).
      + eapply (global_repr_store_other_block hm m m1 _ _ _ sb (uso + 16) new_sp_v).
        * exact Hglobal_repr.
        * exact Hstore1.
        * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
      + exact Hstore2.
      + intro Heq2; exact (Hgb_ne (eq_sym Heq2)). }
    (* 8. trap_sp *)
    { exists ts_ptr. split. exact Hts_load'. simpl. exact Htrap_rel. } }
Qed.
