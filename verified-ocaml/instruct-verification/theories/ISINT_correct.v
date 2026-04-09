(* ISINT_correct.v -- ISINT completeness proof using
   the computational evaluator from StepToBigstep.v.

   ISINT handler:
   - Rocq: handle_ISINT pc' s:
       Step (s <|pc:=pc'|> <|accu:= if is_int (accu s) then val_true else val_false|>)
       Always returns Step (no Error).

   - C (Clight AST): The handler body does:
       1. _t'1 = s->accu                          (read accu tagged value)
       2. s->accu = ((_t'1 & 1) << 1) + 1         (tag-bit test + encode as bool)
       3. return 0

   Tagged integer arithmetic correspondence:
     Val_int n:       val_repr = Vlong (Int64.repr (n*2+1)), bit 0 = 1
       C: ((n*2+1) & 1) = 1, (1 << 1) + 1 = 3 = val_repr(Val_int 1) = val_true
     Val_block tag []: val_repr = Vlong (Int64.repr (tag*1024)), bit 0 = 0
       C: ((tag*1024) & 1) = 0, (0 << 1) + 1 = 1 = val_repr(Val_int 0) = val_false

   Precondition: accu is Val_int or Val_block tag [].
   Val_ptr and Val_closure produce Vptr in memory, and CompCert's
   sem_and on Vptr is undefined (sem_binarith requires Vint/Vlong/Vfloat
   values for the operator, but Vptr fails the binarith path), so those
   cases cannot be proved without extending the CompCert semantics.

   Uses abs_rel directly (no separate _pre relation).
   All lemmas imported from HandlerLemmas. *)

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
Local Notation exec := (exec_stmt function_entry1 clight_ge).

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Lemma: sem_and tlong tint on Vlong * Vint(1)                       *)
(* ================================================================== *)

Lemma sem_and_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oand
    (Vlong n) tlong
    (Vint (Int.repr 1)) tint
    m = Some (Vlong (Int64.and n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_and.
  change (classify_binarith tlong tint) with (bin_case_l Signed).
  unfold sem_binarith. simpl binarith_type.
  unfold sem_cast at 1. simpl classify_cast.
  rewrite ptr64_true.
  unfold sem_cast at 1. simpl classify_cast.
  simpl cast_int_long.
  change (Int.signed (Int.repr 1)) with 1%Z.
  reflexivity.
Qed.

(* ================================================================== *)
(* Lemma: sem_shl on tlong * tint: Vlong << Vint(1)                   *)
(* ================================================================== *)

Lemma sem_shl_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong n) tlong
    (Vint (Int.repr 1)) tint
    m = Some (Vlong (Int64.shl' n (Int.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl.
  reflexivity.
Qed.

(* ================================================================== *)
(* Lemma: sem_add on tlong * tint: Vlong + Vint(1)                    *)
(* ================================================================== *)

Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong
    (Vint (Int.repr 1)) tint
    m = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add tlong tint) with add_default.
  unfold sem_binarith.
  change (classify_binarith tlong tint) with (bin_case_l Signed).
  simpl binarith_type.
  unfold sem_cast at 1. simpl classify_cast.
  rewrite ptr64_true.
  unfold sem_cast at 1. simpl classify_cast.
  simpl cast_int_long.
  change (Int.signed (Int.repr 1)) with 1%Z.
  reflexivity.
Qed.

(* ================================================================== *)
(* Lemma: Tagged integer bit-0 is 1                                    *)
(*   Int64.and (Int64.repr (n*2+1)) (Int64.repr 1) = Int64.repr 1     *)
(* ================================================================== *)

Lemma tagged_int_bit0 : forall n,
  Int64.and (Int64.repr (n * 2 + 1)) (Int64.repr 1) = Int64.repr 1.
Proof.
  intros n.
  (* Z.land (n*2+1) 1 = 1 because n*2+1 is odd *)
  apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_and, !Int64.testbit_repr by lia.
  replace (n * 2 + 1)%Z with (2 * n + 1)%Z by lia.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - rewrite Z.testbit_odd_0. reflexivity.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite Z.testbit_odd_succ by lia.
    (* Goal: Z.testbit n (i-1) && Z.testbit 1 (Z.succ(i-1)) = Z.testbit 1 (Z.succ(i-1)) *)
    (* Z.testbit 1 (succ k) for k >= 0: 1 = 2*0+1, testbit_odd_succ gives testbit 0 k = false *)
    assert (Hbit1 : Z.testbit 1 (Z.succ (i - 1)) = false).
    { change 1%Z with (2 * 0 + 1)%Z.
      rewrite Z.testbit_odd_succ by lia.
      apply Z.bits_0. }
    rewrite Hbit1. apply andb_false_r.
Qed.

(* ================================================================== *)
(* Lemma: Tagged block-atom bit-0 is 0                                 *)
(*   Int64.and (Int64.repr (tag*1024)) (Int64.repr 1) = Int64.repr 0  *)
(* ================================================================== *)

Lemma tagged_block_bit0 : forall tag,
  Int64.and (Int64.repr (Z.of_nat tag * 1024)) (Int64.repr 1) = Int64.repr 0.
Proof.
  intros tag.
  apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_and, !Int64.testbit_repr by lia.
  replace (Z.of_nat tag * 1024)%Z with (2 * (Z.of_nat tag * 512))%Z by lia.
  rewrite Z.bits_0.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - rewrite Z.testbit_even_0. reflexivity.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite Z.testbit_even_succ by lia.
    (* Goal: Z.testbit (tag*512) (i-1) && Z.testbit 1 (Z.succ(i-1)) = false *)
    assert (Hbit1 : Z.testbit 1 (Z.succ (i - 1)) = false).
    { change 1%Z with (2 * 0 + 1)%Z.
      rewrite Z.testbit_odd_succ by lia.
      apply Z.bits_0. }
    rewrite Hbit1. apply andb_false_r.
Qed.

(* ================================================================== *)
(* Concrete arithmetic lemmas via native_compute                       *)
(* ================================================================== *)

Lemma shl_1_1 :
  Int64.shl' (Int64.repr 1) (Int.repr 1) = Int64.repr 2.
Proof.
  cut (Int64.unsigned (Int64.shl' (Int64.repr 1) (Int.repr 1))
       = Int64.unsigned (Int64.repr 2)).
  { intro H. rewrite <- (Int64.repr_unsigned (Int64.shl' _ _)).
    rewrite H. apply Int64.repr_unsigned. }
  native_compute. reflexivity.
Qed.

Lemma shl_0_1 :
  Int64.shl' (Int64.repr 0) (Int.repr 1) = Int64.repr 0.
Proof.
  cut (Int64.unsigned (Int64.shl' (Int64.repr 0) (Int.repr 1))
       = Int64.unsigned (Int64.repr 0)).
  { intro H. rewrite <- (Int64.repr_unsigned (Int64.shl' _ _)).
    rewrite H. apply Int64.repr_unsigned. }
  native_compute. reflexivity.
Qed.

Lemma add_2_1 :
  Int64.add (Int64.repr 2) (Int64.repr 1) = Int64.repr 3.
Proof.
  cut (Int64.unsigned (Int64.add (Int64.repr 2) (Int64.repr 1))
       = Int64.unsigned (Int64.repr 3)).
  { intro H. rewrite <- (Int64.repr_unsigned (Int64.add _ _)).
    rewrite H. apply Int64.repr_unsigned. }
  native_compute. reflexivity.
Qed.

Lemma add_0_1 :
  Int64.add (Int64.repr 0) (Int64.repr 1) = Int64.repr 1.
Proof.
  cut (Int64.unsigned (Int64.add (Int64.repr 0) (Int64.repr 1))
       = Int64.unsigned (Int64.repr 1)).
  { intro H. rewrite <- (Int64.repr_unsigned (Int64.add _ _)).
    rewrite H. apply Int64.repr_unsigned. }
  native_compute. reflexivity.
Qed.

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof.
  intros. reflexivity.
Qed.

(* ================================================================== *)
(* Precondition: accu has a Vlong representation (not Vptr).           *)
(*                                                                      *)
(* Val_int n        -> Vlong (tagged n)              OK                *)
(* Val_block tag [] -> Vlong (tagged block-atom)     OK                *)
(* Val_ptr addr     -> Vptr b ofs                    sem_and fails     *)
(* Val_closure a o  -> Vptr b (ofs+delta)            sem_and fails     *)
(*                                                                      *)
(* This is a semantic restriction: the C ISINT handler uses bitwise    *)
(* AND which CompCert only defines for integer-like (Vlong/Vint)       *)
(* values, not for pointer values (Vptr).                              *)
(* ================================================================== *)

Definition isint_accu_vlong (s : Machine.state) : Prop :=
  match Machine.accu s with
  | Val_int _ => True
  | Val_block _ nil => True
  | _ => False
  end.

(* Stronger precondition: also requires Vlong representation for Val_int.
   This excludes the vr_code_ptr case where Val_int is represented as Vptr,
   which cannot be handled by CompCert's sem_and (undefined on Vptr). *)
Definition isint_accu_vlong_strong (s : Machine.state) (ard : abs_rel_data) : Prop :=
  isint_accu_vlong s /\
  match Machine.accu s with
  | Val_int n => int_vlong ard n
  | _ => True
  end.

(* ================================================================== *)
(* Main theorem                                                        *)
(*                                                                      *)
(* Uses a custom statement (like BOOLNOT_correct.v) to add the         *)
(* isint_accu_vlong precondition, since handle_ISINT always returns    *)
(* Step and handler_correct has no Step-case precondition slot.         *)
(* ================================================================== *)

Theorem verify_ISINT_correct :
  forall e le m s,
    match handle_ISINT s.(pc) s with
    | Step s' =>
        forall ard,
        isint_accu_vlong_strong s ard ->
        abs_rel_with_ard e le m s ard ->
        exists le' m' out,
          exec_stmt function_entry1 clight_ge e le m (fn_body f_instr_ISINT) E0 le' m' out /\
          abs_rel e le' m' s'
    | Error msg => True
    | Halt v => False
    | CCall_request _ _ _ => False
    end.
Proof.
  intros e le m s.
  unfold handle_ISINT.

  (* handle_ISINT always returns Step, so we are in the Step branch. *)
  (* Case split on accu to determine is_int result and val_repr form. *)
  destruct (Machine.accu s) as [n | tag fields | addr | addr off] eqn:Haccu_eq.

  (* ================================================================ *)
  (* Case 1: accu = Val_int n => is_int = true, result = val_true     *)
  (* ================================================================ *)
  {
    simpl is_int.

    intros ard [_Hvlong_ok Hint_vlong] Hpre.

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

    pose proof (sptr_ofs_representable ard) as Hso_bound.
    fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne.
    fold sb in Hgb_ne.

    (* Use int_vlong to get that accu_v is Vlong, excluding vr_code_ptr *)
    rewrite Haccu_eq in Hint_vlong.
    simpl in Hint_vlong. unfold int_vlong in Hint_vlong.
    rewrite Haccu_eq in Haccu_repr.
    inversion Haccu_repr; subst accu_v.
    2: { (* vr_code_ptr: Vptr, contradicts int_vlong *)
         exfalso.
         destruct (Hint_vlong _ Haccu_repr) as [z Hz].
         discriminate Hz. }
    set (cv_accu := Vlong (Int64.repr (n * 2 + 1))) in *.

    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    set (cv_result := Vlong (Int64.add (Int64.shl' (Int64.and (Int64.repr (n * 2 + 1)) (Int64.repr 1)) (Int.repr 1)) (Int64.repr 1))) in *.

    destruct (store_succeeds_sb m sb so 8 cv_accu Hsb_writable Haccu_load ltac:(lia) ltac:(lia) cv_result)
      as [m' Hstore].

    set (le' := PTree.set _t'1 cv_accu le).
    exists le'. exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* Part 1: exec *)
    {
      apply (eval_stmt_to_exec clight_ge 10).
      eval_cbn.

      (* S1: Sset _t'1 = s->accu *)
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Haccu_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Haccu_load; eval_cbn.

      (* S2: s->accu = ((_t'1 & 1) << 1) + 1 *)
      (* S2 lvalue *)
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.

      (* Rvalue: resolve _t'1 *)
      rewrite PTree.gss; eval_cbn.

      (* Ebinop Oand: _t'1 & 1 *)
      unfold cv_accu.
      rewrite sem_and_long_int_1; eval_cbn.

      (* Ecast tlong -> tlong (identity) *)
      rewrite sem_cast_long_vlong; eval_cbn.

      (* Ebinop Oshl: ... << 1 *)
      rewrite sem_shl_long_int_1; eval_cbn.

      (* Ebinop Oadd: ... + 1 *)
      rewrite sem_add_long_int_1; eval_cbn.

      (* Sassign sem_cast: typeof rhs (tlong) -> typeof lhs (tlong) *)
      rewrite sem_cast_long_vlong; eval_cbn.

      (* comp_assign_loc: store *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      fold cv_result.
      rewrite Hstore; eval_cbn.

      subst le'. reflexivity.
    }

    (* Part 2: abs_rel for post-state *)
    {
      exists ard.
      set (uso := Ptrofs.unsigned so) in *.

      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) cv_result pc_ptr
                 Hstore Hpc_load). left. lia. }

      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) cv_result (Vptr sp_b sp_ofs)
                 Hstore Hsp_load). right. lia. }

      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) cv_result env_v
                 Hstore Henv_load). right. lia. }

      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) cv_result _
                 Hstore Hextra_load). right. lia. }

      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) cv_result gd_ptr
                 Hstore Hgd_load). right. lia. }

      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) cv_result ts_ptr
                 Hstore Hts_load). right. lia. }

      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some cv_result).
      { pose proof (load_after_store_same m m' sb (uso + 8) cv_result Hstore) as Htmp.
        subst cv_result.
        rewrite load_result_vlong in Htmp.
        exact Htmp. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      { exists pc_ptr. split.
        - exact Hpc_load'.
        - simpl. exact Hpc_rel. }

      { exists cv_result. split.
        - exact Haccu_load'.
        - simpl. subst cv_result.
          rewrite tagged_int_bit0.
          rewrite shl_1_1.
          rewrite add_2_1.
          constructor. }

      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load'.
        - reflexivity.
        - simpl.
          apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) cv_result
                   Hstack_repr Hstore).
                    intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsp_writable. exact Hofs'.
        - exact Hsp_align. }

      { exists env_v. split.
        - exact Henv_load'.
        - simpl. exact Henv_repr. }

      { simpl. exact Hextra_load'. }

      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load'.
        - simpl. exact Hgd_eq.
        - simpl.
          apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) cv_result
                   Hglobal_repr Hstore).
                    intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      { exists ts_ptr. split.
        - exact Hts_load'.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved *)
      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsb_writable. exact Hofs'. }
    }
  }

  (* ================================================================ *)
  (* Case 2: accu = Val_block tag fields => is_int = false             *)
  (* ================================================================ *)
  {
    simpl is_int.

    (* The precondition isint_accu_vlong requires fields = nil *)
    intros ard [Hok _Hint_vlong2] Hpre.
    unfold isint_accu_vlong in Hok. rewrite Haccu_eq in Hok. simpl in Hok.
    destruct fields as [|fhd ftl].
    2: { contradiction. }

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

    pose proof (sptr_ofs_representable ard) as Hso_bound.
    fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne.
    fold sb in Hgb_ne.

    rewrite Haccu_eq in Haccu_repr.
    inversion Haccu_repr; subst accu_v; subst tag0.

    set (cv_accu := Vlong (Int64.repr (Z.of_nat tag * 1024))) in *.

    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    set (cv_result := Vlong (Int64.add (Int64.shl' (Int64.and (Int64.repr (Z.of_nat tag * 1024)) (Int64.repr 1)) (Int.repr 1)) (Int64.repr 1))) in *.

    destruct (store_succeeds_sb m sb so 8 cv_accu Hsb_writable Haccu_load ltac:(lia) ltac:(lia) cv_result)
      as [m' Hstore].

    set (le' := PTree.set _t'1 cv_accu le).
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

      (* S2 lvalue + rvalue *)
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.

      rewrite PTree.gss; eval_cbn.

      unfold cv_accu.
      rewrite sem_and_long_int_1; eval_cbn.
      rewrite sem_cast_long_vlong; eval_cbn.
      rewrite sem_shl_long_int_1; eval_cbn.
      rewrite sem_add_long_int_1; eval_cbn.

      (* Sassign sem_cast *)
      rewrite sem_cast_long_vlong; eval_cbn.

      (* comp_assign_loc: store *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      fold cv_result.
      rewrite Hstore; eval_cbn.

      subst le'. reflexivity.
    }

    (* Part 2: abs_rel for post-state *)
    {
      exists ard.
      set (uso := Ptrofs.unsigned so) in *.

      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) cv_result pc_ptr
                 Hstore Hpc_load). left. lia. }

      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) cv_result (Vptr sp_b sp_ofs)
                 Hstore Hsp_load). right. lia. }

      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) cv_result env_v
                 Hstore Henv_load). right. lia. }

      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) cv_result _
                 Hstore Hextra_load). right. lia. }

      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) cv_result gd_ptr
                 Hstore Hgd_load). right. lia. }

      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) cv_result ts_ptr
                 Hstore Hts_load). right. lia. }

      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some cv_result).
      { pose proof (load_after_store_same m m' sb (uso + 8) cv_result Hstore) as Htmp.
        subst cv_result.
        rewrite load_result_vlong in Htmp.
        exact Htmp. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      { exists pc_ptr. split.
        - exact Hpc_load'.
        - simpl. exact Hpc_rel. }

      { exists cv_result. split.
        - exact Haccu_load'.
        - simpl. subst cv_result.
          rewrite tagged_block_bit0.
          rewrite shl_0_1.
          rewrite add_0_1.
          constructor. }

      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load'.
        - reflexivity.
        - simpl.
          apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) cv_result
                   Hstack_repr Hstore).
                    intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsp_writable. exact Hofs'.
        - exact Hsp_align. }

      { exists env_v. split.
        - exact Henv_load'.
        - simpl. exact Henv_repr. }

      { simpl. exact Hextra_load'. }

      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load'.
        - simpl. exact Hgd_eq.
        - simpl.
          apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) cv_result
                   Hglobal_repr Hstore).
                    intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      { exists ts_ptr. split.
        - exact Hts_load'.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved *)
      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsb_writable. exact Hofs'. }
    }
  }

  (* ================================================================ *)
  (* Case 3: accu = Val_ptr addr => excluded by isint_accu_vlong      *)
  (* ================================================================ *)
  {
    intros ard [Hok _] _Hpre.
    unfold isint_accu_vlong in Hok. rewrite Haccu_eq in Hok. simpl in Hok. contradiction.
  }

  (* ================================================================ *)
  (* Case 4: accu = Val_closure addr off => excluded by precondition  *)
  (* ================================================================ *)
  {
    intros ard [Hok _] _Hpre.
    unfold isint_accu_vlong in Hok. rewrite Haccu_eq in Hok. simpl in Hok. contradiction.
  }
Qed.

(* Wrapper: convert to handler_correct form for the Module Type. *)
Theorem verify_ISINT_handler_correct :
    handler_correct handle_ISINT f_instr_ISINT
      accu_is_immediate
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  pose proof (verify_ISINT_correct e le m s) as H.
  destruct (handle_ISINT (Machine.pc s) s) eqn:Hmatch.
  - intros ard Hrel Hpre.
    apply (H ard).
    + (* isint_accu_vlong_strong from accu_is_immediate *)
      unfold isint_accu_vlong_strong, isint_accu_vlong, accu_is_immediate in *.
      destruct (Machine.accu s) eqn:Heq; try contradiction.
      * split; [exact I | exact Hpre].
      * destruct l; [split; [exact I | exact I] | contradiction].
    + exact Hrel.
  - exact H.
  - exact H.
  - exact H.
Qed.
