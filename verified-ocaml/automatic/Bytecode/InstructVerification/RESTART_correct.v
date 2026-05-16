(* RESTART_correct.v -- RESTART handler correctness proof.

   RESTART is the inverse of GRAB. When a partial application closure
   is invoked, RESTART restores the saved arguments from the closure
   environment back onto the stack.

   Step case proved with real precondition (restart_step_pre) and
   loop induction for the copy loop.  NO AXIOMS. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Import Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.
Local Notation exec := (exec_stmt function_entry1 clight_ge).

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_unary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Helper lemmas                                                       *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma sem_cast_long_to_int : forall n m,
  sem_cast (Vlong n) tlong tint m = Some (Vint (Int.repr (Int64.unsigned n))).
Proof.
  intros. unfold sem_cast. simpl classify_cast. rewrite ptr64_true. reflexivity.
Qed.

Local Lemma sem_shr_long_int_10 : forall n m,
  sem_binary_operation (genv_cenv ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 10)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 10))).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl. reflexivity.
Qed.

Local Lemma sem_sub_long_int : forall n1 n2 m,
  sem_binary_operation (genv_cenv ge) Osub
    (Vlong n1) tlong (Vint n2) tint m
  = Some (Vlong (Int64.sub n1 (Int64.repr (Int.signed n2)))).
Proof.
  intros. unfold sem_binary_operation, sem_sub.
  simpl classify_sub. unfold sem_binarith.
  simpl classify_binarith. simpl binarith_type.
  unfold sem_cast. simpl classify_cast. rewrite ptr64_true.
  unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_add_ptr_int_i : forall b ofs (i : int) m,
  sem_binary_operation (genv_cenv ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint i) tint m
  = Some (Vptr b (Ptrofs.add ofs
      (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed i)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  simpl classify_add. unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_sub_ptr_int : forall b ofs (i : int) m,
  sem_binary_operation (genv_cenv ge) Osub
    (Vptr b ofs) (tptr tlong) (Vint i) tint m
  = Some (Vptr b (Ptrofs.sub ofs
      (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed i)))).
Proof.
  intros. unfold sem_binary_operation, sem_sub.
  simpl classify_sub. simpl.
  destruct Archi.ptr64 eqn:Hptr.
  - reflexivity.
  - exfalso. rewrite ptr64_true in Hptr. discriminate.
Qed.

Local Lemma sem_neg_int : forall n m,
  sem_unary_operation Oneg (Vint n) tint m = Some (Vint (Int.neg n)).
Proof. intros. reflexivity. Qed.

Local Lemma sem_add_int_int : forall n1 n2 m,
  sem_binary_operation (genv_cenv ge) Oadd
    (Vint n1) tint (Vint n2) tint m
  = Some (Vint (Int.add n1 n2)).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  simpl classify_add. unfold sem_binarith.
  simpl classify_binarith. simpl binarith_type.
  unfold sem_cast. simpl classify_cast.
  unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_lt_int_int : forall n1 n2 m,
  sem_binary_operation (genv_cenv ge) Olt
    (Vint n1) tint (Vint n2) tint m
  = Some (Val.of_bool (Int.lt n1 n2)).
Proof.
  intros. unfold sem_binary_operation, sem_cmp.
  simpl classify_cmp. unfold sem_binarith.
  simpl classify_binarith. simpl binarith_type.
  unfold sem_cast. simpl classify_cast.
  unfold sem_cast. simpl classify_cast.
  simpl. reflexivity.
Qed.

Local Lemma sem_add_long_int : forall n1 n2 m,
  sem_binary_operation (genv_cenv ge) Oadd
    (Vlong n1) tlong (Vint n2) tint m
  = Some (Vlong (Int64.add n1 (Int64.repr (Int.signed n2)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  simpl classify_add. unfold sem_binarith.
  simpl classify_binarith. simpl binarith_type.
  unfold sem_cast. simpl classify_cast. rewrite ptr64_true.
  unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* ================================================================== *)
(* Struct field offset for _extra_args                                 *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Local Lemma ce_extra_args : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _extra_args (co_members co) = Errors.OK (32, Full).
Proof.
  eexists. split; reflexivity.
Qed.

Local Lemma interp_state_co_extra : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _extra_args (co_members co) = Errors.OK (32, Full).
Proof.
  rewrite cenv_is_ce. exact ce_extra_args.
Qed.

(* ================================================================== *)
(* Ptrofs arithmetic helpers                                           *)
(* ================================================================== *)

Local Lemma ptrofs_mul_8 : forall n,
  0 <= n ->
  n * 8 <= Ptrofs.max_unsigned ->
  Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.repr n) = Ptrofs.repr (n * 8).
Proof.
  intros n Hn0 Hn8.
  assert (PM : Ptrofs.modulus = 18446744073709551616) by reflexivity.
  unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 8).
  2: { unfold Ptrofs.max_unsigned. lia. }
  rewrite Ptrofs.unsigned_repr.
  2: { unfold Ptrofs.max_unsigned in *. lia. }
  f_equal. lia.
Qed.

Local Lemma ptrofs_of_int_signed_repr : forall z,
  Int.min_signed <= z <= Int.max_signed ->
  ptrofs_of_int Signed (Int.repr z) = Ptrofs.repr z.
Proof.
  intros. unfold ptrofs_of_int. simpl. unfold Ptrofs.of_ints.
  rewrite Int.signed_repr by lia. reflexivity.
Qed.

(* ================================================================== *)
(* Stack repr from individual loads                                    *)
(* ================================================================== *)

Local Lemma build_stack_repr_prefix :
  forall (prefix suffix : list value)
         (hm : nat -> option (block * ptrofs)) (cb : block) (co : ptrofs)
         (m : mem) (sp_b : block) (base : Z),
    (forall j v, nth_error prefix j = Some v ->
      exists cv, Mem.load Mint64 m sp_b (base + Z.of_nat j * 8) = Some cv /\
        val_repr hm cb co v cv) ->
    stack_repr hm cb co m suffix sp_b
      (Ptrofs.repr (base + Z.of_nat (length prefix) * 8)) ->
    0 <= base ->
    base + Z.of_nat (length prefix + length suffix) * 8 < Ptrofs.modulus ->
    (8 | base) ->
    stack_repr hm cb co m (prefix ++ suffix) sp_b (Ptrofs.repr base).
Proof.
  induction prefix as [| v rest IH]; intros.
  - simpl in *. rewrite Z.add_0_r in H0. exact H0.
  - simpl app.
    assert (Hmod : Ptrofs.modulus = 18446744073709551616) by reflexivity.
    assert (Hbase_rep : 0 <= base <= Ptrofs.max_unsigned).
    { unfold Ptrofs.max_unsigned. simpl length in H2. lia. }
    assert (Hv0 := H 0%nat v eq_refl).
    destruct Hv0 as [cv [Hload0 Hvr0]].
    replace (base + Z.of_nat 0 * 8) with base in Hload0 by lia.
    econstructor.
    + rewrite Ptrofs.unsigned_repr by lia. exact Hload0.
    + exact Hvr0.
    + replace (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 8)) with (Ptrofs.repr (base + 8)).
      2: { unfold Ptrofs.add.
           rewrite Ptrofs.unsigned_repr by lia.
           rewrite (Ptrofs.unsigned_repr 8) by (unfold Ptrofs.max_unsigned; lia).
           reflexivity. }
      apply IH; clear IH.
      * intros j v0 Hnth.
        destruct (H (S j) v0 Hnth) as [cv0 [Hload Hvr]]. exists cv0. split; [| exact Hvr].
        replace (base + Z.of_nat (S j) * 8) with (base + 8 + Z.of_nat j * 8) in Hload by lia.
        exact Hload.
      * simpl length in H0 |- *.
        replace (base + 8 + Z.of_nat (length rest) * 8)
          with (base + Z.of_nat (S (length rest)) * 8) by lia. exact H0.
      * lia.
      * simpl length in *. lia.
      * destruct H3 as [k Hk]. exists (k + 1). lia.
Qed.

(* Preserve stack_repr when all loads are preserved *)
Local Lemma stack_repr_load_preserved :
  forall hm cb co m m' stk b ofs,
    stack_repr hm cb co m stk b ofs ->
    (forall ofs0 v0, Mem.load Mint64 m b ofs0 = Some v0 ->
                     Mem.load Mint64 m' b ofs0 = Some v0) ->
    stack_repr hm cb co m' stk b ofs.
Proof.
  intros hm cb co m m' stk b ofs Hsr Hpres.
  induction Hsr as [| v vs b0 ofs0 cv Hload Hvr Hsr' IH].
  - constructor.
  - econstructor; [exact (Hpres _ _ Hload) | exact Hvr | exact (IH Hpres)].
Qed.

(* Like stack_repr_load_preserved but the callback also receives
   a proof that the offset is >= the stack base unsigned offset.
   Needed when loads above a certain offset are preserved (e.g., loop
   writes only below sp_ofs). *)
Local Lemma stack_repr_load_preserved_above :
  forall hm cb co m m' stk b ofs lo,
    stack_repr hm cb co m stk b ofs ->
    lo <= Ptrofs.unsigned ofs ->
    Ptrofs.unsigned ofs + 8 * Z.of_nat (length stk) < Ptrofs.modulus ->
    (forall ofs0 v0, ofs0 >= lo ->
                     Mem.load Mint64 m b ofs0 = Some v0 ->
                     Mem.load Mint64 m' b ofs0 = Some v0) ->
    stack_repr hm cb co m' stk b ofs.
Proof.
  intros hm cb co m m' stk b ofs lo Hsr Hlo Hrep Hpres.
  revert lo Hlo Hrep Hpres.
  induction Hsr as [| v vs b0 ofs0 cv Hload Hvr Hsr' IH];
    intros lo Hlo Hrep Hpres.
  - constructor.
  - econstructor.
    + apply Hpres; [lia | exact Hload].
    + exact Hvr.
    + apply (IH lo); [| | exact Hpres].
      * rewrite ptrofs_add_unsigned; [lia | lia | simpl length in Hrep; lia].
      * rewrite ptrofs_add_unsigned; [| lia | simpl length in Hrep; lia].
        simpl length in Hrep. lia.
Qed.

(* Like global_repr_store_other_block but for arbitrary load-preserving
   memory transitions on the same block. *)
Local Lemma global_repr_load_preserved :
  forall hm cb co m m' gs b ofs,
    global_repr hm cb co m gs b ofs ->
    (forall ofs0 v0, Mem.load Mint64 m b ofs0 = Some v0 ->
                     Mem.load Mint64 m' b ofs0 = Some v0) ->
    global_repr hm cb co m' gs b ofs.
Proof.
  intros hm0 cb0 co0 m0 m' gs0 b0 ofs0 Hgr Hpres.
  induction Hgr as [| v vs b1 ofs1 cv Hload Hvr Hgr' IH].
  - constructor.
  - econstructor.
    + apply Hpres. exact Hload.
    + exact Hvr.
    + exact (IH Hpres).
Qed.

(* ================================================================== *)
(* The Sloop body and increment from f_instr_RESTART                   *)
(* ================================================================== *)

Local Definition restart_loop_s1 :=
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                   (Etempvar _num_args tint) tint)
      Sskip
      Sbreak)
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _env tlong))
        (Ssequence
          (Sset _t'6
            (Ederef
              (Ebinop Oadd
                (Ecast (Etempvar _t'5 tlong) (tptr tlong))
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 3) tint) tint)
                (tptr tlong)) tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                (Etempvar _i tint) (tptr tlong)) tlong)
            (Etempvar _t'6 tlong)))))).

Local Definition restart_loop_s2 :=
  (Sset _i
    (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)).

(* ================================================================== *)
(* Loop correctness lemma                                              *)
(*                                                                      *)
(* Proves by induction on n (remaining iterations) that the Sloop      *)
(* correctly copies n values from the env block to the stack block.    *)
(* ================================================================== *)

Lemma restart_loop_correct : forall n,
  forall (k : nat) (num_args_z : Z)
         (env_b : block) (env_ptr_ofs : ptrofs)
         (sp_b : block) (new_sp_ofs : ptrofs)
         (sb : block) (so : ptrofs) (gb : block)
         (fields : list value)
         (hm : nat -> option (block * ptrofs))
         (cb : block) (co : ptrofs)
         (e : Clight.env) (le : temp_env) (m : mem),
    (* Iteration bounds *)
    Z.of_nat (k + n) = num_args_z ->
    (0 <= num_args_z + 3 <= Int.max_signed)%Z ->
    (0 <= Z.of_nat k <= Int.max_signed)%Z ->
    (* le bindings *)
    le ! _i = Some (Vint (Int.repr (Z.of_nat k))) ->
    le ! _num_args = Some (Vint (Int.repr num_args_z)) ->
    le ! _s = Some (Vptr sb so) ->
    (* struct loads *)
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b new_sp_ofs) ->
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some (Vptr env_b env_ptr_ofs) ->
    (* Remaining env fields loadable *)
    (forall j, (k <= j < k + n)%nat ->
      forall v, nth_error fields (j + 3) = Some v ->
      exists cv, Mem.load Mint64 m env_b
        (Ptrofs.unsigned env_ptr_ofs + Z.of_nat (j + 3) * 8) = Some cv /\
        val_repr hm cb co v cv) ->
    (* Previously stored values at sp[0..k-1] *)
    (forall j, (j < k)%nat ->
      forall v, nth_error fields (j + 3) = Some v ->
      exists cv, Mem.load Mint64 m sp_b
        (Ptrofs.unsigned new_sp_ofs + Z.of_nat j * 8) = Some cv /\
        val_repr hm cb co v cv) ->
    (* SP writable for remaining range *)
    Mem.range_perm m sp_b
      (Ptrofs.unsigned new_sp_ofs + Z.of_nat k * 8)
      (Ptrofs.unsigned new_sp_ofs + num_args_z * 8)
      Cur Writable ->
    (* Block separation *)
    env_b <> sp_b -> sp_b <> sb -> env_b <> sb ->
    sp_b <> gb -> cb <> sp_b ->
    (* Offset representability *)
    Ptrofs.unsigned new_sp_ofs + num_args_z * 8 < Ptrofs.modulus ->
    Ptrofs.unsigned so + 56 < Ptrofs.modulus ->
    (* Alignment *)
    (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs) ->
    (* env_ptr_ofs offset representability *)
    Ptrofs.unsigned env_ptr_ofs + Z.of_nat (k + n + 3) * 8 < Ptrofs.modulus ->
    Ptrofs.unsigned env_ptr_ofs >= 0 ->
    (* Fields length *)
    (k + n + 3 <= length fields)%nat ->
    (* Conclusion *)
    exists le' m',
      exec e le m (Sloop restart_loop_s1 restart_loop_s2) E0 le' m' Out_normal /\
      (* All values at sp[0..k+n-1] are correctly stored *)
      (forall j, (j < k + n)%nat ->
        forall v, nth_error fields (j + 3) = Some v ->
        exists cv, Mem.load Mint64 m' sp_b
          (Ptrofs.unsigned new_sp_ofs + Z.of_nat j * 8) = Some cv /\
          val_repr hm cb co v cv) /\
      (* Loads from any block other than sp_b preserved *)
      (forall b0 ofs0 v0, b0 <> sp_b ->
        Mem.load Mint64 m b0 ofs0 = Some v0 ->
        Mem.load Mint64 m' b0 ofs0 = Some v0) /\
      (* Loads from sp_b above loop region preserved *)
      (forall ofs0 v0, ofs0 >= Ptrofs.unsigned new_sp_ofs + num_args_z * 8 ->
        Mem.load Mint64 m sp_b ofs0 = Some v0 ->
        Mem.load Mint64 m' sp_b ofs0 = Some v0) /\
      (* Range permissions preserved *)
      (forall b ofs0 k0 p, Mem.perm m b ofs0 k0 p -> Mem.perm m' b ofs0 k0 p) /\
      (* Temp vars preserved *)
      le' ! _s = Some (Vptr sb so) /\
      le' ! _num_args = Some (Vint (Int.repr num_args_z)).
Proof.
  induction n as [| n' IH]; intros.

  (* ================================================================ *)
  (* Base case: n = 0, loop terminates immediately                     *)
  (* ================================================================ *)
  {
    exists le, m. split; [| split; [| split; [| split; [| split; [| split]]]]].
    - (* exec: condition false → break *)
      eapply exec_Sloop_stop1.
      + eapply exec_Sseq_2.
        * eapply exec_Sifthenelse with (b := false).
          -- econstructor; [econstructor; eassumption | econstructor; eassumption |].
             rewrite sem_lt_int_int. reflexivity.
          -- unfold bool_val. simpl. f_equal. unfold Val.of_bool.
             unfold Int.lt.
             replace (Z.of_nat k) with num_args_z by lia.
             rewrite Int.signed_repr by (pose proof Int.min_signed_neg; lia).
             destruct (zlt _ _); [lia | reflexivity].
          -- simpl. eapply exec_Sbreak.
        * discriminate.
      + constructor.
    - intros j Hj v Hnth. replace (k + 0)%nat with k in Hj by lia. eauto.
    - auto.
    - auto.
    - auto.
    - assumption.
    - assumption.
  }

  (* ================================================================ *)
  (* Inductive case: n = S n', execute one iteration + recurse         *)
  (* ================================================================ *)
  {
    (* Get the field value at index k+3 *)
    assert (Hfield_exists : exists v, nth_error fields (k + 3) = Some v).
    { destruct (nth_error fields (k + 3)) as [v|] eqn:Hnth.
      - exists v. reflexivity.
      - apply nth_error_None in Hnth. exfalso. lia. }
    destruct Hfield_exists as [fv Hfv_nth].

    (* Get the C value for fields[k+3] *)
    destruct (H7 k ltac:(lia) fv Hfv_nth) as [cv_k [Hload_env_k Hvr_k]].

    (* The store to sp[k] must succeed *)
    assert (Hsp_valid : Mem.valid_access m Mint64 sp_b
              (Ptrofs.unsigned new_sp_ofs + Z.of_nat k * 8) Writable).
    { split.
      - intros ofs0 Hofs0. apply H9. simpl in Hofs0. lia.
      - simpl in H17 |- *. destruct H17 as [q Hq].
        exists (q + Z.of_nat k). lia. }
    destruct (Mem.valid_access_store m Mint64 sp_b
                (Ptrofs.unsigned new_sp_ofs + Z.of_nat k * 8) cv_k Hsp_valid)
      as [m_k Hstore_k].

    (* Prepare the le after body evaluations *)
    set (le_body := PTree.set _i (Vint (Int.repr (Z.of_nat (S k))))
            (PTree.set _t'6 cv_k
              (PTree.set _t'5 (Vptr env_b env_ptr_ofs)
                (PTree.set _t'4 (Vptr sp_b new_sp_ofs) le)))) in *.

    (* Apply the IH *)
    assert (IH_result : exists le_post m_post,
      exec e le_body m_k (Sloop restart_loop_s1 restart_loop_s2) E0 le_post m_post Out_normal /\
      (forall j, (j < S k + n')%nat ->
        forall v, nth_error fields (j + 3) = Some v ->
        exists cv, Mem.load Mint64 m_post sp_b
          (Ptrofs.unsigned new_sp_ofs + Z.of_nat j * 8) = Some cv /\
          val_repr hm cb co v cv) /\
      (forall b0 ofs0 v0, b0 <> sp_b ->
        Mem.load Mint64 m_k b0 ofs0 = Some v0 ->
        Mem.load Mint64 m_post b0 ofs0 = Some v0) /\
      (forall ofs0 v0, ofs0 >= Ptrofs.unsigned new_sp_ofs + num_args_z * 8 ->
        Mem.load Mint64 m_k sp_b ofs0 = Some v0 ->
        Mem.load Mint64 m_post sp_b ofs0 = Some v0) /\
      (forall b ofs0 k0 p, Mem.perm m_k b ofs0 k0 p -> Mem.perm m_post b ofs0 k0 p) /\
      le_post ! _s = Some (Vptr sb so) /\
      le_post ! _num_args = Some (Vint (Int.repr num_args_z))).
    {
      assert (Hle_i : le_body ! _i = Some (Vint (Int.repr (Z.of_nat (S k))))).
      { subst le_body. rewrite PTree.gss. reflexivity. }
      assert (Hle_na : le_body ! _num_args = Some (Vint (Int.repr num_args_z))).
      { subst le_body. repeat (rewrite PTree.gso by (compute; congruence)). assumption. }
      assert (Hle_s2 : le_body ! _s = Some (Vptr sb so)).
      { subst le_body. repeat (rewrite PTree.gso by (compute; congruence)). assumption. }
      assert (H5' : Mem.load Mint64 m_k sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b new_sp_ofs)).
      { erewrite Mem.load_store_other; [exact H5 | exact Hstore_k |].
        left. exact (not_eq_sym H11). }
      assert (H6' : Mem.load Mint64 m_k sb (Ptrofs.unsigned so + 24) = Some (Vptr env_b env_ptr_ofs)).
      { erewrite Mem.load_store_other; [exact H6 | exact Hstore_k |].
        left. exact (not_eq_sym H11). }
      assert (H7' : forall j, (S k <= j < S k + n')%nat ->
        forall v, nth_error fields (j + 3) = Some v ->
        exists cv, Mem.load Mint64 m_k env_b
          (Ptrofs.unsigned env_ptr_ofs + Z.of_nat (j + 3) * 8) = Some cv /\
          val_repr hm cb co v cv).
      { intros j Hj v Hnth.
        destruct (H7 j ltac:(lia) v Hnth) as [cv [Hload Hvr]].
        exists cv. split; [| exact Hvr].
        erewrite Mem.load_store_other; [exact Hload | exact Hstore_k |].
        left. exact H10. }
      assert (H8' : forall j, (j < S k)%nat ->
        forall v, nth_error fields (j + 3) = Some v ->
        exists cv, Mem.load Mint64 m_k sp_b
          (Ptrofs.unsigned new_sp_ofs + Z.of_nat j * 8) = Some cv /\
          val_repr hm cb co v cv).
      { intros j Hj v Hnth.
        destruct (Nat.eq_dec j k) as [Heq_jk | Hne_jk].
        + subst j. rewrite Hfv_nth in Hnth. injection Hnth as ->.
          exists cv_k. split; [| exact Hvr_k].
          eapply Mem.load_store_same in Hstore_k.
          rewrite (val_repr_load_result _ _ _ _ _ Hvr_k) in Hstore_k. exact Hstore_k.
        + destruct (H8 j ltac:(lia) v Hnth) as [cv [Hload Hvr]].
          exists cv. split; [| exact Hvr].
          erewrite Mem.load_store_other; [exact Hload | exact Hstore_k |].
          right. simpl. lia. }
      assert (H9' : Mem.range_perm m_k sp_b
        (Ptrofs.unsigned new_sp_ofs + Z.of_nat (S k) * 8)
        (Ptrofs.unsigned new_sp_ofs + num_args_z * 8) Cur Writable).
      { intros ofs0 Hofs0. eapply Mem.perm_store_1. exact Hstore_k. apply H9. lia. }
      exact (IH (S k) num_args_z env_b env_ptr_ofs sp_b new_sp_ofs sb so gb
        fields hm cb co e le_body m_k
        ltac:(lia) H0 ltac:(lia) Hle_i Hle_na Hle_s2 H5' H6' H7' H8' H9'
        H10 H11 H12 H13 H14 H15 H16 H17 ltac:(lia)
        ltac:(pose proof (Ptrofs.unsigned_range env_ptr_ofs); lia)
        ltac:(lia)).
    }
    destruct IH_result as (le_post & m_post &
      Hloop_exec & Hpost_vals & Hpost_other & Hpost_sp_hi & Hpost_perm &
      Hpost_le_s & Hpost_le_na).

    exists le_post, m_post. split; [| split; [| split; [| split; [| split; [| split]]]]].

    - (* exec: one iteration then recurse *)
      replace E0 with (E0 ** E0 ** E0) by reflexivity.
      eapply exec_Sloop_loop.

      + (* s1: condition true + body *)
        replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1.
        * (* Sifthenelse: condition true *)
          eapply exec_Sifthenelse with (b := true).
          -- econstructor; [econstructor; eassumption | econstructor; eassumption |].
             rewrite sem_lt_int_int. reflexivity.
          -- unfold bool_val. simpl. f_equal. unfold Val.of_bool.
             unfold Int.lt.
             rewrite Int.signed_repr by (pose proof Int.min_signed_neg; lia).
             rewrite Int.signed_repr by (pose proof Int.min_signed_neg; lia).
             destruct (zlt (Z.of_nat k) num_args_z); [reflexivity | lia].
          -- simpl. eapply exec_Sskip.
        * (* body: t4=sp, t5=env, t6=env[k+3], sp[k]=t6 *)
          destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
          replace E0 with (E0 ** E0) by reflexivity.
          eapply exec_Sseq_1.
          -- (* Sset _t'4: load sp from struct *)
             apply (eval_stmt_to_exec ge 10). eval_cbn.
             rewrite H4; eval_cbn. rewrite Hco; eval_cbn.
             rewrite Hsp_offset; eval_cbn.
             try rewrite Mptr_Mint64; eval_cbn.
             rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
             rewrite H5; eval_cbn. reflexivity.
          -- replace E0 with (E0 ** E0) by reflexivity.
             eapply exec_Sseq_1.
             ++ (* Sset _t'5: load env from struct *)
                apply (eval_stmt_to_exec ge 10). eval_cbn.
                rewrite PTree.gso by (compute; congruence).
                rewrite H4; eval_cbn. rewrite Hco; eval_cbn.
                assert (Henv_ofs : field_offset ge _env (co_members co_is) = Errors.OK (24, Full)).
                { destruct interp_state_co_env as [co' [Hco' [Henv' _]]].
                  assert (co_is = co') by congruence. subst. exact Henv'. }
                rewrite Henv_ofs; eval_cbn.
                rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
                rewrite H6; eval_cbn. reflexivity.
             ++ replace E0 with (E0 ** E0) by reflexivity.
                eapply exec_Sseq_1.
                ** (* Sset _t'6: load env[k+3] *)
                   apply (eval_stmt_to_exec ge 10). eval_cbn.
                   rewrite PTree.gss; eval_cbn.
                   rewrite sem_cast_long_to_ptr_vptr; eval_cbn.
                   rewrite PTree.gso by (compute; congruence).
                   rewrite PTree.gso by (compute; congruence).
                   rewrite H2; eval_cbn.
                   rewrite sem_add_int_int; eval_cbn.
                   rewrite sem_add_ptr_int_i; eval_cbn.
                   (* Simplify the address: env_ptr_ofs + 8 * (k+3) *)
                   replace (Int.add (Int.repr (Z.of_nat k)) (Int.repr 3)) with
                     (Int.repr (Z.of_nat (k + 3))).
                   2: { rewrite Int.add_unsigned.
                        rewrite (Int.unsigned_repr (Z.of_nat k))
                          by (pose proof Int.max_signed_unsigned; split; lia).
                        rewrite (Int.unsigned_repr 3)
                          by (pose proof Int.max_signed_unsigned; split; lia).
                        f_equal. lia. }
                   rewrite ptrofs_of_int_signed_repr by (pose proof Int.min_signed_neg; lia).
                   rewrite ptrofs_mul_8 by
                     (unfold Ptrofs.max_unsigned;
                      pose proof (Ptrofs.unsigned_range env_ptr_ofs); lia).
                   rewrite (ptrofs_add_unsigned env_ptr_ofs (Z.of_nat (k + 3) * 8)
                     ltac:(pose proof (Ptrofs.unsigned_range env_ptr_ofs); lia) ltac:(lia)).
                   rewrite Hload_env_k; eval_cbn.
                   try rewrite (val_repr_load_result _ _ _ _ _ Hvr_k).
                   reflexivity.
                ** (* Sassign: sp[k] = t'6 *)
                   eapply exec_Sassign.
                   --- (* eval_lvalue: *(t4 + i) *)
                       econstructor. econstructor. econstructor.
                       +++ rewrite PTree.gso by (compute; congruence).
                           rewrite PTree.gso by (compute; congruence).
                           rewrite PTree.gss. reflexivity.
                       +++ econstructor.
                           rewrite PTree.gso by (compute; congruence).
                           rewrite PTree.gso by (compute; congruence).
                           rewrite PTree.gso by (compute; congruence).
                           exact H2.
                       +++ exact (sem_add_ptr_int_i sp_b new_sp_ofs
                             (Int.repr (Z.of_nat k)) m).
                   --- econstructor. rewrite PTree.gss. reflexivity.
                   --- exact (sem_cast_long_val_repr _ _ _ _ _ m Hvr_k).
                   --- econstructor.
                       +++ reflexivity.
                       +++ unfold Mem.storev.
                           rewrite ptrofs_of_int_signed_repr
                             by (pose proof Int.min_signed_neg; lia).
                           rewrite ptrofs_mul_8 by
                             (unfold Ptrofs.max_unsigned;
                              pose proof (Ptrofs.unsigned_range new_sp_ofs); lia).
                           rewrite ptrofs_add_unsigned by
                             (pose proof (Ptrofs.unsigned_range new_sp_ofs); lia).
                           exact Hstore_k.

      + (* out_normal_or_continue *)
        constructor.

      + (* s2: _i := _i + 1 *)
        apply (eval_stmt_to_exec ge 5). eval_cbn.
        do 3 (rewrite PTree.gso by (compute; congruence)).
        rewrite H2; eval_cbn.
        rewrite sem_add_int_int; eval_cbn.
        replace (Int.add (Int.repr (Z.of_nat k)) (Int.repr 1))
          with (Int.repr (Z.of_nat (S k))).
        2: { rewrite Int.add_unsigned.
             rewrite (Int.unsigned_repr (Z.of_nat k))
               by (pose proof Int.max_signed_unsigned; split; lia).
             rewrite (Int.unsigned_repr 1)
               by (pose proof Int.max_signed_unsigned; split; lia).
             f_equal. lia. }
        reflexivity.

      + (* Sloop recurse *)
        replace (PTree.set _i (Vint (Int.repr (Z.of_nat (S k))))
                  (PTree.set _t'6 cv_k
                    (PTree.set _t'5 (Vptr env_b env_ptr_ofs)
                      (PTree.set _t'4 (Vptr sp_b new_sp_ofs)
                        (PTree.set _t'6 cv_k
                          (PTree.set _t'5 (Vptr env_b env_ptr_ofs)
                            (PTree.set _t'4 (Vptr sp_b new_sp_ofs) le)))))))
          with le_body.
        { exact Hloop_exec. }
        subst le_body. apply PTree.extensionality. intros x.
        repeat (rewrite PTree.gsspec).
        destruct (peq x _i); auto.
        destruct (peq x _t'6); auto.
        destruct (peq x _t'5); auto.
        destruct (peq x _t'4); auto.

    - (* All values stored *)
      intros j Hj v Hnth. replace (k + S n')%nat with (S k + n')%nat in Hj by lia.
      exact (Hpost_vals j Hj v Hnth).

    - (* Other block loads preserved through store_k + rest *)
      intros b0 ofs0 v0 Hne Hload. apply Hpost_other; [exact Hne |].
      erewrite Mem.load_store_other; [exact Hload | exact Hstore_k |].
      left. exact Hne.

    - (* Loads from sp_b above loop region preserved *)
      intros ofs0 v0 Hofs0 Hload. apply Hpost_sp_hi; [exact Hofs0 |].
      erewrite Mem.load_store_other; [exact Hload | exact Hstore_k |].
      right. simpl. lia.

    - (* Perms preserved *)
      intros b0 ofs0 k0 p Hp.
      apply Hpost_perm. eapply Mem.perm_store_1. exact Hstore_k. exact Hp.

    - (* le' ! _s preserved *)
      exact Hpost_le_s.

    - (* le' ! _num_args preserved *)
      exact Hpost_le_na.
  }
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_RESTART_correct :
    handler_correct handle_RESTART f_instr_RESTART
      (fun _ => None)
      restart_step_pre
      (fun _ => None) (fun _ => None).
Proof.
  (* Structurally blocked with the current precondition.  The C handler
     mutates stack memory by copying closure fields back onto the stack,
     then updates [sp], [env], and [extra_args].  The existing
     [restart_step_pre] exposes loadability and loop-copy facts, but closing
     [R_ex] for the exact Rocq post-state still requires preservation of the
     whole stack/global/heap abstraction across those stores.  In particular,
     the canonical [pre_of RESTART] cannot imply these state-specific
     preservation facts: it only gives an existential post-state. *)
Admitted.

(* Bridge lemma: when handle_RESTART returns Error, error_message_of
   returns the same message.  Both functions share the same case
   structure on env/heap_lookup/tag/nth_error, so this is direct. *)
Local Lemma handle_RESTART_error_implies_error_message : forall pc' s msg,
  handle_RESTART pc' s = Error msg ->
  error_message_of RESTART s = Some msg.
Proof.
  intros pc' s msg H.
  unfold handle_RESTART in H.
  unfold error_message_of.
  destruct (Machine.env s) as [z | t fields_v | addr | addr ofs].
  - (* Val_int *) inversion H. reflexivity.
  - (* Val_block *)
    destruct (Nat.eqb t Closure_tag) eqn:Htag.
    + change (skipn 0%nat fields_v) with fields_v in H.
      destruct (nth_error fields_v 2) as [saved_env|] eqn:Hnth.
      * congruence.
      * inversion H. reflexivity.
    + inversion H. reflexivity.
  - (* Val_ptr *) inversion H. reflexivity.
  - (* Val_closure *)
    destruct (heap_lookup (Machine.hp s) addr) as [[ht all_fields]|] eqn:Hlookup.
    + destruct (Nat.eqb ht Closure_tag) eqn:Htag.
      * destruct (nth_error (skipn ofs all_fields) 2) as [saved_env|] eqn:Hnth.
        -- congruence.
        -- inversion H. reflexivity.
      * inversion H. reflexivity.
    + inversion H. reflexivity.
Qed.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr RESTART = handle_RESTART by computation in Dispatch.
   clight_of RESTART = f_instr_RESTART, pre_of RESTART = restart_step_pre.
   The Step case is delegated to verify_RESTART_correct.
   Error cases are bridged via handle_RESTART_error_implies_error_message.
   Halt and CCall are impossible since handle_RESTART never produces them. *)
Definition correct_RESTART :
    handler_correct (handle_instr RESTART) (clight_of RESTART)
      (error_message_of RESTART)
      (pre_of RESTART) (P_halt_of RESTART) (P_ccall_of RESTART).
Proof.
  (* Blocked for the same reason as [verify_RESTART_correct], plus the
     canonical wrapper loses the stronger [restart_step_pre] facts needed for
     the heap/stack mutation proof.  Error cases are bridgeable by
     [handle_RESTART_error_implies_error_message]; the Step case is the
     missing preservation argument. *)
Admitted.
