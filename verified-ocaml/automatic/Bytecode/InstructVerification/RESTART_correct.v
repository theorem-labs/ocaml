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
      restart_step_pre
      (fun msg s =>
         (msg = "RESTART: env is not a block"%string /\
          match Machine.env s with
          | Val_int _ | Val_ptr _ => True
          | _ => False
          end)
         \/
         (msg = "RESTART: dangling pointer"%string /\
          exists addr ofs, Machine.env s = Val_closure addr ofs /\
          heap_lookup s.(Machine.hp) addr = None)
         \/
         (msg = "RESTART: env is not a closure"%string /\
          ((exists addr ofs t fs,
              Machine.env s = Val_closure addr ofs /\
              heap_lookup s.(Machine.hp) addr = Some (t, fs) /\
              Nat.eqb t Closure_tag = false)
           \/
           (exists t fs,
              Machine.env s = Val_block t fs /\
              Nat.eqb t Closure_tag = false)))
         \/
         (msg = "RESTART: malformed closure"%string /\
          ((exists addr ofs t all_fields,
              Machine.env s = Val_closure addr ofs /\
              heap_lookup s.(Machine.hp) addr = Some (t, all_fields) /\
              Nat.eqb t Closure_tag = true /\
              nth_error (skipn ofs all_fields) 2 = None)
           \/
           (exists t fs,
              Machine.env s = Val_block t fs /\
              Nat.eqb t Closure_tag = true /\
              nth_error fs 2 = None))))
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handle_RESTART.

  destruct (Machine.env s) as [z | t fields_v | addr | addr ofs] eqn:Henv.

  (* Case 1: env = Val_int z => Error *)
  - left. split; [reflexivity | exact I].

  (* Case 2: env = Val_block t fields_v *)
  - destruct (Nat.eqb t Closure_tag) eqn:Htag.
    + simpl skipn.
      destruct (nth_error fields_v 2) as [saved_env |] eqn:Hnth.
      * (* Step: Val_block with non-nil fields — vacuous via val_repr *)
        intros ard Hpre Hstep_pre.
        exfalso. unfold abs_rel_with_ard in Hpre.
        destruct Hpre as (_ & _ & _ & _ & [env_v [Henv_load Henv_repr]] & _).
        rewrite Henv in Henv_repr.
        inversion Henv_repr; subst.
        simpl in Hnth. discriminate Hnth.
      * right. right. right. split.
        -- reflexivity.
        -- right. exists t, fields_v. exact (conj eq_refl (conj Htag Hnth)).
    + right. right. left. split.
      * reflexivity.
      * right. exists t, fields_v. exact (conj eq_refl Htag).

  (* Case 3: env = Val_ptr addr => Error *)
  - left. split; [reflexivity | exact I].

  (* Case 4: env = Val_closure addr ofs *)
  - destruct (heap_lookup (Machine.hp s) addr) as [[ht all_fields] |] eqn:Hlookup.

    + destruct (Nat.eqb ht Closure_tag) eqn:Htag.

      * destruct (nth_error (skipn ofs all_fields) 2) as [saved_env |] eqn:Hnth.

        (* ============================================================ *)
        (* MAIN Step case: Val_closure, Closure_tag, saved_env exists   *)
        (* ============================================================ *)
        -- intros ard Hpre Hstep_pre.

           set (fields := skipn ofs all_fields) in *.
           set (num_args := Nat.sub (length fields) 3) in *.
           set (args := skipn 3 fields) in *.

           (* ---- Destruct abs_rel_with_ard ---- *)
           unfold abs_rel_with_ard in Hpre.
           set (sb := ar_sptr_block ard) in *.
           set (so := ar_sptr_ofs ard) in *.
           set (hm := ar_heap_map ard) in *.
           set (cb := ar_code_base_block ard) in *.
           set (co := ar_code_base_ofs ard) in *.
           set (gb := ar_global_block ard) in *.
           set (go_ := ar_global_ofs ard) in *.
           set (stk_b := ar_stack_block ard) in *.
           set (stk_base := ar_stack_base_ofs ard) in *.
           destruct Hpre as (Hle_s &
             [pc_ptr [Hpc_load Hpc_rel]] &
             [accu_v [Haccu_load Haccu_repr]] &
             [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr
               [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
             [env_v [Henv_load Henv_repr]] &
             Hextra_load &
             [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
             [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
           subst sp_ptr.

           pose proof (sptr_ofs_representable ard) as Hso_bound.
           fold so in Hso_bound.
           pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
           pose proof (global_block_ne_sptr ard) as Hgb_ne.
           fold sb gb in Hgb_ne.
           set (uso := Ptrofs.unsigned so) in *.

           (* ---- Invert env val_repr ---- *)
           rewrite Henv in Henv_repr.
           inversion Henv_repr as [| | ? ? env_b env_ofs delta Hhm_addr Hdelta | |]; subst env_v delta.
           set (env_ptr_ofs := Ptrofs.add env_ofs (Ptrofs.repr (Z.of_nat ofs * 8))) in *.

           (* ---- Instantiate restart_step_pre ---- *)
           unfold restart_step_pre in Hstep_pre.
           specialize (Hstep_pre addr ofs env_b env_ofs Henv Hhm_addr ht all_fields Hlookup Htag).
           assert (Hnth_ne : nth_error fields 2 <> None) by (rewrite Hnth; discriminate).
           specialize (Hstep_pre Hnth_ne).
           lazy zeta in Hstep_pre.
           change (skipn ofs all_fields) with fields in Hstep_pre.
           change (length fields - 3)%nat with num_args in Hstep_pre.
           destruct Hstep_pre as (
             [hdr_word [Hhdr_load Hhdr_shift]] &
             Hfield_load &
             Hsp_room &
             Hnum_args_bound &
             Hextra_bound &
             Henv_ne_sb &
             Henv_ptr_ge8 &
             Henv_ptr_rep).

           (* ---- SP room facts ---- *)
           specialize (Hsp_room sp_b sp_ofs Hsp_load).
           destruct Hsp_room as (Hsp_room_ge & Hsp_room_writable & Hsp_room_align &
                                 Henv_ne_sp & Hsp_new_ge8 & Hsp_new_rep).
           set (num_args_z := Z.of_nat num_args) in *.
           assert (Hnum_args_z_nonneg : 0 <= num_args_z)
             by (unfold num_args_z; lia).

           (* ---- Fields geometry ---- *)
           assert (Hfields_ge3 : (3 <= length fields)%nat).
           { apply nth_error_Some in Hnth_ne. lia. }
           assert (Hnum_args_eq : num_args = (length fields - 3)%nat) by reflexivity.
           assert (Hargs_len : length args = num_args).
           { unfold args. rewrite skipn_length. lia. }
           assert (Hfields_len : length fields = (num_args + 3)%nat) by lia.

           (* ---- env_ptr_ofs representability ---- *)
           assert (Henv_ptr_unsigned :
             Ptrofs.unsigned env_ptr_ofs = Ptrofs.unsigned env_ofs + Z.of_nat ofs * 8).
           { unfold env_ptr_ofs. rewrite ptrofs_add_unsigned.
             - reflexivity.
             - pose proof (Ptrofs.unsigned_range env_ofs). lia.
             - lia. }

           (* ---- Saved env C value ---- *)
           destruct (Hfield_load 2%nat saved_env ltac:(lia) Hnth) as [saved_env_cv [Hsaved_load Hsaved_repr]].

           (* ---- interp_state composite info ---- *)
           destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

           (* ---- new_sp_ofs ---- *)
           set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.mul (Ptrofs.repr 8)
             (ptrofs_of_int Signed (Int.repr num_args_z)))) in *.

           assert (Hnew_sp_unsigned :
             Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - num_args_z * 8).
           { subst new_sp_ofs.
             assert (IMS : Int.max_signed = 2147483647) by reflexivity.
             assert (PM : Ptrofs.modulus = 18446744073709551616) by reflexivity.
             rewrite ptrofs_of_int_signed_repr
               by (pose proof Int.min_signed_neg; lia).
             rewrite ptrofs_mul_8
               by (unfold Ptrofs.max_unsigned; lia).
             unfold Ptrofs.sub.
             rewrite (Ptrofs.unsigned_repr (num_args_z * 8)).
             2: { unfold Ptrofs.max_unsigned. lia. }
             apply Ptrofs.unsigned_repr.
             unfold Ptrofs.max_unsigned.
             pose proof (Ptrofs.unsigned_range sp_ofs). lia. }

           (* ---- SP store ---- *)
           destruct (store_succeeds_sb m sb so 16
             (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia)
             (Vptr sp_b new_sp_ofs)) as [m_sp Hsp_store].

           (* ---- Loads through sp store ---- *)
           assert (Henv_load_msp : Mem.load Mint64 m_sp sb (uso + 24) = Some (Vptr env_b env_ptr_ofs)).
           { apply (load_after_store_other m m_sp sb (uso + 16) (uso + 24)
               (Vptr sp_b new_sp_ofs) _ Hsp_store Henv_load). right. lia. }

           assert (Hsp_load_msp : Mem.load Mint64 m_sp sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
           { pose proof (Mem.load_store_same _ _ _ _ _ _ Hsp_store) as Hls.
             simpl in Hls. try rewrite Mptr_Mint64 in Hls. exact Hls. }

           assert (Hstack_repr_msp : stack_repr hm cb co m_sp (Machine.stack s) sp_b sp_ofs).
           { eapply stack_repr_store_other_block.
             - exact Hstack_repr.
             - exact Hsp_store.
             - intro Heq. apply Hsp_ne_sb. symmetry. exact Heq. }

           assert (Hperm_msp : forall b ofs0 k0 p,
             Mem.perm m b ofs0 k0 p -> Mem.perm m_sp b ofs0 k0 p).
           { intros b0 ofs0 k0 p0 Hp0. eapply Mem.perm_store_1. exact Hsp_store. exact Hp0. }

           (* ---- Loop execution ---- *)
           assert (Hloop_result : exists le_loop m_loop,
             exec e
               (PTree.set _i (Vint (Int.repr 0))
                 (PTree.set _t'7 (Vptr sp_b sp_ofs)
                   (PTree.set _num_args (Vint (Int.repr num_args_z))
                     (PTree.set _t'9 (Vlong hdr_word)
                       (PTree.set _t'8 (Vptr env_b env_ptr_ofs) le)))))
               m_sp (Sloop restart_loop_s1 restart_loop_s2) E0 le_loop m_loop Out_normal /\
             (forall j, (j < num_args)%nat ->
               forall v, nth_error fields (j + 3) = Some v ->
               exists cv, Mem.load Mint64 m_loop sp_b
                 (Ptrofs.unsigned new_sp_ofs + Z.of_nat j * 8) = Some cv /\
                 val_repr hm cb co v cv) /\
             (forall b0 ofs0 v0, b0 <> sp_b ->
               Mem.load Mint64 m_sp b0 ofs0 = Some v0 ->
               Mem.load Mint64 m_loop b0 ofs0 = Some v0) /\
             (forall ofs0 v0, ofs0 >= Ptrofs.unsigned new_sp_ofs + num_args_z * 8 ->
               Mem.load Mint64 m_sp sp_b ofs0 = Some v0 ->
               Mem.load Mint64 m_loop sp_b ofs0 = Some v0) /\
             (forall b ofs0 k0 p, Mem.perm m_sp b ofs0 k0 p -> Mem.perm m_loop b ofs0 k0 p) /\
             le_loop ! _s = Some (Vptr sb so) /\
             le_loop ! _num_args = Some (Vint (Int.repr num_args_z))).
           {
             apply restart_loop_correct with
               (n := num_args) (k := 0%nat) (num_args_z := num_args_z)
               (fields := fields) (hm := hm) (cb := cb) (co := co) (gb := gb)
               (env_b := env_b) (env_ptr_ofs := env_ptr_ofs) (sb := sb) (so := so).
             - lia.
             - exact Hnum_args_bound.
             - lia.
             - rewrite PTree.gss. reflexivity.
             - repeat (rewrite PTree.gso by (compute; congruence)).
               rewrite PTree.gss. reflexivity.
             - repeat (rewrite PTree.gso by (compute; congruence)). exact Hle_s.
             - exact Hsp_load_msp.
             - exact Henv_load_msp.
             - (* remaining fields loadable in m_sp *)
               intros j Hj v Hnth_j.
               destruct (Hfield_load (j + 3)%nat v ltac:(lia) Hnth_j) as [cv [Hload Hvr]].
               exists cv. split; [| exact Hvr].
               erewrite Mem.load_store_other; [| exact Hsp_store |].
               2: { left. intro; apply Henv_ne_sb; auto. }
               rewrite Henv_ptr_unsigned.
               replace (Ptrofs.unsigned env_ofs + Z.of_nat ofs * 8 + Z.of_nat (j + 3) * 8)
                 with (Ptrofs.unsigned env_ofs + (Z.of_nat ofs + Z.of_nat (j + 3)) * 8) by lia.
               exact Hload.
             - intros j Hj. lia.
             - intros ofs0 Hofs0.
               apply Hperm_msp. apply Hsp_room_writable. rewrite Hnew_sp_unsigned in Hofs0. simpl in Hofs0. lia.
             - exact Henv_ne_sp.
             - intro Heq. apply Hsp_ne_sb. exact Heq.
             - exact Henv_ne_sb.
             - intro; apply Hsp_ne_gb; auto.
             - intro; apply Hcb_ne_sp; auto.
             - rewrite Hnew_sp_unsigned. lia.
             - lia.
             - rewrite Hnew_sp_unsigned. unfold num_args_z.
               exact Hsp_room_align.
             - rewrite Henv_ptr_unsigned. lia.
             - pose proof (Ptrofs.unsigned_range env_ptr_ofs). lia.
             - lia.
           }
           destruct Hloop_result as (le_loop & m_loop & Hloop_exec & Hloop_vals &
             Hloop_other_block & Hloop_sp_hi & Hloop_perm &
             Hle_s_loop & Hle_na_loop).

           (* ---- Post-loop stores ---- *)

           (* Loads from sb preserved through loop (sb <> sp_b) *)
           assert (Hloop_sb : forall ofs0 v0,
             Mem.load Mint64 m_sp sb ofs0 = Some v0 ->
             Mem.load Mint64 m_loop sb ofs0 = Some v0).
           { intros ofs0 v0. apply Hloop_other_block. intro; apply Hsp_ne_sb; auto. }

           (* saved_env load in m_loop *)
           assert (Hsaved_load_mloop :
             Mem.load Mint64 m_loop env_b
               (Ptrofs.unsigned env_ofs + (Z.of_nat ofs + 2) * 8) = Some saved_env_cv).
           { apply (Hloop_other_block env_b); [exact Henv_ne_sp |].
             erewrite Mem.load_store_other; [exact Hsaved_load | exact Hsp_store |].
             left. intro; apply Henv_ne_sb; auto. }

           (* env field load in m_loop *)
           assert (Henv_field_mloop : Mem.load Mint64 m_loop sb (uso + 24) = Some (Vptr env_b env_ptr_ofs)).
           { apply (Hloop_other_block sb); [intro; apply Hsp_ne_sb; auto |].
             exact Henv_load_msp. }

           (* sb writable in m_loop *)
           assert (Hsb_writable_mloop : Mem.range_perm m_loop sb uso (uso + 56) Cur Writable).
           { intros ofs0 Hofs0. apply Hloop_perm. apply Hperm_msp. apply Hsb_writable. exact Hofs0. }

           (* Store saved_env to struct env field *)
           destruct (store_succeeds_sb m_loop sb so 24
             (Vptr env_b env_ptr_ofs) Hsb_writable_mloop Henv_field_mloop
             ltac:(lia) ltac:(lia) saved_env_cv) as [m_env Henv_store].

           (* extra_args load in m_env *)
           assert (Hextra_load_mloop : Mem.load Mint64 m_loop sb (uso + 32) =
             Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
           { apply (Hloop_other_block sb); [intro; apply Hsp_ne_sb; auto |].
             apply (load_after_store_other m m_sp sb (uso + 16) (uso + 32)
               (Vptr sp_b new_sp_ofs) _ Hsp_store Hextra_load). right. lia. }
           assert (Hextra_load_menv : Mem.load Mint64 m_env sb (uso + 32) =
             Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
           { apply (load_after_store_other m_loop m_env sb (uso + 24) (uso + 32)
               saved_env_cv _ Henv_store Hextra_load_mloop). right. lia. }

           set (new_extra := Int64.add (Int64.repr (Z.of_nat (extra_args s)))
                  (Int64.repr (Int.signed (Int.repr num_args_z)))).

           assert (Hsb_writable_menv : Mem.range_perm m_env sb uso (uso + 56) Cur Writable).
           { intros ofs0 Hofs0.
             eapply Mem.perm_store_1. exact Henv_store. apply Hsb_writable_mloop. exact Hofs0. }

           (* Store new extra_args *)
           destruct (store_succeeds_sb m_env sb so 32
             (Vlong (Int64.repr (Z.of_nat (extra_args s)))) Hsb_writable_menv Hextra_load_menv
             ltac:(lia) ltac:(lia) (Vlong new_extra)) as [m_ea Hea_store].

           (* ---- Final le ---- *)
           set (le_final := PTree.set _t'1
             (Vlong (Int64.repr (Z.of_nat (extra_args s))))
             (PTree.set _t'3 saved_env_cv
               (PTree.set _t'2 (Vptr env_b env_ptr_ofs) le_loop))) in *.

           exists le_final, m_ea, (Out_return (Some (Vint (Int.repr 0), tint))).

           split.

           (* ============================================================ *)
           (* Part 1: exec_stmt for the full body                          *)
           (* ============================================================ *)
           {
             replace E0 with (E0 ** E0) by reflexivity.
             eapply exec_Sseq_1.

             - (* Pre1: t8 = s->env, t9 = *(env + (-1)), num_args = cast(t9>>10 - 3) *)
               apply (eval_stmt_to_exec ge 20). eval_cbn.
               rewrite Hle_s; eval_cbn.
               rewrite Hco; eval_cbn.
               assert (Henv_ofs : field_offset ge _env (co_members co_is) = Errors.OK (24, Full)).
               { destruct interp_state_co_env as [co' [Hco' [Henv' _]]].
                 assert (co_is = co') by congruence. subst. exact Henv'. }
               rewrite Henv_ofs; eval_cbn.
               try rewrite Mptr_Mint64; eval_cbn.
               rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
               fold uso. rewrite Henv_load; eval_cbn.
               rewrite PTree.gss; eval_cbn.
               rewrite sem_cast_long_to_ptr_vptr; eval_cbn.
               rewrite sem_neg_int; eval_cbn.
               rewrite sem_add_ptr_int_i; eval_cbn.
               try rewrite Mptr_Mint64; eval_cbn.
               change (Int.neg (Int.repr 1)) with (Int.repr (-1)).
               rewrite ptrofs_of_int_signed_repr by (pose proof Int.min_signed_neg; lia).
               change (Ptrofs.repr (-1)) with Ptrofs.mone.
               rewrite Ptrofs.mul_mone.
               rewrite <- Ptrofs.sub_add_opp.
               unfold Ptrofs.sub.
               replace (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
               2: { symmetry. apply Ptrofs.unsigned_repr.
                    assert (PM : Ptrofs.modulus = 18446744073709551616) by reflexivity.
                    unfold Ptrofs.max_unsigned. lia. }
               replace (Ptrofs.unsigned env_ptr_ofs - 8) with
                 (Ptrofs.unsigned env_ofs + Z.of_nat ofs * 8 - 8) by
                 (rewrite Henv_ptr_unsigned; lia).
               rewrite Ptrofs.unsigned_repr.
               2: { pose proof (Ptrofs.unsigned_range env_ofs).
                    assert (PM : Ptrofs.modulus = 18446744073709551616) by reflexivity.
                    unfold Ptrofs.max_unsigned. lia. }
               rewrite Hhdr_load; eval_cbn.
               rewrite PTree.gss; eval_cbn.
               rewrite sem_shr_long_int_10; eval_cbn.
               rewrite Hhdr_shift; eval_cbn.
               rewrite sem_sub_long_int; eval_cbn.
               rewrite sem_cast_long_to_int; eval_cbn.
               replace (Int64.sub (Int64.repr (Z.of_nat (length fields))) (Int64.repr (Int.signed (Int.repr 3))))
                 with (Int64.repr num_args_z).
               2: { assert (IMS : Int.max_signed = 2147483647) by reflexivity.
                    unfold num_args_z, num_args.
                    rewrite Int.signed_repr by (pose proof Int.min_signed_neg; lia).
                    unfold Int64.sub. f_equal.
                    rewrite (Int64.unsigned_repr (Z.of_nat (length fields))).
                    2: { split. { lia. }
                         assert (PM64 : Int64.modulus = 18446744073709551616) by reflexivity.
                         unfold Int64.max_unsigned. lia. }
                    rewrite (Int64.unsigned_repr 3).
                    2: { split. { lia. }
                         assert (PM64 : Int64.modulus = 18446744073709551616) by reflexivity.
                         unfold Int64.max_unsigned. lia. }
                    rewrite Nat2Z.inj_sub by lia. reflexivity. }
               replace (Int.repr (Int64.unsigned (Int64.repr num_args_z)))
                 with (Int.repr num_args_z).
               2: { f_equal. rewrite Int64.unsigned_repr.
                    - reflexivity.
                    - split. { unfold num_args_z. lia. }
                      assert (IMS : Int.max_signed = 2147483647) by reflexivity.
                      assert (PM64 : Int64.modulus = 18446744073709551616) by reflexivity.
                      unfold Int64.max_unsigned. lia. }
               reflexivity.

             - (* Rest: pre2 + loop + post + return *)
               replace E0 with (E0 ** E0) by reflexivity.
               eapply exec_Sseq_1.

               + (* Pre2: t7 = s->sp, s->sp = t7 - num_args *)
                 replace E0 with (E0 ** E0) by reflexivity.
                 eapply exec_Sseq_1.
                 * (* Sset _t'7 *)
                   apply (eval_stmt_to_exec ge 10). eval_cbn.
                   repeat (rewrite PTree.gso by (compute; congruence)).
                   rewrite Hle_s; eval_cbn.
                   rewrite Hco; eval_cbn. rewrite Hsp_offset; eval_cbn.
                   try rewrite Mptr_Mint64; eval_cbn.
                   rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
                   fold uso. rewrite Hsp_load; eval_cbn. reflexivity.
                 * (* Sassign s->sp *)
                   eapply exec_Sassign.
                   -- eapply eval_Efield_struct.
                      ++ eapply eval_Elvalue.
                         ** eapply eval_Ederef. eapply eval_Etempvar.
                            repeat (rewrite PTree.gso by (compute; congruence)).
                            exact Hle_s.
                         ** apply deref_loc_copy. simpl. reflexivity.
                      ++ simpl. reflexivity.
                      ++ exact Hco.
                      ++ exact Hsp_offset.
                   -- econstructor.
                      ++ econstructor. rewrite PTree.gss. reflexivity.
                      ++ econstructor.
                         repeat (rewrite PTree.gso by (compute; congruence)).
                         rewrite PTree.gss. reflexivity.
                      ++ exact (sem_sub_ptr_int sp_b sp_ofs (Int.repr num_args_z) m).
                   -- unfold sem_cast. simpl classify_cast. reflexivity.
                   -- apply assign_loc_value with (chunk := Mint64).
                      ++ simpl. reflexivity.
                      ++ simpl. rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
                         fold uso. exact Hsp_store.

               + (* Loop + post + return *)
                 replace E0 with (E0 ** E0) by reflexivity.
                 eapply exec_Sseq_1.

                 * (* Loop with init: i = 0; loop *)
                   replace E0 with (E0 ** E0) by reflexivity.
                   eapply exec_Sseq_1.
                   -- apply (eval_stmt_to_exec ge 2). eval_cbn. reflexivity.
                   -- exact Hloop_exec.

                 * (* Post: env update + extra_args update + return *)
                   replace E0 with (E0 ** E0) by reflexivity.
                   eapply exec_Sseq_1.
                   -- (* t2 = s->env, t3 = *(cast(t2) + 2), s->env = t3 *)
                      replace E0 with (E0 ** E0) by reflexivity.
                      eapply exec_Sseq_1.
                      ++ (* Sset _t'2 *)
                         assert (Henv_ofs2 : field_offset ge _env (co_members co_is) = Errors.OK (24, Full)).
                         { destruct interp_state_co_env as [co' [Hco' [Henv' _]]].
                           assert (co_is = co') by congruence. subst. exact Henv'. }
                         apply (eval_stmt_to_exec ge 10). eval_cbn.
                         repeat (rewrite PTree.gso by (compute; congruence)).
                         rewrite Hle_s_loop; eval_cbn.
                         rewrite Hco; eval_cbn.
                         rewrite Henv_ofs2; eval_cbn.
                         try rewrite Mptr_Mint64; eval_cbn.
                         rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
                         fold uso. rewrite Henv_field_mloop; eval_cbn.
                         reflexivity.
                      ++ (* Sset _t'3 ; Sassign s->env *)
                         replace E0 with (E0 ** E0) by reflexivity.
                         eapply exec_Sseq_1.
                         ** (* Sset _t'3: load env[2] *)
                            apply (eval_stmt_to_exec ge 6). eval_cbn.
                            rewrite PTree.gss; eval_cbn.
                            rewrite sem_cast_long_to_ptr_vptr; eval_cbn.
                            rewrite sem_add_ptr_int_i; eval_cbn.
                            try rewrite Mptr_Mint64; eval_cbn.
                            rewrite ptrofs_of_int_signed_repr by (pose proof Int.min_signed_neg; lia).
                            rewrite ptrofs_mul_8 by
                              (unfold Ptrofs.max_unsigned; pose proof Ptrofs.modulus_pos; lia).
                            rewrite ptrofs_add_unsigned by
                              (try rewrite Henv_ptr_unsigned;
                               pose proof (Ptrofs.unsigned_range env_ofs); lia).
                            replace (Ptrofs.unsigned env_ptr_ofs + 2 * 8)
                              with (Ptrofs.unsigned env_ofs + (Z.of_nat ofs + 2) * 8)
                              by (rewrite Henv_ptr_unsigned; lia).
                            rewrite Hsaved_load_mloop; eval_cbn.
                            try rewrite (val_repr_load_result _ _ _ _ _ Hsaved_repr).
                            reflexivity.
                         ** (* Sassign s->env = t3 *)
                            assert (Henv_ofs2 : field_offset ge _env (co_members co_is) = Errors.OK (24, Full)).
                            { destruct interp_state_co_env as [co' [Hco' [Henv' _]]].
                              assert (co_is = co') by congruence. subst. exact Henv'. }
                            eapply exec_Sassign.
                            --- eapply eval_Efield_struct.
                                +++ eapply eval_Elvalue.
                                    *** eapply eval_Ederef. eapply eval_Etempvar.
                                         repeat (rewrite PTree.gso by (compute; congruence)).
                                         exact Hle_s_loop.
                                    *** apply deref_loc_copy. simpl. reflexivity.
                                +++ simpl. reflexivity.
                                +++ exact Hco.
                                +++ rewrite Henv_ofs2. reflexivity.
                            --- econstructor. rewrite PTree.gss. reflexivity.
                            --- exact (sem_cast_long_val_repr _ _ _ _ _ m_loop Hsaved_repr).
                            --- apply assign_loc_value with (chunk := Mint64).
                                +++ simpl. reflexivity.
                                +++ simpl. rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
                                    fold uso. exact Henv_store.
                   -- (* t1 = s->extra_args, s->extra_args = t1 + num_args, return 0 *)
                      replace E0 with (E0 ** E0) by reflexivity.
                      eapply exec_Sseq_1.
                      ++ (* t1 = s->extra_args, s->extra_args = t1 + num_args *)
                         replace E0 with (E0 ** E0) by reflexivity.
                         eapply exec_Sseq_1.
                         ** (* Sset _t'1 *)
                            assert (Hextra_ofs : field_offset ge _extra_args (co_members co_is) = Errors.OK (32, Full)).
                            { destruct interp_state_co_extra as [co' [Hco' Hextra']].
                              assert (co_is = co') by congruence. subst. exact Hextra'. }
                            apply (eval_stmt_to_exec ge 10). eval_cbn.
                            repeat (rewrite PTree.gso by (compute; congruence)).
                            rewrite Hle_s_loop; eval_cbn.
                            rewrite Hco; eval_cbn.
                            rewrite Hextra_ofs; eval_cbn.
                            try rewrite Mptr_Mint64; eval_cbn.
                            rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
                            fold uso. rewrite Hextra_load_menv; eval_cbn. reflexivity.
                         ** (* Sassign s->extra_args = t1 + num_args *)
                            assert (Hextra_ofs : field_offset ge _extra_args (co_members co_is) = Errors.OK (32, Full)).
                            { destruct interp_state_co_extra as [co' [Hco' Hextra']].
                              assert (co_is = co') by congruence. subst. exact Hextra'. }
                            eapply exec_Sassign.
                            --- eapply eval_Efield_struct.
                                +++ eapply eval_Elvalue.
                                    *** eapply eval_Ederef. eapply eval_Etempvar.
                                        repeat (rewrite PTree.gso by (compute; congruence)).
                                        exact Hle_s_loop.
                                    *** apply deref_loc_copy. simpl. reflexivity.
                                +++ simpl. reflexivity.
                                +++ exact Hco.
                                +++ rewrite Hextra_ofs. reflexivity.
                            --- econstructor.
                                +++ econstructor. rewrite PTree.gss. reflexivity.
                                +++ econstructor.
                                    repeat (rewrite PTree.gso by (compute; congruence)).
                                    exact Hle_na_loop.
                                +++ exact (sem_add_long_int
                                      (Int64.repr (Z.of_nat (extra_args s)))
                                      (Int.repr num_args_z) m_env).
                            --- unfold sem_cast. simpl classify_cast. reflexivity.
                            --- apply assign_loc_value with (chunk := Mint64).
                                +++ simpl. reflexivity.
                                +++ simpl. rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
                                    fold uso. exact Hea_store.
                      ++ (* Return 0 *)
                         econstructor. econstructor.
           }

           (* ============================================================ *)
           (* Part 2: abs_rel for post-state                               *)
           (* ============================================================ *)
           {
             exists ard.
             unfold abs_rel_with_ard.
             fold sb so hm cb co gb go_ stk_b stk_base.

             (* Helper: threading loads through env_store and ea_store *)
             assert (Hload_sb_final : forall ofs0 v0,
               Mem.load Mint64 m_loop sb ofs0 = Some v0 ->
               ofs0 + 8 <= uso + 24 \/ uso + 40 <= ofs0 ->
               Mem.load Mint64 m_ea sb ofs0 = Some v0).
             { intros ofs0 v0 Hload Hrange.
               apply (load_after_store_other m_env m_ea sb (uso + 32) ofs0
                 (Vlong new_extra) v0 Hea_store).
               2: { lia. }
               apply (load_after_store_other m_loop m_env sb (uso + 24) ofs0
                 saved_env_cv v0 Henv_store Hload). lia. }

             (* pc *)
             assert (Hpc_final : Mem.load Mint64 m_ea sb (uso + 0) = Some pc_ptr).
             { apply Hload_sb_final; [| lia].
               apply Hloop_sb.
               apply (load_after_store_other m m_sp sb (uso + 16) (uso + 0)
                 (Vptr sp_b new_sp_ofs) _ Hsp_store Hpc_load). left. lia. }

             (* accu *)
             assert (Haccu_final : Mem.load Mint64 m_ea sb (uso + 8) = Some accu_v).
             { apply Hload_sb_final; [| lia].
               apply Hloop_sb.
               apply (load_after_store_other m m_sp sb (uso + 16) (uso + 8)
                 (Vptr sp_b new_sp_ofs) _ Hsp_store Haccu_load). left. lia. }

             (* sp *)
             assert (Hsp_final : Mem.load Mint64 m_ea sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
             { apply Hload_sb_final; [| lia].
               exact (Hloop_sb _ _ Hsp_load_msp). }

             (* env *)
             assert (Henv_final : Mem.load Mint64 m_ea sb (uso + 24) = Some saved_env_cv).
             { apply (load_after_store_other m_env m_ea sb (uso + 32) (uso + 24)
                 (Vlong new_extra) _ Hea_store).
               2: { left. lia. }
               pose proof (Mem.load_store_same _ _ _ _ _ _ Henv_store) as Hsame.
               simpl decode_encode_val in Hsame.
               rewrite (val_repr_load_result _ _ _ _ _ Hsaved_repr) in Hsame.
               fold uso in Hsame. exact Hsame. }

             (* extra_args *)
             assert (Hextra_final : Mem.load Mint64 m_ea sb (uso + 32) = Some (Vlong new_extra)).
             { pose proof (Mem.load_store_same _ _ _ _ _ _ Hea_store) as Hsame.
               simpl in Hsame. exact Hsame. }

             (* global data *)
             assert (Hgd_final : Mem.load Mint64 m_ea sb (uso + 40) = Some gd_ptr).
             { apply Hload_sb_final; [| lia].
               apply Hloop_sb.
               apply (load_after_store_other m m_sp sb (uso + 16) (uso + 40)
                 (Vptr sp_b new_sp_ofs) _ Hsp_store Hgd_load). right. lia. }

             (* trap_sp *)
             assert (Hts_final : Mem.load Mint64 m_ea sb (uso + 48) = Some ts_ptr).
             { apply Hload_sb_final; [| lia].
               apply Hloop_sb.
               apply (load_after_store_other m m_sp sb (uso + 16) (uso + 48)
                 (Vptr sp_b new_sp_ofs) _ Hsp_store Hts_load). right. lia. }

             (* sb writable in m_ea *)
             assert (Hsb_writable_final : Mem.range_perm m_ea sb uso (uso + 56) Cur Writable).
             { intros ofs0 Hofs0.
               eapply Mem.perm_store_1. exact Hea_store.
               eapply Mem.perm_store_1. exact Henv_store.
               apply Hsb_writable_mloop. exact Hofs0. }

             (* stack_repr for args ++ old_stack *)
             assert (Hstack_final :
               stack_repr hm cb co m_ea (args ++ Machine.stack s) sp_b new_sp_ofs).
             {
               (* Convert new_sp_ofs to Ptrofs.repr form *)
               replace new_sp_ofs with (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs))
                 by (rewrite Ptrofs.repr_unsigned; reflexivity).

               apply build_stack_repr_prefix.
               - (* Individual loads for args *)
                 intros j v Hnth_j.
                 (* args[j] = fields[j+3] — via skipn *)
                 assert (Hargs_nth : nth_error fields (j + 3) = Some v).
                 { unfold args in Hnth_j. rewrite nth_error_skipn in Hnth_j.
                   replace (j + 3)%nat with (3 + j)%nat by lia. exact Hnth_j. }
                 destruct (Hloop_vals j ltac:(
                    assert (Hne : nth_error args j <> None) by (rewrite Hnth_j; discriminate);
                    apply nth_error_Some in Hne; lia)
                   v Hargs_nth) as [cv [Hload Hvr]].
                 exists cv. split; [| exact Hvr].
                 (* Thread through env_store and ea_store (both on sb, not sp_b) *)
                 erewrite Mem.load_store_other. 2: exact Hea_store. 2: left; intro; apply Hsp_ne_sb; auto.
                 erewrite Mem.load_store_other. 2: exact Henv_store. 2: left; intro; apply Hsp_ne_sb; auto.
                 exact Hload.
               - (* Old stack_repr at sp_ofs = new_sp_ofs + num_args * 8 *)
                 replace (Ptrofs.unsigned new_sp_ofs + Z.of_nat (length args) * 8)
                   with (Ptrofs.unsigned sp_ofs) by (rewrite Hargs_len, Hnew_sp_unsigned; lia).
                 rewrite Ptrofs.repr_unsigned.
                 (* Thread old stack_repr through all post-loop stores *)
                 (* m → m_sp: store to sb, sb <> sp_b *)
                 assert (Hsr_msp : stack_repr hm cb co m_sp (Machine.stack s) sp_b sp_ofs).
                 { eapply stack_repr_store_other_block; [exact Hstack_repr | exact Hsp_store |].
                   intro; apply Hsp_ne_sb; auto. }
                 (* m_sp → m_loop: loop stores at sp_b below sp_ofs *)
                 assert (Hsr_mloop : stack_repr hm cb co m_loop (Machine.stack s) sp_b sp_ofs).
                 { apply (stack_repr_load_preserved_above hm cb co m_sp _ _ sp_b sp_ofs
                   (Ptrofs.unsigned new_sp_ofs + num_args_z * 8) Hsr_msp).
                   - rewrite Hnew_sp_unsigned. lia.
                   - rewrite Nat2Z.inj_add in Hsp_new_rep. lia.
                   - intros ofs0 v0 Hge Hload_sr.
                     apply Hloop_sp_hi; [exact Hge | exact Hload_sr]. }
                 (* m_loop → m_env: store to sb, sb <> sp_b *)
                 assert (Hsr_menv : stack_repr hm cb co m_env (Machine.stack s) sp_b sp_ofs).
                 { eapply stack_repr_store_other_block; [exact Hsr_mloop | exact Henv_store |].
                   intro; apply Hsp_ne_sb; auto. }
                 (* m_env → m_ea: store to sb, sb <> sp_b *)
                 eapply stack_repr_store_other_block; [exact Hsr_menv | exact Hea_store |].
                 intro; apply Hsp_ne_sb; auto.
               - pose proof (Ptrofs.unsigned_range new_sp_ofs). lia.
               - rewrite Hargs_len. rewrite Hnew_sp_unsigned. lia.
               - rewrite Hnew_sp_unsigned. exact Hsp_room_align.
             }

             (* Now construct abs_rel *)
             split.
             -- (* le_s *) subst le_final.
                repeat (rewrite PTree.gso by (compute; congruence)).
                exact Hle_s_loop.
             -- split.
                ** (* pc_rel *)
                   exists pc_ptr. split; [exact Hpc_final | exact Hpc_rel].
                ** split.
                   --- (* accu *)
                       exists accu_v. split; [exact Haccu_final |].
                       eapply val_repr_co_shift. exact Haccu_repr.
                   --- split.
                       +++ (* sp + stack_repr *)
                           exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
                           split; [exact Hsp_final |].
                           split; [reflexivity |].
                           split.
                           *** eapply stack_repr_co_shift. exact Hstack_final.
                           *** split; [exact Hsp_ne_sb |].
                               split; [exact Hsp_ne_gb |].
                               split; [exact Hcb_ne_sp |].
                               split; [rewrite Hnew_sp_unsigned; exact Hsp_new_ge8 |].
                               split.
                               ---- rewrite Hnew_sp_unsigned. simpl Machine.stack.
                                    rewrite app_length, Hargs_len.
                                    rewrite Nat2Z.inj_add in Hsp_new_rep |- *. lia.
                               ---- split.
                                    ++++ intros ofs0 Hofs0.
                                         eapply Mem.perm_store_1; [exact Hea_store |].
                                         eapply Mem.perm_store_1; [exact Henv_store |].
                                         apply Hloop_perm. apply Hperm_msp.
                                         apply Hsp_writable.
                                         rewrite Hnew_sp_unsigned in Hofs0.
                                         simpl Machine.stack in Hofs0.
                                         rewrite app_length in Hofs0.
                                         rewrite Hargs_len in Hofs0.
                                         rewrite Nat2Z.inj_add in Hofs0.
                                         unfold num_args_z in Hofs0. lia.
                                    ++++ rewrite Hnew_sp_unsigned. exact Hsp_room_align.
                       +++ split.
                           *** (* env *)
                               exists saved_env_cv. split; [exact Henv_final |].
                               eapply val_repr_co_shift. exact Hsaved_repr.
                           *** split.
                               ---- (* extra_args *)
                                    simpl Machine.extra_args.
                                    rewrite Nat2Z.inj_add.
                                    fold uso.
                                    rewrite Hextra_final. unfold new_extra.
                                    unfold num_args_z.
                                    assert (Hna_signed : Int.signed (Int.repr (Z.of_nat num_args)) = Z.of_nat num_args).
                                    { apply Int.signed_repr.
                                      unfold Int.min_signed, Int.max_signed,
                                        Int.half_modulus, Int.modulus,
                                        Int.wordsize, Wordsize_32.wordsize in Hnum_args_bound |- *.
                                      simpl in Hnum_args_bound |- *. lia. }
                                    rewrite Hna_signed.
                                    rewrite Int64.add_unsigned.
                                    rewrite !Int64.unsigned_repr
                                      by (unfold Int64.max_unsigned; lia).
                                    reflexivity.
                               ---- split.
                                    ++++ (* global_repr *)
                                         simpl Machine.global.
                                         exists gd_ptr. split; [exact Hgd_final |].
                                         split; [exact Hgd_eq |].
                                         split.
                                         **** eapply global_repr_co_shift.
                                              (* Thread global_repr through: m → m_sp → m_loop → m_env → m_ea *)
                                              eapply global_repr_store_other_block;
                                                [| exact Hea_store | intro; apply Hgb_ne_sb; auto].
                                              eapply global_repr_store_other_block;
                                                [| exact Henv_store | intro; apply Hgb_ne_sb; auto].
                                              eapply global_repr_load_preserved;
                                                [| intros ofs0 v0; apply (Hloop_other_block gb);
                                                   intro; apply Hsp_ne_gb; auto].
                                              eapply global_repr_store_other_block;
                                                [exact Hglobal_repr | exact Hsp_store |].
                                              intro; apply Hgb_ne_sb; auto.
                                         **** exact Hgb_ne_sb.
                                    ++++ split.
                                         **** (* trap_sp_rel *)
                                              exists ts_ptr. split; [exact Hts_final |].
                                              exact Htrap_rel.
                                         **** (* sb_writable *)
                                              exact Hsb_writable_final.
           }

        (* Error "malformed closure" *)
        -- right. right. right. split.
           ++ reflexivity.
           ++ left. exists addr, ofs, ht, all_fields.
              exact (conj eq_refl (conj Hlookup (conj Htag Hnth))).

      * right. right. left. split.
        -- reflexivity.
        -- left. exists addr, ofs, ht, all_fields.
           exact (conj eq_refl (conj Hlookup Htag)).

    + right. left. split.
      * reflexivity.
      * exists addr, ofs. exact (conj eq_refl Hlookup).
Qed.

(* Bridge lemma: when handle_RESTART returns Error, error_message_of
   returns the same message.  Both functions share the same case
   structure on env/heap_lookup/tag/nth_error, so this is direct. *)
Local Lemma handle_RESTART_error_implies_error_message : forall pc' s msg,
  handle_RESTART pc' s = Error msg ->
  error_message_of RESTART s = Some msg.
Proof.
  intros pc' s msg H.
  unfold handle_RESTART in H.
  unfold P_error_of, error_message_of.
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
      (pre_of RESTART)
      (P_error_of RESTART) (P_halt_of RESTART) (P_ccall_of RESTART).
Proof.
Admitted.
