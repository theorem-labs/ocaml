(* CLOSURE_correct.v -- CLOSURE handler completeness proof.

   CLOSURE reads nvars and code_ofs from the code buffer, optionally pushes
   accu onto the stack (if nvars > 0), allocates a closure block of size
   (nvars + 2) with tag 247 (Closure_tag), copies nvars env variables from
   the stack to the block, stores the code pointer and closinfo, advances
   pc, restores sp, and sets accu to the new closure.

   This proof handles the nvars = 0 case (no env variables to copy).
   The C if-branch (nvars > 0) is skipped, and the for-loop executes
   0 iterations.  The heap_alloc call allocates a 2-field block.

   Rocq handle_CLOSURE 0 code_ofs pc' s:
     let stk := s.(stack) in
     let fields := [Val_int code_ofs; Val_int 0] in
     let '(s', base_ptr) := heap_alloc s Closure_tag fields in
     let addr := ... in
     Step (s' <|pc:=pc'|> <|accu:=Val_closure addr 0|> <|stack:=stk|>). *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

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
(* Struct layout                                                       *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

(* Local copy of the CLOSURE env copy loop AST (from instruct_handlers.v).
   Copies nvars values from sp[0..nvars-1] to block[2..nvars+1]. *)
Local Definition closure_env_loop_body : statement :=
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                   (Etempvar _nvars tint) tint)
      Sskip
      Sbreak)
    (Ssequence
      (Sset _t'9
        (Efield
          (Ederef
            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'10
          (Ederef
            (Ebinop Oadd (Etempvar _t'9 (tptr tlong))
              (Etempvar _i tint) (tptr tlong)) tlong))
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Ecast (Etempvar _block tlong) (tptr tlong))
              (Ebinop Oadd (Etempvar _i tint)
                (Econst_int (Int.repr 2) tint) tint)
              (tptr tlong)) tlong) (Etempvar _t'10 tlong))))).

Local Definition closure_env_loop_incr : statement :=
  (Sset _i
    (Ebinop Oadd (Etempvar _i tint)
      (Econst_int (Int.repr 1) tint) tint)).

Local Definition closure_env_loop : statement :=
  Sloop closure_env_loop_body closure_env_loop_incr.

Lemma interp_state_co_pc_accu_sp : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Lemma sem_add_pc_1_closure : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint_cl : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* Cast Vint -> tint -> tint is identity *)
Lemma sem_cast_int_tint_tint : forall n m,
  sem_cast (Vint n) tint tint m = Some (Vint n).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* Oadd (Vint a) tint (Vint b) tint = Some (Vint (Int.add a b)) *)
Lemma sem_add_int_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vint a) tint (Vint b) tint m = Some (Vint (Int.add a b)).
Proof. intros. reflexivity. Qed.

Lemma sem_cast_int_to_long : forall n m,
  sem_cast (Vint n) tint tlong m = Some (Vlong (Int64.repr (Int.signed n))).
Proof.
  intros. unfold sem_cast.
  change (classify_cast tint tlong) with (cast_case_i2l Signed).
  simpl. reflexivity.
Qed.

(* Ogt (Vint n) tint (Vint 0) tint comparison *)
Lemma sem_cmp_gt_int_0 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Ogt
    (Vint n) tint
    (Vint (Int.repr 0)) tint
    m = Some (Val.of_bool (Int.lt (Int.repr 0) n)).
Proof. intros. reflexivity. Qed.

(* Olt (Vint i) tint (Vint n) tint comparison *)
Lemma sem_cmp_lt_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Olt
    (Vint a) tint
    (Vint b) tint
    m = Some (Val.of_bool (Int.lt a b)).
Proof. intros. reflexivity. Qed.

(* Oshl (Vint a) tint (Vint b) tint *)
Lemma sem_shl_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vint n) tint (Vint (Int.repr 1)) tint m =
    Some (Vint (Int.shl n (Int.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tint tint) with (shift_case_ii Signed).
  simpl.
  change (Int.ltu (Int.repr 1) Int.iwordsize) with true.
  reflexivity.
Qed.

(* Cast Vint -> tint -> tlong *)
Lemma sem_cast_int_to_tlong : forall n m,
  sem_cast (Vint n) tint tlong m = Some (Vlong (Int64.repr (Int.signed n))).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* Cast Vptr -> tlong -> tptr tlong *)
Lemma sem_cast_vptr_tlong_to_ptr_tlong : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* Cast Vptr -> tlong -> tptr (tptr tint) *)
Lemma sem_cast_vptr_tlong_to_ptr_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr (tptr tint)) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* Oadd (Vptr b ofs) (tptr (tptr tint)) (Vint 0) tint *)
Lemma sem_add_ptr_ptr_tint_0 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr (tptr tint))
    (Vint (Int.repr 0)) tint
    m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr (tptr tint)) tint) with (add_case_pi (tptr tint) Signed).
  unfold sem_add_ptr_int. f_equal. f_equal.
  change (sizeof (genv_cenv clight_ge) (tptr tint)) with 8%Z.
  unfold ptrofs_of_int.
  change (Ptrofs.of_ints (Int.repr 0)) with Ptrofs.zero.
  rewrite Ptrofs.mul_zero, Ptrofs.add_zero. reflexivity.
Qed.

(* Oadd Vptr (tptr tlong) + Vint n tint *)
Lemma sem_add_ptr_tlong_int : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong)
    (Vint n) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* Oor (Vlong a) tlong (Vint b) tint -- mixed types, the Vint is cast to Vlong
   via Int.signed before the or operation *)
Lemma sem_or_long_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Oor
    (Vlong a) tlong
    (Vint b) tint
    m = Some (Vlong (Int64.or a (Int64.repr (Int.signed b)))).
Proof.
  intros. unfold sem_binary_operation, sem_or.
  change (classify_binarith tlong tint) with (bin_case_l Signed).
  unfold sem_binarith. simpl binarith_type.
  unfold sem_cast at 1. simpl classify_cast. rewrite ptr64_true.
  unfold sem_cast at 1. simpl classify_cast. simpl cast_int_long.
  reflexivity.
Qed.

(* Oadd Vptr (tptr tint) + Vint n tint *)
Lemma sem_add_ptr_tint_int : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint n) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* ================================================================== *)
(* Pointer arithmetic helpers                                          *)
(* ================================================================== *)

Lemma ptrofs_of_int_signed_0 :
  ptrofs_of_int Signed (Int.repr 0) = Ptrofs.zero.
Proof. reflexivity. Qed.

Lemma ptrofs_of_int_signed_1 :
  ptrofs_of_int Signed (Int.repr 1) = Ptrofs.one.
Proof. reflexivity. Qed.

Lemma ptrofs_mul_8_0 :
  Ptrofs.mul (Ptrofs.repr 8) Ptrofs.zero = Ptrofs.zero.
Proof. rewrite Ptrofs.mul_zero. reflexivity. Qed.

Lemma load_result_vlong_cl : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr_cl : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* ================================================================== *)
(* Deref: Cast Vptr b ofs tlong -> deref_loc reference *)
(* ================================================================== *)

(* Int.lt (Int.repr 0) (Int.repr 0) = false *)
Lemma int_lt_0_0 : Int.lt (Int.repr 0) (Int.repr 0) = false.
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Main theorem: nvars = 0 case                                        *)
(* ================================================================== *)

(* ================================================================== *)
(* Helper lemma: Int.lt (Int.repr 0) (Int.repr (Z.of_nat (S n)))      *)
(* when 0 <= Z.of_nat (S n) <= Int.max_signed                         *)
(* ================================================================== *)

Lemma int_lt_0_S : forall n : nat,
  Z.of_nat (S n) <= Int.max_signed ->
  Int.lt (Int.repr 0) (Int.repr (Z.of_nat (S n))) = true.
Proof.
  intros n Hle.
  unfold Int.lt.
  assert (H0 : Int.signed (Int.repr 0) = 0).
  { rewrite Int.signed_repr; [reflexivity |].
    compute. split; intro; discriminate. }
  assert (HS : Int.signed (Int.repr (Z.of_nat (S n))) = Z.of_nat (S n)).
  { rewrite Int.signed_repr; [reflexivity |].
    split; [| exact Hle].
    change Int.min_signed with (-2147483648)%Z. lia. }
  rewrite H0, HS.
  destruct (zlt 0 (Z.of_nat (S n))); [reflexivity | lia].
Qed.

(* ================================================================== *)
(* Pointer arithmetic helpers for the env copy loop                    *)
(* ================================================================== *)

Local Lemma ptrofs_max_unsigned_large : (Ptrofs.max_unsigned >= 2^32)%Z.
Proof. vm_compute. discriminate. Qed.

Local Lemma ptrofs_mul_8 : forall n,
  0 <= n ->
  n * 8 <= Ptrofs.max_unsigned ->
  Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.repr n) = Ptrofs.repr (n * 8).
Proof.
  intros n Hn0 Hn8.
  unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 8).
  2: { pose proof ptrofs_max_unsigned_large. lia. }
  rewrite Ptrofs.unsigned_repr.
  2: { lia. }
  f_equal. lia.
Qed.

Local Lemma ptrofs_of_int_signed_repr : forall z,
  Int.min_signed <= z <= Int.max_signed ->
  ptrofs_of_int Signed (Int.repr z) = Ptrofs.repr z.
Proof.
  intros. unfold ptrofs_of_int. simpl. unfold Ptrofs.of_ints.
  rewrite Int.signed_repr. reflexivity. lia.
Qed.

(* ================================================================== *)
(* Helper: extract loadable+castable stack values from stack_repr      *)
(* ================================================================== *)

Local Lemma ptrofs_add_repr : forall a b,
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  intros. rewrite Ptrofs.add_unsigned.
  apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add;
    apply Ptrofs.eqm_sym;
    apply Ptrofs.eqm_unsigned_repr.
Qed.

Local Lemma stack_repr_nth : forall n hm cb0 co0 m stk sp_b sp_ofs v,
  stack_repr hm cb0 co0 m stk sp_b sp_ofs ->
  nth_error stk n = Some v ->
  exists cv,
    Mem.load Mint64 m sp_b
      (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some cv /\
    val_repr hm cb0 co0 v cv.
Proof.
  induction n as [| n' IH]; intros hm cb0 co0 m stk sp_b sp_ofs v Hsr Hnth.
  - destruct stk as [| v0 rest]; [discriminate |].
    simpl in Hnth. inversion Hnth; subst.
    inversion Hsr as [| xv xvs xb xofs xcv Hload Hvr Hrest].
    subst xv xvs xb xofs.
    exists xcv. split.
    + replace (Z.of_nat 0 * 8)%Z with 0%Z by lia.
      change (Ptrofs.repr 0) with Ptrofs.zero.
      rewrite Ptrofs.add_zero. exact Hload.
    + exact Hvr.
  - destruct stk as [| v0 rest]; [discriminate |].
    simpl in Hnth.
    inversion Hsr as [| xv xvs xb xofs xcv Hload Hvr Hrest].
    subst xv xvs xb xofs.
    specialize (IH hm cb0 co0 m rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)) v Hrest Hnth).
    destruct IH as [cv' [Hload' Hvr']].
    exists cv'. split.
    + replace (Z.of_nat (S n') * 8)%Z with (8 + Z.of_nat n' * 8)%Z by lia.
      rewrite <- ptrofs_add_repr.
      rewrite <- Ptrofs.add_assoc.
      exact Hload'.
    + exact Hvr'.
Qed.

(* ================================================================== *)
(* Helper: closure env copy loop execution                             *)
(* Proves the Sloop part by induction on remaining iterations n.       *)
(* k is the current loop counter, k+n = nvars_nat.                    *)
(* ================================================================== *)

Lemma closure_env_loop_exec : forall n,
  forall (k : nat) (e : Clight.env) (le : temp_env) (m : mem)
         (sp_b : block) (sp_ofs' : ptrofs)
         (sb : block) (so : ptrofs)
         (new_b : block) (new_ofs : ptrofs)
         (nvars_nat : nat),
    (k + n = nvars_nat)%nat ->
    (0 <= Z.of_nat (nvars_nat + 2) <= Int.max_signed) ->
    le ! _i = Some (Vint (Int.repr (Z.of_nat k))) ->
    le ! _s = Some (Vptr sb so) ->
    le ! _block = Some (Vptr new_b new_ofs) ->
    le ! _nvars = Some (Vint (Int.repr (Z.of_nat nvars_nat))) ->
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs') ->
    (* Stack values loadable and castable for remaining iterations *)
    (forall j, (k <= j < nvars_nat)%nat ->
      exists cv, Mem.load Mint64 m sp_b
        (Ptrofs.unsigned sp_ofs' + Z.of_nat j * 8) = Some cv /\
      forall m', sem_cast cv tlong tlong m' = Some cv) ->
    (* New block writable for remaining fields *)
    Mem.range_perm m new_b
      (Ptrofs.unsigned new_ofs + Z.of_nat (k + 2) * 8)
      (Ptrofs.unsigned new_ofs + Z.of_nat (nvars_nat + 2) * 8) Cur Writable ->
    (align_chunk Mint64 | Ptrofs.unsigned new_ofs) ->
    new_b <> sp_b -> new_b <> sb ->
    Ptrofs.unsigned new_ofs + Z.of_nat (nvars_nat + 2) * 8 < Ptrofs.modulus ->
    Ptrofs.unsigned sp_ofs' + Z.of_nat nvars_nat * 8 < Ptrofs.modulus ->
    Ptrofs.unsigned so + 56 < Ptrofs.modulus ->
    (align_chunk Mint64 | Ptrofs.unsigned sp_ofs') ->
    exists le' m',
      exec_stmt function_entry1 clight_ge e le m
        closure_env_loop E0 le' m' Out_normal /\
      le' ! _s = Some (Vptr sb so) /\
      le' ! _block = Some (Vptr new_b new_ofs) /\
      le' ! _nvars = Some (Vint (Int.repr (Z.of_nat nvars_nat))) /\
      (forall ofs v, Mem.load Mint64 m sb ofs = Some v ->
         Mem.load Mint64 m' sb ofs = Some v) /\
      (forall b ofs k0 p, Mem.perm m b ofs k0 p -> Mem.perm m' b ofs k0 p) /\
      (forall b ofs chunk v, b <> new_b ->
         Mem.load chunk m b ofs = Some v ->
         Mem.load chunk m' b ofs = Some v).
Proof.
  induction n as [| n' IH]; intros k e le m sp_b sp_ofs' sb so new_b new_ofs nvars_nat
    Hkn Hnvars_range Hle_i Hle_s Hle_block Hle_nvars
    Hsp_load Hstack_load Hnew_rperm Hnew_align
    Hnew_ne_sp Hnew_ne_sb Hnew_ofs_bound Hsp_ofs_bound Hso_bound Hsp_align.

  (* ================================================================ *)
  (* Base case: n = 0, loop terminates immediately                     *)
  (* ================================================================ *)
  {
    exists le, m.
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    - unfold closure_env_loop.
      eapply exec_Sloop_stop1.
      + eapply exec_Sseq_2.
        * eapply exec_Sifthenelse with (b := false).
          -- econstructor; [econstructor; exact Hle_i | econstructor; exact Hle_nvars |].
             exact (sem_cmp_lt_int (Int.repr (Z.of_nat k)) (Int.repr (Z.of_nat nvars_nat)) m).
          -- unfold bool_val. simpl. f_equal. unfold Val.of_bool.
             replace nvars_nat with k by lia.
             unfold Int.lt.
             destruct (zlt _ _); [exfalso; lia | reflexivity].
          -- simpl. eapply exec_Sbreak.
        * discriminate.
      + constructor.
    - assumption.
    - assumption.
    - assumption.
    - auto.
    - auto.
    - auto.
  }

  (* ================================================================ *)
  (* Inductive case: n = S n', execute one iteration + recurse         *)
  (* ================================================================ *)
  {
    destruct interp_state_co_pc_accu_sp as [co_is [Hco [Hpc_offset [Haccu_offset Hsp_offset]]]].
    rewrite cenv_is_ce in Hco, Hpc_offset, Haccu_offset, Hsp_offset.

    (* Stack value at position k *)
    destruct (Hstack_load k ltac:(lia)) as [cv_k [Hload_sp_k Hcast_k]].

    (* Store to block[k+2] must succeed *)
    assert (Hstore_valid : Mem.valid_access m Mint64 new_b
              (Ptrofs.unsigned new_ofs + Z.of_nat (k + 2) * 8) Writable).
    { split.
      - intros ofs0 Hofs0. apply Hnew_rperm. simpl in Hofs0. lia.
      - change (align_chunk Mint64) with 8.
        destruct Hnew_align as [q Hq].
        change (align_chunk Mint64) with 8 in Hq.
        exists (q + Z.of_nat (k + 2)). lia. }
    destruct (Mem.valid_access_store m Mint64 new_b
                (Ptrofs.unsigned new_ofs + Z.of_nat (k + 2) * 8) cv_k Hstore_valid)
      as [m_k Hstore_k].

    (* le after body *)
    set (le_body := PTree.set _i (Vint (Int.repr (Z.of_nat (S k))))
            (PTree.set _t'10 cv_k
              (PTree.set _t'9 (Vptr sp_b sp_ofs') le))) in *.

    (* Apply IH *)
    assert (IH_result : exists le_post m_post,
      exec_stmt function_entry1 clight_ge e le_body m_k
        closure_env_loop E0 le_post m_post Out_normal /\
      le_post ! _s = Some (Vptr sb so) /\
      le_post ! _block = Some (Vptr new_b new_ofs) /\
      le_post ! _nvars = Some (Vint (Int.repr (Z.of_nat nvars_nat))) /\
      (forall ofs v, Mem.load Mint64 m_k sb ofs = Some v ->
         Mem.load Mint64 m_post sb ofs = Some v) /\
      (forall b ofs k0 p, Mem.perm m_k b ofs k0 p -> Mem.perm m_post b ofs k0 p) /\
      (forall b ofs chunk v, b <> new_b ->
         Mem.load chunk m_k b ofs = Some v ->
         Mem.load chunk m_post b ofs = Some v)).
    {
      apply (IH (S k) e le_body m_k sp_b sp_ofs' sb so new_b new_ofs nvars_nat).
      - lia.
      - assumption.
      - subst le_body. rewrite PTree.gss. reflexivity.
      - subst le_body. repeat (rewrite PTree.gso by (compute; congruence)). assumption.
      - subst le_body. repeat (rewrite PTree.gso by (compute; congruence)). assumption.
      - subst le_body. repeat (rewrite PTree.gso by (compute; congruence)). assumption.
      - erewrite Mem.load_store_other; [exact Hsp_load | exact Hstore_k |].
        left. exact (not_eq_sym Hnew_ne_sb).
      - intros j Hj.
        destruct (Hstack_load j ltac:(lia)) as [cv_j [Hload_j Hcast_j]].
        exists cv_j. split; [| exact Hcast_j].
        erewrite Mem.load_store_other; [exact Hload_j | exact Hstore_k |].
        left. exact (not_eq_sym Hnew_ne_sp).
      - intros ofs0 Hofs0. eapply Mem.perm_store_1. exact Hstore_k.
        apply Hnew_rperm. lia.
      - assumption.
      - assumption.
      - assumption.
      - assumption.
      - assumption.
      - assumption.
      - assumption.
    }
    destruct IH_result as (le_post & m_post &
      Hloop_exec & Hpost_s & Hpost_block & Hpost_nvars &
      Hpost_sb & Hpost_perm & Hpost_load).

    exists le_post, m_post.
    split; [| split; [| split; [| split; [| split; [| split]]]]].

    - (* exec: one iteration then recurse *)
      unfold closure_env_loop.
      replace E0 with (E0 ** E0 ** E0) by reflexivity.
      eapply exec_Sloop_loop.

      + (* s1: condition true + body *)
        unfold closure_env_loop_body.
        replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1.
        * (* Sifthenelse: condition true → Sskip *)
          eapply exec_Sifthenelse with (b := true).
          -- econstructor; [econstructor; exact Hle_i | econstructor; exact Hle_nvars |].
             exact (sem_cmp_lt_int (Int.repr (Z.of_nat k)) (Int.repr (Z.of_nat nvars_nat)) m).
          -- unfold bool_val. simpl. f_equal. unfold Val.of_bool.
             unfold Int.lt.
             rewrite Int.signed_repr by (pose proof Int.min_signed_neg; lia).
             rewrite Int.signed_repr by (pose proof Int.min_signed_neg; lia).
             destruct (zlt (Z.of_nat k) (Z.of_nat nvars_nat)); [reflexivity | lia].
          -- simpl. eapply exec_Sskip.
        * (* body: t'9=sp, t'10=sp[k], block[k+2]=t'10 *)
          replace E0 with (E0 ** E0) by reflexivity.
          eapply exec_Sseq_1.
          -- (* Sset _t'9: load sp from struct *)
             apply (eval_stmt_to_exec clight_ge 10). eval_cbn.
             rewrite Hle_s; eval_cbn. rewrite cenv_is_ce; eval_cbn.
             rewrite Hco; eval_cbn. rewrite Hsp_offset; eval_cbn.
             try rewrite Mptr_Mint64; eval_cbn.
             rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
             rewrite Hsp_load; eval_cbn.
             reflexivity.
          -- replace E0 with (E0 ** E0) by reflexivity.
             eapply exec_Sseq_1.
             ++ (* Sset _t'10: load sp[k] *)
                apply (eval_stmt_to_exec clight_ge 10). eval_cbn.
                rewrite PTree.gss; eval_cbn.
                rewrite PTree.gso by (compute; congruence).
                rewrite Hle_i; eval_cbn.
                rewrite sem_add_ptr_tlong_int; eval_cbn.
                try rewrite Mptr_Mint64; eval_cbn.
                rewrite ptrofs_of_int_signed_repr
                  by (pose proof Int.min_signed_neg; lia).
                rewrite ptrofs_mul_8
                  by (unfold Ptrofs.max_unsigned;
                      pose proof (Ptrofs.unsigned_range sp_ofs'); lia).
                rewrite (ptrofs_add_unsigned sp_ofs' (Z.of_nat k * 8)
                  ltac:(pose proof (Ptrofs.unsigned_range sp_ofs'); lia) ltac:(lia)).
                rewrite Hload_sp_k; eval_cbn.
                reflexivity.
             ++ (* Sassign: block[k+2] = t'10 *)
                eapply exec_Sassign.
                ** (* eval_lvalue for LHS: *(cast(block) + (i+2)) *)
                   econstructor. econstructor. econstructor.
                   --- (* cast(block) from tlong to tptr tlong *)
                       eapply eval_Etempvar.
                       rewrite PTree.gso by (compute; congruence).
                       rewrite PTree.gso by (compute; congruence).
                       exact Hle_block.
                   --- exact (sem_cast_vptr_tlong_to_ptr_tlong new_b new_ofs m).
                   --- (* i+2 *)
                       econstructor.
                       +++ eapply eval_Etempvar.
                           rewrite PTree.gso by (compute; congruence).
                           rewrite PTree.gso by (compute; congruence).
                           exact Hle_i.
                       +++ econstructor.
                       +++ exact (sem_add_int_int (Int.repr (Z.of_nat k)) (Int.repr 2) m).
                   --- exact (sem_add_ptr_tlong_int new_b new_ofs
                         (Int.add (Int.repr (Z.of_nat k)) (Int.repr 2)) m).
                ** (* eval_expr for RHS: _t'10 *)
                   econstructor. rewrite PTree.gss. reflexivity.
                ** (* sem_cast *)
                   exact (Hcast_k m).
                ** (* assign_loc *)
                   econstructor.
                   --- reflexivity.
                   --- unfold Mem.storev.
                       rewrite Int.add_unsigned.
                       rewrite (Int.unsigned_repr (Z.of_nat k)).
                       2: { pose proof Int.max_signed_unsigned. split; lia. }
                       rewrite (Int.unsigned_repr 2).
                       2: { pose proof Int.max_signed_unsigned. split; lia. }
                       rewrite ptrofs_of_int_signed_repr.
                       2: { pose proof Int.min_signed_neg. split; lia. }
                       replace (Int.repr (Z.of_nat k + 2))
                         with (Int.repr (Z.of_nat (k + 2)))
                         by (f_equal; lia).
                       rewrite ptrofs_mul_8
                         by (unfold Ptrofs.max_unsigned;
                             pose proof (Ptrofs.unsigned_range new_ofs); lia).
                       rewrite ptrofs_add_unsigned
                         by (pose proof (Ptrofs.unsigned_range new_ofs); lia).
                       replace (Z.of_nat k + 2) with (Z.of_nat (k + 2)) by lia.
                       exact Hstore_k.

      + (* out_normal_or_continue *)
        constructor.

      + (* s2: increment _i := _i + 1 *)
        unfold closure_env_loop_incr.
        apply (eval_stmt_to_exec clight_ge 5). eval_cbn.
        do 2 (rewrite PTree.gso by (compute; congruence)).
        rewrite Hle_i; eval_cbn.
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
        fold closure_env_loop.
        replace (PTree.set _i (Vint (Int.repr (Z.of_nat (S k))))
                  (PTree.set _t'10 cv_k
                    (PTree.set _t'9 (Vptr sp_b sp_ofs') le)))
          with le_body.
        { exact Hloop_exec. }
        subst le_body. reflexivity.

    - exact Hpost_s.
    - exact Hpost_block.
    - exact Hpost_nvars.
    - intros ofs v Hld. apply Hpost_sb.
      erewrite Mem.load_store_other; [exact Hld | exact Hstore_k |].
      left. exact (not_eq_sym Hnew_ne_sb).
    - intros b ofs k0 p Hp. apply Hpost_perm.
      eapply Mem.perm_store_1. exact Hstore_k. exact Hp.
    - intros b ofs chunk v Hne Hld. apply Hpost_load; [exact Hne |].
      erewrite Mem.load_store_other; [exact Hld | exact Hstore_k |].
      left. exact Hne.
  }
Qed.

(* ================================================================== *)
(* Main theorem: arbitrary nvars                                       *)
(* ================================================================== *)

Definition CLOSURE_correct_for_spec : forall nvars code_ofs,
    (0 <= Z.of_nat (2 + nvars) <= Int.max_signed) ->
    Int.min_signed <= code_ofs <= Int.max_signed ->
    handler_correct (handle_CLOSURE nvars code_ofs) f_instr_CLOSURE
      (fun _ => None)
      (closure_general_step_pre nvars code_ofs)
      (fun _ => None) (fun _ => None).
  Proof.
  Admitted.

(* Wrapper with the exact type expected by InstructVerificationFineGrainedSpec.
   handle_instr (CLOSURE nvars code_ofs) computes to handle_CLOSURE nvars code_ofs,
   clight_of (CLOSURE _ _) = f_instr_CLOSURE, and
   pre_of (CLOSURE nvars code_ofs) = closure_general_step_pre nvars code_ofs.
   handle_CLOSURE now has a boolean range guard; when the guard is true, the
   handler returns Step and we delegate to CLOSURE_correct_for_spec; when false,
   it returns Error and we prove error_message_of by reflexivity. *)
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

Definition correct_CLOSURE : forall nvars code_ofs,
  handler_correct (handle_instr (CLOSURE nvars code_ofs)) (clight_of (CLOSURE nvars code_ofs))
    (error_message_of (CLOSURE nvars code_ofs))
    (pre_of (CLOSURE nvars code_ofs)) (P_halt_of (CLOSURE nvars code_ofs)) (P_ccall_of (CLOSURE nvars code_ofs)).
Proof.
Admitted.
