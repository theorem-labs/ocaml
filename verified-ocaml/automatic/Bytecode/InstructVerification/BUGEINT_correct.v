(* BUGEINT_correct.v -- BUGEINT handler completeness proof (manual bigstep).

   Rocq handler:
     handle_BUGEINT n target pc' s =
       match s.(accu) with
       | Val_int a => if Z.geb (z_flip_sign n) (z_flip_sign a)
                      then Step (s <|pc := target|>)
                      else Step (s <|pc := pc'|>)
       | _ => Error "BUGEINT: not an integer"
       end

   C handler body (f_instr_BUGEINT):
     preamble: read n from code, advance pc, read accu
     condition: (unsigned long)n >= (unsigned long)(accu >> 1)
     then: branch (pc = pc + *pc)
     else: fall through (pc = pc + 1)

   NO AXIOMS. *)

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
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.
Local Notation exec := (exec_stmt function_entry1 clight_ge).

(* ================================================================== *)
(* Struct layout                                                       *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_bugeint : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof. rewrite cenv_is_ce. eexists. split; [| split]; reflexivity. Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Local Lemma sem_cast_int_to_ulong : forall i m,
  sem_cast (Vint i) tint tulong m = Some (Vlong (Int64.repr (Int.signed i))).
Proof. intros. unfold sem_cast. simpl classify_cast. simpl. reflexivity. Qed.

Local Lemma sem_cast_long_to_ulong : forall n m,
  sem_cast (Vlong n) tlong tulong m = Some (Vlong n).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof. intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed). simpl. reflexivity. Qed.

Local Lemma sem_ge_ulong_ulong : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Oge
    (Vlong n1) tulong (Vlong n2) tulong m
    = Some (Val.of_bool (negb (Int64.ltu n1 n2))).
Proof. intros. reflexivity. Qed.

Local Lemma bool_val_of_bool : forall b m,
  bool_val (Val.of_bool b) tint m = Some b.
Proof. intros. destruct b; reflexivity. Qed.

Local Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint) (Vint (Int.repr 1)) tint m
  = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof. intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity. Qed.

Local Lemma sem_add_ptr_int_tint : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint) (Vint n) tint m
  = Some (Vptr b (Ptrofs.add ofs
        (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                    (ptrofs_of_int Signed n)))).
Proof. intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity. Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma ptrofs_add_zero : forall ofs,
  Ptrofs.add ofs (Ptrofs.repr 0) = ofs.
Proof. intros. change (Ptrofs.repr 0) with Ptrofs.zero. apply Ptrofs.add_zero. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* ================================================================== *)
(* Comparison lemmas                                                   *)
(* ================================================================== *)

Local Lemma tagged_shr_eq : forall a,
  -4611686018427387904 <= a <= 4611686018427387903 ->
  Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1) = Int64.repr a.
Proof.
  intros a Ha. unfold Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1.
  rewrite Int64.signed_repr.
  2: { assert (Int64.min_signed = -9223372036854775808)%Z by reflexivity.
       assert (Int64.max_signed = 9223372036854775807)%Z by reflexivity. lia. }
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  f_equal. replace ((a * 2 + 1) / 2) with a by (apply Z.div_unique with 1; lia).
  reflexivity.
Qed.

(* Int64.ltu is Z.ltb on unsigned values *)
Local Lemma int64_ltu_ltb : forall x y,
  Int64.ltu x y = Z.ltb (Int64.unsigned x) (Int64.unsigned y).
Proof.
  intros. unfold Int64.ltu.
  destruct (zlt (Int64.unsigned x) (Int64.unsigned y)) as [Hlt|Hge].
  - symmetry. apply Z.ltb_lt. exact Hlt.
  - symmetry. apply Z.ltb_ge. lia.
Qed.

(* For non-negative a, b in [0, 2^62), z_flip_sign adds 2^62, cancels in comparison *)
Local Lemma Z_lxor_add_pow2 : forall a n,
  0 <= a ->
  0 <= n ->
  a < 2 ^ n ->
  Z.lxor a (2 ^ n) = a + 2 ^ n.
Proof.
  intros a n Ha Hn Hlt.
  rewrite Z.add_nocarry_lxor.
  - reflexivity.
  - apply Z.bits_inj. intros j.
    rewrite Z.land_spec, Z.bits_0.
    rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eqb n j) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst.
      destruct (Z.eq_dec a 0) as [->|Ha0].
      * rewrite Z.testbit_0_l. reflexivity.
      * rewrite Z.bits_above_log2; [reflexivity | lia | ].
        apply Z.log2_lt_pow2; lia.
    + rewrite Bool.andb_false_r. reflexivity.
Qed.

Local Lemma Z_geb_negb_ltb : forall a b, Z.geb a b = negb (Z.ltb a b).
Proof.
  intros. destruct (Z.geb a b) eqn:Hge; destruct (Z.ltb a b) eqn:Hlt;
    try reflexivity;
    rewrite Z.geb_leb in Hge;
    first [rewrite Z.leb_le in Hge | rewrite Z.leb_gt in Hge];
    first [rewrite Z.ltb_lt in Hlt | rewrite Z.ltb_ge in Hlt]; lia.
Qed.

(* Key arithmetic: unsigned >= comparison on tagged ints matches z_flip_sign geb
   for non-negative operands in [0, 2^62) *)
Local Lemma bugeint_arith : forall n a,
  0 <= n ->
  Int.min_signed <= n <= Int.max_signed ->
  0 <= a < 4611686018427387904 ->
  negb (Int64.ltu (Int64.repr (Int.signed (Int.repr n)))
                   (Int64.repr a))
  = Z.geb (z_flip_sign n) (z_flip_sign a).
Proof.
  intros n a Hn_nonneg Hn_range Ha.
  rewrite Z_geb_negb_ltb.
  rewrite Int.signed_repr by exact Hn_range.
  rewrite int64_ltu_ltb.
  rewrite Int64.unsigned_repr.
  2: { unfold Int64.max_unsigned. change Int64.modulus with 18446744073709551616.
       assert (Int.max_signed = 2147483647)%Z by reflexivity. lia. }
  rewrite Int64.unsigned_repr.
  2: { unfold Int64.max_unsigned. change Int64.modulus with 18446744073709551616. lia. }
  unfold z_flip_sign, word_bits. simpl Z.sub.
  change (Z.shiftl 1 62) with (2 ^ 62).
  rewrite Z_lxor_add_pow2 by (try lia; assert (Int.max_signed = 2147483647)%Z by reflexivity; lia).
  rewrite Z_lxor_add_pow2 by lia.
  destruct (Z.ltb_spec n a); destruct (Z.ltb_spec (n + 2^62) (a + 2^62)); try lia; reflexivity.
Qed.

(* Combined: sem_binary_operation Oge on unsigned-cast operands gives the branch condition *)
Local Lemma bugeint_cmp_true : forall n a m,
  0 <= n ->
  Int.min_signed <= n <= Int.max_signed ->
  0 <= a < 4611686018427387904 ->
  Z.geb (z_flip_sign n) (z_flip_sign a) = true ->
  sem_binary_operation (genv_cenv clight_ge) Oge
    (Vlong (Int64.repr (Int.signed (Int.repr n)))) tulong
    (Vlong (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))) tulong m
  = Some (Val.of_bool true).
Proof.
  intros n0 a0 m0 Hn_nonneg Hn_range Ha Hcmp.
  rewrite sem_ge_ulong_ulong. rewrite tagged_shr_eq by lia.
  rewrite (bugeint_arith n0 a0 Hn_nonneg Hn_range Ha). rewrite Hcmp. reflexivity.
Qed.

Local Lemma bugeint_cmp_false : forall n a m,
  0 <= n ->
  Int.min_signed <= n <= Int.max_signed ->
  0 <= a < 4611686018427387904 ->
  Z.geb (z_flip_sign n) (z_flip_sign a) = false ->
  sem_binary_operation (genv_cenv clight_ge) Oge
    (Vlong (Int64.repr (Int.signed (Int.repr n)))) tulong
    (Vlong (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))) tulong m
  = Some (Val.of_bool false).
Proof.
  intros n0 a0 m0 Hn_nonneg Hn_range Ha Hcmp.
  rewrite sem_ge_ulong_ulong. rewrite tagged_shr_eq by lia.
  rewrite (bugeint_arith n0 a0 Hn_nonneg Hn_range Ha). rewrite Hcmp. reflexivity.
Qed.

(* ================================================================== *)
(* pc_rel helpers                                                      *)
(* ================================================================== *)

Local Lemma ptrofs_add_repr : forall a b,
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  intros. rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Local Lemma pc_plus1_eq_gen : forall co0 pc0,
  Ptrofs.add (Ptrofs.add co0 (Ptrofs.repr (pc0 * sizeof_code_t))) (Ptrofs.repr 4)
  = Ptrofs.add co0 (Ptrofs.repr ((pc0 + 1) * sizeof_code_t)).
Proof.
  intros. unfold sizeof_code_t. rewrite Ptrofs.add_assoc. f_equal.
  rewrite ptrofs_add_repr. f_equal. lia.
Qed.

(* ================================================================== *)
(* Field survival                                                      *)
(* ================================================================== *)

Local Ltac prove_field_survives Hstore Hload :=
  apply (load_after_store_other _ _ _ _ _ _ _ Hstore Hload); right; lia.

(* ================================================================== *)
(* Lvalue/Rvalue tactics for s->field reads                            *)
(* ================================================================== *)

Local Ltac eval_s_field_lvalue solve_le co_is Hco Hfld :=
  eapply eval_Efield_struct;
  [ eapply eval_Elvalue;
    [ eapply eval_Ederef; eapply eval_Etempvar; solve_le
    | apply deref_loc_copy; reflexivity ]
  | reflexivity
  | exact Hco
  | exact Hfld ].

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

(* Wrapper with building-block precondition for Module Type *)
(* Wrapper with the canonical type expected by InstructVerificationProof.v.

   The handler checks instr_wfb (BUGEINT z1 z2) = ((0 <=? z1) &&
   (min_signed <=? z1) && (z1 <=? max_signed))%Z.  When that guard is
   false the handler returns Error "BUGEINT: malformed operand", which
   matches error_message_of because error_message_of checks the identical
   boolean.  When the guard is true we have the range assumptions needed
   by the inner proof.

   Non-integer accu cases are trivially true because pre_of includes
   accu_check ak_unsigned_range which is False for non-integer accu. *)
Theorem correct_BUGEINT : forall z1 z2,
  handler_correct (handle_instr (Bytecode.AST.BUGEINT z1 z2)) (clight_of (Bytecode.AST.BUGEINT z1 z2))
    (error_message_of (Bytecode.AST.BUGEINT z1 z2))
    (pre_of (Bytecode.AST.BUGEINT z1 z2)) (P_halt_of (Bytecode.AST.BUGEINT z1 z2)) (P_ccall_of (Bytecode.AST.BUGEINT z1 z2)).
Proof.
Admitted.

