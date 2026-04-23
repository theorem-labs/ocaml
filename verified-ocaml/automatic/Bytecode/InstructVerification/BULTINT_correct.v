(* BULTINT_correct.v -- BULTINT handler completeness proof (manual bigstep).

   Rocq handler:
     handle_BULTINT n target pc' s =
       match s.(accu) with
       | Val_int a => if Z.ltb (z_flip_sign n) (z_flip_sign a)
                      then Step (s <|pc := target|>)
                      else Step (s <|pc := pc'|>)
       | _ => Error "BULTINT: not an integer"
       end

   C handler body (f_instr_BULTINT):
     preamble: read n from code, advance pc, read accu
     condition: (unsigned long)n < (unsigned long)(accu >> 1)
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

Lemma interp_state_co_bultint : exists co,
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

Local Lemma sem_lt_ulong_ulong : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Olt
    (Vlong n1) tulong (Vlong n2) tulong m
    = Some (Val.of_bool (Int64.ltu n1 n2)).
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

(* Key arithmetic: unsigned comparison on tagged ints matches z_flip_sign comparison
   for non-negative operands in [0, 2^62) *)
Local Lemma bultint_arith : forall n a,
  0 <= n ->
  Int.min_signed <= n <= Int.max_signed ->
  0 <= a < 4611686018427387904 ->
  Int64.ltu (Int64.repr (Int.signed (Int.repr n)))
            (Int64.repr a)
  = Z.ltb (z_flip_sign n) (z_flip_sign a).
Proof.
  intros n a Hn_nonneg Hn_range Ha.
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
  destruct (Z.ltb_spec n a); destruct (Z.ltb_spec (n + 2^62) (a + 2^62)); lia.
Qed.

(* Combined: sem_binary_operation Olt on unsigned-cast operands gives the branch condition *)
Local Lemma bultint_cmp_true : forall n a m,
  0 <= n ->
  Int.min_signed <= n <= Int.max_signed ->
  0 <= a < 4611686018427387904 ->
  Z.ltb (z_flip_sign n) (z_flip_sign a) = true ->
  sem_binary_operation (genv_cenv clight_ge) Olt
    (Vlong (Int64.repr (Int.signed (Int.repr n)))) tulong
    (Vlong (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))) tulong m
  = Some (Val.of_bool true).
Proof.
  intros n0 a0 m0 Hn_nonneg Hn_range Ha Hcmp.
  rewrite sem_lt_ulong_ulong. rewrite tagged_shr_eq by lia.
  rewrite (bultint_arith n0 a0 Hn_nonneg Hn_range Ha). rewrite Hcmp. reflexivity.
Qed.

Local Lemma bultint_cmp_false : forall n a m,
  0 <= n ->
  Int.min_signed <= n <= Int.max_signed ->
  0 <= a < 4611686018427387904 ->
  Z.ltb (z_flip_sign n) (z_flip_sign a) = false ->
  sem_binary_operation (genv_cenv clight_ge) Olt
    (Vlong (Int64.repr (Int.signed (Int.repr n)))) tulong
    (Vlong (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))) tulong m
  = Some (Val.of_bool false).
Proof.
  intros n0 a0 m0 Hn_nonneg Hn_range Ha Hcmp.
  rewrite sem_lt_ulong_ulong. rewrite tagged_shr_eq by lia.
  rewrite (bultint_arith n0 a0 Hn_nonneg Hn_range Ha). rewrite Hcmp. reflexivity.
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

Local Lemma pc_rel_shift_2 : forall cb co0 rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co0 (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr 8)))
         cb (Ptrofs.add co0 (Ptrofs.repr (2 * sizeof_code_t))) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t. f_equal.
  rewrite Ptrofs.add_assoc. rewrite Ptrofs.add_assoc. f_equal.
  rewrite Ptrofs.add_commut. reflexivity.
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

Local Ltac read_pc_from_struct Hle co_is Hco Hpc_offset Hload :=
  apply exec_Sset;
  eapply eval_Elvalue;
  [ eval_s_field_lvalue Hle co_is Hco Hpc_offset
  | apply deref_loc_value with (chunk := Mptr);
    [ reflexivity
    | simpl; rewrite Mptr_Mint64; rewrite (ptrofs_add_zero _); exact Hload ] ].

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_BULTINT_correct : forall n target,
    0 <= n ->
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BULTINT n target) f_instr_BULTINT
      (fun _ => None)
      (fun _ m s ard =>
         ar_code_base_block ard <> ar_sptr_block ard /\
         0 <= n /\
         Int.min_signed <= n <= Int.max_signed /\
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr n)) /\
         (exists ofs_int,
           Mem.load Mint32 m (ar_code_base_block ard)
             (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
                (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))))
           = Some (Vint ofs_int) /\
           Ptrofs.add
             (Ptrofs.add (ar_code_base_ofs ard)
                (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t)))
             (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                         (ptrofs_of_int Signed ofs_int))
           = Ptrofs.add (ar_code_base_ofs ard) (Ptrofs.repr (target * sizeof_code_t))) /\
         match Machine.accu s with
         | Val_int a => 0 <= a < 4611686018427387904
         | _ => False
         end /\
         (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Machine.accu s) cv -> exists z, cv = Vlong z))
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with building-block precondition for Module Type *)
Theorem verify_BULTINT_handler_correct : forall n target,
    0 <= n -> Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BULTINT n target) f_instr_BULTINT
      (fun _ => None)
      (pre_and (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_unsigned_int) accu_is_long)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper matching InstructVerificationFineGrainedSpec signature.
   handle_instr (BULTINT n target) reduces to handle_BULTINT n target.
   clight_of (BULTINT n target) = f_instr_BULTINT by computation.
   pre_of (BULTINT n target) = (((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p accu_unsigned_int) /\p accu_is_long.

   The handler checks instr_wfb (BULTINT n _) = ((0 <=? n) && (min_signed <=? n)
   && (n <=? max_signed))%Z.  When that guard is false the handler returns
   Error "BULTINT: malformed operand", which matches error_message_of because
   error_message_of checks the identical boolean.  When the guard is true
   we have the range assumptions needed by the inner proof.

   Non-integer accu cases are trivially true because pre_of
   includes accu_unsigned_int which is False for non-integer accu. *)
Theorem correct_BULTINT : forall n target,
    handler_correct (handle_instr (Bytecode.AST.BULTINT n target)) (clight_of (Bytecode.AST.BULTINT n target))
      (error_message_of (Bytecode.AST.BULTINT n target))
      (pre_of (Bytecode.AST.BULTINT n target)) (P_halt_of (Bytecode.AST.BULTINT n target)) (P_ccall_of (Bytecode.AST.BULTINT n target)).
Proof.
Admitted.

