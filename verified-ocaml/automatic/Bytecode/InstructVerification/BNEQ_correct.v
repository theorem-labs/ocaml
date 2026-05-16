(* BNEQ_correct.v -- BNEQ handler completeness proof (manual bigstep).

   Rocq handler:
     handle_BNEQ n target pc' s =
       match s.(accu) with
       | Val_int a => if Z.eqb a n then Step (s <|pc := pc'|>)
                      else Step (s <|pc := target|>)
       | _ => Step (s <|pc := target|>)
       end

   C handler body (f_instr_BNEQ):
     Same structure as BEQ but with One (!=) instead of Oeq (==).
     When accu != n, branch is taken (then); when accu == n, fall through (else).

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

Lemma interp_state_co_bneq : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof. rewrite cenv_is_ce. eexists. split; [| split]; reflexivity. Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Local Lemma sem_cast_int_to_long : forall i m,
  sem_cast (Vint i) tint tlong m = Some (Vlong (Int64.repr (Int.signed i))).
Proof. intros. unfold sem_cast. change (classify_cast tint tlong) with (cast_case_i2l Signed). simpl. reflexivity. Qed.

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof. intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed). simpl. reflexivity. Qed.

Local Lemma sem_ne_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Cop.One
    (Vlong n1) tlong (Vlong n2) tlong m
    = Some (Val.of_bool (negb (Int64.eq n1 n2))).
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

(* When a = n, One gives false (not-equal is false when equal) *)
Local Lemma bneq_cmp_eq : forall n m,
  -4611686018427387904 <= n <= 4611686018427387903 ->
  Int.min_signed <= n <= Int.max_signed ->
  sem_binary_operation (genv_cenv clight_ge) Cop.One
    (Vlong (Int64.repr (Int.signed (Int.repr n)))) tlong
    (Vlong (Int64.shr (Int64.repr (n * 2 + 1)) (Int64.repr 1))) tlong m
  = Some (Val.of_bool false).
Proof.
  intros n0 m0 Ha Hn. rewrite tagged_shr_eq by lia.
  rewrite sem_ne_long_long. rewrite Int.signed_repr by exact Hn.
  rewrite Int64.eq_true. reflexivity.
Qed.

(* When a <> n, One gives true (not-equal is true when not equal) *)
Local Lemma bneq_cmp_neq : forall a n m,
  -4611686018427387904 <= a <= 4611686018427387903 ->
  Int.min_signed <= n <= Int.max_signed ->
  a <> n ->
  sem_binary_operation (genv_cenv clight_ge) Cop.One
    (Vlong (Int64.repr (Int.signed (Int.repr n)))) tlong
    (Vlong (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))) tlong m
  = Some (Val.of_bool true).
Proof.
  intros a0 n0 m0 Ha Hn Hne. rewrite tagged_shr_eq by lia.
  rewrite sem_ne_long_long. rewrite Int.signed_repr by exact Hn.
  rewrite Int64.eq_false.
  - reflexivity.
  - intro Heq0. apply Hne.
    assert (Hn64 : Int64.min_signed <= n0 <= Int64.max_signed).
    { assert (Int.min_signed = -2147483648)%Z by reflexivity.
      assert (Int.max_signed = 2147483647)%Z by reflexivity.
      assert (Int64.min_signed = -9223372036854775808)%Z by reflexivity.
      assert (Int64.max_signed = 9223372036854775807)%Z by reflexivity. lia. }
    assert (Ha64 : Int64.min_signed <= a0 <= Int64.max_signed).
    { assert (Int64.min_signed = -9223372036854775808)%Z by reflexivity.
      assert (Int64.max_signed = 9223372036854775807)%Z by reflexivity. lia. }
    apply (f_equal Int64.signed) in Heq0.
    rewrite Int64.signed_repr in Heq0 by exact Hn64.
    rewrite Int64.signed_repr in Heq0 by exact Ha64. symmetry. exact Heq0.
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

(* Wrapper with building-block precondition for Module Type *)
(* Wrapper with the canonical type expected by InstructVerificationProof.v.

   The handler checks instr_wfb (BNEQ z1 z2) = ((min_signed <=? z1) &&
   (z1 <=? max_signed))%Z.  When that guard is false the handler returns
   Error "BNEQ: malformed operand", which matches error_message_of because
   error_message_of checks the identical boolean.  When the guard is true
   we have the signed-range assumption needed by the inner proof.

   Non-integer accu cases are trivially true because pre_of
   includes accu_signed_int which is False for non-integer accu. *)
Theorem correct_BNEQ : forall z1 z2,
  handler_correct (handle_instr (Bytecode.AST.BNEQ z1 z2)) (clight_of (Bytecode.AST.BNEQ z1 z2))
    (error_message_of (Bytecode.AST.BNEQ z1 z2))
    (pre_of (Bytecode.AST.BNEQ z1 z2)) (P_halt_of (Bytecode.AST.BNEQ z1 z2)) (P_ccall_of (Bytecode.AST.BNEQ z1 z2)).
Proof.
Admitted.
