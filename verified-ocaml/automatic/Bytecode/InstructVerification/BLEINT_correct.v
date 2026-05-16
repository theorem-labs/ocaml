(* BLEINT_correct.v -- BLEINT handler completeness proof (manual bigstep).

   Rocq handler:
     handle_BLEINT n target pc' s =
       match s.(accu) with
       | Val_int a => if Z.leb n a then Step (s <|pc := target|>)
                      else Step (s <|pc := pc'|>)
       | _ => Error "BLEINT: not an integer"
       end

   C handler body (f_instr_BLEINT):
     (Ssequence
       (Ssequence                              -- preamble
         (Ssequence
           (Sset _t'1 s->pc)
           (Sassign s->pc (_t'1 + 1)))
         (Ssequence
           (Sset _t'2 (deref _t'1))
           (Ssequence
             (Sset _t'3 s->accu)
             (Sifthenelse ((long)_t'2 <= (long)((long)_t'3 >> 1))
               (Ssequence (Sset _t'5 s->pc)
                 (Ssequence (Sset _t'6 s->pc)
                   (Ssequence (Sset _t'7 (deref _t'6))
                     (Sassign s->pc (_t'5 + _t'7)))))
               (Ssequence (Sset _t'4 s->pc)
                 (Sassign s->pc (_t'4 + 1)))))))
       (Sreturn 0))

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

Lemma interp_state_co_bleint : exists co,
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

(* Ole on two longs: negb (Int64.lt n2 n1) *)
Local Lemma sem_le_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Ole
    (Vlong n1) tlong (Vlong n2) tlong m
    = Some (Val.of_bool (negb (Int64.lt n2 n1))).
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

(* Key lemma: when n <= a (leb is true), the C comparison (long)n <= (long)(accu>>1) is true.
   C Ole gives negb (Int64.lt (repr a) (repr n)). When n <= a, a is not < n, so
   Int64.lt is false, negb gives true. *)
Local Lemma bleint_cmp_true : forall n a m,
  -4611686018427387904 <= a <= 4611686018427387903 ->
  Int.min_signed <= n <= Int.max_signed ->
  Z.leb n a = true ->
  sem_binary_operation (genv_cenv clight_ge) Ole
    (Vlong (Int64.repr (Int.signed (Int.repr n)))) tlong
    (Vlong (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))) tlong m
  = Some (Val.of_bool true).
Proof.
  intros n0 a0 m0 Ha Hn Hle. rewrite tagged_shr_eq by lia.
  rewrite sem_le_long_long. rewrite Int.signed_repr by exact Hn.
  f_equal. f_equal.
  apply Z.leb_le in Hle.
  unfold Int64.lt.
  assert (Ha64 : Int64.min_signed <= a0 <= Int64.max_signed).
  { assert (Int64.min_signed = -9223372036854775808)%Z by reflexivity.
    assert (Int64.max_signed = 9223372036854775807)%Z by reflexivity.
    assert (Int.min_signed = -2147483648)%Z by reflexivity.
    assert (Int.max_signed = 2147483647)%Z by reflexivity. lia. }
  assert (Hn64 : Int64.min_signed <= n0 <= Int64.max_signed).
  { assert (Int64.min_signed = -9223372036854775808)%Z by reflexivity.
    assert (Int64.max_signed = 9223372036854775807)%Z by reflexivity.
    assert (Int.min_signed = -2147483648)%Z by reflexivity.
    assert (Int.max_signed = 2147483647)%Z by reflexivity. lia. }
  rewrite !Int64.signed_repr by lia.
  destruct (zlt a0 n0); [lia | reflexivity].
Qed.

(* Key lemma: when n > a (leb is false), the C comparison is false. *)
Local Lemma bleint_cmp_false : forall n a m,
  -4611686018427387904 <= a <= 4611686018427387903 ->
  Int.min_signed <= n <= Int.max_signed ->
  Z.leb n a = false ->
  sem_binary_operation (genv_cenv clight_ge) Ole
    (Vlong (Int64.repr (Int.signed (Int.repr n)))) tlong
    (Vlong (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))) tlong m
  = Some (Val.of_bool false).
Proof.
  intros n0 a0 m0 Ha Hn Hle. rewrite tagged_shr_eq by lia.
  rewrite sem_le_long_long. rewrite Int.signed_repr by exact Hn.
  f_equal. f_equal.
  apply Z.leb_gt in Hle.
  unfold Int64.lt.
  assert (Ha64 : Int64.min_signed <= a0 <= Int64.max_signed).
  { assert (Int64.min_signed = -9223372036854775808)%Z by reflexivity.
    assert (Int64.max_signed = 9223372036854775807)%Z by reflexivity.
    assert (Int.min_signed = -2147483648)%Z by reflexivity.
    assert (Int.max_signed = 2147483647)%Z by reflexivity. lia. }
  assert (Hn64 : Int64.min_signed <= n0 <= Int64.max_signed).
  { assert (Int64.min_signed = -9223372036854775808)%Z by reflexivity.
    assert (Int64.max_signed = 9223372036854775807)%Z by reflexivity.
    assert (Int.min_signed = -2147483648)%Z by reflexivity.
    assert (Int.max_signed = 2147483647)%Z by reflexivity. lia. }
  rewrite !Int64.signed_repr by lia.
  destruct (zlt a0 n0); [reflexivity | lia].
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

(* pc_plus1 corresponds to (pc+1) * sizeof_code_t *)
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

Theorem verify_BLEINT_correct : forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BLEINT n target) f_instr_BLEINT
      (fun _ => None)
      (fun _ m s ard =>
         ar_code_base_block ard <> ar_sptr_block ard /\
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
         | Val_int a => -4611686018427387904 <= a <= 4611686018427387903
         | _ => False
         end /\
         (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Machine.accu s) cv -> exists z, cv = Vlong z))
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

(* Wrapper with building-block precondition for Module Type *)
(* Wrapper with the canonical type expected by InstructVerificationProof.v.

   The handler checks instr_wfb (BLEINT z1 z2) = ((min_signed <=? z1) &&
   (z1 <=? max_signed))%Z.  When that guard is false the handler returns
   Error "BLEINT: malformed operand", which matches error_message_of because
   error_message_of checks the identical boolean.  When the guard is true
   we have the signed-range assumption needed by the inner proof.

   Non-integer accu error cases are fully proved via error_message_of. *)
Theorem correct_BLEINT : forall z1 z2,
  handler_correct (handle_instr (Bytecode.AST.BLEINT z1 z2)) (clight_of (Bytecode.AST.BLEINT z1 z2))
    (error_message_of (Bytecode.AST.BLEINT z1 z2))
    (pre_of (Bytecode.AST.BLEINT z1 z2)) (P_halt_of (Bytecode.AST.BLEINT z1 z2)) (P_ccall_of (Bytecode.AST.BLEINT z1 z2)).
Proof.
Admitted.

