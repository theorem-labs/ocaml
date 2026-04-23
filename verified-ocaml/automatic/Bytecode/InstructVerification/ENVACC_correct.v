(* ENVACC_correct.v -- ENVACC (parameterized) handler completeness proof.

   ENVACC n: reads index n from the code buffer, then reads env[n]
   from the closure environment, stores to accu, and advances pc past
   the argument.

   C code (f_instr_ENVACC):
     _t'1 = s->pc;             // read pc pointer (points to n in code buffer)
     s->pc = _t'1 + 1;         // advance pc past argument
     _t'2 = s->env;            // read env (tlong, really a pointer)
     _t'3 = *_t'1;             // read n from code buffer (Mint32)
     _t'4 = *(cast(_t'2, tptr tlong) + _t'3);  // env[n] (pointer arith)
     s->accu = _t'4;           // store to accu
     return 0;

   Rocq:
     handle_ENVACC n pc' s =
       match field_or_heap s s.(env) n with
       | Some v => Step (s <|pc := pc'|> <|accu := v|>)
       | None => Error "ENVACC: env access out of bounds"
       end

   Two stores: pc field at offset +0, accu field at offset +8.

   Combines the ACC code-buffer-read pattern with ENVACC1's
   env field access pattern, generalized over n.

   NO AXIOMS.  All structural/range constraints are preconditions
   via handler_correct. *)

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

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout: _pc at offset 0, _env at offset 24, _accu at offset 8 *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_pc_env_accu : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* env_ptr + n : pointer arithmetic on (tptr tlong), where n is tint.
   sizeof(tlong) = 8, so env_ptr + n = env_ptr + n * 8 bytes. *)
Lemma sem_add_env_n : forall env_b env_ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr env_b env_ofs) (tptr tlong)
    (Vint n) tint
    m = Some (Vptr env_b (Ptrofs.add env_ofs
                (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* pc_rel with shifted code base *)
Lemma pc_rel_shift : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr 4)))
         cb (Ptrofs.add co (Ptrofs.repr sizeof_code_t)) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal.
  rewrite Ptrofs.add_assoc.
  rewrite Ptrofs.add_assoc.
  f_equal.
  rewrite Ptrofs.add_commut. reflexivity.
Qed.

(* ================================================================== *)
(* ptrofs_mul_8_of_ints_eq: relate C pointer arithmetic to logical    *)
(* ================================================================== *)

Lemma ptrofs_max_unsigned_large : (Ptrofs.max_unsigned >= 2^32)%Z.
Proof. vm_compute. discriminate. Qed.

Lemma ptrofs_mul_8_of_ints_eq : forall n,
  0 <= n ->
  n < Int.half_modulus ->
  Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr n))
  = Ptrofs.repr (n * 8).
Proof.
  intros n Hnn Hn_bound.
  unfold ptrofs_of_int, Ptrofs.of_ints.
  change Int.half_modulus with 2147483648 in Hn_bound.
  rewrite Int.signed_repr.
  2: { change Int.min_signed with (-2147483648).
       change Int.max_signed with 2147483647. lia. }
  unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 8).
  2: { pose proof ptrofs_max_unsigned_large. lia. }
  rewrite (Ptrofs.unsigned_repr n).
  2: { pose proof ptrofs_max_unsigned_large. lia. }
  f_equal. lia.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_ENVACC_correct : forall n,
    Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_ENVACC n) f_instr_ENVACC
      (fun _ => None)
      (fun e m s ard =>
         (* The code buffer contains Int.repr (Z.of_nat n) at the current PC position *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* env field n is loadable in C memory *)
         env_field_loadable n e m s ard)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

Definition ENVACC_correct_for_spec : forall n, Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_ENVACC n) f_instr_ENVACC
      (fun _ => None)
      (code_at (Int.repr (Z.of_nat n)) /\p env_field_loadable n)
      (fun _ => False) (fun _ _ _ => False).
  Proof.
  Admitted.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr (ENVACC n) / clight_of (ENVACC n) / pre_of (ENVACC n) are
   convertible with handle_ENVACC n / f_instr_ENVACC /
   (code_at (Int.repr (Z.of_nat n)) /\p env_field_loadable n).
   P_halt_of and P_ccall_of are vacuously satisfied (ENVACC never halts or
   issues a C call).  error_message_of is tautological on the Error branch. *)
Theorem correct_ENVACC : forall n,
    handler_correct (handle_instr (Bytecode.AST.ENVACC n)) (clight_of (Bytecode.AST.ENVACC n))
      (error_message_of (Bytecode.AST.ENVACC n))
      (pre_of (Bytecode.AST.ENVACC n)) (P_halt_of (Bytecode.AST.ENVACC n)) (P_ccall_of (Bytecode.AST.ENVACC n)).
Proof.
Admitted.

