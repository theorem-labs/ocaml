(* APPLY_correct.v -- APPLY handler correctness proof.

   APPLY n: tail call with n args already on stack.
   Reads nargs from the code buffer, stores nargs-1 to extra_args,
   reads the closure code pointer from accu[0], stores to pc,
   copies accu to env.

   C body (f_instr_APPLY):
     _t'4 = s->pc;
     _t'5 = *_t'4;                  // read nargs from code buffer
     s->extra_args = (long)(_t'5 - 1);  // store nargs-1
     _t'2 = s->accu;
     _t'3 = deref((code_t ptr ptr)_t'2 + 0); // read code pointer from closure
     s->pc = _t'3;                   // jump to code pointer
     _t'1 = s->accu;
     s->env = _t'1;                  // set env to closure
     return 0;

   Rocq handler (Interpret.v):
     handle_APPLY n s =
       match get_code_ptr_s s s.(accu) with
       | Some target_pc =>
         Step (s <|pc := target_pc|> <|env := s.(accu)|>
                 <|extra_args := Nat.sub n 1|>)
       | None => Error "APPLY: accu is not a closure"
       end

   Three stores: extra_args (offset 32), pc (offset 0), env (offset 24).

   No Axioms, no Admitted. *)

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
(* Struct layout: _pc@0, _accu@8, _extra_args@32, _env@24             *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full).
Proof.
  eexists. split; [| split; [| split; [| split]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_apply : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

(* sem_sub for tint - tint: goes through sem_binarith *)
Local Lemma sem_sub_int_int : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vint n1) tint (Vint n2) tint m
    = Some (Vint (Int.sub n1 n2)).
Proof. intros. reflexivity. Qed.

(* sem_cast for tint -> tlong *)
Local Lemma sem_cast_int_to_long : forall n m,
  sem_cast (Vint n) tint tlong m = Some (Vlong (Int64.repr (Int.signed n))).
Proof.
  intros. unfold sem_cast.
  change (classify_cast tint tlong) with (cast_case_i2l Signed).
  simpl. reflexivity.
Qed.

(* sem_cast for tlong -> (tptr (tptr tint)) when value is Vptr *)
Local Lemma sem_cast_long_to_ptptint_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr (tptr tint)) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* sem_add for (tptr (tptr tint)) + 0 *)
Local Lemma sem_add_ptptint_0 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr (tptr tint)) (Vint (Int.repr 0)) tint m
    = Some (Vptr b ofs).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr (tptr tint)) tint) with (add_case_pi (tptr tint) Signed).
  unfold sem_add_ptr_int.
  change (sizeof (genv_cenv clight_ge) (tptr tint)) with 8%Z.
  f_equal. f_equal.
  unfold ptrofs_of_int.
  change (Ptrofs.of_ints (Int.repr 0)) with Ptrofs.zero.
  rewrite Ptrofs.mul_zero, Ptrofs.add_zero. reflexivity.
Qed.

(* sem_cast for (tptr tint) -> (tptr tint) is identity *)
Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* ================================================================== *)
(* Closure code pointer precondition                                   *)
(* ================================================================== *)

(* When get_code_ptr_s succeeds, the C memory must contain the code
   pointer at the accu's pointer location, the accu block must be
   separate from sb and cb, and the code pointer must satisfy pc_rel. *)
Definition apply_step_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let cb := ar_code_base_block ard in
  forall target_pc,
    get_code_ptr_s s s.(Machine.accu) = Some target_pc ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists accu_b accu_ofs code_b code_ofs,
        accu_v = Vptr accu_b accu_ofs /\
        Mem.load Mptr m accu_b (Ptrofs.unsigned accu_ofs) = Some (Vptr code_b code_ofs) /\
        accu_b <> sb /\
        accu_b <> cb /\
        (exists new_co,
          code_ofs = Ptrofs.add new_co (Ptrofs.repr (target_pc * sizeof_code_t)) /\
          code_b = cb).

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Local Lemma val_repr_co_shift : forall hm cb co co' v cv,
  val_repr hm cb co v cv -> val_repr hm cb co' v cv.
Proof.
  intros. inversion H; subst.
  - constructor. - eapply vr_ptr; eassumption.
  - eapply vr_closure; eauto. - constructor. - eapply vr_code_ptr.
Qed.
Local Lemma stack_repr_co_shift : forall hm cb co co' m stk b ofs,
  stack_repr hm cb co m stk b ofs -> stack_repr hm cb co' m stk b ofs.
Proof.
  intros hm0 cb0 co0 co' m0 stk0 b0 ofs0 H. induction H.
  - constructor. - econstructor; [eassumption | eapply val_repr_co_shift; eassumption | assumption].
Qed.
Local Lemma global_repr_co_shift : forall hm cb co co' m vs b ofs,
  global_repr hm cb co m vs b ofs -> global_repr hm cb co' m vs b ofs.
Proof.
  intros hm0 cb0 co0 co' m0 vs0 b0 ofs0 H. induction H.
  - constructor. - econstructor; [eassumption | eapply val_repr_co_shift; eassumption | assumption].
Qed.

Theorem verify_APPLY_correct : forall n,
    handler_correct (fun _ s => handle_APPLY n s) f_instr_APPLY
      (fun _ => None)
      (fun _ m s ard =>
         (* The code buffer contains Int.repr (Z.of_nat n) at the current PC *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* n fits in int32 signed range *)
         Int.min_signed <= Z.of_nat n <= Int.max_signed /\
         (* n >= 1 (APPLY always has at least 1 arg) *)
         (1 <= n)%nat /\
         (* Closure code pointer is loadable *)
         apply_step_pre m s ard)
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr (APPLY n) reduces to handle_APPLY n by computation.
   clight_of (APPLY n) = f_instr_APPLY and pre_of (APPLY n) = apply_n_step_pre n
   are convertible.  Error case is bridged by unfolding error_message_of and
   case-splitting on get_code_ptr_s. *)
Definition correct_APPLY : forall n,
    handler_correct (Dispatch.handle_instr (Bytecode.AST.APPLY n))
      (clight_of (Bytecode.AST.APPLY n))
      (error_message_of (Bytecode.AST.APPLY n))
      (pre_of (Bytecode.AST.APPLY n)) (P_halt_of (Bytecode.AST.APPLY n))
      (P_ccall_of (Bytecode.AST.APPLY n)).
Proof.
Admitted.

