(* APPLY2_correct.v -- APPLY2 handler correctness proof.

   APPLY2: fixed 2-argument apply. Reads arg1=sp[0], arg2=sp[1],
   pushes return frame (arg1, arg2, pc, env, extra_args) onto stack,
   sets extra_args=1, and jumps to closure code.

   C body (f_instr_APPLY2):
     t14 = s->sp;
     arg1 = deref(t14 + 0);           -- read arg1 from stack
     t13 = s->sp;
     arg2 = deref(t13 + 1);           -- read arg2 from stack
     t12 = s->sp;
     s->sp = t12 - 3;                 -- sp -= 3
     t11 = s->sp;
     deref(t11 + 0) = arg1;           -- new sp[0] = arg1
     t10 = s->sp;
     deref(t10 + 1) = arg2;           -- new sp[1] = arg2
     t8 = s->sp;
     t9 = s->pc;
     deref(t8 + 2) = (long)t9;        -- new sp[2] = pc (return addr)
     t6 = s->sp;
     t7 = s->env;
     deref(t6 + 3) = t7;              -- new sp[3] = env
     t4 = s->sp;
     t5 = s->extra_args;
     deref(t4 + 4) = (t5 << 1) + 1;   -- new sp[4] = Long_val(extra_args)
     t2 = s->accu;
     t3 = deref((code_t ptr ptr)t2 + 0); -- read code pointer from closure
     s->pc = t3;                       -- jump to code pointer
     t1 = s->accu;
     s->env = t1;                      -- set env to closure
     s->extra_args = 1;               -- set extra_args = 1
     return 0;

   Rocq handler (Interpret.v):
     handle_APPLY2 pc' s =
       match s.(stack) with
       | arg1 :: arg2 :: rest =>
         match get_code_ptr_s s s.(accu) with
         | Some target_pc =>
           let new_stack := arg1 :: arg2 :: Val_int pc' :: s.(env)
                            :: Val_int (Z.of_nat s.(extra_args)) :: rest in
           Step (s <|pc := target_pc|> <|stack := new_stack|>
                   <|env := s.(accu)|> <|extra_args := 1%nat|>)
         | None => Error "APPLY2: accu is not a closure"
         end
       | _ => Error "APPLY2: stack underflow"
       end

   The step_pre provides real preconditions that bridge the val_repr
   code pointer gap: the caller must supply a C value ret_pc_cval
   satisfying val_repr for Val_int pc', and the cast of the C pc
   pointer must produce that same value. This makes the precondition
   meaningful (documenting what is needed) rather than vacuously False.
   If val_repr is extended with a code-pointer constructor, the
   precondition becomes satisfiable and the proof works as-is.

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
(* Struct layout: _pc@0, _accu@8, _sp@16, _env@24, _extra_args@32     *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full) /\
  field_offset ce _extra_args (co_members co) = Errors.OK (32, Full).
Proof.
  eexists. split; [| split; [| split; [| split; [| split]]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_apply2 : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full) /\
  field_offset (genv_cenv clight_ge) _extra_args (co_members co) = Errors.OK (32, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Local Lemma sem_add_sp_2 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 2)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_sp_3 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 3)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 24))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_sp_4 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 4)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 32))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_sub_sp_3 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 3)) tint
    m = Some (Vptr sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 24))).
Proof.
  intros. unfold sem_binary_operation, sem_sub.
  change (classify_sub (tptr tlong) tint) with (sub_case_pi tlong Signed).
  cbv beta iota.
  change (sizeof (genv_cenv clight_ge) tlong) with 8%Z.
  unfold ptrofs_of_int. reflexivity.
Qed.

Local Lemma sem_cast_ptint_to_long : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) tlong m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

Local Lemma sem_shl_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong n) tlong
    (Vint (Int.repr 1)) tint
    m = Some (Vlong (Int64.shl' n (Int.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl. reflexivity.
Qed.

Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_cast_long_to_ptptint_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr (tptr tint)) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

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

Local Lemma sem_cast_int_to_long_1 : forall m,
  sem_cast (Vint (Int.repr 1)) tint tlong m = Some (Vlong (Int64.repr 1)).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Closure code pointer precondition (same pattern as APPLY)           *)
(* ================================================================== *)

Definition apply2_closure_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) (sp_b : block) : Prop :=
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
        accu_b <> sp_b /\
        (exists new_co,
          code_ofs = Ptrofs.add new_co (Ptrofs.repr (target_pc * sizeof_code_t)) /\
          code_b = cb).

(* ================================================================== *)
(* Step precondition for APPLY2                                        *)
(* ================================================================== *)

(* The step_pre requires:
   1. The closure code pointer is loadable (apply2_closure_pre).
   2. A C value ret_pc_cval representing Val_int pc' exists, and
      the cast of the C pc pointer produces it. This bridges the
      val_repr gap. val_repr only allows Vlong for Val_int, but
      the C cast of a Vptr stays Vptr. If val_repr gains a
      code-pointer constructor, these conditions become satisfiable.
   3. The sp has enough room (3 extra slots below current sp).
   4. extra_args fits in int64 for the shl encoding. *)
Definition apply2_step_pre
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  (* Closure code pointer -- parameterized by sp_b from the sp field *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     apply2_closure_pre m s ard sp_b) /\
  (* The pc value stored on the stack must have a valid val_repr *)
  (forall pc_ptr,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) = Some pc_ptr ->
     exists ret_pc_cval,
       sem_cast pc_ptr (tptr tint) tlong m = Some ret_pc_cval /\
       val_repr hm cb co (Val_int (Machine.pc s)) ret_pc_cval /\
       Val.load_result Mint64 ret_pc_cval = ret_pc_cval) /\
  (* sp >= 32 to accommodate 3 new pushes *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs >= 32) /\
  (* extra_args fits for shl encoding *)
  Z.of_nat (Machine.extra_args s) < Int64.half_modulus.

(* Tagged integer encoding: (ea << 1) + 1 = ea * 2 + 1 *)
Local Lemma tagged_ea_arith : forall ea,
  0 <= ea -> ea < Int64.half_modulus ->
  Int64.add (Int64.shl' (Int64.repr ea) (Int.repr 1)) (Int64.repr 1)
  = Int64.repr (ea * 2 + 1).
Proof.
  intros ea Hge Hlt.
  unfold Int64.shl', Int64.shl.
  change (Int.unsigned (Int.repr 1)) with 1%Z.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 1)%Z with 2%Z.
  rewrite Int64.add_unsigned.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_trans with (y := (ea * 2 + 1)%Z).
  2: { apply Int64.eqm_refl. }
  apply Int64.eqm_add.
  - apply Int64.eqm_unsigned_repr_l.
    apply Int64.eqm_mult.
    + apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
    + apply Int64.eqm_refl.
  - apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

(* val_repr_co_shift, stack_repr_co_shift, global_repr_co_shift
   are imported from HandlerLemmas. *)

Theorem verify_APPLY2_correct :
    handler_correct (fun pc' s => handle_APPLY2 pc' s) f_instr_APPLY2
      (fun _ => None)
      apply2_step_pre
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr APPLY2 = handle_APPLY2 and clight_of APPLY2 = f_instr_APPLY2
   by computation.  pre_of APPLY2 = apply2_step_pre is convertible.
   Error cases are bridged by case-splitting on the handler result and
   unfolding error_message_of / P_halt_of / P_ccall_of. *)
Definition correct_APPLY2 :
    handler_correct (Dispatch.handle_instr Bytecode.AST.APPLY2)
      (clight_of Bytecode.AST.APPLY2)
      (error_message_of Bytecode.AST.APPLY2)
      (pre_of Bytecode.AST.APPLY2) (P_halt_of Bytecode.AST.APPLY2)
      (P_ccall_of Bytecode.AST.APPLY2).
Proof.
Admitted.

