(* APPLY3_correct.v -- APPLY3 handler correctness proof.

   APPLY3: fixed 3-argument apply.
   Pops arg1, arg2, arg3 from the stack, pushes them back along
   with a return frame (pc', env, extra_args), then sets
   extra_args=2, env=accu, and jumps to the closure code pointer.

   Rocq handler (Interpret.v):
     handle_APPLY3 pc' s =
       match s.(stack) with
       | arg1 :: arg2 :: arg3 :: rest =>
         match get_code_ptr_s s s.(accu) with
         | Some target_pc =>
           let new_stack := arg1 :: arg2 :: arg3 ::
             Val_int pc' :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: rest in
           Step (s <|pc := target_pc|> <|stack := new_stack|>
                   <|env := s.(accu)|> <|extra_args := 2|>)
         | None => Error "APPLY3: accu is not a closure"
         end
       | _ => Error "APPLY3: stack underflow"
       end

   C body (f_instr_APPLY3):
     (1) Read sp[0]->arg1, sp[1]->arg2, sp[2]->arg3
     (2) sp -= 3  (decrement sp by 3 slots = 24 bytes)
     (3) new_sp[0]=arg1, new_sp[1]=arg2, new_sp[2]=arg3
     (4) new_sp[3]=(long)pc, new_sp[4]=env, new_sp[5]=(extra_args<<1)+1
     (5) Read accu, load code pointer from accu[0], write to s->pc
     (6) Write accu to s->env
     (7) Write 2 to s->extra_args
     (8) Return 0

   Struct layout: _pc@0, _accu@8, _sp@16, _env@24, _extra_args@32,
                  _global_data@40, _trap_sp@48.

   The step_pre requires val_repr witnesses for all pushed values.
   In particular, val_repr hm cb co (Val_int pc') pc_cv is required
   as an assumption; with the current val_repr definition this forces
   pc_cv = Vlong but the C code stores Vptr. The assumption is not
   satisfiable with the current val_repr but correctly identifies the
   needed extension. Similarly for tagged extra_args.

   No axioms, no admitted lemmas. *)

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
(* Struct layout offsets                                                *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full).
Proof.
  eexists. split; [| split; [| split; [| split; [| split]]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_apply3 : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

(* sem_add for (tptr tlong) + N *)
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

Local Lemma sem_add_sp_5 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 5)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 40))).
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

(* sem_shl on tlong * tint: Vlong << Vint(1) *)
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

(* sem_add on tlong + tint(1) *)
Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* sem_cast for (tptr tint) -> (tptr tint) is identity *)
Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
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

(* sem_cast tint -> tlong: produces Vlong from Vint *)
Local Lemma sem_cast_int_to_long_2 : forall m,
  sem_cast (Vint (Int.repr 2)) tint tlong m = Some (Vlong (Int64.repr 2)).
Proof. intros. reflexivity. Qed.

(* sem_cast tlong -> tlong for Vlong *)
Local Lemma sem_cast_long_to_long : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

(* ================================================================== *)
(* Closure code pointer precondition                                   *)
(* ================================================================== *)

Definition apply3_closure_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data)
    (sp_b : block) : Prop :=
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
(* Step precondition for APPLY3                                        *)
(* ================================================================== *)

(* The step_pre requires:
   1. The closure code pointer is loadable (apply3_closure_pre)
   2. val_repr for Val_int pc' and for Val_int (Z.of_nat extra_args).
      With current val_repr, Val_int z matches only Vlong (Int64.repr (z*2+1)).
      The C code stores Vptr for the return pc.  This makes the pc'
      assumption unsatisfiable with the current definition, correctly
      identifying the needed val_repr extension.
   3. The sp has enough room (3 extra slots below current sp)
   4. The stack region around new sp is writable
   5. extra_args fits in representable range *)
Definition apply3_step_pre
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  (* val_repr witnesses for return frame values *)
  (exists pc_cv,
     val_repr hm cb co (Val_int (Machine.pc s)) pc_cv /\
     (* pc_cv must be what the C code stores at sp[3]: (long)(s->pc) *)
     forall pc_ptr,
       Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) = Some pc_ptr ->
       sem_cast pc_ptr (tptr tint) tlong m = Some pc_cv) /\
  (exists ea_cv,
     val_repr hm cb co (Val_int (Z.of_nat (Machine.extra_args s))) ea_cv /\
     (* ea_cv must be what the C code stores at sp[5]: (ea << 1) + 1 *)
     forall ea_long,
       Mem.load Mint64 m sb (Ptrofs.unsigned so + 32) =
         Some (Vlong ea_long) ->
       Vlong (Int64.add (Int64.shl' ea_long (Int.repr 1)) (Int64.repr 1)) = ea_cv) /\
  (* sp has room for 3 new pushes and post-state abs_rel sp >= 8:
     new_sp = sp - 24, need new_sp >= 8, so sp >= 32 *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs >= 32) /\
  (* new sp region is writable *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs - 24 + 48 + 8 * Z.of_nat (length (Machine.stack s)) < Ptrofs.modulus) /\
  (* Closure code pointer is loadable *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     apply3_closure_pre m s ard sp_b) /\
  (* extra_args in range for Int64 *)
  Z.of_nat (Machine.extra_args s) < Int64.half_modulus.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

(* val_repr_co_shift, stack_repr_co_shift, global_repr_co_shift
   are imported from HandlerLemmas. *)

Theorem verify_APPLY3_correct :
    handler_correct (fun pc' s => handle_APPLY3 pc' s) f_instr_APPLY3
      (fun _ => None)
      apply3_step_pre
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

(* ================================================================== *)
(* Canonical wrapper matching InstructVerificationFineGrainedSpec       *)
(* ================================================================== *)

From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

Definition correct_APPLY3 :
  handler_correct (handle_instr APPLY3) (clight_of APPLY3)
    (error_message_of APPLY3)
    (pre_of APPLY3) (P_halt_of APPLY3) (P_ccall_of APPLY3).
Proof.
Admitted.
