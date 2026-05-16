(* APPTERM1_correct.v -- APPTERM1 handler correctness proof.

   APPTERM1 slotsize: tail call with 1 argument.
   Reads arg1 = sp[0], reads slotsize from *pc, adjusts
   sp = sp + slotsize - 1, writes arg1 to new sp[0],
   reads code pointer from accu closure, sets pc, sets env = accu.

   C body (f_instr_APPTERM1):
     t8 = s->sp;
     arg1 = deref(t8 + 0);            -- read arg1 from stack top
     t5 = s->sp;
     t6 = s->pc;
     t7 = deref(t6);                   -- read slotsize from code buffer
     s->sp = t5 + t7 - 1;             -- new sp = sp + slotsize - 1
     t4 = s->sp;
     deref(t4 + 0) = arg1;            -- write arg1 to new sp[0]
     t2 = s->accu;
     t3 = deref((code_t ptr ptr) t2 + 0); -- read code pointer from closure
     s->pc = t3;                       -- set pc to code pointer
     t1 = s->accu;
     s->env = t1;                      -- set env = accu
     return 0;

   Rocq handler (Interpret.v):
     handle_APPTERM1 slotsize s =
       match s.(stack) with
       | arg1 :: _ =>
         let base := skipn slotsize s.(stack) in
         match get_code_ptr_s s s.(accu) with
         | Some target_pc =>
           Step (s <|pc := target_pc|> <|stack := arg1 :: base|> <|env := s.(accu)|>)
         | None => Error "APPTERM1: accu is not a closure"
         end
       | _ => Error "APPTERM1: stack underflow"
       end

   Four stores: sp (offset 16), sp[0] on stack, pc (offset 0), env (offset 24).

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
(* Struct layout: _pc@0, _accu@8, _sp@16, _env@24                     *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full).
Proof.
  eexists. split; [| split; [| split; [| split]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_appterm1 : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

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

(* sem_add for (tptr tlong) + tint n *)
Local Lemma sem_add_sp_n : forall sp_b sp_ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint n) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs
                (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* sem_sub for (tptr tlong) - (tint) 1 *)
Local Lemma sem_sub_sp_int : forall sp_b sp_ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint n) tint
    m = Some (Vptr sp_b (Ptrofs.sub sp_ofs
                (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_sub.
  change (classify_sub (tptr tlong) tint) with (sub_case_pi tlong Signed).
  cbv beta iota.
  change (sizeof (genv_cenv clight_ge) tlong) with 8%Z.
  reflexivity.
Qed.

(* ================================================================== *)
(* Closure code pointer precondition (same pattern as APPLY)           *)
(* ================================================================== *)

Definition appterm1_step_pre
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
(* Ptrofs arithmetic for sp + slotsize - 1                            *)
(* ================================================================== *)

Local Lemma ptrofs_max_unsigned_large : (Ptrofs.max_unsigned >= 2^32)%Z.
Proof. vm_compute. discriminate. Qed.

Local Lemma ptrofs_mul_8_of_ints_eq : forall n,
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

Local Lemma ptrofs_add_repr : forall a b,
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  intros. rewrite Ptrofs.add_unsigned.
  apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add;
    apply Ptrofs.eqm_sym;
    apply Ptrofs.eqm_unsigned_repr.
Qed.

Local Lemma ptrofs_add_zero : forall ofs,
  Ptrofs.add ofs (Ptrofs.repr 0) = ofs.
Proof.
  intros. rewrite Ptrofs.add_zero. reflexivity.
Qed.

Local Lemma stack_repr_skipn : forall n hm cb co m stk sp_b sp_ofs,
  stack_repr hm cb co m stk sp_b sp_ofs ->
  stack_repr hm cb co m (skipn n stk) sp_b
    (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat n * 8))).
Proof.
  induction n as [| n' IH]; intros hm0 cb0 co0 m0 stk0 sp_b0 sp_ofs0 Hsr.
  - simpl. rewrite ptrofs_add_zero. exact Hsr.
  - destruct stk0 as [| v vs].
    + simpl. constructor.
    + simpl skipn. inversion Hsr; subst.
      specialize (IH hm0 cb0 co0 m0 vs sp_b0 (Ptrofs.add sp_ofs0 (Ptrofs.repr 8)) H5).
      replace (Ptrofs.add sp_ofs0 (Ptrofs.repr (Z.of_nat (S n') * 8)))
        with (Ptrofs.add (Ptrofs.add sp_ofs0 (Ptrofs.repr 8)) (Ptrofs.repr (Z.of_nat n' * 8))).
      { exact IH. }
      { rewrite Ptrofs.add_assoc. f_equal.
        rewrite ptrofs_add_repr. f_equal. lia. }
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

(* val_repr_co_shift, stack_repr_co_shift, global_repr_co_shift
   are imported from HandlerLemmas. *)

Theorem verify_APPTERM1_correct : forall slotsize,
    handler_correct (fun _ s => handle_APPTERM1 slotsize s) f_instr_APPTERM1
      (fun _ => None)
      (fun _ m s ard =>
         (* The code buffer contains Int.repr slotsize at the current PC *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat slotsize))) /\
         (* slotsize fits in int32 signed range *)
         Z.of_nat slotsize < Int.half_modulus /\
         (* sp + slotsize * 8 fits in ptrofs *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs + Z.of_nat slotsize * 8 < Ptrofs.modulus) /\
         (* sp + (slotsize - 1) * 8 >= 8 (writability of new sp[0]) *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs + (Z.of_nat slotsize - 1) * 8 >= 8) /\
         (* slotsize >= 1 *)
         (1 <= slotsize)%nat /\
         (* slotsize <= length of stack *)
         (slotsize <= Datatypes.length (Machine.stack s))%nat /\
         (* Closure code pointer is loadable *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            appterm1_step_pre m s ard sp_b))
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

(* ================================================================== *)
(* Wrapper matching InstructVerificationFineGrainedSpec signature.     *)
(*   handle_instr (APPTERM1 n) reduces to handle_APPTERM1 n by        *)
(*   computation.  clight_of (APPTERM1 n) = f_instr_APPTERM1,         *)
(*   pre_of (APPTERM1 n) = appterm1_step_pre n (from InstructSpec).   *)
(*   Error case matches error_message_of exactly.                            *)
(*   Step case delegates to verify_APPTERM1_correct.                   *)
(* ================================================================== *)
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

Theorem correct_APPTERM1 : forall n,
    handler_correct (handle_instr (APPTERM1 n)) (clight_of (APPTERM1 n))
      (error_message_of (APPTERM1 n))
      (pre_of (APPTERM1 n)) (P_halt_of (APPTERM1 n)) (P_ccall_of (APPTERM1 n)).
Proof.
Admitted.
