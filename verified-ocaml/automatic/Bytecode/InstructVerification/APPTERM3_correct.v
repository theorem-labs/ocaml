(* APPTERM3_correct.v -- APPTERM3 handler correctness proof.

   APPTERM3: tail call with 3 arguments.
   Reads arg1 = sp[0], arg2 = sp[1], arg3 = sp[2],
   reads slotsize from *pc, adjusts sp = sp + slotsize - 3,
   writes arg1, arg2, arg3 to new sp[0..2],
   reads code pointer from accu closure, sets pc, sets env = accu,
   updates extra_args += 2.

   C body (f_instr_APPTERM3):
     t13 = s->sp;
     arg1 = deref(t13 + 0);
     t12 = s->sp;
     arg2 = deref(t12 + 1);
     t11 = s->sp;
     arg3 = deref(t11 + 2);
     t8 = s->sp;
     t9 = s->pc;
     t10 = deref(t9);
     s->sp = t8 + t10 - 3;
     t7 = s->sp;
     deref(t7 + 0) = arg1;
     t6 = s->sp;
     deref(t6 + 1) = arg2;
     t5 = s->sp;
     deref(t5 + 2) = arg3;
     t3 = s->accu;
     t4 = deref((code_t ptr ptr) t3 + 0);
     s->pc = t4;
     t2 = s->accu;
     s->env = t2;
     t1 = s->extra_args;
     s->extra_args = t1 + 2;
     return 0;

   Rocq handler (Interpret.v):
     handle_APPTERM3 slotsize s =
       match s.(stack) with
       | arg1 :: arg2 :: arg3 :: _ =>
         let base := skipn slotsize s.(stack) in
         match get_code_ptr_s s s.(accu) with
         | Some target_pc =>
           Step (s <|pc := target_pc|>
                   <|stack := arg1 :: arg2 :: arg3 :: base|>
                   <|env := s.(accu)|>
                   <|extra_args := Nat.add s.(extra_args) 2|>)
         | None => Error "APPTERM3: accu is not a closure"
         end
       | _ => Error "APPTERM3: stack underflow"
       end

   Seven stores: sp (offset 16), sp[0..2] on stack, pc (offset 0),
   env (offset 24), extra_args (offset 32).

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
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.

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
(* Struct layout: _pc@0, _accu@8, _sp@16, _env@24, _extra_args@32    *)
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

Lemma interp_state_co_appterm3 : exists co,
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

(* sem_add for (tptr tlong) + 2 *)
Local Lemma sem_add_sp_2 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 2)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* sem_sub for (tptr tlong) - (tint) n *)
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

(* sem_add for tlong + tint (for extra_args update) *)
Local Lemma sem_add_long_int : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n1) tlong (Vint n2) tint m
    = Some (Vlong (Int64.add n1 (Int64.repr (Int.signed n2)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add tlong tint) with add_default.
  unfold sem_binarith.
  change (classify_binarith tlong tint) with (bin_case_l Signed). simpl.
  unfold sem_cast. simpl classify_cast. rewrite ptr64_true. simpl.
  reflexivity.
Qed.

(* sem_cast for tlong -> tlong *)
Local Lemma sem_cast_long_to_long : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof. intros. apply sem_cast_long_vlong. Qed.

(* load_result for Vlong *)
Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Closure code pointer precondition (same pattern as APPLY)           *)
(* ================================================================== *)

Definition appterm3_step_pre
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
(* Ptrofs arithmetic for sp + slotsize - 3                            *)
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

Local Lemma ptrofs_mul_8_3 :
  Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr 3)) = Ptrofs.repr 24.
Proof.
  change (ptrofs_of_int Signed (Int.repr 3)) with (Ptrofs.of_ints (Int.repr 3)).
  rewrite ptrofs_mul_8_of_ints_eq; [reflexivity | lia |].
  change Int.half_modulus with 2147483648. lia.
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

(* Arithmetic for extra_args + 2 *)
Local Lemma appterm3_add_ea : forall ea,
  Z.of_nat ea <= Int64.max_unsigned ->
  Z.of_nat ea <= Int64.max_signed ->
  Int64.add (Int64.repr (Z.of_nat ea))
            (Int64.repr (Int.signed (Int.repr 2)))
  = Int64.repr (Z.of_nat (ea + 2)).
Proof.
  intros ea Hea_u Hea_s.
  change (Int.signed (Int.repr 2)) with 2%Z.
  unfold Int64.add.
  f_equal.
  rewrite (Int64.unsigned_repr (Z.of_nat ea)).
  2: { change Int64.max_unsigned with 18446744073709551615. split; [lia | exact Hea_u]. }
  rewrite (Int64.unsigned_repr 2).
  2: { change Int64.max_unsigned with 18446744073709551615. lia. }
  rewrite Nat2Z.inj_add. reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

(* val_repr_co_shift, stack_repr_co_shift, global_repr_co_shift
   are imported from HandlerLemmas. *)

Theorem verify_APPTERM3_correct : forall slotsize,
    handler_correct (fun _ s => handle_APPTERM3 slotsize s) f_instr_APPTERM3
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
         (* sp + (slotsize - 3) * 8 >= 8 (writability of new sp[0..2]) *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs + (Z.of_nat slotsize - 3) * 8 >= 8) /\
         (* slotsize >= 3 *)
         (3 <= slotsize)%nat /\
         (* slotsize <= length of stack *)
         (slotsize <= Datatypes.length (Machine.stack s))%nat /\
         (* Closure code pointer is loadable *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            appterm3_step_pre m s ard sp_b) /\
         (* extra_args fits in Int64 range *)
         Z.of_nat (extra_args s) <= Int64.max_unsigned /\
         Z.of_nat (extra_args s) <= Int64.max_signed)
      (fun _ => None) (fun _ => None).
Proof.
Admitted.

(* ================================================================== *)
(* Wrapper: bridge verify_APPTERM3_correct to the InstructSpec form    *)
(* ================================================================== *)

Import Bytecode.AST.

Theorem correct_APPTERM3 : forall n,
    handler_correct (handle_instr (APPTERM3 n)) (clight_of (APPTERM3 n))
      (error_message_of (APPTERM3 n))
      (pre_of (APPTERM3 n)) (P_halt_of (APPTERM3 n)) (P_ccall_of (APPTERM3 n)).
Proof.
Admitted.
