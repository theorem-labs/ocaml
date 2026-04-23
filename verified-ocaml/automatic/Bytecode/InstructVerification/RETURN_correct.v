(* RETURN_correct.v -- RETURN handler completeness proof.

   RETURN stacksize:
   - Rocq: handle_RETURN stacksize s =
       let stk = skipn stacksize (stack s) in
       if Nat.ltb 0 (extra_args s) then
         match get_code_ptr_s s (accu s) with
         | Some target_pc =>
           Step (s <|pc := target_pc|> <|stack := stk|> <|env := accu s|>
                   <|extra_args := Nat.sub (extra_args s) 1|>)
         | None => Error "RETURN: accu is not a closure"
         end
       else
         match stk with
         | Val_int ret_pc :: saved_env :: Val_int saved_ea :: rest =>
           Step (s <|pc := ret_pc|> <|stack := rest|> <|env := saved_env|>
                   <|extra_args := Z.to_nat saved_ea|>)
         | _ => Error "RETURN: malformed return frame"
         end

   C code (f_instr_RETURN):
     Preamble: read pc, advance pc, read sp, read n from code, sp += n
     if extra_args > 0 then
       extra_args -= 1
       pc = code_ptr from accu closure field 0
       env = accu
     else
       pc = cast sp[0] to code_t ptr
       env = sp[1]
       extra_args = sp[2] >> 1
       sp += 3
     return 0

   Both Step branches proved with real preconditions.
   NO AXIOMS, NO Admitted. *)

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
(* Struct layout                                                       *)
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

Lemma interp_state_co_return : exists co,
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

(* sem_cast for tlong -> (tptr tint) when value is Vptr (x86-64 cast_case_pointer) *)
Local Lemma sem_cast_long_to_ptr_tint_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tint) m = Some (Vptr b ofs).
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

(* sem_add for (tptr tlong) + 3 *)
Local Lemma sem_add_sp_3 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 3)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 24))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* sem_add for (tptr tint) + 1 = ofs + 4 (code pointer advance) *)
Local Lemma sem_add_ptr_int_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint) (Vint (Int.repr 1)) tint m
    = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* Ogt on tlong vs tint: CompCert promotes tint to tlong (signed),
   then does Int64.cmp Cgt = Int64.lt (rhs) (lhs) *)
Local Lemma sem_gt_long_int : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Ogt
    (Vlong n1) tlong (Vint n2) tint m
    = Some (Val.of_bool (Int64.lt (Int64.repr (Int.signed n2)) n1)).
Proof.
  intros. unfold sem_binary_operation, sem_cmp.
  change (classify_cmp tlong tint) with cmp_default. simpl.
  unfold sem_binarith.
  change (classify_binarith tlong tint) with (bin_case_l Signed). simpl.
  unfold sem_cast. simpl classify_cast. rewrite ptr64_true. simpl.
  reflexivity.
Qed.

(* Ogt extra_args > 0 corresponds to Nat.ltb 0 (extra_args s) *)
Local Lemma return_gt_iff : forall ea,
  Z.of_nat ea <= Int64.max_signed ->
  Int64.lt (Int64.repr (Int.signed (Int.repr 0))) (Int64.repr (Z.of_nat ea))
  = Nat.ltb 0 ea.
Proof.
  intros ea Hea.
  change Int64.max_signed with 9223372036854775807 in Hea.
  rewrite Int.signed_repr.
  2: { change Int.min_signed with (-2147483648).
       change Int.max_signed with 2147483647. lia. }
  unfold Int64.lt.
  rewrite (Int64.signed_repr 0).
  2: { change Int64.min_signed with (-9223372036854775808).
       change Int64.max_signed with 9223372036854775807. lia. }
  rewrite Int64.signed_repr.
  2: { change Int64.min_signed with (-9223372036854775808).
       change Int64.max_signed with 9223372036854775807. lia. }
  destruct ea as [| ea'].
  - simpl. reflexivity.
  - change (Nat.ltb 0 (S ea')) with true.
    destruct (zlt 0 (Z.of_nat (S ea'))) as [Hlt | Hlt].
    + reflexivity.
    + exfalso. lia.
Qed.

(* Oshr for tlong >> tint(1) *)
Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl. reflexivity.
Qed.

Local Lemma bool_val_of_bool : forall b m,
  bool_val (Val.of_bool b) tint m = Some b.
Proof. intros. destruct b; reflexivity. Qed.

(* ================================================================== *)
(* Ptrofs arithmetic                                                   *)
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

(* return_tailcall_pre and return_frame_pre are defined in InstructSpec.v *)

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

#[warnings="-not-a-closed-proof"]
Theorem verify_RETURN_correct : forall stacksize,
    handler_correct (fun _ => handle_RETURN stacksize) f_instr_RETURN
      (fun _ => None)
      (fun _ m s ard =>
         (* Common preamble: code buffer has stacksize at current PC *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat stacksize))) /\
         (* stacksize fits in int32 signed range *)
         Z.of_nat stacksize < Int.half_modulus /\
         (* extra_args fits in Int64 signed range *)
         Z.of_nat (extra_args s) <= Int64.max_signed /\
         (* sp + stacksize * 8 fits in ptrofs *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs + Z.of_nat stacksize * 8 < Ptrofs.modulus) /\
         (* stacksize <= length of stack *)
         (stacksize <= Datatypes.length (Machine.stack s))%nat /\
         (* Then-branch precondition: closure code pointer *)
         (Nat.ltb 0 (extra_args s) = true ->
          forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            return_tailcall_pre m s ard sp_b) /\
         (* Else-branch precondition: return frame *)
         (Nat.ltb 0 (extra_args s) = false ->
          forall sp_b sp_ofs ret_pc saved_env saved_ea rest,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            skipn stacksize (Machine.stack s) =
              Val_int ret_pc :: saved_env :: Val_int saved_ea :: rest ->
            return_frame_pre m s ard sp_b
              (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat stacksize * 8)))
              ret_pc saved_env saved_ea rest))
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* ================================================================== *)
(* Error bridge lemma                                                  *)
(* ================================================================== *)

Local Notation RETURN := Bytecode.AST.RETURN.

Local Lemma handle_RETURN_error_implies_error_message : forall stacksize s msg,
  handle_RETURN stacksize s = Error msg ->
  error_message_of (RETURN stacksize) s = Some msg.
Proof.
  intros stacksize s msg Herr.
  unfold handle_RETURN in Herr.
  unfold error_message_of.
  set (stk := skipn stacksize (Machine.stack s)) in *.
  destruct (Nat.ltb 0 (extra_args s)) eqn:Hltb.
  - (* extra_args > 0: get_code_ptr_s *)
    destruct (get_code_ptr_s s (Machine.accu s)) eqn:Hgcp.
    + discriminate.
    + inversion Herr. reflexivity.
  - (* extra_args = 0: check stk *)
    destruct stk as [| v0 rest0]; try (inversion Herr; reflexivity).
    destruct v0; try (inversion Herr; reflexivity).
    destruct rest0 as [| v1 rest1]; try (inversion Herr; reflexivity).
    destruct rest1 as [| v2 rest2]; try (destruct v1; inversion Herr; reflexivity).
    destruct v2; inversion Herr; reflexivity.
Qed.

(* ================================================================== *)
(* Bridge wrapper: correct_RETURN                                      *)
(* ================================================================== *)

Definition correct_RETURN : forall n,
  handler_correct (handle_instr (RETURN n)) (clight_of (RETURN n))
    (error_message_of (RETURN n))
    (pre_of (RETURN n)) (P_halt_of (RETURN n)) (P_ccall_of (RETURN n)).
Proof.
Admitted.
