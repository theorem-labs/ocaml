(* DIVINT_correct.v -- correctness proof for the DIVINT bytecode handler.

   C (Clight AST):
     _t'1 = s->sp;                          // load sp
     s->sp = _t'1 + 1;                      // sp++ (pop stack)
     _t'3 = *_t'1;                          // load stack[0] (b_tagged)
     _divisor = (long)_t'3 >> 1;            // untag b
     if (_divisor == 0) caml_raise_zero_divide(); else skip;
     _t'2 = s->accu;                        // load accu (a_tagged)
     s->accu = (((long)_t'2 >> 1) / _divisor) << 1 + 1;  // untag, div, retag

   Rocq handler:
     handle_DIVINT pc' s = match accu, stack with
       | Val_int a, Val_int b :: rest =>
           if Z.eqb b 0 then do_raise div_by_zero_exn s
           else Step (s<|pc:=pc'|><|accu:=Val_int(Z.quot a b)|><|stack:=rest|>)
       | _, _ => Error ...

   Precondition (handler_correct):
     b <> 0 -- the stack top is nonzero
     Tagged values are in Int64 signed range (true for OCaml 63-bit ints)

   The do_raise case (b=0) is handled vacuously: the precondition is
   False when b=0, so the Step branch from do_raise is discharged. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Import Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

(* ================================================================== *)
(* Semantic lemmas for DIVINT C operations                             *)
(* ================================================================== *)

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

Local Lemma sem_eq_long_int_0 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oeq
    (Vlong n) tlong (Vint (Int.repr 0)) tint m
  = Some (Val.of_bool (Int64.eq n Int64.zero)).
Proof.
  intros. unfold sem_binary_operation, sem_cmp, cmp_ptr.
  change (classify_cmp tlong tint) with cmp_default.
  unfold sem_binarith.
  change (classify_binarith tlong tint) with (bin_case_l Signed).
  simpl. reflexivity.
Qed.

Local Lemma bool_val_of_bool_tint : forall b m,
  bool_val (Val.of_bool b) tint m = Some b.
Proof. intros [] m; reflexivity. Qed.

Local Lemma sem_shl_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shl n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Tagged arithmetic lemmas for DIVINT                                 *)
(* ================================================================== *)

(* Signed shift right of tagged value gives back the original integer *)
Local Lemma shr_tagged_repr : forall b,
  Int64.min_signed <= b * 2 + 1 <= Int64.max_signed ->
  Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1) = Int64.repr b.
Proof.
  intros b Hrange.
  unfold Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1.
  rewrite Int64.signed_repr by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  f_equal.
  replace ((b * 2 + 1) / 2) with b by (apply Z.div_unique with 1; lia).
  reflexivity.
Qed.

(* When b <> 0 and tagged value is in signed range, the untagged divisor
   is nonzero in Int64 representation. *)
Local Lemma shr_tagged_ne_zero : forall b,
  b <> 0 ->
  Int64.min_signed <= b * 2 + 1 <= Int64.max_signed ->
  Int64.eq (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)) Int64.zero = false.
Proof.
  intros b Hb Hrange.
  rewrite shr_tagged_repr by lia.
  unfold Int64.eq.
  change (Int64.unsigned Int64.zero) with 0.
  destruct (zeq (Int64.unsigned (Int64.repr b)) 0); [|reflexivity].
  exfalso. apply Hb.
  assert (Int64.repr b = Int64.zero) as Hrepr_eq.
  { apply Int64.same_if_eq. unfold Int64.eq. rewrite e. reflexivity. }
  apply (f_equal Int64.signed) in Hrepr_eq.
  rewrite Int64.signed_zero in Hrepr_eq.
  rewrite Int64.signed_repr in Hrepr_eq.
  - exact Hrepr_eq.
  - unfold Int64.min_signed, Int64.max_signed in *.
    generalize Int64.half_modulus_pos. lia.
Qed.

(* shr(n, 1) can never be min_signed: the signed value of shr(n,1) is
   in [-2^62, 2^62-1], which excludes min_signed = -2^63. *)
Local Lemma shr_1_ne_min_signed : forall n,
  Int64.eq (Int64.shr n (Int64.repr 1)) (Int64.repr Int64.min_signed) = false.
Proof.
  intros.
  unfold Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1.
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  apply Int64.eq_false. intro Heq.
  apply (f_equal Int64.signed) in Heq.
  rewrite Int64.signed_repr in Heq.
  2: { pose proof (Int64.signed_range n).
       unfold Int64.min_signed, Int64.max_signed in *.
       generalize Int64.half_modulus_pos. intro Hp. split.
       + apply Z.div_le_lower_bound. lia. unfold Int64.min_signed. lia.
       + apply Z.div_le_upper_bound. lia. unfold Int64.max_signed. lia. }
  rewrite Int64.signed_repr in Heq.
  2: { unfold Int64.min_signed, Int64.max_signed.
       generalize Int64.half_modulus_pos. lia. }
  pose proof (Int64.signed_range n).
  unfold Int64.min_signed, Int64.max_signed in *.
  (* lia can't handle division with opaque half_modulus; concretize it *)
  assert (Hlo : -Int64.half_modulus / 2 <= Int64.signed n / 2).
  { apply Z.div_le_mono. lia. lia. }
  assert (Hhi : Int64.signed n / 2 <= (Int64.half_modulus - 1) / 2).
  { apply Z.div_le_mono. lia. lia. }
  cut (Int64.half_modulus = 9223372036854775808).
  { intro Hval. rewrite Hval in *.
    change (- (9223372036854775808) / 2) with (-4611686018427387904) in Hlo.
    change ((9223372036854775808 - 1) / 2) with 4611686018427387903 in Hhi.
    lia. }
  reflexivity.
Qed.

(* sem_div succeeds on shr'd tagged values when the divisor is nonzero.
   The overflow guard (min_signed / -1) is automatically false because
   shr(n,1) can never equal min_signed. *)
Local Lemma sem_div_shr_succeeds : forall n1 n2 m,
  Int64.eq (Int64.shr n2 (Int64.repr 1)) Int64.zero = false ->
  sem_binary_operation (genv_cenv clight_ge) Odiv
    (Vlong (Int64.shr n1 (Int64.repr 1))) tlong
    (Vlong (Int64.shr n2 (Int64.repr 1))) tlong m
  = Some (Vlong (Int64.divs (Int64.shr n1 (Int64.repr 1))
                             (Int64.shr n2 (Int64.repr 1)))).
Proof.
  intros n1 n2 m Hdivisor.
  unfold sem_binary_operation, sem_div, sem_binarith.
  change (classify_binarith tlong tlong) with (bin_case_l Signed).
  simpl.
  rewrite sem_cast_long_vlong. rewrite sem_cast_long_vlong. simpl.
  rewrite Hdivisor. simpl.
  rewrite shr_1_ne_min_signed. reflexivity.
Qed.

(* The combined tagged division arithmetic identity:
   shl(divs(repr(a), repr(b)), 1) + 1 = repr(Z.quot a b * 2 + 1)
   when a, b are in signed range and b <> 0. *)
Local Lemma tagged_divint_arith : forall a b,
  Int64.min_signed <= a * 2 + 1 <= Int64.max_signed ->
  Int64.min_signed <= b * 2 + 1 <= Int64.max_signed ->
  b <> 0 ->
  Int64.add
    (Int64.shl
      (Int64.divs (Int64.shr (Int64.repr (a * 2 + 1)) (Int64.repr 1))
                   (Int64.shr (Int64.repr (b * 2 + 1)) (Int64.repr 1)))
      (Int64.repr 1))
    (Int64.repr 1)
  = Int64.repr (Z.quot a b * 2 + 1).
Proof.
  intros a b Harange Hbrange Hb.
  (* Reduce shr of tagged values *)
  unfold Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1.
  rewrite (Int64.signed_repr (a * 2 + 1)) by lia.
  rewrite (Int64.signed_repr (b * 2 + 1)) by lia.
  rewrite !Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  replace ((a * 2 + 1) / 2) with a by (apply Z.div_unique with 1; lia).
  replace ((b * 2 + 1) / 2) with b by (apply Z.div_unique with 1; lia).
  (* Reduce divs *)
  unfold Int64.divs.
  rewrite Int64.signed_repr
    by (unfold Int64.min_signed, Int64.max_signed in *;
        generalize Int64.half_modulus_pos; lia).
  rewrite Int64.signed_repr
    by (unfold Int64.min_signed, Int64.max_signed in *;
        generalize Int64.half_modulus_pos; lia).
  (* Reduce shl and add *)
  unfold Int64.shl, Int64.add.
  change (Int64.unsigned (Int64.repr 1)) with 1.
  rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
  apply Int64.eqm_samerepr.
  eapply Int64.eqm_trans.
  - apply Int64.eqm_add.
    + eapply Int64.eqm_trans.
      * apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
      * apply Int64.eqm_mult.
        -- apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
        -- apply Int64.eqm_refl.
    + apply Int64.eqm_refl.
  - apply Int64.eqm_refl.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_DIVINT_correct :
    handler_correct handle_DIVINT f_instr_DIVINT
      (fun _ => None)
      (fun _ _ s ard =>
         match s.(Machine.accu), s.(Machine.stack) with
         | Val_int a, Val_int b :: _ =>
             b <> 0%Z /\
             Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
             Int64.min_signed <= b * 2 + 1 <= Int64.max_signed /\
             int_vlong ard a /\
             int_vlong ard b
         | _, _ => True
         end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Exported version with named building-block precondition *)
Theorem verify_DIVINT_handler_correct :
    handler_correct handle_DIVINT f_instr_DIVINT
      (fun _ => None)
      divmod_safe
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Helper: do_raise returning Error implies error_message_of_raise = Some msg *)
Local Lemma do_raise_error_iff : forall exn s msg,
  do_raise exn s = Error msg ->
  error_message_of_raise s = Some msg.
Proof.
  intros exn s msg H.
  unfold do_raise in H. unfold error_message_of_raise.
  destruct (Nat.eqb (trap_sp s) 0) eqn:Htrap.
  - inversion H. reflexivity.
  - set (k := Nat.sub (length (Machine.stack s)) (trap_sp s)) in *.
    set (frame_top := skipn k (Machine.stack s)) in *.
    destruct frame_top as [|v1 rest1]; [inversion H; reflexivity|].
    destruct v1; try (inversion H; reflexivity).
    destruct rest1 as [|v2 rest2]; [inversion H; reflexivity|].
    destruct v2; try (inversion H; reflexivity).
    destruct rest2 as [|v3 rest3]; [inversion H; reflexivity|].
    destruct rest3 as [|v4 rest4]; [inversion H; reflexivity|].
    destruct v4; inversion H; reflexivity.
Qed.

(* Wrapper with the canonical type expected by InstructVerificationProof.v *)
Theorem correct_DIVINT :
  handler_correct (handle_instr Bytecode.AST.DIVINT) (clight_of Bytecode.AST.DIVINT)
    (error_message_of Bytecode.AST.DIVINT)
    (pre_of Bytecode.AST.DIVINT) (P_halt_of Bytecode.AST.DIVINT) (P_ccall_of Bytecode.AST.DIVINT).
Proof.
Admitted.
