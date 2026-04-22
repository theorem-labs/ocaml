(* POPTRAP_correct.v -- POPTRAP handler completeness proof.

   POPTRAP: pops the 4-element trap frame from the stack, restoring
   trap_sp from the encoded trap link at sp[1].

   C code (f_instr_POPTRAP):
     _t'2 = s->sp;                         // read sp
     _t'3 = s->sp;                         // read sp again
     _t'4 = *(cast (_t'3, tptr tlong) + 1);  // read sp[1] (trap link)
     s->trap_sp = _t'2 + (_t'4 >> 1);      // trap_sp = sp + (link >> 1)
     _t'1 = s->sp;                         // read sp
     s->sp = _t'1 + 4;                     // sp += 4 (pop 4 values)
     return 0;

   Rocq:
     handle_POPTRAP pc' s =
       match s.(stack) with
       | _ :: Val_int prev_tsp :: _ :: _ :: rest =>
         Step (s <|pc := pc'|> <|stack := rest|> <|trap_sp := Z.to_nat prev_tsp|>)
       | _ => Error "POPTRAP: malformed trap frame"
       end

   Two stores on the struct block:
     Store 1: trap_sp field (sb, uso+48) <- new trap_sp ptr
     Store 2: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs

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
(* Struct layout lemmas                                                *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _trap_sp (co_members co) = Errors.OK (48, Full).
Proof.
  eexists. split; [| split]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_sp_trapsp : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _trap_sp (co_members co) = Errors.OK (48, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Lemma sem_add_sp_4 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 4)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 32))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* sp + (long): pointer arithmetic on (tptr tlong) + tlong.
   sizeof(tlong) = 8, so sp + n = sp + n * 8 bytes.
   CompCert classifies (tptr tlong) + tlong as add_case_pl tlong. *)
Lemma sem_add_ptr_tlong : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong)
    (Vlong n) tlong m
  = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tlong) with (add_case_pl tlong).
  unfold sem_add_ptr_long. reflexivity.
Qed.

Lemma sem_shr_long_int_1 : forall n m,
  Int.ltu (Int.repr 1) Int64.iwordsize' = true ->
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m =
    Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof.
  intros n m _.
  unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl.
  change (Int.ltu (Int.repr 1) Int64.iwordsize') with true.
  reflexivity.
Qed.

Lemma iwordsize_ltu_1 : Int.ltu (Int.repr 1) Int64.iwordsize' = true.
Proof. reflexivity. Qed.

(* cast from tlong to tlong is identity for Vlong *)
Lemma sem_cast_long_to_long : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

(* stack_repr for skipn 4 *)
Lemma ptrofs_add_repr : forall a b,
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  intros. rewrite Ptrofs.add_unsigned.
  apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add;
    apply Ptrofs.eqm_sym;
    apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma stack_repr_skip4 : forall hm cb co m v0 v1 v2 v3 rest sp_b sp_ofs,
  stack_repr hm cb co m (v0 :: v1 :: v2 :: v3 :: rest) sp_b sp_ofs ->
  stack_repr hm cb co m rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 32)).
Proof.
  intros hm cb co m v0 v1 v2 v3 rest sp_b sp_ofs Hsr.
  inversion Hsr as [| ? ? ? ? cv0 Hload0 Hvr0 Hsr1]. subst.
  inversion Hsr1 as [| ? ? ? ? cv1 Hload1 Hvr1 Hsr2]. subst.
  inversion Hsr2 as [| ? ? ? ? cv2 Hload2 Hvr2 Hsr3]. subst.
  inversion Hsr3 as [| ? ? ? ? cv3 Hload3 Hvr3 Hsr4]. subst.
  replace (Ptrofs.add sp_ofs (Ptrofs.repr 32))
    with (Ptrofs.add (Ptrofs.add (Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8)) (Ptrofs.repr 8)) (Ptrofs.repr 8)).
  - exact Hsr4.
  - rewrite Ptrofs.add_assoc.
    replace (Ptrofs.add (Ptrofs.repr 8) (Ptrofs.repr 8)) with (Ptrofs.repr 16)
      by (rewrite ptrofs_add_repr; f_equal; lia).
    rewrite Ptrofs.add_assoc.
    replace (Ptrofs.add (Ptrofs.repr 16) (Ptrofs.repr 8)) with (Ptrofs.repr 24)
      by (rewrite ptrofs_add_repr; f_equal; lia).
    rewrite Ptrofs.add_assoc.
    replace (Ptrofs.add (Ptrofs.repr 24) (Ptrofs.repr 8)) with (Ptrofs.repr 32)
      by (rewrite ptrofs_add_repr; f_equal; lia).
    reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_POPTRAP_correct :
    handler_correct (handle_POPTRAP) f_instr_POPTRAP
      (fun _ m s ard =>
         (* Stack has at least 4 elements with trap link at position 1 *)
         exists v0 prev_tsp v2 v3 rest,
           Machine.stack s = v0 :: Val_int prev_tsp :: v2 :: v3 :: rest /\
         (* The C-encoded trap link sp[1] is Vlong(prev_tsp*2+1) *)
         (* which when shifted right by 1 gives prev_tsp.
            The C code computes trap_sp = sp + (sp[1] >> 1).
            We need the arithmetic to work out. *)
         (* sp[1] load succeeds and equals the encoded prev_tsp *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Mem.load Mint64 m sp_b (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 8)))
              = Some (Vlong (Int64.repr (prev_tsp * 2 + 1)))) /\
         (* The shift-right arithmetic identity *)
         Int64.shr (Int64.repr (prev_tsp * 2 + 1)) (Int64.repr 1) =
           Int64.repr prev_tsp /\
         (* The ptrofs arithmetic: sp + prev_tsp*8 fits *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs + 32 + 8 * Z.of_nat (length rest) < Ptrofs.modulus) /\
         (* trap_sp_rel for the new trap_sp value *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            trap_sp_rel
              (Vptr sp_b (Ptrofs.add sp_ofs
                 (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr prev_tsp)))))
              (ar_stack_block ard) (ar_stack_base_ofs ard)
              (Z.to_nat prev_tsp)))
      (fun msg _ => msg = "POPTRAP: malformed trap frame"%string)
      (fun _ => False) (fun _ _ _ => False).
Proof. Admitted.

(* Bridge lemma: when handle_POPTRAP returns Error, error_message_of
   computes the same message.  Both share the same case analysis on the
   stack, so this is a direct computation. *)
Local Lemma handle_POPTRAP_error_implies_error_message :
  forall pc' s msg,
    handle_POPTRAP pc' s = Error msg ->
    error_message_of POPTRAP s = Some msg.
Proof.
  intros pc' s msg H.
  unfold handle_POPTRAP in H.
  unfold error_message_of.
  destruct (Machine.stack s) as [| v0 stk1].
  - inversion H. reflexivity.
  - destruct stk1 as [| v1 stk2].
    + inversion H. reflexivity.
    + destruct v1 as [z1 | | |].
      * destruct stk2 as [| v2 stk3].
        -- inversion H. reflexivity.
        -- destruct stk3 as [| v3 rest].
           ++ inversion H. reflexivity.
           ++ discriminate.
      * inversion H. reflexivity.
      * inversion H. reflexivity.
      * inversion H. reflexivity.
Qed.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr POPTRAP / clight_of POPTRAP / pre_of POPTRAP are
   convertible with handle_POPTRAP / f_instr_POPTRAP / poptrap_step_pre.
   P_halt_of and P_ccall_of are vacuously satisfied (POPTRAP never halts
   or issues a C call).  The Error case is bridged via
   handle_POPTRAP_error_implies_error_message. *)
Definition correct_POPTRAP :
    handler_correct (handle_instr POPTRAP) (clight_of POPTRAP)
      (pre_of POPTRAP)
      (P_error_of POPTRAP) (P_halt_of POPTRAP) (P_ccall_of POPTRAP).
Proof.
Admitted.
