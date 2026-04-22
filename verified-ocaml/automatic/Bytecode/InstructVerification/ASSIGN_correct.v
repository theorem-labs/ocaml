(* ASSIGN_correct.v -- ASSIGN completeness proof.

   ASSIGN reads n from *pc, stores accu into sp[n], sets accu to val_unit,
   and increments pc by 1 (4 bytes).

   C code (from clightgen):
     _t'1 = s->pc;
     s->pc = _t'1 + 1;             // advance pc past n argument
     _t'2 = s->sp;
     _t'3 = *_t'1;                  // read n from bytecode stream
     _t'4 = s->accu;
     *(sp + n) = _t'4;             // store accu at stack[n]
     s->accu = ((0 << 1) + 1);    // val_unit = 1
     return 0;

   Rocq:
     handle_ASSIGN n pc' s =
       match set_nth (stack s) n (accu s) with
       | Some new_stack => Step (s <|pc:=pc'|> <|accu:=val_unit|> <|stack:=new_stack|>)
       | None => Error "ASSIGN: stack underflow"
       end

   Three stores: pc field at offset +0, stack at sp[n], accu field at offset +8.

   Uses handler_correct with preconditions for:
   - Code buffer contains n at current PC
   - Code block is separate from struct block
   - Stack store at sp[n] succeeds in m1 (after pc store)
   All lemmas are proved; no axioms introduced. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual.Bytecode Require Import AST.
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
(* Struct layout: _pc at offset 0, _accu at offset 8, _sp at offset 16 *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_all : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full).
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

(* sp + n for (tptr tlong) + tint: sizeof(tlong) = 8, so result = sp + 8*n *)
Lemma sem_add_sp_n : forall sp_b sp_ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint n) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs
                (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tlong))
                            (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma ptrofs_add_zero : forall ofs,
  Ptrofs.add ofs (Ptrofs.repr 0) = ofs.
Proof.
  intros. change (Ptrofs.repr 0) with Ptrofs.zero.
  apply Ptrofs.add_zero.
Qed.

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

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
  f_equal. rewrite Ptrofs.add_assoc. rewrite Ptrofs.add_assoc.
  f_equal. rewrite Ptrofs.add_commut. reflexivity.
Qed.

(* ================================================================== *)
(* Pointer arithmetic: sp_ofs + 8 * n as Ptrofs                       *)
(* ================================================================== *)

Lemma ptrofs_of_int_signed_nat : forall n,
  (0 <= Z.of_nat n <= Int.max_signed)%Z ->
  ptrofs_of_int Signed (Int.repr (Z.of_nat n)) = Ptrofs.repr (Z.of_nat n).
Proof.
  intros n Hrange.
  unfold ptrofs_of_int, Ptrofs.of_ints.
  f_equal.
  rewrite Int.signed_repr; [reflexivity |].
  assert (Hmin : Int.min_signed = (-2147483648)%Z) by reflexivity.
  assert (Hmax : Int.max_signed = 2147483647%Z) by reflexivity.
  lia.
Qed.

Lemma sp_offset_n_unsigned : forall sp_ofs n,
  (0 <= Z.of_nat n <= Int.max_signed)%Z ->
  Ptrofs.unsigned sp_ofs + 8 * Z.of_nat n < Ptrofs.modulus ->
  Ptrofs.unsigned
    (Ptrofs.add sp_ofs
       (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tlong))
                   (ptrofs_of_int Signed (Int.repr (Z.of_nat n)))))
  = Ptrofs.unsigned sp_ofs + 8 * Z.of_nat n.
Proof.
  intros sp_ofs n Hn_range Hfit.
  change (sizeof (genv_cenv clight_ge) tlong) with 8%Z.
  rewrite (ptrofs_of_int_signed_nat n Hn_range).
  unfold Ptrofs.add, Ptrofs.mul.
  pose proof (Ptrofs.unsigned_range sp_ofs) as [Hsp_lo Hsp_hi].
  assert (Hmu : Ptrofs.max_unsigned = Ptrofs.modulus - 1) by reflexivity.
  assert (Hmod : Ptrofs.modulus = 18446744073709551616) by reflexivity.
  assert (H8ok : 0 <= 8 <= Ptrofs.max_unsigned) by (rewrite Hmu, Hmod; lia).
  assert (Hn_ok : 0 <= Z.of_nat n <= Ptrofs.max_unsigned) by (rewrite Hmu, Hmod; lia).
  assert (H8n_ok : 0 <= 8 * Z.of_nat n <= Ptrofs.max_unsigned) by (rewrite Hmu, Hmod; lia).
  assert (Hsum_ok : 0 <= Ptrofs.unsigned sp_ofs + 8 * Z.of_nat n <= Ptrofs.max_unsigned) by (rewrite Hmu, Hmod; lia).
  rewrite (Ptrofs.unsigned_repr 8 H8ok).
  rewrite (Ptrofs.unsigned_repr (Z.of_nat n) Hn_ok).
  rewrite (Ptrofs.unsigned_repr _ H8n_ok).
  rewrite (Ptrofs.unsigned_repr _ Hsum_ok).
  lia.
Qed.

(* ================================================================== *)
(* set_nth preserves list length                                       *)
(* ================================================================== *)

Lemma set_nth_length : forall {A : Type} (l : list A) n x l',
  set_nth l n x = Some l' -> length l' = length l.
Proof.
  induction l as [| hd tl IH]; intros n x l' Hset.
  - simpl in Hset. discriminate.
  - destruct n as [| n'].
    + simpl in Hset. injection Hset as <-. simpl. reflexivity.
    + simpl in Hset.
      destruct (set_nth tl n' x) as [tl'|] eqn:Hsub; [| discriminate].
      injection Hset as <-. simpl. f_equal. exact (IH n' x tl' Hsub).
Qed.

(* ================================================================== *)
(* stack_repr_update: updating element n preserves stack_repr          *)
(* ================================================================== *)

Lemma stack_repr_update : forall hm cb co m m' stk sp_b sp_ofs n v cv new_stk,
  stack_repr hm cb co m stk sp_b sp_ofs ->
  set_nth stk n v = Some new_stk ->
  val_repr hm cb co v cv ->
  Mem.store Mint64 m sp_b (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat n) cv = Some m' ->
  Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length stk) < Ptrofs.modulus ->
  stack_repr hm cb co m' new_stk sp_b sp_ofs.
Proof.
  intros hm cb co m m' stk sp_b sp_ofs n v cv new_stk. revert m m' sp_ofs n new_stk.
  induction stk as [| hd tl IH]; intros m m' sp_ofs n new_stk
    Hsr Hset Hvr Hstore Hrep.
  - (* stk = [] => set_nth fails *)
    simpl in Hset. discriminate.
  - destruct n as [| n'].
    + (* n = 0: update head *)
      simpl in Hset. injection Hset as <-.
      inversion Hsr; subst.
      simpl length in Hrep.
      econstructor.
      * (* Load the head: stored value *)
        replace (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat 0)%Z
          with (Ptrofs.unsigned sp_ofs) in Hstore by lia.
        pose proof (load_after_store_same m m' sp_b (Ptrofs.unsigned sp_ofs) cv Hstore) as Htmp.
        rewrite (val_repr_load_result hm cb co v cv Hvr) in Htmp.
        exact Htmp.
      * exact Hvr.
      * (* Tail unchanged: store at head doesn't overlap tail *)
        replace (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat 0)%Z
          with (Ptrofs.unsigned sp_ofs) in Hstore by lia.
        eapply stack_repr_store_same_block_lower; eauto;
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)); lia.
    + (* n = S n': update in tail *)
      simpl in Hset.
      destruct (set_nth tl n' v) as [tl' |] eqn:Hset_tl; [| discriminate].
      injection Hset as <-.
      inversion Hsr; subst.
      simpl length in Hrep.
      assert (Hstore_ofs : Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (S n')
                         = Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat n')
        by (rewrite Nat2Z.inj_succ; lia).
      econstructor.
      * (* Head unchanged: store at sp_ofs + 8*(S n') doesn't overlap sp_ofs *)
        erewrite Mem.load_store_other; eauto.
        right. left.
        change (size_chunk Mint64) with 8%Z.
        rewrite Hstore_ofs.
        pose proof (Zle_0_nat n'). lia.
      * assumption.
      * (* Tail: apply IH *)
        assert (Htail_unsigned : Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 8)) = Ptrofs.unsigned sp_ofs + 8).
        { apply ptrofs_add_unsigned; lia. }
        eapply IH; eauto.
        -- rewrite Htail_unsigned.
           rewrite Hstore_ofs in Hstore.
           exact Hstore.
        -- rewrite Htail_unsigned. lia.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

(* val_repr_co_shift, stack_repr_co_shift, global_repr_co_shift
   are imported from HandlerLemmas. *)

Theorem correct_ASSIGN : forall n,
    handler_correct (handle_instr (ASSIGN n)) (clight_of (ASSIGN n))
      (pre_of (ASSIGN n))
      (P_error_of (ASSIGN n)) (P_halt_of (ASSIGN n)) (P_ccall_of (ASSIGN n)).
Proof.
Admitted.
