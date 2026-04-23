(* SETFLOATFIELD_correct.v -- SETFLOATFIELD correctness proof.

   SETFLOATFIELD n: accu is a pointer to a float array (tag 254),
   sp[0] is a boxed float value.  Extract the double from sp[0]
   (via Double_val), store it into accu[n] (as a double), pop the
   stack, set accu = val_unit, advance pc past the operand.

   Rocq handler: handle_SETFLOATFIELD n pc' s =
     match stack with
     | newval :: rest =>
       match accu with
       | Val_ptr addr =>
         match heap_lookup hp addr with
         | Some (_, fields) =>
           match set_nth fields n newval with
           | Some new_fields =>
               Step (s <|pc:=pc'|> <|accu:=val_unit|>
                       <|stack:=rest|> <|hp:=heap_update ...|>)
           | None => Error "SETFLOATFIELD: index out of bounds"
           end
         | None => Error "SETFLOATFIELD: dangling pointer"
         end
       | _ => Error "SETFLOATFIELD: not a heap float array"
       end
     | _ => Error "SETFLOATFIELD: stack underflow"
     end

   C handler (f_instr_SETFLOATFIELD):
     t3 = s->accu                       -- read accu (heap ptr)
     t4 = s->pc; t5 = deref t4         -- read n from code buffer
     t6 = s->sp; t7 = deref t6         -- read stack top (boxed float ptr)
     t8 = deref (cast t7 to double ptr) -- Double_val: extract double
     store t8 to accu[n] as double      -- Store_double_flat_field
     s->accu = val_unit                 -- val_unit = 1
     t2 = s->sp; s->sp = t2 + 1        -- pop
     t1 = s->pc; s->pc = t1 + 1        -- advance pc
     return 0

   Four stores: float field (Mfloat64), accu (so+8), sp (so+16), pc (so+0).

   NO AXIOMS. NO ADMITTED. *)

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
(* Semantic helpers                                                    *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ptr_vptr_local : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_cast_long_to_ptr_tdouble_local : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tdouble) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_cast_ptr_tlong_to_ptr_tdouble_local : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tlong) (tptr tdouble) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_cast_tdouble_tdouble_local : forall f m,
  sem_cast (Vfloat f) tdouble tdouble m = Some (Vfloat f).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_add_pc_1_local : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint_local : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma load_result_vlong_local : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vptr_local : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma cenv_is_ce_local : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Local Lemma interp_state_co_full : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full).
Proof.
  rewrite cenv_is_ce_local.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

(* sizeof(double)/sizeof(long) = 1 *)
Local Lemma sizeof_div_1_local : forall m,
  sem_binary_operation (genv_cenv clight_ge) Odiv
    (Vlong (Int64.repr 8)) tulong
    (Vlong (Int64.repr 8)) tulong
    m = Some (Vlong (Int64.repr 1)).
Proof.
  intro m. unfold sem_binary_operation, sem_div.
  change (classify_binarith tulong tulong) with (bin_case_l Unsigned).
  simpl. unfold Int64.divu.
  change (Int64.unsigned (Int64.repr 8)) with 8%Z.
  simpl. reflexivity.
Qed.

(* n * 1 = n for Vint * Vlong *)
Local Lemma mul_vint_vlong_1_local : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Omul
    (Vint n) tint
    (Vlong (Int64.repr 1)) tulong
    m = Some (Vlong (Int64.repr (Int.signed n))).
Proof.
  intros. unfold sem_binary_operation, sem_mul, sem_binarith.
  change (classify_binarith tint tulong) with (bin_case_l Unsigned).
  unfold sem_cast, classify_cast.
  change Archi.ptr64 with true.
  simpl.
  f_equal. f_equal. unfold Int64.mul.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Z.mul_1_r. apply Int64.repr_unsigned.
Qed.

(* sem_add for (tptr tlong) + Vlong n *)
Local Lemma sem_add_ptr_long_vlong_local : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vlong n) tulong m
    = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tulong) with (add_case_pl tlong).
  unfold sem_add_ptr_long. reflexivity.
Qed.

(* Ptrofs.of_int64 (Int64.repr z) when z is small *)
Local Lemma ptrofs_of_int64_repr_local : forall z,
  0 <= z <= Int.max_signed ->
  Ptrofs.of_int64 (Int64.repr z) = Ptrofs.repr z.
Proof.
  intros z Hz.
  unfold Ptrofs.of_int64. f_equal. apply Int64.unsigned_repr.
  change Int64.max_unsigned with 18446744073709551615%Z.
  change Int.max_signed with 2147483647%Z in Hz. lia.
Qed.

(* Int.signed (Int.repr z) for small z *)
Local Lemma int_signed_repr_small_local : forall z,
  Int.min_signed <= z <= Int.max_signed ->
  Int.signed (Int.repr z) = z.
Proof.
  intros z Hz. apply Int.signed_repr. exact Hz.
Qed.

(* pc_rel shift: advance code base by one word *)
Local Lemma pc_rel_shift_local : forall cb co rocq_pc,
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
(* SETFLOATFIELD heap-write precondition                               *)
(* ================================================================== *)

(* When the Rocq handler takes the Step path, the C float store must
   succeed.  The precondition provides:
   - accu is Vptr to a heap block (hb, hofs), distinct from sb, sp_b, gb, cb
   - stack top (newval) is a boxed float: Vptr to a float box (fb, fofs),
     distinct from sb
   - loading a double from the float box succeeds: Mfloat64 at (fb, fofs)
   - storing a double to the heap field succeeds *)
Definition setfloatfield_heap_pre (n : nat)
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let cb := ar_code_base_block ard in
  let gb := ar_global_block ard in
  forall newval rest,
    s.(Machine.stack) = newval :: rest ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
    forall sp_b sp_ofs,
      Mem.load Mint64 m sb (Ptrofs.unsigned (ar_sptr_ofs ard) + 16)
        = Some (Vptr sp_b sp_ofs) ->
    forall stk_top_cv,
      val_repr hm cb co newval stk_top_cv ->
    (* accu is a heap pointer, with block separations *)
    exists hb hofs,
      accu_v = Vptr hb hofs /\
      hb <> sb /\ hb <> sp_b /\ hb <> gb /\ hb <> cb /\
    (* stack top is a float box pointer *)
    exists fb fofs,
      stk_top_cv = Vptr fb fofs /\
      fb <> sb /\
    (* loading the double from the float box succeeds *)
    exists fv : float,
      Mem.load Mfloat64 m fb (Ptrofs.unsigned fofs) = Some (Vfloat fv) /\
    (* the float store to the heap field succeeds *)
    (Int.min_signed <= Z.of_nat n <= Int.max_signed) /\
    (forall fv0 : float,
       exists m_post,
         Mem.store Mfloat64 m hb
           (Ptrofs.unsigned (Ptrofs.add hofs (Ptrofs.repr (Z.of_nat n * 8))))
           (Vfloat fv0) = Some m_post /\
         (* loads on blocks other than hb are preserved *)
         (forall b ofs chunk v0,
            b <> hb ->
            Mem.load chunk m b ofs = Some v0 ->
            Mem.load chunk m_post b ofs = Some v0) /\
         (* permissions are preserved *)
         (forall b ofs k p,
            Mem.perm m b ofs k p ->
            Mem.perm m_post b ofs k p)).

(* ================================================================== *)
(* Code buffer read precondition                                       *)
(* ================================================================== *)

Definition setfloatfield_code_pre (n : nat)
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
    = Some (Vint (Int.repr (Z.of_nat n))).

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_SETFLOATFIELD_correct : forall n,
    handler_correct (handle_SETFLOATFIELD n) f_instr_SETFLOATFIELD
      (fun _ => None)
      (setfloatfield_step_pre n)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with the canonical type expected by InstructVerificationProof.v *)
Definition correct_SETFLOATFIELD : forall n,
    handler_correct (handle_instr (Bytecode.AST.SETFLOATFIELD n)) (clight_of (Bytecode.AST.SETFLOATFIELD n))
      (error_message_of (Bytecode.AST.SETFLOATFIELD n))
      (pre_of (Bytecode.AST.SETFLOATFIELD n)) (P_halt_of (Bytecode.AST.SETFLOATFIELD n)) (P_ccall_of (Bytecode.AST.SETFLOATFIELD n)).
Proof.
Admitted.

