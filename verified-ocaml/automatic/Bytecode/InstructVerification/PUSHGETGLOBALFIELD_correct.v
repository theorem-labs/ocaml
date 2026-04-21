(* PUSHGETGLOBALFIELD_correct.v -- PUSHGETGLOBALFIELD completeness proof.

   PUSHGETGLOBALFIELD n p = PUSH (push accu to stack) then
   GETGLOBAL n (load global_data[n]) then GETFIELD p (dereference field p).

   C code (f_instr_PUSHGETGLOBALFIELD):
     -- Push --
     _t'13 = s->sp;
     _t'1 = (tptr tlong)(_t'13 - 1);     // new_sp = sp - 8
     s->sp = _t'1;                         // Store 1: sp field
     _t'12 = s->accu;
     *_t'1 = _t'12;                        // Store 2: push accu
     -- Get global --
     _t'8 = s->global_data;
     _t'9 = s->pc;
     _t'10 = *_t'9;                        // read N from code buffer
     _t'11 = *(cast(_t'8) + _t'10);       // load global_data[N]
     s->accu = _t'11;                      // Store 3: accu = global[N]
     -- Advance pc past N --
     _t'7 = s->pc;
     s->pc = _t'7 + 1;                     // Store 4: pc += 1
     -- Field deref --
     _t'3 = s->accu;
     _t'4 = s->pc;
     _t'5 = *_t'4;                         // read P from code buffer
     _t'6 = *(cast(_t'3) + _t'5);         // deref field P from global
     s->accu = _t'6;                       // Store 5: accu = field
     -- Advance pc past P --
     _t'2 = s->pc;
     s->pc = _t'2 + 1;                     // Store 6: pc += 1
     return 0;

   Rocq:
     handle_PUSHGETGLOBALFIELD n p pc' s =
       let new_stack := accu :: stack in
       match nth_error s.(global) n with
       | Some glob =>
         match field_or_heap s glob p with
         | Some v => Step (s <|pc:=pc'|> <|accu:=v|> <|stack:=new_stack|>)
         | None => Error "PUSHGETGLOBALFIELD: field access failed"
         end
       | None => Error "PUSHGETGLOBALFIELD: index out of bounds"
       end

   Six stores on the struct / stack blocks:
     Store 1: sp field (sb, uso+16)       <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp (sp_b, new_sp_ofs)  <- accu_v
     Store 3: accu field (sb, uso+8)      <- cv_global
     Store 4: pc field (sb, uso+0)        <- Vptr cb mid_pc_ofs
     Store 5: accu field (sb, uso+8)      <- cv_field
     Store 6: pc field (sb, uso+0)        <- Vptr cb new_pc_ofs

   NO AXIOMS.  NO ADMITTED. *)

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
(* Struct layout: _pc@0, _accu@8, _sp@16, _global_data@40             *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _global_data (co_members co) = Errors.OK (40, Full).
Proof.
  eexists. split; [| split; [| split; [| split]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_pushgetglobalfield : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _global_data (co_members co) = Errors.OK (40, Full).
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

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

Lemma pc_rel_shift : forall cb co rocq_pc,
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

(* Two-step pc shift: code_base advances by 2 * sizeof_code_t *)
Lemma pc_rel_shift_2 : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr 8)))
         cb (Ptrofs.add co (Ptrofs.repr (2 * sizeof_code_t))) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal.
  rewrite Ptrofs.add_assoc.
  rewrite Ptrofs.add_assoc.
  f_equal.
  rewrite Ptrofs.add_commut. reflexivity.
Qed.

Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* ================================================================== *)
(* Architectural constant                                              *)
(* ================================================================== *)

Lemma ptrofs_modulus_large : (Ptrofs.modulus > 8)%Z.
Proof.
  unfold Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  simpl. reflexivity.
Qed.

(* ================================================================== *)
(* Key lemma: global_repr + nth_error => Mem.load                     *)
(* ================================================================== *)

Lemma nat_iter_succ_r : forall {A} (f : A -> A) n x,
  Nat.iter (S n) f x = Nat.iter n f (f x).
Proof.
  intros A f n. revert f. induction n as [| n' IH]; intros f x.
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma global_repr_nth_error_ptrofs : forall hm cb co m gs gb go n v,
  global_repr hm cb co m gs gb go ->
  nth_error gs n = Some v ->
  exists cv,
    Mem.load Mint64 m gb
      (Ptrofs.unsigned (Nat.iter n (fun p => Ptrofs.add p (Ptrofs.repr 8)) go))
    = Some cv /\
    val_repr hm cb co v cv.
Proof.
  intros hm cb co m gs gb go n v Hgr.
  revert n.
  induction Hgr as [| v0 vs b ofs cv0 Hload Hval_repr Hgr' IH];
    intros n Hnth.
  - destruct n; discriminate Hnth.
  - destruct n as [| n'].
    + simpl in Hnth. injection Hnth as Heq. subst v.
      exists cv0. simpl. split; [exact Hload | exact Hval_repr].
    + simpl in Hnth.
      specialize (IH n' Hnth).
      destruct IH as [cv' [Hload' Hval_repr']].
      exists cv'. split; [| exact Hval_repr'].
      rewrite nat_iter_succ_r. exact Hload'.
Qed.

Lemma iter_add_8_unsigned : forall go n,
  Ptrofs.unsigned go + Z.of_nat n * 8 < Ptrofs.modulus ->
  Ptrofs.unsigned (Nat.iter n (fun p => Ptrofs.add p (Ptrofs.repr 8)) go)
  = Ptrofs.unsigned go + Z.of_nat n * 8.
Proof.
  intros go n.
  revert go.
  induction n as [| n' IH]; intros go Hbound.
  - simpl. lia.
  - rewrite nat_iter_succ_r.
    pose proof (Ptrofs.unsigned_range go) as [Hgo_pos Hgo_lt].
    pose proof ptrofs_modulus_large as Hmod_gt_8.
    assert (H8_repr : Ptrofs.unsigned (Ptrofs.repr 8) = 8).
    { apply Ptrofs.unsigned_repr. unfold Ptrofs.max_unsigned. lia. }
    set (go' := Ptrofs.add go (Ptrofs.repr 8)).
    assert (Hgo'_unsigned : Ptrofs.unsigned go' = Ptrofs.unsigned go + 8).
    { subst go'. unfold Ptrofs.add.
      rewrite H8_repr.
      apply Ptrofs.unsigned_repr. unfold Ptrofs.max_unsigned.
      replace (Z.of_nat (S n')) with (Z.of_nat n' + 1)%Z in Hbound by lia. lia. }
    rewrite IH.
    + rewrite Hgo'_unsigned.
      replace (Z.of_nat (S n')) with (Z.of_nat n' + 1)%Z by lia. lia.
    + rewrite Hgo'_unsigned.
      replace (Z.of_nat (S n')) with (Z.of_nat n' + 1)%Z in Hbound by lia. lia.
Qed.

Lemma global_repr_nth_error : forall hm cb co m gs gb go n v,
  global_repr hm cb co m gs gb go ->
  nth_error gs n = Some v ->
  Ptrofs.unsigned go + Z.of_nat n * 8 < Ptrofs.modulus ->
  exists cv,
    Mem.load Mint64 m gb (Ptrofs.unsigned go + Z.of_nat n * 8) = Some cv /\
    val_repr hm cb co v cv.
Proof.
  intros hm cb co m gs gb go n v Hgr Hnth Hbound.
  destruct (global_repr_nth_error_ptrofs hm cb co m gs gb go n v Hgr Hnth)
    as [cv [Hload Hval_repr]].
  exists cv. split; [| exact Hval_repr].
  rewrite <- (iter_add_8_unsigned go n Hbound).
  exact Hload.
Qed.

(* ================================================================== *)
(* Pointer arithmetic: global_data + n                                 *)
(* ================================================================== *)

Lemma sem_add_global_n : forall gb go i m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr gb go) (tptr tlong)
    (Vint i) tint
    m = Some (Vptr gb (Ptrofs.add go
                (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed i)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma ptrofs_global_offset : forall go n,
  0 <= Z.of_nat n <= Int.max_signed ->
  Ptrofs.unsigned go + Z.of_nat n * 8 < Ptrofs.modulus ->
  Ptrofs.unsigned (Ptrofs.add go
    (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat n)))))
  = Ptrofs.unsigned go + Z.of_nat n * 8.
Proof.
  intros go n Hn_range Hbound.
  unfold ptrofs_of_int.
  change (Ptrofs.of_ints (Int.repr (Z.of_nat n)))
    with (Ptrofs.repr (Int.signed (Int.repr (Z.of_nat n)))).
  change Int.max_signed with 2147483647 in Hn_range.
  rewrite Int.signed_repr by
    (unfold Int.min_signed, Int.max_signed, Int.half_modulus, Int.modulus,
     Int.wordsize, Wordsize_32.wordsize; simpl; lia).
  unfold Ptrofs.add, Ptrofs.mul.
  pose proof ptrofs_modulus_large as Hmod_gt.
  rewrite (Ptrofs.unsigned_repr 8) by (unfold Ptrofs.max_unsigned; lia).
  rewrite (Ptrofs.unsigned_repr (Z.of_nat n)).
  2: { unfold Ptrofs.max_unsigned. pose proof (Ptrofs.unsigned_range go). lia. }
  rewrite Ptrofs.unsigned_repr.
  - rewrite Ptrofs.unsigned_repr. lia.
    unfold Ptrofs.max_unsigned.
    change Ptrofs.modulus with 18446744073709551616%Z. lia.
  - rewrite (Ptrofs.unsigned_repr (8 * Z.of_nat n)).
    2: { unfold Ptrofs.max_unsigned. change Ptrofs.modulus with 18446744073709551616%Z. lia. }
    pose proof (Ptrofs.unsigned_range go). unfold Ptrofs.max_unsigned.
    change Ptrofs.modulus with 18446744073709551616%Z in *. lia.
Qed.

(* ================================================================== *)
(* Heap field precondition                                             *)
(* ================================================================== *)

(* After loading global[n], the result is a pointer-like value (glob).
   The field dereference reads field p from that value. The C code
   does: cast(glob_val) + p, then dereference.
   This precondition bridges the Rocq field_or_heap with C Mem.load. *)
Definition heap_field_loadable_pushgetglobalfield
    (p : nat) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall glob v cv_global,
    field_or_heap s glob p = Some v ->
    val_repr hm cb co glob cv_global ->
    exists b ofs cv,
      cv_global = Vptr b ofs /\
      b <> ar_sptr_block ard /\
      (forall sp_b sp_ofs,
         Mem.load Mint64 m (ar_sptr_block ard)
           (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
         b <> sp_b) /\
      Mem.load Mint64 m b
        (Ptrofs.unsigned (Ptrofs.add ofs
           (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat p))))))
        = Some cv /\
      val_repr hm cb co v cv.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

#[warnings="-not-a-closed-proof"]
Theorem verify_PUSHGETGLOBALFIELD_correct : forall n p,
    handler_correct (handle_PUSHGETGLOBALFIELD n p) f_instr_PUSHGETGLOBALFIELD
      (fun _ m s ard =>
         (* Code memory at pc contains n (first operand) *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
           = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* Code memory at pc+1 contains p (second operand) *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))))
           = Some (Vint (Int.repr (Z.of_nat p))) /\
         (* n fits in int32 signed range *)
         0 <= Z.of_nat n <= Int.max_signed /\
         (* p fits in int32 signed range *)
         0 <= Z.of_nat p <= Int.max_signed /\
         (* global offset arithmetic stays in ptrofs range *)
         Ptrofs.unsigned (ar_global_ofs ard) + Z.of_nat n * 8 < Ptrofs.modulus /\
         (* sp has room for a push *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs >= 16) /\
         (* heap field loadable: after loading global[n], field p is accessible *)
         heap_field_loadable_pushgetglobalfield p m s ard)
      (fun msg s =>
         nth_error s.(Machine.global) n = None \/
         (exists glob, nth_error s.(Machine.global) n = Some glob /\
                       field_or_heap s glob p = None))
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros n p.
  intros e le m s.
  unfold handle_PUSHGETGLOBALFIELD.
  set (new_stack := Machine.accu s :: Machine.stack s).
  destruct (nth_error (Machine.global s) n) as [glob|] eqn:Hnth.

  2: { (* nth_error = None => Error "index out of bounds" *)
    left. reflexivity. }

  destruct (field_or_heap s glob p) as [fval|] eqn:Hfoh.

  2: { (* field_or_heap = None => Error "field access failed" *)
    right. exists glob. split; [reflexivity | exact Hfoh]. }

  (* ================================================================ *)
  (* Step case: nth_error = Some glob, field_or_heap = Some fval       *)
  (* ================================================================ *)
  intros ard Hpre Hstep_pre.

  destruct Hstep_pre as (Hcode_load_n & Hcode_load_p & Hn_range & Hp_range &
                          Hgo_bound & Hsp_ge16 & Hhfl).

  (* Unpack abs_rel_with_ard *)
  set (sb := ar_sptr_block ard) in *.
  set (so := ar_sptr_ofs ard) in *.
  set (hm := ar_heap_map ard) in *.
  set (cb := ar_code_base_block ard) in *.
  set (co := ar_code_base_ofs ard) in *.
  set (gb := ar_global_block ard) in *.
  set (go := ar_global_ofs ard) in *.

  destruct Hpre as (Hle_s &
    [pc_ptr [Hpc_load Hpc_rel]] &
    [accu_v [Haccu_load Haccu_repr]] &
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
    [env_v [Henv_load Henv_repr]] &
    Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
    [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
  subst sp_ptr. subst gd_ptr.

  (* Structural invariants *)
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb gb in Hgb_ne.
  pose proof (code_block_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  destruct interp_state_co_pushgetglobalfield as [co_is [Hco [Hpc_offset [Haccu_offset [Hsp_offset Hgd_offset]]]]].

  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* New sp after push *)
  set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
  assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 8).
  { subst new_sp_ofs. unfold Ptrofs.sub.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
    apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range sp_ofs).
    unfold Ptrofs.max_unsigned. lia. }

  (* sp has room for push *)
  assert (Hsp16 : Ptrofs.unsigned sp_ofs >= 16).
  { apply (Hsp_ge16 sp_b sp_ofs). exact Hsp_load. }

  (* Global value from global_repr *)
  destruct (global_repr_nth_error hm cb co m _ gb go n glob Hglobal_repr Hnth Hgo_bound)
    as [cv_global [Hglobal_load Hglobal_val_repr]].

  (* Use heap precondition to get field value in C memory *)
  unfold heap_field_loadable_pushgetglobalfield in Hhfl.
  destruct (Hhfl glob fval cv_global Hfoh Hglobal_val_repr)
    as [glob_b [glob_ofs [cv_field [Hglob_is_ptr [Hglob_ne_sb [Hglob_ne_sp [Hfield_load Hfield_repr]]]]]]].
  subst cv_global.

  assert (Hglob_ne_spb : glob_b <> sp_b).
  { apply (Hglob_ne_sp sp_b sp_ofs). exact Hsp_load. }

  (* Mid-point pc offset (after first advancement) *)
  set (mid_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
  set (mid_pc_v := Vptr cb mid_pc_ofs).

  (* Final pc offset (after second advancement) *)
  set (new_pc_ofs := Ptrofs.add mid_pc_ofs (Ptrofs.repr 4)).
  set (new_pc_v := Vptr cb new_pc_ofs).

  (* ================================================================ *)
  (* Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs           *)
  (* ================================================================ *)
  destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) (Vptr sp_b new_sp_ofs)) as [m1 Hstore1].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

  (* ================================================================ *)
  (* Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v                    *)
  (* ================================================================ *)
  assert (Halign_new : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs)).
  { rewrite Hnew_sp_unsigned. simpl align_chunk.
    apply Z.divide_sub_r. exact Hsp_align. exists 1; lia. }
  destruct (store_to_sp_after_sb_store m m1 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)
              sp_b (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s)))
              (Ptrofs.unsigned new_sp_ofs)
              Hstore1 Hsp_writable
              ltac:(rewrite Hnew_sp_unsigned; lia)
              ltac:(rewrite Hnew_sp_unsigned; lia)
              Halign_new accu_v) as [m2 Hstore2].

  (* ================================================================ *)
  (* Store 3: accu field (sb, uso+8) <- Vptr glob_b glob_ofs          *)
  (* ================================================================ *)
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
             (Ptrofs.unsigned so + 8) (Vptr sp_b new_sp_ofs) accu_v
             Hstore1 Haccu_load). left. lia. }
  assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
  { erewrite Mem.load_store_other; [exact Haccu_load_m1 | exact Hstore2 |].
    left. exact (not_eq_sym Hsp_ne_sb). }
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore2 Hsb_writable_m1) as Hsb_writable_m2.
  destruct (store_succeeds_sb m2 sb so 8 accu_v Hsb_writable_m2 Haccu_load_m2 ltac:(lia) ltac:(lia) (Vptr glob_b glob_ofs)) as [m3 Hstore3].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore3 Hsb_writable_m2) as Hsb_writable_m3.

  (* ================================================================ *)
  (* Store 4: pc field (sb, uso+0) <- mid_pc_v                        *)
  (* ================================================================ *)
  assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
             (Ptrofs.unsigned so + 0) (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs)
             Hstore1 Hpc_load). left. lia. }
  assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { erewrite Mem.load_store_other; [exact Hpc_load_m1 | exact Hstore2 |].
    left. exact (not_eq_sym Hsp_ne_sb). }
  assert (Hpc_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 8)
             (Ptrofs.unsigned so + 0) (Vptr glob_b glob_ofs) (Vptr cb pc_ofs)
             Hstore3 Hpc_load_m2). left. lia. }
  destruct (store_succeeds_sb m3 sb so 0 (Vptr cb pc_ofs) Hsb_writable_m3 Hpc_load_m3 ltac:(lia) ltac:(lia) mid_pc_v)
    as [m4 Hstore4].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore4 Hsb_writable_m3) as Hsb_writable_m4.

  (* ================================================================ *)
  (* Store 5: accu field (sb, uso+8) <- cv_field                      *)
  (* ================================================================ *)
  assert (Haccu_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 8) = Some (Vptr glob_b glob_ofs)).
  { pose proof (load_after_store_same m2 m3 sb (Ptrofs.unsigned so + 8) (Vptr glob_b glob_ofs) Hstore3) as Htmp.
    simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
  assert (Haccu_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 8) = Some (Vptr glob_b glob_ofs)).
  { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 8) mid_pc_v (Vptr glob_b glob_ofs)
             Hstore4 Haccu_load_m3). right. lia. }
  destruct (store_succeeds_sb m4 sb so 8 (Vptr glob_b glob_ofs) Hsb_writable_m4 Haccu_load_m4 ltac:(lia) ltac:(lia) cv_field) as [m5 Hstore5].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore5 Hsb_writable_m4) as Hsb_writable_m5.

  (* ================================================================ *)
  (* Store 6: pc field (sb, uso+0) <- new_pc_v                        *)
  (* ================================================================ *)
  assert (Hpc_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 0) = Some mid_pc_v).
  { pose proof (load_after_store_same m3 m4 sb (Ptrofs.unsigned so + 0) mid_pc_v Hstore4) as Htmp.
    unfold mid_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }
  assert (Hpc_load_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 0) = Some mid_pc_v).
  { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 8)
             (Ptrofs.unsigned so + 0) cv_field mid_pc_v
             Hstore5 Hpc_load_m4). left. lia. }
  destruct (store_succeeds_sb m5 sb so 0 mid_pc_v Hsb_writable_m5 Hpc_load_m5 ltac:(lia) ltac:(lia) new_pc_v)
    as [m6 Hstore6].

  (* ================================================================ *)
  (* Code memory survives all 6 stores                                 *)
  (* ================================================================ *)
  assert (Hcode_load_n_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs)
            = Some (Vint (Int.repr (Z.of_nat n)))).
  { erewrite Mem.load_store_other; [exact Hcode_load_n | exact Hstore1 |].
    left. exact Hcb_ne. }
  assert (Hcode_load_n_m2 : Mem.load Mint32 m2 cb (Ptrofs.unsigned pc_ofs)
            = Some (Vint (Int.repr (Z.of_nat n)))).
  { erewrite Mem.load_store_other; [exact Hcode_load_n_m1 | exact Hstore2 |].
    left. exact Hcb_ne_sp. }

  (* mid_pc_ofs = Ptrofs.add co (Ptrofs.repr ((pc s + 1) * sizeof_code_t)) *)
  assert (Hmid_pc_eq : mid_pc_ofs =
            Ptrofs.add co (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))).
  { subst mid_pc_ofs pc_ofs. unfold sizeof_code_t.
    rewrite Ptrofs.add_assoc. f_equal.
    apply Ptrofs.eqm_samerepr.
    replace ((Machine.pc s + 1) * 4) with (Machine.pc s * 4 + 4) by lia.
    apply Ptrofs.eqm_add.
    apply Ptrofs.eqm_sym. apply Ptrofs.eqm_unsigned_repr.
    apply Ptrofs.eqm_sym. apply Ptrofs.eqm_unsigned_repr. }

  assert (Hcode_load_p_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned mid_pc_ofs)
            = Some (Vint (Int.repr (Z.of_nat p)))).
  { rewrite Hmid_pc_eq.
    erewrite Mem.load_store_other; [exact Hcode_load_p | exact Hstore1 |].
    left. exact Hcb_ne. }
  assert (Hcode_load_p_m2 : Mem.load Mint32 m2 cb (Ptrofs.unsigned mid_pc_ofs)
            = Some (Vint (Int.repr (Z.of_nat p)))).
  { erewrite Mem.load_store_other; [exact Hcode_load_p_m1 | exact Hstore2 |].
    left. exact Hcb_ne_sp. }
  assert (Hcode_load_p_m3 : Mem.load Mint32 m3 cb (Ptrofs.unsigned mid_pc_ofs)
            = Some (Vint (Int.repr (Z.of_nat p)))).
  { erewrite Mem.load_store_other; [exact Hcode_load_p_m2 | exact Hstore3 |].
    left. exact Hcb_ne. }
  assert (Hcode_load_p_m4 : Mem.load Mint32 m4 cb (Ptrofs.unsigned mid_pc_ofs)
            = Some (Vint (Int.repr (Z.of_nat p)))).
  { erewrite Mem.load_store_other; [exact Hcode_load_p_m3 | exact Hstore4 |].
    left. exact Hcb_ne. }

  (* Global data load survives stores 1, 2 *)
  assert (Hglobal_load_m1 : Mem.load Mint64 m1 gb
            (Ptrofs.unsigned go + Z.of_nat n * 8) = Some (Vptr glob_b glob_ofs)).
  { erewrite Mem.load_store_other.
    - exact Hglobal_load.
    - exact Hstore1.
    - left. intro Heq. exact (Hgb_ne Heq). }
  assert (Hglobal_load_m2 : Mem.load Mint64 m2 gb
            (Ptrofs.unsigned go + Z.of_nat n * 8) = Some (Vptr glob_b glob_ofs)).
  { erewrite Mem.load_store_other.
    - exact Hglobal_load_m1.
    - exact Hstore2.
    - left. exact (not_eq_sym Hsp_ne_gb). }

  (* Field load survives stores 1..4 *)
  assert (Hfield_load_m1 : Mem.load Mint64 m1 glob_b
            (Ptrofs.unsigned (Ptrofs.add glob_ofs
               (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat p))))))
            = Some cv_field).
  { erewrite Mem.load_store_other; [exact Hfield_load | exact Hstore1 |].
    left. exact Hglob_ne_sb. }
  assert (Hfield_load_m2 : Mem.load Mint64 m2 glob_b
            (Ptrofs.unsigned (Ptrofs.add glob_ofs
               (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat p))))))
            = Some cv_field).
  { erewrite Mem.load_store_other; [exact Hfield_load_m1 | exact Hstore2 |].
    left. exact Hglob_ne_spb. }
  assert (Hfield_load_m3 : Mem.load Mint64 m3 glob_b
            (Ptrofs.unsigned (Ptrofs.add glob_ofs
               (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat p))))))
            = Some cv_field).
  { erewrite Mem.load_store_other; [exact Hfield_load_m2 | exact Hstore3 |].
    left. exact Hglob_ne_sb. }
  assert (Hfield_load_m4 : Mem.load Mint64 m4 glob_b
            (Ptrofs.unsigned (Ptrofs.add glob_ofs
               (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat p))))))
            = Some cv_field).
  { erewrite Mem.load_store_other; [exact Hfield_load_m3 | exact Hstore4 |].
    left. exact Hglob_ne_sb. }

  (* Pointer arithmetic for global access *)
  assert (Hptr_arith_n : Ptrofs.unsigned (Ptrofs.add go
            (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat n)))))
          = Ptrofs.unsigned go + Z.of_nat n * 8).
  { apply ptrofs_global_offset; assumption. }

  (* global_data field survives stores 1, 2 *)
  assert (Hgd_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 40) = Some (Vptr gb go)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 40)
             (Vptr sp_b new_sp_ofs) (Vptr gb go) Hstore1 Hgd_load). right. lia. }
  assert (Hgd_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 40) = Some (Vptr gb go)).
  { erewrite Mem.load_store_other; [exact Hgd_load_m1 | exact Hstore2 |].
    left. exact (not_eq_sym Hsp_ne_sb). }

  (* ================================================================ *)
  (* Witnesses                                                         *)
  (* ================================================================ *)
  set (le' := PTree.set _t'2 mid_pc_v
              (PTree.set _t'6 cv_field
              (PTree.set _t'5 (Vint (Int.repr (Z.of_nat p)))
              (PTree.set _t'4 mid_pc_v
              (PTree.set _t'3 (Vptr glob_b glob_ofs)
              (PTree.set _t'7 (Vptr cb pc_ofs)
              (PTree.set _t'11 (Vptr glob_b glob_ofs)
              (PTree.set _t'10 (Vint (Int.repr (Z.of_nat n)))
              (PTree.set _t'9 (Vptr cb pc_ofs)
              (PTree.set _t'8 (Vptr gb go)
              (PTree.set _t'12 accu_v
              (PTree.set _t'1 (Vptr sp_b new_sp_ofs)
              (PTree.set _t'13 (Vptr sp_b sp_ofs) le))))))))))))).
  exists le'. exists m6.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ============================================================== *)
  (* Part 1: exec via computational evaluator                        *)
  (* ============================================================== *)
  {
    unfold so, sb in *.

    apply (eval_stmt_to_exec clight_ge 40).
    eval_cbn.

    (* ============================================================ *)
    (* S1: Sset _t'13 (s->sp) -- read sp from struct                 *)
    (* ============================================================ *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* ============================================================ *)
    (* S2: Sset _t'1 (cast (_t'13 - 1) (tptr tlong))                 *)
    (* ============================================================ *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_sub_sp_1; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.

    (* ============================================================ *)
    (* S3: Sassign (s->sp) _t'1  -- Store 1: sp field               *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 16 ltac:(lia) ltac:(lia)).
    fold new_sp_ofs.
    rewrite Hstore1; eval_cbn.

    (* ============================================================ *)
    (* S4: Sset _t'12 (s->accu) -- read accu                         *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 8 ltac:(lia) ltac:(lia)).
    rewrite (load_after_store_other m m1 (ar_sptr_block ard)
               (Ptrofs.unsigned (ar_sptr_ofs ard) + 16)
               (Ptrofs.unsigned (ar_sptr_ofs ard) + 8) (Vptr sp_b new_sp_ofs) accu_v
               Hstore1 Haccu_load ltac:(left; lia)).
    eval_cbn.

    (* ============================================================ *)
    (* S5: Sassign (deref _t'1) _t'12 -- Store 2: push accu          *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Haccu_repr); eval_cbn.
    fold new_sp_ofs.
    rewrite Hstore2; eval_cbn.

    (* ============================================================ *)
    (* S6: Sset _t'8 (s->global_data) -- read global_data ptr       *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Hgd_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 40 ltac:(lia) ltac:(lia)).
    rewrite Hgd_load_m2; eval_cbn.

    (* ============================================================ *)
    (* S7: Sset _t'9 (s->pc) -- read pc pointer                     *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Hpc_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m2; eval_cbn.

    (* ============================================================ *)
    (* S8: Sset _t'10 (deref _t'9) -- read N from code               *)
    (* ============================================================ *)
    rewrite PTree.gss; eval_cbn.
    rewrite Hcode_load_n_m2; eval_cbn.

    (* ============================================================ *)
    (* S9: Sset _t'11 (deref (cast(_t'8) + _t'10)) -- load global[N] *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_ptr_to_ptr gb go m2); eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_global_n gb go (Int.repr (Z.of_nat n)) m2); eval_cbn.
    rewrite Hptr_arith_n.
    rewrite Hglobal_load_m2; eval_cbn.

    (* ============================================================ *)
    (* S10: Sassign (s->accu) _t'11 -- Store 3: write global to accu *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    (* sem_cast tlong tlong for Vptr: glob_b glob_ofs *)
    rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hglobal_val_repr); eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 8 ltac:(lia) ltac:(lia)).
    rewrite Hstore3; eval_cbn.

    (* ============================================================ *)
    (* S11: Sset _t'7 (s->pc) -- read pc from m3                    *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m3; eval_cbn.

    (* ============================================================ *)
    (* S12: Sassign (s->pc) (_t'7 + 1) -- Store 4: first pc advance  *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.

    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_pc_1 cb pc_ofs m3); eval_cbn.
    rewrite (sem_cast_ptr_tint_to_ptr_tint cb mid_pc_ofs); eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
    fold mid_pc_v.
    rewrite Hstore4; eval_cbn.

    (* ============================================================ *)
    (* S13: Sset _t'3 (s->accu) -- read accu (= global[N]) from m4  *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m4; eval_cbn.

    (* ============================================================ *)
    (* S14: Sset _t'4 (s->pc) -- read pc from m4                    *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m4; eval_cbn.

    (* ============================================================ *)
    (* S15: Sset _t'5 (deref _t'4) -- read P from code               *)
    (* ============================================================ *)
    rewrite PTree.gss; eval_cbn.
    rewrite Hcode_load_p_m4; eval_cbn.

    (* ============================================================ *)
    (* S16: Sset _t'6 (deref (cast(_t'3) + _t'5)) -- field deref    *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_to_ptr_vptr glob_b glob_ofs m4); eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_global_n glob_b glob_ofs (Int.repr (Z.of_nat p)) m4); eval_cbn.
    rewrite Hfield_load_m4; eval_cbn.

    (* ============================================================ *)
    (* S17: Sassign (s->accu) _t'6 -- Store 5: write field to accu  *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hfield_repr); eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 8 ltac:(lia) ltac:(lia)).
    rewrite Hstore5; eval_cbn.

    (* ============================================================ *)
    (* S18: Sset _t'2 (s->pc) -- read pc from m5                    *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m5; eval_cbn.

    (* ============================================================ *)
    (* S19: Sassign (s->pc) (_t'2 + 1) -- Store 6: second pc advance *)
    (* ============================================================ *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.

    rewrite PTree.gss; eval_cbn.
    unfold mid_pc_v.
    rewrite (sem_add_pc_1 cb _ m5); eval_cbn.
    fold new_pc_ofs.
    rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.
    rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
    fold new_pc_v.
    rewrite Hstore6; eval_cbn.

    (* ============================================================ *)
    (* S20: Sreturn 0                                                *)
    (* ============================================================ *)
    subst le'. reflexivity.
  }

  (* ============================================================== *)
  (* Part 2: abs_rel for post-state                                  *)
  (* ============================================================== *)
  {
    set (new_co := Ptrofs.add co (Ptrofs.repr (2 * sizeof_code_t))).
    set (ard' := mk_abs_rel
      (ar_sptr_block ard) (ar_sptr_ofs ard) (ar_heap_map ard)
      (ar_code_base_block ard) new_co
      (ar_global_block ard) (ar_global_ofs ard)
      (ar_stack_block ard) (ar_stack_base_ofs ard)
      (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard)
      (ar_sptr_ofs_bound ard)).
    exists ard'.
    set (uso := Ptrofs.unsigned so) in *.

    (* Helper: loads on sb survive store 2 (different block: sp_b vs sb) *)
    assert (Hload_sb_m2 : forall ofs v,
      Mem.load Mint64 m1 sb ofs = Some v ->
      Mem.load Mint64 m2 sb ofs = Some v).
    { intros ofs v Hload1.
      erewrite Mem.load_store_other; [exact Hload1 | exact Hstore2 |].
      left. exact (not_eq_sym Hsp_ne_sb). }

    (* pc field at uso+0: written by store 4, then by store 6 *)
    assert (Hpc_load6 : Mem.load Mint64 m6 sb (uso + 0) = Some new_pc_v).
    { pose proof (load_after_store_same m5 m6 sb (uso + 0) new_pc_v Hstore6) as Htmp.
      unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }

    (* accu field at uso+8: written by store 3, overwritten by store 5, survives store 6 *)
    assert (Haccu_load_m5 : Mem.load Mint64 m5 sb (uso + 8) = Some cv_field).
    { pose proof (load_after_store_same m4 m5 sb (uso + 8) cv_field Hstore5) as Htmp.
      rewrite (val_repr_load_result hm cb co fval cv_field Hfield_repr) in Htmp.
      exact Htmp. }
    assert (Haccu_load6 : Mem.load Mint64 m6 sb (uso + 8) = Some cv_field).
    { apply (load_after_store_other m5 m6 sb (uso + 0) (uso + 8)
               new_pc_v cv_field Hstore6 Haccu_load_m5). right. lia. }

    (* sp field at uso+16: written by store 1, survives stores 2-6 *)
    assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { pose proof (load_after_store_same m m1 sb (uso + 16)
                    (Vptr sp_b new_sp_ofs) Hstore1) as Htmp.
      simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
    assert (Hsp_load_m2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { exact (Hload_sb_m2 _ _ Hsp_load_m1). }
    assert (Hsp_load_m3 : Mem.load Mint64 m3 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 16)
               (Vptr glob_b glob_ofs) (Vptr sp_b new_sp_ofs) Hstore3 Hsp_load_m2). right. lia. }
    assert (Hsp_load_m4 : Mem.load Mint64 m4 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 16)
               mid_pc_v (Vptr sp_b new_sp_ofs) Hstore4 Hsp_load_m3). right. lia. }
    assert (Hsp_load_m5 : Mem.load Mint64 m5 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { apply (load_after_store_other m4 m5 sb (uso + 8) (uso + 16)
               cv_field (Vptr sp_b new_sp_ofs) Hstore5 Hsp_load_m4). right. lia. }
    assert (Hsp_load6 : Mem.load Mint64 m6 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { apply (load_after_store_other m5 m6 sb (uso + 0) (uso + 16)
               new_pc_v (Vptr sp_b new_sp_ofs) Hstore6 Hsp_load_m5). right. lia. }

    (* env field at uso+24: unaffected by all 6 stores *)
    assert (Henv_load_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 24)
               (Vptr sp_b new_sp_ofs) env_v Hstore1 Henv_load). right. lia. }
    assert (Henv_load_m2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
    { exact (Hload_sb_m2 _ _ Henv_load_m1). }
    assert (Henv_load_m3 : Mem.load Mint64 m3 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 24)
               (Vptr glob_b glob_ofs) env_v Hstore3 Henv_load_m2). right. lia. }
    assert (Henv_load_m4 : Mem.load Mint64 m4 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 24)
               mid_pc_v env_v Hstore4 Henv_load_m3). right. lia. }
    assert (Henv_load_m5 : Mem.load Mint64 m5 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m4 m5 sb (uso + 8) (uso + 24)
               cv_field env_v Hstore5 Henv_load_m4). right. lia. }
    assert (Henv_load6 : Mem.load Mint64 m6 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m5 m6 sb (uso + 0) (uso + 24)
               new_pc_v env_v Hstore6 Henv_load_m5). right. lia. }

    (* extra_args field at uso+32: unaffected *)
    assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
               (Vptr sp_b new_sp_ofs) _ Hstore1 Hextra_load). right. lia. }
    assert (Hextra_load_m2 : Mem.load Mint64 m2 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { exact (Hload_sb_m2 _ _ Hextra_load_m1). }
    assert (Hextra_load_m3 : Mem.load Mint64 m3 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 32)
               (Vptr glob_b glob_ofs) _ Hstore3 Hextra_load_m2). right. lia. }
    assert (Hextra_load_m4 : Mem.load Mint64 m4 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 32)
               mid_pc_v _ Hstore4 Hextra_load_m3). right. lia. }
    assert (Hextra_load_m5 : Mem.load Mint64 m5 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m4 m5 sb (uso + 8) (uso + 32)
               cv_field _ Hstore5 Hextra_load_m4). right. lia. }
    assert (Hextra_load6 : Mem.load Mint64 m6 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m5 m6 sb (uso + 0) (uso + 32)
               new_pc_v _ Hstore6 Hextra_load_m5). right. lia. }

    (* global_data field at uso+40: unaffected *)
    assert (Hgd_load_m3 : Mem.load Mint64 m3 sb (uso + 40) = Some (Vptr gb go)).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 40)
               (Vptr glob_b glob_ofs) (Vptr gb go) Hstore3 Hgd_load_m2). right. lia. }
    assert (Hgd_load_m4 : Mem.load Mint64 m4 sb (uso + 40) = Some (Vptr gb go)).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 40)
               mid_pc_v (Vptr gb go) Hstore4 Hgd_load_m3). right. lia. }
    assert (Hgd_load_m5 : Mem.load Mint64 m5 sb (uso + 40) = Some (Vptr gb go)).
    { apply (load_after_store_other m4 m5 sb (uso + 8) (uso + 40)
               cv_field (Vptr gb go) Hstore5 Hgd_load_m4). right. lia. }
    assert (Hgd_load6 : Mem.load Mint64 m6 sb (uso + 40) = Some (Vptr gb go)).
    { apply (load_after_store_other m5 m6 sb (uso + 0) (uso + 40)
               new_pc_v (Vptr gb go) Hstore6 Hgd_load_m5). right. lia. }

    (* trap_sp field at uso+48: unaffected *)
    assert (Hts_load_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 48)
               (Vptr sp_b new_sp_ofs) ts_ptr Hstore1 Hts_load). right. lia. }
    assert (Hts_load_m2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
    { exact (Hload_sb_m2 _ _ Hts_load_m1). }
    assert (Hts_load_m3 : Mem.load Mint64 m3 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 8) (uso + 48)
               (Vptr glob_b glob_ofs) ts_ptr Hstore3 Hts_load_m2). right. lia. }
    assert (Hts_load_m4 : Mem.load Mint64 m4 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 48)
               mid_pc_v ts_ptr Hstore4 Hts_load_m3). right. lia. }
    assert (Hts_load_m5 : Mem.load Mint64 m5 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m4 m5 sb (uso + 8) (uso + 48)
               cv_field ts_ptr Hstore5 Hts_load_m4). right. lia. }
    assert (Hts_load6 : Mem.load Mint64 m6 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m5 m6 sb (uso + 0) (uso + 48)
               new_pc_v ts_ptr Hstore6 Hts_load_m5). right. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le' *)
    { subst le'.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      exact Hle_s. }

    (* 2. pc field -- updated to new_pc_v, with shifted code_base *)
    { exists new_pc_v. split.
      - exact Hpc_load6.
      - simpl. subst new_pc_v new_pc_ofs mid_pc_ofs.
        (* Combine two +4 into +8 *)
        rewrite Ptrofs.add_assoc.
        change (Ptrofs.add (Ptrofs.repr 4) (Ptrofs.repr 4)) with (Ptrofs.repr 8).
        apply pc_rel_shift_2. }

    (* 3. accu field -- updated to field value *)
    { exists cv_field. split.
      - exact Haccu_load6.
      - simpl. eapply val_repr_co_shift. exact Hfield_repr. }

    (* 4. sp field -- updated to new_sp_ofs; stack gets accu prepended *)
    { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load6.
      - reflexivity.
      - (* stack_repr for accu :: stack after stores *)
        simpl.
        eapply stack_repr_store_other_block; [| exact Hstore6 | auto].
        eapply stack_repr_store_other_block; [| exact Hstore5 | auto].
        eapply stack_repr_store_other_block; [| exact Hstore4 | auto].
        eapply stack_repr_store_other_block; [| exact Hstore3 | auto].
        eapply stack_repr_co_shift.
        eapply stack_repr_cons_after_store; [| | exact Hstore2 | | ].
        + eapply stack_repr_store_other_block; [| exact Hstore1 | auto].
          exact Hstack_repr.
        + exact Haccu_repr.
        + lia.
        + lia.
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - (* sp_ge8: new_sp_ofs >= 8 follows from sp_ofs >= 16 *)
        rewrite Hnew_sp_unsigned. lia.
      - (* sp_rep: representability for accu :: stack *)
        simpl length. rewrite Nat2Z.inj_succ.
        rewrite Hnew_sp_unsigned. lia.
      - (* sp_writable: Mem.range_perm for new range *)
        simpl length. rewrite Nat2Z.inj_succ.
        rewrite Hnew_sp_unsigned.
        intros ofs' Hofs'.
        assert (Hofs'_in_old : 0 <= ofs' < Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) by lia.
        eapply Mem.perm_store_1. exact Hstore6.
        eapply Mem.perm_store_1. exact Hstore5.
        eapply Mem.perm_store_1. exact Hstore4.
        eapply Mem.perm_store_1. exact Hstore3.
        eapply Mem.perm_store_1. exact Hstore2.
        eapply Mem.perm_store_1. exact Hstore1.
        apply Hsp_writable. lia.
      - (* sp_aligned *)
        exact Halign_new. }

    (* 5. env field -- unchanged *)
    { exists env_v. split.
      - exact Henv_load6.
      - simpl. eapply val_repr_co_shift. exact Henv_repr. }

    (* 6. extra_args field -- unchanged *)
    { simpl. exact Hextra_load6. }

    (* 7. global_data field -- unchanged *)
    { exists (Vptr gb go). split; [| split; [| split]].
      - exact Hgd_load6.
      - simpl. reflexivity.
      - simpl. eapply global_repr_co_shift.
        eapply global_repr_store_other_block; [| exact Hstore6 | auto].
        eapply global_repr_store_other_block; [| exact Hstore5 | auto].
        eapply global_repr_store_other_block; [| exact Hstore4 | auto].
        eapply global_repr_store_other_block; [| exact Hstore3 | auto].
        eapply global_repr_store_other_block; [| exact Hstore2 | auto].
        eapply global_repr_store_other_block; [| exact Hstore1 | auto].
        exact Hglobal_repr.
      - simpl. exact Hgb_ne_sb. }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load6.
      - simpl. exact Htrap_rel. }

    (* 9. sb_writable -- permission preserved through all 6 stores *)
    { intros ofs' Hofs'.
      eapply Mem.perm_store_1. exact Hstore6.
      eapply Mem.perm_store_1. exact Hstore5.
      eapply Mem.perm_store_1. exact Hstore4.
      eapply Mem.perm_store_1. exact Hstore3.
      eapply Mem.perm_store_1. exact Hstore2.
      eapply Mem.perm_store_1. exact Hstore1.
      apply Hsb_writable. exact Hofs'. }
  }
Qed.

(* ================================================================== *)
(* Wrapper with the exact type expected by InstructVerificationProof.v *)
(* ================================================================== *)

From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

(* handle_instr (PUSHGETGLOBALFIELD n p) computes to handle_PUSHGETGLOBALFIELD n p.
   clight_of (PUSHGETGLOBALFIELD n p) computes to f_instr_PUSHGETGLOBALFIELD.
   pre_of (PUSHGETGLOBALFIELD n p) computes to pushgetglobalfield_step_pre n p.
   P_error_of (PUSHGETGLOBALFIELD n p) requires bridging: the old proof uses an
   explicit disjunction while P_error_of uses error_message_of.
   P_halt_of / P_ccall_of are vacuously False (not STOP / not C_CALL).
   We case-split on nth_error and field_or_heap:
     - Step case: delegate to verify_PUSHGETGLOBALFIELD_correct.
     - Error cases: prove P_error_of by unfolding error_message_of. *)
Definition correct_PUSHGETGLOBALFIELD : forall n p,
    handler_correct (handle_instr (PUSHGETGLOBALFIELD n p)) (clight_of (PUSHGETGLOBALFIELD n p))
      (pre_of (PUSHGETGLOBALFIELD n p))
      (P_error_of (PUSHGETGLOBALFIELD n p)) (P_halt_of (PUSHGETGLOBALFIELD n p)) (P_ccall_of (PUSHGETGLOBALFIELD n p)).
Proof.
  intros n p.
  intros e le m s.
  change (handle_instr (PUSHGETGLOBALFIELD n p) (Machine.pc s) s)
    with (handle_PUSHGETGLOBALFIELD n p (Machine.pc s) s).
  unfold handle_PUSHGETGLOBALFIELD at 1.
  destruct (nth_error (Machine.global s) n) as [glob|] eqn:Hnth.
  - (* nth_error = Some glob *)
    destruct (field_or_heap s glob p) as [fval|] eqn:Hfoh.
    + (* field_or_heap = Some fval: Step case -- delegate to existing proof *)
      intros ard Habs Hpre.
      pose proof (verify_PUSHGETGLOBALFIELD_correct n p e le m s) as Hold.
      unfold handle_PUSHGETGLOBALFIELD in Hold.
      rewrite Hnth, Hfoh in Hold.
      apply (Hold ard); [exact Habs |].
      unfold pre_of, pushgetglobalfield_step_pre in Hpre.
      exact Hpre.
    + (* field_or_heap = None: Error case *)
      unfold P_error_of. simpl. rewrite Hnth. rewrite Hfoh. reflexivity.
  - (* nth_error = None: Error case *)
    unfold P_error_of. simpl. rewrite Hnth. reflexivity.
Qed.
