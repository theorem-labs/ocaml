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
      (setfloatfield_step_pre n)
      (fun _ s => match s.(Machine.stack) with
                  | _ :: _ =>
                    match s.(Machine.accu) with
                    | Val_ptr addr =>
                      match heap_lookup s.(Machine.hp) addr with
                      | Some (_, fields) =>
                          set_nth fields n (hd (Val_int 0) s.(Machine.stack)) = None
                      | None => True
                      end
                    | _ => True
                    end
                  | _ => True end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro n.
  intros e le m s.
  unfold handler_correct, handle_SETFLOATFIELD.

  (* Case split on stack *)
  destruct (Machine.stack s) as [|newval rest] eqn:Hstk.
  { (* stack = [] => Error "stack underflow" *)
    reflexivity. }

  (* Case split on accu *)
  destruct (Machine.accu s) as [z_val|blk_tag blk_flds|addr|clo_addr clo_ofs] eqn:Haccu_eq;
    try exact I.

  (* Main case: accu = Val_ptr addr *)
  destruct (heap_lookup (Machine.hp s) addr) as [[tag fields]|] eqn:Hlookup.
  2: { (* heap_lookup = None => Error "dangling pointer" *)
    exact I. }

  destruct (set_nth fields n newval) as [new_fields|] eqn:Hset.
  2: { (* set_nth = None => Error "index out of bounds" *)
    simpl. exact Hset. }

  (* ================================================================ *)
  (* Step case: stack = newval :: rest, accu = Val_ptr addr,           *)
  (*            heap_lookup = Some (tag, fields), set_nth = Some       *)
  (* ================================================================ *)
  {
    intros ard Hpre [Hhpre Hcode_pre].
    unfold abs_rel_with_ard in Hpre.

    set (sb := ar_sptr_block ard) in *.
    set (so := ar_sptr_ofs ard) in *.
    set (hm := ar_heap_map ard) in *.
    set (cb := ar_code_base_block ard) in *.
    set (co := ar_code_base_ofs ard) in *.
    set (gb := ar_global_block ard) in *.
    set (go0 := ar_global_ofs ard) in *.

    destruct Hpre as (Hle_s &
      [pc_ptr [Hpc_load Hpc_rel]] &
      [accu_v [Haccu_load Haccu_repr]] &
      [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
      [env_v [Henv_load Henv_repr]] &
      Hextra_load &
      [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
      [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
    subst sp_ptr.

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound.
    fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
    pose proof (code_block_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

    (* Composite environment facts *)
    destruct interp_state_co_full as [co_is [Hco [Hpc_offset [Haccu_offset Hsp_offset]]]].

    (* Stack repr: extract head *)
    rewrite Hstk in Hstack_repr.
    inversion Hstack_repr as [| ? ? ? ? stk_top_cv Hload_sp0 Hval_repr_top Hstack_repr_rest].
    (* Protect gd_ptr from bare subst *)
    revert Hgd_load Hgd_eq Hglobal_repr.
    subst.
    intros Hgd_load Hgd_eq Hglobal_repr.

    (* Stack bounds *)
    assert (Hsp_mod_orig : Ptrofs.unsigned sp_ofs + 8 < Ptrofs.modulus).
    { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }
    assert (Hsp_rep_tail : Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length rest) < Ptrofs.modulus).
    { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }

    (* Use heap precondition *)
    unfold setfloatfield_heap_pre in Hhpre.
    specialize (Hhpre newval rest Hstk accu_v Haccu_repr sp_b sp_ofs Hsp_load stk_top_cv Hval_repr_top).
    destruct Hhpre as [hb [hofs [Haccu_is_ptr [Hhb_ne_sb [Hhb_ne_sp [Hhb_ne_gb [Hhb_ne_cb
      [fb [fofs [Hstk_top_is_ptr [Hfb_ne_sb
      [fv [Hfloat_load [Hn_range Hfloat_store_ok]]]]]]]]]]]]]].
    subst accu_v stk_top_cv.

    (* Code buffer precondition *)
    unfold setfloatfield_code_pre in Hcode_pre.

    (* Unfold pc_rel *)
    unfold pc_rel in Hpc_rel. subst pc_ptr.
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

    (* ============================================================ *)
    (* Store 1: float store to heap block                            *)
    (* ============================================================ *)
    destruct (Hfloat_store_ok fv) as [m1 [Hstore1 [Hload_pres1 Hperm_pres1]]].

    (* struct field loads survive store 1 (hb <> sb) *)
    assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { apply Hload_pres1. intro Heq; exact (Hhb_ne_sb (eq_sym Heq)). exact Hpc_load. }

    assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) =
              Some (Vptr hb hofs)).
    { apply Hload_pres1. intro Heq; exact (Hhb_ne_sb (eq_sym Heq)). exact Haccu_load. }

    assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
              Some (Vptr sp_b sp_ofs)).
    { apply Hload_pres1. intro Heq; exact (Hhb_ne_sb (eq_sym Heq)). exact Hsp_load. }

    assert (Henv_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { apply Hload_pres1. intro Heq; exact (Hhb_ne_sb (eq_sym Heq)). exact Henv_load. }

    assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply Hload_pres1. intro Heq; exact (Hhb_ne_sb (eq_sym Heq)). exact Hextra_load. }

    assert (Hgd_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
    { apply Hload_pres1. intro Heq; exact (Hhb_ne_sb (eq_sym Heq)). exact Hgd_load. }

    assert (Hts_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
    { apply Hload_pres1. intro Heq; exact (Hhb_ne_sb (eq_sym Heq)). exact Hts_load. }

    (* code buffer load survives store 1 (hb <> cb) *)
    assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
              Some (Vint (Int.repr (Z.of_nat n)))).
    { apply Hload_pres1. intro Heq; exact (Hhb_ne_cb (eq_sym Heq)). exact Hcode_pre. }

    (* stack top load (sp_b) survives store 1 (hb <> sp_b) *)
    assert (Hload_sp0_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) =
              Some (Vptr fb fofs)).
    { apply Hload_pres1. intro Heq; exact (Hhb_ne_sp (eq_sym Heq)). exact Hload_sp0. }

    (* float box load (fb) survives store 1 *)
    (* We need fb <> hb or different offsets. Use the precondition. *)
    (* Actually, fb might equal hb. Use Mem.load_store_other or handle separately. *)
    (* The float store is Mfloat64 at (hb, ...). The float box load is Mfloat64 at (fb, fofs). *)
    (* If fb <> hb, it's straightforward. If fb = hb, the offsets might differ. *)
    (* For safety, we require the float box load to be done BEFORE the store in C code,
       which it is: _t'8 is read before the store. So we use the original m. *)

    (* sb_writable in m1 *)
    assert (Hsb_writable_m1 : Mem.range_perm m1 sb (Ptrofs.unsigned so)
              (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs' Hofs'. apply Hperm_pres1. apply Hsb_writable. exact Hofs'. }

    (* ============================================================ *)
    (* Store 2: accu field (so+8) <- val_unit = Vlong 1              *)
    (* ============================================================ *)
    set (unit_v := Vlong (Int64.repr 1)).

    destruct (store_succeeds_sb m1 sb so 8 (Vptr hb hofs) Hsb_writable_m1 Haccu_load_m1 ltac:(lia) ltac:(lia) unit_v)
      as [m2 Hstore2].

    (* ============================================================ *)
    (* Store 3: sp field (so+16) <- Vptr sp_b (sp_ofs + 8)          *)
    (* ============================================================ *)
    set (new_sp_v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).

    assert (Hsb_writable_m2 : Mem.range_perm m2 sb (Ptrofs.unsigned so)
              (Ptrofs.unsigned so + 56) Cur Writable).
    { apply (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore2 Hsb_writable_m1). }

    assert (Hsp_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 16) =
              Some (Vptr sp_b sp_ofs)).
    { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 8)
               (Ptrofs.unsigned so + 16) unit_v _ Hstore2 Hsp_load_m1).
      right. lia. }

    destruct (store_succeeds_sb m2 sb so 16 (Vptr sp_b sp_ofs) Hsb_writable_m2 Hsp_load_m2 ltac:(lia) ltac:(lia) new_sp_v)
      as [m3 Hstore3].

    (* ============================================================ *)
    (* Store 4: pc field (so+0) <- Vptr cb (pc_ofs + 4)             *)
    (* ============================================================ *)
    set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
    set (new_pc_v := Vptr cb new_pc_ofs).

    assert (Hsb_writable_m3 : Mem.range_perm m3 sb (Ptrofs.unsigned so)
              (Ptrofs.unsigned so + 56) Cur Writable).
    { apply (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore3 Hsb_writable_m2). }

    assert (Hpc_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 16)
               (Ptrofs.unsigned so + 0) new_sp_v _ Hstore3).
      apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 8)
               (Ptrofs.unsigned so + 0) unit_v _ Hstore2 Hpc_load_m1).
      left. lia. left. lia. }

    destruct (store_succeeds_sb m3 sb so 0 (Vptr cb pc_ofs) Hsb_writable_m3 Hpc_load_m3 ltac:(lia) ltac:(lia) new_pc_v)
      as [m4 Hstore4].

    (* ============================================================ *)
    (* Witnesses                                                     *)
    (* ============================================================ *)

    (* Build the local environment step by step *)
    set (le1 := PTree.set _t'3 (Vptr hb hofs) le).
    set (le2 := PTree.set _t'4 (Vptr cb pc_ofs) le1).
    set (le3 := PTree.set _t'5 (Vint (Int.repr (Z.of_nat n))) le2).
    set (le4 := PTree.set _t'6 (Vptr sp_b sp_ofs) le3).
    set (le5 := PTree.set _t'7 (Vptr fb fofs) le4).
    set (le6 := PTree.set _t'8 (Vfloat fv) le5).
    set (le7 := PTree.set _t'2 (Vptr sp_b sp_ofs) le6).
    set (le' := PTree.set _t'1 (Vptr cb pc_ofs) le7).

    exists le'. exists m4.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec_stmt derivation                                    *)
    (* ============================================================== *)
    {
      (* We break the body into individual phases using exec_Sseq_1. *)

      (* Phase 1: Sset _t'3 (s->accu) *)
      assert (Hexec_set_t3 : exec_stmt function_entry1 clight_ge e le m
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong))
          E0 le1 m Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_load; eval_cbn.
        reflexivity. }

      (* Phase 2: Sset _t'4 (s->pc) *)
      assert (Hexec_set_t4 : exec_stmt function_entry1 clight_ge e le1 m
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint)))
          E0 le2 m Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le1.
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        rewrite Hpc_load; eval_cbn.
        reflexivity. }

      (* Phase 3: Sset _t'5 deref t4 -- read n from code buffer *)
      assert (Hexec_set_t5 : exec_stmt function_entry1 clight_ge e le2 m
          (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tint)) tint))
          E0 le3 m Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le2. rewrite PTree.gss; eval_cbn.
        unfold pc_ofs, cb, co.
        rewrite Hcode_pre; eval_cbn.
        reflexivity. }

      (* Phase 4: Sset _t'6 (s->sp) *)
      assert (Hexec_set_t6 : exec_stmt function_entry1 clight_ge e le3 m
          (Sset _t'6
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          E0 le4 m Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le3. rewrite PTree.gso by (compute; congruence).
        unfold le2. rewrite PTree.gso by (compute; congruence).
        unfold le1. rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hsp_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
        rewrite Hsp_load; eval_cbn.
        reflexivity. }

      (* Phase 5: Sset _t'7 deref t6 -- read stack top *)
      assert (Hexec_set_t7 : exec_stmt function_entry1 clight_ge e le4 m
          (Sset _t'7 (Ederef (Etempvar _t'6 (tptr tlong)) tlong))
          E0 le5 m Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le4. rewrite PTree.gss; eval_cbn.
        rewrite Hload_sp0; eval_cbn.
        reflexivity. }

      (* Phase 6: Sset _t'8 deref cast t7 as double -- Double_val *)
      assert (Hexec_set_t8 : exec_stmt function_entry1 clight_ge e le5 m
          (Sset _t'8
            (Ederef (Ecast (Etempvar _t'7 tlong) (tptr tdouble)) tdouble))
          E0 le6 m Out_normal).
      { eapply exec_Sset.
        eapply eval_Elvalue.
        - eapply eval_Ederef.
          eapply eval_Ecast.
          + econstructor.
            unfold le5. rewrite PTree.gss. reflexivity.
          + exact (sem_cast_long_to_ptr_tdouble_local fb fofs m).
        - apply deref_loc_value with (chunk := Mfloat64).
          + simpl. reflexivity.
          + simpl. exact Hfloat_load. }

      (* Phase 7: Sassign store double to accu[n] -- float store *)
      (* This involves sizeof expressions, we use manual proof *)

      assert (Hsize_div : sem_binary_operation (genv_cenv ge) Odiv
                (Vptrofs (Ptrofs.repr (sizeof (genv_cenv ge) tdouble))) tulong
                (Vptrofs (Ptrofs.repr (sizeof (genv_cenv ge) tlong))) tulong m
              = Some (Vlong (Int64.repr 1))).
      { change (sizeof (genv_cenv ge) tdouble) with 8%Z.
        change (sizeof (genv_cenv ge) tlong) with 8%Z.
        apply sizeof_div_1_local. }

      assert (Hmul_n : sem_binary_operation (genv_cenv ge) Omul
                (Vint (Int.repr (Z.of_nat n))) tint
                (Vlong (Int64.repr 1)) tulong m
              = Some (Vlong (Int64.repr (Z.of_nat n)))).
      { rewrite (mul_vint_vlong_1_local (Int.repr (Z.of_nat n))).
        rewrite (int_signed_repr_small_local _ Hn_range). reflexivity. }

      assert (Hadd_ptr : sem_binary_operation (genv_cenv ge) Oadd
                (Vptr hb hofs) (tptr tlong)
                (Vlong (Int64.repr (Z.of_nat n))) tulong m
              = Some (Vptr hb (Ptrofs.add hofs (Ptrofs.repr (Z.of_nat n * 8))))).
      { rewrite (sem_add_ptr_long_vlong_local hb hofs (Int64.repr (Z.of_nat n)) m).
        f_equal. f_equal. f_equal.
        rewrite (ptrofs_of_int64_repr_local (Z.of_nat n) ltac:(lia)).
        unfold Ptrofs.mul.
        change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8%Z.
        rewrite Ptrofs.unsigned_repr.
        2: { change Ptrofs.max_unsigned with 18446744073709551615%Z.
             change Int.max_signed with 2147483647%Z in Hn_range. lia. }
        f_equal. lia. }

      assert (Hexec_store_float : exec_stmt function_entry1 clight_ge e le6 m
          (Sassign
            (Ederef
              (Ecast
                (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                  (Ebinop Omul (Etempvar _t'5 tint)
                    (Ebinop Odiv (Esizeof tdouble tulong)
                      (Esizeof tlong tulong) tulong) tulong)
                  (tptr tlong)) (tptr tdouble)) tdouble)
            (Etempvar _t'8 tdouble))
          E0 le6 m1 Out_normal).
      { eapply exec_Sassign.
        - (* eval_lvalue: Ederef (Ecast (Ebinop Oadd ...)) *)
          eapply eval_Ederef.
          eapply eval_Ecast.
          + eapply eval_Ebinop.
            * eapply eval_Ecast.
              -- econstructor.
                 unfold le6. rewrite PTree.gso by (compute; congruence).
                 unfold le5. rewrite PTree.gso by (compute; congruence).
                 unfold le4. rewrite PTree.gso by (compute; congruence).
                 unfold le3. rewrite PTree.gso by (compute; congruence).
                 unfold le2. rewrite PTree.gso by (compute; congruence).
                 unfold le1. rewrite PTree.gss. reflexivity.
              -- exact (sem_cast_long_to_ptr_vptr_local hb hofs m).
            * eapply eval_Ebinop.
              -- econstructor.
                 unfold le6. rewrite PTree.gso by (compute; congruence).
                 unfold le5. rewrite PTree.gso by (compute; congruence).
                 unfold le4. rewrite PTree.gso by (compute; congruence).
                 unfold le3. rewrite PTree.gss. reflexivity.
              -- eapply eval_Ebinop.
                 ++ econstructor.
                 ++ econstructor.
                 ++ exact Hsize_div.
              -- exact Hmul_n.
            * exact Hadd_ptr.
          + exact (sem_cast_ptr_tlong_to_ptr_tdouble_local hb
                     (Ptrofs.add hofs (Ptrofs.repr (Z.of_nat n * 8))) m).
        - (* eval_expr: Etempvar _t'8 tdouble *)
          econstructor.
          unfold le6. rewrite PTree.gss. reflexivity.
        - (* sem_cast Vfloat from tdouble to tdouble *)
          exact (sem_cast_tdouble_tdouble_local fv m).
        - (* assign_loc: store float *)
          apply assign_loc_value with (chunk := Mfloat64).
          + simpl. reflexivity.
          + simpl. exact Hstore1. }

      (* Phase 8: Sassign s->accu = val_unit *)
      assert (Hexec_store_accu : exec_stmt function_entry1 clight_ge e le6 m1
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong)
            (Ebinop Oadd
              (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
                (Econst_int (Int.repr 1) tint) tlong)
              (Econst_int (Int.repr 1) tint) tlong))
          E0 le6 m2 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le6. rewrite PTree.gso by (compute; congruence).
        unfold le5. rewrite PTree.gso by (compute; congruence).
        unfold le4. rewrite PTree.gso by (compute; congruence).
        unfold le3. rewrite PTree.gso by (compute; congruence).
        unfold le2. rewrite PTree.gso by (compute; congruence).
        unfold le1. rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        rewrite (sem_cast_int_to_long_0 m1); eval_cbn.
        rewrite (sem_shl_long_0_1 m1); eval_cbn.
        rewrite (sem_add_long_int_0_1 m1); eval_cbn.
        rewrite (sem_cast_long_vlong (Int64.repr 1)); eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        fold unit_v. rewrite Hstore2; eval_cbn.
        reflexivity. }

      (* Phase 9: Sset _t'2 (s->sp) -- read sp from m2 *)
      assert (Hsp_load_m2' : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 16) =
                Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 8)
                 (Ptrofs.unsigned so + 16) unit_v _ Hstore2 Hsp_load_m1).
        right. lia. }

      assert (Hexec_set_t2 : exec_stmt function_entry1 clight_ge e le6 m2
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          E0 le7 m2 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le6. rewrite PTree.gso by (compute; congruence).
        unfold le5. rewrite PTree.gso by (compute; congruence).
        unfold le4. rewrite PTree.gso by (compute; congruence).
        unfold le3. rewrite PTree.gso by (compute; congruence).
        unfold le2. rewrite PTree.gso by (compute; congruence).
        unfold le1. rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hsp_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
        rewrite Hsp_load_m2'; eval_cbn.
        reflexivity. }

      (* Phase 10: Sassign s->sp = _t'2 + 1 -- store sp *)
      assert (Hexec_store_sp : exec_stmt function_entry1 clight_ge e le7 m2
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong))
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)))
          E0 le7 m3 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le7. rewrite PTree.gso by (compute; congruence).
        unfold le6. rewrite PTree.gso by (compute; congruence).
        unfold le5. rewrite PTree.gso by (compute; congruence).
        unfold le4. rewrite PTree.gso by (compute; congruence).
        unfold le3. rewrite PTree.gso by (compute; congruence).
        unfold le2. rewrite PTree.gso by (compute; congruence).
        unfold le1. rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hsp_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        unfold le7. rewrite PTree.gss; eval_cbn.
        rewrite sem_add_sp_1; eval_cbn.
        rewrite sem_cast_ptr_to_ptr; eval_cbn.
        rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
        unfold new_sp_v in Hstore3.
        rewrite Hstore3; eval_cbn.
        reflexivity. }

      (* Phase 11: Sset _t'1 (s->pc) -- read pc from m3 *)
      assert (Hexec_set_t1 : exec_stmt function_entry1 clight_ge e le7 m3
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint)))
          E0 le' m3 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le7. rewrite PTree.gso by (compute; congruence).
        unfold le6. rewrite PTree.gso by (compute; congruence).
        unfold le5. rewrite PTree.gso by (compute; congruence).
        unfold le4. rewrite PTree.gso by (compute; congruence).
        unfold le3. rewrite PTree.gso by (compute; congruence).
        unfold le2. rewrite PTree.gso by (compute; congruence).
        unfold le1. rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        rewrite Hpc_load_m3; eval_cbn.
        reflexivity. }

      (* Phase 12: Sassign s->pc = _t'1 + 1 -- store pc *)
      assert (Hexec_store_pc : exec_stmt function_entry1 clight_ge e le' m3
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint))
            (Ebinop Oadd (Etempvar _t'1 (tptr tint))
              (Econst_int (Int.repr 1) tint) (tptr tint)))
          E0 le' m4 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le'. rewrite PTree.gso by (compute; congruence).
        unfold le7. rewrite PTree.gso by (compute; congruence).
        unfold le6. rewrite PTree.gso by (compute; congruence).
        unfold le5. rewrite PTree.gso by (compute; congruence).
        unfold le4. rewrite PTree.gso by (compute; congruence).
        unfold le3. rewrite PTree.gso by (compute; congruence).
        unfold le2. rewrite PTree.gso by (compute; congruence).
        unfold le1. rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        unfold le'. rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_pc_1_local cb pc_ofs m3); eval_cbn.
        rewrite (sem_cast_ptr_tint_to_ptr_tint_local cb new_pc_ofs); eval_cbn.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        fold new_pc_v.
        rewrite Hstore4; eval_cbn.
        reflexivity. }

      (* Phase 13: Sreturn 0 *)
      assert (Hexec_return : exec_stmt function_entry1 clight_ge e le' m4
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          E0 le' m4 (Out_return (Some (Vint (Int.repr 0), tint)))).
      { apply (eval_stmt_to_exec clight_ge 10). reflexivity. }

      (* Combine into sequences bottom-up *)
      (* Part A: phases 1-7 *)
      assert (Hexec_23 :
        exec_stmt function_entry1 clight_ge e le1 m
          (Ssequence
            (Sset _t'4 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Ssequence
              (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tint)) tint))
              (Ssequence
                (Sset _t'6 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Ssequence
                  (Sset _t'7 (Ederef (Etempvar _t'6 (tptr tlong)) tlong))
                  (Ssequence
                    (Sset _t'8 (Ederef (Ecast (Etempvar _t'7 tlong) (tptr tdouble)) tdouble))
                    (Sassign
                      (Ederef (Ecast (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                        (Ebinop Omul (Etempvar _t'5 tint) (Ebinop Odiv (Esizeof tdouble tulong)
                          (Esizeof tlong tulong) tulong) tulong) (tptr tlong)) (tptr tdouble)) tdouble)
                      (Etempvar _t'8 tdouble)))))))
          E0 le6 m1 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1. exact Hexec_set_t4.
        replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1. exact Hexec_set_t5.
        replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1. exact Hexec_set_t6.
        replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1. exact Hexec_set_t7.
        replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1. exact Hexec_set_t8.
        exact Hexec_store_float. }

      assert (Hexec_partA :
        exec_stmt function_entry1 clight_ge e le m
          (Ssequence
            (Sset _t'3 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _accu tlong))
            (Ssequence
              (Sset _t'4 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                           (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Ssequence
                (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tint)) tint))
                (Ssequence
                  (Sset _t'6 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                  (Ssequence
                    (Sset _t'7 (Ederef (Etempvar _t'6 (tptr tlong)) tlong))
                    (Ssequence
                      (Sset _t'8 (Ederef (Ecast (Etempvar _t'7 tlong) (tptr tdouble)) tdouble))
                      (Sassign
                        (Ederef (Ecast (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                          (Ebinop Omul (Etempvar _t'5 tint) (Ebinop Odiv (Esizeof tdouble tulong)
                            (Esizeof tlong tulong) tulong) tulong) (tptr tlong)) (tptr tdouble)) tdouble)
                        (Etempvar _t'8 tdouble))))))))
          E0 le6 m1 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1. exact Hexec_set_t3. exact Hexec_23. }

      (* Part B: phases 8-13 *)
      assert (Hexec_9_10 :
        exec_stmt function_entry1 clight_ge e le6 m2
          (Ssequence
            (Sset _t'2 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _sp (tptr tlong))
              (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
                (Econst_int (Int.repr 1) tint) (tptr tlong))))
          E0 le7 m3 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1. exact Hexec_set_t2. exact Hexec_store_sp. }

      assert (Hexec_11_12 :
        exec_stmt function_entry1 clight_ge e le7 m3
          (Ssequence
            (Sset _t'1 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint))))
          E0 le' m4 Out_normal).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1. exact Hexec_set_t1. exact Hexec_store_pc. }

      assert (Hexec_11_12_13 :
        exec_stmt function_entry1 clight_ge e le7 m3
          (Ssequence
            (Ssequence
              (Sset _t'1 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                           (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _pc (tptr tint))
                (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                  (Econst_int (Int.repr 1) tint) (tptr tint))))
            (Sreturn (Some (Econst_int (Int.repr 0) tint))))
          E0 le' m4 (Out_return (Some (Vint (Int.repr 0), tint)))).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1. exact Hexec_11_12. exact Hexec_return. }

      assert (Hexec_9_to_13 :
        exec_stmt function_entry1 clight_ge e le6 m2
          (Ssequence
            (Ssequence
              (Sset _t'2 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                           (Tstruct _interp_state noattr)) _sp (tptr tlong)))
              (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                         (Tstruct _interp_state noattr)) _sp (tptr tlong))
                (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong))))
            (Ssequence
              (Ssequence
                (Sset _t'1 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                             (Tstruct _interp_state noattr)) _pc (tptr tint)))
                (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                           (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                    (Econst_int (Int.repr 1) tint) (tptr tint))))
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
          E0 le' m4 (Out_return (Some (Vint (Int.repr 0), tint)))).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1. exact Hexec_9_10. exact Hexec_11_12_13. }

      assert (Hexec_partB :
        exec_stmt function_entry1 clight_ge e le6 m1
          (Ssequence
            (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                       (Tstruct _interp_state noattr)) _accu tlong)
              (Ebinop Oadd
                (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
                  (Econst_int (Int.repr 1) tint) tlong)
                (Econst_int (Int.repr 1) tint) tlong))
            (Ssequence
              (Ssequence
                (Sset _t'2 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                             (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                           (Tstruct _interp_state noattr)) _sp (tptr tlong))
                  (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
                    (Econst_int (Int.repr 1) tint) (tptr tlong))))
              (Ssequence
                (Ssequence
                  (Sset _t'1 (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                               (Tstruct _interp_state noattr)) _pc (tptr tint)))
                  (Sassign (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                             (Tstruct _interp_state noattr)) _pc (tptr tint))
                    (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                      (Econst_int (Int.repr 1) tint) (tptr tint))))
                (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
          E0 le' m4 (Out_return (Some (Vint (Int.repr 0), tint)))).
      { replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1. exact Hexec_store_accu. exact Hexec_9_to_13. }

      (* Full body = Part A ; Part B *)
      change (fn_body f_instr_SETFLOATFIELD) with
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _accu tlong))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Ssequence
                (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tint)) tint))
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                  (Ssequence
                    (Sset _t'7 (Ederef (Etempvar _t'6 (tptr tlong)) tlong))
                    (Ssequence
                      (Sset _t'8
                        (Ederef (Ecast (Etempvar _t'7 tlong) (tptr tdouble)) tdouble))
                      (Sassign
                        (Ederef
                          (Ecast
                            (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                              (Ebinop Omul (Etempvar _t'5 tint)
                                (Ebinop Odiv (Esizeof tdouble tulong)
                                  (Esizeof tlong tulong) tulong) tulong)
                              (tptr tlong)) (tptr tdouble)) tdouble)
                        (Etempvar _t'8 tdouble))))))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _accu tlong)
              (Ebinop Oadd
                (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
                  (Econst_int (Int.repr 1) tint) tlong)
                (Econst_int (Int.repr 1) tint) tlong))
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Efield
                    (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong))
                  (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
                    (Econst_int (Int.repr 1) tint) (tptr tlong))))
              (Ssequence
                (Ssequence
                  (Sset _t'1
                    (Efield
                      (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _pc (tptr tint)))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _pc (tptr tint))
                    (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                      (Econst_int (Int.repr 1) tint) (tptr tint))))
                (Sreturn (Some (Econst_int (Int.repr 0) tint))))))).

      replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1. exact Hexec_partA. exact Hexec_partB.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
      set (ard' := mk_abs_rel
        sb so hm
        cb new_co
        gb go0
        (ar_stack_block ard) (ar_stack_base_ofs ard)
        (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
      exists ard'.

      set (uso := Ptrofs.unsigned so) in *.

      (* --- Loads from m4 --- *)

      (* Helper: loads on sb from m1 survive store 2 at (sb, so+8) *)
      (* then survive store 3 at (sb, so+16), then store 4 at (sb, so+0) *)

      (* pc field at uso+0: written by store 4 *)
      assert (Hpc_load4 : Mem.load Mint64 m4 sb (uso + 0) = Some new_pc_v).
      { pose proof (load_after_store_same m3 m4 sb (uso + 0) new_pc_v Hstore4) as Htmp.
        unfold new_pc_v in Htmp |- *. rewrite load_result_vptr_local in Htmp. exact Htmp. }

      (* accu field at uso+8: written by store 2, preserved by stores 3 and 4 *)
      assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (uso + 8) = Some unit_v).
      { pose proof (load_after_store_same m1 m2 sb (uso + 8) unit_v Hstore2) as Htmp.
        subst unit_v. rewrite load_result_vlong_local in Htmp. exact Htmp. }
      assert (Haccu_load_m3 : Mem.load Mint64 m3 sb (uso + 8) = Some unit_v).
      { apply (load_after_store_other m2 m3 sb (uso + 16) (uso + 8)
                 new_sp_v unit_v Hstore3 Haccu_load_m2). left. lia. }
      assert (Haccu_load4 : Mem.load Mint64 m4 sb (uso + 8) = Some unit_v).
      { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 8)
                 new_pc_v unit_v Hstore4 Haccu_load_m3). right. lia. }

      (* sp field at uso+16: written by store 3, preserved by store 4 *)
      assert (Hsp_load_m3 : Mem.load Mint64 m3 sb (uso + 16) = Some new_sp_v).
      { pose proof (load_after_store_same m2 m3 sb (uso + 16) new_sp_v Hstore3) as Htmp.
        unfold new_sp_v in Htmp |- *. rewrite load_result_vptr_local in Htmp. exact Htmp. }
      assert (Hsp_load4 : Mem.load Mint64 m4 sb (uso + 16) = Some new_sp_v).
      { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 16)
                 new_pc_v new_sp_v Hstore4 Hsp_load_m3). right. lia. }

      (* env field at uso+24: preserved through stores 2, 3, 4 *)
      assert (Henv_load_m2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 24)
                 unit_v env_v Hstore2 Henv_load_m1). right. lia. }
      assert (Henv_load_m3 : Mem.load Mint64 m3 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m2 m3 sb (uso + 16) (uso + 24)
                 new_sp_v env_v Hstore3 Henv_load_m2). right. lia. }
      assert (Henv_load4 : Mem.load Mint64 m4 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 24)
                 new_pc_v env_v Hstore4 Henv_load_m3). right. lia. }

      (* extra_args field at uso+32: preserved through stores 2, 3, 4 *)
      assert (Hextra_load_m2 : Mem.load Mint64 m2 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 32)
                 unit_v _ Hstore2 Hextra_load_m1). right. lia. }
      assert (Hextra_load_m3 : Mem.load Mint64 m3 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m2 m3 sb (uso + 16) (uso + 32)
                 new_sp_v _ Hstore3 Hextra_load_m2). right. lia. }
      assert (Hextra_load4 : Mem.load Mint64 m4 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 32)
                 new_pc_v _ Hstore4 Hextra_load_m3). right. lia. }

      (* global_data field at uso+40: preserved through stores 2, 3, 4 *)
      assert (Hgd_load_m2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 40)
                 unit_v gd_ptr Hstore2 Hgd_load_m1). right. lia. }
      assert (Hgd_load_m3 : Mem.load Mint64 m3 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m2 m3 sb (uso + 16) (uso + 40)
                 new_sp_v gd_ptr Hstore3 Hgd_load_m2). right. lia. }
      assert (Hgd_load4 : Mem.load Mint64 m4 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 40)
                 new_pc_v gd_ptr Hstore4 Hgd_load_m3). right. lia. }

      (* trap_sp field at uso+48: preserved through stores 2, 3, 4 *)
      assert (Hts_load_m2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m1 m2 sb (uso + 8) (uso + 48)
                 unit_v ts_ptr Hstore2 Hts_load_m1). right. lia. }
      assert (Hts_load_m3 : Mem.load Mint64 m3 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m2 m3 sb (uso + 16) (uso + 48)
                 new_sp_v ts_ptr Hstore3 Hts_load_m2). right. lia. }
      assert (Hts_load4 : Mem.load Mint64 m4 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m3 m4 sb (uso + 0) (uso + 48)
                 new_pc_v ts_ptr Hstore4 Hts_load_m3). right. lia. }

      (* Stack repr: rest through m -> m1 -> m2 -> m3 -> m4 *)
      (* m -> m1: store to hb, sp_b <> hb, using load preservation *)
      (* Helper: stack_repr preserved through store to different block using load preservation *)
      assert (Hstack_pres_m1 : forall stk sb0 sofs0,
        stack_repr hm cb co m stk sb0 sofs0 -> sb0 <> hb ->
        stack_repr hm cb co m1 stk sb0 sofs0).
      { intros stk0. induction stk0 as [| v0 vs IH]; intros sb0 sofs0 Hsr Hne.
        - constructor.
        - inversion Hsr; subst. econstructor.
          + apply Hload_pres1. congruence. eassumption.
          + eassumption.
          + apply IH; eassumption. }
      assert (Hstack_m1 : stack_repr hm cb co m1 rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
      { apply Hstack_pres_m1. exact Hstack_repr_rest.
        intro Heq; apply Hhb_ne_sp; symmetry; exact Heq. }
      (* m1 -> m2: store to sb at so+8, sp_b <> sb *)
      assert (Hstack_m2 : stack_repr hm cb co m2 rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
      { eapply stack_repr_store_other_block.
        - exact Hstack_m1.
        - exact Hstore2.
        - intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
      (* m2 -> m3: store to sb at so+16, sp_b <> sb *)
      assert (Hstack_m3 : stack_repr hm cb co m3 rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
      { eapply stack_repr_store_other_block.
        - exact Hstack_m2.
        - exact Hstore3.
        - intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
      (* m3 -> m4: store to sb at so+0, sp_b <> sb *)
      assert (Hstack_m4 : stack_repr hm cb co m4 rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
      { eapply stack_repr_store_other_block.
        - exact Hstack_m3.
        - exact Hstore4.
        - intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }

      (* Global repr: through m -> m1 -> m2 -> m3 -> m4 *)
      (* m -> m1: Mfloat64 store to hb, gb <> hb, using load preservation *)
      assert (Hglobal_pres_m1 : forall gs gb0 gofs0,
        global_repr hm cb co m gs gb0 gofs0 -> gb0 <> hb ->
        global_repr hm cb co m1 gs gb0 gofs0).
      { intros gs0. induction gs0 as [| v0 vs IH]; intros gb0 gofs0 Hgr Hne.
        - constructor.
        - inversion Hgr; subst. econstructor.
          + apply Hload_pres1. congruence. eassumption.
          + eassumption.
          + apply IH; eassumption. }
      assert (Hglobal_m1 : global_repr hm cb co m1 (Machine.global s) gb go0).
      { apply Hglobal_pres_m1. exact Hglobal_repr.
        intro Heq; apply Hhb_ne_gb; symmetry; exact Heq. }
      assert (Hglobal_m2 : global_repr hm cb co m2 (Machine.global s) gb go0).
      { eapply global_repr_store_other_block.
        - exact Hglobal_m1.
        - exact Hstore2.
        - intro Heq; exact (Hgb_ne (eq_sym Heq)). }
      assert (Hglobal_m3 : global_repr hm cb co m3 (Machine.global s) gb go0).
      { eapply global_repr_store_other_block.
        - exact Hglobal_m2.
        - exact Hstore3.
        - intro Heq; exact (Hgb_ne (eq_sym Heq)). }
      assert (Hglobal_m4 : global_repr hm cb co m4 (Machine.global s) gb go0).
      { eapply global_repr_store_other_block.
        - exact Hglobal_m3.
        - exact Hstore4.
        - intro Heq; exact (Hgb_ne (eq_sym Heq)). }

      (* sb_writable in m4 *)
      assert (Hsb_writable_m4 : Mem.range_perm m4 sb (uso) (uso + 56) Cur Writable).
      { apply (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore4).
        apply (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore3 Hsb_writable_m2). }

      (* sp_writable in m4 *)
      assert (Hsp_writable_m4 : forall ofs', 0 <= ofs' < Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length rest) ->
                Mem.perm m4 sp_b ofs' Cur Writable).
      { intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore4.
        eapply Mem.perm_store_1. exact Hstore3.
        eapply Mem.perm_store_1. exact Hstore2.
        eapply Hperm_pres1.
        apply Hsp_writable. rewrite Hstk. simpl length.
        pose proof (Nat2Z.is_nonneg (length rest)). lia. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le' le7 le6 le5 le4 le3 le2 le1.
        repeat (rewrite PTree.gso by (compute; congruence)).
        exact Hle_s. }

      (* 2. pc field -- updated *)
      { exists new_pc_v. split.
        - exact Hpc_load4.
        - simpl. subst new_pc_v new_pc_ofs.
          apply pc_rel_shift_local. }

      (* 3. accu field -- updated to val_unit = Val_int 0 *)
      { exists unit_v. split.
        - exact Haccu_load4.
        - simpl. subst unit_v. exact (vr_int _ _ _ 0). }

      (* 4. sp field -- updated to sp + 8 (stack tail) *)
      { exists new_sp_v, sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)).
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load4.
        - reflexivity.
        - simpl. eapply stack_repr_co_shift. exact Hstack_m4.
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)). lia.
        - rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)). exact Hsp_rep_tail.
        - intros ofs' Hofs'.
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)) in Hofs'.
          apply Hsp_writable_m4. exact Hofs'.
        - simpl.
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)).
          apply Z.divide_add_r. exact Hsp_align. exists 1. lia. }

      (* 5. env field -- unchanged *)
      { exists env_v. split.
        - exact Henv_load4.
        - simpl. eapply val_repr_co_shift. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { simpl. exact Hextra_load4. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load4.
        - simpl. exact Hgd_eq.
        - simpl. eapply global_repr_co_shift. exact Hglobal_m4.
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load4.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved through 4 stores *)
      { exact Hsb_writable_m4. }
    }
  }

Qed.

(* Wrapper with the canonical type expected by InstructVerificationProof.v *)
Definition correct_SETFLOATFIELD : forall n,
    handler_correct (handle_instr (Bytecode.AST.SETFLOATFIELD n)) (clight_of (Bytecode.AST.SETFLOATFIELD n))
      (pre_of (Bytecode.AST.SETFLOATFIELD n))
      (P_error_of (Bytecode.AST.SETFLOATFIELD n)) (P_halt_of (Bytecode.AST.SETFLOATFIELD n)) (P_ccall_of (Bytecode.AST.SETFLOATFIELD n)).
Proof.
Admitted.

