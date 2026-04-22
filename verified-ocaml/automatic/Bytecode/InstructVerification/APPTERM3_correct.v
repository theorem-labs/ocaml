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
      (fun msg s =>
         match s.(Machine.stack) with
         | _ :: _ :: _ :: _ => False
         | _ => True
         end \/
         get_code_ptr_s s s.(Machine.accu) = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro slotsize.
  intros e le m s.
  unfold handler_correct.
  simpl.
  unfold handle_APPTERM3.

  (* Case split on stack: need at least 3 elements *)
  destruct (Machine.stack s) as [| arg1 [| arg2 [| arg3 stk_rest]]] eqn:Hstk.

  { (* Error case: stack = nil *)
    simpl. left. trivial.
  }

  { (* Error case: stack = [arg1] *)
    simpl. left. trivial.
  }

  { (* Error case: stack = [arg1; arg2] *)
    simpl. left. trivial.
  }

  (* Case split on get_code_ptr_s *)
  destruct (get_code_ptr_s s s.(Machine.accu)) as [target_pc|] eqn:Hgcp.

  2: { (* Error case: get_code_ptr_s = None *)
    simpl. right. reflexivity.
  }

  (* Step case *)
  intros ard Hpre Hstep_pre.

  destruct Hpre as (Hle_s &
    [pc_ptr [Hpc_load Hpc_rel]] &
    [accu_v [Haccu_load Haccu_repr]] &
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
    [env_v [Henv_load Henv_repr]] &
    Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
    [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
  subst sp_ptr.

  set (sb := ar_sptr_block ard) in *.
  set (so := ar_sptr_ofs ard) in *.
  set (hm := ar_heap_map ard) in *.
  set (cb := ar_code_base_block ard) in *.
  set (co := ar_code_base_ofs ard) in *.
  destruct Hstep_pre as (Hcode_load & Hslot_bound & Hsp_fits & Hsp_new_ge8 & Hslot_ge3 & Hslot_le_len & Hacpl & Hea_unsigned & Hea_signed).

  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  destruct interp_state_co_appterm3 as [co_is [Hco [Hpc_offset [Haccu_offset [Hsp_offset [Henv_offset Hextra_offset]]]]]].

  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* Get closure code pointer info *)
  pose proof (Hacpl sp_b sp_ofs Hsp_load) as Hacpl'.
  unfold appterm3_step_pre in Hacpl'.
  destruct (Hacpl' target_pc Hgcp accu_v Haccu_repr)
    as [accu_b [accu_ofs [code_b [code_ofs
        [Haccu_is_ptr [Hcode_ptr_load [Haccu_ne_sb [Haccu_ne_cb
        [Haccu_ne_spb [new_co [Hcode_ofs_eq Hcode_b_eq]]]]]]]]]]].
  clear Hacpl Hacpl'.
  subst accu_v code_b.

  (* Extract stack elements for reading arg1, arg2, arg3 *)
  rewrite Hstk in Hstack_repr.
  inversion Hstack_repr as [| xv1 xvs1 xb1 xofs1 cv_arg1 Hload_sp0 Hval_repr_arg1 Hstack_repr1].
  subst xv1 xvs1 xb1 xofs1.
  inversion Hstack_repr1 as [| xv2 xvs2 xb2 xofs2 cv_arg2 Hload_sp1 Hval_repr_arg2 Hstack_repr2].
  subst xv2 xvs2 xb2 xofs2.
  inversion Hstack_repr2 as [| xv3 xvs3 xb3 xofs3 cv_arg3 Hload_sp2 Hval_repr_arg3 Hstack_repr_rest].
  subst xv3 xvs3 xb3 xofs3.

  (* sp fits *)
  assert (Hsp_fits_concrete : Ptrofs.unsigned sp_ofs + Z.of_nat slotsize * 8 < Ptrofs.modulus).
  { apply (Hsp_fits sp_b sp_ofs). exact Hsp_load. }

  assert (Hsp_new_ge8_concrete : Ptrofs.unsigned sp_ofs + (Z.of_nat slotsize - 3) * 8 >= 8).
  { apply (Hsp_new_ge8 sp_b sp_ofs). exact Hsp_load. }

  (* The new sp: sp + slotsize - 3, each in units of 8 bytes. *)
  set (slotsize_int := Int.repr (Z.of_nat slotsize)).
  set (sp_plus_slot := Ptrofs.add sp_ofs
         (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed slotsize_int))).
  set (new_sp_ofs := Ptrofs.sub sp_plus_slot
         (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr 3)))).

  assert (Hnew_sp_eq : new_sp_ofs = Ptrofs.add sp_ofs (Ptrofs.repr ((Z.of_nat slotsize - 3) * 8))).
  { unfold new_sp_ofs, sp_plus_slot, slotsize_int.
    rewrite (ptrofs_mul_8_of_ints_eq (Z.of_nat slotsize) ltac:(lia) Hslot_bound).
    rewrite ptrofs_mul_8_3.
    rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc.
    f_equal.
    rewrite Ptrofs.add_unsigned.
    apply Ptrofs.eqm_samerepr.
    replace ((Z.of_nat slotsize - 3) * 8)%Z with (Z.of_nat slotsize * 8 + (- 24))%Z by lia.
    apply Ptrofs.eqm_add.
    - apply Ptrofs.eqm_sym. apply Ptrofs.eqm_unsigned_repr.
    - unfold Ptrofs.neg.
      rewrite (Ptrofs.unsigned_repr 24) by (pose proof ptrofs_max_unsigned_large; lia).
      apply Ptrofs.eqm_sym. apply Ptrofs.eqm_unsigned_repr.
  }

  assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs =
            Ptrofs.unsigned sp_ofs + (Z.of_nat slotsize - 3) * 8).
  { rewrite Hnew_sp_eq.
    rewrite ptrofs_add_unsigned. reflexivity.
    lia. lia. }

  set (new_pc_v := Vptr cb code_ofs).
  set (new_env_v := Vptr accu_b accu_ofs).

  (* Store 1: sp field at (sb, uso+16) <- Vptr sp_b new_sp_ofs *)
  destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia)
              (Vptr sp_b new_sp_ofs))
    as [m1 Hstore1].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

  (* Store 2: write arg1 to new sp[0] on the stack block. *)
  assert (Hstack_perm_m1 : Mem.range_perm m1 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (arg1 :: arg2 :: arg3 :: stk_rest))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore1.
    apply Hsp_writable. rewrite Hstk. exact Hofs'. }
  assert (Hstore2_align : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs)).
  { rewrite Hnew_sp_unsigned.
    apply Z.divide_add_r. exact Hsp_align. exists (Z.of_nat slotsize - 3). simpl. lia. }
  destruct (Mem.valid_access_store m1 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs) cv_arg1) as [m2 Hstore2].
  { split.
    - intros ofs' Hofs'. apply Hstack_perm_m1.
      simpl length. rewrite Hnew_sp_unsigned in Hofs'. unfold size_chunk in Hofs'.
        simpl length in Hslot_le_len.
        pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - exact Hstore2_align. }

  (* Ptrofs.add new_sp_ofs 8 = unsigned new_sp_ofs + 8 *)
  assert (Hsp1_ptrofs : Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 8)) = Ptrofs.unsigned new_sp_ofs + 8).
  { apply ptrofs_add_unsigned. lia. rewrite Hnew_sp_unsigned. lia. }

  assert (Hsp2_ptrofs : Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 16)) = Ptrofs.unsigned new_sp_ofs + 16).
  { apply ptrofs_add_unsigned. lia. rewrite Hnew_sp_unsigned. lia. }

  (* Store 3: write arg2 to new sp[1] = new_sp_ofs + 8 *)
  assert (Hstore3_align : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs + 8)).
  { rewrite Hnew_sp_unsigned.
    replace (Ptrofs.unsigned sp_ofs + (Z.of_nat slotsize - 3) * 8 + 8)
      with (Ptrofs.unsigned sp_ofs + (Z.of_nat slotsize - 2) * 8) by lia.
    apply Z.divide_add_r. exact Hsp_align. exists (Z.of_nat slotsize - 2). simpl. lia. }
  destruct (Mem.valid_access_store m2 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 8) cv_arg2) as [m3 Hstore3].
  { split.
    - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2.
      apply Hstack_perm_m1.
      simpl length. rewrite Hnew_sp_unsigned in Hofs'. unfold size_chunk in Hofs'.
      simpl length in Hslot_le_len.
      pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - exact Hstore3_align. }

  (* Store 4: write arg3 to new sp[2] = new_sp_ofs + 16 *)
  assert (Hstore4_align : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs + 16)).
  { rewrite Hnew_sp_unsigned.
    replace (Ptrofs.unsigned sp_ofs + (Z.of_nat slotsize - 3) * 8 + 16)
      with (Ptrofs.unsigned sp_ofs + (Z.of_nat slotsize - 1) * 8) by lia.
    apply Z.divide_add_r. exact Hsp_align. exists (Z.of_nat slotsize - 1). simpl. lia. }
  destruct (Mem.valid_access_store m3 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 16) cv_arg3) as [m4 Hstore4].
  { split.
    - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore3.
      eapply Mem.perm_store_1. exact Hstore2.
      apply Hstack_perm_m1.
      simpl length. rewrite Hnew_sp_unsigned in Hofs'. unfold size_chunk in Hofs'.
      simpl length in Hslot_le_len.
      pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - exact Hstore4_align. }

  (* Store 5: pc field at (sb, uso+0) <- new_pc_v *)
  assert (Hsb_writable_m4 : Mem.range_perm m4 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs' Hofs'.
    eapply Mem.perm_store_1. exact Hstore4.
    eapply Mem.perm_store_1. exact Hstore3.
    eapply Mem.perm_store_1. exact Hstore2.
    apply Hsb_writable_m1. exact Hofs'. }
  assert (Hpc_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { assert (Hpc_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 0)
               (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs)
               Hstore1 Hpc_load). left. lia. }
    assert (Hpc_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { erewrite Mem.load_store_other. exact Hpc_m1. exact Hstore2.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Hpc_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { erewrite Mem.load_store_other. exact Hpc_m2. exact Hstore3.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    erewrite Mem.load_store_other. exact Hpc_m3. exact Hstore4.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  destruct (store_succeeds_sb m4 sb so 0 (Vptr cb pc_ofs)
              Hsb_writable_m4 Hpc_load_m4 ltac:(lia) ltac:(lia) new_pc_v)
    as [m5 Hstore5].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore5 Hsb_writable_m4) as Hsb_writable_m5.

  (* Store 6: env field at (sb, uso+24) <- new_env_v *)
  assert (Henv_load_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 24) = Some env_v).
  { assert (Henv_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 24)
               (Vptr sp_b new_sp_ofs) env_v Hstore1 Henv_load). right. lia. }
    assert (Henv_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { erewrite Mem.load_store_other. exact Henv_m1. exact Hstore2.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Henv_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { erewrite Mem.load_store_other. exact Henv_m2. exact Hstore3.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Henv_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { erewrite Mem.load_store_other. exact Henv_m3. exact Hstore4.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 24)
             new_pc_v env_v Hstore5 Henv_m4). right. lia. }
  destruct (store_succeeds_sb m5 sb so 24 env_v
              Hsb_writable_m5 Henv_load_m5 ltac:(lia) ltac:(lia) new_env_v)
    as [m6 Hstore6].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore6 Hsb_writable_m5) as Hsb_writable_m6.

  (* Store 7: extra_args field at (sb, uso+32) <- new_ea_v *)
  set (new_ea := Nat.add (extra_args s) 2).
  set (new_ea_v := Vlong (Int64.add (Int64.repr (Z.of_nat (extra_args s)))
                                     (Int64.repr (Int.signed (Int.repr 2))))).

  assert (Hextra_load_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 32) =
            Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
  { assert (Hextra_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 32)
               (Vptr sp_b new_sp_ofs) _ Hstore1 Hextra_load). right. lia. }
    assert (Hextra_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { erewrite Mem.load_store_other. exact Hextra_m1. exact Hstore2.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Hextra_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { erewrite Mem.load_store_other. exact Hextra_m2. exact Hstore3.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Hextra_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { erewrite Mem.load_store_other. exact Hextra_m3. exact Hstore4.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Hextra_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 32)
               new_pc_v _ Hstore5 Hextra_m4). right. lia. }
    apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 32)
             new_env_v _ Hstore6 Hextra_m5). right. lia. }
  destruct (store_succeeds_sb m6 sb so 32 (Vlong (Int64.repr (Z.of_nat (extra_args s))))
              Hsb_writable_m6 Hextra_load_m6 ltac:(lia) ltac:(lia) new_ea_v)
    as [m7 Hstore7].

  (* Intermediate load facts *)
  (* accu in m1 *)
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8)
             (Vptr sp_b new_sp_ofs) (Vptr accu_b accu_ofs)
             Hstore1 Haccu_load). left. lia. }

  (* sp load in m1 *)
  assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs) Hstore1) as Htmp.
    simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }

  (* arg1 load in m1: stack data survives store to sb (different block) *)
  assert (Hload_sp0_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) = Some cv_arg1).
  { erewrite Mem.load_store_other. exact Hload_sp0. exact Hstore1.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* arg2 load in m1 *)
  assert (Hload_sp1_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 8))) = Some cv_arg2).
  { erewrite Mem.load_store_other. exact Hload_sp1. exact Hstore1.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* arg3 load: the offset from stack_repr inversion is (sp_ofs + 8 + 8), which equals (sp_ofs + 16) *)
  assert (Hload_sp2_flat : Mem.load Mint64 m sp_b (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 16))) = Some cv_arg3).
  { replace (Ptrofs.add sp_ofs (Ptrofs.repr 16))
      with (Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8)).
    exact Hload_sp2.
    rewrite Ptrofs.add_assoc, ptrofs_add_repr. reflexivity. }

  (* arg3 load in m1 *)
  assert (Hload_sp2_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 16))) = Some cv_arg3).
  { erewrite Mem.load_store_other. exact Hload_sp2_flat. exact Hstore1.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* code buffer in m1 *)
  assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
            Some (Vint slotsize_int)).
  { erewrite Mem.load_store_other. exact Hcode_load. exact Hstore1.
    left. exact Hcb_ne. }

  (* accu in m2 *)
  assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { erewrite Mem.load_store_other. exact Haccu_load_m1. exact Hstore2.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* accu in m3 *)
  assert (Haccu_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { erewrite Mem.load_store_other. exact Haccu_load_m2. exact Hstore3.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* accu in m4 *)
  assert (Haccu_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { erewrite Mem.load_store_other. exact Haccu_load_m3. exact Hstore4.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* code pointer from closure in m1: accu_b <> sb *)
  assert (Hcode_ptr_load_m1 : Mem.load Mptr m1 accu_b (Ptrofs.unsigned accu_ofs) =
            Some (Vptr cb code_ofs)).
  { erewrite Mem.load_store_other. exact Hcode_ptr_load. exact Hstore1.
    left. exact Haccu_ne_sb. }

  (* code pointer from closure in m2..m4 *)
  assert (Hcode_ptr_load_m2 : Mem.load Mptr m2 accu_b (Ptrofs.unsigned accu_ofs) =
            Some (Vptr cb code_ofs)).
  { erewrite Mem.load_store_other. exact Hcode_ptr_load_m1. exact Hstore2.
    left. exact Haccu_ne_spb. }
  assert (Hcode_ptr_load_m3 : Mem.load Mptr m3 accu_b (Ptrofs.unsigned accu_ofs) =
            Some (Vptr cb code_ofs)).
  { erewrite Mem.load_store_other. exact Hcode_ptr_load_m2. exact Hstore3.
    left. exact Haccu_ne_spb. }
  assert (Hcode_ptr_load_m4 : Mem.load Mptr m4 accu_b (Ptrofs.unsigned accu_ofs) =
            Some (Vptr cb code_ofs)).
  { erewrite Mem.load_store_other. exact Hcode_ptr_load_m3. exact Hstore4.
    left. exact Haccu_ne_spb. }

  (* accu in m5 *)
  assert (Haccu_load_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 8)
             new_pc_v (Vptr accu_b accu_ofs)
             Hstore5 Haccu_load_m4). right. lia. }

  (* sp load in m1..m4: survived stores to sp_b (same block, but possibly at different offsets) *)
  (* We need s->sp reads from the MODIFIED memory (after store1 which updated sp). *)
  (* In m1, sp field has new_sp_ofs. Need to propagate through stores 2,3,4 *)
  assert (Hsp_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { erewrite Mem.load_store_other. exact Hsp_load_m1. exact Hstore2.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hsp_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { erewrite Mem.load_store_other. exact Hsp_load_m2. exact Hstore3.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hsp_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { erewrite Mem.load_store_other. exact Hsp_load_m3. exact Hstore4.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* Witnesses *)
  set (le1 := PTree.set _t'13 (Vptr sp_b sp_ofs) le).
  set (le2 := PTree.set _arg1 cv_arg1 le1).
  set (le3 := PTree.set _t'12 (Vptr sp_b sp_ofs) le2).
  set (le4 := PTree.set _arg2 cv_arg2 le3).
  set (le5 := PTree.set _t'11 (Vptr sp_b sp_ofs) le4).
  set (le6 := PTree.set _arg3 cv_arg3 le5).
  set (le7 := PTree.set _t'8 (Vptr sp_b sp_ofs) le6).
  set (le8 := PTree.set _t'9 (Vptr cb pc_ofs) le7).
  set (le9 := PTree.set _t'10 (Vint slotsize_int) le8).
  (* After store1 (sp update), read new sp *)
  set (le10 := PTree.set _t'7 (Vptr sp_b new_sp_ofs) le9).
  (* After store2 (arg1 write), read new sp again for arg2 write *)
  set (le11 := PTree.set _t'6 (Vptr sp_b new_sp_ofs) le10).
  (* After store3 (arg2 write), read new sp again for arg3 write *)
  set (le12 := PTree.set _t'5 (Vptr sp_b new_sp_ofs) le11).
  (* Read accu, code pointer, store pc *)
  set (le13 := PTree.set _t'3 (Vptr accu_b accu_ofs) le12).
  set (le14 := PTree.set _t'4 (Vptr cb code_ofs) le13).
  (* Read accu, store env *)
  set (le15 := PTree.set _t'2 (Vptr accu_b accu_ofs) le14).
  (* Read extra_args, store new extra_args *)
  set (le16 := PTree.set _t'1 (Vlong (Int64.repr (Z.of_nat (extra_args s)))) le15).
  exists le16. exists m7.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ================================================================ *)
  (* Part 1: exec -- the C body executes                               *)
  (* ================================================================ *)
  {
    apply (eval_stmt_to_exec clight_ge 50).
    eval_cbn.

    (* S1: Sset _t'13 (s->sp) *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* S2: Sset _arg1 = deref(_t'13 + 0) *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_0; eval_cbn.
    rewrite Hload_sp0; eval_cbn.

    (* S3: Sset _t'12 (s->sp) *)
    rewrite PTree.gso by (compute; congruence).
    rewrite PTree.gso by (compute; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* S4: Sset _arg2 = deref(_t'12 + 1) *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_1; eval_cbn.
    rewrite Hload_sp1; eval_cbn.

    (* S5: Sset _t'11 (s->sp) *)
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* S6: Sset _arg3 = deref(_t'11 + 2) *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_2; eval_cbn.
    rewrite Hload_sp2_flat; eval_cbn.

    (* S7: Sset _t'8 (s->sp) *)
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* S8: Sset _t'9 (s->pc) -- first _pc access, needs Hpc_offset *)
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Hpc_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load; eval_cbn.

    (* S9: Sset _t'10 = deref(_t'9) *)
    rewrite PTree.gss; eval_cbn.
    rewrite Hcode_load; eval_cbn.

    (* S10: Sassign s->sp = _t'8 + _t'10 - 3 *)
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite PTree.gss; eval_cbn.
    fold slotsize_int.
    rewrite (sem_add_sp_n sp_b sp_ofs slotsize_int m); eval_cbn.
    fold sp_plus_slot.
    rewrite (sem_sub_sp_int sp_b sp_plus_slot (Int.repr 3) m); eval_cbn.
    fold new_sp_ofs.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hstore1; eval_cbn.

    (* S11: Sset _t'7 (s->sp) -- read NEW sp in m1 *)
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m1; eval_cbn.

    (* S12: Sassign deref(_t'7 + 0) = _arg1 *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_0; eval_cbn.
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hval_repr_arg1); eval_cbn.
    rewrite Hstore2; eval_cbn.

    (* S13: Sset _t'6 (s->sp) -- read NEW sp in m2 *)
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m2; eval_cbn.

    (* S14: Sassign deref(_t'6 + 1) = _arg2 *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_1; eval_cbn.
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hval_repr_arg2); eval_cbn.
    rewrite Hsp1_ptrofs.
    rewrite Hstore3; eval_cbn.

    (* S15: Sset _t'5 (s->sp) -- read NEW sp in m3 *)
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m3; eval_cbn.

    (* S16: Sassign deref(_t'5 + 2) = _arg3 *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_2; eval_cbn.
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hval_repr_arg3); eval_cbn.
    rewrite Hsp2_ptrofs.
    rewrite Hstore4; eval_cbn.

    (* S17: Sset _t'3 (s->accu) in m4 *)
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Haccu_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m4; eval_cbn.

    (* S18: Sset _t'4 = deref(cast(_t'3) + 0) -- code pointer *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_to_ptptint_vptr; eval_cbn.
    rewrite (sem_add_ptptint_0 accu_b accu_ofs m4); eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite Mptr_Mint64 in Hcode_ptr_load_m4.
    rewrite Hcode_ptr_load_m4; eval_cbn.

    (* S19: Sassign s->pc = _t'4 *)
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_ptr_tint_to_ptr_tint; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Mptr_Mint64; eval_cbn.
    fold new_pc_v.
    rewrite Hstore5; eval_cbn.

    (* S20: Sset _t'2 (s->accu) -- read accu in m5 *)
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m5; eval_cbn.

    (* S21: Sassign s->env = _t'2 *)
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Henv_offset; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_vptr accu_b accu_ofs m5); eval_cbn.
    rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
    fold new_env_v.
    rewrite Hstore6; eval_cbn.

    (* S22: Sset _t'1 (s->extra_args) -- read extra_args in m6 *)
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Hextra_offset; eval_cbn.
    rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
    rewrite Hextra_load_m6; eval_cbn.

    (* S23: Sassign s->extra_args = _t'1 + 2 *)
    repeat (rewrite PTree.gso by (compute; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_long_int (Int64.repr (Z.of_nat (extra_args s))) (Int.repr 2) m6); eval_cbn.
    rewrite (sem_cast_long_to_long _ m6); eval_cbn.
    rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
    fold new_ea_v.
    rewrite Hstore7; eval_cbn.

    (* Sreturn 0 *)
    subst le16 le15 le14 le13 le12 le11 le10 le9 le8 le7 le6 le5 le4 le3 le2 le1. reflexivity.
  }

  (* ================================================================ *)
  (* Part 2: abs_rel for post-state                                    *)
  (* ================================================================ *)
  {
    set (uso := Ptrofs.unsigned so) in *.
    set (ard' := mk_abs_rel sb so hm cb new_co
                   (ar_global_block ard) (ar_global_ofs ard)
                   (ar_stack_block ard) (ar_stack_base_ofs ard)
                   (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard)
                   (ar_sptr_ofs_bound ard)).
    exists ard'.

    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore7 Hsb_writable_m6) as Hsb_writable_m7.

    (* Loads in final memory m7 *)

    (* pc at uso+0: written in store5, survived store6 at +24, store7 at +32 *)
    assert (Hpc_load7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
    { assert (Hpc_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
      { pose proof (load_after_store_same m4 m5 sb (Ptrofs.unsigned so + 0) new_pc_v Hstore5) as Htmp.
        unfold new_pc_v in Htmp. simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp.
        exact Htmp. }
      assert (Hpc_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
      { apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 0)
                 new_env_v new_pc_v Hstore6 Hpc_m5). left. lia. }
      apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 0)
               new_ea_v new_pc_v Hstore7 Hpc_m6). left. lia. }

    (* accu at uso+8: unaffected by all stores *)
    assert (Haccu_load7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 8) =
              Some (Vptr accu_b accu_ofs)).
    { assert (Haccu_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 8) =
                Some (Vptr accu_b accu_ofs)).
      { exact Haccu_load_m5. }
      assert (Haccu_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 8) =
                Some (Vptr accu_b accu_ofs)).
      { apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 8)
                 new_env_v (Vptr accu_b accu_ofs) Hstore6 Haccu_m5). left. lia. }
      apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 8)
               new_ea_v (Vptr accu_b accu_ofs) Hstore7 Haccu_m6). left. lia. }

    (* sp at uso+16: written in store1, survived stores 2-7 *)
    assert (Hsp_load7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 16) =
              Some (Vptr sp_b new_sp_ofs)).
    { assert (Hsp_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 16) =
                Some (Vptr sp_b new_sp_ofs)).
      { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
                 new_pc_v (Vptr sp_b new_sp_ofs) Hstore5 Hsp_load_m4). right. lia. }
      assert (Hsp_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 16) =
                Some (Vptr sp_b new_sp_ofs)).
      { apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 16)
                 new_env_v (Vptr sp_b new_sp_ofs) Hstore6 Hsp_m5). left. lia. }
      apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 16)
               new_ea_v (Vptr sp_b new_sp_ofs) Hstore7 Hsp_m6). left. lia. }

    (* env at uso+24: written in store6 *)
    assert (Henv_load7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 24) = Some new_env_v).
    { assert (Henv_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 24) = Some new_env_v).
      { pose proof (load_after_store_same m5 m6 sb (Ptrofs.unsigned so + 24) new_env_v Hstore6) as Htmp.
        unfold new_env_v in Htmp. simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp.
        exact Htmp. }
      apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 24)
               new_ea_v new_env_v Hstore7 Henv_m6). left. lia. }

    (* extra_args at uso+32: written in store7 *)
    assert (Hextra_load7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 32) = Some new_ea_v).
    { pose proof (load_after_store_same m6 m7 sb (Ptrofs.unsigned so + 32) new_ea_v Hstore7) as Htmp.
      unfold new_ea_v in Htmp. rewrite load_result_vlong in Htmp.
      exact Htmp. }

    (* global_data at uso+40 *)
    assert (Hgd_load7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
    { assert (Hgd_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 40)
                 (Vptr sp_b new_sp_ofs) gd_ptr Hstore1 Hgd_load). right. lia. }
      assert (Hgd_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
      { erewrite Mem.load_store_other. exact Hgd_m1. exact Hstore2.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hgd_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
      { erewrite Mem.load_store_other. exact Hgd_m2. exact Hstore3.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hgd_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
      { erewrite Mem.load_store_other. exact Hgd_m3. exact Hstore4.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hgd_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
      { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 40)
                 new_pc_v gd_ptr Hstore5 Hgd_m4). right. lia. }
      assert (Hgd_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
      { apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 40)
                 new_env_v gd_ptr Hstore6 Hgd_m5). right. lia. }
      apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 40)
               new_ea_v gd_ptr Hstore7 Hgd_m6). right. lia. }

    (* trap_sp at uso+48 *)
    assert (Hts_load7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
    { assert (Hts_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 48)
                 (Vptr sp_b new_sp_ofs) ts_ptr Hstore1 Hts_load). right. lia. }
      assert (Hts_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { erewrite Mem.load_store_other. exact Hts_m1. exact Hstore2.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hts_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { erewrite Mem.load_store_other. exact Hts_m2. exact Hstore3.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hts_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { erewrite Mem.load_store_other. exact Hts_m3. exact Hstore4.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hts_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 48)
                 new_pc_v ts_ptr Hstore5 Hts_m4). right. lia. }
      assert (Hts_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 48)
                 new_env_v ts_ptr Hstore6 Hts_m5). right. lia. }
      apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 48)
               new_ea_v ts_ptr Hstore7 Hts_m6). right. lia. }

    (* sb_writable in m7 *)
    assert (Hsb_writable_m7' : Mem.range_perm m7 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { exact Hsb_writable_m7. }

    (* Stack repr for post-state: arg1 :: arg2 :: arg3 :: skipn slotsize (arg1 :: arg2 :: arg3 :: stk_rest) *)
    assert (Hstack_m7 :
      stack_repr hm cb co m7 (arg1 :: arg2 :: arg3 :: skipn slotsize (arg1 :: arg2 :: arg3 :: stk_rest)) sp_b new_sp_ofs).
    {
      (* arg1 :: arg2 :: arg3 :: tail -- build stack_repr with econstructor *)
      (* arg1 at new_sp_ofs *)
      econstructor.
      { (* Load arg1 from m7 *)
        assert (Harg1_m2 : Mem.load Mint64 m2 sp_b (Ptrofs.unsigned new_sp_ofs) = Some cv_arg1).
        { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore2) as Htmp.
          rewrite (val_repr_load_result hm cb co arg1 cv_arg1 Hval_repr_arg1) in Htmp.
          exact Htmp. }
        assert (Harg1_m3 : Mem.load Mint64 m3 sp_b (Ptrofs.unsigned new_sp_ofs) = Some cv_arg1).
        { erewrite Mem.load_store_other. exact Harg1_m2. exact Hstore3.
          right. rewrite Hnew_sp_unsigned. unfold size_chunk. lia. }
        assert (Harg1_m4 : Mem.load Mint64 m4 sp_b (Ptrofs.unsigned new_sp_ofs) = Some cv_arg1).
        { erewrite Mem.load_store_other. exact Harg1_m3. exact Hstore4.
          right. rewrite Hnew_sp_unsigned. unfold size_chunk. lia. }
        assert (Harg1_m5 : Mem.load Mint64 m5 sp_b (Ptrofs.unsigned new_sp_ofs) = Some cv_arg1).
        { erewrite Mem.load_store_other. exact Harg1_m4. exact Hstore5.
          left. intro Heq; apply Hsp_ne_sb; auto. }
        assert (Harg1_m6 : Mem.load Mint64 m6 sp_b (Ptrofs.unsigned new_sp_ofs) = Some cv_arg1).
        { erewrite Mem.load_store_other. exact Harg1_m5. exact Hstore6.
          left. intro Heq; apply Hsp_ne_sb; auto. }
        erewrite Mem.load_store_other. exact Harg1_m6. exact Hstore7.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      { eapply val_repr_co_shift; exact Hval_repr_arg1. }

      (* arg2 at new_sp_ofs + 8 *)
      econstructor.
      { rewrite Hsp1_ptrofs.
        assert (Harg2_m3 : Mem.load Mint64 m3 sp_b (Ptrofs.unsigned new_sp_ofs + 8) = Some cv_arg2).
        { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore3) as Htmp.
          rewrite (val_repr_load_result hm cb co arg2 cv_arg2 Hval_repr_arg2) in Htmp.
          exact Htmp. }
        assert (Harg2_m4 : Mem.load Mint64 m4 sp_b (Ptrofs.unsigned new_sp_ofs + 8) = Some cv_arg2).
        { erewrite Mem.load_store_other. exact Harg2_m3. exact Hstore4.
          right. unfold size_chunk. lia. }
        assert (Harg2_m5 : Mem.load Mint64 m5 sp_b (Ptrofs.unsigned new_sp_ofs + 8) = Some cv_arg2).
        { erewrite Mem.load_store_other. exact Harg2_m4. exact Hstore5.
          left. intro Heq; apply Hsp_ne_sb; auto. }
        assert (Harg2_m6 : Mem.load Mint64 m6 sp_b (Ptrofs.unsigned new_sp_ofs + 8) = Some cv_arg2).
        { erewrite Mem.load_store_other. exact Harg2_m5. exact Hstore6.
          left. intro Heq; apply Hsp_ne_sb; auto. }
        erewrite Mem.load_store_other. exact Harg2_m6. exact Hstore7.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      { eapply val_repr_co_shift; exact Hval_repr_arg2. }

      (* arg3 at new_sp_ofs + 16 *)
      econstructor.
      { replace (Ptrofs.add (Ptrofs.add new_sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8))
          with (Ptrofs.add new_sp_ofs (Ptrofs.repr 16))
          by (rewrite Ptrofs.add_assoc, ptrofs_add_repr; reflexivity).
        rewrite Hsp2_ptrofs.
        assert (Harg3_m4 : Mem.load Mint64 m4 sp_b (Ptrofs.unsigned new_sp_ofs + 16) = Some cv_arg3).
        { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore4) as Htmp.
          rewrite (val_repr_load_result hm cb co arg3 cv_arg3 Hval_repr_arg3) in Htmp.
          exact Htmp. }
        assert (Harg3_m5 : Mem.load Mint64 m5 sp_b (Ptrofs.unsigned new_sp_ofs + 16) = Some cv_arg3).
        { erewrite Mem.load_store_other. exact Harg3_m4. exact Hstore5.
          left. intro Heq; apply Hsp_ne_sb; auto. }
        assert (Harg3_m6 : Mem.load Mint64 m6 sp_b (Ptrofs.unsigned new_sp_ofs + 16) = Some cv_arg3).
        { erewrite Mem.load_store_other. exact Harg3_m5. exact Hstore6.
          left. intro Heq; apply Hsp_ne_sb; auto. }
        erewrite Mem.load_store_other. exact Harg3_m6. exact Hstore7.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      { eapply val_repr_co_shift; exact Hval_repr_arg3. }

      (* Tail: skipn slotsize (stack s) at new_sp_ofs + 24 = sp_ofs + slotsize * 8 *)
      replace (Ptrofs.add (Ptrofs.add (Ptrofs.add new_sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8)) (Ptrofs.repr 8))
        with (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat slotsize * 8))).
      2: { rewrite Hnew_sp_eq, !Ptrofs.add_assoc.
           f_equal. rewrite !ptrofs_add_repr. f_equal. lia. }
      rewrite <- Hstk.
      eapply stack_repr_co_shift.
      apply (stack_repr_store_other_block hm cb co m6 m7 _ sp_b _ sb (Ptrofs.unsigned so + 32) new_ea_v).
      { apply (stack_repr_store_other_block hm cb co m5 m6 _ sp_b _ sb (Ptrofs.unsigned so + 24) new_env_v).
        { apply (stack_repr_store_other_block hm cb co m4 m5 _ sp_b _ sb (Ptrofs.unsigned so + 0) new_pc_v).
          { apply (stack_repr_store_same_block_lower hm cb co m3 m4 _ sp_b _
                     (Ptrofs.unsigned new_sp_ofs + 16) cv_arg3).
            { apply (stack_repr_store_same_block_lower hm cb co m2 m3 _ sp_b _
                       (Ptrofs.unsigned new_sp_ofs + 8) cv_arg2).
              { apply (stack_repr_store_same_block_lower hm cb co m1 m2 _ sp_b _
                         (Ptrofs.unsigned new_sp_ofs) cv_arg1).
                { eapply stack_repr_co_shift.
                apply (stack_repr_store_other_block hm cb co m m1 _ sp_b
                           (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat slotsize * 8)))
                           sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)).
                  { exact (stack_repr_skipn slotsize hm cb co m (Machine.stack s) sp_b sp_ofs
                             (eq_ind _ (fun stk => stack_repr hm cb co m stk sp_b sp_ofs) Hstack_repr _ (eq_sym Hstk))). }
                  { exact Hstore1. }
                  { intro Heq; apply Hsp_ne_sb; auto. } }
                { exact Hstore2. }
                { rewrite Hnew_sp_unsigned.
                  rewrite ptrofs_add_unsigned; [lia | lia | lia]. }
                { rewrite length_skipn. rewrite Hstk. simpl length.
                  rewrite ptrofs_add_unsigned; [| lia | lia].
                  rewrite Nat2Z.inj_sub by exact Hslot_le_len.
                  rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. } }
              { exact Hstore3. }
              { rewrite Hnew_sp_unsigned.
                rewrite ptrofs_add_unsigned; [lia | lia | lia]. }
              { rewrite length_skipn. rewrite Hstk. simpl length.
                rewrite ptrofs_add_unsigned; [| lia | lia].
                rewrite Nat2Z.inj_sub by exact Hslot_le_len.
                rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. } }
            { exact Hstore4. }
            { rewrite Hnew_sp_unsigned.
              rewrite ptrofs_add_unsigned; [lia | lia | lia]. }
            { rewrite length_skipn. rewrite Hstk. simpl length.
              rewrite ptrofs_add_unsigned; [| lia | lia].
              rewrite Nat2Z.inj_sub by exact Hslot_le_len.
              rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. } }
          { exact Hstore5. }
          { intro Heq; apply Hsp_ne_sb; auto. } }
        { exact Hstore6. }
        { intro Heq; apply Hsp_ne_sb; auto. } }
      { exact Hstore7. }
      { intro Heq; apply Hsp_ne_sb; auto. }
    }

    (* le16 ! _s *)
    assert (Hle16_s : le16 ! _s = Some (Vptr sb so)).
    { subst le16 le15 le14 le13 le12 le11 le10 le9 le8 le7 le6 le5 le4 le3 le2 le1.
      repeat (rewrite PTree.gso by (compute; congruence)).
      exact Hle_s. }

    (* The new extra_args value matches *)
    assert (Hnew_ea_eq : new_ea_v = Vlong (Int64.repr (Z.of_nat new_ea))).
    { unfold new_ea_v, new_ea.
      f_equal.
      apply appterm3_add_ea; assumption. }

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le' *)
    { exact Hle16_s. }

    (* 2. pc field -- updated to new_pc_v *)
    { exists new_pc_v. split.
      - exact Hpc_load7.
      - simpl. unfold pc_rel, new_pc_v. f_equal.
        subst code_ofs. reflexivity. }

    (* 3. accu field -- unchanged *)
    { exists (Vptr accu_b accu_ofs). split.
      - exact Haccu_load7.
      - simpl. eapply val_repr_co_shift; exact Haccu_repr. }

    (* 4. sp field -- updated *)
    { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load7.
      - reflexivity.
      - simpl stack. eapply stack_repr_co_shift. exact Hstack_m7.
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - (* sp_ge8 *) rewrite Hnew_sp_unsigned. lia.
      - (* sp_rep *)
        simpl stack.
        change (Datatypes.length (arg1 :: arg2 :: arg3 :: skipn slotsize (arg1 :: arg2 :: arg3 :: stk_rest)))
          with (S (S (S (Datatypes.length (skipn slotsize (arg1 :: arg2 :: arg3 :: stk_rest)))))).
        rewrite length_skipn. simpl length.
        rewrite Hnew_sp_unsigned.
        rewrite Hstk in Hsp_rep. simpl length in Hsp_rep.
        simpl length in Hslot_le_len. zify. lia.
      - (* sp_writable *)
        simpl stack. simpl length.
        change (Datatypes.length (arg1 :: arg2 :: arg3 :: skipn slotsize (arg1 :: arg2 :: arg3 :: stk_rest)))
          with (S (S (S (Datatypes.length (skipn slotsize (arg1 :: arg2 :: arg3 :: stk_rest)))))).
        rewrite length_skipn. simpl length.
        rewrite Hnew_sp_unsigned.
        replace (Ptrofs.unsigned sp_ofs + (Z.of_nat slotsize - 3) * 8 +
                  8 * Z.of_nat (S (S (S (S (S (S (Datatypes.length stk_rest))) - slotsize)))))
          with (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (S (S (S (Datatypes.length stk_rest))))).
        2: { simpl length in Hslot_le_len. zify. lia. }
        intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore7.
        eapply Mem.perm_store_1. exact Hstore6.
        eapply Mem.perm_store_1. exact Hstore5.
        eapply Mem.perm_store_1. exact Hstore4.
        eapply Mem.perm_store_1. exact Hstore3.
        eapply Mem.perm_store_1. exact Hstore2.
        eapply Mem.perm_store_1. exact Hstore1.
        apply Hsp_writable. rewrite Hstk. simpl length. exact Hofs'.
      - rewrite Hnew_sp_unsigned.
        apply Z.divide_add_r. exact Hsp_align. exists (Z.of_nat slotsize - 3). simpl. lia. }

    (* 5. env field -- updated to accu *)
    { exists new_env_v. split.
      - exact Henv_load7.
      - simpl. eapply val_repr_co_shift; exact Haccu_repr. }

    (* 6. extra_args field -- updated *)
    { simpl. rewrite Hnew_ea_eq in Hextra_load7. exact Hextra_load7. }

    (* 7. global_data field -- unchanged *)
    { exists gd_ptr. split; [| split; [| split]].
      - exact Hgd_load7.
      - simpl. exact Hgd_eq.
      - simpl.
        eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m6 m7 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (Ptrofs.unsigned so + 32) new_ea_v).
        + eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m5 m6 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sb (Ptrofs.unsigned so + 24) new_env_v).
          * eapply global_repr_co_shift.
          apply (global_repr_store_other_block hm cb co m4 m5 _
                     (ar_global_block ard) (ar_global_ofs ard)
                     sb (Ptrofs.unsigned so + 0) new_pc_v).
            { eapply global_repr_co_shift.
            apply (global_repr_store_other_block hm cb co m3 m4 _
                       (ar_global_block ard) (ar_global_ofs ard)
                       sp_b (Ptrofs.unsigned new_sp_ofs + 16) cv_arg3).
              { eapply global_repr_co_shift.
              apply (global_repr_store_other_block hm cb co m2 m3 _
                         (ar_global_block ard) (ar_global_ofs ard)
                         sp_b (Ptrofs.unsigned new_sp_ofs + 8) cv_arg2).
                { eapply global_repr_co_shift.
                apply (global_repr_store_other_block hm cb co m1 m2 _
                           (ar_global_block ard) (ar_global_ofs ard)
                           sp_b (Ptrofs.unsigned new_sp_ofs) cv_arg1).
                  { eapply global_repr_co_shift.
                  apply (global_repr_store_other_block hm cb co m m1 _
                             (ar_global_block ard) (ar_global_ofs ard)
                             sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)).
                    exact Hglobal_repr. exact Hstore1.
                    intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)). }
                  { exact Hstore2. }
                  { intro Heq2; exact (Hsp_ne_gb Heq2). } }
                { exact Hstore3. }
                { intro Heq2; exact (Hsp_ne_gb Heq2). } }
              { exact Hstore4. }
              { intro Heq2; exact (Hsp_ne_gb Heq2). } }
            { exact Hstore5. }
            { intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)). }
          * exact Hstore6.
          * intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
        + exact Hstore7.
        + intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load7.
      - simpl. exact Htrap_rel. }

    (* 9. sb_writable *)
    { exact Hsb_writable_m7'. }
  }
Qed.

(* ================================================================== *)
(* Wrapper: bridge verify_APPTERM3_correct to the InstructSpec form    *)
(* ================================================================== *)

Import Bytecode.AST.

Theorem correct_APPTERM3 : forall n,
    handler_correct (handle_instr (APPTERM3 n)) (clight_of (APPTERM3 n))
      (pre_of (APPTERM3 n))
      (P_error_of (APPTERM3 n)) (P_halt_of (APPTERM3 n)) (P_ccall_of (APPTERM3 n)).
Proof.
  intro n.
  unfold handler_correct.
  intros e le m s.
  change (handle_instr (APPTERM3 n) (Machine.pc s) s)
    with (handle_APPTERM3 n s).
  unfold handle_APPTERM3.
  destruct (Machine.stack s) as [| arg1 rest] eqn:Hstk.
  - (* Error case: stack = nil *)
    unfold P_error_of, error_message_of. rewrite Hstk. reflexivity.
  - destruct rest as [| arg2 rest2] eqn:Hrest.
    + (* Error case: stack = [arg1] *)
      unfold P_error_of, error_message_of. rewrite Hstk. reflexivity.
    + destruct rest2 as [| arg3 rest3] eqn:Hrest2.
      * (* Error case: stack = [arg1; arg2] *)
        unfold P_error_of, error_message_of. rewrite Hstk. reflexivity.
      * destruct (get_code_ptr_s s s.(Machine.accu)) as [target_pc|] eqn:Hgcp.
        -- (* Step case: delegate to verify_APPTERM3_correct *)
           intros ard Habs Hpre.
           pose proof (verify_APPTERM3_correct n) as Hverify.
           unfold handler_correct in Hverify.
           specialize (Hverify e le m s).
           unfold handle_APPTERM3 in Hverify.
           rewrite Hstk in Hverify. rewrite Hgcp in Hverify.
           apply (Hverify ard); [exact Habs |].
           (* Bridge: pre_of (APPTERM3 n) uses apply3_closure_pre;
              verify uses the local appterm3_step_pre.
              These are definitionally identical after unfolding. *)
           change (pre_of (APPTERM3 n)) with (InstructSpec.appterm3_step_pre n) in Hpre.
           unfold InstructSpec.appterm3_step_pre in Hpre.
           unfold apply3_closure_pre in Hpre.
           destruct Hpre as (Hcode & Hbound & Hfits & Hge8 & Hge3 & Hlen & Hclosure & Hextra_u & Hextra_s).
           refine (conj Hcode (conj Hbound (conj Hfits (conj Hge8 (conj Hge3 (conj _ (conj _ (conj Hextra_u Hextra_s)))))))).
           { rewrite Hstk in Hlen. exact Hlen. }
           { intros sp_b sp_ofs Hsp_load.
             specialize (Hclosure sp_b sp_ofs Hsp_load).
             unfold appterm3_step_pre.
             exact Hclosure. }
        -- (* Error case: get_code_ptr_s = None *)
           unfold P_error_of, error_message_of. rewrite Hstk. rewrite Hgcp. reflexivity.
Qed.
