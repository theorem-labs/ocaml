(* SETFIELD_correct.v -- SETFIELD (parametric) correctness proof.

   SETFIELD n: reads field index n from the code buffer, pops the
   stack top (new value), reads accu as a heap pointer, calls
   caml_modify to write the new value to heap field n, sets
   accu = val_unit, advances pc by 1.

   Rocq handler:
     handle_SETFIELD n pc' s =
       match stack with
       | newval :: rest =>
         match accu with
         | Val_ptr addr =>
           match heap_lookup hp addr with
           | Some (_, fields) =>
             match set_nth fields n newval with
             | Some new_fields => Step (s <|pc:=pc'|> <|accu:=val_unit|>
                                          <|stack:=rest|> <|hp:=heap_update ...|>)
             | None => Error "index out of bounds"
             end
           | None => Error "dangling pointer"
           end
         | _ => Error "not a mutable block"
         end
       | _ => Error "stack underflow"
       end

   C handler (f_instr_SETFIELD):
     _t'1 = s->sp;               // read sp
     s->sp = _t'1 + 1;           // sp++ (pop)
     _t'3 = s->accu;             // read accu (tlong)
     _t'4 = s->pc;               // read pc
     _t'5 = *_t'4;               // read field index n from code buffer
     _t'6 = *_t'1;               // read stack top
     caml_modify(cast(_t'3) + _t'5, _t'6);   // heap write via caml_modify
     s->accu = ((0 << 1) + 1);   // val_unit = 1
     _t'2 = s->pc;               // read pc
     s->pc = _t'2 + 1;           // advance pc
     return 0;

   Combines SETFIELD0 (sp pop + heap write + val_unit) and
   SETGLOBAL (caml_modify external call + code buffer read + pc advance).

   NO AXIOMS.  NO ADMITTED. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
Require Import instruct_handlers.
Require Import InstructSpec.
Require Import StepToBigstep.
Require Import HandlerLemmas.

Local Notation ge := clight_ge.

(* ================================================================== *)
(* Struct layout facts                                                 *)
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

Local Lemma interp_state_co_setfield : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* caml_modify definitions                                             *)
(* ================================================================== *)

Definition caml_modify_ef : external_function :=
  EF_external "caml_modify"
    (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid cc_default).

Definition caml_modify_fundef : Ctypes.fundef function :=
  Ctypes.External caml_modify_ef ((tptr tlong) :: tlong :: nil) tvoid cc_default.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_add_ptr_int_n : forall b ofs n_int m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong)
    (Vint n_int) tint
    m = Some (Vptr b (Ptrofs.add ofs
                (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tlong))
                            (ptrofs_of_int Signed n_int)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

Local Lemma pc_rel_shift : forall cb co rocq_pc,
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
(* The target address for caml_modify: accu_ptr + n                    *)
(* ================================================================== *)

Definition heap_field_target (hofs : ptrofs) (n_int : int) : ptrofs :=
  Ptrofs.add hofs (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tlong))
                               (ptrofs_of_int Signed n_int)).

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_SETFIELD_correct : forall n,
    handler_correct (handle_SETFIELD n) f_instr_SETFIELD
      (fun e m s ard =>
         let cb := ar_code_base_block ard in
         let co := ar_code_base_ofs ard in
         let sb := ar_sptr_block ard in
         let so := ar_sptr_ofs ard in
         let hm := ar_heap_map ard in
         let cb := ar_code_base_block ard in
         let co := ar_code_base_ofs ard in
         (* 0. e does not bind _caml_modify *)
         e ! _caml_modify = None /\
         (* 1. Code buffer contains Z.of_nat n at current PC *)
         Mem.load Mint32 m cb
           (Ptrofs.unsigned (Ptrofs.add co
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* 2. n fits in int32 signed range *)
         Int.min_signed <= Z.of_nat n <= Int.max_signed /\
         (* 3. Genv lookup for caml_modify *)
         (exists b_cm,
            Genv.find_symbol ge _caml_modify = Some b_cm /\
            Genv.find_funct ge (Vptr b_cm Ptrofs.zero) = Some caml_modify_fundef) /\
         (* 4. caml_modify external call: for the actual values,
            there exists m_cm witnessing the call with empty trace *)
         (forall newval rest,
            Machine.stack s = newval :: rest ->
            forall accu_v,
              val_repr hm cb co (Machine.accu s) accu_v ->
            forall sp_b sp_ofs,
              Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
            forall stk_top_cv,
              val_repr hm cb co newval stk_top_cv ->
            exists hb hofs,
              accu_v = Vptr hb hofs /\
              hb <> sb /\
              hb <> sp_b /\
              hb <> ar_global_block ard /\
              hb <> cb /\
              (* sp pop store succeeds *)
              (exists m_sp,
                Mem.store Mint64 m sb (Ptrofs.unsigned so + 16)
                  (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))) = Some m_sp /\
                (* stack top survives sp store *)
                Mem.load Mint64 m_sp sp_b (Ptrofs.unsigned sp_ofs) = Some stk_top_cv /\
                (* accu survives sp store *)
                Mem.load Mint64 m_sp sb (Ptrofs.unsigned so + 8) = Some (Vptr hb hofs) /\
                (* pc survives sp store *)
                Mem.load Mint64 m_sp sb (Ptrofs.unsigned so + 0) =
                  Some (Vptr cb (Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t)))) /\
                (* caml_modify call succeeds *)
                (exists m_cm,
                  external_call caml_modify_ef ge
                    (Vptr hb (heap_field_target hofs (Int.repr (Z.of_nat n)))
                     :: stk_top_cv :: nil)
                    m_sp E0 Vundef m_cm /\
                  (* sb loads preserved through caml_modify *)
                  (forall ofs v,
                     Mem.load Mint64 m_sp sb ofs = Some v ->
                     Mem.load Mint64 m_cm sb ofs = Some v) /\
                  (* sb stores succeed in m_cm *)
                  (forall ofs v_old v_new,
                     Mem.load Mint64 m_sp sb ofs = Some v_old ->
                     exists m', Mem.store Mint64 m_cm sb ofs v_new = Some m') /\
                  (* sp_b loads preserved (sp_b <> hb) *)
                  (forall ofs v,
                     Mem.load Mint64 m_sp sp_b ofs = Some v ->
                     Mem.load Mint64 m_cm sp_b ofs = Some v) /\
                  (* cb loads preserved (cb <> hb) *)
                  (forall ofs v,
                     Mem.load Mint32 m_sp cb ofs = Some v ->
                     Mem.load Mint32 m_cm cb ofs = Some v) /\
                  (* global_repr preserved (gb <> hb) *)
                  (global_repr hm cb co m_cm
                     (Machine.global s) (ar_global_block ard) (ar_global_ofs ard)) /\
                  (* Permission preservation *)
                  (forall b ofs k p,
                     Mem.valid_block m_sp b -> Mem.perm m_sp b ofs k p ->
                     Mem.perm m_cm b ofs k p)))))
      (fun _ s => match s.(Machine.stack) with
                  | newval :: _ =>
                    match s.(Machine.accu) with
                    | Val_ptr addr =>
                      match heap_lookup s.(Machine.hp) addr with
                      | Some (_, fields) => set_nth fields n newval = None
                      | None => True
                      end
                    | _ => True
                    end
                  | _ => True end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro n.
  intros e le m s.
  unfold handle_SETFIELD.

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
    simpl. reflexivity. }

  (* ================================================================ *)
  (* Step case: stack = newval :: rest, accu = Val_ptr addr,           *)
  (*            heap_lookup = Some (tag, fields), set_nth = Some       *)
  (* ================================================================ *)
  {
    intros ard Hpre Hstep_pre.
    unfold abs_rel_with_ard in Hpre.

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
    subst sp_ptr.

    destruct Hstep_pre as (He_caml & Hcode_load & Hn_range & [b_cm [Hfind_symbol Hfind_funct]] & Hcaml_pre).

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
    pose proof (code_block_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

    (* Composite environment facts *)
    destruct interp_state_co_setfield as [co_is [Hco [Hpc_offset [Haccu_offset Hsp_offset]]]].

    (* Subst pc_ptr to concrete form *)
    unfold pc_rel in Hpc_rel. subst pc_ptr gd_ptr.
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

    (* Stack repr: extract head *)
    rewrite Hstk in Hstack_repr.
    inversion Hstack_repr as [| ? ? ? ? stk_top_cv Hload_sp0 Hval_repr_top Hstack_repr_rest].
    (* Protect gd variables from bare subst *)
    revert Hgd_load Hglobal_repr.
    subst.
    intros Hgd_load Hglobal_repr.

    (* Stack bounds *)
    assert (Hsp_mod_orig : Ptrofs.unsigned sp_ofs + 8 < Ptrofs.modulus).
    { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }
    assert (Hsp_rep_tail : Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length rest) < Ptrofs.modulus).
    { rewrite Hstk in Hsp_rep. simpl length in Hsp_rep. lia. }

    (* Use heap precondition *)
    rewrite Haccu_eq in Haccu_repr.
    specialize (Hcaml_pre newval rest eq_refl accu_v Haccu_repr sp_b sp_ofs Hsp_load stk_top_cv Hval_repr_top).
    destruct Hcaml_pre as [hb [hofs [Haccu_is_ptr [Hhb_ne_sb [Hhb_ne_sp [Hhb_ne_gb [Hhb_ne_cb
      [m_sp [Hstore_sp [Hload_sp0_msp [Haccu_load_msp [Hpc_load_msp Hcaml_call]]]]]]]]]]]].
    subst accu_v.

    destruct Hcaml_call as [m_cm [Hext_call [Hcm_sb_loads [Hcm_sb_stores [Hcm_sp_loads [Hcm_cb_loads [Hcm_global_repr Hcm_perm]]]]]]].

    (* ============================================================ *)
    (* Store 1: accu field (so+8) <- val_unit                        *)
    (* ============================================================ *)
    set (unit_v := Vlong (Int64.repr 1)).

    (* sb_writable in m_cm *)
    assert (Hsb_writable_msp : Mem.range_perm m_sp sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore_sp. apply Hsb_writable. exact Hofs'. }
    assert (Hsb_writable_cm : Mem.range_perm m_cm sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs' Hofs'. apply Hcm_perm.
      - eapply Mem.perm_valid_block. apply Hsb_writable_msp. exact Hofs'.
      - apply Hsb_writable_msp. exact Hofs'. }

    (* Accu load in m_cm *)
    assert (Haccu_load_cm : Mem.load Mint64 m_cm sb (Ptrofs.unsigned so + 8) = Some (Vptr hb hofs)).
    { apply Hcm_sb_loads. exact Haccu_load_msp. }

    destruct (Hcm_sb_stores (Ptrofs.unsigned so + 8) (Vptr hb hofs) unit_v Haccu_load_msp)
      as [m1 Hstore1].

    (* ============================================================ *)
    (* Store 2: pc field (so+0) <- pc + 4                            *)
    (* ============================================================ *)
    set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
    set (new_pc_v := Vptr cb new_pc_ofs).

    (* pc load in m1 *)
    assert (Hpc_load_cm : Mem.load Mint64 m_cm sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { apply Hcm_sb_loads. exact Hpc_load_msp. }
    assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { apply (load_after_store_other m_cm m1 sb (Ptrofs.unsigned so + 8)
               (Ptrofs.unsigned so + 0) unit_v (Vptr cb pc_ofs)
               Hstore1 Hpc_load_cm). left. lia. }

    (* sb_writable in m1 *)
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable_cm) as Hsb_writable_m1.
    destruct (store_succeeds_sb m1 sb so 0 (Vptr cb pc_ofs) Hsb_writable_m1 Hpc_load_m1 ltac:(lia) ltac:(lia) new_pc_v)
      as [m2 Hstore2].

    (* ============================================================ *)
    (* Witnesses                                                     *)
    (* ============================================================ *)

    (* Build the temp env for the proof *)
    set (le1 := PTree.set _t'1 (Vptr sp_b sp_ofs) le).
    set (le2 := PTree.set _t'3 (Vptr hb hofs) le1).
    set (le3 := PTree.set _t'4 (Vptr cb pc_ofs) le2).
    set (le4 := PTree.set _t'5 (Vint (Int.repr (Z.of_nat n))) le3).
    set (le5 := PTree.set _t'6 stk_top_cv le4).
    set (le6 := le5). (* Scall with optid=None doesn't change le *)
    set (le7 := PTree.set _t'2 (Vptr cb pc_ofs) le6).

    exists le7. exists m2.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec_stmt derivation (manual bigstep)                   *)
    (* ============================================================== *)
    {
      (* Body structure:
         Ssequence
           (Ssequence                          -- Part A: sp pop + reads + caml_modify
             (Ssequence
               (Sset _t'1 (s->sp))
               (Sassign (s->sp) (_t'1 + 1)))   -- sp pop
             (Ssequence
               (Sset _t'3 (s->accu))
               (Ssequence
                 (Sset _t'4 (s->pc))
                 (Ssequence
                   (Sset _t'5 (deref _t'4))
                   (Ssequence
                     (Sset _t'6 (deref _t'1))
                     (Scall None caml_modify [cast(_t'3)+_t'5; _t'6]))))))
           (Ssequence                          -- Part B: assign accu, advance pc, return
             (Sassign (s->accu) val_unit_expr)
             (Ssequence
               (Ssequence
                 (Sset _t'2 (s->pc))
                 (Sassign (s->pc) (_t'2 + 1)))
               (Sreturn 0))) *)

      apply exec_Sseq_1 with (t1 := E0) (le1 := le6) (m1 := m_cm).

      (* -- Part A: sp pop + reads + caml_modify call -- *)
      {
        apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m_sp).

        (* Sset _t'1 ; Sassign sp *)
        {
          apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m).

          (* Sset _t'1 (s->sp) *)
          {
            apply exec_Sset.
            eapply eval_Elvalue.
            - eapply eval_Efield_struct.
              + eapply eval_Elvalue.
                * eapply eval_Ederef. eapply eval_Etempvar. exact Hle_s.
                * apply deref_loc_copy. simpl. reflexivity.
              + simpl. reflexivity.
              + exact Hco.
              + exact Hsp_offset.
            - apply deref_loc_value with (chunk := Mptr).
              * simpl. reflexivity.
              * simpl. rewrite Mptr_Mint64.
                rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
                exact Hsp_load.
          }

          (* Sassign (s->sp) (_t'1 + 1) -- store: sp pop *)
          {
            apply exec_Sassign with (loc := sb)
              (ofs := Ptrofs.add so (Ptrofs.repr 16))
              (bf := Full)
              (v2 := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)))
              (v := Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
            - eapply eval_Efield_struct.
              + eapply eval_Elvalue.
                * eapply eval_Ederef.
                  eapply eval_Etempvar.
                  subst le1. rewrite PTree.gso by (compute; congruence). exact Hle_s.
                * apply deref_loc_copy. simpl. reflexivity.
              + simpl. reflexivity.
              + exact Hco.
              + exact Hsp_offset.
            - eapply eval_Ebinop.
              + eapply eval_Etempvar.
                subst le1. rewrite PTree.gss. reflexivity.
              + apply eval_Econst_int.
              + apply sem_add_sp_1.
            - apply sem_cast_ptr_to_ptr.
            - apply assign_loc_value with (chunk := Mptr).
              + simpl. reflexivity.
              + simpl. rewrite Mptr_Mint64.
                rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
                exact Hstore_sp.
          }
        }

        (* Sset _t'3 ; rest *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le2) (m1 := m_sp).
        {
          apply exec_Sset.
          eapply eval_Elvalue.
          - eapply eval_Efield_struct.
            + eapply eval_Elvalue.
              * eapply eval_Ederef.
                eapply eval_Etempvar.
                subst le1. rewrite PTree.gso by (compute; congruence). exact Hle_s.
              * apply deref_loc_copy. simpl. reflexivity.
            + simpl. reflexivity.
            + exact Hco.
            + exact Haccu_offset.
          - apply deref_loc_value with (chunk := Mint64).
            * simpl. reflexivity.
            * simpl.
              rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
              exact Haccu_load_msp.
        }

        (* Sset _t'4 ; rest *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le3) (m1 := m_sp).
        {
          apply exec_Sset.
          eapply eval_Elvalue.
          - eapply eval_Efield_struct.
            + eapply eval_Elvalue.
              * eapply eval_Ederef.
                eapply eval_Etempvar.
                subst le2 le1.
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                exact Hle_s.
              * apply deref_loc_copy. simpl. reflexivity.
            + simpl. reflexivity.
            + exact Hco.
            + exact Hpc_offset.
          - apply deref_loc_value with (chunk := Mptr).
            * simpl. reflexivity.
            * simpl. rewrite Mptr_Mint64.
              rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
              exact Hpc_load_msp.
        }

        (* Sset _t'5 ; rest *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m_sp).
        {
          apply exec_Sset.
          eapply eval_Elvalue.
          - eapply eval_Ederef.
            eapply eval_Etempvar.
            subst le3. rewrite PTree.gss. reflexivity.
          - apply deref_loc_value with (chunk := Mint32).
            * simpl. reflexivity.
            * simpl.
              (* Code buffer load in m_sp: cb <> sb so store to sb preserves it *)
              assert (Hcode_load_msp : Mem.load Mint32 m_sp cb
                        (Ptrofs.unsigned pc_ofs) = Some (Vint (Int.repr (Z.of_nat n)))).
              { erewrite Mem.load_store_other.
                - exact Hcode_load.
                - exact Hstore_sp.
                - left. exact Hcb_ne. }
              exact Hcode_load_msp.
        }

        (* Sset _t'6 ; Scall *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le5) (m1 := m_sp).
        {
          apply exec_Sset.
          eapply eval_Elvalue.
          - eapply eval_Ederef.
            eapply eval_Etempvar.
            subst le4 le3 le2 le1.
            rewrite PTree.gso by (compute; congruence).
            rewrite PTree.gso by (compute; congruence).
            rewrite PTree.gso by (compute; congruence).
            rewrite PTree.gss. reflexivity.
          - apply deref_loc_value with (chunk := Mint64).
            * simpl. reflexivity.
            * simpl. exact Hload_sp0_msp.
        }

        (* Scall None caml_modify [cast(_t'3)+_t'5; _t'6] *)
        {
          eapply exec_Scall with
            (tyargs := (tptr tlong) :: tlong :: nil)
            (tyres := tvoid)
            (cconv := cc_default)
            (vargs := Vptr hb (heap_field_target hofs (Int.repr (Z.of_nat n)))
                      :: stk_top_cv :: nil)
            (vres := Vundef).
          - (* classify_fun *)
            simpl. reflexivity.
          - (* eval_expr for Evar _caml_modify *)
            eapply eval_Elvalue.
            + eapply eval_Evar_global.
              * exact He_caml.
              * exact Hfind_symbol.
            + apply deref_loc_reference. simpl. reflexivity.
          - (* eval_exprlist *)
            econstructor.
            + (* arg1: cast(_t'3) + _t'5 *)
              eapply eval_Ebinop.
              * eapply eval_Ecast.
                eapply eval_Etempvar.
                subst le5 le4 le3 le2.
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gss. reflexivity.
                { apply sem_cast_long_to_ptr_vptr. }
              * eapply eval_Etempvar.
                subst le5 le4.
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gss. reflexivity.
              * apply sem_add_ptr_int_n.
            + (* sem_cast for arg1 *)
              simpl. apply sem_cast_ptr_to_ptr.
            + econstructor.
              * (* arg2: _t'6 = stk_top_cv *)
                eapply eval_Etempvar.
                subst le5. rewrite PTree.gss. reflexivity.
              * (* sem_cast for arg2: stk_top_cv tlong -> tlong *)
                apply (sem_cast_long_val_repr hm cb co _ stk_top_cv m_sp Hval_repr_top).
              * econstructor.
          - (* Genv.find_funct *)
            exact Hfind_funct.
          - (* type_of_fundef *)
            simpl. reflexivity.
          - (* eval_funcall *)
            apply eval_funcall_external.
            exact Hext_call.
        }
      }

      (* -- Part B: assign accu, advance pc, return 0 -- *)
      {
        simpl. (* set_opttemp None Vundef le5 = le5 *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le6) (m1 := m1).
        {
          (* Sassign (s->accu) (((cast 0 tlong) << 1) + 1) *)
          apply exec_Sassign with (loc := sb)
            (ofs := Ptrofs.add so (Ptrofs.repr 8))
            (bf := Full) (v2 := unit_v) (v := unit_v).
          - eapply eval_Efield_struct.
            + eapply eval_Elvalue.
              * eapply eval_Ederef.
                eapply eval_Etempvar.
                subst le6 le5 le4 le3 le2 le1.
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                exact Hle_s.
              * apply deref_loc_copy. simpl. reflexivity.
            + simpl. reflexivity.
            + exact Hco.
            + exact Haccu_offset.
          - eapply eval_Ebinop.
            + eapply eval_Ebinop.
              * eapply eval_Ecast.
                apply eval_Econst_int.
                { apply sem_cast_int_to_long_0. }
              * apply eval_Econst_int.
              * apply sem_shl_long_0_1.
            + apply eval_Econst_int.
            + apply sem_add_long_int_0_1.
          - apply sem_cast_long_vlong.
          - apply assign_loc_value with (chunk := Mint64).
            + simpl. reflexivity.
            + simpl.
              rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
              exact Hstore1.
        }

        apply exec_Sseq_1 with (t1 := E0) (le1 := le7) (m1 := m2).
        {
          (* Sset _t'2 (s->pc) ; Sassign (s->pc) (_t'2 + 1) *)
          apply exec_Sseq_1 with (t1 := E0) (le1 := le7) (m1 := m1).
          {
            apply exec_Sset.
            eapply eval_Elvalue.
            - eapply eval_Efield_struct.
              + eapply eval_Elvalue.
                * eapply eval_Ederef.
                  eapply eval_Etempvar.
                  subst le6 le5 le4 le3 le2 le1.
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  exact Hle_s.
                * apply deref_loc_copy. simpl. reflexivity.
              + simpl. reflexivity.
              + exact Hco.
              + exact Hpc_offset.
            - apply deref_loc_value with (chunk := Mptr).
              * simpl. reflexivity.
              * simpl. rewrite Mptr_Mint64.
                rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
                exact Hpc_load_m1.
          }

          {
            apply exec_Sassign with (loc := sb)
              (ofs := Ptrofs.add so (Ptrofs.repr 0))
              (bf := Full) (v2 := new_pc_v) (v := new_pc_v).
            - eapply eval_Efield_struct.
              + eapply eval_Elvalue.
                * eapply eval_Ederef.
                  eapply eval_Etempvar.
                  subst le7 le6 le5 le4 le3 le2 le1.
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  exact Hle_s.
                * apply deref_loc_copy. simpl. reflexivity.
              + simpl. reflexivity.
              + exact Hco.
              + exact Hpc_offset.
            - eapply eval_Ebinop.
              + eapply eval_Etempvar.
                subst le7. rewrite PTree.gss. reflexivity.
              + apply eval_Econst_int.
              + apply sem_add_pc_1.
            - apply sem_cast_ptr_tint_to_ptr_tint.
            - apply assign_loc_value with (chunk := Mptr).
              + simpl. reflexivity.
              + simpl. rewrite Mptr_Mint64.
                rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
                exact Hstore2.
          }
        }

        (* Sreturn 0 *)
        { apply exec_Sreturn_some.
          apply eval_Econst_int. }
      }
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
      set (ard' := mk_abs_rel
        sb so hm cb new_co gb go
        (ar_stack_block ard) (ar_stack_base_ofs ard)
        (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
      exists ard'.
      set (uso := Ptrofs.unsigned so) in *.

      (* --- Loads from m2 --- *)

      (* pc field at uso+0: written by store2 *)
      assert (Hpc_final : Mem.load Mint64 m2 sb (uso + 0) = Some new_pc_v).
      { pose proof (load_after_store_same m1 m2 sb (uso + 0) new_pc_v Hstore2) as Htmp.
        subst new_pc_v. rewrite load_result_vptr in Htmp. exact Htmp. }

      (* accu field at uso+8: written by store1, preserved by store2 *)
      assert (Haccu_final : Mem.load Mint64 m2 sb (uso + 8) = Some unit_v).
      { apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 8)
                 new_pc_v unit_v Hstore2).
        - pose proof (load_after_store_same m_cm m1 sb (uso + 8) unit_v Hstore1) as Htmp.
          subst unit_v. rewrite load_result_vlong in Htmp. exact Htmp.
        - right. lia. }

      (* sp field at uso+16: written in m -> m_sp, preserved by caml_modify + stores *)
      assert (Hsp_load_msp : Mem.load Mint64 m_sp sb (uso + 16) =
                Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)))).
      { pose proof (load_after_store_same m m_sp sb (uso + 16)
                     (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))) Hstore_sp) as Htmp.
        simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
      assert (Hsp_load_cm : Mem.load Mint64 m_cm sb (uso + 16) =
                Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)))).
      { apply Hcm_sb_loads. exact Hsp_load_msp. }
      assert (Hsp_final : Mem.load Mint64 m2 sb (uso + 16) =
                Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)))).
      { apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 16)
                 new_pc_v _ Hstore2).
        - apply (load_after_store_other m_cm m1 sb (uso + 8) (uso + 16)
                   unit_v _ Hstore1 Hsp_load_cm). right. lia.
        - right. lia. }

      (* env field at uso+24 *)
      assert (Henv_load_msp : Mem.load Mint64 m_sp sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m_sp sb (uso + 16) (uso + 24)
                 (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))) env_v
                 Hstore_sp Henv_load). right. lia. }
      assert (Henv_load_cm : Mem.load Mint64 m_cm sb (uso + 24) = Some env_v).
      { apply Hcm_sb_loads. exact Henv_load_msp. }
      assert (Henv_final : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 24)
                 new_pc_v env_v Hstore2).
        - apply (load_after_store_other m_cm m1 sb (uso + 8) (uso + 24)
                   unit_v env_v Hstore1 Henv_load_cm). right. lia.
        - right. lia. }

      (* extra_args field at uso+32 *)
      assert (Hextra_load_msp : Mem.load Mint64 m_sp sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m_sp sb (uso + 16) (uso + 32)
                 (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))) _
                 Hstore_sp Hextra_load). right. lia. }
      assert (Hextra_load_cm : Mem.load Mint64 m_cm sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply Hcm_sb_loads. exact Hextra_load_msp. }
      assert (Hextra_final : Mem.load Mint64 m2 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 32)
                 new_pc_v _ Hstore2).
        - apply (load_after_store_other m_cm m1 sb (uso + 8) (uso + 32)
                   unit_v _ Hstore1 Hextra_load_cm). right. lia.
        - right. lia. }

      (* global_data field at uso+40 *)
      assert (Hgd_load_msp : Mem.load Mint64 m_sp sb (uso + 40) = Some (Vptr gb go)).
      { apply (load_after_store_other m m_sp sb (uso + 16) (uso + 40)
                 (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))) (Vptr gb go)
                 Hstore_sp Hgd_load). right. lia. }
      assert (Hgd_load_cm : Mem.load Mint64 m_cm sb (uso + 40) = Some (Vptr gb go)).
      { apply Hcm_sb_loads. exact Hgd_load_msp. }
      assert (Hgd_final : Mem.load Mint64 m2 sb (uso + 40) = Some (Vptr gb go)).
      { apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 40)
                 new_pc_v (Vptr gb go) Hstore2).
        - apply (load_after_store_other m_cm m1 sb (uso + 8) (uso + 40)
                   unit_v (Vptr gb go) Hstore1 Hgd_load_cm). right. lia.
        - right. lia. }

      (* trap_sp field at uso+48 *)
      assert (Hts_load_msp : Mem.load Mint64 m_sp sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m_sp sb (uso + 16) (uso + 48)
                 (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))) ts_ptr
                 Hstore_sp Hts_load). right. lia. }
      assert (Hts_load_cm : Mem.load Mint64 m_cm sb (uso + 48) = Some ts_ptr).
      { apply Hcm_sb_loads. exact Hts_load_msp. }
      assert (Hts_final : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 48)
                 new_pc_v ts_ptr Hstore2).
        - apply (load_after_store_other m_cm m1 sb (uso + 8) (uso + 48)
                   unit_v ts_ptr Hstore1 Hts_load_cm). right. lia.
        - right. lia. }

      (* stack_repr through stores: need stack_repr in m2 for rest *)
      (* m -> m_sp (sb store), m_sp -> m_cm (caml_modify, sp_b loads preserved),
         m_cm -> m1 (sb store), m1 -> m2 (sb store) *)
      assert (Hstack_repr_msp : stack_repr hm cb co m_sp rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
      { eapply (stack_repr_store_other_block hm cb co m m_sp _ sp_b
                  (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 16)
                  (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8)))).
        - exact Hstack_repr_rest.
        - exact Hstore_sp.
        - intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }

      assert (Hstack_repr_cm : stack_repr hm cb co m_cm rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
      { assert (Haux : forall vs sp_ofs0,
                  stack_repr hm cb co m_sp vs sp_b sp_ofs0 ->
                  stack_repr hm cb co m_cm vs sp_b sp_ofs0).
        { induction vs as [| v' vs' IHvs]; intros sp0 Hsr.
          - constructor.
          - inversion Hsr; subst.
            econstructor.
            + apply Hcm_sp_loads. exact H1.
            + exact H2.
            + apply IHvs. exact H5. }
        apply Haux. exact Hstack_repr_msp. }

      assert (Hstack_repr_m1 : stack_repr hm cb co m1 rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
      { apply (stack_repr_store_other_block hm cb co m_cm m1 _ sp_b
                 (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 8) unit_v
                 Hstack_repr_cm Hstore1).
        intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }

      assert (Hstack_repr_m2 : stack_repr hm cb co m2 rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
      { apply (stack_repr_store_other_block hm cb co m1 m2 _ sp_b
                 (Ptrofs.add sp_ofs (Ptrofs.repr 8)) sb (uso + 0) new_pc_v
                 Hstack_repr_m1 Hstore2).
        intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }

      (* global_repr through m_cm -> m1 -> m2 *)
      assert (Hglobal_m1 : global_repr hm cb co m1
                (Machine.global s) gb go).
      { apply (global_repr_store_other_block hm cb co m_cm m1 _ gb go sb (uso + 8) unit_v
                 Hcm_global_repr Hstore1).
        intro Heq; exact (Hgb_ne (eq_sym Heq)). }

      assert (Hglobal_m2 : global_repr hm cb co m2
                (Machine.global s) gb go).
      { apply (global_repr_store_other_block hm cb co m1 m2 _ gb go sb (uso + 0) new_pc_v
                 Hglobal_m1 Hstore2).
        intro Heq; exact (Hgb_ne (eq_sym Heq)). }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le_final *)
      { subst le7 le6 le5 le4 le3 le2 le1.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field -- updated *)
      { exists new_pc_v. split.
        - exact Hpc_final.
        - simpl. subst new_pc_v new_pc_ofs. apply pc_rel_shift. }

      (* 3. accu field -- val_unit = Val_int 0 *)
      { exists unit_v. split.
        - exact Haccu_final.
        - simpl. subst unit_v. exact (vr_int _ _ _ 0). }

      (* 4. sp field -- updated to sp + 8 (stack tail) *)
      { exists (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))), sp_b, (Ptrofs.add sp_ofs (Ptrofs.repr 8)).
        split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
        - exact Hsp_final.
        - reflexivity.
        - simpl. eapply stack_repr_co_shift. exact Hstack_repr_m2.
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)). lia.
        - split; [| split].
          + rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)). exact Hsp_rep_tail.
          + (* sp_writable: permission preserved through stores + caml_modify *)
            assert (Hsp_writable_tail : Mem.range_perm m sp_b 0
                      (Ptrofs.unsigned sp_ofs + 8 + 8 * Z.of_nat (length rest)) Cur Writable).
            { intros o Ho. apply Hsp_writable. rewrite Hstk. simpl length.
              pose proof (Nat2Z.is_nonneg (length rest)). lia. }
            intros ofs' Hofs'.
            rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)) in Hofs'.
            eapply Mem.perm_store_1. exact Hstore2.
            eapply Mem.perm_store_1. exact Hstore1.
            apply Hcm_perm.
            * eapply Mem.perm_valid_block. eapply Mem.perm_store_1. exact Hstore_sp.
              apply Hsp_writable_tail. exact Hofs'.
            * eapply Mem.perm_store_1. exact Hstore_sp.
              apply Hsp_writable_tail. exact Hofs'.
          + simpl.
            rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)).
            apply Z.divide_add_r. exact Hsp_align. exists 1. lia. }

      (* 5. env field *)
      { exists env_v. split.
        - exact Henv_final.
        - simpl. eapply val_repr_co_shift. exact Henv_repr. }

      (* 6. extra_args field *)
      { simpl. exact Hextra_final. }

      (* 7. global_data field *)
      { exists (Vptr gb go). split; [| split; [| split]].
        - exact Hgd_final.
        - simpl. reflexivity.
        - simpl. eapply global_repr_co_shift. exact Hglobal_m2.
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field *)
      { exists ts_ptr. split.
        - exact Hts_final.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved through stores + caml_modify *)
      { intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore2.
        eapply Mem.perm_store_1. exact Hstore1.
        apply Hcm_perm.
        - eapply Mem.perm_valid_block. eapply Mem.perm_store_1. exact Hstore_sp.
          apply Hsb_writable. exact Hofs'.
        - eapply Mem.perm_store_1. exact Hstore_sp.
          apply Hsb_writable. exact Hofs'. }
    }
  }

Qed.
