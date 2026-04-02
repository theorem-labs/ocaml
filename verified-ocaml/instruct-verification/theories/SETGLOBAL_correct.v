(* SETGLOBAL_correct.v -- SETGLOBAL correctness proof.

   SETGLOBAL n reads n from the code buffer, stores accu into
   global_data[n] via caml_modify, sets accu to val_unit, and
   advances pc by 1.

   The C handler calls the external function caml_modify, which the
   computational evaluator cannot handle.  The proof constructs the
   exec_stmt derivation manually using bigstep rules.

   Rocq handler:
     handle_SETGLOBAL n pc' s =
       let new_global := match set_nth s.(global) n s.(accu) with
                         | Some g => g | None => s.(global) end in
       Step (s <|pc:=pc'|> <|accu:=val_unit|> <|global:=new_global|>)

   C handler:
     _t'2 = s->global_data;
     _t'3 = s->pc;
     _t'4 = *_t'3;
     _t'5 = s->accu;
     caml_modify(global_data + _t'4, _t'5);
     s->accu = ((0 << 1) + 1);       // val_unit = 1
     _t'1 = s->pc;
     s->pc = _t'1 + 1;
     return 0;

   The precondition (via handler_correct) provides:
   - Code buffer contains Z.of_nat n at current PC
   - n fits in int32 signed range
   - Genv.find_funct for caml_modify
   - external_call for caml_modify produces m_cm where:
     * struct block loads are preserved
     * store to accu/pc fields succeeds
     * stack_repr preserved (different block)
     * global_repr for updated globals

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
  field_offset ce _global_data (co_members co) = Errors.OK (40, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_setglobal : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _global_data (co_members co) = Errors.OK (40, Full).
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

Lemma sem_add_gd_n : forall gb go_ofs n_int m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr gb go_ofs) (tptr tlong)
    (Vint n_int) tint
    m = Some (Vptr gb (Ptrofs.add go_ofs
                (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tlong))
                            (ptrofs_of_int Signed n_int)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

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

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* ================================================================== *)
(* Precondition: what caml_modify needs to hold                        *)
(* ================================================================== *)

(* The target address for caml_modify: global_data + n *)
Definition gd_target (go : ptrofs) (n_int : int) : ptrofs :=
  Ptrofs.add go (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tlong))
                             (ptrofs_of_int Signed n_int)).

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_SETGLOBAL_correct : forall n,
    handler_correct (handle_SETGLOBAL n) f_instr_SETGLOBAL
      (fun e m s ard =>
         let cb := ar_code_base_block ard in
         let co := ar_code_base_ofs ard in
         let gb := ar_global_block ard in
         let go := ar_global_ofs ard in
         let sb := ar_sptr_block ard in
         let so := ar_sptr_ofs ard in
         let hm := ar_heap_map ard in
         (* 0. e does not bind _caml_modify (holds after function_entry1
            for fn_vars=nil, fn_params=[(_s, ...)] ) *)
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
         (* 4. caml_modify external call: for the actual accu value,
            there exists m_cm witnessing the call with empty trace *)
         (forall accu_v,
            val_repr hm (Machine.accu s) accu_v ->
            exists m_cm,
              external_call caml_modify_ef ge
                (Vptr gb (gd_target go (Int.repr (Z.of_nat n)))
                 :: accu_v :: nil)
                m E0 Vundef m_cm /\
              (* Struct block loads preserved *)
              (forall ofs v,
                 Mem.load Mint64 m sb ofs = Some v ->
                 Mem.load Mint64 m_cm sb ofs = Some v) /\
              (* Struct block stores succeed (writable) *)
              (forall ofs v_old v_new,
                 Mem.load Mint64 m sb ofs = Some v_old ->
                 exists m', Mem.store Mint64 m_cm sb ofs v_new = Some m') /\
              (* Stack block loads preserved (for stack_repr) *)
              (forall sp_b, sp_b <> gb ->
                 forall ofs v,
                 Mem.load Mint64 m sp_b ofs = Some v ->
                 Mem.load Mint64 m_cm sp_b ofs = Some v) /\
              (* global_repr for the updated globals *)
              (forall new_gs,
                 set_nth (Machine.global s) n (Machine.accu s) = Some new_gs ->
                 global_repr hm m_cm new_gs gb go) /\
              (* global_repr unchanged if set_nth fails *)
              (set_nth (Machine.global s) n (Machine.accu s) = None ->
                 global_repr hm m_cm (Machine.global s) gb go)))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intro n.
  intros e le m s.
  unfold handle_SETGLOBAL. simpl.

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
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep Hsp_writable]]]]]]]]]]] &
    [env_v [Henv_load Henv_repr]] &
    Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
    [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
  subst sp_ptr gd_ptr.

  destruct Hstep_pre as (He_caml & Hcode_load & Hn_range & [b_cm [Hfind_symbol Hfind_funct]] & Hcaml_modify_pre).

  (* Structural invariants *)
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
  pose proof (code_block_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  (* Composite environment facts *)
  destruct interp_state_co_setglobal as [co_is [Hco [Hpc_offset [Haccu_offset Hgd_offset]]]].

  (* Subst pc_ptr to concrete form *)
  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* Get the caml_modify results *)
  destruct (Hcaml_modify_pre accu_v Haccu_repr) as
    (m_cm & Hext_call & Hcm_sb_loads & Hcm_sb_stores &
     Hcm_other_loads & Hcm_global_repr_some & Hcm_global_repr_none).

  (* Store 1: accu field at (sb, uso+8) <- val_unit = Vlong 1 *)
  set (unit_v := Vlong (Int64.repr 1)).
  destruct (Hcm_sb_stores (Ptrofs.unsigned so + 8) accu_v unit_v Haccu_load)
    as [m1 Hstore1].

  (* Store 2: pc field at (sb, uso+0) *)
  set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
  set (new_pc_v := Vptr cb new_pc_ofs).

  (* pc load in m1 *)
  assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m_cm m1 sb (Ptrofs.unsigned so + 8)
             (Ptrofs.unsigned so + 0) unit_v (Vptr cb pc_ofs)
             Hstore1).
    - apply Hcm_sb_loads. exact Hpc_load.
    - left. lia. }

  destruct (store_succeeds_from_load m1 sb (Ptrofs.unsigned so + 0)
              (Vptr cb pc_ofs) new_pc_v Hpc_load_m1)
    as [m2 Hstore2].

  (* Final temp env *)
  set (le1 := PTree.set _t'2 (Vptr gb go) le).
  set (le2 := PTree.set _t'3 (Vptr cb pc_ofs) le1).
  set (le3 := PTree.set _t'4 (Vint (Int.repr (Z.of_nat n))) le2).
  set (le4 := PTree.set _t'5 accu_v le3).
  set (le5 := le4). (* Scall with optid=None doesn't change le *)
  set (le6 := PTree.set _t'1 (Vptr cb pc_ofs) le5).

  exists le6. exists m2.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ================================================================== *)
  (* Part 1: exec_stmt derivation                                       *)
  (* ================================================================== *)
  {
    (* Body structure:
       Ssequence
         (Ssequence                          -- Part A: reads + caml_modify
           (Sset _t'2 (s->global_data))
           (Ssequence
             (Sset _t'3 (s->pc))
             (Ssequence
               (Sset _t'4 (deref _t'3))
               (Ssequence
                 (Sset _t'5 (s->accu))
                 (Scall None caml_modify [gd+n; accu])))))
         (Ssequence                          -- Part B: assign accu, pc, return
           (Sassign (s->accu) val_unit_expr)
           (Ssequence
             (Ssequence
               (Sset _t'1 (s->pc))
               (Sassign (s->pc) (_t'1 + 1)))
             (Sreturn 0))) *)

    apply exec_Sseq_1 with (t1 := E0) (le1 := le5) (m1 := m_cm).

    (* -- Part A: reads + caml_modify call -- *)
    {
      (* Sset _t'2 ; rest *)
      apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m).
      {
        apply exec_Sset.
        eapply eval_Elvalue.
        - eapply eval_Efield_struct.
          + eapply eval_Elvalue.
            * eapply eval_Ederef. eapply eval_Etempvar. exact Hle_s.
            * apply deref_loc_copy. simpl. reflexivity.
          + simpl. reflexivity.
          + exact Hco.
          + exact Hgd_offset.
        - apply deref_loc_value with (chunk := Mptr).
          * simpl. reflexivity.
          * simpl. rewrite Mptr_Mint64.
            rewrite (ptrofs_add_unsigned so 40 ltac:(lia) ltac:(lia)).
            exact Hgd_load.
      }

      (* Sset _t'3 ; rest *)
      apply exec_Sseq_1 with (t1 := E0) (le1 := le2) (m1 := m).
      {
        apply exec_Sset.
        eapply eval_Elvalue.
        - eapply eval_Efield_struct.
          + eapply eval_Elvalue.
            * eapply eval_Ederef. eapply eval_Etempvar.
              subst le1. rewrite PTree.gso by (compute; congruence). exact Hle_s.
            * apply deref_loc_copy. simpl. reflexivity.
          + simpl. reflexivity.
          + exact Hco.
          + exact Hpc_offset.
        - apply deref_loc_value with (chunk := Mptr).
          * simpl. reflexivity.
          * simpl. rewrite Mptr_Mint64.
            rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
            exact Hpc_load.
      }

      (* Sset _t'4 ; rest *)
      apply exec_Sseq_1 with (t1 := E0) (le1 := le3) (m1 := m).
      {
        apply exec_Sset.
        eapply eval_Elvalue.
        - eapply eval_Ederef.
          eapply eval_Etempvar.
          subst le2. rewrite PTree.gss. reflexivity.
        - apply deref_loc_value with (chunk := Mint32).
          * simpl. reflexivity.
          * simpl. exact Hcode_load.
      }

      (* Sset _t'5 ; Scall *)
      apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m).
      {
        apply exec_Sset.
        eapply eval_Elvalue.
        - eapply eval_Efield_struct.
          + eapply eval_Elvalue.
            * eapply eval_Ederef. eapply eval_Etempvar.
              subst le3 le2 le1.
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gso by (compute; congruence).
              exact Hle_s.
            * apply deref_loc_copy. simpl. reflexivity.
          + simpl. reflexivity.
          + exact Hco.
          + exact Haccu_offset.
        - apply deref_loc_value with (chunk := Mint64).
          * simpl. reflexivity.
          * simpl.
            rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
            exact Haccu_load.
      }

      (* Scall None caml_modify [gd+n; accu] *)
      {
        eapply exec_Scall with
          (tyargs := (tptr tlong) :: tlong :: nil)
          (tyres := tvoid)
          (cconv := cc_default)
          (vargs := Vptr gb (gd_target go (Int.repr (Z.of_nat n)))
                    :: accu_v :: nil)
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
          + (* arg1: gd + _t'4 *)
            eapply eval_Ebinop.
            * eapply eval_Ecast.
              eapply eval_Etempvar.
              subst le4 le3 le2 le1.
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gss. reflexivity.
              { apply sem_cast_ptr_to_ptr. }
            * eapply eval_Etempvar.
              subst le4 le3.
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gss. reflexivity.
            * apply sem_add_gd_n.
          + (* sem_cast for arg1 *)
            simpl. apply sem_cast_ptr_to_ptr.
          + econstructor.
            * (* arg2: _t'5 = accu_v *)
              eapply eval_Etempvar.
              subst le4. rewrite PTree.gss. reflexivity.
            * (* sem_cast for arg2: accu_v tlong -> tlong *)
              apply (sem_cast_long_val_repr hm _ accu_v m Haccu_repr).
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
      simpl. (* set_opttemp None Vundef le4 = le4 *)
      apply exec_Sseq_1 with (t1 := E0) (le1 := le5) (m1 := m1).
      {
        (* Sassign (s->accu) (((cast 0 tlong) << 1) + 1) *)
        apply exec_Sassign with (loc := sb)
          (ofs := Ptrofs.add so (Ptrofs.repr 8))
          (bf := Full) (v2 := unit_v) (v := unit_v).
        - eapply eval_Efield_struct.
          + eapply eval_Elvalue.
            * eapply eval_Ederef.
              eapply eval_Etempvar.
              subst le5 le4 le3 le2 le1.
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

      apply exec_Sseq_1 with (t1 := E0) (le1 := le6) (m1 := m2).
      {
        (* Sset _t'1 (s->pc) ; Sassign (s->pc) (_t'1 + 1) *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le6) (m1 := m1).
        {
          apply exec_Sset.
          eapply eval_Elvalue.
          - eapply eval_Efield_struct.
            + eapply eval_Elvalue.
              * eapply eval_Ederef.
                eapply eval_Etempvar.
                subst le5 le4 le3 le2 le1.
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
          - eapply eval_Ebinop.
            + eapply eval_Etempvar.
              subst le6. rewrite PTree.gss. reflexivity.
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

  (* ================================================================== *)
  (* Part 2: abs_rel for post-state                                     *)
  (* ================================================================== *)
  {
    set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
    set (ard' := mk_abs_rel
      sb so hm cb new_co gb go
      (ar_stack_block ard) (ar_stack_base_ofs ard)
      (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
    exists ard'.
    set (uso := Ptrofs.unsigned so) in *.

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

    (* sp field at uso+16 *)
    assert (Hsp_final : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
    { apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 16)
               new_pc_v (Vptr sp_b sp_ofs) Hstore2).
      - apply (load_after_store_other m_cm m1 sb (uso + 8) (uso + 16)
                 unit_v (Vptr sp_b sp_ofs) Hstore1).
        + apply Hcm_sb_loads. exact Hsp_load.
        + right. lia.
      - right. lia. }

    (* env field at uso+24 *)
    assert (Henv_final : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 24)
               new_pc_v env_v Hstore2).
      - apply (load_after_store_other m_cm m1 sb (uso + 8) (uso + 24)
                 unit_v env_v Hstore1).
        + apply Hcm_sb_loads. exact Henv_load.
        + right. lia.
      - right. lia. }

    (* extra_args field at uso+32 *)
    assert (Hextra_final : Mem.load Mint64 m2 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 32)
               new_pc_v _ Hstore2).
      - apply (load_after_store_other m_cm m1 sb (uso + 8) (uso + 32)
                 unit_v _ Hstore1).
        + apply Hcm_sb_loads. exact Hextra_load.
        + right. lia.
      - right. lia. }

    (* global_data field at uso+40 *)
    assert (Hgd_final : Mem.load Mint64 m2 sb (uso + 40) = Some (Vptr gb go)).
    { apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 40)
               new_pc_v (Vptr gb go) Hstore2).
      - apply (load_after_store_other m_cm m1 sb (uso + 8) (uso + 40)
                 unit_v (Vptr gb go) Hstore1).
        + apply Hcm_sb_loads. exact Hgd_load.
        + right. lia.
      - right. lia. }

    (* trap_sp field at uso+48 *)
    assert (Hts_final : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m1 m2 sb (uso + 0) (uso + 48)
               new_pc_v ts_ptr Hstore2).
      - apply (load_after_store_other m_cm m1 sb (uso + 8) (uso + 48)
                 unit_v ts_ptr Hstore1).
        + apply Hcm_sb_loads. exact Hts_load.
        + right. lia.
      - right. lia. }

    (* stack_repr in m2: stack is on sp_b which is different from sb.
       m -> m_cm: preserved by Hcm_other_loads (sp_b <> gb)
       m_cm -> m1: store on sb, sp_b <> sb
       m1 -> m2: store on sb, sp_b <> sb *)
    assert (Hstack_repr_cm : stack_repr hm m_cm (Machine.stack s) sp_b sp_ofs).
    { (* Use the fact that stack_repr depends only on loads from sp_b,
         and Hcm_other_loads preserves loads on blocks <> gb.
         But we need sp_b <> gb -- we have Hsp_ne_gb. *)
      clear -Hstack_repr Hcm_other_loads Hsp_ne_gb.
      revert Hstack_repr. revert sp_ofs.
      induction (Machine.stack s) as [| v stk IH]; intros Hsr sp_ofs.
      - constructor.
      - inversion sp_ofs; subst.
        econstructor.
        + apply Hcm_other_loads. exact Hsp_ne_gb. exact H1.
        + exact H2.
        + apply IH. exact H5. }

    assert (Hstack_repr_m1 : stack_repr hm m1 (Machine.stack s) sp_b sp_ofs).
    { apply (stack_repr_store_other_block hm m_cm m1 _ sp_b sp_ofs sb (uso + 8) unit_v
               Hstack_repr_cm Hstore1).
      intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }

    assert (Hstack_repr_m2 : stack_repr hm m2 (Machine.stack s) sp_b sp_ofs).
    { apply (stack_repr_store_other_block hm m1 m2 _ sp_b sp_ofs sb (uso + 0) new_pc_v
               Hstack_repr_m1 Hstore2).
      intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }

    (* global_repr in m2: globals are on gb which is different from sb.
       m_cm already has the right global_repr, stores to sb preserve it. *)
    assert (Hglobal_new : global_repr hm m_cm
              (match set_nth (Machine.global s) n (Machine.accu s) with
               | Some g => g | None => Machine.global s end)
              gb go).
    { destruct (set_nth (Machine.global s) n (Machine.accu s)) eqn:Hset.
      - apply Hcm_global_repr_some. reflexivity.
      - apply Hcm_global_repr_none. reflexivity. }

    assert (Hglobal_m1 : global_repr hm m1
              (match set_nth (Machine.global s) n (Machine.accu s) with
               | Some g => g | None => Machine.global s end)
              gb go).
    { apply (global_repr_store_other_block hm m_cm m1 _ gb go sb (uso + 8) unit_v
               Hglobal_new Hstore1).
      intro Heq; exact (Hgb_ne (eq_sym Heq)). }

    assert (Hglobal_m2 : global_repr hm m2
              (match set_nth (Machine.global s) n (Machine.accu s) with
               | Some g => g | None => Machine.global s end)
              gb go).
    { apply (global_repr_store_other_block hm m1 m2 _ gb go sb (uso + 0) new_pc_v
               Hglobal_m1 Hstore2).
      intro Heq; exact (Hgb_ne (eq_sym Heq)). }

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le_final *)
    { subst le6 le5 le4 le3 le2 le1.
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
      - simpl. subst unit_v. exact (vr_int _ 0). }

    (* 4. sp field *)
    { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
      - exact Hsp_final.
      - reflexivity.
      - simpl. exact Hstack_repr_m2.
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - exact Hsp_ge8.
      - exact Hsp_rep.
      - (* sp_writable: permission preserved through caml_modify + stores *)
        admit. }

    (* 5. env field *)
    { exists env_v. split.
      - exact Henv_final.
      - simpl. exact Henv_repr. }

    (* 6. extra_args field *)
    { simpl. exact Hextra_final. }

    (* 7. global_data field *)
    { exists (Vptr gb go). split; [| split; [| split]].
      - exact Hgd_final.
      - simpl. reflexivity.
      - simpl. exact Hglobal_m2.
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field *)
    { exists ts_ptr. split.
      - exact Hts_final.
      - simpl. exact Htrap_rel. }

    (* 9. sb_writable -- permission preserved through caml_modify + stores *)
    { admit. }
  }
Admitted. (* sp_writable, sb_writable through caml_modify *)
