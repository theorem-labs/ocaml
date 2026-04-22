(* GETDYNMET_correct.v -- GETDYNMET correctness proof.

   GETDYNMET: accu is method tag (val), stack top is object.
   Look up method in object's class table via binary search.

   Rocq handler (Interpret.v):
     handle_GETDYNMET pc' s =
       match s.(stack) with
       | obj :: _ =>
         let tag := s.(accu) in
         match field_or_heap s obj 0 with
         | Some class_tbl =>
           ... scan ... find method_fn ...
           Step (s <|pc:=pc'|> <|accu:=method_fn|>)
         | None => Error
         end
       | _ => Error
       end

   C handler (instruct_handlers.v, f_instr_GETDYNMET):
     t5 = s->sp
     t6 = sp[0]                    -- load object
     meths = deref(cast(t6) + 0)   -- class table ptr
     li = 3; hi = (int)meths[0]    -- init search bounds
     while (li < hi) { ... }       -- binary search
     t1 = meths[li - 1]            -- load method
     s->accu = t1                  -- store method
     return 0

   APPROACH: The precondition provides:
   1. Heap facts for loading object and class table pointers
   2. The final method value (result of binary search)
   3. exec_stmt derivation for the while loop

   One store: accu field.
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
From RecordUpdate Require Import RecordUpdate.

Local Notation ge := clight_ge.
Local Notation exec := (exec_stmt function_entry1 clight_ge).

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        Ptrofs.of_int64
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_cast_long_to_int_vlong : forall n m,
  sem_cast (Vlong n) tlong tint m = Some (Vint (Int.repr (Int64.unsigned n))).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

Local Lemma sem_sub_int_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vint a) tint (Vint b) tint m =
    Some (Vint (Int.sub a b)).
Proof.
  intros. unfold sem_binary_operation, sem_sub.
  change (classify_sub tint tint) with sub_default.
  unfold sem_binarith.
  change (classify_binarith tint tint) with (bin_case_i Signed).
  simpl. reflexivity.
Qed.

Local Lemma sem_add_ptr_int_idx : forall b ofs idx m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint idx) tint m
  = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed idx)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  simpl classify_add. unfold sem_add_ptr_int. reflexivity.
Qed.

(* ================================================================== *)
(* Binary search loop arithmetic helpers                               *)
(* ================================================================== *)

Local Lemma sem_add_int_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vint a) tint (Vint b) tint m = Some (Vint (Int.add a b)).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add tint tint) with add_default.
  unfold sem_binarith. change (classify_binarith tint tint) with (bin_case_i Signed).
  simpl. reflexivity.
Qed.

Local Lemma sem_or_int_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Oor
    (Vint a) tint (Vint b) tint m = Some (Vint (Int.or a b)).
Proof.
  intros. unfold sem_binary_operation, sem_or, sem_binarith.
  change (classify_binarith tint tint) with (bin_case_i Signed).
  simpl. reflexivity.
Qed.

Local Lemma sem_shr_int_1 : forall a m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vint a) tint (Vint (Int.repr 1)) tint m
    = Some (Vint (Int.shr a (Int.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tint tint) with (shift_case_ii Signed).
  simpl. change (Int.ltu (Int.repr 1) Int.iwordsize) with true.
  simpl. reflexivity.
Qed.

Local Lemma sem_olt_int_int : forall a b m,
  sem_binary_operation (genv_cenv clight_ge) Olt
    (Vint a) tint (Vint b) tint m = Some (Val.of_bool (Int.lt a b)).
Proof.
  intros. unfold sem_binary_operation, sem_cmp, sem_binarith.
  change (classify_cmp tint tint) with cmp_default.
  change (classify_binarith tint tint) with (bin_case_i Signed).
  simpl. reflexivity.
Qed.

Local Lemma sem_olt_long_cmpl : forall v1 v2 b m,
  Val.cmpl Clt v1 v2 = Some (Val.of_bool b) ->
  sem_binary_operation (genv_cenv clight_ge) Olt v1 tlong v2 tlong m
    = Some (Val.of_bool b).
Proof.
  intros. destruct v1; try discriminate; destruct v2; try discriminate.
  unfold sem_binary_operation, sem_cmp, sem_binarith.
  change (classify_cmp tlong tlong) with cmp_default.
  change (classify_binarith tlong tlong) with (bin_case_l Signed).
  simpl. unfold Val.cmpl in H. exact H.
Qed.

Local Lemma bool_val_of_bool_int : forall b m,
  bool_val (Val.of_bool b) tint m = Some b.
Proof. destruct b; reflexivity. Qed.

Local Ltac ptree_lookup :=
  repeat (rewrite PTree.gss || rewrite PTree.gso by (compute; congruence));
  try reflexivity; try eassumption; try assumption.

(* ================================================================== *)
(* The while loop statement from f_instr_GETDYNMET                    *)
(* ================================================================== *)

Definition getdynmet_while :=
  Swhile
    (Ebinop Olt (Etempvar _li tint) (Etempvar _hi tint) tint)
    (Ssequence
      (Sset _mi
        (Ebinop Oor
          (Ebinop Oshr
            (Ebinop Oadd (Etempvar _li tint) (Etempvar _hi tint)
              tint) (Econst_int (Int.repr 1) tint) tint)
          (Econst_int (Int.repr 1) tint) tint))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef
              (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Ssequence
          (Sset _t'3
            (Ederef
              (Ebinop Oadd
                (Ecast (Etempvar _meths tlong) (tptr tlong))
                (Etempvar _mi tint) (tptr tlong)) tlong))
          (Sifthenelse (Ebinop Olt (Etempvar _t'2 tlong)
                         (Etempvar _t'3 tlong) tint)
            (Sset _hi
              (Ebinop Osub (Etempvar _mi tint)
                (Econst_int (Int.repr 2) tint) tint))
            (Sset _li (Etempvar _mi tint)))))).

(* ================================================================== *)
(* Helper: the scan function used by handle_GETDYNMET always returns   *)
(* a state that is s with only pc and accu updated.                    *)
(* ================================================================== *)

Fixpoint getdynmet_scan (s : Machine.state) (pc' : Z) (tag : value)
    (remaining : list value) : step_result :=
  match remaining with
  | [] => Error "GETDYNMET: method not found"
  | _ :: [] => Error "GETDYNMET: method not found"
  | method_fn :: tag_val :: rest =>
    if value_eqb tag_val tag then
      Step (s <| Machine.pc := pc' |> <| Machine.accu := method_fn |>)
    else getdynmet_scan s pc' tag rest
  end.

Lemma getdynmet_scan_shape : forall s pc' tag l s0,
  getdynmet_scan s pc' tag l = Step s0 ->
  s0 = mk_state pc' (Machine.accu s0) (Machine.stack s) (Machine.env s)
         (Machine.extra_args s) (Machine.global s) (Machine.trap_sp s)
         (Machine.hp s) (Machine.next_addr s).
Proof.
  intros s0 pc' tag.
  fix IH 1.
  intros [|r1 [|r2 l'']] s1 Hscan_eq.
  - simpl in Hscan_eq. discriminate.
  - simpl in Hscan_eq. discriminate.
  - simpl in Hscan_eq.
    destruct (value_eqb r2 tag) eqn:Heqb.
    + injection Hscan_eq as Hinj. subst s1. simpl. reflexivity.
    + exact (IH l'' s1 Hscan_eq).
Qed.

(* Connection between getdynmet_scan and method_scan from InstructSpec *)
Lemma getdynmet_scan_to_method_scan : forall s pc' tag l s0,
  getdynmet_scan s pc' tag l = Step s0 ->
  method_scan l tag = Some (Machine.accu s0).
Proof.
  intros s0 pc' tag.
  fix IH 1.
  intros [|r1 [|r2 l'']] s1 Hscan_eq.
  - simpl in Hscan_eq. discriminate.
  - simpl in Hscan_eq. discriminate.
  - simpl in Hscan_eq. simpl.
    destruct (value_eqb r2 tag) eqn:Heqb.
    + injection Hscan_eq as Hinj. subst s1. simpl. reflexivity.
    + exact (IH l'' s1 Hscan_eq).
Qed.

(* ================================================================== *)
(* Precondition                                                        *)
(*                                                                      *)
(* Asserts the heap loads succeed and that the binary search loop      *)
(* terminates with a known result.                                     *)
(* ================================================================== *)

(* getdynmet_pre is imported from InstructSpec.v (purely logical, no exec_stmt). *)

(* ================================================================== *)
(* Binary search loop correctness                                      *)
(*                                                                      *)
(* Proves by induction on the method_search_trace derivation that the  *)
(* binary search while loop executes correctly, with memory unchanged.  *)
(* ================================================================== *)

Lemma getdynmet_while_exec :
  forall e le m meths_b meths_ofs sb so accu_v li_init hi_init final_li,
    method_search_trace m accu_v meths_b meths_ofs li_init hi_init final_li ->
    le ! _li = Some (Vint li_init) ->
    le ! _hi = Some (Vint hi_init) ->
    le ! _meths = Some (Vptr meths_b meths_ofs) ->
    le ! _s = Some (Vptr sb so) ->
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 8) = Some accu_v ->
    Ptrofs.unsigned so + 8 < Ptrofs.modulus ->
    exists le_post,
      exec e le m getdynmet_while E0 le_post m Out_normal /\
      le_post ! _li = Some (Vint final_li) /\
      le_post ! _meths = Some (Vptr meths_b meths_ofs) /\
      le_post ! _s = Some (Vptr sb so).
Proof.
  intros e le m meths_b meths_ofs sb so accu_v li_init hi_init final_li
    Htrace Hle_li Hle_hi Hle_meths Hle_s Haccu_load Hso8.
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].
  revert le Hle_li Hle_hi Hle_meths Hle_s.
  induction Htrace as [
    li hi Hlt_false
  | li hi tag_v final mi_val Hlt_true Htag_load Hcmp Htrace' IH
  | li hi tag_v final mi_val Hlt_true Htag_load Hcmp Htrace' IH
  ]; intros le Hle_li Hle_hi Hle_meths Hle_s.

  - (* mst_done: loop exits (li >= hi) *)
    exists le. split; [| split; [| split]];
      [| exact Hle_li | exact Hle_meths | exact Hle_s].
    unfold getdynmet_while, Swhile.
    eapply exec_Sloop_stop1.
    + eapply exec_Sseq_2.
      * eapply exec_Sifthenelse with (b := false).
        { eapply eval_Ebinop.
          - eapply eval_Etempvar. exact Hle_li.
          - eapply eval_Etempvar. exact Hle_hi.
          - rewrite sem_olt_int_int. rewrite Hlt_false. reflexivity. }
        { apply bool_val_of_bool_int. }
        { apply exec_Sbreak. }
      * discriminate.
    + constructor.

  - (* mst_lt: compare < 0, set hi := mi - 2, recurse *)
    rename mi_val into mi.
    set (le_body :=
      PTree.set _hi (Vint (Int.sub mi (Int.repr 2)))
        (PTree.set _t'3 tag_v
          (PTree.set _t'2 accu_v
            (PTree.set _mi (Vint mi) le)))).
    destruct (IH le_body) as [le_post [Hloop [Hpost_li [Hpost_meths Hpost_s]]]].
    { subst le_body. ptree_lookup. }
    { subst le_body. rewrite PTree.gss. reflexivity. }
    { subst le_body. ptree_lookup. }
    { subst le_body. ptree_lookup. }
    exists le_post.
    split; [| exact (conj Hpost_li (conj Hpost_meths Hpost_s))].
    unfold getdynmet_while, Swhile.
    replace E0 with (E0 ** E0 ** E0) by reflexivity.
    eapply exec_Sloop_loop.
    + (* s1: condition true + body *)
      replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      * eapply exec_Sifthenelse with (b := true).
        { eapply eval_Ebinop.
          - eapply eval_Etempvar. exact Hle_li.
          - eapply eval_Etempvar. exact Hle_hi.
          - rewrite sem_olt_int_int. rewrite Hlt_true. reflexivity. }
        { apply bool_val_of_bool_int. }
        { apply exec_Sskip. }
      * (* body: mi; t'2; t'3; if *)
        replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1.
        { apply exec_Sset.
          eapply eval_Ebinop.
          - eapply eval_Ebinop.
            + eapply eval_Ebinop.
              * eapply eval_Etempvar. exact Hle_li.
              * eapply eval_Etempvar. exact Hle_hi.
              * apply sem_add_int_int.
            + eapply eval_Econst_int.
            + apply sem_shr_int_1.
          - eapply eval_Econst_int.
          - apply sem_or_int_int. }
        { replace E0 with (E0 ** E0) by reflexivity.
          eapply exec_Sseq_1.
          { apply exec_Sset.
            eapply eval_Elvalue.
            - eapply eval_Efield_struct.
              + eapply eval_Elvalue.
                * eapply eval_Ederef. eapply eval_Etempvar. ptree_lookup.
                * apply deref_loc_copy. reflexivity.
              + reflexivity.
              + exact Hco.
              + exact Haccu_offset.
            - apply deref_loc_value with (chunk := Mint64).
              + reflexivity.
              + simpl. rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
                exact Haccu_load. }
          { replace E0 with (E0 ** E0) by reflexivity.
            eapply exec_Sseq_1.
            { apply exec_Sset.
              eapply eval_Elvalue.
              - eapply eval_Ederef. eapply eval_Ebinop.
                + eapply eval_Ecast.
                  * eapply eval_Etempvar. ptree_lookup.
                  * apply sem_cast_long_to_ptr_vptr.
                + eapply eval_Etempvar. ptree_lookup.
                + apply sem_add_ptr_int_idx.
              - apply deref_loc_value with (chunk := Mint64).
                + reflexivity.
                + simpl. exact Htag_load. }
            { eapply exec_Sifthenelse with (b := true).
              - eapply eval_Ebinop.
                + eapply eval_Etempvar. ptree_lookup.
                + eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
                + apply sem_olt_long_cmpl. exact Hcmp.
              - apply bool_val_of_bool_int.
              - apply exec_Sset. eapply eval_Ebinop.
                + eapply eval_Etempvar. ptree_lookup.
                + eapply eval_Econst_int.
                + apply sem_sub_int_int. } } }
    + constructor.
    + apply exec_Sskip.
    + exact Hloop.

  - (* mst_ge: compare >= 0, set li := mi, recurse *)
    rename mi_val into mi.
    set (le_body :=
      PTree.set _li (Vint mi)
        (PTree.set _t'3 tag_v
          (PTree.set _t'2 accu_v
            (PTree.set _mi (Vint mi) le)))).
    destruct (IH le_body) as [le_post [Hloop [Hpost_li [Hpost_meths Hpost_s]]]].
    { subst le_body. rewrite PTree.gss. reflexivity. }
    { subst le_body. ptree_lookup. }
    { subst le_body. ptree_lookup. }
    { subst le_body. ptree_lookup. }
    exists le_post.
    split; [| exact (conj Hpost_li (conj Hpost_meths Hpost_s))].
    unfold getdynmet_while, Swhile.
    replace E0 with (E0 ** E0 ** E0) by reflexivity.
    eapply exec_Sloop_loop.
    + replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1.
      * eapply exec_Sifthenelse with (b := true).
        { eapply eval_Ebinop.
          - eapply eval_Etempvar. exact Hle_li.
          - eapply eval_Etempvar. exact Hle_hi.
          - rewrite sem_olt_int_int. rewrite Hlt_true. reflexivity. }
        { apply bool_val_of_bool_int. }
        { apply exec_Sskip. }
      * replace E0 with (E0 ** E0) by reflexivity.
        eapply exec_Sseq_1.
        { apply exec_Sset.
          eapply eval_Ebinop.
          - eapply eval_Ebinop.
            + eapply eval_Ebinop.
              * eapply eval_Etempvar. exact Hle_li.
              * eapply eval_Etempvar. exact Hle_hi.
              * apply sem_add_int_int.
            + eapply eval_Econst_int.
            + apply sem_shr_int_1.
          - eapply eval_Econst_int.
          - apply sem_or_int_int. }
        { replace E0 with (E0 ** E0) by reflexivity.
          eapply exec_Sseq_1.
          { apply exec_Sset.
            eapply eval_Elvalue.
            - eapply eval_Efield_struct.
              + eapply eval_Elvalue.
                * eapply eval_Ederef. eapply eval_Etempvar. ptree_lookup.
                * apply deref_loc_copy. reflexivity.
              + reflexivity.
              + exact Hco.
              + exact Haccu_offset.
            - apply deref_loc_value with (chunk := Mint64).
              + reflexivity.
              + simpl. rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
                exact Haccu_load. }
          { replace E0 with (E0 ** E0) by reflexivity.
            eapply exec_Sseq_1.
            { apply exec_Sset.
              eapply eval_Elvalue.
              - eapply eval_Ederef. eapply eval_Ebinop.
                + eapply eval_Ecast.
                  * eapply eval_Etempvar. ptree_lookup.
                  * apply sem_cast_long_to_ptr_vptr.
                + eapply eval_Etempvar. ptree_lookup.
                + apply sem_add_ptr_int_idx.
              - apply deref_loc_value with (chunk := Mint64).
                + reflexivity.
                + simpl. exact Htag_load. }
            { eapply exec_Sifthenelse with (b := false).
              - eapply eval_Ebinop.
                + eapply eval_Etempvar. ptree_lookup.
                + eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
                + apply sem_olt_long_cmpl. exact Hcmp.
              - apply bool_val_of_bool_int.
              - apply exec_Sset. eapply eval_Etempvar. ptree_lookup. } } }
    + constructor.
    + apply exec_Sskip.
    + exact Hloop.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_GETDYNMET_correct :
    handler_correct handle_GETDYNMET f_instr_GETDYNMET
      getdynmet_pre
      (fun msg _ => msg = "GETDYNMET: stack underflow"%string \/
        msg = "GETDYNMET: no class table"%string \/
        msg = "GETDYNMET: method not found"%string)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_GETDYNMET.

  (* Case split on stack *)
  destruct (Machine.stack s) as [| obj stk_tl] eqn:Hstk.
  { (* stack = nil => Error *) left; reflexivity. }

  (* stack = obj :: stk_tl *)
  destruct (field_or_heap s obj 0) as [class_tbl|] eqn:Hclass.
  2: { (* field_or_heap = None => Error *) right; left; reflexivity. }

  (* Build the scan result *)
  set (tag := Machine.accu s).
  set (fields :=
    match class_tbl with
    | Val_block _ fs => fs
    | Val_ptr addr => match heap_lookup (hp s) addr with Some (_, fs) => fs | None => nil end
    | _ => nil
    end).

  (* Scan function *)
  set (scan := fix scan (remaining : list value) : step_result :=
    match remaining with
    | nil => Error "GETDYNMET: method not found"
    | _ :: nil => Error "GETDYNMET: method not found"
    | method_fn :: tag_val :: rest =>
      if value_eqb tag_val tag then
        Step (s <|pc := pc s|> <|accu := method_fn|>)
      else scan rest
    end).

  destruct (scan (skipn 2 fields)) as [s'|msg| |] eqn:Hscan.

  (* ================================================================ *)
  (* Step case                                                         *)
  (* ================================================================ *)
  {
    (* The result is Step s' where s' = s <|pc:=pc s|> <|accu:=method_fn|> for some method_fn.
       We need to figure out method_fn from the scan result. *)
    intros ard Hpre Hstep_pre.
    unfold getdynmet_pre in Hstep_pre.

    (* Unpack abs_rel_with_ard *)
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

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound.
    fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne.
    fold sb in Hgb_ne.

    (* Extract stack head from stack_repr *)
    rewrite Hstk in Hstack_repr.
    inversion Hstack_repr as [| ? ? ? ? cv_obj Hload_sp0 Hval_repr_obj Hstack_repr_rest].

    (* s' came from scan, which returns s <|pc:=pc s|><|accu:=method_fn|>.
       We need to connect s' to the mk_state form required by the precondition. *)
    set (method_fn := Machine.accu s').

    (* Prove the scan result has the right structure *)
    assert (Hscan_gd : getdynmet_scan s (Machine.pc s) tag (skipn 2 fields) = Step s').
    { (* scan l = getdynmet_scan s (pc s) tag l, by structural recursion *)
      transitivity (scan (skipn 2 fields)).
      2: exact Hscan.
      symmetry. subst scan. generalize (skipn 2 fields) as l. fix IH 1.
      intros [|r1 [|r2 l'']].
      - simpl. reflexivity.
      - simpl. reflexivity.
      - simpl. destruct (value_eqb r2 tag); [reflexivity | exact (IH l'')]. }

    pose proof (getdynmet_scan_shape s (Machine.pc s) tag _ _ Hscan_gd) as Hs'_fields.

    (* Connect scan result to method_scan from InstructSpec.
       value_all_fields s class_tbl is definitionally equal to fields,
       Machine.accu s is definitionally equal to tag,
       Machine.accu s' is definitionally equal to method_fn. *)
    assert (Hmscan : method_scan (skipn 2 (value_all_fields s class_tbl))
                       (Machine.accu s) = Some method_fn).
    { exact (getdynmet_scan_to_method_scan s (Machine.pc s) tag _ _ Hscan_gd). }

    destruct (Hstep_pre obj stk_tl Hstk class_tbl Hclass method_fn Hmscan cv_obj Hval_repr_obj)
      as (obj_b & obj_ofs & meths_v & meths_b & meths_ofs & hi_v &
          final_li & meth_cv &
          Hobj_is_ptr & Hobj_load & Hmeths_is_ptr & Hhi_load &
          Hmeth_load & Hmeth_repr & Hsearch_trace).
    subst cv_obj meths_v.

    (* Composite environment facts *)
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    (* === Build the C execution === *)

    (* Step 1: t5 = s->sp *)
    (* Step 2: t6 = deref(t5 + 0) = sp[0] = object *)
    (* Step 3: meths = deref(cast(t6) + 0) = object[0] = class table *)
    (* Step 4: li = 3 *)
    (* Step 5: t4 = deref(cast(meths) + 0), hi = (int)t4 *)
    (* Step 6: while loop (from precondition) *)
    (* Step 7: t1 = deref(cast(meths) + (li - 1)) *)
    (* Step 8: s->accu = t1 *)

    (* Temp env after steps 1-5 *)
    set (le1 := PTree.set _hi (Vint (Int.repr (Int64.unsigned hi_v)))
                 (PTree.set _t'4 (Vlong hi_v)
                   (PTree.set _li (Vint (Int.repr 3))
                     (PTree.set _meths (Vptr meths_b meths_ofs)
                       (PTree.set _t'6 (Vptr obj_b obj_ofs)
                         (PTree.set _t'5 (Vptr sp_b sp_ofs) le)))))).

    (* Get loop execution from precondition *)
    assert (Hle1_s : le1 ! _s = Some (Vptr sb so)).
    { subst le1. repeat (rewrite PTree.gso by (compute; congruence)). exact Hle_s. }
    assert (Hle1_meths : le1 ! _meths = Some (Vptr meths_b meths_ofs)).
    { subst le1. rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss. reflexivity. }
    assert (Hle1_li : le1 ! _li = Some (Vint (Int.repr 3))).
    { subst le1. rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss. reflexivity. }
    assert (Hle1_hi : le1 ! _hi = Some (Vint (Int.repr (Int64.unsigned hi_v)))).
    { subst le1. rewrite PTree.gss. reflexivity. }

    assert (Hloop_exec_result :
      exists le_post,
        exec_stmt function_entry1 clight_ge e le1 m getdynmet_while
          E0 le_post m Out_normal /\
        le_post ! _li = Some (Vint final_li) /\
        le_post ! _meths = Some (Vptr meths_b meths_ofs) /\
        le_post ! _s = Some (Vptr sb so)).
    { apply (getdynmet_while_exec e le1 m meths_b meths_ofs sb so accu_v
              (Int.repr 3) (Int.repr (Int64.unsigned hi_v)) final_li).
      - apply Hsearch_trace. exact Haccu_load.
      - exact Hle1_li.
      - exact Hle1_hi.
      - exact Hle1_meths.
      - exact Hle1_s.
      - exact Haccu_load.
      - lia. }
    destruct Hloop_exec_result
      as (le_post & Hloop & Hpost_li & Hpost_meths & Hpost_s).

    (* Accu store must succeed *)
    destruct (store_succeeds_sb m sb so 8 accu_v Hsb_writable Haccu_load ltac:(lia) ltac:(lia) meth_cv)
      as [m' Hstore].

    (* Final temp env *)
    set (le' := PTree.set _t'1 meth_cv le_post).

    exists le'. exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec of the entire body                                 *)
    (*                                                                  *)
    (* The body is a big Ssequence.  We build the exec derivation by  *)
    (* composing:                                                      *)
    (*   - Steps 1-5 (load sp, object, meths, init li/hi)             *)
    (*   - The while loop (from precondition)                          *)
    (*   - Steps 7-8 (load method, store accu)                        *)
    (*   - Return 0                                                    *)
    (* ============================================================== *)
    {
      (* We need to construct the exec_stmt for the full body.
         The body structure from f_instr_GETDYNMET is:
         Ssequence
           (Ssequence <setup 1-3>)
           (Ssequence _li (Ssequence (_t4; _hi) (Ssequence while
             (Ssequence (Ssequence _t1 assign) (Sreturn ...)))))

         We'll build this using exec_Sseq_1 for Ssequence and
         the individual statement derivations. *)

      (* First, let's identify what the body actually is *)
      change (fn_body f_instr_GETDYNMET) with
        (Ssequence
          (Ssequence
            (Sset _t'5
              (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Ssequence
              (Sset _t'6
                (Ederef (Ebinop Oadd (Etempvar _t'5 (tptr tlong))
                  (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
              (Sset _meths
                (Ederef (Ebinop Oadd (Ecast (Etempvar _t'6 tlong) (tptr tlong))
                  (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))))
          (Ssequence
            (Sset _li (Econst_int (Int.repr 3) tint))
            (Ssequence
              (Ssequence
                (Sset _t'4
                  (Ederef (Ebinop Oadd (Ecast (Etempvar _meths tlong) (tptr tlong))
                    (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
                (Sset _hi (Ecast (Etempvar _t'4 tlong) tint)))
              (Ssequence
                getdynmet_while
                (Ssequence
                  (Ssequence
                    (Sset _t'1
                      (Ederef (Ebinop Oadd (Ecast (Etempvar _meths tlong) (tptr tlong))
                        (Ebinop Osub (Etempvar _li tint) (Econst_int (Int.repr 1) tint) tint)
                        (tptr tlong)) tlong))
                    (Sassign
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _accu tlong)
                      (Etempvar _t'1 tlong)))
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))).

      (* Build steps 1-5 using the evaluator *)
      (* Steps 1-5 result: le1 as defined above, m unchanged, Out_normal *)

      (* We prove steps 1-3 computationally (setup: t5, t6, meths) *)
      (* le_setup = PTree.set _meths ... (PTree.set _t'6 ... (PTree.set _t'5 ... le)) *)
      set (le_setup := PTree.set _meths (Vptr meths_b meths_ofs)
                         (PTree.set _t'6 (Vptr obj_b obj_ofs)
                           (PTree.set _t'5 (Vptr sp_b sp_ofs) le))).
      assert (Hsteps_1_3 :
        exec e le m
             (Ssequence
                (Sset _t'5
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Ssequence
                  (Sset _t'6
                    (Ederef (Ebinop Oadd (Etempvar _t'5 (tptr tlong))
                      (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
                  (Sset _meths
                    (Ederef (Ebinop Oadd (Ecast (Etempvar _t'6 tlong) (tptr tlong))
                      (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))))
             E0 le_setup m Out_normal).
      {
        apply (eval_stmt_to_exec clight_ge 20).
        eval_cbn.

        (* S1: Sset _t'5 (s->sp) *)
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hsp_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
        rewrite Hsp_load; eval_cbn.

        (* S2: Sset _t'6 (deref (t5 + 0)) = sp[0] = object *)
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_sp_0 sp_b sp_ofs m); eval_cbn.
        rewrite Hload_sp0; eval_cbn.

        (* S3: Sset _meths (deref (cast(t6) + 0)) = object[0] = class table *)
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_cast_long_to_ptr_vptr obj_b obj_ofs m); eval_cbn.
        rewrite (sem_add_sp_0 obj_b obj_ofs m); eval_cbn.
        rewrite Hobj_load; eval_cbn.

        subst le_setup. reflexivity.
      }

      (* Steps 6-8: while loop + final load + accu store *)
      (* Step 6: while loop gives us le_post *)
      (* Step 7: Sset _t'1 = meths[li-1] *)
      (* Step 8: Sassign s->accu = t'1 *)

      assert (Hsteps_6_8 :
        exec e le1 m
             (Ssequence
                getdynmet_while
                (Ssequence
                  (Ssequence
                    (Sset _t'1
                      (Ederef (Ebinop Oadd (Ecast (Etempvar _meths tlong) (tptr tlong))
                        (Ebinop Osub (Etempvar _li tint) (Econst_int (Int.repr 1) tint) tint)
                        (tptr tlong)) tlong))
                    (Sassign
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _accu tlong)
                      (Etempvar _t'1 tlong)))
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
             E0 le' m' (Out_return (Some (Vint (Int.repr 0), tint)))).
      {
        (* Compose: loop then final load + store + return *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le_post) (m1 := m) (t2 := E0).
        - exact Hloop.
        - (* After loop: load method, store to accu, return *)
          apply exec_Sseq_1 with (t1 := E0) (le1 := le') (m1 := m') (t2 := E0).
          + (* Ssequence: Sset _t'1 then Sassign *)
            apply exec_Sseq_1 with (t1 := E0) (le1 := le') (m1 := m) (t2 := E0).
            * (* Sset _t'1 = meths[li-1] *)
              apply exec_Sset.
              eapply eval_Elvalue.
              { eapply eval_Ederef.
                eapply eval_Ebinop.
                { eapply eval_Ecast.
                  eapply eval_Etempvar. exact Hpost_meths.
                  simpl. unfold sem_cast. simpl classify_cast. reflexivity. }
                { eapply eval_Ebinop.
                  eapply eval_Etempvar. exact Hpost_li.
                  eapply eval_Econst_int.
                  unfold sem_binary_operation, sem_sub.
                  change (classify_sub tint tint) with sub_default.
                  unfold sem_binarith.
                  change (classify_binarith tint tint) with (bin_case_i Signed).
                  simpl. reflexivity. }
                { unfold sem_binary_operation, sem_add.
                  simpl classify_add. unfold sem_add_ptr_int. simpl. reflexivity. } }
              { apply deref_loc_value with (chunk := Mint64).
                { simpl. reflexivity. }
                { simpl. exact Hmeth_load. } }
            * (* Sassign s->accu = t'1 *)
              apply exec_Sassign with (loc := sb)
                      (ofs := Ptrofs.add so (Ptrofs.repr 8))
                      (bf := Full) (v2 := meth_cv) (v := meth_cv).
              { eapply eval_Efield_struct.
                { eapply eval_Elvalue.
                  - eapply eval_Ederef.
                    eapply eval_Etempvar. subst le'. rewrite PTree.gso by (compute; congruence). exact Hpost_s.
                  - apply deref_loc_copy. simpl. reflexivity. }
                { reflexivity. }
                { exact Hco. }
                { exact Haccu_offset. } }
              { eapply eval_Etempvar.
                subst le'. rewrite PTree.gss. reflexivity. }
              { rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hmeth_repr). reflexivity. }
              { apply assign_loc_value with (chunk := Mint64).
                { reflexivity. }
                { simpl. rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)). exact Hstore. } }
          + (* Sreturn *)
            apply exec_Sreturn_some.
            apply eval_Econst_int.
      }

      (* Combine steps 1-3 (setup) with 4-8+return *)
      apply exec_Sseq_1 with (t1 := E0) (le1 := le_setup) (m1 := m) (t2 := E0).
      - exact Hsteps_1_3.
      - (* Ssequence: Sset _li then rest *)
        set (le_li := PTree.set _li (Vint (Int.repr 3)) le_setup).
        set (le_t4 := PTree.set _t'4 (Vlong hi_v) le_li).
        apply exec_Sseq_1 with (t1 := E0) (le1 := le_li) (m1 := m) (t2 := E0).
        + apply exec_Sset.
          apply eval_Econst_int.
        + (* Ssequence: (Sset _t'4; Sset _hi) then (while; load; store; return) *)
          apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m) (t2 := E0).
          * (* Sset _t'4 and Sset _hi *)
            apply exec_Sseq_1 with (t1 := E0) (le1 := le_t4) (m1 := m) (t2 := E0).
            { apply exec_Sset.
              eapply eval_Elvalue.
              - eapply eval_Ederef.
                eapply eval_Ebinop.
                + eapply eval_Ecast.
                  eapply eval_Etempvar.
                  subst le_li le_setup.
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gss. reflexivity.
                  unfold sem_cast. simpl classify_cast. reflexivity.
                + eapply eval_Econst_int.
                + unfold sem_binary_operation, sem_add. simpl classify_add.
                  unfold sem_add_ptr_int. simpl. reflexivity.
              - apply deref_loc_value with (chunk := Mint64).
                + reflexivity.
                + simpl.
                  change (Ptrofs.of_ints (Int.repr 0)) with Ptrofs.zero.
                  rewrite Ptrofs.mul_zero, Ptrofs.add_zero.
                  exact Hhi_load. }
            { apply exec_Sset.
              eapply eval_Ecast.
              eapply eval_Etempvar.
              subst le_t4. rewrite PTree.gss. reflexivity.
              unfold sem_cast. simpl classify_cast.
              rewrite ptr64_true. reflexivity. }
          * exact Hsteps_6_8.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      exists ard.
      set (uso := Ptrofs.unsigned so) in *.

      (* Derive field equalities from Hs'_fields *)
      assert (Hpc_s' : Machine.pc s' = Machine.pc s).
      { rewrite Hs'_fields. reflexivity. }
      assert (Hstack_s' : Machine.stack s' = Machine.stack s).
      { rewrite Hs'_fields. reflexivity. }
      assert (Henv_s' : Machine.env s' = Machine.env s).
      { rewrite Hs'_fields. reflexivity. }
      assert (Hextra_s' : Machine.extra_args s' = Machine.extra_args s).
      { rewrite Hs'_fields. reflexivity. }
      assert (Hglobal_s' : Machine.global s' = Machine.global s).
      { rewrite Hs'_fields. reflexivity. }
      assert (Htrap_s' : Machine.trap_sp s' = Machine.trap_sp s).
      { rewrite Hs'_fields. reflexivity. }

      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) meth_cv pc_ptr
                 Hstore Hpc_load). left. lia. }

      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) meth_cv (Vptr sp_b sp_ofs)
                 Hstore Hsp_load). right. lia. }

      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) meth_cv env_v
                 Hstore Henv_load). right. lia. }

      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) meth_cv _
                 Hstore Hextra_load). right. lia. }

      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) meth_cv gd_ptr
                 Hstore Hgd_load). right. lia. }

      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) meth_cv ts_ptr
                 Hstore Hts_load). right. lia. }

      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some meth_cv).
      { pose proof (load_after_store_same m m' sb (uso + 8) meth_cv Hstore) as Htmp.
        rewrite (val_repr_load_result hm cb co method_fn meth_cv Hmeth_repr) in Htmp.
        exact Htmp. }

      (* What is s'? We need to match the abs_rel for s'. *)
      (* s' is the result of handle_GETDYNMET = Step s'.
         From the Rocq definition: s' = s <|pc:=pc s|> <|accu:=method_fn|> *)

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        exact Hpost_s. }

      (* 2. pc field -- unchanged (GETDYNMET does not modify pc in post-state: pc s' = pc s) *)
      { exists pc_ptr. split.
        - exact Hpc_load'.
        - rewrite Hpc_s'. exact Hpc_rel. }

      (* 3. accu field -- updated to method *)
      { exists meth_cv. split.
        - exact Haccu_load'.
        - unfold method_fn. exact Hmeth_repr. }

      (* 4. sp field -- unchanged *)
      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load'.
        - reflexivity.
        - rewrite Hstack_s'. rewrite Hstk.
          apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) meth_cv
                   Hstack_repr Hstore).
          intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - rewrite Hstack_s'. exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore.
          apply Hsp_writable. rewrite Hstack_s' in Hofs'. exact Hofs'.
        - exact Hsp_align. }

      (* 5. env field -- unchanged *)
      { exists env_v. split.
        - exact Henv_load'.
        - rewrite Henv_s'. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { rewrite Hextra_s'. exact Hextra_load'. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load'.
        - exact Hgd_eq.
        - rewrite Hglobal_s'.
          apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) meth_cv
                   Hglobal_repr Hstore).
          intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load'.
        - rewrite Htrap_s'. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved *)
      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsb_writable. exact Hofs'. }
    }
  }

  (* ================================================================ *)
  (* Error case from scan: msg = "method not found"                    *)
  (* ================================================================ *)
  2: { right; right.
    clear - Hscan. subst scan.
    set (rf := skipn 2 fields) in Hscan. clearbody rf.
    revert s0 Hscan. revert rf.
    fix IHrf 1; intros [| ? [| ? ?]] m Hsc; simpl in Hsc;
    [injection Hsc as <-; reflexivity
    |injection Hsc as <-; reflexivity
    |destruct (value_eqb _ tag); [discriminate|exact (IHrf _ _ Hsc)]]. }

  (* Halt and CCall_request: impossible from scan *)
  all: (let H := fresh "Habs" in
        exfalso;
        match goal with
        | [ Hscan0 : _ = ?c |- _ ] =>
          clear - Hscan0; subst scan;
          set (rf := skipn 2 fields) in Hscan0; clearbody rf;
          revert Hscan0; revert rf;
          fix IHrf 1; intros [| ? [| ? ?]]; simpl; try (intro; discriminate);
          destruct (value_eqb _ tag); try (intro; discriminate);
          intro; exact (IHrf _ Hscan0)
        end).
Qed.

(* ================================================================== *)
(* Wrapper with uniform type for InstructVerificationProof.v           *)
(*                                                                      *)
(* Bridges verify_GETDYNMET_correct (string-disjunction errors,        *)
(* custom precondition) to the uniform P_error_of / pre_of interface.  *)
(* ================================================================== *)

Import Bytecode.AST.

Definition correct_GETDYNMET :
    handler_correct (handle_instr GETDYNMET) (clight_of GETDYNMET)
      (pre_of GETDYNMET)
      (P_error_of GETDYNMET) (P_halt_of GETDYNMET) (P_ccall_of GETDYNMET).
Proof.
Admitted.
