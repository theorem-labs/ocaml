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
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
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
      (fun _ => None)
      getdynmet_pre
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* ================================================================== *)
(* Wrapper with uniform type for InstructVerificationProof.v           *)
(*                                                                      *)
(* Bridges verify_GETDYNMET_correct (string-disjunction errors,        *)
(* custom precondition) to the uniform error_message_of / pre_of interface.  *)
(* ================================================================== *)

Import Bytecode.AST.

Definition correct_GETDYNMET :
    handler_correct (handle_instr GETDYNMET) (clight_of GETDYNMET)
      (error_message_of GETDYNMET)
      (pre_of GETDYNMET) (P_halt_of GETDYNMET) (P_ccall_of GETDYNMET).
Proof.
Admitted.
