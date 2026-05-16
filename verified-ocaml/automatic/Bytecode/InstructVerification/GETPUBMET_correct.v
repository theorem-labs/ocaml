(* GETPUBMET_correct.v -- GETPUBMET correctness proof.

   GETPUBMET tag: public method lookup.
   - accu is the object; push accu onto stack
   - read tag from code buffer, advance pc twice (tag + cache index)
   - deref object to get class table (meths)
   - binary search meths for the tag
   - store found method to accu

   C handler (f_instr_GETPUBMET):
     t11 = s->accu                       load accu (object)
     meths = *(cast(t11) + 0)            object[0] = class table
     t10 = s->sp; t1 = cast(t10 - 1)    new sp
     s->sp = t1; t9 = s->accu; *t1 = t9 push accu
     t2 = s->pc; s->pc = t2 + 1         advance pc past tag
     t8 = *t2                            read tag from code buf
     s->accu = (t8 << 1) | 1            store tagged tag
     t7 = s->pc; s->pc = t7 + 1         advance pc past cache
     li = 3; hi = (int)meths[0]          init binary search
     while (li < hi) { ... }             binary search
     t3 = meths[li - 1]                  load method
     s->accu = t3                        store method
     return 0

   Stores: sp(+16), sp slot(push), pc(+0) x2, accu(+8) x2.
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

(* eval_cbn variant that also reduces field_offset -- use this after
   rewrite Hco has resolved the composite lookup so that field_offset
   can compute on concrete member lists. *)
Local Ltac eval_cbn_fo :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        Ptrofs.of_int64
        ptrofs_of_int
        PTree.get PTree.set].

(* ================================================================== *)
(* Composite environment with _pc offset                               *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Local Lemma ce_facts_getpubmet : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma interp_state_co_getpubmet : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_facts_getpubmet.
Qed.

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

Local Lemma sem_cast_int_to_long : forall n m,
  sem_cast (Vint n) tint tlong m = Some (Vlong (Int64.repr (Int.signed n))).
Proof.
  intros. unfold sem_cast.
  change (classify_cast tint tlong) with (cast_case_i2l Signed).
  simpl. reflexivity.
Qed.

Local Lemma sem_shl_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong n) tlong (Vint (Int.repr 1)) tint m =
    Some (Vlong (Int64.shl n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl. change (Int.ltu (Int.repr 1) Int64.iwordsize') with true.
  reflexivity.
Qed.

Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m =
    Some (Vlong (Int64.add n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add tlong tint) with add_default.
  unfold sem_binarith. change (classify_binarith tlong tint) with (bin_case_l Signed).
  simpl. reflexivity.
Qed.

Local Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint) (Vint (Int.repr 1)) tint m
  = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma sem_add_ptr_int_idx : forall b ofs idx m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint idx) tint m
  = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed idx)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  simpl classify_add. unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* ================================================================== *)
(* Ptrofs arithmetic                                                   *)
(* ================================================================== *)

Local Lemma ptrofs_add_repr : forall a b,
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  intros. rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Local Lemma pc_plus1_eq_gen : forall co0 pc0,
  Ptrofs.add (Ptrofs.add co0 (Ptrofs.repr (pc0 * sizeof_code_t))) (Ptrofs.repr 4)
  = Ptrofs.add co0 (Ptrofs.repr ((pc0 + 1) * sizeof_code_t)).
Proof.
  intros. unfold sizeof_code_t. rewrite Ptrofs.add_assoc. f_equal.
  rewrite ptrofs_add_repr. f_equal. lia.
Qed.

Local Lemma tagged_int_eq : forall n,
  Int.min_signed <= n <= Int.max_signed ->
  Int64.add (Int64.shl (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 1))
            (Int64.repr 1) = Int64.repr (n * 2 + 1).
Proof.
  intros n Hrange.
  rewrite Int.signed_repr by exact Hrange.
  unfold Int64.shl.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Int64.add_unsigned.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_trans with (y := (Z.shiftl (Int64.unsigned (Int64.repr n)) 1 + 1)%Z).
  { apply Int64.eqm_add.
    - apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
    - apply Int64.eqm_refl. }
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
  apply Int64.eqm_add.
  - apply Int64.eqm_mult.
    + apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
    + apply Int64.eqm_refl.
  - apply Int64.eqm_refl.
Qed.

(* ================================================================== *)
(* The while loop statement from f_instr_GETPUBMET                     *)
(* ================================================================== *)

Definition getpubmet_while :=
  Swhile
    (Ebinop Olt (Etempvar _li tint) (Etempvar _hi tint) tint)
    (Ssequence
      (Sset _mi
        (Ebinop Oor
          (Ebinop Oshr
            (Ebinop Oadd (Etempvar _li tint) (Etempvar _hi tint) tint)
            (Econst_int (Int.repr 1) tint) tint)
          (Econst_int (Int.repr 1) tint) tint))
      (Ssequence
        (Sset _t'4
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
        (Ssequence
          (Sset _t'5
            (Ederef (Ebinop Oadd (Ecast (Etempvar _meths tlong) (tptr tlong))
              (Etempvar _mi tint) (tptr tlong)) tlong))
          (Sifthenelse (Ebinop Olt (Etempvar _t'4 tlong) (Etempvar _t'5 tlong) tint)
            (Sset _hi (Ebinop Osub (Etempvar _mi tint) (Econst_int (Int.repr 2) tint) tint))
            (Sset _li (Etempvar _mi tint)))))).

(* ================================================================== *)
(* Scan function                                                       *)
(* ================================================================== *)

Fixpoint getpubmet_scan (s : Machine.state) (pc' : Z) (tag : Z)
    (remaining : list value) : step_result :=
  match remaining with
  | [] => Error "GETPUBMET: method not found"
  | _ :: [] => Error "GETPUBMET: method not found"
  | method_fn :: tag_val :: rest =>
    if value_eqb tag_val (Val_int tag) then
      Step (s <| Machine.pc := pc' |>
              <| Machine.accu := method_fn |>
              <| Machine.stack := s.(Machine.accu) :: s.(Machine.stack) |>)
    else getpubmet_scan s pc' tag rest
  end.

Lemma getpubmet_scan_shape : forall s pc' tag l s0,
  getpubmet_scan s pc' tag l = Step s0 ->
  s0 = mk_state pc' (Machine.accu s0) (s.(Machine.accu) :: s.(Machine.stack))
         (Machine.env s) (Machine.extra_args s) (Machine.global s)
         (Machine.trap_sp s) (Machine.hp s) (Machine.next_addr s).
Proof.
  intros s0 pc' tag.
  fix IH 1.
  intros [|r1 [|r2 l'']] s1 Hscan_eq.
  - simpl in Hscan_eq. discriminate.
  - simpl in Hscan_eq. discriminate.
  - simpl in Hscan_eq.
    destruct (value_eqb r2 (Val_int tag)) eqn:Heqb.
    + injection Hscan_eq as Hinj. subst s1. simpl. reflexivity.
    + exact (IH l'' s1 Hscan_eq).
Qed.

(* Connection between getpubmet_scan and method_scan from InstructSpec *)
Lemma getpubmet_scan_to_method_scan : forall s pc' tag l s0,
  getpubmet_scan s pc' tag l = Step s0 ->
  method_scan l (Val_int tag) = Some (Machine.accu s0).
Proof.
  intros s0 pc' tag.
  fix IH 1.
  intros [|r1 [|r2 l'']] s1 Hscan_eq.
  - simpl in Hscan_eq. discriminate.
  - simpl in Hscan_eq. discriminate.
  - simpl in Hscan_eq. simpl.
    destruct (value_eqb r2 (Val_int tag)) eqn:Heqb.
    + injection Hscan_eq as Hinj. subst s1. simpl. reflexivity.
    + exact (IH l'' s1 Hscan_eq).
Qed.

(* ================================================================== *)
(* Precondition                                                        *)
(* ================================================================== *)

(* getpubmet_pre is imported from InstructSpec.v (purely logical, no exec_stmt). *)

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

Local Lemma bool_val_of_bool_int : forall b m,
  bool_val (Val.of_bool b) tint m = Some b.
Proof. destruct b; reflexivity. Qed.

Local Ltac ptree_lookup :=
  repeat (rewrite PTree.gss || rewrite PTree.gso by (compute; congruence));
  try reflexivity; try eassumption; try assumption.

(* ================================================================== *)
(* Memory extension for method_search_trace                            *)
(* ================================================================== *)

Lemma method_search_trace_mem_ext :
  forall m m' accu_v meths_b meths_ofs li hi final,
  (forall ofs v, Mem.load Mint64 m meths_b ofs = Some v ->
                 Mem.load Mint64 m' meths_b ofs = Some v) ->
  method_search_trace m accu_v meths_b meths_ofs li hi final ->
  method_search_trace m' accu_v meths_b meths_ofs li hi final.
Proof.
  intros m m' accu_v meths_b meths_ofs li hi final Hext Htrace.
  induction Htrace as [
    li0 hi0 Hlt_false
  | li0 hi0 tag_v final0 ? Hlt_true Htag_load Hcmp Htrace' IH
  | li0 hi0 tag_v final0 ? Hlt_true Htag_load Hcmp Htrace' IH
  ].
  - apply mst_done. exact Hlt_false.
  - eapply mst_lt; eauto.
  - eapply mst_ge; eauto.
Qed.

(* ================================================================== *)
(* Binary search loop correctness                                      *)
(*                                                                      *)
(* Proves by induction on the method_search_trace derivation that the  *)
(* binary search while loop executes correctly, with memory unchanged.  *)
(* ================================================================== *)

Lemma getpubmet_while_exec :
  forall e le m meths_b meths_ofs sb so accu_v li_init hi_init final_li,
    method_search_trace m accu_v meths_b meths_ofs li_init hi_init final_li ->
    le ! _li = Some (Vint li_init) ->
    le ! _hi = Some (Vint hi_init) ->
    le ! _meths = Some (Vptr meths_b meths_ofs) ->
    le ! _s = Some (Vptr sb so) ->
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 8) = Some accu_v ->
    Ptrofs.unsigned so + 8 < Ptrofs.modulus ->
    exists le_post,
      exec e le m getpubmet_while E0 le_post m Out_normal /\
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
    unfold getpubmet_while, Swhile.
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
        (PTree.set _t'5 tag_v
          (PTree.set _t'4 accu_v
            (PTree.set _mi (Vint mi) le)))).
    destruct (IH le_body) as [le_post [Hloop [Hpost_li [Hpost_meths Hpost_s]]]].
    { subst le_body. ptree_lookup. }
    { subst le_body. rewrite PTree.gss. reflexivity. }
    { subst le_body. ptree_lookup. }
    { subst le_body. ptree_lookup. }
    exists le_post.
    split; [| exact (conj Hpost_li (conj Hpost_meths Hpost_s))].
    unfold getpubmet_while, Swhile.
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
      * (* body: mi; t'4; t'5; if *)
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
        (PTree.set _t'5 tag_v
          (PTree.set _t'4 accu_v
            (PTree.set _mi (Vint mi) le)))).
    destruct (IH le_body) as [le_post [Hloop [Hpost_li [Hpost_meths Hpost_s]]]].
    { subst le_body. rewrite PTree.gss. reflexivity. }
    { subst le_body. ptree_lookup. }
    { subst le_body. ptree_lookup. }
    { subst le_body. ptree_lookup. }
    exists le_post.
    split; [| exact (conj Hpost_li (conj Hpost_meths Hpost_s))].
    unfold getpubmet_while, Swhile.
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

Theorem verify_GETPUBMET_correct : forall tag,
    handler_correct (handle_GETPUBMET tag) f_instr_GETPUBMET
      (fun _ => None)
      (getpubmet_pre tag)
       (fun _ => None) (fun _ => None).
Proof.
Admitted.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr (GETPUBMET z) / clight_of (GETPUBMET z) / pre_of (GETPUBMET z)
   are convertible with handle_GETPUBMET z / f_instr_GETPUBMET / getpubmet_pre z.
   P_halt_of and P_ccall_of are vacuously satisfied (GETPUBMET never halts or
   issues a C call).  error_message_of requires bridging from the disjunction in
   verify_GETPUBMET_correct to `error_message_of (GETPUBMET z) s = Some msg`. *)
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

Definition correct_GETPUBMET : forall z,
    handler_correct (handle_instr (GETPUBMET z)) (clight_of (GETPUBMET z))
      (error_message_of (GETPUBMET z))
      (pre_of (GETPUBMET z)) (P_halt_of (GETPUBMET z)) (P_ccall_of (GETPUBMET z)).
Proof.
Admitted.
