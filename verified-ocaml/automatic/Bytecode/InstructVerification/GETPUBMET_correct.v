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
      (getpubmet_pre tag)
      (fun msg _ => msg = "GETPUBMET: no class table"%string \/
        msg = "GETPUBMET: method not found"%string)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro tag.
  intros e le m s.
  unfold handler_correct, handle_GETPUBMET.

  set (new_stack := Machine.accu s :: Machine.stack s).
  set (real_fields :=
    match field_or_heap s (Machine.accu s) 0 with
    | Some class_tbl =>
      match class_tbl with
      | Val_block _ fs => fs
      | Val_ptr addr => match heap_lookup (hp s) addr with Some (_, fs) => fs | None => nil end
      | _ => nil
      end
    | None => nil
    end).

  destruct (field_or_heap s (Machine.accu s) 0) as [class_tbl|] eqn:Hclass.
  2: { (* field_or_heap = None => Error *) left; reflexivity. }

  set (actual_fields :=
    match class_tbl with
    | Val_block _ fs => fs
    | Val_ptr addr => match heap_lookup (hp s) addr with Some (_, fs) => fs | None => nil end
    | _ => nil
    end).

  set (scan := fix scan (remaining : list value) : step_result :=
    match remaining with
    | nil => Error "GETPUBMET: method not found"
    | _ :: nil => Error "GETPUBMET: method not found"
    | method_fn :: tag_val :: rest =>
      if value_eqb tag_val (Val_int tag) then
        Step (s <|pc := pc s|> <|accu := method_fn|> <|stack := new_stack|>)
      else scan rest
    end).

  destruct (scan (skipn 2 actual_fields)) as [s'|msg| |] eqn:Hscan.

  (* ================================================================ *)
  (* Step case                                                         *)
  (* ================================================================ *)
  {
    intros ard Hpre Hstep_pre.
    unfold getpubmet_pre in Hstep_pre.
    destruct Hstep_pre as (Hcode_load & Htag_range & [sp_b' [sp_ofs' [Hsp_load' Hsp_ge16]]] & Hheap_pre).

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

    pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
    pose proof (ar_code_ne_sptr ard) as Hcb_ne_sb. fold sb cb in Hcb_ne_sb.

    simpl in Hsp_load'. fold sb so in Hsp_load'.
    assert (sp_b' = sp_b /\ sp_ofs' = sp_ofs) as [-> ->]
      by (rewrite Hsp_load in Hsp_load'; injection Hsp_load'; auto).

    set (method_fn := Machine.accu s').

    assert (Hscan_gp : getpubmet_scan s (Machine.pc s) tag (skipn 2 actual_fields) = Step s').
    { transitivity (scan (skipn 2 actual_fields)).
      2: exact Hscan.
      symmetry. subst scan. generalize (skipn 2 actual_fields) as l. fix IH 1.
      intros [|r1 [|r2 l'']].
      - simpl. reflexivity.
      - simpl. reflexivity.
      - simpl. destruct (value_eqb r2 (Val_int tag)); [reflexivity | exact (IH l'')]. }

    pose proof (getpubmet_scan_shape s (Machine.pc s) tag _ _ Hscan_gp) as Hs'_fields.

    (* Connect scan result to method_scan from InstructSpec.
       value_all_fields s class_tbl is definitionally equal to actual_fields,
       Machine.accu s' is definitionally equal to method_fn. *)
    assert (Hmscan : method_scan (skipn 2 (value_all_fields s class_tbl))
                       (Val_int tag) = Some method_fn).
    { exact (getpubmet_scan_to_method_scan s (Machine.pc s) tag _ _ Hscan_gp). }

    destruct (Hheap_pre class_tbl Hclass method_fn Hmscan accu_v Haccu_repr)
      as (accu_b & accu_ofs & meths_b & meths_ofs & hi_v &
          final_li & meth_cv &
          Haccu_is_ptr & Hobj_load & Hhi_load &
          Hmeths_ne_sb & Hmeths_ne_sp_fn & Hmeth_load & Hmeth_repr & Hmst).
    subst accu_v.

    (* meths_b <> sp_b *)
    assert (Hmeths_ne_sp : meths_b <> sp_b).
    { exact (Hmeths_ne_sp_fn sp_b sp_ofs Hsp_load). }

    (* Composite environment *)
    destruct interp_state_co_getpubmet as [co_is [Hco [Hpc_offset [Hsp_offset Haccu_offset]]]].

    (* pc_ptr is concrete *)
    unfold pc_rel in Hpc_rel. subst pc_ptr.
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

    set (tagged_tag := Int64.repr (tag * 2 + 1)).
    set (tagged_tag_v := Vlong tagged_tag).

    set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
    assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 8).
    { subst new_sp_ofs. unfold Ptrofs.sub.
      change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
      apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range sp_ofs).
      unfold Ptrofs.max_unsigned. lia. }
    assert (Halign_new : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs)).
    { rewrite Hnew_sp_unsigned. simpl.
      apply Z.divide_sub_r; [exact Hsp_align | exists 1; lia]. }

    set (pc1 := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
    set (pc1_v := Vptr cb pc1).
    set (pc2 := Ptrofs.add pc1 (Ptrofs.repr 4)).
    set (pc2_v := Vptr cb pc2).

    (* ============================================================== *)
    (* Store sequence: m -> m1 -> m2 -> m3 -> m4 -> m5 -> m6 -> m7   *)
    (*   m1: sp store (+16)                                            *)
    (*   m2: push store (sp_b)                                         *)
    (*   m3: pc store (+0, first advance)                              *)
    (*   m4: accu store (+8, tagged tag)                               *)
    (*   m5: pc store (+0, second advance)                             *)
    (*   -- binary search loop runs in m5, no stores --                *)
    (*   m6: accu store (+8, method result)                            *)
    (* ============================================================== *)

    (* Store 1: s->sp = new_sp *)
    destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) (Vptr sp_b new_sp_ofs)) as [m1 Hstore1].
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hw1.

    (* Store 2: push accu to *new_sp *)
    destruct (store_to_sp_after_sb_store m m1 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)
                sp_b (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s)))
                (Ptrofs.unsigned new_sp_ofs)
                Hstore1 Hsp_writable
                ltac:(rewrite Hnew_sp_unsigned; lia)
                ltac:(rewrite Hnew_sp_unsigned; lia)
                Halign_new
                (Vptr accu_b accu_ofs)) as [m2 Hstore2].

    (* Helper: loads on sb survive store 2 (sp_b <> sb) *)
    assert (Hload_sb_m2 : forall ofs v,
      Mem.load Mint64 m1 sb ofs = Some v -> Mem.load Mint64 m2 sb ofs = Some v).
    { intros ofs v Hload1.
      erewrite Mem.load_store_other; [exact Hload1 | exact Hstore2 |].
      left. exact (not_eq_sym Hsp_ne_sb). }

    (* Accu in m1, m2 *)
    assert (Haccu_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some (Vptr accu_b accu_ofs)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8)
               (Vptr sp_b new_sp_ofs) _ Hstore1 Haccu_load). left. lia. }
    assert (Haccu_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some (Vptr accu_b accu_ofs)).
    { exact (Hload_sb_m2 _ _ Haccu_m1). }

    (* pc in m1, m2 *)
    assert (Hpc_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) = Some (Vptr cb pc_ofs)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 0)
               (Vptr sp_b new_sp_ofs) _ Hstore1 Hpc_load). left. lia. }
    assert (Hpc_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) = Some (Vptr cb pc_ofs)).
    { exact (Hload_sb_m2 _ _ Hpc_m1). }

    (* sb writable in m2 *)
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore2 Hw1) as Hw2.

    (* Store 3: s->pc = pc + 1 *)
    destruct (store_succeeds_sb m2 sb so 0 (Vptr cb pc_ofs) Hw2 Hpc_m2 ltac:(lia) ltac:(lia) pc1_v)
      as [m3 Hstore3].
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore3 Hw2) as Hw3.

    (* Accu in m3 *)
    assert (Haccu_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 8) = Some (Vptr accu_b accu_ofs)).
    { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 8)
               pc1_v _ Hstore3 Haccu_m2). right. lia. }

    (* Store 4: s->accu = tagged tag *)
    destruct (store_succeeds_sb m3 sb so 8 (Vptr accu_b accu_ofs) Hw3 Haccu_m3 ltac:(lia) ltac:(lia) tagged_tag_v)
      as [m4 Hstore4].
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore4 Hw3) as Hw4.

    (* pc in m3, m4 *)
    assert (Hpc_m3_same : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 0) = Some pc1_v).
    { pose proof (load_after_store_same m2 m3 sb (Ptrofs.unsigned so + 0) pc1_v Hstore3) as Htmp.
      unfold pc1_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }
    assert (Hpc_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 0) = Some pc1_v).
    { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 0)
               tagged_tag_v _ Hstore4 Hpc_m3_same). left. lia. }

    (* Store 5: s->pc = pc + 2 *)
    destruct (store_succeeds_sb m4 sb so 0 pc1_v Hw4 Hpc_m4 ltac:(lia) ltac:(lia) pc2_v)
      as [m5 Hstore5].
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore5 Hw4) as Hw5.

    (* Accu (tagged) in m4, m5 *)
    assert (Haccu_m4_tagged : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 8) = Some tagged_tag_v).
    { pose proof (load_after_store_same m3 m4 sb (Ptrofs.unsigned so + 8) tagged_tag_v Hstore4) as Htmp.
      subst tagged_tag_v. rewrite load_result_vlong in Htmp. exact Htmp. }
    assert (Haccu_m5_tagged : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 8) = Some tagged_tag_v).
    { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 8)
               pc2_v _ Hstore5 Haccu_m4_tagged). right. lia. }

    (* Code load survives all stores *)
    assert (Hcode_load_m5 : Mem.load Mint32 m5 cb (Ptrofs.unsigned pc_ofs) =
              Some (Vint (Int.repr tag))).
    { erewrite Mem.load_store_other; [| exact Hstore5 | left; exact Hcb_ne_sb].
      erewrite Mem.load_store_other; [| exact Hstore4 | left; exact Hcb_ne_sb].
      erewrite Mem.load_store_other; [| exact Hstore3 | left; exact Hcb_ne_sb].
      erewrite Mem.load_store_other; [| exact Hstore2 | left; exact Hcb_ne_sp].
      erewrite Mem.load_store_other; [| exact Hstore1 | left; exact Hcb_ne_sb].
      exact Hcode_load. }

    (* meths loads survive all stores from m to m5 *)
    assert (Hmeths_survive_m5 : forall idx_ofs v,
      Mem.load Mint64 m meths_b idx_ofs = Some v ->
      Mem.load Mint64 m5 meths_b idx_ofs = Some v).
    { intros idx_ofs v Hload.
      erewrite Mem.load_store_other; [| exact Hstore5 | left; exact Hmeths_ne_sb].
      erewrite Mem.load_store_other; [| exact Hstore4 | left; exact Hmeths_ne_sb].
      erewrite Mem.load_store_other; [| exact Hstore3 | left; exact Hmeths_ne_sb].
      erewrite Mem.load_store_other; [| exact Hstore2 | left; exact Hmeths_ne_sp].
      erewrite Mem.load_store_other; [| exact Hstore1 | left; exact Hmeths_ne_sb].
      exact Hload. }

    (* Fields in m5 that we need for later *)
    assert (Hsp_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b new_sp_ofs)).
    { assert (H1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b new_sp_ofs)).
      { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs) Hstore1) as Htmp.
        simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
      assert (H2 := Hload_sb_m2 _ _ H1).
      assert (H3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b new_sp_ofs)).
      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
                 pc1_v _ Hstore3 H2). right. lia. }
      assert (H4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b new_sp_ofs)).
      { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 16)
                 tagged_tag_v _ Hstore4 H3). right. lia. }
      apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
               pc2_v _ Hstore5 H4). right. lia. }

    assert (Henv_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { assert (H1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some env_v).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 24)
                 (Vptr sp_b new_sp_ofs) _ Hstore1 Henv_load). right. lia. }
      assert (H2 := Hload_sb_m2 _ _ H1).
      assert (H3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 24) = Some env_v).
      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 24)
                 pc1_v _ Hstore3 H2). right. lia. }
      assert (H4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 24) = Some env_v).
      { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 24)
                 tagged_tag_v _ Hstore4 H3). right. lia. }
      apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 24)
               pc2_v _ Hstore5 H4). right. lia. }

    assert (Hextra_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { assert (H1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 32)
                 (Vptr sp_b new_sp_ofs) _ Hstore1 Hextra_load). right. lia. }
      assert (H2 := Hload_sb_m2 _ _ H1).
      assert (H3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 32)
                 pc1_v _ Hstore3 H2). right. lia. }
      assert (H4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 32) = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 32)
                 tagged_tag_v _ Hstore4 H3). right. lia. }
      apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 32)
               pc2_v _ Hstore5 H4). right. lia. }

    assert (Hgd_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
    { assert (H1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 40)
                 (Vptr sp_b new_sp_ofs) _ Hstore1 Hgd_load). right. lia. }
      assert (H2 := Hload_sb_m2 _ _ H1).
      assert (H3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 40)
                 pc1_v _ Hstore3 H2). right. lia. }
      assert (H4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
      { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 40)
                 tagged_tag_v _ Hstore4 H3). right. lia. }
      apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 40)
               pc2_v _ Hstore5 H4). right. lia. }

    assert (Hts_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
    { assert (H1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 48)
                 (Vptr sp_b new_sp_ofs) _ Hstore1 Hts_load). right. lia. }
      assert (H2 := Hload_sb_m2 _ _ H1).
      assert (H3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 48)
                 pc1_v _ Hstore3 H2). right. lia. }
      assert (H4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 48)
                 tagged_tag_v _ Hstore4 H3). right. lia. }
      apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 48)
               pc2_v _ Hstore5 H4). right. lia. }

    (* pc in m5 *)
    assert (Hpc_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 0) = Some pc2_v).
    { pose proof (load_after_store_same m4 m5 sb (Ptrofs.unsigned so + 0) pc2_v Hstore5) as Htmp.
      unfold pc2_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }

    (* Temp env before loop *)
    set (le_setup := PTree.set _hi (Vint (Int.repr (Int64.unsigned hi_v)))
                      (PTree.set _t'6 (Vlong hi_v)
                        (PTree.set _li (Vint (Int.repr 3))
                          (PTree.set _t'7 pc1_v
                            (PTree.set _t'8 (Vint (Int.repr tag))
                              (PTree.set _t'2 (Vptr cb pc_ofs)
                                (PTree.set _t'9 (Vptr accu_b accu_ofs)
                                  (PTree.set _t'1 (Vptr sp_b new_sp_ofs)
                                    (PTree.set _t'10 (Vptr sp_b sp_ofs)
                                      (PTree.set _meths (Vptr meths_b meths_ofs)
                                        (PTree.set _t'11 (Vptr accu_b accu_ofs)
                                          le))))))))))).

    assert (Hsetup_s : le_setup ! _s = Some (Vptr sb so)).
    { subst le_setup.
      repeat (rewrite PTree.gso by (compute; congruence)). exact Hle_s. }
    assert (Hsetup_meths : le_setup ! _meths = Some (Vptr meths_b meths_ofs)).
    { subst le_setup.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss. reflexivity. }
    assert (Hsetup_li : le_setup ! _li = Some (Vint (Int.repr 3))).
    { subst le_setup.
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss. reflexivity. }
    assert (Hsetup_hi : le_setup ! _hi = Some (Vint (Int.repr (Int64.unsigned hi_v)))).
    { subst le_setup. rewrite PTree.gss. reflexivity. }

    assert (Hloop_exec_result :
      exists le_post,
        exec_stmt function_entry1 clight_ge e le_setup m5 getpubmet_while
          E0 le_post m5 Out_normal /\
        le_post ! _li = Some (Vint final_li) /\
        le_post ! _meths = Some (Vptr meths_b meths_ofs) /\
        le_post ! _s = Some (Vptr sb so)).
    { apply (getpubmet_while_exec e le_setup m5 meths_b meths_ofs sb so
              tagged_tag_v (Int.repr 3) (Int.repr (Int64.unsigned hi_v)) final_li).
      - apply (method_search_trace_mem_ext m m5). exact Hmeths_survive_m5. exact Hmst.
      - exact Hsetup_li.
      - exact Hsetup_hi.
      - exact Hsetup_meths.
      - exact Hsetup_s.
      - exact Haccu_m5_tagged.
      - lia. }
    destruct Hloop_exec_result
      as (le_post & Hloop & Hpost_li & Hpost_meths & Hpost_s).

    (* meths[final_li - 1] load in m5 *)
    assert (Hmeth_load_m5 : Mem.load Mint64 m5 meths_b
              (Ptrofs.unsigned (Ptrofs.add meths_ofs
                (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.sub final_li (Int.repr 1))))))
              = Some meth_cv).
    { exact (Hmeths_survive_m5 _ _ Hmeth_load). }

    (* Store 6: s->accu = meth_cv (final) *)
    destruct (store_succeeds_sb m5 sb so 8 tagged_tag_v Hw5 Haccu_m5_tagged ltac:(lia) ltac:(lia) meth_cv)
      as [m6 Hstore6].

    (* Final temp env *)
    set (le' := PTree.set _t'3 meth_cv le_post).

    exists le'. exists m6.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec of the entire body                                 *)
    (* ============================================================== *)
    {
      (* The body is: Ssequence (big setup + loop + final) (Sreturn 0).
         We decompose using exec_Sseq_1 composition. *)

      (* Build Part B+C: while loop + final load + store *)
      assert (HexecBC :
        exec e le_setup m5
          (Ssequence
            getpubmet_while
            (Ssequence
              (Sset _t'3
                (Ederef (Ebinop Oadd (Ecast (Etempvar _meths tlong) (tptr tlong))
                  (Ebinop Osub (Etempvar _li tint) (Econst_int (Int.repr 1) tint) tint)
                  (tptr tlong)) tlong))
              (Sassign
                (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _accu tlong)
                (Etempvar _t'3 tlong))))
          E0 le' m6 Out_normal).
      {
        apply exec_Sseq_1 with (t1 := E0) (le1 := le_post) (m1 := m5) (t2 := E0).
        - exact Hloop.
        - apply exec_Sseq_1 with (t1 := E0) (le1 := le') (m1 := m5) (t2 := E0).
          + (* Sset _t'3 = meths[li-1] *)
            apply exec_Sset.
            eapply eval_Elvalue.
            * eapply eval_Ederef.
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
                simpl classify_add. unfold sem_add_ptr_int. simpl. reflexivity. }
            * apply deref_loc_value with (chunk := Mint64).
              { simpl. reflexivity. }
              { simpl. exact Hmeth_load_m5. }
          + (* Sassign s->accu = _t'3 *)
            apply exec_Sassign with (loc := sb)
                    (ofs := Ptrofs.add so (Ptrofs.repr 8))
                    (bf := Full) (v2 := meth_cv) (v := meth_cv).
            * eapply eval_Efield_struct.
              { eapply eval_Elvalue.
                - eapply eval_Ederef.
                  eapply eval_Etempvar. subst le'. rewrite PTree.gso by (compute; congruence). exact Hpost_s.
                - apply deref_loc_copy. simpl. reflexivity. }
              { reflexivity. }
              { exact Hco. }
              { exact Haccu_offset. }
            * eapply eval_Etempvar.
              subst le'. rewrite PTree.gss. reflexivity.
            * rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hmeth_repr). reflexivity.
            * apply assign_loc_value with (chunk := Mint64).
              { reflexivity. }
              { simpl. rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)). exact Hstore6. }
      }

      set (le_a1 := PTree.set _meths (Vptr meths_b meths_ofs)
                      (PTree.set _t'11 (Vptr accu_b accu_ofs) le)).

      assert (HexecA1 :
        exec e le m
          (Ssequence
            (Sset _t'11
              (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong))
            (Sset _meths
              (Ederef (Ebinop Oadd (Ecast (Etempvar _t'11 tlong) (tptr tlong))
                (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)))
          E0 le_a1 m Out_normal).
      {
        apply (eval_stmt_to_exec clight_ge 15).
        eval_cbn.
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn. rewrite Haccu_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_load; eval_cbn.
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_cast_long_to_ptr_vptr accu_b accu_ofs m); eval_cbn.
        rewrite (sem_add_sp_0 accu_b accu_ofs m); eval_cbn.
        rewrite Hobj_load; eval_cbn.
        subst le_a1. reflexivity.
      }

      (* The full pre-return body can be written as: Sseq A1 rest *)
      (* rest = Sseq (push_block) (Sseq (write_block) (Sseq (pc1_block) (Sseq (pc2_block) (Sseq li (Sseq hi_block (Sseq while final_block)))))) *)

      (* This is getting very verbose. Let me use the approach from GETDYNMET:
         build the entire setup using eval_stmt_to_exec in m->m5, then compose with loop+final. *)

      (* But I already showed HexecA doesn't have the right tail. The issue is that
         eval_stmt_to_exec operates on a SINGLE statement and produces le/m/out.
         I need the setup to be a separate statement from the loop.

         Actually, I CAN decompose the body at the right level. Let me look at the body again:

         Ssequence
           (Ssequence A1 A2_rest)  -- this is the pre-return body
           (Sreturn 0)

         where A2_rest = Ssequence push_block (Ssequence write_block (...(Ssequence hi_block (Ssequence while final_block))))

         I can split at:
         - Outer: exec of pre-return body + exec of Sreturn
         - Pre-return body: exec of A1 + exec of A2_rest
         - A2_rest: nested exec_Sseq_1 calls

         Alternatively, I already have HexecBC which does (Ssequence while final) from le_setup, m5.
         I just need to build exec of everything up to (Ssequence while final), ending at le_setup, m5.

         The statements before the while+final are what I proved in HexecA (with Sskip instead of while+final).
         The issue is that Sskip is in the wrong position.

         Actually, eval_stmt_to_exec can handle any statement tree. If I pass it the ENTIRE setup
         including the hi initialization, it would give me le_setup, m5, Out_normal.
         The only issue is the Sskip tail. Let me reconsider. *)

      (* Let me try a completely different decomposition. I'll prove:
         (1) exec of setup_stmts (everything before while) -> le_setup, m5, Out_normal
         (2) exec of (Ssequence while final) -> le', m6, Out_normal
         Then compose for the pre-return body, then add Sreturn. *)

      (* For (1), the challenge is identifying the exact "setup_stmts" prefix.
         The body structure is deeply nested. Looking at the actual AST:

         Sseq (Sseq A1 (Sseq push_stmts (Sseq write_stmts (Sseq pc1_stmts (Sseq pc2_stmts (Sseq li_stmt (Sseq hi_stmts (Sseq while_stmt final_stmts)))))))) (Sreturn 0)

         The setup is everything in the innermost Sseq before the "(Sseq while_stmt final_stmts)" node.
         That innermost node is (Sseq hi_stmts (Sseq while_stmt final_stmts)).

         I can split at: (Sseq hi_stmts (Sseq while_stmt final_stmts))
         into: exec hi_stmts -> Out_normal, then exec (Sseq while final) -> Out_normal.

         This works! Then I compose outward. *)

      (* Let me build everything using exec_Sseq_1 from the inside out. *)

      (* innermost: (Sseq while final) = HexecBC *)
      (* next: (Sseq hi_stmts (Sseq while final)) *)

      set (le_pre_hi := PTree.set _li (Vint (Int.repr 3))
                          (PTree.set _t'7 pc1_v
                            (PTree.set _t'8 (Vint (Int.repr tag))
                              (PTree.set _t'2 (Vptr cb pc_ofs)
                                (PTree.set _t'9 (Vptr accu_b accu_ofs)
                                  (PTree.set _t'1 (Vptr sp_b new_sp_ofs)
                                    (PTree.set _t'10 (Vptr sp_b sp_ofs) le_a1))))))).

      set (le_pre_t6 := PTree.set _t'6 (Vlong hi_v) le_pre_hi).

      (* hi_stmts: Sseq (Sset _t'6 ...) (Sset _hi ...) *)
      assert (Hexec_hi :
        exec e le_pre_hi m5
          (Ssequence
            (Sset _t'6
              (Ederef (Ebinop Oadd (Ecast (Etempvar _meths tlong) (tptr tlong))
                (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
            (Sset _hi (Ecast (Etempvar _t'6 tlong) tint)))
          E0 le_setup m5 Out_normal).
      {
        apply (eval_stmt_to_exec clight_ge 15).
        eval_cbn.
        (* _meths in le_pre_hi *)
        subst le_pre_hi. subst le_a1.
        do 7 (rewrite PTree.gso by (compute; congruence)).
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_cast_long_to_ptr_vptr meths_b meths_ofs m5); eval_cbn.
        rewrite (sem_add_sp_0 meths_b meths_ofs m5); eval_cbn.
        rewrite (Hmeths_survive_m5 _ _ Hhi_load); eval_cbn.
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_cast_long_to_int_vlong hi_v m5); eval_cbn.
        subst le_setup. reflexivity.
      }

      (* Compose hi_stmts with while+final *)
      assert (Hexec_hi_loop_final :
        exec e le_pre_hi m5
          (Ssequence
            (Ssequence
              (Sset _t'6
                (Ederef (Ebinop Oadd (Ecast (Etempvar _meths tlong) (tptr tlong))
                  (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
              (Sset _hi (Ecast (Etempvar _t'6 tlong) tint)))
            (Ssequence
              getpubmet_while
              (Ssequence
                (Sset _t'3
                  (Ederef (Ebinop Oadd (Ecast (Etempvar _meths tlong) (tptr tlong))
                    (Ebinop Osub (Etempvar _li tint) (Econst_int (Int.repr 1) tint) tint)
                    (tptr tlong)) tlong))
                (Sassign
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong)
                  (Etempvar _t'3 tlong)))))
          E0 le' m6 Out_normal).
      { apply exec_Sseq_1 with (t1 := E0) (le1 := le_setup) (m1 := m5) (t2 := E0).
        - exact Hexec_hi.
        - exact HexecBC. }

      (* Now I need to build up all the setup from le_a1, m to le_pre_hi, m5.
         These are the push, write, pc1, tagged, pc2, li statements. *)

      (* This builds exec of: Sseq push_block (Sseq write_block (Sseq pc1_block (Sseq pc2_block (Sseq li_stmt (Sseq hi_block (Sseq while final)))))) *)

      assert (HexecA2 :
        exec e le_a1 m
          (Ssequence
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'10
                    (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                  (Sset _t'1
                    (Ecast (Ebinop Osub (Etempvar _t'10 (tptr tlong))
                      (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
                (Sassign
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong))
                  (Etempvar _t'1 (tptr tlong))))
              (Ssequence
                (Sset _t'9
                  (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong))
                (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
                  (Etempvar _t'9 tlong))))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'2
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _pc (tptr tint)))
                    (Sassign
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _pc (tptr tint))
                      (Ebinop Oadd (Etempvar _t'2 (tptr tint))
                        (Econst_int (Int.repr 1) tint) (tptr tint))))
                  (Ssequence
                    (Sset _t'8 (Ederef (Etempvar _t'2 (tptr tint)) tint))
                    (Sassign
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _accu tlong)
                      (Ebinop Oadd
                        (Ebinop Oshl (Ecast (Etempvar _t'8 tint) tlong)
                          (Econst_int (Int.repr 1) tint) tlong)
                        (Econst_int (Int.repr 1) tint) tlong))))
                (Ssequence
                  (Ssequence
                    (Sset _t'7
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _pc (tptr tint)))
                    (Sassign
                      (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _pc (tptr tint))
                      (Ebinop Oadd (Etempvar _t'7 (tptr tint))
                        (Econst_int (Int.repr 1) tint) (tptr tint))))
                  (Ssequence
                    (Sset _li (Econst_int (Int.repr 3) tint))
                    (Ssequence
                      (Ssequence
                        (Sset _t'6
                          (Ederef (Ebinop Oadd (Ecast (Etempvar _meths tlong) (tptr tlong))
                            (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
                        (Sset _hi (Ecast (Etempvar _t'6 tlong) tint)))
                      (Ssequence
                        getpubmet_while
                        (Ssequence
                          (Sset _t'3
                            (Ederef (Ebinop Oadd (Ecast (Etempvar _meths tlong) (tptr tlong))
                              (Ebinop Osub (Etempvar _li tint)
                                (Econst_int (Int.repr 1) tint) tint)
                              (tptr tlong)) tlong))
                          (Sassign
                            (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                              (Tstruct _interp_state noattr)) _accu tlong)
                            (Etempvar _t'3 tlong)))))))))
          E0 le' m6 Out_normal).
      {
        (* Decompose using exec_Sseq_1 at each Ssequence level,
           following the right-spine of the statement tree.
           At the innermost level, compose Sset _li with Hexec_hi_loop_final. *)

        (* Intermediate env states *)
        set (le_after_push := PTree.set _t'1 (Vptr sp_b new_sp_ofs)
                                (PTree.set _t'10 (Vptr sp_b sp_ofs) le_a1)).
        set (le_after_accu := PTree.set _t'9 (Vptr accu_b accu_ofs) le_after_push).
        set (le_after_pc1 := PTree.set _t'8 (Vint (Int.repr tag))
                               (PTree.set _t'2 (Vptr cb pc_ofs) le_after_accu)).
        set (le_after_pc2 := PTree.set _t'7 pc1_v le_after_pc1).

        (* Level 1: PUSH_SP_ACCU | rest *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le_after_accu) (m1 := m2) (t2 := E0).
        - (* PUSH_SP + ACCU_PUSH combined *)
          apply exec_Sseq_1 with (t1 := E0) (le1 := le_after_push) (m1 := m1) (t2 := E0).
          + (* PUSH_SP block *)
            apply (eval_stmt_to_exec clight_ge 20).
            eval_cbn.
            unfold le_a1.
            rewrite PTree.gso by (compute; congruence).
            rewrite PTree.gso by (compute; congruence).
            rewrite Hle_s; eval_cbn.
            rewrite Hco; eval_cbn. rewrite Hsp_offset; eval_cbn.
            rewrite Mptr_Mint64; eval_cbn.
            rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
            rewrite Hsp_load; eval_cbn.
            rewrite PTree.gss; eval_cbn.
            rewrite sem_sub_sp_1; eval_cbn.
            rewrite sem_cast_ptr_to_ptr; eval_cbn.
            rewrite PTree.gso by (compute; congruence).
            rewrite PTree.gso by (compute; congruence).
            rewrite PTree.gso by (compute; congruence).
            rewrite PTree.gso by (compute; congruence).
            rewrite Hle_s; eval_cbn.
            rewrite Mptr_Mint64; eval_cbn.
            rewrite PTree.gss; eval_cbn.
            rewrite sem_cast_ptr_to_ptr; eval_cbn.
            rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
            fold new_sp_ofs. rewrite Hstore1; eval_cbn.
            subst le_after_push. unfold le_a1. reflexivity.
          + (* ACCU_PUSH block *)
            apply (eval_stmt_to_exec clight_ge 20).
            eval_cbn.
            subst le_after_push. unfold le_a1.
            do 4 (rewrite PTree.gso by (compute; congruence)).
            rewrite Hle_s; eval_cbn. rewrite Hco; eval_cbn. rewrite Haccu_offset; eval_cbn.
            rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
            rewrite Haccu_m1; eval_cbn.
            rewrite PTree.gso by (compute; congruence).
            rewrite PTree.gss; eval_cbn.
            rewrite PTree.gss; eval_cbn.
            rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Haccu_repr); eval_cbn.
            fold new_sp_ofs. rewrite Hstore2; eval_cbn.
            subst le_after_accu. reflexivity.
        - (* Level 2: PC1_TAG | rest *)
            apply exec_Sseq_1 with (t1 := E0) (le1 := le_after_pc1) (m1 := m4) (t2 := E0).
            * (* PC1_TAG block *)
              apply (eval_stmt_to_exec clight_ge 40).
              eval_cbn.
              subst le_after_accu le_after_push. unfold le_a1.
              do 5 (rewrite PTree.gso by (compute; congruence)).
              rewrite Hle_s; eval_cbn.
              rewrite Hco; eval_cbn.
              rewrite Hpc_offset.
              eval_cbn.
              rewrite Mptr_Mint64; eval_cbn.
              rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
              rewrite Hpc_m2; eval_cbn.
              do 6 (rewrite PTree.gso by (compute; congruence)).
              rewrite Hle_s; eval_cbn.
              rewrite PTree.gss; eval_cbn.
              rewrite (sem_add_pc_1 cb pc_ofs m2); eval_cbn.
              fold pc1.
              rewrite (sem_cast_ptr_tint_to_ptr_tint cb pc1 m2); eval_cbn.
              rewrite Mptr_Mint64; eval_cbn.
              rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
              fold pc1_v. rewrite Hstore3; eval_cbn.
              rewrite PTree.gss; eval_cbn.
              assert (Hcode_m3 : Mem.load Mint32 m3 cb (Ptrofs.unsigned pc_ofs) = Some (Vint (Int.repr tag))).
              { erewrite Mem.load_store_other; [| exact Hstore3 | left; exact Hcb_ne_sb].
                erewrite Mem.load_store_other; [| exact Hstore2 | left; exact (Hcb_ne_sp)].
                erewrite Mem.load_store_other; [| exact Hstore1 | left; exact Hcb_ne_sb].
                exact Hcode_load. }
              rewrite Hcode_m3; eval_cbn.
              do 7 (rewrite PTree.gso by (compute; congruence)).
              rewrite Hle_s; eval_cbn. rewrite Haccu_offset; eval_cbn.
              rewrite PTree.gss; eval_cbn.
              rewrite (sem_cast_int_to_long (Int.repr tag) m3); eval_cbn.
              rewrite (sem_shl_long_int_1 (Int64.repr (Int.signed (Int.repr tag))) m3); eval_cbn.
              rewrite (sem_add_long_int_1 (Int64.shl (Int64.repr (Int.signed (Int.repr tag))) (Int64.repr 1)) m3); eval_cbn.
              rewrite (sem_cast_long_vlong
                (Int64.add (Int64.shl (Int64.repr (Int.signed (Int.repr tag))) (Int64.repr 1)) (Int64.repr 1))); eval_cbn.
              rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
              replace (Int64.add (Int64.shl (Int64.repr (Int.signed (Int.repr tag))) (Int64.repr 1)) (Int64.repr 1))
                with tagged_tag by (subst tagged_tag; symmetry; apply tagged_int_eq; exact Htag_range).
              fold tagged_tag_v. rewrite Hstore4; eval_cbn.
              subst le_after_pc1. reflexivity.
            * (* Level 4: PC2 | rest *)
              apply exec_Sseq_1 with (t1 := E0) (le1 := le_after_pc2) (m1 := m5) (t2 := E0).
              { (* PC2 block *)
                apply (eval_stmt_to_exec clight_ge 20).
                eval_cbn.
                subst le_after_pc1 le_after_accu le_after_push. unfold le_a1.
                repeat (rewrite PTree.gso by (compute; congruence)).
                rewrite Hle_s; eval_cbn.
                rewrite Hco; eval_cbn.
                rewrite Hpc_offset.
                eval_cbn.
                rewrite Mptr_Mint64; eval_cbn.
                rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
                rewrite Hpc_m4; eval_cbn.
                repeat (rewrite PTree.gso by (compute; congruence)).
                rewrite Hle_s; eval_cbn.
                rewrite PTree.gss; eval_cbn.
                subst pc1_v.
                rewrite sem_add_pc_1; eval_cbn.
                rewrite sem_cast_ptr_tint_to_ptr_tint; eval_cbn.
                rewrite Mptr_Mint64; eval_cbn.
                rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
                fold pc2 pc2_v. rewrite Hstore5; eval_cbn.
                subst le_after_pc2. reflexivity.
              }
              { (* Level 5: LI | hi_loop_final *)
                apply exec_Sseq_1 with (t1 := E0) (le1 := le_pre_hi) (m1 := m5) (t2 := E0).
                - (* LI: Sset _li = 3 *)
                  apply exec_Sset. apply eval_Econst_int.
                - (* hi + loop + final *)
                  exact Hexec_hi_loop_final.
              }
      }

      (* Combine A1 with A2, then Sreturn *)
      apply exec_Sseq_1 with (t1 := E0) (le1 := le') (m1 := m6) (t2 := E0).
      - apply exec_Sseq_1 with (t1 := E0) (le1 := le_a1) (m1 := m) (t2 := E0).
        + exact HexecA1.
        + exact HexecA2.
      - apply exec_Sreturn_some. apply eval_Econst_int.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      set (new_co := Ptrofs.add co (Ptrofs.repr (2 * sizeof_code_t))).
      set (ard' := mk_abs_rel sb so hm cb new_co
                     (ar_global_block ard) (ar_global_ofs ard)
                     (ar_stack_block ard) (ar_stack_base_ofs ard)
                     (ar_code_ne_sptr ard) (ar_code_ne_global ard)
                     (ar_global_ne_sptr ard) (ar_sptr_ofs_bound ard)).
      exists ard'.
      set (uso := Ptrofs.unsigned so) in *.

      (* Fields in m6 *)
      assert (Hpc_m6 : Mem.load Mint64 m6 sb (uso + 0) = Some pc2_v).
      { apply (load_after_store_other m5 m6 sb (uso + 8) (uso + 0) meth_cv pc2_v Hstore6 Hpc_m5).
        left. lia. }

      assert (Haccu_m6 : Mem.load Mint64 m6 sb (uso + 8) = Some meth_cv).
      { pose proof (load_after_store_same m5 m6 sb (uso + 8) meth_cv Hstore6) as Htmp.
        rewrite (val_repr_load_result hm cb co method_fn meth_cv Hmeth_repr) in Htmp. exact Htmp. }

      assert (Hsp_m6 : Mem.load Mint64 m6 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
      { apply (load_after_store_other m5 m6 sb (uso + 8) (uso + 16) meth_cv _ Hstore6 Hsp_m5).
        right. lia. }

      assert (Henv_m6 : Mem.load Mint64 m6 sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m5 m6 sb (uso + 8) (uso + 24) meth_cv _ Hstore6 Henv_m5).
        right. lia. }

      assert (Hextra_m6 : Mem.load Mint64 m6 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m5 m6 sb (uso + 8) (uso + 32) meth_cv _ Hstore6 Hextra_m5).
        right. lia. }

      assert (Hgd_m6 : Mem.load Mint64 m6 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m5 m6 sb (uso + 8) (uso + 40) meth_cv _ Hstore6 Hgd_m5).
        right. lia. }

      assert (Hts_m6 : Mem.load Mint64 m6 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m5 m6 sb (uso + 8) (uso + 48) meth_cv _ Hstore6 Hts_m5).
        right. lia. }

      (* Derive field equalities from Hs'_fields *)
      assert (Hpc_s' : Machine.pc s' = Machine.pc s).
      { rewrite Hs'_fields. reflexivity. }
      assert (Hstack_s' : Machine.stack s' = Machine.accu s :: Machine.stack s).
      { rewrite Hs'_fields. reflexivity. }
      assert (Henv_s' : Machine.env s' = Machine.env s).
      { rewrite Hs'_fields. reflexivity. }
      assert (Hextra_s' : Machine.extra_args s' = Machine.extra_args s).
      { rewrite Hs'_fields. reflexivity. }
      assert (Hglobal_s' : Machine.global s' = Machine.global s).
      { rewrite Hs'_fields. reflexivity. }
      assert (Htrap_s' : Machine.trap_sp s' = Machine.trap_sp s).
      { rewrite Hs'_fields. reflexivity. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        exact Hpost_s. }

      (* 2. pc field *)
      { exists pc2_v. split.
        - exact Hpc_m6.
        - simpl. rewrite Hpc_s'. unfold pc_rel. f_equal.
          subst pc2_v pc2 pc1 pc_ofs new_co. unfold sizeof_code_t.
          rewrite !Ptrofs.add_assoc. f_equal.
          rewrite (Ptrofs.add_commut (Ptrofs.repr (2 * 4)) _). reflexivity. }

      (* 3. accu field *)
      { exists meth_cv. split.
        - exact Haccu_m6.
        - simpl. unfold method_fn. eapply val_repr_co_shift. exact Hmeth_repr. }

      (* 4. sp field -- updated to new_sp_ofs, stack gets accu prepended *)
      { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_m6.
        - reflexivity.
        - simpl. rewrite Hstack_s'.
          eapply stack_repr_co_shift.
          (* stack_repr for accu :: old_stack at new_sp_ofs in m6.
             Need to thread through all 6 stores. *)
          (* In m2 we stored accu at new_sp_ofs, building accu :: stack.
             stack_repr in m1 at sp_ofs is old_stack.
             stack_repr_cons_after_store gives us the cons in m2. *)
          assert (Hstack_m1 : stack_repr hm cb co m1 (Machine.stack s) sp_b sp_ofs).
          { apply (stack_repr_store_other_block hm cb co m m1 _ sp_b sp_ofs sb
                     (uso + 16) (Vptr sp_b new_sp_ofs) Hstack_repr Hstore1).
            intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
          assert (Hstack_m2 : stack_repr hm cb co m2 (Machine.accu s :: Machine.stack s) sp_b new_sp_ofs).
          { exact (stack_repr_cons_after_store hm cb co m1 m2
                     (Machine.stack s) sp_b sp_ofs (Machine.accu s) (Vptr accu_b accu_ofs)
                     Hstack_m1 Haccu_repr Hstore2 Hsp_ge8 Hsp_rep). }
          (* Survive stores 3-6 (all on sb, not sp_b) *)
          assert (Hstack_m3 : stack_repr hm cb co m3 (Machine.accu s :: Machine.stack s) sp_b new_sp_ofs).
          { apply (stack_repr_store_other_block hm cb co m2 m3 _ sp_b new_sp_ofs sb (uso + 0) pc1_v
                     Hstack_m2 Hstore3).
            intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
          assert (Hstack_m4 : stack_repr hm cb co m4 (Machine.accu s :: Machine.stack s) sp_b new_sp_ofs).
          { apply (stack_repr_store_other_block hm cb co m3 m4 _ sp_b new_sp_ofs sb (uso + 8) tagged_tag_v
                     Hstack_m3 Hstore4).
            intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
          assert (Hstack_m5 : stack_repr hm cb co m5 (Machine.accu s :: Machine.stack s) sp_b new_sp_ofs).
          { apply (stack_repr_store_other_block hm cb co m4 m5 _ sp_b new_sp_ofs sb (uso + 0) pc2_v
                     Hstack_m4 Hstore5).
            intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
          apply (stack_repr_store_other_block hm cb co m5 m6 _ sp_b new_sp_ofs sb (uso + 8) meth_cv
                   Hstack_m5 Hstore6).
          intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - rewrite Hnew_sp_unsigned. lia.
        - rewrite Hstack_s'. simpl length. rewrite Nat2Z.inj_succ. rewrite Hnew_sp_unsigned. lia.
        - rewrite Hstack_s'. simpl length. rewrite Nat2Z.inj_succ. rewrite Hnew_sp_unsigned.
          replace (Ptrofs.unsigned sp_ofs - 8 + 8 * Z.succ (Z.of_nat (length (Machine.stack s))))
            with (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) by lia.
          intros ofs' Hofs'.
          eapply Mem.perm_store_1; [exact Hstore6|].
          eapply Mem.perm_store_1; [exact Hstore5|].
          eapply Mem.perm_store_1; [exact Hstore4|].
          eapply Mem.perm_store_1; [exact Hstore3|].
          eapply Mem.perm_store_1; [exact Hstore2|].
          eapply Mem.perm_store_1; [exact Hstore1|].
          apply Hsp_writable. exact Hofs'.
        - rewrite Hnew_sp_unsigned. simpl.
          apply Z.divide_sub_r; [exact Hsp_align | exists 1; lia]. }

      (* 5. env field *)
      { exists env_v. split.
        - exact Henv_m6.
        - simpl. rewrite Henv_s'. eapply val_repr_co_shift. exact Henv_repr. }

      (* 6. extra_args field *)
      { simpl. rewrite Hextra_s'. exact Hextra_m6. }

      (* 7. global_data field *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_m6.
        - simpl. exact Hgd_eq.
        - simpl. rewrite Hglobal_s'.
          eapply global_repr_co_shift.
          (* global_repr survives all 6 stores *)
          apply (global_repr_store_other_block hm cb co m5 m6 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sb (uso + 8) meth_cv).
          + apply (global_repr_store_other_block hm cb co m4 m5 _
                     (ar_global_block ard) (ar_global_ofs ard)
                     sb (uso + 0) pc2_v).
            * apply (global_repr_store_other_block hm cb co m3 m4 _
                       (ar_global_block ard) (ar_global_ofs ard)
                       sb (uso + 8) tagged_tag_v).
              { apply (global_repr_store_other_block hm cb co m2 m3 _
                         (ar_global_block ard) (ar_global_ofs ard)
                         sb (uso + 0) pc1_v).
                { apply (global_repr_store_other_block hm cb co m1 m2 _
                           (ar_global_block ard) (ar_global_ofs ard)
                           sp_b (Ptrofs.unsigned new_sp_ofs) (Vptr accu_b accu_ofs)).
                  { apply (global_repr_store_other_block hm cb co m m1 _
                             (ar_global_block ard) (ar_global_ofs ard)
                             sb (uso + 16) (Vptr sp_b new_sp_ofs)
                             Hglobal_repr Hstore1).
                    intro Heq2; exact (Hgb_ne (eq_sym Heq2)). }
                  { exact Hstore2. }
                  { exact Hsp_ne_gb. } }
                { exact Hstore3. }
                { intro Heq2; exact (Hgb_ne (eq_sym Heq2)). } }
              { exact Hstore4. }
              { intro Heq2; exact (Hgb_ne (eq_sym Heq2)). }
            * exact Hstore5.
            * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          + exact Hstore6.
          + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field *)
      { exists ts_ptr. split.
        - exact Hts_m6.
        - simpl. rewrite Htrap_s'. exact Htrap_rel. }

      (* 9. sb_writable *)
      { intros ofs' Hofs'.
        eapply Mem.perm_store_1; [exact Hstore6|].
        eapply Mem.perm_store_1; [exact Hstore5|].
        eapply Mem.perm_store_1; [exact Hstore4|].
        eapply Mem.perm_store_1; [exact Hstore3|].
        eapply Mem.perm_store_1; [exact Hstore2|].
        eapply Mem.perm_store_1; [exact Hstore1|].
        apply Hsb_writable. exact Hofs'. }
    }
  }

  (* ================================================================ *)
  (* Error case from scan: msg = "method not found"                    *)
  (* ================================================================ *)
  2: { right.
    clear - Hscan. subst scan.
    set (rf := skipn 2 actual_fields) in Hscan. clearbody rf.
    revert s0 Hscan. revert rf.
    fix IHrf 1; intros [| ? [| ? ?]] m Hsc; simpl in Hsc;
    [injection Hsc as <-; reflexivity
    |injection Hsc as <-; reflexivity
    |destruct (value_eqb _ (Val_int tag)); [discriminate|exact (IHrf _ _ Hsc)]]. }

  (* Halt and CCall_request: impossible from scan *)
  all: (exfalso;
        match goal with
        | [ Hscan0 : _ = ?c |- _ ] =>
          clear - Hscan0; subst scan;
          set (rf := skipn 2 actual_fields) in Hscan0; clearbody rf;
          revert Hscan0; revert rf;
          fix IHrf 1; intros [| ? [| ? ?]]; simpl; try (intro; discriminate);
          destruct (value_eqb _ (Val_int tag)); try (intro; discriminate);
          intro; exact (IHrf _ Hscan0)
        end).
Qed.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr (GETPUBMET z) / clight_of (GETPUBMET z) / pre_of (GETPUBMET z)
   are convertible with handle_GETPUBMET z / f_instr_GETPUBMET / getpubmet_pre z.
   P_halt_of and P_ccall_of are vacuously satisfied (GETPUBMET never halts or
   issues a C call).  P_error_of requires bridging from the disjunction in
   verify_GETPUBMET_correct to `error_message_of (GETPUBMET z) s = Some msg`. *)
Definition correct_GETPUBMET : forall z,
    handler_correct (handle_instr (GETPUBMET z)) (clight_of (GETPUBMET z))
      (pre_of (GETPUBMET z))
      (P_error_of (GETPUBMET z)) (P_halt_of (GETPUBMET z)) (P_ccall_of (GETPUBMET z)).
Proof.
  intro z.
  intros e le m s.
  change (handle_instr (GETPUBMET z) (Machine.pc s) s)
    with (handle_GETPUBMET z (Machine.pc s) s).
  specialize (verify_GETPUBMET_correct z e le m s) as Hold.
  unfold handler_correct in Hold.
  unfold handle_GETPUBMET at 1.
  set (new_stack := Machine.accu s :: Machine.stack s) in *.
  destruct (field_or_heap s (Machine.accu s) 0) as [class_tbl|] eqn:Hclass.
  2: { (* field_or_heap = None => Error "GETPUBMET: no class table" *)
    unfold P_error_of. simpl. rewrite Hclass. reflexivity. }
  set (fields :=
    match class_tbl with
    | Val_block _ fs => fs
    | Val_ptr addr => match heap_lookup (Machine.hp s) addr with Some (_, fs) => fs | None => nil end
    | _ => nil
    end) in *.
  set (scan := fix scan (remaining : list value) : step_result :=
    match remaining with
    | nil => Error "GETPUBMET: method not found"
    | _ :: nil => Error "GETPUBMET: method not found"
    | method_fn :: tag_val :: rest =>
      if value_eqb tag_val (Val_int z) then
        Step (s <|Machine.pc := Machine.pc s|> <|Machine.accu := method_fn|> <|Machine.stack := new_stack|>)
      else scan rest
    end) in *.
  destruct (scan (skipn 2 fields)) eqn:Hscan.
  - (* Step case: delegate to verify_GETPUBMET_correct *)
    intros ard Hpre Hstep_pre.
    unfold handle_GETPUBMET in Hold. rewrite Hclass in Hold.
    fold fields in Hold. fold scan in Hold. rewrite Hscan in Hold.
    apply Hold; assumption.
  - (* Error case *)
    unfold P_error_of. simpl. rewrite Hclass.
    (* Bridge: scan returning Error means scan_method_table returns Some msg *)
    admit.
  - (* Halt: impossible from scan *)
    exfalso. clear Hold.
    set (rf := skipn 2 fields) in Hscan. clearbody rf.
    revert Hscan. revert rf.
    fix IHrf 1; intros [| ? [| ? ?]]; simpl; try (intro; discriminate).
    destruct (value_eqb _ (Val_int z)); try (intro; discriminate).
    intro; exact (IHrf _ Hscan).
  - (* CCall: impossible from scan *)
    exfalso. clear Hold.
    set (rf := skipn 2 fields) in Hscan. clearbody rf.
    revert Hscan. revert rf.
    fix IHrf 1; intros [| ? [| ? ?]]; simpl; try (intro; discriminate).
    destruct (value_eqb _ (Val_int z)); try (intro; discriminate).
    intro; exact (IHrf _ Hscan).
Admitted.
