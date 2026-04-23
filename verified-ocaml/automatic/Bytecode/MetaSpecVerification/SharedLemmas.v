(* SharedLemmas.v - [UNTRUSTED] Shared axioms and derived lemmas for
   per-instruction handler uniqueness proofs.

   The generic uniqueness proof is parameterised over an abstract state S,
   a witness type W, an abstraction relation R : Clight.env -> temp_env ->
   mem -> S -> W -> Prop, and pc extraction pc_of : S -> Z.  The Section
   hypotheses R_total and R_functional supply the totality and functionality
   properties for the fully generic theorem.

   handler_correct_gen now takes err : S -> option string instead of P_error.
   When err s = Some msg, the handler must return Error msg.
   When err s = None, Error is False, and Step/Halt/CCall have exec_stmt
   returning fixed integer codes (0/1/3).

   The concrete closed helpers additionally assume abs_rel totality and
   functionality for compatibility with the current fine-grained MetaSpec
   surface. *)

From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Coqlib Integers Ctypes Cop Clight ClightBigstep Events Globalenvs Memory Values.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.

(* ================================================================== *)
(* Fine-grained determinism facts for the E0 Clight executions used by
   handler_correct.  Full trace equality is too strong for CompCert
   external calls; the handler specs use [clight_returns], whose trace is
   fixed to [E0]. *)
(* ================================================================== *)

Lemma load_bitfield_deterministic :
  forall ty sz sg pos width m addr v1 v2,
    load_bitfield ty sz sg pos width m addr v1 ->
    load_bitfield ty sz sg pos width m addr v2 ->
    v1 = v2.
Proof.
  intros. inv H; inv H0. congruence.
Qed.

Lemma store_bitfield_deterministic :
  forall ty sz sg pos width m addr v m1 v1 m2 v2,
    store_bitfield ty sz sg pos width m addr v m1 v1 ->
    store_bitfield ty sz sg pos width m addr v m2 v2 ->
    m1 = m2 /\ v1 = v2.
Proof.
  intros. inv H; inv H0. split; congruence.
Qed.

Lemma deref_loc_deterministic :
  forall ty m b ofs bf v1 v2,
    deref_loc ty m b ofs bf v1 ->
    deref_loc ty m b ofs bf v2 ->
    v1 = v2.
Proof.
  intros. inv H; inv H0; try congruence.
  eapply load_bitfield_deterministic; eauto.
Qed.

Lemma assign_loc_deterministic :
  forall ce ty m b ofs bf v m1 m2,
    assign_loc ce ty m b ofs bf v m1 ->
    assign_loc ce ty m b ofs bf v m2 ->
    m1 = m2.
Proof.
  intros. inv H; inv H0; try congruence.
  - destruct (store_bitfield_deterministic
        _ _ _ _ _ _ _ _ _ _ _ _ H1 H7); auto.
Qed.

Lemma eval_expr_lvalue_deterministic :
  forall ge e le m,
  (forall a v1,
    eval_expr ge e le m a v1 ->
    forall v2, eval_expr ge e le m a v2 -> v1 = v2)
  /\
  (forall a b1 ofs1 bf1,
    eval_lvalue ge e le m a b1 ofs1 bf1 ->
    forall b2 ofs2 bf2,
      eval_lvalue ge e le m a b2 ofs2 bf2 ->
      b1 = b2 /\ ofs1 = ofs2 /\ bf1 = bf2).
Proof.
  intros ge e le m.
  apply (eval_expr_lvalue_ind ge e le m
    (fun a v1 =>
       forall v2, eval_expr ge e le m a v2 -> v1 = v2)
    (fun a b1 ofs1 bf1 =>
       forall b2 ofs2 bf2,
         eval_lvalue ge e le m a b2 ofs2 bf2 ->
         b1 = b2 /\ ofs1 = ofs2 /\ bf1 = bf2)); intros.
  - inv H; auto.
    match goal with
    | Hlv: eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ => inv Hlv
    end.
  - inv H; auto.
    match goal with
    | Hlv: eval_lvalue _ _ _ _ (Econst_float _ _) _ _ _ |- _ => inv Hlv
    end.
  - inv H; auto.
    match goal with
    | Hlv: eval_lvalue _ _ _ _ (Econst_single _ _) _ _ _ |- _ => inv Hlv
    end.
  - inv H; auto.
    match goal with
    | Hlv: eval_lvalue _ _ _ _ (Econst_long _ _) _ _ _ |- _ => inv Hlv
    end.
  - inv H0; try congruence.
    match goal with
    | Hlv: eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inv Hlv
    end.
  - inv H1.
    + exploit H0; eauto. intros (? & ? & ?). subst. auto.
    + match goal with
      | Hlv: eval_lvalue _ _ _ _ (Eaddrof _ _) _ _ _ |- _ => inv Hlv
      end.
  - inv H2.
    + exploit H0; eauto. intros. subst. congruence.
    + match goal with
      | Hlv: eval_lvalue _ _ _ _ (Eunop _ _ _) _ _ _ |- _ => inv Hlv
      end.
  - inv H4.
    + exploit H0; eauto. intros. subst.
      exploit H2; eauto. intros. subst.
      congruence.
    + match goal with
      | Hlv: eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inv Hlv
      end.
  - inv H2.
    + exploit H0; eauto. intros. subst. congruence.
    + match goal with
      | Hlv: eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inv Hlv
      end.
  - inv H; auto.
    match goal with
    | Hlv: eval_lvalue _ _ _ _ (Esizeof _ _) _ _ _ |- _ => inv Hlv
    end.
  - inv H; auto.
    match goal with
    | Hlv: eval_lvalue _ _ _ _ (Ealignof _ _) _ _ _ |- _ => inv Hlv
    end.
  - inv H2; try solve [inv H; congruence].
    exploit H0; eauto. intros (? & ? & ?). subst.
    eapply deref_loc_deterministic; eauto.
  - inv H0; try congruence; repeat split; congruence.
  - inv H1; try congruence; repeat split; congruence.
  - inv H1.
    exploit H0; eauto. intros. subst. repeat split; congruence.
  - inv H4; try congruence.
    exploit H0; eauto. intros. subst. repeat split; congruence.
  - inv H4; try congruence.
    exploit H0; eauto. intros. subst. repeat split; congruence.
Qed.

Lemma eval_expr_deterministic :
  forall ge e le m a v1 v2,
    eval_expr ge e le m a v1 ->
    eval_expr ge e le m a v2 ->
    v1 = v2.
Proof.
  intros. eapply (proj1 (eval_expr_lvalue_deterministic ge e le m)); eauto.
Qed.

Lemma eval_lvalue_deterministic :
  forall ge e le m a b1 ofs1 bf1 b2 ofs2 bf2,
    eval_lvalue ge e le m a b1 ofs1 bf1 ->
    eval_lvalue ge e le m a b2 ofs2 bf2 ->
    b1 = b2 /\ ofs1 = ofs2 /\ bf1 = bf2.
Proof.
  intros. eapply (proj2 (eval_expr_lvalue_deterministic ge e le m)); eauto.
Qed.

Lemma eval_exprlist_deterministic :
  forall ge e le m al tyl vl1,
    eval_exprlist ge e le m al tyl vl1 ->
    forall vl2, eval_exprlist ge e le m al tyl vl2 -> vl1 = vl2.
Proof.
  induction 1; intros vl2 H2; inv H2; auto.
  assert (v1 = v0) by (eapply eval_expr_deterministic; eauto).
  subst v0.
  assert (v2 = v3) by congruence.
  assert (vl = vl0) by eauto.
  subst. reflexivity.
Qed.

Lemma alloc_variables_deterministic :
  forall ge e m vars e1 m1 e2 m2,
    alloc_variables ge e m vars e1 m1 ->
    alloc_variables ge e m vars e2 m2 ->
    e1 = e2 /\ m1 = m2.
Proof.
  intros ge e m vars e1 m1 e2 m2 H1.
  revert e2 m2.
  induction H1; intros e2' m2' H2; inv H2; auto.
  rewrite H in H9. inv H9.
  eapply IHalloc_variables; eauto.
Qed.

Lemma bind_parameters_deterministic :
  forall ge e m params args m1 m2,
    bind_parameters ge e m params args m1 ->
    bind_parameters ge e m params args m2 ->
    m1 = m2.
Proof.
  intros ge e m params args m1 m2 H1.
  revert m2.
  induction H1; intros m2' H2; inv H2; auto.
  assert (b = b0) by congruence. subst b0.
  assert (m1 = m3) by (eapply assign_loc_deterministic; eauto).
  subst m3. eauto.
Qed.

Lemma function_entry1_deterministic :
  forall ge f vargs m e1 le1 m1 e2 le2 m2,
    function_entry1 ge f vargs m e1 le1 m1 ->
    function_entry1 ge f vargs m e2 le2 m2 ->
    e1 = e2 /\ le1 = le2 /\ m1 = m2.
Proof.
  intros. inv H; inv H0.
  destruct (alloc_variables_deterministic
    ge empty_env m (fn_params f ++ fn_vars f) e1 m0 e2 m3 H2 H4)
    as [? ?]. subst e2 m3.
  assert (m1 = m2) by (eapply bind_parameters_deterministic; eauto).
  subst m2. auto.
Qed.

Lemma out_break_or_return_deterministic :
  forall out out1 out2,
    out_break_or_return out out1 ->
    out_break_or_return out out2 ->
    out1 = out2.
Proof.
  intros. inv H; inv H0; auto.
Qed.

Lemma out_break_or_return_not_normal_or_continue :
  forall out out',
    out_break_or_return out out' ->
    out_normal_or_continue out ->
    False.
Proof.
  intros. inv H; inv H0.
Qed.

Lemma outcome_result_value_deterministic :
  forall out ty v1 m v2,
    outcome_result_value out ty v1 m ->
    outcome_result_value out ty v2 m ->
    v1 = v2.
Proof.
  destruct out as [| | |ov]; simpl; intros; try contradiction.
  - destruct ty; simpl in *; try contradiction; congruence.
  - destruct ov as [[v ty']|]; simpl in *.
    + destruct H as [_ Hcast1]. destruct H0 as [_ Hcast2]. congruence.
    + destruct ty; simpl in *; try contradiction; congruence.
Qed.

Lemma exec_stmt_eval_funcall_E0_deterministic :
  forall ge,
  (forall e le m s t le1 m1 out1,
    exec_stmt function_entry1 ge e le m s t le1 m1 out1 ->
    t = E0 ->
    forall le2 m2 out2,
      exec_stmt function_entry1 ge e le m s E0 le2 m2 out2 ->
      le1 = le2 /\ m1 = m2 /\ out1 = out2)
  /\
  (forall m fd args t m1 res1,
    eval_funcall function_entry1 ge m fd args t m1 res1 ->
    t = E0 ->
    forall m2 res2,
      eval_funcall function_entry1 ge m fd args E0 m2 res2 ->
      m1 = m2 /\ res1 = res2).
Proof.
  intro ge.
  apply (exec_stmt_funcall_ind function_entry1 ge
    (fun e le m s t le1 m1 out1 =>
       t = E0 ->
       forall le2 m2 out2,
         exec_stmt function_entry1 ge e le m s E0 le2 m2 out2 ->
         le1 = le2 /\ m1 = m2 /\ out1 = out2)
    (fun m fd args t m1 res1 =>
       t = E0 ->
       forall m2 res2,
         eval_funcall function_entry1 ge m fd args E0 m2 res2 ->
         m1 = m2 /\ res1 = res2));
    intros; subst.
  - match goal with
    | Hx: exec_stmt _ _ _ _ _ Sskip E0 _ _ _ |- _ => inv Hx
    end; auto.
  - match goal with
    | Hx: exec_stmt _ _ _ _ _ (Sassign _ _) E0 _ _ _ |- _ => inv Hx
    end.
    match goal with
    | H1: eval_lvalue ?ge ?e ?le ?m ?a ?b1 ?ofs1 ?bf1,
      H2: eval_lvalue ?ge ?e ?le ?m ?a ?b2 ?ofs2 ?bf2 |- _ =>
        destruct (eval_lvalue_deterministic ge e le m a b1 ofs1 bf1 b2 ofs2 bf2 H1 H2)
          as (? & ? & ?); subst
    end.
    match goal with
    | H1: eval_expr ?ge ?e ?le ?m ?a ?v1,
      H2: eval_expr ?ge ?e ?le ?m ?a ?v2 |- _ =>
        assert (v1 = v2) by (eapply eval_expr_deterministic; eauto); subst
    end.
    match goal with
    | H1: sem_cast ?v ?t1 ?t2 ?m = Some ?v1,
      H2: sem_cast ?v ?t1 ?t2 ?m = Some ?v2 |- _ =>
        assert (v1 = v2) by congruence; subst
    end.
    match goal with
    | H1: assign_loc ?ce ?ty ?m ?b ?ofs ?bf ?v ?m1,
      H2: assign_loc ?ce ?ty ?m ?b ?ofs ?bf ?v ?m2 |- _ =>
        assert (m1 = m2) by (eapply assign_loc_deterministic; eauto); subst
    end; auto.
  - match goal with
    | Hx: exec_stmt _ _ _ _ _ (Sset _ _) E0 _ _ _ |- _ => inv Hx
    end.
    match goal with
    | H1: eval_expr ?ge ?e ?le ?m ?a ?v1,
      H2: eval_expr ?ge ?e ?le ?m ?a ?v2 |- _ =>
        assert (v1 = v2) by (eapply eval_expr_deterministic; eauto); subst
    end; auto.
  - match goal with
    | Hx: exec_stmt _ _ _ _ _ (Scall _ _ _) E0 _ _ _ |- _ => inv Hx
    end.
    match goal with
    | H1: eval_expr ?ge ?e ?le ?m ?a ?v1,
      H2: eval_expr ?ge ?e ?le ?m ?a ?v2 |- _ =>
        assert (v1 = v2) by (eapply eval_expr_deterministic; eauto); subst
    end.
    rewrite H in H10. inv H10.
    match goal with
    | H1: eval_exprlist ?ge ?e ?le ?m ?al ?tyargs ?vargs1,
      H2: eval_exprlist ?ge ?e ?le ?m ?al ?tyargs ?vargs2 |- _ =>
        assert (vargs1 = vargs2) by (eapply eval_exprlist_deterministic; eauto); subst
    end.
    match goal with
    | H1: Genv.find_funct _ ?vf = Some ?f1,
      H2: Genv.find_funct _ ?vf = Some ?f2 |- _ =>
        assert (f1 = f2) by congruence; subst
    end.
    match goal with
    | IH: E0 = E0 -> forall m2 res2,
            eval_funcall function_entry1 ge _ _ _ E0 m2 res2 -> _,
      Hcall: eval_funcall function_entry1 ge _ _ _ E0 _ _ |- _ =>
        destruct (IH eq_refl _ _ Hcall) as [? ?]; subst
    end; auto.
  - match goal with
    | Hx: exec_stmt _ _ _ _ _ (Sbuiltin _ _ _ _) E0 _ _ _ |- _ => inv Hx
    end.
    match goal with
    | H1: eval_exprlist ?ge ?e ?le ?m ?al ?tyargs ?vargs1,
      H2: eval_exprlist ?ge ?e ?le ?m ?al ?tyargs ?vargs2 |- _ =>
        assert (vargs1 = vargs2) by (eapply eval_exprlist_deterministic; eauto); subst
    end.
    match goal with
    | H1: external_call ?ef ?ge ?vargs ?m E0 ?vres1 ?m1,
      H2: external_call ?ef ?ge ?vargs ?m E0 ?vres2 ?m2 |- _ =>
        destruct (external_call_deterministic ef ge vargs m E0 vres1 m1 vres2 m2 H1 H2)
          as [? ?]; subst
    end; auto.
  - destruct (Eapp_E0_inv _ _ H3) as [? ?]. subst.
    inv H4.
    + destruct (Eapp_E0_inv _ _ H10) as [? ?]. subst.
      destruct (H0 eq_refl _ _ _ H11) as (? & ? & ?). subst.
      destruct (H2 eq_refl _ _ _ H15) as (? & ? & ?). subst.
      auto.
    + destruct (H0 eq_refl _ _ _ H10) as (? & ? & ?). subst.
      contradiction.
  - match goal with
    | Hx: exec_stmt _ _ _ _ _ (Ssequence _ _) E0 _ _ _ |- _ => inv Hx
    end.
    + destruct (Eapp_E0_inv _ _ H8) as [? ?]. subst.
      destruct (H0 eq_refl _ _ _ H9) as (? & ? & ?). subst.
      contradiction.
    + destruct (H0 eq_refl _ _ _ H8) as (? & ? & ?). subst.
      auto.
  - match goal with
    | Hx: exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) E0 _ _ _ |- _ => inv Hx
    end.
    match goal with
    | H1: eval_expr ?ge ?e ?le ?m ?a ?v1,
      H2: eval_expr ?ge ?e ?le ?m ?a ?v2 |- _ =>
        assert (v1 = v2) by (eapply eval_expr_deterministic; eauto); subst
    end.
    match goal with
    | H1: bool_val ?v ?ty ?m = Some ?b1,
      H2: bool_val ?v ?ty ?m = Some ?b2 |- _ =>
        assert (b1 = b2) by congruence; subst
    end.
    match goal with
    | IH: E0 = E0 -> forall le2 m2 out2,
            exec_stmt function_entry1 ge _ _ _ _ E0 le2 m2 out2 -> _,
      Hexec: exec_stmt function_entry1 ge _ _ _ _ E0 _ _ _ |- _ =>
        destruct (IH eq_refl _ _ _ Hexec) as (? & ? & ?); subst
    end; auto.
  - match goal with
    | Hx: exec_stmt _ _ _ _ _ (Sreturn None) E0 _ _ _ |- _ => inv Hx
    end; auto.
  - match goal with
    | Hx: exec_stmt _ _ _ _ _ (Sreturn (Some _)) E0 _ _ _ |- _ => inv Hx
    end.
    match goal with
    | H1: eval_expr ?ge ?e ?le ?m ?a ?v1,
      H2: eval_expr ?ge ?e ?le ?m ?a ?v2 |- _ =>
        assert (v1 = v2) by (eapply eval_expr_deterministic; eauto); subst
    end; auto.
  - match goal with
    | Hx: exec_stmt _ _ _ _ _ Sbreak E0 _ _ _ |- _ => inv Hx
    end; auto.
  - match goal with
    | Hx: exec_stmt _ _ _ _ _ Scontinue E0 _ _ _ |- _ => inv Hx
    end; auto.
  - match goal with
    | Hx: exec_stmt _ _ _ _ _ (Sloop _ _) E0 _ _ _ |- _ => inv Hx
    end.
    + destruct (H0 eq_refl _ _ _ H8) as (? & ? & ?). subst.
      match goal with
      | H1: out_break_or_return ?o ?out1,
        H2: out_break_or_return ?o ?out2 |- _ =>
          assert (out1 = out2) by (eapply out_break_or_return_deterministic; eauto);
          subst
      end; auto.
    + destruct (Eapp_E0_inv _ _ H5) as [? ?]. subst.
      destruct (H0 eq_refl _ _ _ H6) as (? & ? & ?). subst.
      match goal with
      | Hb: out_break_or_return ?o _, Hn: out_normal_or_continue ?o |- _ =>
          exact (False_rect _ (out_break_or_return_not_normal_or_continue _ _ Hb Hn))
      end.
    + destruct (Eapp_E0_inv _ _ H5) as [? Happ]. subst.
      destruct (Eapp_E0_inv _ _ Happ) as [? ?]. subst.
      destruct (H0 eq_refl _ _ _ H6) as (? & ? & ?). subst.
      match goal with
      | Hb: out_break_or_return ?o _, Hn: out_normal_or_continue ?o |- _ =>
          exact (False_rect _ (out_break_or_return_not_normal_or_continue _ _ Hb Hn))
      end.
  - destruct (Eapp_E0_inv _ _ H5) as [? ?]. subst.
    inv H6.
    + destruct (H0 eq_refl _ _ _ H12) as (? & ? & ?). subst.
      match goal with
      | Hb: out_break_or_return ?o _, Hn: out_normal_or_continue ?o |- _ =>
          exact (False_rect _ (out_break_or_return_not_normal_or_continue _ _ Hb Hn))
      end.
    + destruct (Eapp_E0_inv _ _ H9) as [? ?]. subst.
      destruct (H0 eq_refl _ _ _ H10) as (? & ? & ?). subst.
      destruct (H3 eq_refl _ _ _ H15) as (? & ? & ?). subst.
      match goal with
      | H1: out_break_or_return ?o ?out1,
        H2: out_break_or_return ?o ?out2 |- _ =>
          assert (out1 = out2) by (eapply out_break_or_return_deterministic; eauto);
          subst
      end; auto.
    + destruct (Eapp_E0_inv _ _ H9) as [? Happ]. subst.
      destruct (Eapp_E0_inv _ _ Happ) as [? ?]. subst.
      destruct (H0 eq_refl _ _ _ H10) as (? & ? & ?). subst.
      destruct (H3 eq_refl _ _ _ H15) as (? & ? & ?). subst.
      inv H4.
  - destruct (Eapp_E0_inv _ _ H6) as [? Happ]. subst.
    destruct (Eapp_E0_inv _ _ Happ) as [? ?]. subst.
    inv H7.
    + destruct (H0 eq_refl _ _ _ H13) as (? & ? & ?). subst.
      match goal with
      | Hb: out_break_or_return ?o _, Hn: out_normal_or_continue ?o |- _ =>
          exact (False_rect _ (out_break_or_return_not_normal_or_continue _ _ Hb Hn))
      end.
    + destruct (Eapp_E0_inv _ _ H10) as [? ?]. subst.
      destruct (H0 eq_refl _ _ _ H11) as (? & ? & ?). subst.
      destruct (H3 eq_refl _ _ _ H16) as (? & ? & ?). subst.
      inv H20.
    + destruct (Eapp_E0_inv _ _ H10) as [? Happ2]. subst.
      destruct (Eapp_E0_inv _ _ Happ2) as [? ?]. subst.
      destruct (H0 eq_refl _ _ _ H11) as (? & ? & ?). subst.
      destruct (H3 eq_refl _ _ _ H16) as (? & ? & ?). subst.
      destruct (H5 eq_refl _ _ _ H20) as (? & ? & ?). subst.
      auto.
  - match goal with
    | Hx: exec_stmt _ _ _ _ _ (Sswitch _ _) E0 _ _ _ |- _ => inv Hx
    end.
    match goal with
    | H1: eval_expr ?ge ?e ?le ?m ?a ?v1,
      H2: eval_expr ?ge ?e ?le ?m ?a ?v2 |- _ =>
        assert (v1 = v2) by (eapply eval_expr_deterministic; eauto); subst
    end.
    match goal with
    | H1: sem_switch_arg ?v ?ty = Some ?n1,
      H2: sem_switch_arg ?v ?ty = Some ?n2 |- _ =>
        assert (n1 = n2) by congruence; subst
    end.
    match goal with
    | IH: E0 = E0 -> forall le2 m2 out2,
            exec_stmt function_entry1 ge _ _ _ _ E0 le2 m2 out2 -> _,
      Hexec: exec_stmt function_entry1 ge _ _ _ _ E0 _ _ _ |- _ =>
        destruct (IH eq_refl _ _ _ Hexec) as (? & ? & ?); subst
    end; auto.
  - match goal with
    | Hx: eval_funcall _ _ _ (Internal _) _ E0 _ _ |- _ => inv Hx
    end.
    destruct (function_entry1_deterministic _ _ _ _ _ _ _ _ _ _ H H6)
      as (? & ? & ?). subst.
    destruct (H1 eq_refl _ _ _ H7) as (? & ? & ?). subst.
    split.
    + congruence.
    + eapply outcome_result_value_deterministic; eauto.
  - match goal with
    | Hx: eval_funcall _ _ _ (External _ _ _ _) _ E0 _ _ |- _ => inv Hx
    end.
    match goal with
    | H1: external_call ?ef ?ge ?vargs ?m E0 ?vres1 ?m1,
      H2: external_call ?ef ?ge ?vargs ?m E0 ?vres2 ?m2 |- _ =>
        destruct (external_call_deterministic ef ge vargs m E0 vres1 m1 vres2 m2 H1 H2)
          as [? ?]; subst
    end; auto.
Qed.

Lemma clight_returns_deterministic :
  forall f retcode e le m le1 m1 le2 m2,
    clight_returns f retcode e le m le1 m1 ->
    clight_returns f retcode e le m le2 m2 ->
    le1 = le2 /\ m1 = m2.
Proof.
  unfold clight_returns. intros.
  destruct (proj1 (exec_stmt_eval_funcall_E0_deterministic clight_ge)
    _ _ _ _ _ _ _ _ H eq_refl _ _ _ H0) as (? & ? & _).
  auto.
Qed.

(* ================================================================== *)
(* Generic uniqueness proof                                            *)
(*                                                                      *)
(* Parameterised over S, W, R, pc_of with R_total and R_functional     *)
(* as Section hypotheses (not axioms).                                 *)
(*                                                                      *)
(* Uses the new handler_correct_gen with err : S -> option string.     *)
(* The err case split makes cross-constructor exclusion provable:      *)
(*   Some msg => both handlers return Error msg (trivial)              *)
(*   None     => Error is excluded (False in handler_correct_gen)       *)
(* ================================================================== *)

Section GenericUniqueness.

Variables (S : Type) (W : Type).
Variable (pc_of : S -> Z).
Variable (R : Clight.env -> temp_env -> mem -> S -> W -> Prop).

(* R is total: every abstract state has a Clight context + witness *)
Hypothesis R_total : forall s, exists e le m w, R e le m s w.

(* R is functional: same Clight context implies same abstract state *)
Hypothesis R_functional : forall e le m s1 s2 w1 w2,
  R e le m s1 w1 -> R e le m s2 w2 -> s1 = s2.

(* ================================================================== *)
(* Main generic theorem                                                *)
(* ================================================================== *)

Lemma handler_correct_gen_determines_em_eq :
  forall (f : function)
         (h1 h2 : Z -> S -> step_result_gen S)
         (err : S -> option string)
         (step_pre : Clight.env -> mem -> S -> W -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> S -> Prop),
    (forall s e le m w, R e le m s w -> step_pre e m s w) ->
    handler_correct_gen S W pc_of R h1 f err step_pre P_halt P_ccall ->
    handler_correct_gen S W pc_of R h2 f err step_pre P_halt P_ccall ->
    forall s, em_eq_gen (h1 (pc_of s) s) (h2 (pc_of s) s).
Proof. Admitted.

End GenericUniqueness.

(* ================================================================== *)
(* Module satisfying MetaSpecGen                                       *)
(* ================================================================== *)

Module SharedLemmasMetaSpecGen <: MetaSpecGen.

  Definition handler_unique_mod_errors_gen :
    forall (S : Type) (W : Type) (pc_of_S : S -> Z)
           (R : Clight.env -> temp_env -> mem -> S -> W -> Prop),
      (forall s, exists e le m w, R e le m s w) ->
      (forall e le m s1 s2 w1 w2, R e le m s1 w1 -> R e le m s2 w2 -> s1 = s2) ->
      forall (f : function)
             (h1 h2 : Z -> S -> step_result_gen S)
             (err : S -> option string)
             (step_pre : Clight.env -> mem -> S -> W -> Prop)
             (P_halt : value -> Prop)
             (P_ccall : nat -> list value -> S -> Prop),
        (forall s e le m w, R e le m s w -> step_pre e m s w) ->
        handler_correct_gen S W pc_of_S R h1 f err step_pre P_halt P_ccall ->
        handler_correct_gen S W pc_of_S R h2 f err step_pre P_halt P_ccall ->
        forall s, em_eq_gen (h1 (pc_of_S s) s) (h2 (pc_of_S s) s).
  Proof.
    intros S W pc_of_S R Htotal Hfunc.
    intros f h1 h2 err step_pre P_halt P_ccall Hpre_holds Hc1 Hc2 s.
    exact (handler_correct_gen_determines_em_eq S W pc_of_S R Htotal Hfunc
             f h1 h2 err step_pre P_halt P_ccall Hpre_holds Hc1 Hc2 s).
  Qed.

End SharedLemmasMetaSpecGen.

(* ================================================================== *)
(* Concrete instantiation                                              *)
(*                                                                      *)
(* The main concrete theorem takes totality and functionality as        *)
(* hypotheses.  The closed per-instruction uniqueness lemmas below      *)
(* still need concrete compatibility assumptions for abs_rel_with_ard.  *)
(* ================================================================== *)

Axiom abs_rel_functional :
  forall (e : Clight.env) (le : temp_env) (m : mem) (s1 s2 : state),
    abs_rel e le m s1 -> abs_rel e le m s2 -> s1 = s2.

Axiom abs_rel_inhabitable :
  forall (f : function)
         (err : state -> option string)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (s : state),
    exists (e : Clight.env) (le : temp_env) (m : mem) (ard : abs_rel_data),
      abs_rel_with_ard e le m s ard /\ step_pre e m s ard.

Lemma unique_non_halt_ccall_from_handler_correct :
  forall (f : function)
         (err : state -> option string)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result),
    (forall v, P_halt v -> False) ->
    (forall n args s, P_ccall n args s -> False) ->
    handler_correct h1 f err step_pre P_halt P_ccall ->
    handler_correct h2 f err step_pre P_halt P_ccall ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros f err step_pre P_halt P_ccall h1 h2 Hno_halt Hno_ccall Hc1 Hc2 s.
  destruct (abs_rel_inhabitable f err step_pre s)
    as [e [le [m [ard [Hrel Hpre]]]]].
  unfold handler_correct, handler_correct_gen in Hc1, Hc2.
  destruct (err s) as [msg|] eqn:Herr.
  - specialize (Hc1 e le m s).
    specialize (Hc2 e le m s).
    rewrite Herr in Hc1, Hc2.
    rewrite Hc1, Hc2. constructor.
  - specialize (Hc1 e le m s).
    specialize (Hc2 e le m s).
    rewrite Herr in Hc1, Hc2.
    destruct (h1 (Machine.pc s) s) as [s1|v1|msg1|n1 args1 s1] eqn:E1;
      destruct (h2 (Machine.pc s) s) as [s2|v2|msg2|n2 args2 s2] eqn:E2;
      try contradiction;
      try (destruct Hc1 as [HP _]; exfalso; eauto);
      try (destruct Hc2 as [HP _]; exfalso; eauto).
    specialize (Hc1 ard Hrel Hpre).
    specialize (Hc2 ard Hrel Hpre).
    destruct Hc1 as [le1 [m1 [Hexec1 [ard1 Hrel1]]]].
    destruct Hc2 as [le2 [m2 [Hexec2 [ard2 Hrel2]]]].
    destruct (clight_returns_deterministic
      _ _ _ _ _ _ _ _ _ Hexec1 Hexec2) as [Hle Hm].
    subst le2 m2.
    assert (s1 = s2).
    { eapply abs_rel_functional with (e := e) (le := le1) (m := m1).
      - exists ard1. exact Hrel1.
      - exists ard2. exact Hrel2. }
    subst s2. constructor.
Qed.

(* Main concrete theorem -- takes totality and functionality as hypotheses *)
Lemma handler_correct_determines_em_eq :
  forall (f : function)
         (err : state -> option string)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_halt : value -> Prop)
         (P_ccall : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result) (s : state),
    (forall s0, exists e le m w, abs_rel_with_ard e le m s0 w) ->
    (forall e le m s1 s2 w1 w2,
       abs_rel_with_ard e le m s1 w1 -> abs_rel_with_ard e le m s2 w2 -> s1 = s2) ->
    (forall s e le m w, abs_rel_with_ard e le m s w -> step_pre e m s w) ->
    handler_correct h1 f err step_pre P_halt P_ccall ->
    handler_correct h2 f err step_pre P_halt P_ccall ->
    em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros f err step_pre P_halt P_ccall h1 h2 s Htotal Hfunc Hpre_holds Hc1 Hc2.
  (* handler_correct unfolds to handler_correct_gen state abs_rel_data Machine.pc abs_rel_with_ard *)
  (* Use the generic theorem *)
  pose proof (handler_correct_gen_determines_em_eq
    state abs_rel_data Machine.pc abs_rel_with_ard Htotal Hfunc
    f h1 h2 err step_pre P_halt P_ccall Hpre_holds Hc1 Hc2 s) as Hgen.
  (* em_eq_gen on step_result (= step_result_gen state) implies em_eq *)
  remember (h1 s.(pc) s) as r1.
  remember (h2 s.(pc) s) as r2.
  destruct Hgen; constructor.
Qed.

(* ================================================================== *)
(* Derived helper lemmas (concrete, backward compat)                   *)
(* ================================================================== *)

Section GenericHelpers.

Variables (f : function)
          (err : state -> option string)
          (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
          (P_halt_pred : value -> Prop)
          (P_ccall_pred : nat -> list value -> state -> Prop).

Hypothesis abs_rel_total :
  forall s, exists e le m w, abs_rel_with_ard e le m s w.

Hypothesis abs_rel_func :
  forall e le m s1 s2 w1 w2,
    abs_rel_with_ard e le m s1 w1 -> abs_rel_with_ard e le m s2 w2 -> s1 = s2.

Variable step_pre_holds :
  forall s e le m w, abs_rel_with_ard e le m s w -> step_pre e m s w.

Lemma generic_step_step_eq :
  forall (h1 h2 : Z -> state -> step_result) s s1 s2,
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Step s1 -> h2 s.(pc) s = Step s2 -> s1 = s2.
Proof.
  intros h1 h2 s s1 s2 Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem. reflexivity.
Qed.

Lemma generic_step_error_excl :
  forall (h1 h2 : Z -> state -> step_result) s s' msg,
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = Error msg -> False.
Proof.
  intros h1 h2 s s' msg Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

Lemma generic_halt_halt_eq :
  forall (h1 h2 : Z -> state -> step_result) s v1 v2,
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Halt v1 -> h2 s.(pc) s = Halt v2 -> v1 = v2.
Proof.
  intros h1 h2 s v1 v2 Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem. reflexivity.
Qed.

Lemma generic_step_halt_excl :
  forall (h1 h2 : Z -> state -> step_result) s s' v,
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = Halt v -> False.
Proof.
  intros h1 h2 s s' v Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

Lemma generic_halt_error_excl :
  forall (h1 h2 : Z -> state -> step_result) s v msg,
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Halt v -> h2 s.(pc) s = Error msg -> False.
Proof.
  intros h1 h2 s v msg Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

Lemma generic_ccall_ccall_eq :
  forall (h1 h2 : Z -> state -> step_result) s n1 args1 s1 n2 args2 s2,
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = CCall_request n1 args1 s1 ->
    h2 s.(pc) s = CCall_request n2 args2 s2 ->
    n1 = n2 /\ args1 = args2 /\ s1 = s2.
Proof.
  intros h1 h2 s n1 args1 s1 n2 args2 s2 Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem. auto.
Qed.

Lemma generic_step_ccall_excl :
  forall (h1 h2 : Z -> state -> step_result) s s' n0 args0 s'',
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Step s' -> h2 s.(pc) s = CCall_request n0 args0 s'' -> False.
Proof.
  intros h1 h2 s s' n0 args0 s'' Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

Lemma generic_error_ccall_excl :
  forall (h1 h2 : Z -> state -> step_result) s msg n0 args0 s',
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Error msg -> h2 s.(pc) s = CCall_request n0 args0 s' -> False.
Proof.
  intros h1 h2 s msg n0 args0 s' Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

Lemma generic_halt_ccall_excl :
  forall (h1 h2 : Z -> state -> step_result) s v n0 args0 s',
    handler_correct h1 f err step_pre P_halt_pred P_ccall_pred ->
    handler_correct h2 f err step_pre P_halt_pred P_ccall_pred ->
    h1 s.(pc) s = Halt v -> h2 s.(pc) s = CCall_request n0 args0 s' -> False.
Proof.
  intros h1 h2 s v n0 args0 s' Hc1 Hc2 E1 E2.
  pose proof (handler_correct_determines_em_eq f err step_pre P_halt_pred P_ccall_pred h1 h2 s abs_rel_total abs_rel_func step_pre_holds Hc1 Hc2) as Hem.
  rewrite E1, E2 in Hem. inversion Hem.
Qed.

End GenericHelpers.

(* Fully generic uniqueness lemma (concrete) *)
Lemma unique_from_handler_correct :
  forall (f : function)
         (err : state -> option string)
         (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
         (P_halt_p : value -> Prop)
         (P_ccall_p : nat -> list value -> state -> Prop)
         (h1 h2 : Z -> state -> step_result),
    (forall s0, exists e le m w, abs_rel_with_ard e le m s0 w) ->
    (forall e le m s1 s2 w1 w2,
       abs_rel_with_ard e le m s1 w1 -> abs_rel_with_ard e le m s2 w2 -> s1 = s2) ->
    (forall s e le m w, abs_rel_with_ard e le m s w -> step_pre e m s w) ->
    handler_correct h1 f err step_pre P_halt_p P_ccall_p ->
    handler_correct h2 f err step_pre P_halt_p P_ccall_p ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
Proof.
  intros. apply handler_correct_determines_em_eq with (f := f) (err := err)
    (step_pre := step_pre) (P_halt := P_halt_p) (P_ccall := P_ccall_p); assumption.
Qed.
