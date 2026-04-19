(* StepToBigstep.v -- Computational evaluator for Clight statements,
   with a soundness theorem bridging to ClightBigstep.exec_stmt.

   PURPOSE: Make "Part 1" of handler proofs (constructing exec_stmt
   derivations) computational rather than manual tactic work.

   APPROACH: We define decidable/computable evaluators for Clight
   expressions and statements. When the evaluator returns Some(...),
   we prove the corresponding bigstep relation holds.  Handler proofs
   can then:
     1. Apply eval_stmt with concrete fuel
     2. Use vm_compute / native_compute to discharge the evaluation
     3. Apply the soundness lemma to get exec_stmt

   The evaluator handles the subset of Clight that appears in
   instruction handler bodies:
     - Sset (temp := expr)
     - Sassign (lvalue = expr)
     - Ssequence (s1 ; s2)
     - Sifthenelse (if expr then s1 else s2)
     - Sreturn
     - Sskip, Sbreak, Scontinue
     - Sbuiltin (for external calls -- left abstract)
     - Sloop (with fuel bound) *)

From Stdlib Require Import ZArith List Bool.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Values AST Memory.
From compcert Require Import Errors Ctypes Cop Clight Clightdefs.
From compcert Require Import Globalenvs Maps Events.
From compcert Require Import ClightBigstep.
From compcert Require Import Smallstep.

(* ================================================================== *)
(* Section 1: Computational expression evaluator                       *)
(* ================================================================== *)

Section EVAL.

Variable ge : Clight.genv.

(* Computational deref_loc: given type, memory, block, offset, bitfield,
   compute the value if possible. *)
Definition comp_deref_loc (ty : type) (m : mem) (b : block) (ofs : ptrofs)
    (bf : bitfield) : option val :=
  match bf with
  | Full =>
      match access_mode ty with
      | By_value chunk => Mem.loadv chunk m (Vptr b ofs)
      | By_reference => Some (Vptr b ofs)
      | By_copy => Some (Vptr b ofs)
      | By_nothing => None
      end
  | Bits _ _ _ _ => None  (* Bitfields not handled computationally *)
  end.

(* Computational assign_loc: store a value at the given location. *)
Definition comp_assign_loc (ty : type) (m : mem) (b : block) (ofs : ptrofs)
    (bf : bitfield) (v : val) : option mem :=
  match bf with
  | Full =>
      match access_mode ty with
      | By_value chunk => Mem.storev chunk m (Vptr b ofs) v
      | _ => None  (* By_copy/By_reference stores not handled *)
      end
  | Bits _ _ _ _ => None
  end.

(* Computational expression evaluator.
   Returns (value, optional lvalue info) or None on failure.
   We use fuel to handle mutual recursion between eval_expr/eval_lvalue. *)

(* Forward declaration for lvalue evaluation *)
Fixpoint comp_eval_expr (fuel : nat) (e : env) (le : temp_env) (m : mem)
    (a : expr) {struct fuel} : option val :=
  match fuel with
  | O => None
  | S fuel' =>
      match a with
      | Econst_int i _ => Some (Vint i)
      | Econst_float f _ => Some (Vfloat f)
      | Econst_single f _ => Some (Vsingle f)
      | Econst_long i _ => Some (Vlong i)
      | Etempvar id _ => le ! id
      | Eaddrof a' _ =>
          match comp_eval_lvalue fuel' e le m a' with
          | Some (loc, ofs, Full) => Some (Vptr loc ofs)
          | _ => None
          end
      | Eunop op a' _ =>
          match comp_eval_expr fuel' e le m a' with
          | Some v1 => sem_unary_operation op v1 (typeof a') m
          | None => None
          end
      | Ebinop op a1 a2 _ =>
          match comp_eval_expr fuel' e le m a1,
                comp_eval_expr fuel' e le m a2 with
          | Some v1, Some v2 =>
              sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m
          | _, _ => None
          end
      | Ecast a' ty =>
          match comp_eval_expr fuel' e le m a' with
          | Some v1 => sem_cast v1 (typeof a') ty m
          | None => None
          end
      | Esizeof ty1 ty => Some (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
      | Ealignof ty1 ty => Some (Vptrofs (Ptrofs.repr (alignof ge ty1)))
      (* For lvalue expressions, try lvalue eval + deref *)
      | Evar _ _ | Ederef _ _ | Efield _ _ _ =>
          match comp_eval_lvalue fuel' e le m a with
          | Some (loc, ofs, bf) => comp_deref_loc (typeof a) m loc ofs bf
          | None => None
          end
      end
  end

with comp_eval_lvalue (fuel : nat) (e : env) (le : temp_env) (m : mem)
    (a : expr) {struct fuel} : option (block * ptrofs * bitfield) :=
  match fuel with
  | O => None
  | S fuel' =>
      match a with
      | Evar id ty =>
          match e ! id with
          | Some (l, ty') =>
              if type_eq ty ty' then Some (l, Ptrofs.zero, Full) else None
          | None =>
              match Genv.find_symbol ge id with
              | Some l => Some (l, Ptrofs.zero, Full)
              | None => None
              end
          end
      | Ederef a' _ =>
          match comp_eval_expr fuel' e le m a' with
          | Some (Vptr l ofs) => Some (l, ofs, Full)
          | _ => None
          end
      | Efield a' i ty =>
          match comp_eval_expr fuel' e le m a' with
          | Some (Vptr l ofs) =>
              match typeof a' with
              | Tstruct id _ =>
                  match ge.(genv_cenv) ! id with
                  | Some co =>
                      match field_offset ge i (co_members co) with
                      | OK (delta, bf) =>
                          Some (l, Ptrofs.add ofs (Ptrofs.repr delta), bf)
                      | Error _ => None
                      end
                  | None => None
                  end
              | Tunion id _ =>
                  match ge.(genv_cenv) ! id with
                  | Some co =>
                      match union_field_offset ge i (co_members co) with
                      | OK (delta, bf) =>
                          Some (l, Ptrofs.add ofs (Ptrofs.repr delta), bf)
                      | Error _ => None
                      end
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  end.

(* Computational expression list evaluator *)
Fixpoint comp_eval_exprlist (fuel : nat) (e : env) (le : temp_env) (m : mem)
    (al : list expr) (tyl : list type) {struct al}
    : option (list val) :=
  match al, tyl with
  | nil, nil => Some nil
  | a :: al', ty :: tyl' =>
      match comp_eval_expr fuel e le m a with
      | Some v1 =>
          match sem_cast v1 (typeof a) ty m with
          | Some v2 =>
              match comp_eval_exprlist fuel e le m al' tyl' with
              | Some vl => Some (v2 :: vl)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | _, _ => None
  end.

(* ================================================================== *)
(* Section 2: Computational statement evaluator                        *)
(* ================================================================== *)

(* The outcome type from ClightBigstep *)
(* We use ClightBigstep.outcome directly *)

(* Computational statement evaluator.
   Returns (trace, new temp_env, new mem, outcome) or None. *)
Fixpoint comp_eval_stmt (fuel : nat) (e : env) (le : temp_env) (m : mem)
    (s : statement) {struct fuel}
    : option (trace * temp_env * mem * outcome) :=
  match fuel with
  | O => None
  | S fuel' =>
      match s with
      (* Sskip *)
      | Sskip => Some (E0, le, m, Out_normal)

      (* Sassign lhs rhs *)
      | Sassign a1 a2 =>
          match comp_eval_lvalue fuel' e le m a1 with
          | Some (loc, ofs, bf) =>
              match comp_eval_expr fuel' e le m a2 with
              | Some v2 =>
                  match sem_cast v2 (typeof a2) (typeof a1) m with
                  | Some v =>
                      match comp_assign_loc (typeof a1) m loc ofs bf v with
                      | Some m' => Some (E0, le, m', Out_normal)
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end

      (* Sset id expr *)
      | Sset id a =>
          match comp_eval_expr fuel' e le m a with
          | Some v => Some (E0, PTree.set id v le, m, Out_normal)
          | None => None
          end

      (* Ssequence s1 s2 *)
      | Ssequence s1 s2 =>
          match comp_eval_stmt fuel' e le m s1 with
          | Some (t1, le1, m1, Out_normal) =>
              match comp_eval_stmt fuel' e le1 m1 s2 with
              | Some (t2, le2, m2, out) =>
                  Some (t1 ** t2, le2, m2, out)
              | None => None
              end
          | Some (t1, le1, m1, out) =>
              (* out <> Out_normal: sequence short-circuits *)
              Some (t1, le1, m1, out)
          | None => None
          end

      (* Sifthenelse a s1 s2 *)
      | Sifthenelse a s1 s2 =>
          match comp_eval_expr fuel' e le m a with
          | Some v1 =>
              match bool_val v1 (typeof a) m with
              | Some b =>
                  comp_eval_stmt fuel' e le m (if b then s1 else s2)
              | None => None
              end
          | None => None
          end

      (* Sreturn None *)
      | Sreturn None => Some (E0, le, m, Out_return None)

      (* Sreturn (Some a) *)
      | Sreturn (Some a) =>
          match comp_eval_expr fuel' e le m a with
          | Some v => Some (E0, le, m, Out_return (Some (v, typeof a)))
          | None => None
          end

      (* Sbreak *)
      | Sbreak => Some (E0, le, m, Out_break)

      (* Scontinue *)
      | Scontinue => Some (E0, le, m, Out_continue)

      (* Sloop s1 s2 -- bounded by fuel *)
      | Sloop s1 s2 =>
          match comp_eval_stmt fuel' e le m s1 with
          | Some (t1, le1, m1, Out_normal) =>
              match comp_eval_stmt fuel' e le1 m1 s2 with
              | Some (t2, le2, m2, Out_normal) =>
                  (* Continue looping *)
                  match comp_eval_stmt fuel' e le2 m2 (Sloop s1 s2) with
                  | Some (t3, le3, m3, out) =>
                      Some (t1 ** t2 ** t3, le3, m3, out)
                  | None => None
                  end
              | Some (t2, le2, m2, Out_break) =>
                  Some (t1 ** t2, le2, m2, Out_normal)
              | Some (t2, le2, m2, Out_return ov) =>
                  Some (t1 ** t2, le2, m2, Out_return ov)
              | Some (_, _, _, Out_continue) => None  (* ill-formed *)
              | None => None
              end
          | Some (t1, le1, m1, Out_continue) =>
              match comp_eval_stmt fuel' e le1 m1 s2 with
              | Some (t2, le2, m2, Out_normal) =>
                  match comp_eval_stmt fuel' e le2 m2 (Sloop s1 s2) with
                  | Some (t3, le3, m3, out) =>
                      Some (t1 ** t2 ** t3, le3, m3, out)
                  | None => None
                  end
              | Some (t2, le2, m2, Out_break) =>
                  Some (t1 ** t2, le2, m2, Out_normal)
              | Some (t2, le2, m2, Out_return ov) =>
                  Some (t1 ** t2, le2, m2, Out_return ov)
              | Some (_, _, _, Out_continue) => None
              | None => None
              end
          | Some (t1, le1, m1, Out_break) =>
              Some (t1, le1, m1, Out_normal)
          | Some (t1, le1, m1, Out_return ov) =>
              Some (t1, le1, m1, Out_return ov)
          | None => None
          end

      (* Sswitch a sl *)
      | Sswitch a sl =>
          match comp_eval_expr fuel' e le m a with
          | Some v =>
              match sem_switch_arg v (typeof a) with
              | Some n =>
                  match comp_eval_stmt fuel' e le m
                          (seq_of_labeled_statement (select_switch n sl)) with
                  | Some (t, le1, m1, out) =>
                      Some (t, le1, m1, outcome_switch out)
                  | None => None
                  end
              | None => None
              end
          | None => None
          end

      (* Scall -- not handled computationally (involves function calls) *)
      | Scall _ _ _ => None

      (* Sbuiltin -- not handled computationally (involves external calls) *)
      | Sbuiltin _ _ _ _ => None

      (* Slabel -- not in bigstep semantics *)
      | Slabel _ _ => None

      (* Sgoto -- not handled computationally *)
      | Sgoto _ => None
      end
  end.

(* ================================================================== *)
(* Section 3: Soundness of expression evaluator                        *)
(* ================================================================== *)

(* Fuel monotonicity: evaluation with more fuel agrees with less fuel. *)
(* (Omitted for brevity -- straightforward by induction on fuel.)      *)

Section EXPR_SOUNDNESS.

Variable e : env.
Variable le : temp_env.
Variable m : mem.

(* Soundness of comp_deref_loc *)
Lemma comp_deref_loc_sound : forall ty b ofs bf v,
  comp_deref_loc ty m b ofs bf = Some v ->
  deref_loc ty m b ofs bf v.
Proof.
  unfold comp_deref_loc. intros ty b ofs bf v.
  destruct bf.
  - (* Full *)
    destruct (access_mode ty) eqn:Hacc; try discriminate.
    + (* By_value *)
      intros H. apply deref_loc_value with (chunk := m0); auto.
    + (* By_reference *)
      intros H. injection H; intros; subst.
      apply deref_loc_reference; auto.
    + (* By_copy *)
      intros H. injection H; intros; subst.
      apply deref_loc_copy; auto.
  - (* Bits *)
    discriminate.
Qed.

(* Soundness of comp_assign_loc *)
Lemma comp_assign_loc_sound : forall ty b ofs bf v m',
  comp_assign_loc ty m b ofs bf v = Some m' ->
  assign_loc ge ty m b ofs bf v m'.
Proof.
  unfold comp_assign_loc. intros ty b ofs bf v m'.
  destruct bf.
  - (* Full *)
    destruct (access_mode ty) eqn:Hacc; try discriminate.
    intros H. apply assign_loc_value with (chunk := m0); auto.
  - (* Bits *)
    discriminate.
Qed.

(* Soundness of the expression evaluator.
   We prove: comp_eval_expr = Some v  ->  eval_expr ge e le m a v
   and:      comp_eval_lvalue = Some (b,ofs,bf)  ->  eval_lvalue ge e le m a b ofs bf

   The proof proceeds by mutual induction on fuel. *)

Lemma comp_eval_expr_lvalue_sound :
  forall fuel,
  (forall a v,
    comp_eval_expr fuel e le m a = Some v ->
    eval_expr ge e le m a v)
  /\
  (forall a b ofs bf,
    comp_eval_lvalue fuel e le m a = Some (b, ofs, bf) ->
    eval_lvalue ge e le m a b ofs bf).
Proof.
  induction fuel as [| fuel' IH].
  - (* fuel = 0 *)
    split; intros; simpl in *; discriminate.
  - (* fuel = S fuel' *)
    destruct IH as [IHexpr IHlval].
    split.
    + (* eval_expr soundness *)
      intros a v Heval.
      simpl in Heval.
      destruct a; try discriminate.
      * (* Econst_int *)
        injection Heval; intros; subst. constructor.
      * (* Econst_float *)
        injection Heval; intros; subst. constructor.
      * (* Econst_single *)
        injection Heval; intros; subst. constructor.
      * (* Econst_long *)
        injection Heval; intros; subst. constructor.
      * (* Evar -- lvalue + deref *)
        destruct (comp_eval_lvalue fuel' e le m (Evar i t)) eqn:Hlv;
          try discriminate.
        destruct p as [[b' ofs'] bf'].
        apply IHlval in Hlv.
        apply comp_deref_loc_sound in Heval.
        eapply eval_Elvalue; eauto.
      * (* Etempvar *)
        apply eval_Etempvar. exact Heval.
      * (* Ederef -- lvalue + deref *)
        destruct (comp_eval_lvalue fuel' e le m (Ederef a t)) eqn:Hlv;
          try discriminate.
        destruct p as [[b' ofs'] bf'].
        apply IHlval in Hlv.
        apply comp_deref_loc_sound in Heval.
        eapply eval_Elvalue; eauto.
      * (* Eaddrof *)
        destruct (comp_eval_lvalue fuel' e le m a) eqn:Hlv;
          try discriminate.
        destruct p as [[b' ofs'] bf'].
        destruct bf'; try discriminate.
        injection Heval; intros; subst.
        apply eval_Eaddrof. apply IHlval. exact Hlv.
      * (* Eunop *)
        destruct (comp_eval_expr fuel' e le m a) eqn:He;
          try discriminate.
        apply eval_Eunop with (v1 := v0).
        apply IHexpr. exact He.
        exact Heval.
      * (* Ebinop *)
        destruct (comp_eval_expr fuel' e le m a1) eqn:He1;
          try discriminate.
        destruct (comp_eval_expr fuel' e le m a2) eqn:He2;
          try discriminate.
        apply eval_Ebinop with (v1 := v0) (v2 := v1).
        apply IHexpr. exact He1.
        apply IHexpr. exact He2.
        exact Heval.
      * (* Ecast *)
        destruct (comp_eval_expr fuel' e le m a) eqn:He;
          try discriminate.
        apply eval_Ecast with (v1 := v0).
        apply IHexpr. exact He.
        exact Heval.
      * (* Efield -- lvalue + deref *)
        destruct (comp_eval_lvalue fuel' e le m (Efield a i t)) eqn:Hlv;
          try discriminate.
        destruct p as [[b' ofs'] bf'].
        apply IHlval in Hlv.
        apply comp_deref_loc_sound in Heval.
        eapply eval_Elvalue; eauto.
      * (* Esizeof *)
        injection Heval; intros; subst. constructor.
      * (* Ealignof *)
        injection Heval; intros; subst. constructor.
    + (* eval_lvalue soundness *)
      intros a b ofs bf Heval.
      simpl in Heval.
      destruct a; try discriminate.
      * (* Evar *)
        destruct (e ! i) eqn:He.
        -- destruct p as [l ty'].
           destruct (type_eq t ty') eqn:Hteq; try discriminate.
           injection Heval; intros; subst.
           apply eval_Evar_local. exact He.
        -- destruct (Genv.find_symbol ge i) eqn:Hfs; try discriminate.
           injection Heval; intros; subst.
           apply eval_Evar_global; auto.
      * (* Ederef *)
        destruct (comp_eval_expr fuel' e le m a) eqn:He; try discriminate.
        destruct v; try discriminate.
        injection Heval; intros; subst.
        apply eval_Ederef.
        apply IHexpr. exact He.
      * (* Efield *)
        destruct (comp_eval_expr fuel' e le m a) eqn:He; try discriminate.
        destruct v; try discriminate.
        destruct (typeof a) eqn:Hty; try discriminate.
        -- (* Tstruct *)
           destruct (genv_cenv ge) ! i1 eqn:Hco; try discriminate.
           destruct (field_offset ge i (co_members c)) as [[delta bf']|] eqn:Hfo; try discriminate.
           injection Heval; intros; subst.
           apply eval_Efield_struct with (id := i1) (co := c)
             (att := a0) (delta := delta); try assumption.
           apply IHexpr. exact He.
        -- (* Tunion *)
           destruct (genv_cenv ge) ! i1 eqn:Hco; try discriminate.
           destruct (union_field_offset ge i (co_members c)) as [[delta bf']|] eqn:Hfo; try discriminate.
           injection Heval; intros; subst.
           apply eval_Efield_union with (id := i1) (co := c)
             (att := a0) (delta := delta); try assumption.
           apply IHexpr. exact He.
Qed.

Definition comp_eval_expr_sound fuel :=
  proj1 (comp_eval_expr_lvalue_sound fuel).

Definition comp_eval_lvalue_sound fuel :=
  proj2 (comp_eval_expr_lvalue_sound fuel).

(* Soundness of expression list evaluator *)
Lemma comp_eval_exprlist_sound : forall fuel al tyl vl,
  comp_eval_exprlist fuel e le m al tyl = Some vl ->
  eval_exprlist ge e le m al tyl vl.
Proof.
  intros fuel. induction al; intros tyl vl Heval.
  - (* nil *)
    destruct tyl; simpl in Heval; try discriminate.
    injection Heval; intros; subst. constructor.
  - (* cons *)
    destruct tyl; simpl in Heval; try discriminate.
    destruct (comp_eval_expr fuel e le m a) eqn:He; try discriminate.
    destruct (sem_cast v (typeof a) t m) eqn:Hc; try discriminate.
    destruct (comp_eval_exprlist fuel e le m al tyl) eqn:Hr; try discriminate.
    injection Heval; intros; subst.
    econstructor.
    + eapply comp_eval_expr_sound. exact He.
    + exact Hc.
    + apply IHal. exact Hr.
Qed.

End EXPR_SOUNDNESS.

(* ================================================================== *)
(* Section 4: Soundness of statement evaluator                         *)
(* ================================================================== *)

Section STMT_SOUNDNESS.

(* Helper: if an outcome is not Out_normal, record which one it is *)
Lemma outcome_not_normal_dec : forall out,
  out <> Out_normal \/  out = Out_normal.
Proof.
  destruct out; auto.
  left; discriminate.
  left; discriminate.
  left; discriminate.
Qed.

(* Ltac helpers for repeated proof patterns in statement soundness *)
Local Ltac deopt H :=
  match type of H with
  | match ?x with _ => _ end = Some _ =>
      let Hx := fresh "Hx" in
      destruct x eqn:Hx; try discriminate; deopt H
  | Some _ = Some _ => injection H; intros; subst
  | _ => idtac
  end.

Local Ltac apply_expr_sound H :=
  eapply comp_eval_expr_sound in H.

Local Ltac apply_lval_sound H :=
  eapply comp_eval_lvalue_sound in H.

(* The main soundness theorem *)
Theorem comp_eval_stmt_sound : forall fuel env0 le m s t le' m' out,
  comp_eval_stmt fuel env0 le m s = Some (t, le', m', out) ->
  exec_stmt function_entry1 ge env0 le m s t le' m' out.
Proof.
  induction fuel as [| fuel' IH]; intros env0 le m s t le' m' out Heval.
  - (* fuel = 0 *)
    simpl in Heval. discriminate.
  - (* fuel = S fuel' *)
    destruct s;
    (* Reduce comp_eval_stmt in Heval for this particular statement form *)
    simpl in Heval;
    (* Handle trivially impossible cases (Scall, Sbuiltin, Sgoto return None) *)
    try (exact (match Heval with end));
    try discriminate.

    + (* Sskip *)
      injection Heval; intros; subst.
      constructor.

    + (* Sassign lhs rhs *)
      rename e into lhs. rename e0 into rhs.
      destruct (comp_eval_lvalue fuel' env0 le m lhs) as [[[loc ofs] bf]|] eqn:Hlv;
        try discriminate.
      destruct (comp_eval_expr fuel' env0 le m rhs) eqn:He;
        try discriminate.
      destruct (sem_cast v (typeof rhs) (typeof lhs) m) eqn:Hc;
        try discriminate.
      destruct (comp_assign_loc (typeof lhs) m loc ofs bf v0) eqn:Ha;
        try discriminate.
      injection Heval; intros; subst.
      econstructor.
      * eapply comp_eval_lvalue_sound. exact Hlv.
      * eapply comp_eval_expr_sound. exact He.
      * exact Hc.
      * eapply comp_assign_loc_sound. exact Ha.

    + (* Sset id expr *)
      rename e into the_expr.
      destruct (comp_eval_expr fuel' env0 le m the_expr) eqn:He;
        try discriminate.
      injection Heval; intros; subst.
      econstructor.
      eapply comp_eval_expr_sound. exact He.

    + (* Ssequence s1 s2 *)
      destruct (comp_eval_stmt fuel' env0 le m s1) as [[[[t1 le1] m1] out1]|] eqn:Hs1;
        try discriminate.
      destruct out1.
      * (* Out_break from s1 *)
        injection Heval; intros; subst.
        apply exec_Sseq_2.
        apply IH. exact Hs1.
        discriminate.
      * (* Out_continue from s1 *)
        injection Heval; intros; subst.
        apply exec_Sseq_2.
        apply IH. exact Hs1.
        discriminate.
      * (* Out_normal from s1 -- continue with s2 *)
        destruct (comp_eval_stmt fuel' env0 le1 m1 s2) as [[[[t2 le2] m2] out2]|] eqn:Hs2;
          try discriminate.
        injection Heval; intros; subst.
        eapply exec_Sseq_1.
        apply IH. exact Hs1.
        apply IH. exact Hs2.
      * (* Out_return from s1 *)
        injection Heval; intros; subst.
        apply exec_Sseq_2.
        apply IH. exact Hs1.
        discriminate.

    + (* Sifthenelse cond s_true s_false *)
      rename e into cond_expr.
      destruct (comp_eval_expr fuel' env0 le m cond_expr) eqn:He;
        try discriminate.
      destruct (bool_val v (typeof cond_expr) m) eqn:Hb;
        try discriminate.
      apply exec_Sifthenelse with (v1 := v) (b := b).
      * eapply comp_eval_expr_sound. exact He.
      * exact Hb.
      * apply IH. exact Heval.

    + (* Sloop s1 s2 *)
      destruct (comp_eval_stmt fuel' env0 le m s1) as [[[[t1 le1] m1] out1]|] eqn:Hs1;
        try discriminate.
      destruct out1.
      * (* Out_break from s1 body *)
        injection Heval; intros; subst.
        eapply exec_Sloop_stop1.
        apply IH. exact Hs1.
        constructor.
      * (* Out_continue from s1 body -- go to s2 *)
        destruct (comp_eval_stmt fuel' env0 le1 m1 s2) as [[[[t2 le2] m2] out2]|] eqn:Hs2;
          try discriminate.
        destruct out2.
        -- (* Out_break from s2 *)
           injection Heval; intros; subst.
           eapply exec_Sloop_stop2.
           apply IH. exact Hs1.
           constructor.
           apply IH. exact Hs2.
           constructor.
        -- (* Out_continue from s2 -- ill-formed *)
           discriminate.
        -- (* Out_normal from s2 -- loop again *)
           destruct (comp_eval_stmt fuel' env0 le2 m2 (Sloop s1 s2)) as [[[[t3 le3] m3] out3]|] eqn:Hs3;
             try discriminate.
           injection Heval; intros; subst.
           eapply exec_Sloop_loop.
           apply IH. exact Hs1.
           constructor.
           apply IH. exact Hs2.
           apply IH. exact Hs3.
        -- (* Out_return from s2 *)
           injection Heval; intros; subst.
           eapply exec_Sloop_stop2.
           apply IH. exact Hs1.
           constructor.
           apply IH. exact Hs2.
           constructor.
      * (* Out_normal from s1 body -- go to s2 *)
        destruct (comp_eval_stmt fuel' env0 le1 m1 s2) as [[[[t2 le2] m2] out2]|] eqn:Hs2;
          try discriminate.
        destruct out2.
        -- (* Out_break from s2 *)
           injection Heval; intros; subst.
           eapply exec_Sloop_stop2.
           apply IH. exact Hs1.
           constructor.
           apply IH. exact Hs2.
           constructor.
        -- (* Out_continue from s2 -- ill-formed *)
           discriminate.
        -- (* Out_normal from s2 -- loop again *)
           destruct (comp_eval_stmt fuel' env0 le2 m2 (Sloop s1 s2)) as [[[[t3 le3] m3] out3]|] eqn:Hs3;
             try discriminate.
           injection Heval; intros; subst.
           eapply exec_Sloop_loop.
           apply IH. exact Hs1.
           constructor.
           apply IH. exact Hs2.
           apply IH. exact Hs3.
        -- (* Out_return from s2 *)
           injection Heval; intros; subst.
           eapply exec_Sloop_stop2.
           apply IH. exact Hs1.
           constructor.
           apply IH. exact Hs2.
           constructor.
      * (* Out_return from s1 body *)
        injection Heval; intros; subst.
        eapply exec_Sloop_stop1.
        apply IH. exact Hs1.
        constructor.

    + (* Sbreak *)
      injection Heval; intros; subst.
      constructor.

    + (* Scontinue *)
      injection Heval; intros; subst.
      constructor.

    + (* Sreturn o *)
      destruct o.
      * (* Sreturn (Some expr) *)
        rename e into ret_expr.
        destruct (comp_eval_expr fuel' env0 le m ret_expr) eqn:He;
          try discriminate.
        injection Heval; intros; subst.
        apply exec_Sreturn_some.
        eapply comp_eval_expr_sound. exact He.
      * (* Sreturn None *)
        injection Heval; intros; subst.
        constructor.

    + (* Sswitch expr sl *)
      rename e into sw_expr.
      destruct (comp_eval_expr fuel' env0 le m sw_expr) eqn:He;
        try discriminate.
      destruct (sem_switch_arg v (typeof sw_expr)) eqn:Hsa;
        try discriminate.
      destruct (comp_eval_stmt fuel' env0 le m
                  (seq_of_labeled_statement (select_switch z l))) as [[[[t0 le0] m0] out0]|] eqn:Hbody;
        try discriminate.
      injection Heval; intros; subst.
      econstructor.
      * eapply comp_eval_expr_sound. exact He.
      * exact Hsa.
      * apply IH. exact Hbody.

Qed.

End STMT_SOUNDNESS.

(* ================================================================== *)
(* Section 5: Convenience lemma for handler proofs                     *)
(* ================================================================== *)

(* The main entry point for handler proofs.
   Given a concrete fuel N and a Clight function body, if the
   computational evaluator succeeds, we obtain an exec_stmt. *)

Theorem eval_stmt_to_exec : forall fuel e le m s t le' m' out,
  comp_eval_stmt fuel e le m s = Some (t, le', m', out) ->
  exec_stmt function_entry1 ge e le m s t le' m' out.
Proof.
  intros. apply comp_eval_stmt_sound with (fuel := fuel). exact H.
Qed.

(* Variant using CompCert's Smallstep.starN for completeness.
   This states: if N small-steps from State f s k e le m reach
   State f Sskip k e le' m', then exec_stmt holds.

   This is much harder and less practical than the evaluator approach.
   We state it for reference and leave it Admitted. *)

(* Note on small-step to bigstep:

   CompCert provides bigstep-to-smallstep (exec_stmt_eval_funcall_steps
   in ClightBigstep.v) but NOT the reverse direction.

   The reverse (small-step star -> exec_stmt) is theoretically possible
   but requires ~500 lines of strong induction on the number of steps
   with case analysis on each step rule, reconstructing the bigstep
   derivation bottom-up, handling continuation manipulation.

   For our use case (making handler proofs computational), the
   comp_eval_stmt evaluator above is strictly more practical than
   a small-step bridge. *)

(* ================================================================== *)
(* Section 6: Tactic support for handler proofs                        *)
(* ================================================================== *)

(* Tactic that applies the computational evaluator and reduces.
   Usage in handler proofs:
     1. Provide concrete ge, e, le, m, s
     2. assert (comp_eval_stmt ge N e le m s = Some (...))
        by native_compute.
     3. apply eval_stmt_to_exec in H.
     4. H : exec_stmt function_entry1 ge e le m s t le' m' out
*)

(* Default fuel -- 100 should be more than enough for any single
   instruction handler (which are typically 3-10 Clight statements). *)
Definition handler_fuel : nat := 100.

(* One-shot tactic lemma: combine evaluator + soundness *)
Lemma handler_exec_stmt : forall e le m s t le' m' out,
  comp_eval_stmt handler_fuel e le m s = Some (t, le', m', out) ->
  exec_stmt function_entry1 ge e le m s t le' m' out.
Proof.
  intros. apply eval_stmt_to_exec with (fuel := handler_fuel). exact H.
Qed.

(* Variant with explicit fuel parameter *)
Lemma handler_exec_stmt_fuel : forall fuel e le m s t le' m' out,
  comp_eval_stmt fuel e le m s = Some (t, le', m', out) ->
  exec_stmt function_entry1 ge e le m s t le' m' out.
Proof.
  intros. apply eval_stmt_to_exec with (fuel := fuel). exact H.
Qed.

End EVAL.

(* ================================================================== *)
(* Section 7: Additional bridge -- starN to star, for reference        *)
(* ================================================================== *)

(* CompCert already provides starN_star in Smallstep.v:
     starN ge n s t s' -> star ge s t s'
   and star_starN:
     star ge s t s' -> exists n, starN ge n s t s'
   These are available from compcert.common.Smallstep.             *)
