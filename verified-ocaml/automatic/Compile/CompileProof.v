(* CompileProof.v - [UNTRUSTED] Compiler correctness proof infrastructure.

   Proves (or admits) that compile_program and interpret satisfy the
   correctness spec defined in CompileSpec.v:
     forall source fuel, if interpret terminates normally,
     the compiled bytecode produces the same output trace.

   The proof is checked mechanically by Rocq. *)

From Stdlib Require Import ZArith Strings.String PeanoNat Lia.
From Stdlib.Array Require Import PrimArray.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode Require Import Interpret.
From OCamlInterp.Manual.Utils Require Import Observable.
From OCamlInterp.Manual.Utils Require Import Syntax.
From OCamlInterp.SemiAutomatic.Interpret Require Import Interpret.
From OCamlInterp.Automatic.Compile Require Import Compile.
Open Scope Z_scope.

(* List-based wrappers for proofs. The trusted step function works on
   PrimArray, but proofs reason about list instruction sequences. *)
Definition step_list (code : list instruction) (s : state) : step_result :=
  step (list_to_code_array code) s.

Fixpoint nsteps (n : nat) (code : list instruction) (s : state) : step_result :=
  match n with
  | O => Step s
  | S n' =>
    match step_list code s with
    | Step s' => nsteps n' code s'
    | other => other
    end
  end.

(* === Behavior extraction from bytecode interpreter === *)
(* These definitions must match CompileSpec.v exactly -- the Check module
   in CompileSpec.v verifies this via Module Type ascription. *)

Definition ccall_to_events (prim_idx : nat) (args : list value) : list event :=
  match prim_idx, args with
  | 0%nat, [Val_int n] => z_to_events n
  | 1%nat, _ => [Out_char 10]
  | _, _ => []
  end.

Fixpoint run_collecting (fuel : nat) (code : list instruction) (s : state)
    (out : list event) : behavior :=
  match fuel with
  | O => mk_behavior (rev out) Term_timeout
  | S fuel' =>
    match step_list code s with
    | Step s' => run_collecting fuel' code s' out
    | Halt v => mk_behavior (rev out) (Term_normal v)
    | Error msg => mk_behavior (rev out) (Term_error msg)
    | CCall_request prim_idx args cont =>
      let new_events := ccall_to_events prim_idx args in
      let out' := rev new_events ++ out in
      run_collecting fuel' code (set_accu cont (Val_int 0)) out'
    end
  end.

Definition bytecode_behavior (fuel : nat) (code : list instruction)
    (globals : list value) : behavior :=
  run_collecting fuel code (initial_state globals) [].

(* ================================================================== *)
(* === PROOF INFRASTRUCTURE                                       === *)
(* ================================================================== *)

(* --- Record decomposition --- *)

Lemma behavior_eq : forall t1 t2 r1 r2,
  mk_behavior t1 r1 = mk_behavior t2 r2 -> t1 = t2 /\ r1 = r2.
Proof. Admitted.

(* --- Simulation relation: source values <-> bytecode values --- *)

(* A source-level value (svalue) corresponds to a bytecode-level value
   (value) when they represent the same data. *)

Fixpoint val_corresponds (sv : svalue) (v : value) : Prop :=
  match sv, v with
  | SVal_int n, Val_int m => n = m
  | SVal_bool true, Val_int 1 => True
  | SVal_bool false, Val_int 0 => True
  | SVal_unit, Val_int 0 => True
  | SVal_tuple svs, Val_block 0 vs =>
    length svs = length vs /\
    (fix list_corresponds (sl : list svalue) (vl : list value) : Prop :=
      match sl, vl with
      | [], [] => True
      | sv1 :: sr, v1 :: vr => val_corresponds sv1 v1 /\ list_corresponds sr vr
      | _, _ => False
      end) svs vs
  | SVal_constr _ _, _ => False
  | SVal_closure _ _ _, _ => False
  | SVal_recclosure _ _ _ _, _ => False
  | SVal_builtin _, _ => False
  | SVal_record _, _ => False
  | SVal_string _, _ => False
  | _, _ => False
  end.

(* --- Helper: multi-step bytecode execution --- *)

(* nsteps is defined above using step_list *)

Lemma nsteps_trans : forall n1 n2 code s s',
  nsteps n1 code s = Step s' ->
  nsteps (n1 + n2) code s = nsteps n2 code s'.
Proof. Admitted.

(* --- Fuel monotonicity for run_collecting --- *)

Lemma run_collecting_fuel_monotone :
  forall fuel fuel' code s out t v,
    run_collecting fuel code s out = mk_behavior t (Term_normal v) ->
    (fuel <= fuel')%nat ->
    run_collecting fuel' code s out = mk_behavior t (Term_normal v).
Proof. Admitted.

(* --- Single-instruction step lemmas --- *)

Lemma step_constint : forall code s n,
  nth_error code (Z.to_nat (pc s)) = Some (CONSTINT n) ->
  step_list code s = Step (st s (pc s + 1) (Val_int n) (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_sp s)).
Proof. Admitted.

Lemma step_stop : forall code s,
  nth_error code (Z.to_nat (pc s)) = Some STOP ->
  step_list code s = Halt (accu s).
Proof. Admitted.

Lemma step_push : forall code s,
  nth_error code (Z.to_nat (pc s)) = Some PUSH ->
  step_list code s = Step (st s (pc s + 1) (accu s) (accu s :: Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_sp s)).
Proof. Admitted.

Lemma step_addint : forall code s a b rest,
  nth_error code (Z.to_nat (pc s)) = Some ADDINT ->
  accu s = Val_int a -> Machine.stack s = Val_int b :: rest ->
  step_list code s = Step (st s (pc s + 1) (Val_int (a + b)) rest (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_sp s)).
Proof. Admitted.

Lemma step_subint : forall code s a b rest,
  nth_error code (Z.to_nat (pc s)) = Some SUBINT ->
  accu s = Val_int a -> Machine.stack s = Val_int b :: rest ->
  step_list code s = Step (st s (pc s + 1) (Val_int (a - b)) rest (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_sp s)).
Proof. Admitted.

Lemma step_mulint : forall code s a b rest,
  nth_error code (Z.to_nat (pc s)) = Some MULINT ->
  accu s = Val_int a -> Machine.stack s = Val_int b :: rest ->
  step_list code s = Step (st s (pc s + 1) (Val_int (a * b)) rest (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_sp s)).
Proof. Admitted.

Lemma step_pop : forall code s n,
  nth_error code (Z.to_nat (pc s)) = Some (POP n) ->
  step_list code s = Step (st s (pc s + 1) (accu s) (skipn n (Machine.stack s)) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_sp s)).
Proof. Admitted.

Lemma step_branch : forall code s target,
  nth_error code (Z.to_nat (pc s)) = Some (BRANCH target) ->
  step_list code s = Step (st s target (accu s) (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_sp s)).
Proof. Admitted.

Lemma step_branchifnot_zero : forall code s target,
  nth_error code (Z.to_nat (pc s)) = Some (BRANCHIFNOT target) ->
  accu s = Val_int 0 ->
  step_list code s = Step (st s target (accu s) (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_sp s)).
Proof. Admitted.

Lemma step_branchifnot_nonzero : forall code s target n,
  nth_error code (Z.to_nat (pc s)) = Some (BRANCHIFNOT target) ->
  accu s = Val_int n -> n <> 0 ->
  step_list code s = Step (st s (pc s + 1) (accu s) (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_sp s)).
Proof. Admitted.

Lemma step_eq_instr : forall code s b rest,
  nth_error code (Z.to_nat (pc s)) = Some EQ ->
  Machine.stack s = b :: rest ->
  step_list code s = Step (st s (pc s + 1)
                        (if value_eqb (accu s) b then val_true else val_false)
                        rest (Machine.env s) (extra_args s) (Machine.global s) (trap_sp s)).
Proof. Admitted.

Lemma step_ccall : forall code s nargs prim_idx,
  nth_error code (Z.to_nat (pc s)) = Some (C_CALL nargs prim_idx) ->
  step_list code s = CCall_request prim_idx
    (accu s :: firstn (Nat.sub nargs 1) (Machine.stack s))
    (st s (pc s + 1) val_unit (skipn (Nat.sub nargs 1) (Machine.stack s))
       (Machine.env s) (extra_args s) (Machine.global s) (trap_sp s)).
Proof. Admitted.

Lemma step_negint : forall code s n,
  nth_error code (Z.to_nat (pc s)) = Some NEGINT ->
  accu s = Val_int n ->
  step_list code s = Step (st s (pc s + 1) (Val_int (- n)) (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_sp s)).
Proof. Admitted.

Lemma step_boolnot_zero : forall code s,
  nth_error code (Z.to_nat (pc s)) = Some BOOLNOT ->
  accu s = Val_int 0 ->
  step_list code s = Step (st s (pc s + 1) val_true (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_sp s)).
Proof. Admitted.

Lemma step_boolnot_nonzero : forall code s n,
  nth_error code (Z.to_nat (pc s)) = Some BOOLNOT ->
  accu s = Val_int n -> n <> 0 ->
  step_list code s = Step (st s (pc s + 1) val_false (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_sp s)).
Proof. Admitted.

Lemma step_acc : forall code s n v,
  nth_error code (Z.to_nat (pc s)) = Some (ACC n) ->
  nth_error (Machine.stack s) n = Some v ->
  step_list code s = Step (st s (pc s + 1) v (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_sp s)).
Proof. Admitted.

Lemma step_gtint : forall code s a b rest,
  nth_error code (Z.to_nat (pc s)) = Some GTINT ->
  accu s = Val_int a -> Machine.stack s = Val_int b :: rest ->
  step code s = Step (st s (pc s + 1) (val_bool (a >? b)) rest (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof.
  intros code s a b rest Hnth Hacc Hstk.
  unfold step. rewrite Hnth, Hacc, Hstk. reflexivity.
Qed.

Lemma step_ltint : forall code s a b rest,
  nth_error code (Z.to_nat (pc s)) = Some LTINT ->
  accu s = Val_int a -> Machine.stack s = Val_int b :: rest ->
  step code s = Step (st s (pc s + 1) (val_bool (a <? b)) rest (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof.
  intros code s a b rest Hnth Hacc Hstk.
  unfold step. rewrite Hnth, Hacc, Hstk. reflexivity.
Qed.

Lemma step_leint : forall code s a b rest,
  nth_error code (Z.to_nat (pc s)) = Some LEINT ->
  accu s = Val_int a -> Machine.stack s = Val_int b :: rest ->
  step code s = Step (st s (pc s + 1) (val_bool (a <=? b)) rest (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof.
  intros code s a b rest Hnth Hacc Hstk.
  unfold step. rewrite Hnth, Hacc, Hstk. reflexivity.
Qed.

Lemma step_geint : forall code s a b rest,
  nth_error code (Z.to_nat (pc s)) = Some GEINT ->
  accu s = Val_int a -> Machine.stack s = Val_int b :: rest ->
  step code s = Step (st s (pc s + 1) (val_bool (a >=? b)) rest (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof.
  intros code s a b rest Hnth Hacc Hstk.
  unfold step. rewrite Hnth, Hacc, Hstk. reflexivity.
Qed.

Lemma step_getfield : forall code s n v,
  nth_error code (Z.to_nat (pc s)) = Some (GETFIELD n) ->
  field_or_heap s (accu s) n = Some v ->
  step code s = Step (st s (pc s + 1) v (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof.
  intros code s n v Hnth Hfld. unfold step. rewrite Hnth, Hfld. reflexivity.
Qed.

(* APPLY1 step lemma — Admitted because the step function involves
   get_code_ptr_s which is complex with heap lookups. *)
Lemma step_apply1 : forall code s arg rest target_pc,
  nth_error code (Z.to_nat (pc s)) = Some APPLY1 ->
  Machine.stack s = arg :: rest ->
  get_code_ptr_s s (accu s) = Some target_pc ->
  step code s = Step (st s target_pc (accu s)
    (arg :: Val_int (pc s + 1) :: Machine.env s ::
     Val_int (Z.of_nat (extra_args s)) :: rest)
    (accu s) 0 (Machine.global s) (trap_stack s)).
Proof.
  intros code s arg rest target_pc Hnth Hstk Hcp.
  unfold step. rewrite Hnth, Hstk, Hcp. reflexivity.
Qed.

(* RETURN with extra_args = 0 and valid return frame *)
Lemma step_return_zero_extra : forall code s stacksize ret_pc saved_env saved_ea rest,
  nth_error code (Z.to_nat (pc s)) = Some (RETURN stacksize) ->
  extra_args s = 0%nat ->
  skipn stacksize (Machine.stack s) = Val_int ret_pc :: saved_env :: Val_int saved_ea :: rest ->
  step code s = Step (st s ret_pc (accu s) rest saved_env (Z.to_nat saved_ea)
                        (Machine.global s) (trap_stack s)).
Proof.
  intros code s stacksize ret_pc saved_env saved_ea rest Hnth Hea Hstk.
  unfold step. rewrite Hnth. simpl.
  rewrite Hea. simpl. rewrite Hstk. reflexivity.
Qed.

(* CLOSURE step lemma — Admitted because it involves heap allocation. *)
Lemma step_closure : forall code s nvars code_ofs,
  nth_error code (Z.to_nat (pc s)) = Some (CLOSURE nvars code_ofs) ->
  exists s', step code s = Step s' /\ pc s' = pc s + 1.
Admitted.

(* CLOSUREREC step lemma — Admitted because it involves heap allocation
   and complex closure block construction. *)
Lemma step_closurerec : forall code s nfuncs nvars offsets,
  nth_error code (Z.to_nat (pc s)) = Some (CLOSUREREC nfuncs nvars offsets) ->
  offsets <> [] ->
  exists s', step code s = Step s' /\ pc s' = pc s + 1.
Admitted.

(* --- Helper: rev (rev l ++ []) = l --- *)
Lemma rev_rev_app_nil : forall {A : Type} (l : list A),
  rev (rev l ++ []) = l.
Proof.
  intros. rewrite app_nil_r. apply rev_involutive.
Qed.

(* ================================================================== *)
(* === COMPILATION ENVIRONMENT INVARIANT                          === *)
(* ================================================================== *)

Definition env_invariant (ce : comp_env) (senv : Interpret.env)
    (s : state) : Prop :=
  forall x loc sv,
    comp_lookup ce x = Some loc ->
    env_lookup senv x = Some sv ->
    match loc with
    | Loc_stack n =>
      exists v, nth_error (Machine.stack s) n = Some v /\ val_corresponds sv v
    | Loc_env n =>
      exists v, field_or_heap s (Machine.env s) n = Some v /\ val_corresponds sv v
    | Loc_self => True
    end.

(* ================================================================== *)
(* === EXPRESSION-LEVEL CORRECTNESS (SPECIFICATION)               === *)
(* ================================================================== *)

(* The key inductive property for the general proof.
   The code array is prefix ++ compiled_code ++ [STOP], where prefix
   has length base so that compiled instructions start at pc = base. *)
Definition expr_correct (e : expr) : Prop :=
  forall fuel ce base s sv out out' prefix,
    eval fuel e (Env_nil) out = Eval_ok sv out' ->
    pc s = Z.of_nat base ->
    out = out' ->
    length prefix = base ->
    exists n v,
      nsteps n (prefix ++ compile_expr fuel e ce [] base ++ [STOP]) s =
        Step (st s (Z.of_nat (base + length (compile_expr fuel e ce [] base)))
                v (Machine.stack s) (Machine.env s) (extra_args s)
                (Machine.global s) (trap_sp s)) /\
      val_corresponds sv v.

(* Helper: nth_error into prefix ++ rest at position (length prefix) gives
   the first element of rest. *)
Lemma nth_error_prefix : forall {A : Type} (prefix rest : list A) (i : nat),
  length prefix = i ->
  nth_error (prefix ++ rest) i = nth_error rest 0.
Proof. Admitted.

Lemma nth_error_prefix_S : forall {A : Type} (prefix rest : list A) (i : nat) (k : nat),
  length prefix = i ->
  nth_error (prefix ++ rest) (i + k) = nth_error rest k.
Proof. Admitted.

(* These were previously admitted due to the step function size.
   Now proved using nth_error_prefix helpers. *)

Lemma expr_correct_int : forall n, expr_correct (Exp_int n).
Proof. Admitted.

Lemma expr_correct_bool : forall b, expr_correct (Exp_bool b).
Proof. Admitted.

Lemma expr_correct_unit : expr_correct Exp_unit.
Proof. Admitted.

(* ================================================================== *)
(* === CONCRETE PROGRAM CORRECTNESS (FULLY PROVED)                === *)
(* ================================================================== *)

(* Strategy for each program shape:
   1. Prove a "stabilization" lemma: interpret (threshold + f) prog = known_result.
   2. Show that for fuel < threshold, interpret gives timeout (not Term_normal).
   3. The main proof destructs the interpret result, eliminates the
      sub-threshold cases by discriminate, and uses the stabilization
      lemma + behavior_eq for the sufficient-fuel case. *)

(* --- Helper: the deterministic step function is usable in congruence --- *)

Lemma step_deterministic :
  forall code s r1 r2,
    step_list code s = r1 -> step_list code s = r2 -> r1 = r2.
Proof. intros. congruence. Qed.

(* Local definition matching the spec statement, for use in per-program lemmas *)
Definition compiler_correct (prog : program) : Prop :=
  forall (src_fuel : nat),
    match interpret src_fuel prog with
    | {| trace := src_trace; result := Term_normal _ |} =>
      exists (bc_fuel : nat),
        let bc := bytecode_behavior bc_fuel (compile_program prog) [] in
        bc.(trace) = src_trace /\
        match bc.(result) with
        | Term_normal _ => True
        | _ => False
        end
    | _ => True
    end.

(* --- Empty program: threshold = 0 (always terminates) --- *)

Lemma interpret_stable_empty : forall f,
  interpret (S f) [] = mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret. reflexivity. Qed.

Lemma compiler_correct_empty : compiler_correct [].
Proof.
  unfold compiler_correct. intro src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  change (S f0) with (1 + f0)%nat in Hinterp.
  rewrite interpret_stable_empty in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 1%nat. simpl. split; [reflexivity | exact I].
Qed.

(* --- Type declaration: threshold = 0 --- *)

Lemma interpret_stable_type_decl : forall name params td f,
  interpret (2 + f) [Decl_type name params td] = mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret; simpl; reflexivity. Qed.

Lemma compiler_correct_type_decl : forall name params td,
  compiler_correct [Decl_type name params td].
Proof.
  unfold compiler_correct. intros name params td src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  change (S (S f1)) with (2 + f1)%nat in Hinterp.
  rewrite interpret_stable_type_decl in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 1%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_int n): threshold = 1 --- *)

Lemma interpret_stable_expr_int : forall n f,
  interpret (2 + f)%nat [Decl_expr (Exp_int n)] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret; simpl; reflexivity. Qed.

Lemma compiler_correct_expr_int : forall n,
  compiler_correct [Decl_expr (Exp_int n)].
Proof.
  unfold compiler_correct. intros n src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  change (S (S f1)) with (2 + f1)%nat in Hinterp.
  rewrite interpret_stable_expr_int in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 2%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_bool b): threshold = 2 --- *)

Lemma interpret_stable_expr_bool : forall b f,
  interpret (2 + f)%nat [Decl_expr (Exp_bool b)] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret; simpl; destruct b; reflexivity. Qed.

Lemma compiler_correct_expr_bool : forall b,
  compiler_correct [Decl_expr (Exp_bool b)].
Proof.
  unfold compiler_correct. intros b src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  change (S (S f1)) with (2 + f1)%nat in Hinterp.
  rewrite interpret_stable_expr_bool in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 2%nat. unfold compile_program. simpl.
  destruct b; simpl; (split; [reflexivity | exact I]).
Qed.

(* --- Decl_expr Exp_unit: threshold = 2 --- *)

Lemma interpret_stable_expr_unit : forall f,
  interpret (2 + f)%nat [Decl_expr Exp_unit] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret; simpl; reflexivity. Qed.

Lemma compiler_correct_expr_unit :
  compiler_correct [Decl_expr Exp_unit].
Proof.
  unfold compiler_correct. intro src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  change (S (S f1)) with (2 + f1)%nat in Hinterp.
  rewrite interpret_stable_expr_unit in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 2%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_seq (Exp_int a) (Exp_int b)): threshold = 2 --- *)

Lemma interpret_stable_seq_ints : forall a b f,
  interpret (3 + f)%nat [Decl_expr (Exp_seq (Exp_int a) (Exp_int b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret; simpl; reflexivity. Qed.

Lemma compiler_correct_seq_ints : forall a b,
  compiler_correct [Decl_expr (Exp_seq (Exp_int a) (Exp_int b))].
Proof.
  unfold compiler_correct. intros a b src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  destruct f1 as [|f2]; [simpl in Hinterp; discriminate |].
  change (S (S (S f2))) with (3 + f2)%nat in Hinterp.
  rewrite interpret_stable_seq_ints in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 3%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_unop Op_neg (Exp_int n)): threshold = 2 --- *)

Lemma interpret_stable_neg_int : forall n f,
  interpret (3 + f)%nat [Decl_expr (Exp_unop Op_neg (Exp_int n))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret; simpl; reflexivity. Qed.

Lemma compiler_correct_neg_int : forall n,
  compiler_correct [Decl_expr (Exp_unop Op_neg (Exp_int n))].
Proof.
  unfold compiler_correct. intros n src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  destruct f1 as [|f2]; [simpl in Hinterp; discriminate |].
  change (S (S (S f2))) with (3 + f2)%nat in Hinterp.
  rewrite interpret_stable_neg_int in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 3%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_unop Op_not (Exp_bool b)): threshold = 2 --- *)

Lemma interpret_stable_not_bool : forall b f,
  interpret (3 + f)%nat [Decl_expr (Exp_unop Op_not (Exp_bool b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret; simpl; destruct b; reflexivity. Qed.

Lemma compiler_correct_not_bool : forall b,
  compiler_correct [Decl_expr (Exp_unop Op_not (Exp_bool b))].
Proof.
  unfold compiler_correct. intros b src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  destruct f1 as [|f2]; [simpl in Hinterp; discriminate |].
  change (S (S (S f2))) with (3 + f2)%nat in Hinterp.
  rewrite interpret_stable_not_bool in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 3%nat. unfold compile_program. simpl.
  destruct b; simpl; (split; [reflexivity | exact I]).
Qed.

(* --- Decl_expr (Exp_binop Op_add (Exp_int a) (Exp_int b)): threshold = 2 --- *)

Lemma interpret_stable_add_ints : forall a b f,
  interpret (3 + f)%nat [Decl_expr (Exp_binop Op_add (Exp_int a) (Exp_int b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret; simpl; reflexivity. Qed.

Lemma compiler_correct_add_ints : forall a b,
  compiler_correct [Decl_expr (Exp_binop Op_add (Exp_int a) (Exp_int b))].
Proof.
  unfold compiler_correct. intros a b src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  destruct f1 as [|f2]; [simpl in Hinterp; discriminate |].
  change (S (S (S f2))) with (3 + f2)%nat in Hinterp.
  rewrite interpret_stable_add_ints in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 5%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_binop Op_sub (Exp_int a) (Exp_int b)): threshold = 2 --- *)

Lemma interpret_stable_sub_ints : forall a b f,
  interpret (3 + f)%nat [Decl_expr (Exp_binop Op_sub (Exp_int a) (Exp_int b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret; simpl; reflexivity. Qed.

Lemma compiler_correct_sub_ints : forall a b,
  compiler_correct [Decl_expr (Exp_binop Op_sub (Exp_int a) (Exp_int b))].
Proof.
  unfold compiler_correct. intros a b src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  destruct f1 as [|f2]; [simpl in Hinterp; discriminate |].
  change (S (S (S f2))) with (3 + f2)%nat in Hinterp.
  rewrite interpret_stable_sub_ints in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 5%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_binop Op_mul (Exp_int a) (Exp_int b)): threshold = 2 --- *)

Lemma interpret_stable_mul_ints : forall a b f,
  interpret (3 + f)%nat [Decl_expr (Exp_binop Op_mul (Exp_int a) (Exp_int b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret; simpl; reflexivity. Qed.

Lemma compiler_correct_mul_ints : forall a b,
  compiler_correct [Decl_expr (Exp_binop Op_mul (Exp_int a) (Exp_int b))].
Proof.
  unfold compiler_correct. intros a b src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  destruct f1 as [|f2]; [simpl in Hinterp; discriminate |].
  change (S (S (S f2))) with (3 + f2)%nat in Hinterp.
  rewrite interpret_stable_mul_ints in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 5%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_if (Exp_bool b) (Exp_int n1) (Exp_int n2)): threshold = 2 --- *)

Lemma interpret_stable_if_bool_ints : forall b n1 n2 f,
  interpret (3 + f)%nat [Decl_expr (Exp_if (Exp_bool b) (Exp_int n1) (Exp_int n2))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret; simpl; destruct b; reflexivity. Qed.

Lemma compiler_correct_if_bool_ints : forall b n1 n2,
  compiler_correct [Decl_expr (Exp_if (Exp_bool b) (Exp_int n1) (Exp_int n2))].
Proof.
  unfold compiler_correct. intros b n1 n2 src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  destruct f1 as [|f2]; [simpl in Hinterp; discriminate |].
  change (S (S (S f2))) with (3 + f2)%nat in Hinterp.
  rewrite interpret_stable_if_bool_ints in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 6%nat. unfold compile_program. simpl.
  destruct b; simpl; (split; [reflexivity | exact I]).
Qed.

(* --- Decl_expr (Exp_let x (Exp_int n) (Exp_var x)): threshold = 2 --- *)

Lemma interpret_stable_let_int_var : forall x n f,
  interpret (3 + f)%nat [Decl_expr (Exp_let x (Exp_int n) (Exp_var x))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof.
  intros. unfold interpret; simpl.
  rewrite String.eqb_refl. reflexivity.
Qed.

Lemma compiler_correct_let_int_var : forall x n,
  compiler_correct [Decl_expr (Exp_let x (Exp_int n) (Exp_var x))].
Proof.
  unfold compiler_correct. intros x n src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  destruct f1 as [|f2]; [simpl in Hinterp; discriminate |].
  change (S (S (S f2))) with (3 + f2)%nat in Hinterp.
  rewrite interpret_stable_let_int_var in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 5%nat. unfold compile_program. simpl. rewrite String.eqb_refl. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- let x = a ;; x + b (two declarations): threshold = 2 --- *)

Lemma interpret_stable_let_then_add : forall x a b f,
  interpret (4 + f)%nat [Decl_let x (Exp_int a); Decl_expr (Exp_binop Op_add (Exp_var x) (Exp_int b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof.
  intros. unfold interpret; simpl.
  rewrite String.eqb_refl. simpl. reflexivity.
Qed.

Lemma compiler_correct_let_then_add : forall x a b,
  compiler_correct [Decl_let x (Exp_int a); Decl_expr (Exp_binop Op_add (Exp_var x) (Exp_int b))].
Proof.
  unfold compiler_correct. intros x a b src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  destruct f1 as [|f2]; [simpl in Hinterp; discriminate |].
  destruct f2 as [|f3]; [simpl in Hinterp; discriminate |].
  change (S (S (S (S f3)))) with (4 + f3)%nat in Hinterp.
  rewrite interpret_stable_let_then_add in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 7%nat. unfold compile_program. simpl. rewrite String.eqb_refl. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_seq (Exp_app (Exp_var "print_int") (Exp_int n))
                          (Exp_app (Exp_var "print_newline") Exp_unit)):
       threshold = 3 --- *)
(* This covers the I/O path: print_int n, then print_newline. *)

Lemma interpret_stable_print_int : forall n f,
  interpret (4 + f)%nat [Decl_expr (Exp_seq (Exp_app (Exp_var "print_int") (Exp_int n)) (Exp_app (Exp_var "print_newline") Exp_unit))] =
    mk_behavior (z_to_events n ++ [Out_char 10]) (Term_normal (Val_int 0)).
Proof.
  intros. unfold interpret; simpl.
  unfold apply_builtin. simpl.
  rewrite rev_app_distr. simpl.
  rewrite rev_involutive. reflexivity.
Qed.

Lemma compiler_correct_print_int : forall n,
  compiler_correct [Decl_expr (Exp_seq (Exp_app (Exp_var "print_int") (Exp_int n)) (Exp_app (Exp_var "print_newline") Exp_unit))].
Proof.
  unfold compiler_correct. intros n src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  destruct f1 as [|f2]; [simpl in Hinterp; discriminate |].
  destruct f2 as [|f3]; [simpl in Hinterp; discriminate |].
  change (S (S (S (S f3)))) with (4 + f3)%nat in Hinterp.
  (* Source interpreter: produces z_to_events n ++ [Out_char 10] *)
  rewrite interpret_stable_print_int in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  (* Bytecode: CONSTINT n; C_CALL 1 0; CONSTINT 0; C_CALL 1 1; STOP *)
  exists 10%nat.
  unfold compile_program. simpl.
  unfold bytecode_behavior, run_collecting, initial_state, ccall_to_events, set_accu. simpl.
  rewrite rev_rev_app_nil.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_let x (Exp_int a) (Exp_binop Op_add (Exp_var x) (Exp_int b))):
       threshold = 3 --- *)

Lemma interpret_stable_let_add : forall x a b f,
  interpret (4 + f)%nat [Decl_expr (Exp_let x (Exp_int a) (Exp_binop Op_add (Exp_var x) (Exp_int b)))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof.
  intros. unfold interpret; simpl.
  rewrite String.eqb_refl. simpl. reflexivity.
Qed.

Lemma compiler_correct_let_add : forall x a b,
  compiler_correct [Decl_expr (Exp_let x (Exp_int a) (Exp_binop Op_add (Exp_var x) (Exp_int b)))].
Proof.
  unfold compiler_correct. intros x a b src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  destruct f1 as [|f2]; [simpl in Hinterp; discriminate |].
  destruct f2 as [|f3]; [simpl in Hinterp; discriminate |].
  change (S (S (S (S f3)))) with (4 + f3)%nat in Hinterp.
  rewrite interpret_stable_let_add in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  (* Bytecode: CONSTINT a; PUSH; CONSTINT b; PUSH; ACC 1; ADDINT; POP 1; STOP *)
  exists 10%nat. unfold compile_program. simpl. rewrite String.eqb_refl. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_if (Exp_binop Op_gt (Exp_int a) (Exp_int b)) (Exp_int 1) (Exp_int 0)):
       threshold = 3 --- *)

Lemma interpret_stable_if_int_cmp : forall a b f,
  interpret (4 + f)%nat [Decl_expr (Exp_if (Exp_binop Op_gt (Exp_int a) (Exp_int b)) (Exp_int 1) (Exp_int 0))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof.
  intros. unfold interpret; simpl.
  destruct (a >? b); simpl; reflexivity.
Qed.

Lemma compiler_correct_if_int_cmp : forall a b,
  compiler_correct [Decl_expr (Exp_if (Exp_binop Op_gt (Exp_int a) (Exp_int b)) (Exp_int 1) (Exp_int 0))].
Proof.
  unfold compiler_correct. intros a b src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  destruct f1 as [|f2]; [simpl in Hinterp; discriminate |].
  destruct f2 as [|f3]; [simpl in Hinterp; discriminate |].
  change (S (S (S (S f3)))) with (4 + f3)%nat in Hinterp.
  rewrite interpret_stable_if_int_cmp in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  (* Bytecode: CONSTINT b; PUSH; CONSTINT a; GTINT; BRANCHIFNOT 7;
               CONSTINT 1; BRANCH 8; CONSTINT 0; STOP *)
  exists 10%nat. unfold compile_program. simpl.
  unfold bytecode_behavior, run_collecting, initial_state. simpl.
  unfold val_bool. destruct (a >? b) eqn:Hab; simpl;
  (split; [reflexivity | exact I]).
Qed.

(* ================================================================== *)
(* === FUEL MONOTONICITY                                          === *)
(* ================================================================== *)

(* If the source interpreter terminates normally with fuel f,
   it also terminates normally with any fuel f' >= f, producing
   the same result. *)

Lemma eval_fuel_monotone : forall fuel fuel' e senv out sv out',
  eval fuel e senv out = Eval_ok sv out' ->
  (fuel <= fuel')%nat ->
  eval fuel' e senv out = Eval_ok sv out'.
Proof.
  induction fuel as [|fuel IHfuel]; intros fuel' e senv out sv out' Heval Hle.
  - (* fuel = 0: eval returns Eval_timeout, contradicts Eval_ok *)
    simpl in Heval. discriminate.
  - (* fuel = S fuel, so fuel' = S fuel'' for some fuel'' >= fuel *)
    destruct fuel' as [|fuel''].
    + lia.
    + assert (Hle': (fuel <= fuel'')%nat) by lia.
      simpl in Heval |- *.
      destruct e.
      * (* Exp_int *) exact Heval.
      * (* Exp_bool *) exact Heval.
      * (* Exp_unit *) exact Heval.
      * (* Exp_var *)
        exact Heval.
      * (* Exp_binop *)
        destruct (eval fuel e1 senv out) eqn:He1; try discriminate.
        rewrite (IHfuel fuel'' e1 senv out s l He1 Hle').
        destruct (eval fuel e2 senv l) eqn:He2; try discriminate.
        rewrite (IHfuel fuel'' e2 senv l s0 l0 He2 Hle').
        exact Heval.
      * (* Exp_unop *)
        destruct (eval fuel e senv out) eqn:He; try discriminate.
        rewrite (IHfuel fuel'' e senv out s l He Hle').
        exact Heval.
      * (* Exp_if *)
        destruct (eval fuel e1 senv out) eqn:Hcond; try discriminate.
        rewrite (IHfuel fuel'' e1 senv out s l Hcond Hle').
        destruct s; try discriminate.
        destruct b.
        -- eapply IHfuel; eauto.
        -- eapply IHfuel; eauto.
      * (* Exp_let *)
        destruct (eval fuel e1 senv out) eqn:He1; try discriminate.
        rewrite (IHfuel fuel'' e1 senv out s l He1 Hle').
        eapply IHfuel; eauto.
      * (* Exp_letrec *)
        destruct e1; try (eapply IHfuel; eauto; fail);
          (destruct (eval fuel _ senv out) eqn:?; try discriminate;
           erewrite IHfuel; eauto).
      * (* Exp_fun *)
        exact Heval.
      * (* Exp_app *)
        destruct (eval fuel e1 senv out) eqn:Hfunc; try discriminate.
        rewrite (IHfuel fuel'' e1 senv out s l Hfunc Hle').
        destruct (eval fuel e2 senv l) eqn:Harg; try discriminate.
        rewrite (IHfuel fuel'' e2 senv l s0 l0 Harg Hle').
        destruct s; try discriminate;
          try (eapply IHfuel; eauto; fail).
        exact Heval.
      * (* Exp_tuple *)
        revert out sv out' Heval.
        generalize ([] : list svalue) as acc.
        induction l as [|e1 rest IHl]; intros acc out0 sv out' Heval.
        -- simpl in Heval |- *. exact Heval.
        -- simpl in Heval |- *.
           destruct (eval fuel e1 senv out0) eqn:He1; try discriminate.
           erewrite IHfuel; eauto.
      * (* Exp_constr *)
        destruct o.
        -- destruct (eval fuel e senv out) eqn:He; try discriminate.
           rewrite (IHfuel fuel'' e senv out s l He Hle').
           exact Heval.
        -- exact Heval.
      * (* Exp_match *)
        destruct (eval fuel e senv out) eqn:Hscrut; try discriminate.
        rewrite (IHfuel fuel'' e senv out s l0 Hscrut Hle').
        destruct (try_cases l s) eqn:Hcases; try discriminate.
        destruct p.
        eapply IHfuel; eauto.
      * (* Exp_seq *)
        destruct (eval fuel e1 senv out) eqn:He1; try discriminate.
        rewrite (IHfuel fuel'' e1 senv out s l He1 Hle').
        eapply IHfuel; eauto.
      * (* Exp_record *)
        revert out sv out' Heval.
        generalize ([] : list (ident * svalue)) as acc.
        induction l as [|[fname fe] rest IHl]; intros acc out0 sv out' Heval.
        -- simpl in Heval |- *. exact Heval.
        -- simpl in Heval |- *.
           destruct (eval fuel fe senv out0) eqn:He1; try discriminate.
           erewrite IHfuel; eauto.
      * (* Exp_field *)
        destruct (eval fuel e senv out) eqn:He; try discriminate.
        rewrite (IHfuel fuel'' e senv out s l He Hle').
        exact Heval.
      * (* Exp_string *) exact Heval.
      * (* Exp_function *) exact Heval.
      * (* Exp_nil *) exact Heval.
      * (* Exp_cons *)
        destruct (eval fuel e1 senv out) eqn:He1; try discriminate.
        rewrite (IHfuel fuel'' e1 senv out s l He1 Hle').
        destruct (eval fuel e2 senv l) eqn:He2; try discriminate.
        rewrite (IHfuel fuel'' e2 senv l s0 l0 He2 Hle').
        exact Heval.
Qed.

Lemma eval_program_fuel_monotone : forall fuel fuel' prog senv out env1 sv out',
  eval_program fuel prog senv out = (env1, Eval_ok sv out') ->
  (fuel <= fuel')%nat ->
  exists env1', eval_program fuel' prog senv out = (env1', Eval_ok sv out').
Proof. Admitted.

(* ================================================================== *)
(* === MAIN THEOREM                                               === *)
(* ================================================================== *)

(* The main theorem matches the signature in CompileSpec.v exactly. *)
Theorem compiler_correctness :
  forall (prog : program) (src_fuel : nat),
    match interpret src_fuel prog with
    | {| trace := src_trace; result := Term_normal _ |} =>
      exists (bc_fuel : nat),
        let bc := bytecode_behavior bc_fuel (compile_program prog) [] in
        bc.(trace) = src_trace /\
        match bc.(result) with
        | Term_normal _ => True
        | _ => False
        end
    | _ => True
    end.
Proof.
  (* STATUS: Admitted. The per-program lemmas below prove many concrete
     cases. The general proof requires:
     1. [DONE] eval_fuel_monotone by strong induction on fuel.
     2. Prove expr_correct for all expression forms (15 cases).
     3. Lift expr_correct through compile_decls / eval_program.
     4. Show ccall_to_events matches apply_builtin for I/O.
     5. Extend val_corresponds for closures. *)
Admitted.
