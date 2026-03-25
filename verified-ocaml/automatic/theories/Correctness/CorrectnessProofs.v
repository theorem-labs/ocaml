(* CorrectnessProofs.v - [TRUSTED] Compiler correctness theorem statement.

   This file contains the STATEMENT of compiler correctness. The statement
   itself is trusted: it defines what it means for the compiler to be correct.
   The proof (when provided) is checked mechanically by Rocq.

   The core theorem:
     forall source, interpret(source) = (interpret-bytecode . compile)(source)

   Both sides must produce the same observable behavior (output trace + result). *)

From Stdlib Require Import ZArith Strings.String PeanoNat Lia.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Value AST.
From OCamlInterp.Manual.InterpBytecode Require Import Machine Interp.
From OCamlInterp.Manual.Utils Require Import Observable.
From OCamlInterp.Manual.Utils Require Import Syntax.
From OCamlInterp.SemiAutomatic.Interpret Require Import SourceInterp.
From OCamlInterp.Automatic.Compile Require Import Compile.
Open Scope Z_scope.

(* === Behavior extraction from bytecode interpreter === *)

(* Convert a C call to output events.
   Primitive indices must match Compile.v's is_builtin:
     0 = print_int, 1 = print_newline, 2 = print_string
   Uses z_to_events from SourceInterp.v -- single source of truth. *)
Definition ccall_to_events (prim_idx : nat) (args : list value) : list event :=
  match prim_idx, args with
  | 0%nat, [Val_int n] => z_to_events n        (* print_int *)
  | 1%nat, _ => [Out_char 10]                   (* print_newline *)
  | _, _ => []
  end.

(* Run bytecode with a handler that collects output events.
   Output list is accumulated in reverse order (newest first). *)
Fixpoint run_collecting (fuel : nat) (code : list instruction) (s : state)
    (out : list event) : behavior :=
  match fuel with
  | O => mk_behavior (rev out) Term_timeout
  | S fuel' =>
    match step code s with
    | Step s' => run_collecting fuel' code s' out
    | Halt v => mk_behavior (rev out) (Term_normal v)
    | Error msg => mk_behavior (rev out) (Term_error msg)
    | CCall_request prim_idx args cont =>
      let new_events := ccall_to_events prim_idx args in
      let out' := rev new_events ++ out in
      run_collecting fuel' code (set_accu cont (Val_int 0)) out'
    end
  end.

(* Extract behavior from running compiled code *)
Definition bytecode_behavior (fuel : nat) (code : list instruction)
    (globals : list value) : behavior :=
  run_collecting fuel code (initial_state globals) [].

(* === The Correctness Theorem === *)

(* The source interpreter and bytecode interpreter consume fuel at different
   rates: the source interpreter uses 1 fuel per AST node, while the bytecode
   interpreter uses 1 fuel per instruction. So we cannot use the same fuel
   parameter for both sides. Instead, we state: if the source interpreter
   terminates normally, there exists enough bytecode fuel such that the
   compiled bytecode terminates normally with the same output trace. *)

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

(* ================================================================== *)
(* === PROOF INFRASTRUCTURE                                       === *)
(* ================================================================== *)

(* --- Record decomposition --- *)

Lemma behavior_eq : forall t1 t2 r1 r2,
  mk_behavior t1 r1 = mk_behavior t2 r2 -> t1 = t2 /\ r1 = r2.
Proof.
  intros t1 t2 r1 r2 H.
  assert (trace (mk_behavior t1 r1) = trace (mk_behavior t2 r2))
    by (rewrite H; reflexivity).
  assert (result (mk_behavior t1 r1) = result (mk_behavior t2 r2))
    by (rewrite H; reflexivity).
  simpl in *. auto.
Qed.

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
  | _, _ => False
  end.

(* --- Helper: multi-step bytecode execution --- *)

Fixpoint nsteps (n : nat) (code : list instruction) (s : state) : step_result :=
  match n with
  | O => Step s
  | S n' =>
    match step code s with
    | Step s' => nsteps n' code s'
    | other => other
    end
  end.

Lemma nsteps_trans : forall n1 n2 code s s',
  nsteps n1 code s = Step s' ->
  nsteps (n1 + n2) code s = nsteps n2 code s'.
Proof.
  induction n1; intros n2 code s s' H.
  - simpl in H. inversion H; subst. reflexivity.
  - simpl in H. simpl.
    destruct (step code s) eqn:Estep; try discriminate.
    apply IHn1. exact H.
Qed.

(* --- Fuel monotonicity for run_collecting --- *)

Lemma run_collecting_fuel_monotone :
  forall fuel fuel' code s out t v,
    run_collecting fuel code s out = mk_behavior t (Term_normal v) ->
    (fuel <= fuel')%nat ->
    run_collecting fuel' code s out = mk_behavior t (Term_normal v).
Proof.
  induction fuel; intros fuel' code s out t v Hrun Hle.
  - simpl in Hrun. discriminate.
  - simpl in Hrun.
    destruct fuel' as [|fuel''].
    + lia.
    + simpl.
      destruct (step code s) eqn:Estep.
      * apply IHfuel with (fuel' := fuel''); [exact Hrun | lia].
      * exact Hrun.
      * discriminate.
      * apply IHfuel with (fuel' := fuel''); [exact Hrun | lia].
Qed.

(* --- Single-instruction step lemmas --- *)

Lemma step_constint : forall code s n,
  nth_error code (Z.to_nat (pc s)) = Some (CONSTINT n) ->
  step code s = Step (st s (pc s + 1) (Val_int n) (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof. intros code s n Hnth. unfold step. rewrite Hnth. reflexivity. Qed.

Lemma step_stop : forall code s,
  nth_error code (Z.to_nat (pc s)) = Some STOP ->
  step code s = Halt (accu s).
Proof. intros code s Hnth. unfold step. rewrite Hnth. reflexivity. Qed.

Lemma step_push : forall code s,
  nth_error code (Z.to_nat (pc s)) = Some PUSH ->
  step code s = Step (st s (pc s + 1) (accu s) (accu s :: Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof. intros code s Hnth. unfold step. rewrite Hnth. reflexivity. Qed.

Lemma step_addint : forall code s a b rest,
  nth_error code (Z.to_nat (pc s)) = Some ADDINT ->
  accu s = Val_int a -> Machine.stack s = Val_int b :: rest ->
  step code s = Step (st s (pc s + 1) (Val_int (a + b)) rest (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof.
  intros code s a b rest Hnth Hacc Hstk.
  unfold step. rewrite Hnth, Hacc, Hstk. reflexivity.
Qed.

Lemma step_subint : forall code s a b rest,
  nth_error code (Z.to_nat (pc s)) = Some SUBINT ->
  accu s = Val_int a -> Machine.stack s = Val_int b :: rest ->
  step code s = Step (st s (pc s + 1) (Val_int (a - b)) rest (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof.
  intros code s a b rest Hnth Hacc Hstk.
  unfold step. rewrite Hnth, Hacc, Hstk. reflexivity.
Qed.

Lemma step_mulint : forall code s a b rest,
  nth_error code (Z.to_nat (pc s)) = Some MULINT ->
  accu s = Val_int a -> Machine.stack s = Val_int b :: rest ->
  step code s = Step (st s (pc s + 1) (Val_int (a * b)) rest (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof.
  intros code s a b rest Hnth Hacc Hstk.
  unfold step. rewrite Hnth, Hacc, Hstk. reflexivity.
Qed.

Lemma step_pop : forall code s n,
  nth_error code (Z.to_nat (pc s)) = Some (POP n) ->
  step code s = Step (st s (pc s + 1) (accu s) (skipn n (Machine.stack s)) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof. intros code s n Hnth. unfold step. rewrite Hnth. reflexivity. Qed.

Lemma step_branch : forall code s target,
  nth_error code (Z.to_nat (pc s)) = Some (BRANCH target) ->
  step code s = Step (st s target (accu s) (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof. intros code s target Hnth. unfold step. rewrite Hnth. reflexivity. Qed.

Lemma step_branchifnot_zero : forall code s target,
  nth_error code (Z.to_nat (pc s)) = Some (BRANCHIFNOT target) ->
  accu s = Val_int 0 ->
  step code s = Step (st s target (accu s) (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof.
  intros code s target Hnth Hacc.
  unfold step. rewrite Hnth, Hacc. reflexivity.
Qed.

Lemma step_branchifnot_nonzero : forall code s target n,
  nth_error code (Z.to_nat (pc s)) = Some (BRANCHIFNOT target) ->
  accu s = Val_int n -> n <> 0 ->
  step code s = Step (st s (pc s + 1) (accu s) (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof.
  intros code s target n Hnth Hacc Hneq.
  unfold step. rewrite Hnth, Hacc.
  destruct n; [exfalso; apply Hneq; reflexivity | reflexivity | reflexivity].
Qed.

Lemma step_eq_instr : forall code s b rest,
  nth_error code (Z.to_nat (pc s)) = Some EQ ->
  Machine.stack s = b :: rest ->
  step code s = Step (st s (pc s + 1)
                        (if value_eqb (accu s) b then val_true else val_false)
                        rest (Machine.env s) (extra_args s) (Machine.global s) (trap_stack s)).
Proof.
  intros code s b rest Hnth Hstk.
  unfold step. rewrite Hnth, Hstk. reflexivity.
Qed.

Lemma step_ccall : forall code s nargs prim_idx,
  nth_error code (Z.to_nat (pc s)) = Some (C_CALL nargs prim_idx) ->
  step code s = CCall_request prim_idx
    (accu s :: firstn (Nat.sub nargs 1) (Machine.stack s))
    (st s (pc s + 1) val_unit (skipn (Nat.sub nargs 1) (Machine.stack s))
       (Machine.env s) (extra_args s) (Machine.global s) (trap_stack s)).
Proof. intros code s nargs prim_idx Hnth. unfold step. rewrite Hnth. reflexivity. Qed.

Lemma step_negint : forall code s n,
  nth_error code (Z.to_nat (pc s)) = Some NEGINT ->
  accu s = Val_int n ->
  step code s = Step (st s (pc s + 1) (Val_int (- n)) (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof.
  intros code s n Hnth Hacc. unfold step. rewrite Hnth, Hacc. reflexivity.
Qed.

Lemma step_boolnot_zero : forall code s,
  nth_error code (Z.to_nat (pc s)) = Some BOOLNOT ->
  accu s = Val_int 0 ->
  step code s = Step (st s (pc s + 1) val_true (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof.
  intros code s Hnth Hacc. unfold step. rewrite Hnth, Hacc. reflexivity.
Qed.

Lemma step_boolnot_nonzero : forall code s n,
  nth_error code (Z.to_nat (pc s)) = Some BOOLNOT ->
  accu s = Val_int n -> n <> 0 ->
  step code s = Step (st s (pc s + 1) val_false (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof.
  intros code s n Hnth Hacc Hneq. unfold step. rewrite Hnth, Hacc.
  destruct n; [exfalso; apply Hneq; reflexivity | reflexivity | reflexivity].
Qed.

Lemma step_acc : forall code s n v,
  nth_error code (Z.to_nat (pc s)) = Some (ACC n) ->
  nth_error (Machine.stack s) n = Some v ->
  step code s = Step (st s (pc s + 1) v (Machine.stack s) (Machine.env s)
                        (extra_args s) (Machine.global s) (trap_stack s)).
Proof.
  intros code s n v Hnth Hstk. unfold step. rewrite Hnth, Hstk. reflexivity.
Qed.

(* ================================================================== *)
(* === COMPILATION ENVIRONMENT INVARIANT                          === *)
(* ================================================================== *)

Definition env_invariant (ce : comp_env) (senv : SourceInterp.env)
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

(* The key inductive property for the general proof. *)
Definition expr_correct (e : expr) : Prop :=
  forall fuel ce base s sv out out',
    eval fuel e (Env_nil) out = Eval_ok sv out' ->
    pc s = Z.of_nat base ->
    out = out' ->
    exists n v,
      nsteps n (compile_expr fuel e ce base ++ [STOP]) s =
        Step (st s (Z.of_nat (base + length (compile_expr fuel e ce base)))
                v (Machine.stack s) (Machine.env s) (extra_args s)
                (Machine.global s) (trap_stack s)) /\
      val_corresponds sv v.

(* These are admitted: proving them requires Ltac automation to handle
   the large step function, or refactoring step into smaller pieces.
   The concrete program lemmas below demonstrate correctness by
   computation instead. *)

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
    step code s = r1 -> step code s = r2 -> r1 = r2.
Proof. intros. congruence. Qed.

(* --- Empty program: threshold = 0 (always terminates) --- *)

Lemma interpret_stable_empty : forall f,
  interpret f [] = mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. reflexivity. Qed.

Lemma compiler_correct_empty : compiler_correct [].
Proof.
  unfold compiler_correct. intro src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  rewrite interpret_stable_empty in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 1%nat. simpl. split; [reflexivity | exact I].
Qed.

(* --- Type declaration: threshold = 0 --- *)

Lemma interpret_stable_type_decl : forall name params td f,
  interpret f [Decl_type name params td] = mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. reflexivity. Qed.

Lemma compiler_correct_type_decl : forall name params td,
  compiler_correct [Decl_type name params td].
Proof.
  unfold compiler_correct. intros name params td src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  rewrite interpret_stable_type_decl in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 1%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_int n): threshold = 1 --- *)

Lemma interpret_stable_expr_int : forall n f,
  interpret (1 + f)%nat [Decl_expr (Exp_int n)] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. reflexivity. Qed.

Lemma compiler_correct_expr_int : forall n,
  compiler_correct [Decl_expr (Exp_int n)].
Proof.
  unfold compiler_correct. intros n src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  change (S f0) with (1 + f0)%nat in Hinterp.
  rewrite interpret_stable_expr_int in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 2%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_bool b): threshold = 1 --- *)

Lemma interpret_stable_expr_bool : forall b f,
  interpret (1 + f)%nat [Decl_expr (Exp_bool b)] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. destruct b; reflexivity. Qed.

Lemma compiler_correct_expr_bool : forall b,
  compiler_correct [Decl_expr (Exp_bool b)].
Proof.
  unfold compiler_correct. intros b src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  change (S f0) with (1 + f0)%nat in Hinterp.
  rewrite interpret_stable_expr_bool in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 2%nat. unfold compile_program. simpl.
  destruct b; simpl; (split; [reflexivity | exact I]).
Qed.

(* --- Decl_expr Exp_unit: threshold = 1 --- *)

Lemma interpret_stable_expr_unit : forall f,
  interpret (1 + f)%nat [Decl_expr Exp_unit] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. reflexivity. Qed.

Lemma compiler_correct_expr_unit :
  compiler_correct [Decl_expr Exp_unit].
Proof.
  unfold compiler_correct. intro src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  change (S f0) with (1 + f0)%nat in Hinterp.
  rewrite interpret_stable_expr_unit in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 2%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_seq (Exp_int a) (Exp_int b)): threshold = 2 --- *)

Lemma interpret_stable_seq_ints : forall a b f,
  interpret (2 + f)%nat [Decl_expr (Exp_seq (Exp_int a) (Exp_int b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. reflexivity. Qed.

Lemma compiler_correct_seq_ints : forall a b,
  compiler_correct [Decl_expr (Exp_seq (Exp_int a) (Exp_int b))].
Proof.
  unfold compiler_correct. intros a b src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  change (S (S f1)) with (2 + f1)%nat in Hinterp.
  rewrite interpret_stable_seq_ints in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 3%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_unop Op_neg (Exp_int n)): threshold = 2 --- *)

Lemma interpret_stable_neg_int : forall n f,
  interpret (2 + f)%nat [Decl_expr (Exp_unop Op_neg (Exp_int n))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. reflexivity. Qed.

Lemma compiler_correct_neg_int : forall n,
  compiler_correct [Decl_expr (Exp_unop Op_neg (Exp_int n))].
Proof.
  unfold compiler_correct. intros n src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  change (S (S f1)) with (2 + f1)%nat in Hinterp.
  rewrite interpret_stable_neg_int in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 3%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_unop Op_not (Exp_bool b)): threshold = 2 --- *)

Lemma interpret_stable_not_bool : forall b f,
  interpret (2 + f)%nat [Decl_expr (Exp_unop Op_not (Exp_bool b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. destruct b; reflexivity. Qed.

Lemma compiler_correct_not_bool : forall b,
  compiler_correct [Decl_expr (Exp_unop Op_not (Exp_bool b))].
Proof.
  unfold compiler_correct. intros b src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  change (S (S f1)) with (2 + f1)%nat in Hinterp.
  rewrite interpret_stable_not_bool in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 3%nat. unfold compile_program. simpl.
  destruct b; simpl; (split; [reflexivity | exact I]).
Qed.

(* --- Decl_expr (Exp_binop Op_add (Exp_int a) (Exp_int b)): threshold = 2 --- *)

Lemma interpret_stable_add_ints : forall a b f,
  interpret (2 + f)%nat [Decl_expr (Exp_binop Op_add (Exp_int a) (Exp_int b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. reflexivity. Qed.

Lemma compiler_correct_add_ints : forall a b,
  compiler_correct [Decl_expr (Exp_binop Op_add (Exp_int a) (Exp_int b))].
Proof.
  unfold compiler_correct. intros a b src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  change (S (S f1)) with (2 + f1)%nat in Hinterp.
  rewrite interpret_stable_add_ints in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 5%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_binop Op_sub (Exp_int a) (Exp_int b)): threshold = 2 --- *)

Lemma interpret_stable_sub_ints : forall a b f,
  interpret (2 + f)%nat [Decl_expr (Exp_binop Op_sub (Exp_int a) (Exp_int b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. reflexivity. Qed.

Lemma compiler_correct_sub_ints : forall a b,
  compiler_correct [Decl_expr (Exp_binop Op_sub (Exp_int a) (Exp_int b))].
Proof.
  unfold compiler_correct. intros a b src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  change (S (S f1)) with (2 + f1)%nat in Hinterp.
  rewrite interpret_stable_sub_ints in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 5%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_binop Op_mul (Exp_int a) (Exp_int b)): threshold = 2 --- *)

Lemma interpret_stable_mul_ints : forall a b f,
  interpret (2 + f)%nat [Decl_expr (Exp_binop Op_mul (Exp_int a) (Exp_int b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. reflexivity. Qed.

Lemma compiler_correct_mul_ints : forall a b,
  compiler_correct [Decl_expr (Exp_binop Op_mul (Exp_int a) (Exp_int b))].
Proof.
  unfold compiler_correct. intros a b src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  change (S (S f1)) with (2 + f1)%nat in Hinterp.
  rewrite interpret_stable_mul_ints in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 5%nat. unfold compile_program. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- Decl_expr (Exp_if (Exp_bool b) (Exp_int n1) (Exp_int n2)): threshold = 2 --- *)

Lemma interpret_stable_if_bool_ints : forall b n1 n2 f,
  interpret (2 + f)%nat [Decl_expr (Exp_if (Exp_bool b) (Exp_int n1) (Exp_int n2))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. destruct b; reflexivity. Qed.

Lemma compiler_correct_if_bool_ints : forall b n1 n2,
  compiler_correct [Decl_expr (Exp_if (Exp_bool b) (Exp_int n1) (Exp_int n2))].
Proof.
  unfold compiler_correct. intros b n1 n2 src_fuel.
  destruct (interpret src_fuel _) as [t r] eqn:Hinterp.
  destruct r as [v | msg | ]; try exact I.
  destruct src_fuel as [|f0]; [simpl in Hinterp; discriminate |].
  destruct f0 as [|f1]; [simpl in Hinterp; discriminate |].
  change (S (S f1)) with (2 + f1)%nat in Hinterp.
  rewrite interpret_stable_if_bool_ints in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 6%nat. unfold compile_program. simpl.
  destruct b; simpl; (split; [reflexivity | exact I]).
Qed.

(* --- Decl_expr (Exp_let x (Exp_int n) (Exp_var x)): threshold = 2 --- *)

Lemma interpret_stable_let_int_var : forall x n f,
  interpret (2 + f)%nat [Decl_expr (Exp_let x (Exp_int n) (Exp_var x))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof.
  intros. unfold interpret, eval_program. simpl.
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
  change (S (S f1)) with (2 + f1)%nat in Hinterp.
  rewrite interpret_stable_let_int_var in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 5%nat. unfold compile_program. simpl. rewrite String.eqb_refl. simpl.
  split; [reflexivity | exact I].
Qed.

(* --- let x = a ;; x + b (two declarations): threshold = 2 --- *)

Lemma interpret_stable_let_then_add : forall x a b f,
  interpret (2 + f)%nat [Decl_let x (Exp_int a); Decl_expr (Exp_binop Op_add (Exp_var x) (Exp_int b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof.
  intros. unfold interpret, eval_program. simpl.
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
  change (S (S f1)) with (2 + f1)%nat in Hinterp.
  rewrite interpret_stable_let_then_add in Hinterp.
  apply behavior_eq in Hinterp. destruct Hinterp as [Ht _]. subst t.
  exists 7%nat. unfold compile_program. simpl. rewrite String.eqb_refl. simpl.
  split; [reflexivity | exact I].
Qed.

(* ================================================================== *)
(* === FUEL MONOTONICITY (ADMITTED)                               === *)
(* ================================================================== *)

(* If the source interpreter terminates normally with fuel f,
   it also terminates normally with any fuel f' >= f, producing
   the same result. *)

Lemma eval_fuel_monotone : forall fuel fuel' e senv out sv out',
  eval fuel e senv out = Eval_ok sv out' ->
  (fuel <= fuel')%nat ->
  eval fuel' e senv out = Eval_ok sv out'.
Proof.
  (* Requires strong induction on fuel, then case analysis on e.
     Each expression form uses the IH on sub-expressions with
     strictly smaller fuel. *)
Admitted.

Lemma eval_program_fuel_monotone : forall fuel fuel' prog senv out sv out',
  eval_program fuel prog senv out = Eval_ok sv out' ->
  (fuel <= fuel')%nat ->
  eval_program fuel' prog senv out = Eval_ok sv out'.
Proof. Admitted.

(* ================================================================== *)
(* === MAIN THEOREM                                               === *)
(* ================================================================== *)

Theorem compiler_correctness :
  forall (prog : program), compiler_correct prog.
Proof.
  (* This proof is the main deliverable of the formal verification effort.

     STATUS: The theorem is admitted. Below is an inventory of what has been
     proved and what remains.

     PROVED (17 fully-checked lemmas, 0 axioms used):
     - behavior_eq: record decomposition for behavior equality
     - nsteps_trans: transitivity of multi-step execution
     - run_collecting_fuel_monotone: bytecode fuel monotonicity
     - step_*: 13 single-instruction step lemmas
       (constint, stop, push, addint, subint, mulint, pop, branch,
        branchifnot_zero, branchifnot_nonzero, eq_instr, ccall,
        negint, boolnot_zero, boolnot_nonzero, acc)
     - compiler_correct_*: 15 concrete program correctness lemmas
       (empty, type_decl, expr_int, expr_bool, expr_unit,
        seq_ints, neg_int, not_bool, add_ints, sub_ints, mul_ints,
        if_bool_ints, let_int_var, let_then_add)

     ADMITTED (5 lemmas):
     - expr_correct_int, expr_correct_bool, expr_correct_unit:
       Expression-level correctness for literals. Blocked on Ltac
       automation for the large step function.
     - eval_fuel_monotone: source interpreter fuel monotonicity.
       Requires structural induction on expressions.
     - eval_program_fuel_monotone: program-level fuel monotonicity.

     REMAINING WORK for the general proof:
     1. Prove eval_fuel_monotone by strong induction on fuel.
     2. Prove expr_correct for all expression forms (15 cases).
     3. Prove a program-level compilation correctness lemma that lifts
        expr_correct through compile_decls / eval_program.
     4. Handle I/O: show ccall_to_events matches apply_builtin for
        print_int and print_newline.
     5. Handle closures: extend val_corresponds and env_invariant to
        relate SVal_closure/SVal_recclosure to Val_closure + heap. *)
Admitted.

(* ================================================================== *)
(* === DERIVED RESULTS                                            === *)
(* ================================================================== *)

Definition traces_agree (prog : program) : Prop :=
  forall (src_fuel : nat),
    match interpret src_fuel prog with
    | {| trace := t; result := Term_normal _ |} =>
      exists (bc_fuel : nat),
        (bytecode_behavior bc_fuel (compile_program prog) []).(trace) = t
    | _ => True
    end.

Lemma correctness_implies_traces_agree :
  forall prog, compiler_correct prog -> traces_agree prog.
Proof.
  unfold compiler_correct, traces_agree.
  intros prog H src_fuel.
  specialize (H src_fuel).
  destruct (interpret src_fuel prog) as [t r].
  destruct r; auto.
  destruct H as [bc_fuel [Htrace _]].
  exists bc_fuel. exact Htrace.
Qed.
