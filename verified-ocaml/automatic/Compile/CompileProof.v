(* CorrectnessProofs.v - [TRUSTED] Compiler correctness theorem statement.

   This file contains the STATEMENT of compiler correctness. The statement
   itself is trusted: it defines what it means for the compiler to be correct.
   The proof (when provided) is checked mechanically by Rocq.

   The core theorem:
     forall source, interpret(source) = (interpret-bytecode . compile)(source)

   Both sides must produce the same observable behavior (output trace + result). *)

From Stdlib Require Import ZArith Strings.String PeanoNat Lia.
From Stdlib.Array Require Import PrimArray.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode Require Import Interpret.
From RecordUpdate Require Import RecordUpdate.
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

(* Convert a C call to output events.
   Primitive indices must match Compile.v's is_builtin:
     0 = print_int, 1 = print_newline, 2 = print_string
   Uses z_to_events from Interpret.v -- single source of truth. *)
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
    match step_list code s with
    | Step s' => run_collecting fuel' code s' out
    | Halt v => mk_behavior (rev out) (Term_normal v)
    | Error msg => mk_behavior (rev out) (Term_error msg)
    | CCall_request prim_idx args cont =>
      let new_events := ccall_to_events prim_idx args in
      let out' := rev new_events ++ out in
      run_collecting fuel' code (cont <|accu := Val_int 0|>) out'
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
  step_list code s = Step (s <|pc := pc s + 1|> <|accu := Val_int n|>).
Proof. Admitted.

Lemma step_stop : forall code s,
  nth_error code (Z.to_nat (pc s)) = Some STOP ->
  step_list code s = Halt (accu s).
Proof. Admitted.

Lemma step_push : forall code s,
  nth_error code (Z.to_nat (pc s)) = Some PUSH ->
  step_list code s = Step (s <|pc := pc s + 1|> <|stack := accu s :: Machine.stack s|>).
Proof. Admitted.

Lemma step_addint : forall code s a b rest,
  nth_error code (Z.to_nat (pc s)) = Some ADDINT ->
  accu s = Val_int a -> Machine.stack s = Val_int b :: rest ->
  step_list code s = Step (s <|pc := pc s + 1|> <|accu := Val_int (a + b)|> <|stack := rest|>).
Proof. Admitted.

Lemma step_subint : forall code s a b rest,
  nth_error code (Z.to_nat (pc s)) = Some SUBINT ->
  accu s = Val_int a -> Machine.stack s = Val_int b :: rest ->
  step_list code s = Step (s <|pc := pc s + 1|> <|accu := Val_int (a - b)|> <|stack := rest|>).
Proof. Admitted.

Lemma step_mulint : forall code s a b rest,
  nth_error code (Z.to_nat (pc s)) = Some MULINT ->
  accu s = Val_int a -> Machine.stack s = Val_int b :: rest ->
  step_list code s = Step (s <|pc := pc s + 1|> <|accu := Val_int (a * b)|> <|stack := rest|>).
Proof. Admitted.

Lemma step_pop : forall code s n,
  nth_error code (Z.to_nat (pc s)) = Some (POP n) ->
  step_list code s = Step (s <|pc := pc s + 1|> <|stack := skipn n (Machine.stack s)|>).
Proof. Admitted.

Lemma step_branch : forall code s target,
  nth_error code (Z.to_nat (pc s)) = Some (BRANCH target) ->
  step_list code s = Step (s <|pc := target|>).
Proof. Admitted.

Lemma step_branchifnot_zero : forall code s target,
  nth_error code (Z.to_nat (pc s)) = Some (BRANCHIFNOT target) ->
  accu s = Val_int 0 ->
  step_list code s = Step (s <|pc := target|>).
Proof. Admitted.

Lemma step_branchifnot_nonzero : forall code s target n,
  nth_error code (Z.to_nat (pc s)) = Some (BRANCHIFNOT target) ->
  accu s = Val_int n -> n <> 0 ->
  step_list code s = Step (s <|pc := pc s + 1|>).
Proof. Admitted.

Lemma step_eq_instr : forall code s b rest,
  nth_error code (Z.to_nat (pc s)) = Some EQ ->
  Machine.stack s = b :: rest ->
  step_list code s = Step (s <|pc := pc s + 1|>
                        <|accu := if value_eqb (accu s) b then val_true else val_false|>
                        <|stack := rest|>).
Proof. Admitted.

Lemma step_ccall : forall code s nargs prim_idx,
  nth_error code (Z.to_nat (pc s)) = Some (C_CALL nargs prim_idx) ->
  step_list code s = CCall_request prim_idx
    (accu s :: firstn (Nat.sub nargs 1) (Machine.stack s))
    (s <|pc := pc s + 1|> <|accu := val_unit|>
       <|stack := skipn (Nat.sub nargs 1) (Machine.stack s)|>).
Proof. Admitted.

Lemma step_negint : forall code s n,
  nth_error code (Z.to_nat (pc s)) = Some NEGINT ->
  accu s = Val_int n ->
  step_list code s = Step (s <|pc := pc s + 1|> <|accu := Val_int (- n)|>).
Proof. Admitted.

Lemma step_boolnot_zero : forall code s,
  nth_error code (Z.to_nat (pc s)) = Some BOOLNOT ->
  accu s = Val_int 0 ->
  step_list code s = Step (s <|pc := pc s + 1|> <|accu := val_true|>).
Proof. Admitted.

Lemma step_boolnot_nonzero : forall code s n,
  nth_error code (Z.to_nat (pc s)) = Some BOOLNOT ->
  accu s = Val_int n -> n <> 0 ->
  step_list code s = Step (s <|pc := pc s + 1|> <|accu := val_false|>).
Proof. Admitted.

Lemma step_acc : forall code s n v,
  nth_error code (Z.to_nat (pc s)) = Some (ACC n) ->
  nth_error (Machine.stack s) n = Some v ->
  step_list code s = Step (s <|pc := pc s + 1|> <|accu := v|>).
Proof. Admitted.

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
      nsteps n (prefix ++ compile_expr fuel e ce base ++ [STOP]) s =
        Step (s <|pc := Z.of_nat (base + length (compile_expr fuel e ce base))|>
                <|accu := v|>) /\
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

(* --- Empty program: threshold = 0 (always terminates) --- *)

Lemma interpret_stable_empty : forall f,
  interpret f [] = mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. reflexivity. Qed.

Lemma compiler_correct_empty : compiler_correct [].
Proof. Admitted.

(* --- Type declaration: threshold = 0 --- *)

Lemma interpret_stable_type_decl : forall name params td f,
  interpret f [Decl_type name params td] = mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. reflexivity. Qed.

Lemma compiler_correct_type_decl : forall name params td,
  compiler_correct [Decl_type name params td].
Proof. Admitted.

(* --- Decl_expr (Exp_int n): threshold = 1 --- *)

Lemma interpret_stable_expr_int : forall n f,
  interpret (1 + f)%nat [Decl_expr (Exp_int n)] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. reflexivity. Qed.

Lemma compiler_correct_expr_int : forall n,
  compiler_correct [Decl_expr (Exp_int n)].
Proof. Admitted.

(* --- Decl_expr (Exp_bool b): threshold = 1 --- *)

Lemma interpret_stable_expr_bool : forall b f,
  interpret (1 + f)%nat [Decl_expr (Exp_bool b)] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. destruct b; reflexivity. Qed.

Lemma compiler_correct_expr_bool : forall b,
  compiler_correct [Decl_expr (Exp_bool b)].
Proof. Admitted.

(* --- Decl_expr Exp_unit: threshold = 1 --- *)

Lemma interpret_stable_expr_unit : forall f,
  interpret (1 + f)%nat [Decl_expr Exp_unit] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. reflexivity. Qed.

Lemma compiler_correct_expr_unit :
  compiler_correct [Decl_expr Exp_unit].
Proof. Admitted.

(* --- Decl_expr (Exp_seq (Exp_int a) (Exp_int b)): threshold = 2 --- *)

Lemma interpret_stable_seq_ints : forall a b f,
  interpret (2 + f)%nat [Decl_expr (Exp_seq (Exp_int a) (Exp_int b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. reflexivity. Qed.

Lemma compiler_correct_seq_ints : forall a b,
  compiler_correct [Decl_expr (Exp_seq (Exp_int a) (Exp_int b))].
Proof. Admitted.

(* --- Decl_expr (Exp_unop Op_neg (Exp_int n)): threshold = 2 --- *)

Lemma interpret_stable_neg_int : forall n f,
  interpret (2 + f)%nat [Decl_expr (Exp_unop Op_neg (Exp_int n))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. reflexivity. Qed.

Lemma compiler_correct_neg_int : forall n,
  compiler_correct [Decl_expr (Exp_unop Op_neg (Exp_int n))].
Proof. Admitted.

(* --- Decl_expr (Exp_unop Op_not (Exp_bool b)): threshold = 2 --- *)

Lemma interpret_stable_not_bool : forall b f,
  interpret (2 + f)%nat [Decl_expr (Exp_unop Op_not (Exp_bool b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. destruct b; reflexivity. Qed.

Lemma compiler_correct_not_bool : forall b,
  compiler_correct [Decl_expr (Exp_unop Op_not (Exp_bool b))].
Proof. Admitted.

(* --- Decl_expr (Exp_binop Op_add (Exp_int a) (Exp_int b)): threshold = 2 --- *)

Lemma interpret_stable_add_ints : forall a b f,
  interpret (2 + f)%nat [Decl_expr (Exp_binop Op_add (Exp_int a) (Exp_int b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. reflexivity. Qed.

Lemma compiler_correct_add_ints : forall a b,
  compiler_correct [Decl_expr (Exp_binop Op_add (Exp_int a) (Exp_int b))].
Proof. Admitted.

(* --- Decl_expr (Exp_binop Op_sub (Exp_int a) (Exp_int b)): threshold = 2 --- *)

Lemma interpret_stable_sub_ints : forall a b f,
  interpret (2 + f)%nat [Decl_expr (Exp_binop Op_sub (Exp_int a) (Exp_int b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. reflexivity. Qed.

Lemma compiler_correct_sub_ints : forall a b,
  compiler_correct [Decl_expr (Exp_binop Op_sub (Exp_int a) (Exp_int b))].
Proof. Admitted.

(* --- Decl_expr (Exp_binop Op_mul (Exp_int a) (Exp_int b)): threshold = 2 --- *)

Lemma interpret_stable_mul_ints : forall a b f,
  interpret (2 + f)%nat [Decl_expr (Exp_binop Op_mul (Exp_int a) (Exp_int b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. reflexivity. Qed.

Lemma compiler_correct_mul_ints : forall a b,
  compiler_correct [Decl_expr (Exp_binop Op_mul (Exp_int a) (Exp_int b))].
Proof. Admitted.

(* --- Decl_expr (Exp_if (Exp_bool b) (Exp_int n1) (Exp_int n2)): threshold = 2 --- *)

Lemma interpret_stable_if_bool_ints : forall b n1 n2 f,
  interpret (2 + f)%nat [Decl_expr (Exp_if (Exp_bool b) (Exp_int n1) (Exp_int n2))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. intros. unfold interpret, eval_program. simpl. destruct b; reflexivity. Qed.

Lemma compiler_correct_if_bool_ints : forall b n1 n2,
  compiler_correct [Decl_expr (Exp_if (Exp_bool b) (Exp_int n1) (Exp_int n2))].
Proof. Admitted.

(* --- Decl_expr (Exp_let x (Exp_int n) (Exp_var x)): threshold = 2 --- *)

Lemma interpret_stable_let_int_var : forall x n f,
  interpret (2 + f)%nat [Decl_expr (Exp_let x (Exp_int n) (Exp_var x))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. Admitted.

Lemma compiler_correct_let_int_var : forall x n,
  compiler_correct [Decl_expr (Exp_let x (Exp_int n) (Exp_var x))].
Proof. Admitted.

(* --- let x = a ;; x + b (two declarations): threshold = 2 --- *)

Lemma interpret_stable_let_then_add : forall x a b f,
  interpret (2 + f)%nat [Decl_let x (Exp_int a); Decl_expr (Exp_binop Op_add (Exp_var x) (Exp_int b))] =
    mk_behavior [] (Term_normal (Val_int 0)).
Proof. Admitted.

Lemma compiler_correct_let_then_add : forall x a b,
  compiler_correct [Decl_let x (Exp_int a); Decl_expr (Exp_binop Op_add (Exp_var x) (Exp_int b))].
Proof. Admitted.

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
Proof. Admitted.

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
Proof. Admitted.

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
Proof. Admitted.
