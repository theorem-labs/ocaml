(* SourceInterp.v - [UNTRUSTED] Source-level interpreter for OCaml AST.
   Directly evaluates Syntax.v expressions. Serves as the specification
   of what programs mean. Validated by PBT against ocamlrun.

   This interpreter is untrusted: the correctness theorem in Correctness.v
   states that this interpreter and the bytecode interpreter agree. The
   theorem's STATEMENT is trusted; its proof (checked by Rocq) is not. *)

From Stdlib Require Import ZArith Bool PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From OCamlInterp.Trusted.Bytecode Require Import Value.
From OCamlInterp.Trusted Require Import Observable.
From OCamlInterp.SemiTrusted Require Import Syntax.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(* === Source-level values === *)

(* Built-in function identifiers *)
Inductive builtin : Type :=
  | Bi_print_int
  | Bi_print_string
  | Bi_print_newline
  | Bi_print_char
  | Bi_compare
  | Bi_fst
  | Bi_snd.

Inductive svalue : Type :=
  | SVal_int    : Z -> svalue
  | SVal_bool   : bool -> svalue
  | SVal_unit   : svalue
  | SVal_tuple  : list svalue -> svalue
  | SVal_constr : ident -> option svalue -> svalue
  | SVal_closure : ident -> expr -> env -> svalue
  | SVal_recclosure : ident -> ident -> expr -> env -> svalue
  | SVal_builtin : builtin -> svalue
with env : Type :=
  | Env_nil  : env
  | Env_cons : ident -> svalue -> env -> env.

Fixpoint env_lookup (e : env) (x : ident) : option svalue :=
  match e with
  | Env_nil => None
  | Env_cons y v rest =>
    if String.eqb x y then Some v else env_lookup rest x
  end.

Definition env_extend (e : env) (x : ident) (v : svalue) : env :=
  Env_cons x v e.

Fixpoint env_append (e1 e2 : env) : env :=
  match e1 with
  | Env_nil => e2
  | Env_cons x v rest => Env_cons x v (env_append rest e2)
  end.

(* === Pattern matching === *)

Fixpoint match_pattern (p : pattern) (v : svalue) : option env :=
  match p, v with
  | Pat_wild, _ => Some Env_nil
  | Pat_var x, _ => Some (Env_cons x v Env_nil)
  | Pat_int n, SVal_int m => if Z.eqb n m then Some Env_nil else None
  | Pat_bool b, SVal_bool c => if Bool.eqb b c then Some Env_nil else None
  | Pat_unit, SVal_unit => Some Env_nil
  | Pat_constr c None, SVal_constr d None =>
    if String.eqb c d then Some Env_nil else None
  | Pat_constr c (Some p'), SVal_constr d (Some v') =>
    if String.eqb c d then match_pattern p' v' else None
  | Pat_tuple ps, SVal_tuple vs =>
    if Nat.eqb (List.length ps) (List.length vs) then
      (fix match_list (ps : list pattern) (vs : list svalue) : option env :=
        match ps, vs with
        | [], [] => Some Env_nil
        | p1 :: pr, v1 :: vr =>
          match match_pattern p1 v1, match_list pr vr with
          | Some e1, Some e2 => Some (env_append e1 e2)
          | _, _ => None
          end
        | _, _ => None
        end) ps vs
    else None
  | _, _ => None
  end.

Fixpoint try_cases (cases : list (pattern * expr)) (v : svalue) :
    option (expr * env) :=
  match cases with
  | [] => None
  | (p, body) :: rest =>
    match match_pattern p v with
    | Some bindings => Some (body, bindings)
    | None => try_cases rest v
    end
  end.

(* === Evaluation result === *)

(* Output is threaded as a reversed list of events *)
Inductive eval_result : Type :=
  | Eval_ok      : svalue -> list event -> eval_result
  | Eval_err     : string -> list event -> eval_result
  | Eval_timeout : list event -> eval_result.

(* === Binary/unary operations === *)

Definition eval_binop (op : binop) (v1 v2 : svalue) : option svalue :=
  match op, v1, v2 with
  | Op_add, SVal_int a, SVal_int b => Some (SVal_int (a + b))
  | Op_sub, SVal_int a, SVal_int b => Some (SVal_int (a - b))
  | Op_mul, SVal_int a, SVal_int b => Some (SVal_int (a * b))
  | Op_div, SVal_int a, SVal_int b =>
    if Z.eqb b 0 then None else Some (SVal_int (Z.quot a b))
  | Op_mod, SVal_int a, SVal_int b =>
    if Z.eqb b 0 then None else Some (SVal_int (Z.rem a b))
  | Op_eq, SVal_int a, SVal_int b => Some (SVal_bool (Z.eqb a b))
  | Op_neq, SVal_int a, SVal_int b => Some (SVal_bool (negb (Z.eqb a b)))
  | Op_lt, SVal_int a, SVal_int b => Some (SVal_bool (a <? b))
  | Op_le, SVal_int a, SVal_int b => Some (SVal_bool (a <=? b))
  | Op_gt, SVal_int a, SVal_int b => Some (SVal_bool (a >? b))
  | Op_ge, SVal_int a, SVal_int b => Some (SVal_bool (a >=? b))
  | Op_and, SVal_bool a, SVal_bool b => Some (SVal_bool (a && b))
  | Op_or, SVal_bool a, SVal_bool b => Some (SVal_bool (a || b))
  | _, _, _ => None
  end.

Definition eval_unop (op : unop) (v : svalue) : option svalue :=
  match op, v with
  | Op_neg, SVal_int n => Some (SVal_int (- n))
  | Op_not, SVal_bool b => Some (SVal_bool (negb b))
  | _, _ => None
  end.

(* === Integer to character events (for print_int) === *)

Fixpoint nat_to_events_aux (fuel n : nat) (acc : list event) : list event :=
  match fuel with
  | O => acc
  | S fuel' =>
    let digit := Out_char (Z.of_nat (48 + Nat.modulo n 10)) in
    let rest := Nat.div n 10 in
    if Nat.eqb rest 0 then digit :: acc
    else nat_to_events_aux fuel' rest (digit :: acc)
  end.

Definition z_to_events (z : Z) : list event :=
  match z with
  | Z0 => [Out_char 48]  (* "0" *)
  | Zpos p => nat_to_events_aux 20 (Pos.to_nat p) []
  | Zneg p => Out_char 45 :: nat_to_events_aux 20 (Pos.to_nat p) []  (* "-" prefix *)
  end.

(* Apply a builtin function, returning result value and new output *)
Definition apply_builtin (b : builtin) (arg : svalue) (out : list event) :
    option (svalue * list event) :=
  match b, arg with
  | Bi_print_int, SVal_int n =>
    Some (SVal_unit, rev (z_to_events n) ++ out)
  | Bi_print_newline, SVal_unit =>
    Some (SVal_unit, Out_char 10 :: out)
  | Bi_print_char, SVal_int c =>
    Some (SVal_unit, Out_char c :: out)
  | Bi_compare, SVal_int a =>
    (* compare returns a curried function: compare a b *)
    (* For now, return a closure-like value; handle in app *)
    None  (* handled specially in eval *)
  | Bi_fst, SVal_tuple (a :: _) => Some (a, out)
  | Bi_snd, SVal_tuple (_ :: b :: _) => Some (b, out)
  | _, _ => None
  end.

(* Standard library environment *)
Definition stdlib_env : env :=
  Env_cons "print_int" (SVal_builtin Bi_print_int)
  (Env_cons "print_string" (SVal_builtin Bi_print_string)
  (Env_cons "print_newline" (SVal_builtin Bi_print_newline)
  (Env_cons "print_char" (SVal_builtin Bi_print_char)
  (Env_cons "compare" (SVal_builtin Bi_compare)
  (Env_cons "fst" (SVal_builtin Bi_fst)
  (Env_cons "snd" (SVal_builtin Bi_snd)
  Env_nil)))))).

(* === Main evaluation function, structurally decreasing on fuel === *)

Fixpoint eval (fuel : nat) (e : expr) (env0 : env) (out : list event) : eval_result :=
  match fuel with
  | O => Eval_timeout out
  | S fuel' =>
  match e with
  | Exp_int n => Eval_ok (SVal_int n) out
  | Exp_bool b => Eval_ok (SVal_bool b) out
  | Exp_unit => Eval_ok SVal_unit out

  | Exp_var x =>
    match env_lookup env0 x with
    | Some v => Eval_ok v out
    | None => Eval_err "unbound variable" out
    end

  | Exp_binop op e1 e2 =>
    match eval fuel' e1 env0 out with
    | Eval_ok v1 out1 =>
      match eval fuel' e2 env0 out1 with
      | Eval_ok v2 out2 =>
        match eval_binop op v1 v2 with
        | Some v => Eval_ok v out2
        | None => Eval_err "binop type error" out2
        end
      | other => other
      end
    | other => other
    end

  | Exp_unop op e1 =>
    match eval fuel' e1 env0 out with
    | Eval_ok v1 out1 =>
      match eval_unop op v1 with
      | Some v => Eval_ok v out1
      | None => Eval_err "unop type error" out1
      end
    | other => other
    end

  | Exp_if cond then_e else_e =>
    match eval fuel' cond env0 out with
    | Eval_ok (SVal_bool true) out1 => eval fuel' then_e env0 out1
    | Eval_ok (SVal_bool false) out1 => eval fuel' else_e env0 out1
    | Eval_ok _ out1 => Eval_err "if: non-bool condition" out1
    | other => other
    end

  | Exp_let x e1 e2 =>
    match eval fuel' e1 env0 out with
    | Eval_ok v1 out1 => eval fuel' e2 (env_extend env0 x v1) out1
    | other => other
    end

  | Exp_letrec f e1 e2 =>
    match e1 with
    | Exp_fun param body =>
      let clos := SVal_recclosure f param body env0 in
      eval fuel' e2 (env_extend env0 f clos) out
    | _ =>
      match eval fuel' e1 env0 out with
      | Eval_ok v1 out1 => eval fuel' e2 (env_extend env0 f v1) out1
      | other => other
      end
    end

  | Exp_fun x body =>
    Eval_ok (SVal_closure x body env0) out

  | Exp_app func arg =>
    match eval fuel' func env0 out with
    | Eval_ok fv out1 =>
      match eval fuel' arg env0 out1 with
      | Eval_ok av out2 =>
        match fv with
        | SVal_closure param body cenv =>
          eval fuel' body (env_extend cenv param av) out2
        | SVal_recclosure name param body cenv =>
          let cenv' := env_extend cenv name fv in
          eval fuel' body (env_extend cenv' param av) out2
        | SVal_builtin b =>
          match apply_builtin b av out2 with
          | Some (rv, out3) => Eval_ok rv out3
          | None => Eval_err "builtin type error" out2
          end
        | _ => Eval_err "application of non-function" out2
        end
      | other => other
      end
    | other => other
    end

  | Exp_tuple es =>
    (fix eval_list (fuel0 : nat) (es : list expr) (acc : list svalue) (out0 : list event) : eval_result :=
      match es with
      | [] => Eval_ok (SVal_tuple (rev acc)) out0
      | e1 :: rest =>
        match eval fuel0 e1 env0 out0 with
        | Eval_ok v out1 => eval_list fuel0 rest (v :: acc) out1
        | other => other
        end
      end) fuel' es [] out

  | Exp_constr c None => Eval_ok (SVal_constr c None) out
  | Exp_constr c (Some e1) =>
    match eval fuel' e1 env0 out with
    | Eval_ok v out1 => Eval_ok (SVal_constr c (Some v)) out1
    | other => other
    end

  | Exp_match scrut cases =>
    match eval fuel' scrut env0 out with
    | Eval_ok sv out1 =>
      match try_cases cases sv with
      | Some (body, bindings) =>
        eval fuel' body (env_append bindings env0) out1
      | None => Eval_err "match failure" out1
      end
    | other => other
    end

  | Exp_seq e1 e2 =>
    match eval fuel' e1 env0 out with
    | Eval_ok _ out1 => eval fuel' e2 env0 out1
    | other => other
    end

  end
  end.

(* === Top-level program evaluation === *)

Fixpoint eval_program (fuel : nat) (prog : program) (env0 : env) (out : list event) :
    eval_result :=
  match prog with
  | [] => Eval_ok SVal_unit out
  | d :: rest =>
    match d with
    | Decl_let x e =>
      match eval fuel e env0 out with
      | Eval_ok v out' => eval_program fuel rest (env_extend env0 x v) out'
      | other => other
      end
    | Decl_letrec f e =>
      match e with
      | Exp_fun param body =>
        let clos := SVal_recclosure f param body env0 in
        eval_program fuel rest (env_extend env0 f clos) out
      | _ =>
        match eval fuel e env0 out with
        | Eval_ok v out' => eval_program fuel rest (env_extend env0 f v) out'
        | other => other
        end
      end
    | Decl_type _ _ _ =>
      eval_program fuel rest env0 out
    | Decl_expr e =>
      match eval fuel e env0 out with
      | Eval_ok _ out' => eval_program fuel rest env0 out'
      | other => other
      end
    end
  end.

(* Entry point *)
Definition interpret (fuel : nat) (prog : program) : behavior :=
  match eval_program fuel prog stdlib_env [] with
  | Eval_ok _ out => mk_behavior (rev out) (Term_normal (Val_int 0))
  | Eval_err msg out => mk_behavior (rev out) (Term_error msg)
  | Eval_timeout out => mk_behavior (rev out) Term_timeout
  end.
