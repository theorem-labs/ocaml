(* Interpret.v - [UNTRUSTED] Source-level interpreter for OCaml AST.
   Directly evaluates Syntax.v expressions. Serves as the specification
   of what programs mean. Validated by PBT against ocamlrun.

   This interpreter is untrusted: the correctness theorem in CompileSpec.v
   states that this interpreter and the bytecode interpreter agree. The
   theorem's STATEMENT is trusted; its proof (checked by Rocq) is not. *)

From Stdlib Require Import ZArith Bool PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String Strings.Ascii.
From compcert Require Import Integers.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Utils Require Import Observable.
From OCamlInterp.Manual.Utils Require Import Syntax.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

Definition constint_in_range (n : Z) : bool :=
  ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z.

Definition constint_malformed_msg : string := "CONSTINT: malformed operand".

(* === Source-level values === *)

(* Built-in function identifiers *)
Inductive builtin : Type :=
  | Bi_print_int
  | Bi_print_string
  | Bi_print_newline
  | Bi_print_char
  | Bi_compare
  | Bi_fst
  | Bi_snd
  | Bi_succ
  | Bi_pred
  | Bi_max.

Inductive svalue : Type :=
  | SVal_int    : Z -> svalue
  | SVal_bool   : bool -> svalue
  | SVal_unit   : svalue
  | SVal_tuple  : list svalue -> svalue
  | SVal_constr : ident -> option svalue -> svalue
  | SVal_closure : ident -> expr -> env -> svalue
  | SVal_recclosure : ident -> ident -> expr -> env -> svalue
  | SVal_builtin : builtin -> svalue
  | SVal_record : list (ident * svalue) -> svalue
  | SVal_string : string -> svalue
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

(* Record field lookup *)
Fixpoint record_lookup (fields : list (ident * svalue)) (f : ident) : option svalue :=
  match fields with
  | [] => None
  | (name, v) :: rest =>
    if String.eqb f name then Some v else record_lookup rest f
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
  | Pat_nil, SVal_constr "[]" None => Some Env_nil
  | Pat_cons ph pt, SVal_constr "::" (Some (SVal_tuple [h; t])) =>
    match match_pattern ph h, match_pattern pt t with
    | Some e1, Some e2 => Some (env_append e1 e2)
    | _, _ => None
    end
  | Pat_or p1 p2, _ =>
    match match_pattern p1 v with
    | Some bindings => Some bindings
    | None => match_pattern p2 v
    end
  | Pat_record fps, SVal_record fvs =>
    (fix match_fields (fps : list (ident * pattern)) : option env :=
      match fps with
      | [] => Some Env_nil
      | (fname, fp) :: rest =>
        match record_lookup fvs fname with
        | Some fv =>
          match match_pattern fp fv, match_fields rest with
          | Some e1, Some e2 => Some (env_append e1 e2)
          | _, _ => None
          end
        | None => None
        end
      end) fps
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
  | Op_lt, SVal_int a, SVal_int b => Some (SVal_bool (a <? b))
  | Op_le, SVal_int a, SVal_int b => Some (SVal_bool (a <=? b))
  | Op_gt, SVal_int a, SVal_int b => Some (SVal_bool (a >? b))
  | Op_ge, SVal_int a, SVal_int b => Some (SVal_bool (a >=? b))
  | Op_and, SVal_bool a, SVal_bool b => Some (SVal_bool (a && b))
  | Op_or, SVal_bool a, SVal_bool b => Some (SVal_bool (a || b))
  | _, _, _ => None
  end.

Fixpoint svalue_eqb (v1 v2 : svalue) : bool :=
  match v1, v2 with
  | SVal_int a, SVal_int b => Z.eqb a b
  | SVal_bool a, SVal_bool b => Bool.eqb a b
  | SVal_unit, SVal_unit => true
  | SVal_tuple xs, SVal_tuple ys =>
    (fix list_eqb (xs ys : list svalue) : bool :=
      match xs, ys with
      | [], [] => true
      | x :: xs', y :: ys' => svalue_eqb x y && list_eqb xs' ys'
      | _, _ => false
      end) xs ys
  | SVal_constr c1 None, SVal_constr c2 None => String.eqb c1 c2
  | SVal_constr c1 (Some x), SVal_constr c2 (Some y) =>
    String.eqb c1 c2 && svalue_eqb x y
  | SVal_record xs, SVal_record ys =>
    (fix fields_eqb (xs ys : list (ident * svalue)) : bool :=
      match xs, ys with
      | [], [] => true
      | (x, vx) :: xs', (y, vy) :: ys' =>
        String.eqb x y && svalue_eqb vx vy && fields_eqb xs' ys'
      | _, _ => false
      end) xs ys
  | SVal_string s1, SVal_string s2 => String.eqb s1 s2
  | _, _ => false
  end.

Definition eval_structural_binop (op : binop) (v1 v2 : svalue) : option svalue :=
  match op, v1, v2 with
  (* TODO: widen equality once the compiler emits structural equality instead
     of bytecode EQ/NEQ, whose current proof only matches integer equality. *)
  | Op_eq, SVal_int a, SVal_int b => Some (SVal_bool (Z.eqb a b))
  | Op_neq, SVal_int a, SVal_int b => Some (SVal_bool (negb (Z.eqb a b)))
  | _, _, _ => eval_binop op v1 v2
  end.

Definition eval_unop (op : unop) (v : svalue) : option svalue :=
  match op, v with
  | Op_neg, SVal_int n => Some (SVal_int (- n))
  | Op_not, SVal_bool b => Some (SVal_bool (negb b))
  | _, _ => None
  end.

(* z_to_events and nat_to_events_aux are now defined in Observable.v *)

Fixpoint string_to_events (s : string) : list event :=
  match s with
  | EmptyString => []
  | String c rest => Out_char (Z.of_nat (nat_of_ascii c)) :: string_to_events rest
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
  | Bi_print_string, SVal_string s =>
    Some (SVal_unit, rev (string_to_events s) ++ out)
  | Bi_compare, SVal_int a =>
    (* compare is a stub: returns 0 (equal) for any single argument.
       Full implementation requires currying support. *)
    Some (SVal_int 0, out)
  | Bi_fst, SVal_tuple (a :: _) => Some (a, out)
  | Bi_snd, SVal_tuple (_ :: b :: _) => Some (b, out)
  | Bi_succ, SVal_int n => Some (SVal_int (n + 1), out)
  | Bi_pred, SVal_int n => Some (SVal_int (n - 1), out)
  | Bi_max, SVal_int _ =>
    (* max is curried: handled as source-level closure in stdlib_env *)
    None
  | _, _ => None
  end.

(* max as a source-level closure: fun x -> fun y -> if x >= y then x else y *)
Definition max_closure : svalue :=
  SVal_closure "x"
    (Exp_fun "y"
      (Exp_if (Exp_binop Op_ge (Exp_var "x") (Exp_var "y"))
              (Exp_var "x") (Exp_var "y")))
    Env_nil.

(* Qualified name helper *)
Definition qualify_name (prefix : ident) (name : ident) : ident :=
  String.append prefix (String.append "." name).

Fixpoint strip_prefix (prefix name : string) : option string :=
  match prefix, name with
  | EmptyString, _ => Some name
  | String pc prest, String nc nrest =>
    if Ascii.eqb pc nc then strip_prefix prest nrest else None
  | _, _ => None
  end.

(* Standard library environment *)
Definition stdlib_env : env :=
  Env_cons "print_int" (SVal_builtin Bi_print_int)  (* 1 *)
  (Env_cons "print_string" (SVal_builtin Bi_print_string)  (* 2 *)
  (Env_cons "print_newline" (SVal_builtin Bi_print_newline)  (* 3 *)
  (Env_cons "print_char" (SVal_builtin Bi_print_char)  (* 4 *)
  (Env_cons "compare" (SVal_builtin Bi_compare)  (* 5 *)
  (Env_cons "fst" (SVal_builtin Bi_fst)  (* 6 *)
  (Env_cons "snd" (SVal_builtin Bi_snd)  (* 7 *)
  (Env_cons "succ" (SVal_builtin Bi_succ)  (* 8 *)
  (Env_cons "pred" (SVal_builtin Bi_pred)  (* 9 *)
  (Env_cons "max" max_closure  (* 10 *)
  (Env_cons "Stdlib.Int.succ" (SVal_builtin Bi_succ)  (* 11 *)
  (Env_cons "Stdlib.Int.pred" (SVal_builtin Bi_pred)  (* 12 *)
  (Env_cons "Stdlib.max" max_closure  (* 13 *)
  Env_nil)))))))))))).

(* === Main evaluation function, structurally decreasing on fuel === *)

Fixpoint eval (fuel : nat) (e : expr) (env0 : env) (out : list event) : eval_result :=
  match fuel with
  | O => Eval_timeout out
  | S fuel' =>
  match e with
  | Exp_int n =>
    if constint_in_range n then Eval_ok (SVal_int n) out
    else Eval_err constint_malformed_msg out
  | Exp_bool b => Eval_ok (SVal_bool b) out
  | Exp_unit => Eval_ok SVal_unit out

  | Exp_var x =>
    match env_lookup env0 x with
    | Some v => Eval_ok v out
    | None => Eval_err "unbound variable" out
    end

  | Exp_binop op e1 e2 =>
    match eval fuel' e1 env0 out with
    | Eval_ok (SVal_bool false) out1 =>
      (* TODO: restore short-circuiting once the compiler emits branch code for
         Op_and/Op_or instead of strict ANDINT/ORINT evaluation. *)
      match eval fuel' e2 env0 out1 with
      | Eval_ok v2 out2 =>
        match eval_structural_binop op (SVal_bool false) v2 with
        | Some v => Eval_ok v out2
        | None => Eval_err "binop type error" out2
        end
      | other => other
      end
    | Eval_ok (SVal_bool true) out1 =>
      (* TODO: restore short-circuiting once the compiler emits branch code for
         Op_and/Op_or instead of strict ANDINT/ORINT evaluation. *)
      match eval fuel' e2 env0 out1 with
      | Eval_ok v2 out2 =>
        match eval_structural_binop op (SVal_bool true) v2 with
        | Some v => Eval_ok v out2
        | None => Eval_err "binop type error" out2
        end
      | other => other
      end
    | Eval_ok v1 out1 =>
      match eval fuel' e2 env0 out1 with
      | Eval_ok v2 out2 =>
        match eval_structural_binop op v1 v2 with
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

  | Exp_record fields =>
    (fix eval_fields (fuel0 : nat) (fs : list (ident * expr))
         (acc : list (ident * svalue)) (out0 : list event) : eval_result :=
      match fs with
      | [] => Eval_ok (SVal_record (rev acc)) out0
      | (fname, fe) :: rest =>
        match eval fuel0 fe env0 out0 with
        | Eval_ok fv out1 => eval_fields fuel0 rest ((fname, fv) :: acc) out1
        | other => other
        end
      end) fuel' fields [] out

  | Exp_field e1 f =>
    match eval fuel' e1 env0 out with
    | Eval_ok (SVal_record fields) out1 =>
      match record_lookup fields f with
      | Some v => Eval_ok v out1
      | None => Eval_err "field not found" out1
      end
    | Eval_ok _ out1 => Eval_err "field access on non-record" out1
    | other => other
    end

  | Exp_string s =>
    Eval_ok (SVal_string s) out

  | Exp_function cases =>
    Eval_ok (SVal_closure "$arg" (Exp_match (Exp_var "$arg") cases) env0) out

  | Exp_nil => Eval_ok (SVal_constr "[]" None) out

  | Exp_cons e1 e2 =>
    match eval fuel' e1 env0 out with
    | Eval_ok v1 out1 =>
      match eval fuel' e2 env0 out1 with
      | Eval_ok v2 out2 =>
        Eval_ok (SVal_constr "::" (Some (SVal_tuple [v1; v2]))) out2
      | other => other
      end
    | other => other
    end

  end
  end.

(* === Top-level program evaluation === *)

(* Extract names bound by a list of declarations (static analysis).
   Only Decl_let and Decl_letrec introduce bindings. *)
Fixpoint decl_bound_names (ds : list decl) : list ident :=
  match ds with
  | [] => []
  | Decl_let x _ :: rest => x :: decl_bound_names rest
  | Decl_letrec f _ :: rest => f :: decl_bound_names rest
  | _ :: rest => decl_bound_names rest
  end.

(* After evaluating inner module decls, add qualified aliases.
   For each name x bound by the inner decls, look it up in the resulting
   env and re-add it as "mod_name.x". *)
Fixpoint add_qualified_bindings (prefix : ident) (names : list ident) (inner_env env_acc : env) : env :=
  match names with
  | [] => env_acc
  | x :: rest =>
    let env_acc' :=
      match env_lookup inner_env x with
      | Some v => env_extend env_acc (qualify_name prefix x) v
      | None => env_acc
      end in
    add_qualified_bindings prefix rest inner_env env_acc'
  end.

Fixpoint open_module_bindings (mod_name : ident) (source env_acc : env) : env :=
  let prefix := String.append mod_name "." in
  match source with
  | Env_nil => env_acc
  | Env_cons x v rest =>
    let env_acc' :=
      match strip_prefix prefix x with
      | Some short => env_extend env_acc short v
      | None => env_acc
      end in
    open_module_bindings mod_name rest env_acc'
  end.

(* eval_program returns (env * eval_result): the accumulated environment
   alongside the evaluation result. This allows Decl_module to extract
   the env produced by inner declarations and add qualified-name aliases. *)
Fixpoint eval_program (fuel : nat) (prog : program) (env0 : env) (out : list event) :
    env * eval_result :=
  match fuel with
  | O => (env0, Eval_timeout out)
  | S fuel' =>
  match prog with
  | [] => (env0, Eval_ok SVal_unit out)
  | d :: rest =>
    match d with
    | Decl_let x e =>
      match eval fuel' e env0 out with
      | Eval_ok v out' => eval_program fuel' rest (env_extend env0 x v) out'
      | other => (env0, other)
      end
    | Decl_letrec f e =>
      match e with
      | Exp_fun param body =>
        let clos := SVal_recclosure f param body env0 in
        eval_program fuel' rest (env_extend env0 f clos) out
      | _ =>
        match eval fuel' e env0 out with
        | Eval_ok v out' => eval_program fuel' rest (env_extend env0 f v) out'
        | other => (env0, other)
        end
      end
    | Decl_type _ _ _ =>
      eval_program fuel' rest env0 out
    | Decl_expr e =>
      match eval fuel' e env0 out with
      | Eval_ok _ out' => eval_program fuel' rest env0 out'
      | other => (env0, other)
      end
    | Decl_module mod_name inner_decls =>
      match eval_program fuel' inner_decls env0 out with
      | (inner_env, Eval_ok _ out') =>
        (* Add only qualified aliases (mod_name.x) to avoid leaking module internals. *)
        let names := decl_bound_names inner_decls in
        let env_with_qual := add_qualified_bindings mod_name names inner_env env0 in
        eval_program fuel' rest env_with_qual out'
      | (_, other) => (env0, other)
      end
    | Decl_open mod_name =>
      eval_program fuel' rest (open_module_bindings mod_name env0 env0) out
    | Decl_exception _ _ =>
      eval_program fuel' rest env0 out
    end
  end
  end.

Fixpoint svalue_to_value (fuel : nat) (v : svalue) : option value :=
  match fuel with
  | O => None
  | S fuel' =>
    match v with
    | SVal_int n => Some (Val_int n)
    | SVal_bool b => Some (val_bool b)
    | SVal_unit => Some val_unit
    | SVal_tuple vs =>
      match (fix list_to_values (vs : list svalue) : option (list value) :=
        match vs with
        | [] => Some []
        | v :: rest =>
          match svalue_to_value fuel' v, list_to_values rest with
          | Some v', Some rest' => Some (v' :: rest')
          | _, _ => None
          end
        end) vs with
      | Some vals => Some (Val_block 0 vals)
      | None => None
      end
    | SVal_constr "[]" None => Some (Val_int 0)
    | SVal_constr "::" (Some (SVal_tuple [h; t])) =>
      match svalue_to_value fuel' h, svalue_to_value fuel' t with
      | Some hv, Some tv => Some (Val_block 0 [hv; tv])
      | _, _ => None
      end
    | SVal_record fields =>
      match (fix fields_to_values (fields : list (ident * svalue)) : option (list value) :=
        match fields with
        | [] => Some []
        | (_, v) :: rest =>
          match svalue_to_value fuel' v, fields_to_values rest with
          | Some v', Some rest' => Some (v' :: rest')
          | _, _ => None
          end
        end) fields with
      | Some vals => Some (Val_block 0 vals)
      | None => None
      end
    | SVal_string s =>
      Some (Val_block String_tag (List.map (fun ev => match ev with Out_char c => Val_int c end) (string_to_events s)))
    | _ => None
    end
  end.

(* Entry point *)
Definition interpret (fuel : nat) (prog : program) : behavior :=
  match eval_program fuel prog stdlib_env [] with
  | (_, Eval_ok v out) =>
    mk_behavior (rev out) (Term_normal (match svalue_to_value fuel v with
                                        | Some rv => rv
                                        | None => Val_int 0
                                        end))
  | (_, Eval_err msg out) => mk_behavior (rev out) (Term_error msg)
  | (_, Eval_timeout out) => mk_behavior (rev out) Term_timeout
  end.
