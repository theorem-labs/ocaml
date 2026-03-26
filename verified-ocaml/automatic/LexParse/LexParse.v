(* LexParse.v - OCaml source string to AST parser.
   Inverts PrettyPrint.v's fully parenthesized output format.
   Uses fuel-based recursion for termination. *)

From Stdlib Require Import ZArith Strings.String Strings.Ascii.
From Stdlib Require Import List Bool Nat. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Syntax.
From OCamlInterp.Manual.Utils Require Import WellFormed.
Open Scope string_scope.

(* ========== String Helpers ========== *)

Fixpoint strip_prefix (pre s : string) : option string :=
  match pre with
  | EmptyString => Some s
  | String c1 pre' =>
    match s with
    | EmptyString => None
    | String c2 s' =>
      if Ascii.eqb c1 c2 then strip_prefix pre' s'
      else None
    end
  end.

(* ========== Integer Parsing ========== *)

(* Read digits, accumulating into nat *)
Fixpoint read_digits (s : string) (acc : nat) : nat * string :=
  match s with
  | String c rest =>
    if is_digit c then
      read_digits rest (acc * 10 + (nat_of_ascii c - 48))
    else (acc, s)
  | EmptyString => (acc, s)
  end.

(* Parse a positive natural number (requires at least one digit) *)
Definition parse_nat (s : string) : option (nat * string) :=
  match s with
  | String c rest =>
    if is_digit c then
      Some (read_digits rest (nat_of_ascii c - 48))
    else None
  | EmptyString => None
  end.

(* Try to parse "(-digits)" as a negative integer *)
Definition try_neg_int (s : string) : option (Z * string) :=
  match strip_prefix "(-" s with
  | Some rest =>
    match rest with
    | String c _ =>
      if is_digit c then
        match parse_nat rest with
        | Some (n, rest') =>
          match strip_prefix ")" rest' with
          | Some rest'' => Some (Z.opp (Z.of_nat n), rest'')
          | None => None
          end
        | None => None
        end
      else None
    | EmptyString => None
    end
  | None => None
  end.

(* ========== Identifier Parsing ========== *)

(* Read maximal sequence of ident chars *)
Fixpoint read_ident_chars (s : string) : string * string :=
  match s with
  | String c rest =>
    if is_ident_char c then
      let (more, remaining) := read_ident_chars rest in
      (String c more, remaining)
    else (EmptyString, s)
  | EmptyString => (EmptyString, s)
  end.

(* Parse an identifier: starts with alpha or underscore *)
Definition parse_ident (s : string) : option (string * string) :=
  match s with
  | String c rest =>
    if is_ident_start c then
      let (more, remaining) := read_ident_chars rest in
      Some (String c more, remaining)
    else None
  | EmptyString => None
  end.

(* ========== Binary Operator Detection ========== *)

Definition try_binop (s : string) : option (binop * string) :=
  match strip_prefix " + " s with Some rest => Some (Op_add, rest) | None =>
  match strip_prefix " - " s with Some rest => Some (Op_sub, rest) | None =>
  match strip_prefix " * " s with Some rest => Some (Op_mul, rest) | None =>
  match strip_prefix " / " s with Some rest => Some (Op_div, rest) | None =>
  match strip_prefix " mod " s with Some rest => Some (Op_mod, rest) | None =>
  match strip_prefix " <> " s with Some rest => Some (Op_neq, rest) | None =>
  match strip_prefix " <= " s with Some rest => Some (Op_le, rest) | None =>
  match strip_prefix " < " s with Some rest => Some (Op_lt, rest) | None =>
  match strip_prefix " >= " s with Some rest => Some (Op_ge, rest) | None =>
  match strip_prefix " > " s with Some rest => Some (Op_gt, rest) | None =>
  match strip_prefix " = " s with Some rest => Some (Op_eq, rest) | None =>
  match strip_prefix " && " s with Some rest => Some (Op_and, rest) | None =>
  match strip_prefix " || " s with Some rest => Some (Op_or, rest) | None =>
  None
  end end end end end end end end end end end end end.

(* ========== Pattern Parsing ========== *)

Fixpoint parse_pattern (fuel : nat) (s : string) : option (pattern * string) :=
  match fuel with
  | O => None
  | S fuel' =>
    (* Try "(-digits)" for negative Pat_int *)
    match try_neg_int s with
    | Some (z, rest) => Some (Pat_int z, rest)
    | None =>
    (* Try "()" for Pat_unit *)
    match strip_prefix "()" s with
    | Some rest => Some (Pat_unit, rest)
    | None =>
    (* Try "(" for parenthesized forms *)
    match strip_prefix "(" s with
    | Some rest1 =>
      (* Parse first sub-pattern *)
      match parse_pattern fuel' rest1 with
      | Some (p1, rest2) =>
        (* Check continuation *)
        match strip_prefix ", " rest2 with
        | Some rest3 =>
          (* Tuple: parse more comma-separated patterns *)
          let fix parse_more (n : nat) (s0 : string) : option (list pattern * string) :=
            match n with
            | O => None
            | S n' =>
              match parse_pattern fuel' s0 with
              | Some (p, rest4) =>
                match strip_prefix ", " rest4 with
                | Some rest5 =>
                  match parse_more n' rest5 with
                  | Some (ps, rest6) => Some (p :: ps, rest6)
                  | None => None
                  end
                | None =>
                  match strip_prefix ")" rest4 with
                  | Some rest5 => Some ([p], rest5)
                  | None => None
                  end
                end
              | None => None
              end
            end
          in
          match parse_more fuel' rest3 with
          | Some (ps, rest4) => Some (Pat_tuple (p1 :: ps), rest4)
          | None => None
          end
        | None =>
          (* Check for " | " -> Pat_or *)
          match strip_prefix " | " rest2 with
          | Some rest3 =>
            match parse_pattern fuel' rest3 with
            | Some (p2, rest4) =>
              match strip_prefix ")" rest4 with
              | Some rest5 => Some (Pat_or p1 p2, rest5)
              | None => None
              end
            | None => None
            end
          | None =>
          match strip_prefix " " rest2 with
          | Some rest3 =>
            (* Constructor with argument: (C pattern) *)
            match p1 with
            | Pat_constr c None =>
              match parse_pattern fuel' rest3 with
              | Some (arg, rest4) =>
                match strip_prefix ")" rest4 with
                | Some rest5 => Some (Pat_constr c (Some arg), rest5)
                | None => None
                end
              | None => None
              end
            | _ => None
            end
          | None => None
          end end
        end
      | None => None
      end
    | None =>
    (* Try "{ " for Pat_record *)
    match strip_prefix "{ " s with
    | Some rest1 =>
      let fix parse_rec_fields (n : nat) (s0 : string) :
        option (list (ident * pattern) * string) :=
        match n with
        | O => None
        | S n' =>
          match parse_ident s0 with
          | Some (fname, rest2) =>
            match strip_prefix " = " rest2 with
            | Some rest3 =>
              match parse_pattern fuel' rest3 with
              | Some (p, rest4) =>
                match strip_prefix "; " rest4 with
                | Some rest5 =>
                  match parse_rec_fields n' rest5 with
                  | Some (fs, rest6) => Some ((fname, p) :: fs, rest6)
                  | None => None
                  end
                | None =>
                  match strip_prefix " }" rest4 with
                  | Some rest5 => Some ([(fname, p)], rest5)
                  | None => None
                  end
                end
              | None => None
              end
            | None => None
            end
          | None => None
          end
        end
      in
      match parse_rec_fields fuel' rest1 with
      | Some (fields, rest2) => Some (Pat_record fields, rest2)
      | None => None
      end
    | None =>
    (* Try atom: digit, keyword, identifier, wildcard *)
    match s with
    | String c rest =>
      if Ascii.eqb c "_"%char then
        match rest with
        | String c' _ =>
          if is_ident_char c' then
            (* Identifier starting with _ *)
            match parse_ident s with
            | Some (id, rest') => Some (Pat_var id, rest')
            | None => None
            end
          else Some (Pat_wild, rest)
        | EmptyString => Some (Pat_wild, rest)
        end
      else if is_digit c then
        match parse_nat s with
        | Some (n, rest') => Some (Pat_int (Z.of_nat n), rest')
        | None => None
        end
      else if is_alpha c then
        match parse_ident s with
        | Some (id, rest') =>
          if String.eqb id "true" then Some (Pat_bool true, rest')
          else if String.eqb id "false" then Some (Pat_bool false, rest')
          else if is_upper c then Some (Pat_constr id None, rest')
          else Some (Pat_var id, rest')
        | None => None
        end
      else None
    | EmptyString => None
    end
    end end end end
  end.

(* ========== Type Expression Parsing ========== *)

Fixpoint parse_type_expr (fuel : nat) (s : string) : option (type_expr * string) :=
  match fuel with
  | O => None
  | S fuel' =>
    (* Try "((" for multi-arg type constructor *)
    match strip_prefix "((" s with
    | Some rest1 =>
      (* Parse comma-separated type args until ") name)" *)
      let fix parse_type_args (n : nat) (s0 : string) : option (list type_expr * string) :=
        match n with
        | O => None
        | S n' =>
          match parse_type_expr fuel' s0 with
          | Some (t, rest2) =>
            match strip_prefix ", " rest2 with
            | Some rest3 =>
              match parse_type_args n' rest3 with
              | Some (ts, rest4) => Some (t :: ts, rest4)
              | None => None
              end
            | None =>
              match strip_prefix ") " rest2 with
              | Some rest3 => Some ([t], rest3)
              | None => None
              end
            end
          | None => None
          end
        end
      in
      match parse_type_args fuel' rest1 with
      | Some (args, rest2) =>
        match parse_ident rest2 with
        | Some (name, rest3) =>
          match strip_prefix ")" rest3 with
          | Some rest4 => Some (Ty_constr name args, rest4)
          | None => None
          end
        | None => None
        end
      | None => None
      end
    | None =>
    (* Try "(" for arrow, tuple, or single-arg constr *)
    match strip_prefix "(" s with
    | Some rest1 =>
      match parse_type_expr fuel' rest1 with
      | Some (t1, rest2) =>
        (* Check for " -> " (arrow) *)
        match strip_prefix " -> " rest2 with
        | Some rest3 =>
          match parse_type_expr fuel' rest3 with
          | Some (t2, rest4) =>
            match strip_prefix ")" rest4 with
            | Some rest5 => Some (Ty_arrow t1 t2, rest5)
            | None => None
            end
          | None => None
          end
        | None =>
        (* Check for " * " (tuple) *)
        match strip_prefix " * " rest2 with
        | Some rest3 =>
          let fix parse_star (n : nat) (s0 : string) : option (list type_expr * string) :=
            match n with
            | O => None
            | S n' =>
              match parse_type_expr fuel' s0 with
              | Some (t, rest4) =>
                match strip_prefix " * " rest4 with
                | Some rest5 =>
                  match parse_star n' rest5 with
                  | Some (ts, rest6) => Some (t :: ts, rest6)
                  | None => None
                  end
                | None =>
                  match strip_prefix ")" rest4 with
                  | Some rest5 => Some ([t], rest5)
                  | None => None
                  end
                end
              | None => None
              end
            end
          in
          match parse_star fuel' rest3 with
          | Some (ts, rest4) => Some (Ty_tuple (t1 :: ts), rest4)
          | None => None
          end
        | None =>
        (* Check for " name)" (single-arg type constr) *)
        match strip_prefix " " rest2 with
        | Some rest3 =>
          match parse_ident rest3 with
          | Some (name, rest4) =>
            match strip_prefix ")" rest4 with
            | Some rest5 => Some (Ty_constr name [t1], rest5)
            | None => None
            end
          | None => None
          end
        | None => None
        end end end
      | None => None
      end
    | None =>
    (* Try identifier or base type *)
    match s with
    | String c _ =>
      if is_alpha c || Ascii.eqb c "_"%char then
        match parse_ident s with
        | Some (id, rest) =>
          if String.eqb id "int" then Some (Ty_int, rest)
          else if String.eqb id "bool" then Some (Ty_bool, rest)
          else if String.eqb id "unit" then Some (Ty_unit, rest)
          else Some (Ty_constr id [], rest)
        | None => None
        end
      else None
    | EmptyString => None
    end
    end end
  end.

(* ========== String Content Parsing ========== *)

(* Read characters until we hit a double-quote character.
   Returns the string contents and the remaining input after the quote. *)
Fixpoint read_string_contents (fuel : nat) (s : string) (acc : string) : option (string * string) :=
  match fuel with
  | O => None
  | S fuel' =>
    match s with
    | EmptyString => None
    | String c rest =>
      if Ascii.eqb c """"%char then Some (acc, rest)
      else read_string_contents fuel' rest (String.append acc (String c EmptyString))
    end
  end.

(* ========== Expression Parsing ========== *)

Fixpoint parse_expr (fuel : nat) (s : string) : option (expr * string) :=
  match fuel with
  | O => None
  | S fuel' =>
    (* Try "(-digits)" for negative Exp_int *)
    match try_neg_int s with
    | Some (z, rest) => Some (Exp_int z, rest)
    | None =>
    (* Try "()" for Exp_unit *)
    match strip_prefix "()" s with
    | Some rest => Some (Exp_unit, rest)
    | None =>
    (* Try "{ " for Exp_record *)
    match strip_prefix "{ " s with
    | Some rest1 =>
      let fix parse_rec_fields (n : nat) (s0 : string) :
        option (list (ident * expr) * string) :=
        match n with
        | O => None
        | S n' =>
          match parse_ident s0 with
          | Some (fname, rest2) =>
            match strip_prefix " = " rest2 with
            | Some rest3 =>
              match parse_expr fuel' rest3 with
              | Some (e, rest4) =>
                match strip_prefix "; " rest4 with
                | Some rest5 =>
                  match parse_rec_fields n' rest5 with
                  | Some (fs, rest6) => Some ((fname, e) :: fs, rest6)
                  | None => None
                  end
                | None =>
                  match strip_prefix " }" rest4 with
                  | Some rest5 => Some ([(fname, e)], rest5)
                  | None => None
                  end
                end
              | None => None
              end
            | None => None
            end
          | None => None
          end
        end
      in
      match parse_rec_fields fuel' rest1 with
      | Some (fields, rest2) => Some (Exp_record fields, rest2)
      | None => None
      end
    | None =>
    (* Try "(" for compound forms *)
    match strip_prefix "(" s with
    | Some rest1 =>
      (* Check for string literal: ("...") *)
      match strip_prefix """" rest1 with
      | Some rest_str =>
        match read_string_contents fuel' rest_str "" with
        | Some (str_val, rest_after_quote) =>
          match strip_prefix ")" rest_after_quote with
          | Some rest_final => Some (Exp_string str_val, rest_final)
          | None => None
          end
        | None => None
        end
      | None =>
      (* Check for function expression: (function ...) *)
      match strip_prefix "function " rest1 with
      | Some rest2 =>
        let fix parse_func_cases (n : nat) (s0 : string) :
          option (list (pattern * expr) * string) :=
          match n with
          | O => None
          | S n' =>
            match strip_prefix "| " s0 with
            | Some rest3 =>
              match parse_pattern fuel' rest3 with
              | Some (pat, rest4) =>
                match strip_prefix " -> " rest4 with
                | Some rest5 =>
                  match parse_expr fuel' rest5 with
                  | Some (body, rest6) =>
                    match strip_prefix " " rest6 with
                    | Some rest7 =>
                      match parse_func_cases n' rest7 with
                      | Some (cases, rest8) =>
                        Some ((pat, body) :: cases, rest8)
                      | None => None
                      end
                    | None =>
                      match strip_prefix ")" rest6 with
                      | Some rest7 => Some ([(pat, body)], rest7)
                      | None => None
                      end
                    end
                  | None => None
                  end
                | None => None
                end
              | None => None
              end
            | None => None
            end
          end
        in
        match parse_func_cases fuel' rest2 with
        | Some (cases, rest3) => Some (Exp_function cases, rest3)
        | None => None
        end
      | None =>
      (* Check keyword forms *)
      match strip_prefix "- " rest1 with
      | Some rest2 =>
        (* Unary negation: (- expr) *)
        match parse_expr fuel' rest2 with
        | Some (e, rest3) =>
          match strip_prefix ")" rest3 with
          | Some rest4 => Some (Exp_unop Op_neg e, rest4)
          | None => None
          end
        | None => None
        end
      | None =>
      match strip_prefix "not " rest1 with
      | Some rest2 =>
        match parse_expr fuel' rest2 with
        | Some (e, rest3) =>
          match strip_prefix ")" rest3 with
          | Some rest4 => Some (Exp_unop Op_not e, rest4)
          | None => None
          end
        | None => None
        end
      | None =>
      match strip_prefix "if " rest1 with
      | Some rest2 =>
        match parse_expr fuel' rest2 with
        | Some (cond, rest3) =>
          match strip_prefix " then " rest3 with
          | Some rest4 =>
            match parse_expr fuel' rest4 with
            | Some (then_e, rest5) =>
              match strip_prefix " else " rest5 with
              | Some rest6 =>
                match parse_expr fuel' rest6 with
                | Some (else_e, rest7) =>
                  match strip_prefix ")" rest7 with
                  | Some rest8 => Some (Exp_if cond then_e else_e, rest8)
                  | None => None
                  end
                | None => None
                end
              | None => None
              end
            | None => None
            end
          | None => None
          end
        | None => None
        end
      | None =>
      match strip_prefix "let rec " rest1 with
      | Some rest2 =>
        match parse_ident rest2 with
        | Some (name, rest3) =>
          match strip_prefix " = " rest3 with
          | Some rest4 =>
            match parse_expr fuel' rest4 with
            | Some (e1, rest5) =>
              match strip_prefix " in " rest5 with
              | Some rest6 =>
                match parse_expr fuel' rest6 with
                | Some (e2, rest7) =>
                  match strip_prefix ")" rest7 with
                  | Some rest8 => Some (Exp_letrec name e1 e2, rest8)
                  | None => None
                  end
                | None => None
                end
              | None => None
              end
            | None => None
            end
          | None => None
          end
        | None => None
        end
      | None =>
      match strip_prefix "let " rest1 with
      | Some rest2 =>
        match parse_ident rest2 with
        | Some (name, rest3) =>
          match strip_prefix " = " rest3 with
          | Some rest4 =>
            match parse_expr fuel' rest4 with
            | Some (e1, rest5) =>
              match strip_prefix " in " rest5 with
              | Some rest6 =>
                match parse_expr fuel' rest6 with
                | Some (e2, rest7) =>
                  match strip_prefix ")" rest7 with
                  | Some rest8 => Some (Exp_let name e1 e2, rest8)
                  | None => None
                  end
                | None => None
                end
              | None => None
              end
            | None => None
            end
          | None => None
          end
        | None => None
        end
      | None =>
      match strip_prefix "fun " rest1 with
      | Some rest2 =>
        match parse_ident rest2 with
        | Some (name, rest3) =>
          match strip_prefix " -> " rest3 with
          | Some rest4 =>
            match parse_expr fuel' rest4 with
            | Some (body, rest5) =>
              match strip_prefix ")" rest5 with
              | Some rest6 => Some (Exp_fun name body, rest6)
              | None => None
              end
            | None => None
            end
          | None => None
          end
        | None => None
        end
      | None =>
      match strip_prefix "match " rest1 with
      | Some rest2 =>
        (* Parse match expression *)
        match parse_expr fuel' rest2 with
        | Some (scrutinee, rest3) =>
          match strip_prefix " with " rest3 with
          | Some rest4 =>
            (* Parse match cases *)
            let fix parse_cases (n : nat) (s0 : string) :
              option (list (pattern * expr) * string) :=
              match n with
              | O => None
              | S n' =>
                match strip_prefix "| " s0 with
                | Some rest5 =>
                  match parse_pattern fuel' rest5 with
                  | Some (pat, rest6) =>
                    match strip_prefix " -> " rest6 with
                    | Some rest7 =>
                      match parse_expr fuel' rest7 with
                      | Some (body, rest8) =>
                        (* Check for more cases or end *)
                        match strip_prefix " " rest8 with
                        | Some rest9 =>
                          match parse_cases n' rest9 with
                          | Some (cases, rest10) =>
                            Some ((pat, body) :: cases, rest10)
                          | None => None
                          end
                        | None =>
                          match strip_prefix ")" rest8 with
                          | Some rest9 => Some ([(pat, body)], rest9)
                          | None => None
                          end
                        end
                      | None => None
                      end
                    | None => None
                    end
                  | None => None
                  end
                | None => None
                end
              end
            in
            match parse_cases fuel' rest4 with
            | Some (cases, rest5) =>
              Some (Exp_match scrutinee cases, rest5)
            | None => None
            end
          | None => None
          end
        | None => None
        end
      | None =>
        (* No keyword matched: parse first sub-expression, then check continuation *)
        match parse_expr fuel' rest1 with
        | Some (e1, rest2) =>
          (* Check for binary operators *)
          match try_binop rest2 with
          | Some (op, rest3) =>
            match parse_expr fuel' rest3 with
            | Some (e2, rest4) =>
              match strip_prefix ")" rest4 with
              | Some rest5 => Some (Exp_binop op e1 e2, rest5)
              | None => None
              end
            | None => None
            end
          | None =>
            (* Check for "." -> field access *)
            match strip_prefix "." rest2 with
            | Some rest3 =>
              match parse_ident rest3 with
              | Some (fname, rest4) =>
                match strip_prefix ")" rest4 with
                | Some rest5 => Some (Exp_field e1 fname, rest5)
                | None => None
                end
              | None => None
              end
            | None =>
            (* Check for ", " -> tuple *)
            match strip_prefix ", " rest2 with
            | Some rest3 =>
              let fix parse_comma (n : nat) (s0 : string) :
                option (list expr * string) :=
                match n with
                | O => None
                | S n' =>
                  match parse_expr fuel' s0 with
                  | Some (e, rest4) =>
                    match strip_prefix ", " rest4 with
                    | Some rest5 =>
                      match parse_comma n' rest5 with
                      | Some (es, rest6) => Some (e :: es, rest6)
                      | None => None
                      end
                    | None =>
                      match strip_prefix ")" rest4 with
                      | Some rest5 => Some ([e], rest5)
                      | None => None
                      end
                    end
                  | None => None
                  end
                end
              in
              match parse_comma fuel' rest3 with
              | Some (es, rest4) => Some (Exp_tuple (e1 :: es), rest4)
              | None => None
              end
            | None =>
              (* Check for "; " -> sequence *)
              match strip_prefix "; " rest2 with
              | Some rest3 =>
                match parse_expr fuel' rest3 with
                | Some (e2, rest4) =>
                  match strip_prefix ")" rest4 with
                  | Some rest5 => Some (Exp_seq e1 e2, rest5)
                  | None => None
                  end
                | None => None
                end
              | None =>
                (* Check for " " -> application or constructor with arg *)
                match strip_prefix " " rest2 with
                | Some rest3 =>
                  match parse_expr fuel' rest3 with
                  | Some (e2, rest4) =>
                    match strip_prefix ")" rest4 with
                    | Some rest5 =>
                      match e1 with
                      | Exp_constr c None =>
                        Some (Exp_constr c (Some e2), rest5)
                      | _ => Some (Exp_app e1 e2, rest5)
                      end
                    | None => None
                    end
                  | None => None
                  end
                | None => None
                end
              end
            end
          end end
        | None => None
        end
      end end end end end end end end end
    | None =>
    (* Not parenthesized: try atoms *)
    match s with
    | String c _ =>
      if is_digit c then
        match parse_nat s with
        | Some (n, rest) => Some (Exp_int (Z.of_nat n), rest)
        | None => None
        end
      else if is_alpha c || Ascii.eqb c "_"%char then
        match parse_ident s with
        | Some (id, rest) =>
          if String.eqb id "true" then Some (Exp_bool true, rest)
          else if String.eqb id "false" then Some (Exp_bool false, rest)
          else if is_upper c then Some (Exp_constr id None, rest)
          else Some (Exp_var id, rest)
        | None => None
        end
      else None
    | EmptyString => None
    end
    end end end end
  end.

(* ========== Type Definition Parsing ========== *)

Fixpoint parse_variant (fuel : nat) (s : string) :
  option (list (ident * option type_expr) * string) :=
  match fuel with
  | O => None
  | S fuel' =>
    match parse_ident s with
    | Some (name, rest) =>
      match strip_prefix " of " rest with
      | Some rest2 =>
        match parse_type_expr fuel' rest2 with
        | Some (t, rest3) =>
          match strip_prefix " | " rest3 with
          | Some rest4 =>
            match parse_variant fuel' rest4 with
            | Some (more, rest5) => Some ((name, Some t) :: more, rest5)
            | None => None
            end
          | None => Some ([(name, Some t)], rest3)
          end
        | None => None
        end
      | None =>
        match strip_prefix " | " rest with
        | Some rest2 =>
          match parse_variant fuel' rest2 with
          | Some (more, rest3) => Some ((name, @None type_expr) :: more, rest3)
          | None => None
          end
        | None => Some ([(name, @None type_expr)], rest)
        end
      end
    | None => None
    end
  end.

Fixpoint parse_td_record_fields (fuel : nat) (s : string) :
  option (list (ident * type_expr) * string) :=
  match fuel with
  | O => None
  | S fuel' =>
    match parse_ident s with
    | Some (fname, rest) =>
      match strip_prefix " : " rest with
      | Some rest2 =>
        match parse_type_expr fuel' rest2 with
        | Some (t, rest3) =>
          match strip_prefix "; " rest3 with
          | Some rest4 =>
            match parse_td_record_fields fuel' rest4 with
            | Some (fs, rest5) => Some ((fname, t) :: fs, rest5)
            | None => None
            end
          | None =>
            match strip_prefix " }" rest3 with
            | Some rest4 => Some ([(fname, t)], rest4)
            | None => None
            end
          end
        | None => None
        end
      | None => None
      end
    | None => None
    end
  end.

Definition parse_type_def (fuel : nat) (s : string) : option (type_def * string) :=
  (* Try "{ " for Td_record *)
  match strip_prefix "{ " s with
  | Some rest =>
    match parse_td_record_fields fuel rest with
    | Some (fields, rest2) => Some (Td_record fields, rest2)
    | None => None
    end
  | None =>
  match s with
  | String c _ =>
    if is_upper c then
      match parse_variant fuel s with
      | Some (constrs, rest) => Some (Td_variant constrs, rest)
      | None => None
      end
    else
      match parse_type_expr fuel s with
      | Some (t, rest) => Some (Td_alias t, rest)
      | None => None
      end
  | EmptyString => None
  end end.

(* ========== Declaration Parsing ========== *)

Definition newline_char : ascii := Ascii.ascii_of_nat 10.
Definition newline_str : string := String newline_char EmptyString.

Definition parse_type_params (s : string) :
  option (list ident * string) :=
  match strip_prefix "(" s with
  | Some rest =>
    (* Multiple params: ('a, 'b, ...) *)
    let fix parse_params (fuel : nat) (s0 : string) :
      option (list ident * string) :=
      match fuel with
      | O => None
      | S fuel' =>
        match strip_prefix "'" s0 with
        | Some rest1 =>
          match parse_ident rest1 with
          | Some (p, rest2) =>
            match strip_prefix ", " rest2 with
            | Some rest3 =>
              match parse_params fuel' rest3 with
              | Some (ps, rest4) => Some (p :: ps, rest4)
              | None => None
              end
            | None =>
              match strip_prefix ") " rest2 with
              | Some rest3 => Some ([p], rest3)
              | None => None
              end
            end
          | None => None
          end
        | None => None
        end
      end
    in
    parse_params (String.length s) rest
  | None =>
    match strip_prefix "'" s with
    | Some rest =>
      (* Single param: 'a *)
      match parse_ident rest with
      | Some (p, rest') =>
        match strip_prefix " " rest' with
        | Some rest'' => Some ([p], rest'')
        | None => None
        end
      | None => None
      end
    | None =>
      (* No params *)
      Some ([], s)
    end
  end.

Fixpoint parse_decl (fuel : nat) (s : string) : option (decl * string) :=
  match fuel with
  | O => None
  | S fuel' =>
  match strip_prefix "let rec " s with
  | Some rest =>
    match parse_ident rest with
    | Some (name, rest') =>
      match strip_prefix " = " rest' with
      | Some rest'' =>
        match parse_expr fuel rest'' with
        | Some (e, rest''') => Some (Decl_letrec name e, rest''')
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | None =>
  match strip_prefix "let " s with
  | Some rest =>
    match parse_ident rest with
    | Some (name, rest') =>
      match strip_prefix " = " rest' with
      | Some rest'' =>
        match parse_expr fuel rest'' with
        | Some (e, rest''') => Some (Decl_let name e, rest''')
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | None =>
  match strip_prefix "type " s with
  | Some rest =>
    match parse_type_params rest with
    | Some (params, rest') =>
      match parse_ident rest' with
      | Some (name, rest'') =>
        match strip_prefix " = " rest'' with
        | Some rest''' =>
          match parse_type_def fuel rest''' with
          | Some (td, rest4) => Some (Decl_type name params td, rest4)
          | None => None
          end
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | None =>
  match strip_prefix "module " s with
  | Some rest =>
    match parse_ident rest with
    | Some (name, rest') =>
      match strip_prefix " = struct " rest' with
      | Some rest'' =>
        let fix parse_module_decls (n : nat) (s0 : string) :
          option (list decl * string) :=
          match n with
          | O => None
          | S n' =>
            match parse_decl fuel' s0 with
            | Some (d, rest3) =>
              match strip_prefix ";;" rest3 with
              | Some rest4 =>
                match strip_prefix newline_str rest4 with
                | Some rest5 =>
                  match parse_module_decls n' rest5 with
                  | Some (ds, rest6) => Some (d :: ds, rest6)
                  | None => None
                  end
                | None =>
                  match strip_prefix " end" rest4 with
                  | Some rest5 => Some ([d], rest5)
                  | None => None
                  end
                end
              | None => None
              end
            | None => None
            end
          end
        in
        match parse_module_decls fuel' rest'' with
        | Some (decls, rest3) => Some (Decl_module name decls, rest3)
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | None =>
  match strip_prefix "open " s with
  | Some rest =>
    match parse_ident rest with
    | Some (name, rest') => Some (Decl_open name, rest')
    | None => None
    end
  | None =>
  match strip_prefix "exception " s with
  | Some rest =>
    match parse_ident rest with
    | Some (name, rest') =>
      match strip_prefix " of " rest' with
      | Some rest'' =>
        match parse_type_expr fuel rest'' with
        | Some (t, rest''') => Some (Decl_exception name (Some t), rest''')
        | None => None
        end
      | None => Some (Decl_exception name None, rest')
      end
    | None => None
    end
  | None =>
    (* Decl_expr *)
    match parse_expr fuel s with
    | Some (e, rest) => Some (Decl_expr e, rest)
    | None => None
    end
  end end end end end end end.

(* ========== Program Parsing ========== *)

Fixpoint parse_program_aux (fuel decl_fuel : nat) (s : string) :
  option (list decl * string) :=
  match fuel with
  | O => Some ([], s)
  | S fuel' =>
    match s with
    | EmptyString => Some ([], EmptyString)
    | String _ _ =>
      match parse_decl decl_fuel s with
      | Some (d, rest) =>
        match strip_prefix ";;" rest with
        | Some rest' =>
          match strip_prefix newline_str rest' with
          | Some rest'' =>
            match parse_program_aux fuel' decl_fuel rest'' with
            | Some (ds, rest''') => Some (d :: ds, rest''')
            | None => None
            end
          | None => Some ([d], rest')
          end
        | None => None
        end
      | None => None
      end
    end
  end.

(* ========== Top-level lex_parse ========== *)

Definition lex_parse (s : string) : option program :=
  let fuel := String.length s in
  match parse_program_aux fuel fuel s with
  | Some (prog, EmptyString) => Some prog
  | _ => None
  end.
