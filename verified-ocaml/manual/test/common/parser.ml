(* parser.ml - [UNTRUSTED] Recursive descent parser for OCaml subset.
   Parses the fully-parenthesized output of PrettyPrint.v.
   Validated by PBT: parse(pretty_print(ast)) = ast *)

open Interp_extracted
open Lexer

(* Convert OCaml string to char list (extracted ident type) *)
let cl s = List.init (String.length s) (fun i -> s.[i])

type 'a parse_result = Ok of 'a * token list | Fail of string

let is_upper s = s <> "" && s.[0] >= 'A' && s.[0] <= 'Z'

(* Parse a pattern *)
let rec parse_pattern tokens =
  match tokens with
  | LPAREN :: RPAREN :: rest -> Ok (Pat_unit, rest)
  | LPAREN :: MINUS :: INT n :: RPAREN :: rest -> Ok (Pat_int (- n), rest)
  | LPAREN :: rest -> parse_paren_pattern rest
  | LBRACKET :: RBRACKET :: rest -> Ok (Pat_nil, rest)
  | LBRACE :: rest -> parse_record_pattern rest
  | TRUE :: rest -> Ok (Pat_bool true, rest)
  | FALSE :: rest -> Ok (Pat_bool false, rest)
  | UNDERSCORE :: rest -> Ok (Pat_wild, rest)
  | INT n :: rest -> Ok (Pat_int n, rest)
  | STRING c :: rest when is_upper c -> Ok (Pat_constr (cl c, None), rest)
  | STRING x :: rest -> Ok (Pat_var (cl x), rest)
  | _ -> Fail "cannot parse pattern"

and parse_record_pattern tokens =
  (* { field = pat; ... } *)
  let rec loop acc toks =
    match toks with
    | STRING f :: EQ :: rest ->
      (match parse_pattern rest with
       | Ok (p, SEMI :: rest2) -> loop ((cl f, p) :: acc) rest2
       | Ok (p, RBRACE :: rest2) -> Ok (Pat_record (List.rev ((cl f, p) :: acc)), rest2)
       | _ -> Fail "bad record pattern field")
    | _ -> Fail "expected field name in record pattern"
  in loop [] tokens

and parse_paren_pattern tokens =
  (* Parse first pattern, then decide based on what follows *)
  match tokens with
  | STRING c :: rest when is_upper c ->
    (* Could be (C arg), (C, ...) tuple, (C), (C :: ...) cons, or (C | ...) or *)
    (match rest with
     | RPAREN :: rest2 -> Ok (Pat_constr (cl c, None), rest2)
     | COLONCOLON :: rest2 ->
       (* Cons: (C :: pat) *)
       (match parse_pattern rest2 with
        | Ok (p2, RPAREN :: rest3) -> Ok (Pat_cons (Pat_constr (cl c, None), p2), rest3)
        | _ -> Fail "bad cons pattern after constructor")
     | PIPE :: rest2 ->
       (* Or: (C | pat) *)
       (match parse_pattern rest2 with
        | Ok (p2, RPAREN :: rest3) -> Ok (Pat_or (Pat_constr (cl c, None), p2), rest3)
        | _ -> Fail "bad or pattern after constructor")
     | COMMA :: rest2 ->
       (* Tuple: (C, p2, ...) *)
       let p1 = Pat_constr (cl c, None) in
       let rec parse_rest acc toks =
         match parse_pattern toks with
         | Ok (p, COMMA :: r) -> parse_rest (p :: acc) r
         | Ok (p, RPAREN :: r) -> Ok (Pat_tuple (List.rev (p :: acc)), r)
         | _ -> Fail "expected , or ) in tuple pattern"
       in parse_rest [p1] rest2
     | _ ->
       (* Try constructor with arg *)
       (match parse_pattern rest with
        | Ok (arg, RPAREN :: rest2) -> Ok (Pat_constr (cl c, Some arg), rest2)
        | Ok (arg, COLONCOLON :: rest2) ->
          (* (C arg :: pat) -> cons of constructor-with-arg *)
          (match parse_pattern rest2 with
           | Ok (p2, RPAREN :: rest3) -> Ok (Pat_cons (Pat_constr (cl c, Some arg), p2), rest3)
           | _ -> Fail "bad cons pattern after constructor with arg")
        | Ok (arg, PIPE :: rest2) ->
          (* (C arg | pat) -> or of constructor-with-arg *)
          (match parse_pattern rest2 with
           | Ok (p2, RPAREN :: rest3) -> Ok (Pat_or (Pat_constr (cl c, Some arg), p2), rest3)
           | _ -> Fail "bad or pattern after constructor with arg")
        | Ok (arg, COMMA :: rest2) ->
          (* (C arg, ...) -> tuple starting with constructor *)
          let p1 = Pat_constr (cl c, Some arg) in
          let rec parse_rest acc toks =
            match parse_pattern toks with
            | Ok (p, COMMA :: r) -> parse_rest (p :: acc) r
            | Ok (p, RPAREN :: r) -> Ok (Pat_tuple (List.rev (p :: acc)), r)
            | _ -> Fail "expected , or ) in tuple pattern"
          in parse_rest [p1] rest2
        | _ -> Fail "bad constructor pattern arg"))
  | _ ->
    (* Non-constructor: parse pattern, check for tuple, or, cons *)
    (match parse_pattern tokens with
     | Ok (p1, COLONCOLON :: rest) ->
       (match parse_pattern rest with
        | Ok (p2, RPAREN :: rest2) -> Ok (Pat_cons (p1, p2), rest2)
        | _ -> Fail "bad cons pattern")
     | Ok (p1, PIPE :: rest) ->
       (match parse_pattern rest with
        | Ok (p2, RPAREN :: rest2) -> Ok (Pat_or (p1, p2), rest2)
        | _ -> Fail "bad or pattern")
     | Ok (p1, COMMA :: rest) ->
       let rec parse_rest acc toks =
         match parse_pattern toks with
         | Ok (p, COMMA :: rest2) -> parse_rest (p :: acc) rest2
         | Ok (p, RPAREN :: rest2) -> Ok (Pat_tuple (List.rev (p :: acc)), rest2)
         | _ -> Fail "expected , or ) in tuple pattern"
       in parse_rest [p1] rest
     | Ok (p, RPAREN :: rest) -> Ok (p, rest)
     | Ok (_, _) -> Fail "expected , or ) after pattern in parens"
     | Fail msg -> Fail msg)

(* Identify which binop a token represents *)
let token_to_binop = function
  | PLUS -> Some Op_add | MINUS -> Some Op_sub | STAR -> Some Op_mul
  | SLASH -> Some Op_div | MOD -> Some Op_mod
  | EQ -> Some Op_eq | NEQ -> Some Op_neq
  | LT -> Some Op_lt | LE -> Some Op_le | GT -> Some Op_gt | GE -> Some Op_ge
  | AMPAMP -> Some Op_and | PIPEPIPE -> Some Op_or
  | _ -> None

(* Parse an expression *)
let rec parse_expr tokens =
  match tokens with
  | LPAREN :: RPAREN :: rest -> Ok (Exp_unit, rest)
  | LPAREN :: rest -> parse_paren_expr rest
  | LBRACKET :: RBRACKET :: rest -> Ok (Exp_nil, rest)
  | LBRACE :: rest -> parse_record_expr rest
  | TRUE :: rest -> Ok (Exp_bool true, rest)
  | FALSE :: rest -> Ok (Exp_bool false, rest)
  | INT n :: rest -> Ok (Exp_int n, rest)
  | STRING c :: rest when is_upper c -> Ok (Exp_constr (cl c, None), rest)
  | STRING x :: rest -> Ok (Exp_var (cl x), rest)
  | _ -> Fail "cannot parse expression"

(* Parse record expression: { f1 = e1; f2 = e2 } *)
and parse_record_expr tokens =
  let rec loop acc toks =
    match toks with
    | STRING f :: EQ :: rest ->
      (match parse_expr rest with
       | Ok (e, SEMI :: rest2) -> loop ((cl f, e) :: acc) rest2
       | Ok (e, RBRACE :: rest2) -> Ok (Exp_record (List.rev ((cl f, e) :: acc)), rest2)
       | _ -> Fail "bad record expr field")
    | _ -> Fail "expected field name in record expr"
  in loop [] tokens

(* Parse expression inside parens - this is where all compound forms live *)
and parse_paren_expr tokens =
  match tokens with
  (* String literal: ("...") *)
  | STRING_LIT s :: RPAREN :: rest -> Ok (Exp_string (cl s), rest)
  (* Negative int or unary negation *)
  | MINUS :: INT n :: RPAREN :: rest -> Ok (Exp_int (- n), rest)
  | MINUS :: rest ->
    (match parse_expr rest with
     | Ok (e, RPAREN :: rest2) -> Ok (Exp_unop (Op_neg, e), rest2)
     | _ -> Fail "bad negation")
  (* not *)
  | NOT :: rest ->
    (match parse_expr rest with
     | Ok (e, RPAREN :: rest2) -> Ok (Exp_unop (Op_not, e), rest2)
     | _ -> Fail "bad not")
  (* if *)
  | IF :: rest ->
    (match parse_expr rest with
     | Ok (e1, THEN :: rest2) ->
       (match parse_expr rest2 with
        | Ok (e2, ELSE :: rest3) ->
          (match parse_expr rest3 with
           | Ok (e3, RPAREN :: rest4) -> Ok (Exp_if (e1, e2, e3), rest4)
           | _ -> Fail "bad if else")
        | _ -> Fail "bad if then")
     | _ -> Fail "bad if cond")
  (* let rec *)
  | LET :: REC :: STRING f :: EQ :: rest ->
    (match parse_expr rest with
     | Ok (e1, IN :: rest2) ->
       (match parse_expr rest2 with
        | Ok (e2, RPAREN :: rest3) -> Ok (Exp_letrec (cl f, e1, e2), rest3)
        | _ -> Fail "bad letrec body")
     | _ -> Fail "bad letrec binding")
  (* let *)
  | LET :: STRING x :: EQ :: rest ->
    (match parse_expr rest with
     | Ok (e1, IN :: rest2) ->
       (match parse_expr rest2 with
        | Ok (e2, RPAREN :: rest3) -> Ok (Exp_let (cl x, e1, e2), rest3)
        | _ -> Fail "bad let body")
     | _ -> Fail "bad let binding")
  (* fun *)
  | FUN :: STRING x :: ARROW :: rest ->
    (match parse_expr rest with
     | Ok (body, RPAREN :: rest2) -> Ok (Exp_fun (cl x, body), rest2)
     | _ -> Fail "bad fun body")
  (* function *)
  | FUNCTION :: rest -> parse_function_cases rest
  (* match *)
  | MATCH :: rest ->
    (match parse_expr rest with
     | Ok (scrut, WITH :: rest2) -> parse_match_cases scrut rest2
     | _ -> Fail "bad match scrutinee")
  (* Constructor with arg: (C e) — or standalone C followed by binop/seq/etc *)
  | STRING c :: rest when is_upper c ->
    let constr_no_arg = Exp_constr (cl c, None) in
    (match parse_expr rest with
     | Ok (arg, RPAREN :: rest2) -> Ok (Exp_constr (cl c, Some arg), rest2)
     | _ -> parse_after_first_expr constr_no_arg rest)
  (* Otherwise: parse first expr, then look at what follows *)
  | _ ->
    (match parse_expr tokens with
     | Ok (e1, rest) -> parse_after_first_expr e1 rest
     | Fail msg -> Fail msg)

(* After first expr in parens, decide what compound form this is *)
and parse_after_first_expr e1 tokens =
  match tokens with
  | RPAREN :: rest -> Ok (e1, rest)
  | COLONCOLON :: rest ->
    (match parse_expr rest with
     | Ok (e2, RPAREN :: rest2) -> Ok (Exp_cons (e1, e2), rest2)
     | _ -> Fail "bad cons")
  | DOT :: STRING f :: RPAREN :: rest -> Ok (Exp_field (e1, cl f), rest)
  | SEMI :: rest ->
    (match parse_expr rest with
     | Ok (e2, RPAREN :: rest2) -> Ok (Exp_seq (e1, e2), rest2)
     | _ -> Fail "bad seq")
  | COMMA :: rest ->
    let rec parse_rest acc toks =
      match parse_expr toks with
      | Ok (e, COMMA :: rest2) -> parse_rest (e :: acc) rest2
      | Ok (e, RPAREN :: rest2) -> Ok (Exp_tuple (List.rev (e :: acc)), rest2)
      | _ -> Fail "bad tuple"
    in parse_rest [e1] rest
  | tok :: _ when token_to_binop tok <> None ->
    let op = match token_to_binop tok with Some o -> o | None -> assert false in
    (match parse_expr (List.tl tokens) with
     | Ok (e2, RPAREN :: rest) -> Ok (Exp_binop (op, e1, e2), rest)
     | _ -> Fail "bad binop rhs")
  | _ ->
    (* Application: (f arg) *)
    (match parse_expr tokens with
     | Ok (e2, RPAREN :: rest) -> Ok (Exp_app (e1, e2), rest)
     | _ -> Fail "bad application")

(* Parse function cases: (function | p -> e | p -> e ...) *)
and parse_function_cases tokens =
  let rec loop acc toks =
    match toks with
    | PIPE :: rest ->
      (match parse_pattern rest with
       | Ok (pat, ARROW :: rest2) ->
         (match parse_expr rest2 with
          | Ok (body, rest3) ->
            let acc' = (pat, body) :: acc in
            (match rest3 with
             | RPAREN :: rest4 -> Ok (Exp_function (List.rev acc'), rest4)
             | PIPE :: _ -> loop acc' rest3
             | _ -> Fail "expected | or ) after function case")
          | Fail msg -> Fail msg)
       | Ok (_, _) -> Fail "expected -> after pattern in function"
       | Fail msg -> Fail msg)
    | RPAREN :: rest -> Ok (Exp_function (List.rev acc), rest)
    | _ -> Fail "expected | or ) in function"
  in loop [] tokens

(* Parse match cases *)
and parse_match_cases scrut tokens =
  let rec loop acc toks =
    match toks with
    | PIPE :: rest ->
      (match parse_pattern rest with
       | Ok (pat, ARROW :: rest2) ->
         (match parse_expr rest2 with
          | Ok (body, rest3) ->
            let acc' = (pat, body) :: acc in
            (match rest3 with
             | RPAREN :: rest4 -> Ok (Exp_match (scrut, List.rev acc'), rest4)
             | PIPE :: _ -> loop acc' rest3
             | _ -> Fail "expected | or ) after match case")
          | Fail msg -> Fail msg)
       | Ok (_, _) -> Fail "expected -> after pattern"
       | Fail msg -> Fail msg)
    | RPAREN :: rest -> Ok (Exp_match (scrut, List.rev acc), rest)
    | _ -> Fail "expected | or ) in match"
  in loop [] tokens

(* Parse a type expression *)
let rec parse_type_expr tokens =
  match tokens with
  | STRING "int" :: rest -> Ok (Ty_int, rest)
  | STRING "bool" :: rest -> Ok (Ty_bool, rest)
  | STRING "unit" :: rest -> Ok (Ty_unit, rest)
  | LPAREN :: rest -> parse_paren_type rest
  | STRING name :: rest -> Ok (Ty_constr (cl name, []), rest)
  | _ -> Fail "cannot parse type"

and parse_paren_type tokens =
  match parse_type_expr tokens with
  | Ok (t1, ARROW :: rest) ->
    (match parse_type_expr rest with
     | Ok (t2, RPAREN :: rest2) -> Ok (Ty_arrow (t1, t2), rest2)
     | _ -> Fail "bad arrow type")
  | Ok (t1, STAR :: rest) ->
    let rec parse_rest acc toks =
      match parse_type_expr toks with
      | Ok (t, STAR :: rest2) -> parse_rest (t :: acc) rest2
      | Ok (t, RPAREN :: rest2) -> Ok (Ty_tuple (List.rev (t :: acc)), rest2)
      | _ -> Fail "bad tuple type"
    in parse_rest [t1] rest
  | Ok (t1, STRING name :: RPAREN :: rest) ->
    Ok (Ty_constr (cl name, [t1]), rest)
  | Ok (t1, COMMA :: rest) ->
    let rec parse_args acc t =
      match parse_type_expr t with
      | Ok (ty, COMMA :: rest2) -> parse_args (ty :: acc) rest2
      | Ok (ty, RPAREN :: STRING name :: RPAREN :: rest2) ->
        Ok (Ty_constr (cl name, List.rev (ty :: acc)), rest2)
      | _ -> Fail "bad multi-arg type constructor"
    in parse_args [t1] rest
  | Ok (t, RPAREN :: rest) -> Ok (t, rest)
  | _ -> Fail "bad parenthesized type"

(* Parse type definition *)
let parse_type_def tokens =
  match tokens with
  | LBRACE :: rest ->
    (* Td_record: { field : type; ... } *)
    let rec parse_fields acc toks =
      match toks with
      | STRING f :: COLON :: rest2 ->
        (match parse_type_expr rest2 with
         | Ok (t, SEMI :: rest3) -> parse_fields ((cl f, t) :: acc) rest3
         | Ok (t, RBRACE :: rest3) -> Ok (Td_record (List.rev ((cl f, t) :: acc)), rest3)
         | _ -> Fail "bad record type field")
      | _ -> Fail "expected field name in record type"
    in parse_fields [] rest
  | _ ->
    let rec parse_variants acc toks =
      match toks with
      | STRING c :: OF :: rest when is_upper c ->
        (match parse_type_expr rest with
         | Ok (t, PIPE :: rest2) -> parse_variants ((cl c, Some t) :: acc) rest2
         | Ok (t, rest2) -> Ok (Td_variant (List.rev ((cl c, Some t) :: acc)), rest2)
         | Fail msg -> Fail msg)
      | STRING c :: PIPE :: rest when is_upper c ->
        parse_variants ((cl c, None) :: acc) rest
      | STRING c :: rest when is_upper c ->
        Ok (Td_variant (List.rev ((cl c, None) :: acc)), rest)
      | _ ->
        if acc = [] then
          match parse_type_expr toks with
          | Ok (t, rest) -> Ok (Td_alias t, rest)
          | Fail msg -> Fail msg
        else Fail "bad variant definition"
    in parse_variants [] tokens

(* Parse a declaration *)
let rec parse_decl tokens =
  match tokens with
  | LET :: REC :: STRING f :: EQ :: rest ->
    (match parse_expr rest with
     | Ok (e, rest2) -> Ok (Decl_letrec (cl f, e), rest2)
     | Fail msg -> Fail msg)
  | LET :: STRING x :: EQ :: rest ->
    (match parse_expr rest with
     | Ok (e, rest2) -> Ok (Decl_let (cl x, e), rest2)
     | Fail msg -> Fail msg)
  | TYPE :: rest ->
    let rec parse_type_params toks =
      match toks with
      | APOSTROPHE :: STRING p :: rest2 ->
        let params, rest3 = parse_type_params rest2 in
        (cl p :: params, rest3)
      | LPAREN :: rest2 ->
        let rec parse_list acc t =
          match t with
          | APOSTROPHE :: STRING p :: COMMA :: rest3 -> parse_list (cl p :: acc) rest3
          | APOSTROPHE :: STRING p :: RPAREN :: rest3 -> (List.rev (cl p :: acc), rest3)
          | _ -> (List.rev acc, t)
        in parse_list [] rest2
      | _ -> ([], toks)
    in
    let params, rest2 = parse_type_params rest in
    (match rest2 with
     | STRING name :: EQ :: rest3 ->
       (match parse_type_def rest3 with
        | Ok (td, rest4) -> Ok (Decl_type (cl name, params, td), rest4)
        | Fail msg -> Fail msg)
     | _ -> Fail "bad type declaration")
  | MODULE :: STRING name :: EQ :: STRUCT :: rest ->
    parse_module_body (cl name) [] rest
  | OPEN :: STRING name :: rest ->
    Ok (Decl_open (cl name), rest)
  | EXCEPTION :: STRING name :: OF :: rest ->
    (match parse_type_expr rest with
     | Ok (t, rest2) -> Ok (Decl_exception (cl name, Some t), rest2)
     | Fail msg -> Fail msg)
  | EXCEPTION :: STRING name :: rest ->
    Ok (Decl_exception (cl name, None), rest)
  | _ ->
    (match parse_expr tokens with
     | Ok (e, rest) -> Ok (Decl_expr e, rest)
     | Fail msg -> Fail msg)

(* Parse module body: decl;; decl;; ... end *)
and parse_module_body name acc tokens =
  match tokens with
  | END :: rest -> Ok (Decl_module (name, List.rev acc), rest)
  | _ ->
    (match parse_decl tokens with
     | Ok (d, SEMISEMI :: rest2) -> parse_module_body name (d :: acc) rest2
     | Ok (d, END :: rest2) -> Ok (Decl_module (name, List.rev (d :: acc)), rest2)
     | Ok (_d, _) -> Fail "expected ;; or end in module body"
     | Fail msg -> Fail msg)

(* Parse a program *)
let parse_program tokens =
  let rec loop acc toks =
    match toks with
    | [] -> Result.Ok (List.rev acc)
    | SEMISEMI :: rest -> loop acc rest
    | _ ->
      match parse_decl toks with
      | Ok (d, rest) ->
        let rest2 = match rest with SEMISEMI :: r -> r | r -> r in
        loop (d :: acc) rest2
      | Fail msg -> Result.Error msg
  in loop [] tokens

(* Main entry point *)
let parse (input : string) : (Interp_extracted.decl list, string) result =
  let tokens = tokenize input in
  parse_program tokens
