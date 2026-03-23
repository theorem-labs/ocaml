(* lexer.ml - [UNTRUSTED] Tokenizer for OCaml subset.
   Validated by PBT: parse(pretty_print(ast)) = ast *)

type token =
  | INT of int
  | STRING of string  (* identifier or keyword *)
  | LPAREN | RPAREN
  | COMMA | SEMI | SEMISEMI | PIPE | UNDERSCORE
  | ARROW    (* -> *)
  | PLUS | MINUS | STAR | SLASH
  | MOD      (* mod *)
  | EQ | NEQ (* = and <> *)
  | LT | LE | GT | GE
  | AMPAMP | PIPEPIPE  (* && and || *)
  | NOT      (* not *)
  | IF | THEN | ELSE
  | LET | REC | IN
  | FUN | MATCH | WITH
  | TYPE | OF
  | TRUE | FALSE
  | APOSTROPHE  (* ' for type params *)
  | EOF

let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_digit c = c >= '0' && c <= '9'
let is_alnum c = is_alpha c || is_digit c || c = '\''

let keyword_or_ident s =
  match s with
  | "if" -> IF | "then" -> THEN | "else" -> ELSE
  | "let" -> LET | "rec" -> REC | "in" -> IN
  | "fun" -> FUN | "match" -> MATCH | "with" -> WITH
  | "type" -> TYPE | "of" -> OF
  | "true" -> TRUE | "false" -> FALSE
  | "not" -> NOT | "mod" -> MOD
  | "_" -> UNDERSCORE
  | s -> STRING s

let tokenize (input : string) : token list =
  let len = String.length input in
  let pos = ref 0 in
  let tokens = ref [] in
  while !pos < len do
    let c = input.[!pos] in
    if c = ' ' || c = '\n' || c = '\r' || c = '\t' then
      incr pos
    else if c = '(' && !pos + 1 < len && input.[!pos + 1] = '*' then begin
      (* Skip comment *)
      pos := !pos + 2;
      let depth = ref 1 in
      while !pos < len && !depth > 0 do
        if !pos + 1 < len && input.[!pos] = '(' && input.[!pos + 1] = '*' then
          (incr depth; pos := !pos + 2)
        else if !pos + 1 < len && input.[!pos] = '*' && input.[!pos + 1] = ')' then
          (decr depth; pos := !pos + 2)
        else incr pos
      done
    end
    else if c = '(' then (tokens := LPAREN :: !tokens; incr pos)
    else if c = ')' then (tokens := RPAREN :: !tokens; incr pos)
    else if c = ',' then (tokens := COMMA :: !tokens; incr pos)
    else if c = ';' && !pos + 1 < len && input.[!pos + 1] = ';' then
      (tokens := SEMISEMI :: !tokens; pos := !pos + 2)
    else if c = ';' then (tokens := SEMI :: !tokens; incr pos)
    else if c = '|' && !pos + 1 < len && input.[!pos + 1] = '|' then
      (tokens := PIPEPIPE :: !tokens; pos := !pos + 2)
    else if c = '|' then (tokens := PIPE :: !tokens; incr pos)
    else if c = '+' then (tokens := PLUS :: !tokens; incr pos)
    else if c = '*' then (tokens := STAR :: !tokens; incr pos)
    else if c = '/' then (tokens := SLASH :: !tokens; incr pos)
    else if c = '=' then (tokens := EQ :: !tokens; incr pos)
    else if c = '<' && !pos + 1 < len && input.[!pos + 1] = '>' then
      (tokens := NEQ :: !tokens; pos := !pos + 2)
    else if c = '<' && !pos + 1 < len && input.[!pos + 1] = '=' then
      (tokens := LE :: !tokens; pos := !pos + 2)
    else if c = '<' then (tokens := LT :: !tokens; incr pos)
    else if c = '>' && !pos + 1 < len && input.[!pos + 1] = '=' then
      (tokens := GE :: !tokens; pos := !pos + 2)
    else if c = '>' then (tokens := GT :: !tokens; incr pos)
    else if c = '&' && !pos + 1 < len && input.[!pos + 1] = '&' then
      (tokens := AMPAMP :: !tokens; pos := !pos + 2)
    else if c = '-' && !pos + 1 < len && input.[!pos + 1] = '>' then
      (tokens := ARROW :: !tokens; pos := !pos + 2)
    else if c = '-' then (tokens := MINUS :: !tokens; incr pos)
    else if c = '\'' then (tokens := APOSTROPHE :: !tokens; incr pos)
    else if is_digit c then begin
      let start = !pos in
      while !pos < len && is_digit input.[!pos] do incr pos done;
      tokens := INT (int_of_string (String.sub input start (!pos - start))) :: !tokens
    end
    else if is_alpha c then begin
      let start = !pos in
      while !pos < len && is_alnum input.[!pos] do incr pos done;
      tokens := keyword_or_ident (String.sub input start (!pos - start)) :: !tokens
    end
    else
      incr pos  (* skip unknown chars *)
  done;
  List.rev !tokens
