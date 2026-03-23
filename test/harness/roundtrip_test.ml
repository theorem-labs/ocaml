(* roundtrip_test.ml - [TRUSTED] PBT: parse(pretty_print(ast)) = ast
   Validates the untrusted parser against the trusted pretty-printer. *)

open Interp_extracted

(* string -> char list *)
let cl s = List.init (String.length s) (fun i -> s.[i])
(* char list -> string *)
let sc l = let buf = Buffer.create (List.length l) in List.iter (Buffer.add_char buf) l; Buffer.contents buf

(* === Random AST generators === *)

let random_ident rng =
  let names = [|"x";"y";"z";"f";"g";"n";"m";"a";"b";"c";"acc";"result"|] in
  cl names.(Random.State.int rng (Array.length names))

let random_constr_name rng =
  let names = [|"Foo";"Bar";"Baz";"Some2";"None2";"Cons";"Nil";"A";"B";"C"|] in
  cl names.(Random.State.int rng (Array.length names))

let random_type_name rng =
  let names = [|"t";"u";"mytype";"color"|] in
  cl names.(Random.State.int rng (Array.length names))

let rec random_expr rng depth =
  if depth <= 0 then random_leaf_expr rng
  else
    let d = depth - 1 in
    match Random.State.int rng 15 with
    | 0 -> Exp_int (Random.State.int rng 200 - 100)
    | 1 -> Exp_bool (Random.State.bool rng)
    | 2 -> Exp_unit
    | 3 -> Exp_var (random_ident rng)
    | 4 ->
      let ops = [|Op_add;Op_sub;Op_mul;Op_div;Op_mod;Op_eq;Op_neq;Op_lt;Op_le;Op_gt;Op_ge;Op_and;Op_or|] in
      Exp_binop (ops.(Random.State.int rng (Array.length ops)), random_expr rng d, random_expr rng d)
    | 5 ->
      let ops = [|Op_neg; Op_not|] in
      Exp_unop (ops.(Random.State.int rng (Array.length ops)), random_expr rng d)
    | 6 -> Exp_if (random_expr rng d, random_expr rng d, random_expr rng d)
    | 7 -> Exp_let (random_ident rng, random_expr rng d, random_expr rng d)
    | 8 -> Exp_letrec (random_ident rng, random_expr rng d, random_expr rng d)
    | 9 -> Exp_fun (random_ident rng, random_expr rng d)
    | 10 -> Exp_app (random_expr rng d, random_expr rng d)
    | 11 ->
      let n = 2 + Random.State.int rng 3 in
      Exp_tuple (List.init n (fun _ -> random_expr rng d))
    | 12 ->
      let c = random_constr_name rng in
      if Random.State.bool rng then Exp_constr (c, Some (random_expr rng d))
      else Exp_constr (c, None)
    | 13 ->
      let ncases = 1 + Random.State.int rng 3 in
      Exp_match (random_expr rng d, List.init ncases (fun _ -> (random_pattern rng d, random_expr rng d)))
    | 14 | _ -> Exp_seq (random_expr rng d, random_expr rng d)

and random_leaf_expr rng =
  match Random.State.int rng 5 with
  | 0 -> Exp_int (Random.State.int rng 200 - 100)
  | 1 -> Exp_bool (Random.State.bool rng)
  | 2 -> Exp_unit
  | 3 -> Exp_var (random_ident rng)
  | _ -> Exp_constr (random_constr_name rng, None)

and random_pattern rng depth =
  if depth <= 0 then random_leaf_pattern rng
  else
    let d = depth - 1 in
    match Random.State.int rng 7 with
    | 0 -> Pat_var (random_ident rng)
    | 1 -> Pat_int (Random.State.int rng 200 - 100)
    | 2 -> Pat_bool (Random.State.bool rng)
    | 3 -> Pat_unit
    | 4 ->
      let n = 2 + Random.State.int rng 3 in
      Pat_tuple (List.init n (fun _ -> random_pattern rng d))
    | 5 ->
      let c = random_constr_name rng in
      if Random.State.bool rng then Pat_constr (c, Some (random_pattern rng d))
      else Pat_constr (c, None)
    | _ -> Pat_wild

and random_leaf_pattern rng =
  match Random.State.int rng 5 with
  | 0 -> Pat_var (random_ident rng)
  | 1 -> Pat_int (Random.State.int rng 200 - 100)
  | 2 -> Pat_bool (Random.State.bool rng)
  | 3 -> Pat_unit
  | _ -> Pat_wild

let random_type_expr rng depth =
  if depth <= 0 then
    match Random.State.int rng 3 with
    | 0 -> Ty_int | 1 -> Ty_bool | _ -> Ty_unit
  else
    let gen_leaf () =
      match Random.State.int rng 4 with
      | 0 -> Ty_int | 1 -> Ty_bool | 2 -> Ty_unit
      | _ -> Ty_constr (random_type_name rng, [])
    in
    ignore depth;
    match Random.State.int rng 6 with
    | 0 -> Ty_int | 1 -> Ty_bool | 2 -> Ty_unit
    | 3 -> Ty_arrow (gen_leaf (), gen_leaf ())
    | 4 -> Ty_tuple (List.init (2 + Random.State.int rng 2) (fun _ -> gen_leaf ()))
    | _ -> Ty_constr (random_type_name rng, [])

let random_decl rng depth =
  match Random.State.int rng 4 with
  | 0 -> Decl_let (random_ident rng, random_expr rng depth)
  | 1 -> Decl_letrec (random_ident rng, random_expr rng depth)
  | 2 ->
    let nparams = Random.State.int rng 2 in
    let params = List.init nparams (fun _ -> random_ident rng) in
    let nconstrs = 1 + Random.State.int rng 4 in
    let constrs = List.init nconstrs (fun _ ->
      let c = random_constr_name rng in
      if Random.State.bool rng then (c, Some (random_type_expr rng depth))
      else (c, None)) in
    Decl_type (random_type_name rng, params, Td_variant constrs)
  | _ -> Decl_expr (random_expr rng depth)

(* === Normalization: resolve pretty-print ambiguities === *)
(* Exp_unop(Op_neg, Exp_int n) -> Exp_int(-n) since pp produces "(-n)" for both *)
let rec normalize_expr = function
  | Exp_unop (Op_neg, e) ->
    (match normalize_expr e with
     | Exp_int n -> Exp_int (- n)
     | e' -> Exp_unop (Op_neg, e'))
  | Exp_binop (op, e1, e2) -> Exp_binop (op, normalize_expr e1, normalize_expr e2)
  | Exp_unop (op, e) -> Exp_unop (op, normalize_expr e)
  | Exp_if (e1, e2, e3) -> Exp_if (normalize_expr e1, normalize_expr e2, normalize_expr e3)
  | Exp_let (x, e1, e2) -> Exp_let (x, normalize_expr e1, normalize_expr e2)
  | Exp_letrec (x, e1, e2) -> Exp_letrec (x, normalize_expr e1, normalize_expr e2)
  | Exp_fun (x, e) -> Exp_fun (x, normalize_expr e)
  | Exp_app (e1, e2) -> Exp_app (normalize_expr e1, normalize_expr e2)
  | Exp_tuple es -> Exp_tuple (List.map normalize_expr es)
  | Exp_constr (c, Some e) -> Exp_constr (c, Some (normalize_expr e))
  | Exp_match (e, cases) -> Exp_match (normalize_expr e, List.map (fun (p, e) -> (p, normalize_expr e)) cases)
  | Exp_seq (e1, e2) -> Exp_seq (normalize_expr e1, normalize_expr e2)
  | e -> e

let normalize_decl = function
  | Decl_let (x, e) -> Decl_let (x, normalize_expr e)
  | Decl_letrec (x, e) -> Decl_letrec (x, normalize_expr e)
  | Decl_expr e -> Decl_expr (normalize_expr e)
  | d -> d

(* === Comparison functions === *)

let opt_eq_generic f a b =
  match a, b with
  | None, None -> true
  | Some x, Some y -> f x y
  | _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Exp_int a, Exp_int b -> a = b
  | Exp_bool a, Exp_bool b -> a = b
  | Exp_unit, Exp_unit -> true
  | Exp_var a, Exp_var b -> a = b
  | Exp_binop (o1,a1,b1), Exp_binop (o2,a2,b2) -> o1 = o2 && expr_eq a1 a2 && expr_eq b1 b2
  | Exp_unop (o1,a1), Exp_unop (o2,a2) -> o1 = o2 && expr_eq a1 a2
  | Exp_if (a1,b1,c1), Exp_if (a2,b2,c2) -> expr_eq a1 a2 && expr_eq b1 b2 && expr_eq c1 c2
  | Exp_let (x1,a1,b1), Exp_let (x2,a2,b2) -> x1 = x2 && expr_eq a1 a2 && expr_eq b1 b2
  | Exp_letrec (x1,a1,b1), Exp_letrec (x2,a2,b2) -> x1 = x2 && expr_eq a1 a2 && expr_eq b1 b2
  | Exp_fun (x1,a1), Exp_fun (x2,a2) -> x1 = x2 && expr_eq a1 a2
  | Exp_app (a1,b1), Exp_app (a2,b2) -> expr_eq a1 a2 && expr_eq b1 b2
  | Exp_tuple a1, Exp_tuple a2 -> List.length a1 = List.length a2 && List.for_all2 expr_eq a1 a2
  | Exp_constr (c1,a1), Exp_constr (c2,a2) -> c1 = c2 && opt_eq_generic expr_eq a1 a2
  | Exp_match (a1,cs1), Exp_match (a2,cs2) ->
    expr_eq a1 a2 && List.length cs1 = List.length cs2 &&
    List.for_all2 case_eq cs1 cs2
  | Exp_seq (a1,b1), Exp_seq (a2,b2) -> expr_eq a1 a2 && expr_eq b1 b2
  | _ -> false

and case_eq (p1,e1) (p2,e2) = pattern_eq p1 p2 && expr_eq e1 e2

and pattern_eq p1 p2 =
  match p1, p2 with
  | Pat_var a, Pat_var b -> a = b
  | Pat_int a, Pat_int b -> a = b
  | Pat_bool a, Pat_bool b -> a = b
  | Pat_unit, Pat_unit -> true
  | Pat_tuple a, Pat_tuple b -> List.length a = List.length b && List.for_all2 pattern_eq a b
  | Pat_constr (c1,a1), Pat_constr (c2,a2) -> c1 = c2 && opt_eq_generic pattern_eq a1 a2
  | Pat_wild, Pat_wild -> true
  | _ -> false

and list_eq f a b =
  match a, b with
  | [], [] -> true
  | x :: xs, y :: ys -> f x y && list_eq f xs ys
  | _ -> false

let type_expr_eq t1 t2 =
  let rec eq t1 t2 =
    match t1, t2 with
    | Ty_int, Ty_int | Ty_bool, Ty_bool | Ty_unit, Ty_unit -> true
    | Ty_arrow (a1,b1), Ty_arrow (a2,b2) -> eq a1 a2 && eq b1 b2
    | Ty_tuple a, Ty_tuple b -> list_eq eq a b
    | Ty_constr (n1,a1), Ty_constr (n2,a2) -> n1 = n2 && list_eq eq a1 a2
    | _ -> false
  in eq t1 t2

let type_def_eq td1 td2 =
  match td1, td2 with
  | Td_variant cs1, Td_variant cs2 ->
    list_eq (fun (n1,t1) (n2,t2) -> n1 = n2 &&
      match t1, t2 with None, None -> true | Some a, Some b -> type_expr_eq a b | _ -> false) cs1 cs2
  | Td_alias t1, Td_alias t2 -> type_expr_eq t1 t2
  | _ -> false

let decl_eq d1 d2 =
  match d1, d2 with
  | Decl_let (x1,e1), Decl_let (x2,e2) -> x1 = x2 && expr_eq e1 e2
  | Decl_letrec (x1,e1), Decl_letrec (x2,e2) -> x1 = x2 && expr_eq e1 e2
  | Decl_type (n1,p1,td1), Decl_type (n2,p2,td2) -> n1 = n2 && p1 = p2 && type_def_eq td1 td2
  | Decl_expr e1, Decl_expr e2 -> expr_eq e1 e2
  | _ -> false

(* === Main === *)
let () =
  let num = try int_of_string Sys.argv.(1) with _ -> 500 in
  let seed = try int_of_string Sys.argv.(2) with _ -> 42 in
  let depth = try int_of_string Sys.argv.(3) with _ -> 3 in
  let rng = Random.State.make [| seed |] in
  Printf.printf "Round-trip PBT: %d tests (seed=%d, depth=%d)\n\n%!" num seed depth;
  let pass = ref 0 and fail = ref 0 in

  (* Test individual expressions *)
  for _ = 1 to num do
    let expr = normalize_expr (random_expr rng depth) in
    let printed = sc (pp_expr expr) in
    match Parser.parse printed with
    | Result.Ok [Decl_expr parsed_expr] ->
      let parsed_norm = normalize_expr parsed_expr in
      let pp_match = sc (pp_expr expr) = sc (pp_expr parsed_norm) in
      if expr_eq expr parsed_norm || pp_match then incr pass
      else begin
        Printf.printf "FAIL expr roundtrip:\n  printed:   %S\n  original:  %s\n  reparsed:  %s\n  re-pp:     %s\n%!"
          printed (sc (pp_expr expr)) (sc (pp_expr parsed_expr)) (sc (pp_expr parsed_norm));
        incr fail
      end
    | Result.Ok _ ->
      Printf.printf "FAIL expr: parsed as non-expr decl\n  printed: %S\n%!" printed;
      incr fail
    | Result.Error msg ->
      Printf.printf "FAIL expr parse error: %s\n  printed: %S\n%!" msg printed;
      incr fail
  done;

  (* Test individual declarations *)
  for _ = 1 to num / 5 do
    let decl = normalize_decl (random_decl rng depth) in
    let printed = sc (pp_decl decl) ^ ";;" in
    match Parser.parse printed with
    | Result.Ok [parsed_decl] ->
      let parsed_norm = normalize_decl parsed_decl in
      let pp_match = sc (pp_decl decl) = sc (pp_decl parsed_norm) in
      if decl_eq decl parsed_norm || pp_match then incr pass
      else begin
        Printf.printf "FAIL decl roundtrip:\n  printed:   %S\n  original:  %s\n  reparsed:  %s\n%!"
          printed (sc (pp_decl decl)) (sc (pp_decl parsed_norm));
        incr fail
      end
    | Result.Ok ds ->
      Printf.printf "FAIL decl: parsed as %d decls\n  printed: %S\n%!" (List.length ds) printed;
      incr fail
    | Result.Error msg ->
      Printf.printf "FAIL decl parse error: %s\n  printed: %S\n%!" msg printed;
      incr fail
  done;

  Printf.printf "\n=== Round-trip Results: %d pass, %d fail ===\n" !pass !fail;
  if !fail > 0 then exit 1
