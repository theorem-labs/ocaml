(* roundtrip_test.ml - [TRUSTED] PBT: parse(pretty_print(ast)) = ast
   Validates the untrusted parser against the trusted pretty-printer.
   Migrated to QCheck. *)

open Interp_extracted
open Test_common

(* === QCheck AST generators === *)

let gen_ident : char list QCheck.Gen.t =
  let names = [|"x";"y";"z";"f";"g";"n";"m";"a";"b";"c";"acc";"result"|] in
  QCheck.Gen.(map cl (oneofa names))

let gen_constr_name : char list QCheck.Gen.t =
  let names = [|"Foo";"Bar";"Baz";"Some2";"None2";"Cons";"Nil2";"A";"B";"C"|] in
  QCheck.Gen.(map cl (oneofa names))

let gen_type_name : char list QCheck.Gen.t =
  let names = [|"t";"u";"mytype";"color"|] in
  QCheck.Gen.(map cl (oneofa names))

let gen_field_name : char list QCheck.Gen.t =
  let names = [|"name";"age";"value";"key";"data"|] in
  QCheck.Gen.(map cl (oneofa names))

let gen_module_name : char list QCheck.Gen.t =
  let names = [|"M";"N";"Foo";"Bar"|] in
  QCheck.Gen.(map cl (oneofa names))

(* Generate simple strings that don't contain double-quotes or backslashes *)
let gen_simple_string : char list QCheck.Gen.t =
  let words = [|"hello";"world";"foo";"bar";"test";"abc";"123"|] in
  QCheck.Gen.(map cl (oneofa words))

let rec gen_expr depth : expr QCheck.Gen.t =
  let open QCheck.Gen in
  if depth <= 0 then gen_leaf_expr
  else
    let d = depth - 1 in
    oneof [
      (* 0: int *)
      map (fun n -> Exp_int n) (int_range (-100) 99);
      (* 1: bool *)
      map (fun b -> Exp_bool b) bool;
      (* 2: unit *)
      pure Exp_unit;
      (* 3: var *)
      map (fun x -> Exp_var x) gen_ident;
      (* 4: binop *)
      (let ops = [|Op_add;Op_sub;Op_mul;Op_div;Op_mod;Op_eq;Op_neq;Op_lt;Op_le;Op_gt;Op_ge;Op_and;Op_or|] in
       map3 (fun op e1 e2 -> Exp_binop (op, e1, e2)) (oneofa ops) (gen_expr d) (gen_expr d));
      (* 5: unop *)
      (let ops = [|Op_neg; Op_not|] in
       map2 (fun op e -> Exp_unop (op, e)) (oneofa ops) (gen_expr d));
      (* 6: if *)
      map3 (fun e1 e2 e3 -> Exp_if (e1, e2, e3)) (gen_expr d) (gen_expr d) (gen_expr d);
      (* 7: let *)
      map3 (fun x e1 e2 -> Exp_let (x, e1, e2)) gen_ident (gen_expr d) (gen_expr d);
      (* 8: letrec *)
      map3 (fun x e1 e2 -> Exp_letrec (x, e1, e2)) gen_ident (gen_expr d) (gen_expr d);
      (* 9: fun *)
      map2 (fun x e -> Exp_fun (x, e)) gen_ident (gen_expr d);
      (* 10: app *)
      map2 (fun e1 e2 -> Exp_app (e1, e2)) (gen_expr d) (gen_expr d);
      (* 11: tuple *)
      (int_range 2 4 >>= fun n ->
       list_repeat n (gen_expr d) >|= fun es -> Exp_tuple es);
      (* 12: constr *)
      map2 (fun c opt -> Exp_constr (c, opt)) gen_constr_name
        (oneof [map (fun e -> Some e) (gen_expr d); pure None]);
      (* 13: match *)
      (int_range 1 3 >>= fun ncases ->
       map2 (fun e cases -> Exp_match (e, cases)) (gen_expr d)
         (list_repeat ncases (map2 (fun p e -> (p, e)) (gen_pattern d) (gen_expr d))));
      (* 14: seq *)
      map2 (fun e1 e2 -> Exp_seq (e1, e2)) (gen_expr d) (gen_expr d);
      (* 15: nil *)
      pure Exp_nil;
      (* 16: cons *)
      map2 (fun e1 e2 -> Exp_cons (e1, e2)) (gen_expr d) (gen_expr d);
      (* 17: string *)
      map (fun s -> Exp_string s) gen_simple_string;
      (* 18: function *)
      (int_range 1 3 >>= fun ncases ->
       list_repeat ncases (map2 (fun p e -> (p, e)) (gen_pattern d) (gen_expr d))
       >|= fun cases -> Exp_function cases);
      (* 19: record *)
      (int_range 1 3 >>= fun nfields ->
       list_repeat nfields (map2 (fun f e -> (f, e)) gen_field_name (gen_expr d))
       >|= fun fields -> Exp_record fields);
      (* 20: field access *)
      map2 (fun e f -> Exp_field (e, f)) (gen_expr d) gen_field_name;
    ]

and gen_leaf_expr : expr QCheck.Gen.t =
  let open QCheck.Gen in
  oneof [
    map (fun n -> Exp_int n) (int_range (-100) 99);
    map (fun b -> Exp_bool b) bool;
    pure Exp_unit;
    map (fun x -> Exp_var x) gen_ident;
    map (fun c -> Exp_constr (c, None)) gen_constr_name;
    pure Exp_nil;
    map (fun s -> Exp_string s) gen_simple_string;
  ]

and gen_pattern depth : pattern QCheck.Gen.t =
  let open QCheck.Gen in
  if depth <= 0 then gen_leaf_pattern
  else
    let d = depth - 1 in
    oneof [
      map (fun x -> Pat_var x) gen_ident;
      map (fun n -> Pat_int n) (int_range (-100) 99);
      map (fun b -> Pat_bool b) bool;
      pure Pat_unit;
      (int_range 2 4 >>= fun n ->
       list_repeat n (gen_pattern d) >|= fun ps -> Pat_tuple ps);
      map2 (fun c opt -> Pat_constr (c, opt)) gen_constr_name
        (oneof [map (fun p -> Some p) (gen_pattern d); pure None]);
      pure Pat_wild;
      (* Pat_or *)
      map2 (fun p1 p2 -> Pat_or (p1, p2)) (gen_pattern d) (gen_pattern d);
      (* Pat_record *)
      (int_range 1 3 >>= fun nfields ->
       list_repeat nfields (map2 (fun f p -> (f, p)) gen_field_name (gen_pattern d))
       >|= fun fields -> Pat_record fields);
      (* Pat_nil *)
      pure Pat_nil;
      (* Pat_cons *)
      map2 (fun p1 p2 -> Pat_cons (p1, p2)) (gen_pattern d) (gen_pattern d);
    ]

and gen_leaf_pattern : pattern QCheck.Gen.t =
  let open QCheck.Gen in
  oneof [
    map (fun x -> Pat_var x) gen_ident;
    map (fun n -> Pat_int n) (int_range (-100) 99);
    map (fun b -> Pat_bool b) bool;
    pure Pat_unit;
    pure Pat_wild;
    pure Pat_nil;
  ]

let gen_type_expr : type_expr QCheck.Gen.t =
  let open QCheck.Gen in
  let gen_leaf () =
    oneof [pure Ty_int; pure Ty_bool; pure Ty_unit;
           map (fun n -> Ty_constr (n, [])) gen_type_name]
  in
  oneof [
    pure Ty_int; pure Ty_bool; pure Ty_unit;
    map2 (fun a b -> Ty_arrow (a, b)) (gen_leaf ()) (gen_leaf ());
    (int_range 2 3 >>= fun n ->
     list_repeat n (gen_leaf ()) >|= fun ts -> Ty_tuple ts);
    map (fun n -> Ty_constr (n, [])) gen_type_name;
  ]

let gen_type_def : type_def QCheck.Gen.t =
  let open QCheck.Gen in
  oneof [
    (* Td_variant *)
    (int_range 1 4 >>= fun nconstrs ->
     list_repeat nconstrs
       (map2 (fun c opt -> (c, opt)) gen_constr_name
         (oneof [map (fun t -> Some t) gen_type_expr; pure None]))
     >|= fun constrs -> Td_variant constrs);
    (* Td_alias *)
    map (fun t -> Td_alias t) gen_type_expr;
    (* Td_record *)
    (int_range 1 3 >>= fun nfields ->
     list_repeat nfields (map2 (fun f t -> (f, t)) gen_field_name gen_type_expr)
     >|= fun fields -> Td_record fields);
  ]

let rec gen_decl depth : decl QCheck.Gen.t =
  let open QCheck.Gen in
  if depth <= 0 then
    oneof [
      map2 (fun x e -> Decl_let (x, e)) gen_ident (gen_expr 1);
      map (fun e -> Decl_expr e) (gen_expr 1);
      map (fun n -> Decl_open n) gen_module_name;
    ]
  else
    oneof [
      map2 (fun x e -> Decl_let (x, e)) gen_ident (gen_expr depth);
      map2 (fun x e -> Decl_letrec (x, e)) gen_ident (gen_expr depth);
      (int_range 0 1 >>= fun nparams ->
       map3 (fun name params td -> Decl_type (name, params, td))
         gen_type_name
         (list_repeat nparams gen_ident)
         gen_type_def);
      map (fun e -> Decl_expr e) (gen_expr depth);
      (* Decl_open *)
      map (fun n -> Decl_open n) gen_module_name;
      (* Decl_exception *)
      map2 (fun n t -> Decl_exception (n, t)) gen_constr_name
        (oneof [map (fun t -> Some t) gen_type_expr; pure None]);
      (* Decl_module *)
      (int_range 1 3 >>= fun ndecls ->
       map2 (fun name ds -> Decl_module (name, ds)) gen_module_name
         (list_repeat ndecls (gen_decl (depth - 1))));
    ]

(* === Normalization: resolve pretty-print ambiguities === *)
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
  | Exp_app (e1, e2) ->
    let e1' = normalize_expr e1 in
    let e2' = normalize_expr e2 in
    (* (C arg) pretty-prints the same as Constr(C, Some(arg)) *)
    (match e1' with
     | Exp_constr (c, None) -> Exp_constr (c, Some e2')
     | _ -> Exp_app (e1', e2'))
  | Exp_tuple es -> Exp_tuple (List.map normalize_expr es)
  | Exp_constr (c, Some e) -> Exp_constr (c, Some (normalize_expr e))
  | Exp_match (e, cases) -> Exp_match (normalize_expr e, List.map (fun (p, e) -> (p, normalize_expr e)) cases)
  | Exp_seq (e1, e2) -> Exp_seq (normalize_expr e1, normalize_expr e2)
  | Exp_cons (e1, e2) -> Exp_cons (normalize_expr e1, normalize_expr e2)
  | Exp_record fields -> Exp_record (List.map (fun (f, e) -> (f, normalize_expr e)) fields)
  | Exp_field (e, f) -> Exp_field (normalize_expr e, f)
  | Exp_function cases -> Exp_function (List.map (fun (p, e) -> (p, normalize_expr e)) cases)
  | e -> e

let rec normalize_decl = function
  | Decl_let (x, e) -> Decl_let (x, normalize_expr e)
  | Decl_letrec (x, e) -> Decl_letrec (x, normalize_expr e)
  | Decl_expr e -> Decl_expr (normalize_expr e)
  | Decl_module (n, ds) -> Decl_module (n, List.map normalize_decl ds)
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
  | Exp_nil, Exp_nil -> true
  | Exp_cons (a1,b1), Exp_cons (a2,b2) -> expr_eq a1 a2 && expr_eq b1 b2
  | Exp_string a, Exp_string b -> a = b
  | Exp_function cs1, Exp_function cs2 ->
    List.length cs1 = List.length cs2 && List.for_all2 case_eq cs1 cs2
  | Exp_record fs1, Exp_record fs2 ->
    List.length fs1 = List.length fs2 &&
    List.for_all2 (fun (n1,e1) (n2,e2) -> n1 = n2 && expr_eq e1 e2) fs1 fs2
  | Exp_field (a1,f1), Exp_field (a2,f2) -> expr_eq a1 a2 && f1 = f2
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
  | Pat_or (a1,b1), Pat_or (a2,b2) -> pattern_eq a1 a2 && pattern_eq b1 b2
  | Pat_record fs1, Pat_record fs2 ->
    List.length fs1 = List.length fs2 &&
    List.for_all2 (fun (n1,p1) (n2,p2) -> n1 = n2 && pattern_eq p1 p2) fs1 fs2
  | Pat_nil, Pat_nil -> true
  | Pat_cons (a1,b1), Pat_cons (a2,b2) -> pattern_eq a1 a2 && pattern_eq b1 b2
  | _ -> false

let rec list_eq f a b =
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
  | Td_record fs1, Td_record fs2 ->
    list_eq (fun (n1,t1) (n2,t2) -> n1 = n2 && type_expr_eq t1 t2) fs1 fs2
  | _ -> false

let rec decl_eq d1 d2 =
  match d1, d2 with
  | Decl_let (x1,e1), Decl_let (x2,e2) -> x1 = x2 && expr_eq e1 e2
  | Decl_letrec (x1,e1), Decl_letrec (x2,e2) -> x1 = x2 && expr_eq e1 e2
  | Decl_type (n1,p1,td1), Decl_type (n2,p2,td2) -> n1 = n2 && p1 = p2 && type_def_eq td1 td2
  | Decl_expr e1, Decl_expr e2 -> expr_eq e1 e2
  | Decl_module (n1,ds1), Decl_module (n2,ds2) ->
    n1 = n2 && List.length ds1 = List.length ds2 && List.for_all2 decl_eq ds1 ds2
  | Decl_open n1, Decl_open n2 -> n1 = n2
  | Decl_exception (n1,t1), Decl_exception (n2,t2) ->
    n1 = n2 && opt_eq_generic type_expr_eq t1 t2
  | _ -> false

(* === Debug dump === *)
let rec dump_expr = function
  | Exp_int n -> Printf.sprintf "Int(%d)" n
  | Exp_bool b -> Printf.sprintf "Bool(%b)" b
  | Exp_unit -> "Unit"
  | Exp_var x -> Printf.sprintf "Var(%s)" (sc x)
  | Exp_binop (_, e1, e2) -> Printf.sprintf "Binop(%s,%s)" (dump_expr e1) (dump_expr e2)
  | Exp_unop (_, e) -> Printf.sprintf "Unop(%s)" (dump_expr e)
  | Exp_if (e1, e2, e3) -> Printf.sprintf "If(%s,%s,%s)" (dump_expr e1) (dump_expr e2) (dump_expr e3)
  | Exp_let (x, e1, e2) -> Printf.sprintf "Let(%s,%s,%s)" (sc x) (dump_expr e1) (dump_expr e2)
  | Exp_letrec (x, e1, e2) -> Printf.sprintf "Letrec(%s,%s,%s)" (sc x) (dump_expr e1) (dump_expr e2)
  | Exp_fun (x, e) -> Printf.sprintf "Fun(%s,%s)" (sc x) (dump_expr e)
  | Exp_app (e1, e2) -> Printf.sprintf "App(%s,%s)" (dump_expr e1) (dump_expr e2)
  | Exp_tuple es -> Printf.sprintf "Tuple(%s)" (String.concat "," (List.map dump_expr es))
  | Exp_constr (c, None) -> Printf.sprintf "Constr(%s,None)" (sc c)
  | Exp_constr (c, Some e) -> Printf.sprintf "Constr(%s,Some(%s))" (sc c) (dump_expr e)
  | Exp_match (e, cs) -> Printf.sprintf "Match(%s,[%s])" (dump_expr e) (String.concat ";" (List.map (fun (p,e) -> Printf.sprintf "(%s,%s)" (dump_pat p) (dump_expr e)) cs))
  | Exp_seq (e1, e2) -> Printf.sprintf "Seq(%s,%s)" (dump_expr e1) (dump_expr e2)
  | Exp_nil -> "Nil"
  | Exp_cons (e1, e2) -> Printf.sprintf "Cons(%s,%s)" (dump_expr e1) (dump_expr e2)
  | Exp_string s -> Printf.sprintf "String(%s)" (sc s)
  | Exp_function cs -> Printf.sprintf "Function([%s])" (String.concat ";" (List.map (fun (p,e) -> Printf.sprintf "(%s,%s)" (dump_pat p) (dump_expr e)) cs))
  | Exp_record fs -> Printf.sprintf "Record([%s])" (String.concat ";" (List.map (fun (f,e) -> Printf.sprintf "(%s,%s)" (sc f) (dump_expr e)) fs))
  | Exp_field (e, f) -> Printf.sprintf "Field(%s,%s)" (dump_expr e) (sc f)
and dump_pat = function
  | Pat_var x -> Printf.sprintf "PVar(%s)" (sc x)
  | Pat_int n -> Printf.sprintf "PInt(%d)" n
  | Pat_bool b -> Printf.sprintf "PBool(%b)" b
  | Pat_unit -> "PUnit"
  | Pat_tuple ps -> Printf.sprintf "PTuple(%s)" (String.concat "," (List.map dump_pat ps))
  | Pat_constr (c, None) -> Printf.sprintf "PConstr(%s,None)" (sc c)
  | Pat_constr (c, Some p) -> Printf.sprintf "PConstr(%s,Some(%s))" (sc c) (dump_pat p)
  | Pat_wild -> "PWild"
  | Pat_or (p1, p2) -> Printf.sprintf "POr(%s,%s)" (dump_pat p1) (dump_pat p2)
  | Pat_record fs -> Printf.sprintf "PRecord([%s])" (String.concat ";" (List.map (fun (f,p) -> Printf.sprintf "(%s,%s)" (sc f) (dump_pat p)) fs))
  | Pat_nil -> "PNil"
  | Pat_cons (p1, p2) -> Printf.sprintf "PCons(%s,%s)" (dump_pat p1) (dump_pat p2)

let dump_decl = function
  | Decl_let (x, e) -> Printf.sprintf "Let(%s,%s)" (sc x) (dump_expr e)
  | Decl_letrec (x, e) -> Printf.sprintf "Letrec(%s,%s)" (sc x) (dump_expr e)
  | Decl_type (n, ps, _td) -> Printf.sprintf "Type(%s,[%s],...)" (sc n) (String.concat "," (List.map sc ps))
  | Decl_expr e -> Printf.sprintf "Expr(%s)" (dump_expr e)
  | Decl_module (n, _ds) -> Printf.sprintf "Module(%s,...)" (sc n)
  | Decl_open n -> Printf.sprintf "Open(%s)" (sc n)
  | Decl_exception (n, _) -> Printf.sprintf "Exception(%s,...)" (sc n)

(* === QCheck tests === *)

let depth = 3

let expr_roundtrip_test =
  QCheck.Test.make ~name:"expr round-trip: parse(pp(e)) = e" ~count:1000
    (QCheck.make (gen_expr depth) ~print:(fun e ->
       let printed = sc (pp_expr e) in
       let norm = normalize_expr e in
       let printed_norm = sc (pp_expr norm) in
       Printf.sprintf "original pp: %s\nnormalized pp: %s" printed printed_norm))
    (fun expr ->
       let expr = normalize_expr expr in
       let printed = sc (pp_expr expr) in
       match Parser.parse printed with
       | Result.Ok [Decl_expr parsed_expr] ->
         let parsed_norm = normalize_expr parsed_expr in
         if not (expr_eq expr parsed_norm) then
           (Printf.eprintf "AST MISMATCH\npp(original):  %s\npp(parsed):    %s\ndump(orig):    %s\ndump(parsed):  %s\n%!"
              (sc (pp_expr expr)) (sc (pp_expr parsed_norm))
              (dump_expr expr) (dump_expr parsed_norm);
            false)
         else true
       | Result.Ok decls ->
         Printf.eprintf "WRONG DECLS (got %d)\n%!" (List.length decls);
         false
       | Result.Error msg ->
         Printf.eprintf "PARSE ERROR on: %s\nerror: %s\n%!" printed msg;
         false)

let decl_roundtrip_test =
  QCheck.Test.make ~name:"decl round-trip: parse(pp(d)) = d" ~count:300
    (QCheck.make (gen_decl depth) ~print:(fun d ->
       let printed = sc (pp_decl d) in
       let norm = normalize_decl d in
       let printed_norm = sc (pp_decl norm) in
       Printf.sprintf "original pp: %s\nnormalized pp: %s" printed printed_norm))
    (fun decl ->
       let decl = normalize_decl decl in
       let printed = sc (pp_decl decl) ^ ";;" in
       match Parser.parse printed with
       | Result.Ok [parsed_decl] ->
         let parsed_norm = normalize_decl parsed_decl in
         if not (decl_eq decl parsed_norm) then
           (Printf.eprintf "DECL AST MISMATCH\npp(original):  %s\npp(parsed):    %s\ndump(orig):    %s\ndump(parsed):  %s\n%!"
              (sc (pp_decl decl)) (sc (pp_decl parsed_norm))
              (dump_decl decl) (dump_decl parsed_norm);
            false)
         else true
       | Result.Ok decls ->
         Printf.eprintf "WRONG DECL COUNT (got %d)\nfor: %s\n%!" (List.length decls) printed;
         false
       | Result.Error msg ->
         Printf.eprintf "DECL PARSE ERROR on: %s\nerror: %s\n%!" printed msg;
         false)

let () =
  exit (QCheck_base_runner.run_tests ~verbose:true [expr_roundtrip_test; decl_roundtrip_test])
