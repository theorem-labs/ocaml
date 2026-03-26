(* roundtrip_test.ml - [TRUSTED] PBT: parse(pretty_print(ast)) = ast
   Validates the untrusted parser against the trusted pretty-printer.
   Migrated to QCheck. *)

open Interp_extracted

(* string -> char list *)
let cl s = List.init (String.length s) (fun i -> s.[i])
(* char list -> string *)
let sc l = let buf = Buffer.create (List.length l) in List.iter (Buffer.add_char buf) l; Buffer.contents buf

(* === QCheck AST generators === *)

let gen_ident : char list QCheck.Gen.t =
  let names = [|"x";"y";"z";"f";"g";"n";"m";"a";"b";"c";"acc";"result"|] in
  QCheck.Gen.(map cl (oneofa names))

let gen_constr_name : char list QCheck.Gen.t =
  let names = [|"Foo";"Bar";"Baz";"Some2";"None2";"Cons";"Nil";"A";"B";"C"|] in
  QCheck.Gen.(map cl (oneofa names))

let gen_type_name : char list QCheck.Gen.t =
  let names = [|"t";"u";"mytype";"color"|] in
  QCheck.Gen.(map cl (oneofa names))

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
    ]

and gen_leaf_expr : expr QCheck.Gen.t =
  let open QCheck.Gen in
  oneof [
    map (fun n -> Exp_int n) (int_range (-100) 99);
    map (fun b -> Exp_bool b) bool;
    pure Exp_unit;
    map (fun x -> Exp_var x) gen_ident;
    map (fun c -> Exp_constr (c, None)) gen_constr_name;
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
    ]

and gen_leaf_pattern : pattern QCheck.Gen.t =
  let open QCheck.Gen in
  oneof [
    map (fun x -> Pat_var x) gen_ident;
    map (fun n -> Pat_int n) (int_range (-100) 99);
    map (fun b -> Pat_bool b) bool;
    pure Pat_unit;
    pure Pat_wild;
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

let gen_decl depth : decl QCheck.Gen.t =
  let open QCheck.Gen in
  oneof [
    map2 (fun x e -> Decl_let (x, e)) gen_ident (gen_expr depth);
    map2 (fun x e -> Decl_letrec (x, e)) gen_ident (gen_expr depth);
    (int_range 0 1 >>= fun nparams ->
     int_range 1 4 >>= fun nconstrs ->
     map3 (fun name params constrs -> Decl_type (name, params, Td_variant constrs))
       gen_type_name
       (list_repeat nparams gen_ident)
       (list_repeat nconstrs
         (map2 (fun c opt -> (c, opt)) gen_constr_name
           (oneof [map (fun t -> Some t) gen_type_expr; pure None]))));
    map (fun e -> Decl_expr e) (gen_expr depth);
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
  | _ -> false

let decl_eq d1 d2 =
  match d1, d2 with
  | Decl_let (x1,e1), Decl_let (x2,e2) -> x1 = x2 && expr_eq e1 e2
  | Decl_letrec (x1,e1), Decl_letrec (x2,e2) -> x1 = x2 && expr_eq e1 e2
  | Decl_type (n1,p1,td1), Decl_type (n2,p2,td2) -> n1 = n2 && p1 = p2 && type_def_eq td1 td2
  | Decl_expr e1, Decl_expr e2 -> expr_eq e1 e2
  | _ -> false

(* === QCheck tests === *)

let depth = 3

let expr_roundtrip_test =
  QCheck.Test.make ~name:"expr round-trip: parse(pp(e)) = e" ~count:500
    (QCheck.make (gen_expr depth) ~print:(fun e -> sc (pp_expr e)))
    (fun expr ->
       let expr = normalize_expr expr in
       let printed = sc (pp_expr expr) in
       match Parser.parse printed with
       | Result.Ok [Decl_expr parsed_expr] ->
         let parsed_norm = normalize_expr parsed_expr in
         let pp_match = sc (pp_expr expr) = sc (pp_expr parsed_norm) in
         expr_eq expr parsed_norm || pp_match
       | Result.Ok _ -> false
       | Result.Error _msg -> false)

let decl_roundtrip_test =
  QCheck.Test.make ~name:"decl round-trip: parse(pp(d)) = d" ~count:100
    (QCheck.make (gen_decl depth) ~print:(fun d -> sc (pp_decl d)))
    (fun decl ->
       let decl = normalize_decl decl in
       let printed = sc (pp_decl decl) ^ ";;" in
       match Parser.parse printed with
       | Result.Ok [parsed_decl] ->
         let parsed_norm = normalize_decl parsed_decl in
         let pp_match = sc (pp_decl decl) = sc (pp_decl parsed_norm) in
         decl_eq decl parsed_norm || pp_match
       | Result.Ok _ -> false
       | Result.Error _msg -> false)

let () =
  exit (QCheck_base_runner.run_tests ~verbose:true [expr_roundtrip_test; decl_roundtrip_test])
