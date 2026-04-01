(* cross_test.ml - Correctness theorem PBT:
     interpret(source) = (interpret-bytecode . compile)(source)

   For each generated program, compare:
   1. Source interpreter: interpret 10000 prog -> extract trace as string
   2. Compiled bytecode path: compile_program prog -> bytecode interpreter step loop -> output

   This does NOT use ocamlc at all -- it directly cross-validates our two paths
   against each other, which is exactly the correctness theorem. *)

open Interp_extracted
open Test_common

(* === Random AST generator === *)

(* Variable names pool -- short distinct names to avoid collisions *)
let var_names = [| "a"; "b"; "c"; "d"; "e"; "m"; "n"; "p"; "q"; "r"; "s"; "t"; "u"; "w" |]

(* Generate a fresh variable name not in scope *)
let gen_fresh_var (scope : string list) : string QCheck.Gen.t =
  let open QCheck.Gen in
  let available = Array.to_list var_names
    |> List.filter (fun v -> not (List.mem v scope)) in
  match available with
  | [] -> (* fallback: make a unique name *)
    map (fun i -> Printf.sprintf "v%d" i) (int_range 0 99)
  | vs -> oneofl vs

(* Parenthesize an OCaml source string for safe embedding *)
let parens s = "(" ^ s ^ ")"

(* gen_int_expr : int -> string list -> (expr * string) QCheck.Gen.t
   Generates a random int-typed expression tree up to the given depth,
   with `scope` tracking currently bound variable names (all assumed to be int).
   Returns both the AST and a matching OCaml source string. *)
let rec gen_int_expr (depth : int) (scope : string list) : (expr * string) QCheck.Gen.t =
  let open QCheck.Gen in
  if depth <= 0 then gen_int_leaf scope
  else
    (* Weight leaves more heavily to keep trees small *)
    frequency [
      (4, gen_int_leaf scope);
      (3, gen_binop depth scope);
      (1, gen_unop depth scope);
      (2, gen_if depth scope);
      (3, gen_let depth scope);
      (2, gen_fun_app depth scope);
      (1, gen_tuple depth scope);
      (1, gen_tuple_pat depth scope);
      (1, gen_match_int depth scope);
      (1, gen_seq depth scope);
    ]

and gen_int_leaf (scope : string list) : (expr * string) QCheck.Gen.t =
  let open QCheck.Gen in
  let base_gens = [
    (* int literal *)
    (5, map (fun n ->
      (Exp_int n, Printf.sprintf "(%d)" n))
      (int_range (-50) 99));
  ] in
  let var_gen = match scope with
    | [] -> []
    | _ ->
      [(3, map (fun v -> (Exp_var (cl v), v)) (oneofl scope))]
  in
  frequency (base_gens @ var_gen)

and gen_binop (depth : int) (scope : string list) : (expr * string) QCheck.Gen.t =
  let open QCheck.Gen in
  let arith_ops = [
    (Op_add, "+"); (Op_sub, "-"); (Op_mul, "*");
  ] in
  let cmp_ops = [
    (Op_eq, "="); (Op_neq, "<>"); (Op_lt, "<");
    (Op_le, "<="); (Op_gt, ">"); (Op_ge, ">=");
  ] in
  let d = depth - 1 in
  oneof [
    (* Arithmetic binop *)
    (gen_int_expr d scope >>= fun (le, ls) ->
     gen_int_expr d scope >>= fun (re, rs) ->
     oneofl arith_ops >>= fun (op, ops) ->
     return (Exp_binop (op, le, re), parens (ls ^ " " ^ ops ^ " " ^ rs)));
    (* Division/mod -- protect against division by zero *)
    (gen_int_expr d scope >>= fun (le, ls) ->
     int_range 1 20 >>= fun divisor ->
     oneofl [(Op_div, "/"); (Op_mod, "mod")] >>= fun (op, ops) ->
     let re = Exp_binop (Op_add, Exp_int divisor, Exp_int 1) in
     let rs = Printf.sprintf "(%d + 1)" divisor in
     return (Exp_binop (op, le, re), parens (ls ^ " " ^ ops ^ " " ^ rs)));
    (* Comparison binop -- result is bool, wrap in if for int context *)
    (gen_int_expr d scope >>= fun (le, ls) ->
     gen_int_expr d scope >>= fun (re, rs) ->
     oneofl cmp_ops >>= fun (op, ops) ->
     return (Exp_if (Exp_binop (op, le, re), Exp_int 1, Exp_int 0),
             parens ("if " ^ ls ^ " " ^ ops ^ " " ^ rs ^ " then 1 else 0")));
  ]

and gen_unop (depth : int) (scope : string list) : (expr * string) QCheck.Gen.t =
  let open QCheck.Gen in
  let d = depth - 1 in
  oneof [
    (* Negation *)
    (gen_int_expr d scope >>= fun (e, s) ->
     return (Exp_unop (Op_neg, e), parens ("- " ^ s)));
    (* Not -- on a comparison *)
    (gen_int_expr d scope >>= fun (le, ls) ->
     gen_int_expr d scope >>= fun (re, rs) ->
     return (Exp_if (Exp_unop (Op_not, Exp_binop (Op_eq, le, re)), Exp_int 1, Exp_int 0),
             parens ("if not (" ^ ls ^ " = " ^ rs ^ ") then 1 else 0")));
  ]

and gen_if (depth : int) (scope : string list) : (expr * string) QCheck.Gen.t =
  let open QCheck.Gen in
  let d = depth - 1 in
  (* Generate a bool condition via comparison *)
  gen_int_expr d scope >>= fun (ce1, cs1) ->
  gen_int_expr d scope >>= fun (ce2, cs2) ->
  oneofl [(Op_gt, ">"); (Op_lt, "<"); (Op_eq, "="); (Op_le, "<=")] >>= fun (cop, cops) ->
  gen_int_expr d scope >>= fun (te, ts) ->
  gen_int_expr d scope >>= fun (fe, fs) ->
  return (Exp_if (Exp_binop (cop, ce1, ce2), te, fe),
          parens ("if " ^ cs1 ^ " " ^ cops ^ " " ^ cs2 ^ " then " ^ ts ^ " else " ^ fs))

and gen_let (depth : int) (scope : string list) : (expr * string) QCheck.Gen.t =
  let open QCheck.Gen in
  let d = depth - 1 in
  gen_fresh_var scope >>= fun v ->
  gen_int_expr d scope >>= fun (ve, vs) ->
  gen_int_expr d (v :: scope) >>= fun (be, bs) ->
  return (Exp_let (cl v, ve, be),
          parens ("let " ^ v ^ " = " ^ vs ^ " in " ^ bs))

and gen_fun_app (depth : int) (scope : string list) : (expr * string) QCheck.Gen.t =
  let open QCheck.Gen in
  let d = depth - 1 in
  gen_fresh_var scope >>= fun fname ->
  gen_fresh_var (fname :: scope) >>= fun param ->
  (* Function body can see param but NOT fname (non-recursive) *)
  gen_int_expr d (param :: scope) >>= fun (body_e, body_s) ->
  gen_int_expr d scope >>= fun (arg_e, arg_s) ->
  return (Exp_let (cl fname,
            Exp_fun (cl param, body_e),
            Exp_app (Exp_var (cl fname), arg_e)),
          parens ("let " ^ fname ^ " " ^ param ^ " = " ^ body_s ^
                  " in " ^ fname ^ " " ^ arg_s))

and gen_tuple (depth : int) (scope : string list) : (expr * string) QCheck.Gen.t =
  let open QCheck.Gen in
  let d = depth - 1 in
  (* Generate a 2-tuple of ints, bind it, and extract with fst/snd *)
  gen_fresh_var scope >>= fun tv ->
  gen_int_expr d scope >>= fun (e1, s1) ->
  gen_int_expr d scope >>= fun (e2, s2) ->
  return (Exp_let (cl tv, Exp_tuple [e1; e2],
            Exp_binop (Op_add,
              Exp_app (Exp_var (cl "fst"), Exp_var (cl tv)),
              Exp_app (Exp_var (cl "snd"), Exp_var (cl tv)))),
          parens ("let " ^ tv ^ " = (" ^ s1 ^ ", " ^ s2 ^ ") in fst " ^
                  tv ^ " + snd " ^ tv))

and gen_tuple_pat (depth : int) (scope : string list) : (expr * string) QCheck.Gen.t =
  let open QCheck.Gen in
  let d = depth - 1 in
  (* Generate a 2-tuple, destructure with Pat_tuple, use bound vars *)
  gen_fresh_var scope >>= fun va ->
  gen_fresh_var (va :: scope) >>= fun vb ->
  gen_int_expr d scope >>= fun (e1, s1) ->
  gen_int_expr d scope >>= fun (e2, s2) ->
  gen_int_expr d (vb :: va :: scope) >>= fun (body_e, body_s) ->
  return (Exp_match (Exp_tuple [e1; e2],
            [(Pat_tuple [Pat_var (cl va); Pat_var (cl vb)], body_e)]),
          parens ("match (" ^ s1 ^ ", " ^ s2 ^ ") with (" ^ va ^ ", " ^ vb ^ ") -> " ^ body_s))

and gen_match_int (depth : int) (scope : string list) : (expr * string) QCheck.Gen.t =
  let open QCheck.Gen in
  let d = depth - 1 in
  gen_int_expr d scope >>= fun (scrut_e, scrut_s) ->
  oneof [
    (* 1 int pattern + wildcard *)
    (gen_int_expr d scope >>= fun (arm0_e, arm0_s) ->
     gen_int_expr d scope >>= fun (wild_e, wild_s) ->
     return (Exp_match (scrut_e,
               [(Pat_int 0, arm0_e); (Pat_wild, wild_e)]),
             parens ("match " ^ scrut_s ^ " with 0 -> " ^ arm0_s ^
                     " | _ -> " ^ wild_s)));
    (* 2 int patterns + wildcard *)
    (gen_int_expr d scope >>= fun (arm0_e, arm0_s) ->
     gen_int_expr d scope >>= fun (arm1_e, arm1_s) ->
     gen_int_expr d scope >>= fun (wild_e, wild_s) ->
     return (Exp_match (scrut_e,
               [(Pat_int 0, arm0_e); (Pat_int 1, arm1_e); (Pat_wild, wild_e)]),
             parens ("match " ^ scrut_s ^ " with 0 -> " ^ arm0_s ^
                     " | 1 -> " ^ arm1_s ^ " | _ -> " ^ wild_s)));
    (* 3 int patterns + wildcard *)
    (gen_int_expr d scope >>= fun (arm0_e, arm0_s) ->
     gen_int_expr d scope >>= fun (arm1_e, arm1_s) ->
     gen_int_expr d scope >>= fun (arm2_e, arm2_s) ->
     gen_int_expr d scope >>= fun (wild_e, wild_s) ->
     return (Exp_match (scrut_e,
               [(Pat_int 0, arm0_e); (Pat_int 1, arm1_e);
                (Pat_int 2, arm2_e); (Pat_wild, wild_e)]),
             parens ("match " ^ scrut_s ^ " with 0 -> " ^ arm0_s ^
                     " | 1 -> " ^ arm1_s ^ " | 2 -> " ^ arm2_s ^
                     " | _ -> " ^ wild_s)));
  ]

and gen_seq (depth : int) (scope : string list) : (expr * string) QCheck.Gen.t =
  let open QCheck.Gen in
  let d = depth - 1 in
  gen_int_expr d scope >>= fun (e1, s1) ->
  gen_int_expr d scope >>= fun (e2, s2) ->
  (* Wrap first expression as a side-effect (ignore its value) *)
  return (Exp_seq (Exp_let (cl "_", e1, Exp_unit), e2),
          parens ("let _ = " ^ s1 ^ " in " ^ s2))

(* Generate a complete program: wrap expression in print_int + print_newline *)
let gen_random_program : (decl list * string) QCheck.Gen.t =
  let open QCheck.Gen in
  (* Use depth 1-3 to keep programs manageable *)
  int_range 1 3 >>= fun depth ->
  gen_int_expr depth [] >>= fun (e, s) ->
  let prog = [Decl_expr (print_int_nl e)] in
  let desc = Printf.sprintf "random[d=%d]: print_int (%s)" depth s in
  return (prog, desc)

(* Same generator but producing OCaml source for ocamlc *)
let gen_random_program_with_source : (decl list * string) QCheck.Gen.t =
  let open QCheck.Gen in
  int_range 1 3 >>= fun depth ->
  gen_int_expr depth [] >>= fun (e, s) ->
  let prog = [Decl_expr (print_int_nl e)] in
  let src = Printf.sprintf "let () = print_int (%s); print_newline ()" s in
  return (prog, src)

(* === QCheck generators producing (prog, description) pairs === *)

let gen_test_case : (decl list * string) QCheck.Gen.t =
  let open QCheck.Gen in
  oneof [
    (* 1. Print a single integer *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl (Exp_int n))] in
      let desc = Printf.sprintf "print_int (%d)" n in
      (prog, desc)) (int_range (-100) 99));

    (* 2. Addition *)
    (map2 (fun a b ->
      let b = b + 1 in
      let prog = [Decl_expr (print_int_nl (Exp_binop (Op_add, Exp_int a, Exp_int b)))] in
      let desc = Printf.sprintf "print_int (%d + %d)" a b in
      (prog, desc)) (int_range 0 99) (int_range 0 99));

    (* 3. Subtraction *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl (Exp_binop (Op_sub, Exp_int a, Exp_int b)))] in
      let desc = Printf.sprintf "print_int (%d - %d)" a b in
      (prog, desc)) (int_range 0 99) (int_range 0 99));

    (* 4. Multiplication *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl (Exp_binop (Op_mul, Exp_int a, Exp_int b)))] in
      let desc = Printf.sprintf "print_int (%d * %d)" a b in
      (prog, desc)) (int_range 0 49) (int_range 0 49));

    (* 5. If with Op_gt *)
    (map2 (fun n t ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_binop (Op_gt, Exp_int n, Exp_int t), Exp_int 1, Exp_int 0)))] in
      let desc = Printf.sprintf "if %d > %d then 1 else 0" n t in
      (prog, desc)) (int_range 0 99) (int_range 0 99));

    (* 6. Let x, let y, add *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "y", Exp_int b,
            Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y"))))))] in
      let desc = Printf.sprintf "let x = %d in let y = %d in x + y" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 7. Function: double *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "x"))),
          Exp_app (Exp_var (cl "f"), Exp_int n))))] in
      let desc = Printf.sprintf "let f x = x + x in f %d" n in
      (prog, desc)) (int_range 0 49));

    (* 8. Recursive factorial *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_letrec (cl "fact",
          Exp_fun (cl "n",
            Exp_if (Exp_binop (Op_le, Exp_var (cl "n"), Exp_int 1),
              Exp_int 1,
              Exp_binop (Op_mul, Exp_var (cl "n"),
                Exp_app (Exp_var (cl "fact"),
                  Exp_binop (Op_sub, Exp_var (cl "n"), Exp_int 1))))),
          Exp_app (Exp_var (cl "fact"), Exp_int n))))] in
      let desc = Printf.sprintf "fact %d" n in
      (prog, desc)) (int_range 0 9));

    (* 9. Tuple fst + snd *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "p", Exp_tuple [Exp_int a; Exp_int b],
          Exp_binop (Op_add,
            Exp_app (Exp_var (cl "fst"), Exp_var (cl "p")),
            Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))))))] in
      let desc = Printf.sprintf "let p = (%d, %d) in fst p + snd p" a b in
      (prog, desc)) (int_range 0 49) (int_range 0 49));

    (* 10. Match on ints: 0, 1, wildcard *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_int 0, Exp_int 100);
           (Pat_int 1, Exp_int 200);
           (Pat_wild, Exp_int 999)])))] in
      let desc = Printf.sprintf "match %d with 0->100 | 1->200 | _->999" n in
      (prog, desc)) (int_range 0 2));

    (* 11. Two-argument function *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_fun (cl "x", Exp_fun (cl "y",
            Exp_binop (Op_add, Exp_binop (Op_mul, Exp_var (cl "x"), Exp_var (cl "y")), Exp_int 1))),
          Exp_app (Exp_app (Exp_var (cl "f"), Exp_int a), Exp_int b))))] in
      let desc = Printf.sprintf "let f x y = x*y+1 in f %d %d" a b in
      (prog, desc)) (int_range 0 29) (int_range 0 29));

    (* 12. Recursive fibonacci *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_letrec (cl "fib",
          Exp_fun (cl "n",
            Exp_if (Exp_binop (Op_le, Exp_var (cl "n"), Exp_int 1),
              Exp_var (cl "n"),
              Exp_binop (Op_add,
                Exp_app (Exp_var (cl "fib"), Exp_binop (Op_sub, Exp_var (cl "n"), Exp_int 1)),
                Exp_app (Exp_var (cl "fib"), Exp_binop (Op_sub, Exp_var (cl "n"), Exp_int 2))))),
          Exp_app (Exp_var (cl "fib"), Exp_int n))))] in
      let desc = Printf.sprintf "fib %d" n in
      (prog, desc)) (int_range 0 11));

    (* 13. Unary negation *)
    (map (fun a ->
      let prog = [Decl_expr (print_int_nl (Exp_unop (Op_neg, Exp_int a)))] in
      let desc = Printf.sprintf "- %d" a in
      (prog, desc)) (int_range 0 99));

    (* 14. Mixed arithmetic: a * b + c *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add, Exp_binop (Op_mul, Exp_int a, Exp_int b), Exp_int c)))] in
      let desc = Printf.sprintf "%d * %d + %d" a b c in
      (prog, desc)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 15. Match with Pat_var binding *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_int 0, Exp_int 42);
           (Pat_var (cl "x"), Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1))])))] in
      let desc = Printf.sprintf "match %d with 0->42 | x->x+1" n in
      (prog, desc)) (int_range 0 99));

    (* 16. Match on computed expression *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_binop (Op_sub, Exp_int a, Exp_int b),
          [(Pat_int 0, Exp_int 1);
           (Pat_wild, Exp_int 0)])))] in
      let desc = Printf.sprintf "match %d-%d with 0->1 | _->0" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 17. Match with many branches *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_int 0, Exp_int 10); (Pat_int 1, Exp_int 20);
           (Pat_int 2, Exp_int 30); (Pat_int 3, Exp_int 40);
           (Pat_wild, Exp_int 50)])))] in
      let desc = Printf.sprintf "match %d many-branches" n in
      (prog, desc)) (int_range 0 4));

    (* 18. Match with if in branch body *)
    (map2 (fun n m ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_int 0, Exp_if (Exp_binop (Op_gt, Exp_int m, Exp_int 5), Exp_int 1, Exp_int 0));
           (Pat_wild, Exp_int 99)])))] in
      let desc = Printf.sprintf "match %d with 0->if %d>5 then 1 else 0 | _->99" n m in
      (prog, desc)) (int_range 0 2) (int_range 0 9));

    (* 19. Function with match body *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_fun (cl "x",
            Exp_match (Exp_var (cl "x"),
              [(Pat_int 0, Exp_int 100); (Pat_int 1, Exp_int 200); (Pat_wild, Exp_int 300)])),
          Exp_app (Exp_var (cl "f"), Exp_int n))))] in
      let desc = Printf.sprintf "fun-with-match %d" n in
      (prog, desc)) (int_range 0 2));

    (* 20. Nested let bindings (4 deep) *)
    (map (fun a ->
      let b = a + 1 in let c = a + 2 in let d = a + 3 in
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "a", Exp_int a,
          Exp_let (cl "b", Exp_int b,
            Exp_let (cl "c", Exp_int c,
              Exp_let (cl "d", Exp_int d,
                Exp_binop (Op_add,
                  Exp_binop (Op_add, Exp_var (cl "a"), Exp_var (cl "b")),
                  Exp_binop (Op_add, Exp_var (cl "c"), Exp_var (cl "d")))))))))] in
      let desc = Printf.sprintf "nested-let-4 a=%d" a in
      (prog, desc)) (int_range 0 9));

    (* 21. Recursive count with match *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_letrec (cl "count",
          Exp_fun (cl "n",
            Exp_match (Exp_var (cl "n"),
              [(Pat_int 0, Exp_int 0);
               (Pat_var (cl "x"), Exp_binop (Op_add, Exp_int 1,
                 Exp_app (Exp_var (cl "count"),
                   Exp_binop (Op_sub, Exp_var (cl "x"), Exp_int 1))))])),
          Exp_app (Exp_var (cl "count"), Exp_int n))))] in
      let desc = Printf.sprintf "rec-count %d" n in
      (prog, desc)) (int_range 0 7));

    (* 22. Top-level Decl_letrec followed by Decl_expr *)
    (map (fun n ->
      let prog = [
        Decl_letrec (cl "fact",
          Exp_fun (cl "n",
            Exp_if (Exp_binop (Op_le, Exp_var (cl "n"), Exp_int 1),
              Exp_int 1,
              Exp_binop (Op_mul, Exp_var (cl "n"),
                Exp_app (Exp_var (cl "fact"),
                  Exp_binop (Op_sub, Exp_var (cl "n"), Exp_int 1))))));
        Decl_expr (print_int_nl (Exp_app (Exp_var (cl "fact"), Exp_int n)))] in
      let desc = Printf.sprintf "top-letrec fact %d" n in
      (prog, desc)) (int_range 0 9));

    (* 23. Tuple fst - snd *)
    (map2 (fun a b ->
      let a = a + 10 in
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "p", Exp_tuple [Exp_int a; Exp_int b],
          Exp_binop (Op_sub,
            Exp_app (Exp_var (cl "fst"), Exp_var (cl "p")),
            Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))))))] in
      let desc = Printf.sprintf "fst-snd (%d,%d)" a b in
      (prog, desc)) (int_range 0 49) (int_range 0 49));

    (* 24. Division + modulo *)
    (map2 (fun a b ->
      let a = a + 1 in let b = b + 1 in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add,
          Exp_binop (Op_div, Exp_int a, Exp_int b),
          Exp_binop (Op_mod, Exp_int a, Exp_int b))))] in
      let desc = Printf.sprintf "%d/%d + %d mod %d" a b a b in
      (prog, desc)) (int_range 0 499) (int_range 0 19));

    (* 25. Nested function application: f (g n) *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)),
          Exp_let (cl "g", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)),
            Exp_app (Exp_var (cl "f"), Exp_app (Exp_var (cl "g"), Exp_int n))))))] in
      let desc = Printf.sprintf "f(g(%d))" n in
      (prog, desc)) (int_range 0 19));

    (* 26. Curried function (make_adder) *)
    (map2 (fun n m ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "make_adder",
          Exp_fun (cl "n", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "n")))),
          Exp_app (Exp_app (Exp_var (cl "make_adder"), Exp_int n), Exp_int m))))] in
      let desc = Printf.sprintf "make_adder %d %d" n m in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 27. Sequential print of two ints *)
    (map2 (fun a b ->
      let prog = [Decl_expr
        (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int a),
          Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int b),
            Exp_app (Exp_var (cl "print_newline"), Exp_unit))))] in
      let desc = Printf.sprintf "seq-print %d %d" a b in
      (prog, desc)) (int_range 0 9) (int_range 0 9));

    (* 28. Multiple comparison operators combined *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add,
          Exp_binop (Op_add,
            Exp_if (Exp_binop (Op_lt, Exp_int a, Exp_int b), Exp_int 1, Exp_int 0),
            Exp_if (Exp_binop (Op_eq, Exp_int a, Exp_int b), Exp_int 10, Exp_int 0)),
          Exp_if (Exp_binop (Op_ge, Exp_int a, Exp_int b), Exp_int 100, Exp_int 0))))] in
      let desc = Printf.sprintf "cmp-combo %d %d" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 29. Variable shadowing *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int b),
            Exp_var (cl "x")))))] in
      let desc = Printf.sprintf "shadow x=%d +%d" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 30. Partial application *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "add",
          Exp_fun (cl "x", Exp_fun (cl "y", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y")))),
          Exp_let (cl "inc", Exp_app (Exp_var (cl "add"), Exp_int 1),
            Exp_app (Exp_var (cl "inc"), Exp_int n)))))] in
      let desc = Printf.sprintf "partial-app inc %d" n in
      (prog, desc)) (int_range 0 49));

    (* 31. Match on bool patterns *)
    (map (fun b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_bool (b),
          [(Pat_bool true, Exp_int 1);
           (Pat_bool false, Exp_int 0)])))] in
      let desc = Printf.sprintf "match-bool %b" b in
      (prog, desc)) QCheck.Gen.bool);

    (* 32. Match on bool patterns with expressions *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_bool (a > b),
          [(Pat_bool true, Exp_int a);
           (Pat_bool false, Exp_int b)])))] in
      let desc = Printf.sprintf "match-bool-expr %d %d" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 33. Match with Pat_unit *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_unit,
          [(Pat_unit, Exp_int n)])))] in
      let desc = Printf.sprintf "match-unit %d" n in
      (prog, desc)) (int_range 0 99));

    (* 34. Nested match *)
    (map2 (fun x y ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int x,
          [(Pat_int 0,
            Exp_match (Exp_int y,
              [(Pat_int 0, Exp_int 10);
               (Pat_wild, Exp_int 20)]));
           (Pat_wild,
            Exp_match (Exp_int y,
              [(Pat_int 0, Exp_int 30);
               (Pat_wild, Exp_int 40)]))])))] in
      let desc = Printf.sprintf "nested-match %d %d" x y in
      (prog, desc)) (int_range 0 2) (int_range 0 2));

    (* 35. Nested match via Pat_var *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_var (cl "x"),
            Exp_match (Exp_var (cl "x"),
              [(Pat_int 0, Exp_int 100);
               (Pat_int 1, Exp_int 200);
               (Pat_wild, Exp_int 300)]))])))] in
      let desc = Printf.sprintf "nested-match-var %d" n in
      (prog, desc)) (int_range 0 3));

    (* 36. 3-element tuple *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "t3", Exp_tuple [Exp_int a; Exp_int b; Exp_int c],
          Exp_let (cl "t2", Exp_tuple [Exp_int a; Exp_int b],
            Exp_binop (Op_add,
              Exp_app (Exp_var (cl "fst"), Exp_var (cl "t2")),
              Exp_app (Exp_var (cl "snd"), Exp_var (cl "t2")))))))] in
      let desc = Printf.sprintf "3-tuple (%d,%d,%d)" a b c in
      (prog, desc)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 37. 3-element tuple via let bindings *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "y", Exp_int b,
            Exp_let (cl "z", Exp_int c,
              Exp_let (cl "p", Exp_tuple [Exp_var (cl "x"); Exp_var (cl "y")],
                Exp_binop (Op_add,
                  Exp_binop (Op_add,
                    Exp_app (Exp_var (cl "fst"), Exp_var (cl "p")),
                    Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))),
                  Exp_var (cl "z"))))))))] in
      let desc = Printf.sprintf "tuple-via-lets %d %d %d" a b c in
      (prog, desc)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 38. Closure: function captures free variable *)
    (map2 (fun x y ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int x,
          Exp_let (cl "f", Exp_fun (cl "y", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y"))),
            Exp_app (Exp_var (cl "f"), Exp_int y)))))] in
      let desc = Printf.sprintf "closure x=%d f(y=%d)" x y in
      (prog, desc)) (int_range 0 49) (int_range 0 49));

    (* 39. Closure: two free variables *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "a", Exp_int a,
          Exp_let (cl "b", Exp_int b,
            Exp_let (cl "f", Exp_fun (cl "c",
              Exp_binop (Op_add, Exp_var (cl "a"),
                Exp_binop (Op_add, Exp_var (cl "b"), Exp_var (cl "c")))),
              Exp_app (Exp_var (cl "f"), Exp_int c))))))] in
      let desc = Printf.sprintf "closure-2free %d %d %d" a b c in
      (prog, desc)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 40. Closure: returned function captures variable *)
    (map2 (fun n m ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "make_mul",
          Exp_fun (cl "n", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "n"), Exp_var (cl "x")))),
          Exp_let (cl "double", Exp_app (Exp_var (cl "make_mul"), Exp_int n),
            Exp_app (Exp_var (cl "double"), Exp_int m)))))] in
      let desc = Printf.sprintf "make_mul %d then %d" n m in
      (prog, desc)) (int_range 1 9) (int_range 0 19));

    (* 41. Recursive function with closure *)
    (map2 (fun base n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "base", Exp_int base,
          Exp_letrec (cl "f",
            Exp_fun (cl "n",
              Exp_if (Exp_binop (Op_le, Exp_var (cl "n"), Exp_int 0),
                Exp_var (cl "base"),
                Exp_binop (Op_add, Exp_int 1,
                  Exp_app (Exp_var (cl "f"),
                    Exp_binop (Op_sub, Exp_var (cl "n"), Exp_int 1))))),
            Exp_app (Exp_var (cl "f"), Exp_int n)))))] in
      let desc = Printf.sprintf "rec-closure base=%d n=%d" base n in
      (prog, desc)) (int_range 10 30) (int_range 0 7));

    (* 42. Multiple sequential print statements (3 ints) *)
    (map3 (fun a b c ->
      let prog = [Decl_expr
        (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int a),
          Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int b),
            Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int c),
              Exp_app (Exp_var (cl "print_newline"), Exp_unit)))))] in
      let desc = Printf.sprintf "seq-3 %d %d %d" a b c in
      (prog, desc)) (int_range 0 9) (int_range 0 9) (int_range 0 9));

    (* 43. Multiple sequential print statements (4 ints) *)
    (map2 (fun a b ->
      let c = a + b in
      let d = a * 2 in
      let prog = [Decl_expr
        (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int a),
          Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int b),
            Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int c),
              Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int d),
                Exp_app (Exp_var (cl "print_newline"), Exp_unit))))))] in
      let desc = Printf.sprintf "seq-4 %d %d %d %d" a b c d in
      (prog, desc)) (int_range 0 9) (int_range 0 9));

    (* 44. Nested function application: f (g (h x)) *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "h", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)),
          Exp_let (cl "g", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)),
            Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_sub, Exp_var (cl "x"), Exp_int 3)),
              Exp_app (Exp_var (cl "f"),
                Exp_app (Exp_var (cl "g"),
                  Exp_app (Exp_var (cl "h"), Exp_int n))))))))] in
      let desc = Printf.sprintf "f(g(h(%d)))" n in
      (prog, desc)) (int_range 0 19));

    (* 45. Higher-order: apply f x = f x *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "apply",
          Exp_fun (cl "f", Exp_fun (cl "x", Exp_app (Exp_var (cl "f"), Exp_var (cl "x")))),
          Exp_app (Exp_app (Exp_var (cl "apply"),
            Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1))),
            Exp_int n))))] in
      let desc = Printf.sprintf "apply (+1) %d" n in
      (prog, desc)) (int_range 0 49));

    (* 46. Higher-order: apply_twice f x = f (f x) *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "apply_twice",
          Exp_fun (cl "f", Exp_fun (cl "x",
            Exp_app (Exp_var (cl "f"), Exp_app (Exp_var (cl "f"), Exp_var (cl "x"))))),
          Exp_app (Exp_app (Exp_var (cl "apply_twice"),
            Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1))),
            Exp_int n))))] in
      let desc = Printf.sprintf "apply_twice (+1) %d" n in
      (prog, desc)) (int_range 0 49));

    (* 47. Higher-order: map-like on pair *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)),
          Exp_let (cl "p", Exp_tuple [Exp_int a; Exp_int b],
            Exp_binop (Op_add,
              Exp_app (Exp_var (cl "f"), Exp_app (Exp_var (cl "fst"), Exp_var (cl "p"))),
              Exp_app (Exp_var (cl "f"), Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))))))))] in
      let desc = Printf.sprintf "map-pair (*2) (%d,%d)" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 48. Op_neq *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_binop (Op_neq, Exp_int a, Exp_int b), Exp_int 1, Exp_int 0)))] in
      let desc = Printf.sprintf "%d <> %d" a b in
      (prog, desc)) (int_range 0 9) (int_range 0 9));

    (* 49. Op_le *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_binop (Op_le, Exp_int a, Exp_int b), Exp_int 1, Exp_int 0)))] in
      let desc = Printf.sprintf "%d <= %d" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 50. Op_ge *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_binop (Op_ge, Exp_int a, Exp_int b), Exp_int 1, Exp_int 0)))] in
      let desc = Printf.sprintf "%d >= %d" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 51. All six comparison operators combined *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add,
          Exp_binop (Op_add,
            Exp_binop (Op_add,
              Exp_if (Exp_binop (Op_eq, Exp_int a, Exp_int b), Exp_int 1, Exp_int 0),
              Exp_if (Exp_binop (Op_neq, Exp_int a, Exp_int b), Exp_int 10, Exp_int 0)),
            Exp_binop (Op_add,
              Exp_if (Exp_binop (Op_lt, Exp_int a, Exp_int b), Exp_int 100, Exp_int 0),
              Exp_if (Exp_binop (Op_le, Exp_int a, Exp_int b), Exp_int 1000, Exp_int 0))),
          Exp_binop (Op_add,
            Exp_if (Exp_binop (Op_gt, Exp_int a, Exp_int b), Exp_int 10000, Exp_int 0),
            Exp_if (Exp_binop (Op_ge, Exp_int a, Exp_int b), Exp_int 100000, Exp_int 0)))))] in
      let desc = Printf.sprintf "all-6-cmp %d %d" a b in
      (prog, desc)) (int_range 0 9) (int_range 0 9));

    (* 52. Variable shadowing in nested scopes *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "y",
            Exp_let (cl "x", Exp_int b,
              Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)),
            Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y"))))))] in
      let desc = Printf.sprintf "nested-shadow %d %d" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 53. Function parameter shadows outer binding *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)),
            Exp_binop (Op_add, Exp_var (cl "x"),
              Exp_app (Exp_var (cl "f"), Exp_int b))))))] in
      let desc = Printf.sprintf "param-shadow x=%d f(%d)" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 54. Triple variable shadowing *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int n,
          Exp_let (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1),
            Exp_let (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2),
              Exp_var (cl "x"))))))] in
      let desc = Printf.sprintf "triple-shadow %d" n in
      (prog, desc)) (int_range 0 19));

    (* 55. Top-level Decl_let + Decl_expr *)
    (map (fun n ->
      let prog = [
        Decl_let (cl "x", Exp_int n);
        Decl_expr (print_int_nl (Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)))] in
      let desc = Printf.sprintf "top-let x=%d" n in
      (prog, desc)) (int_range 0 99));

    (* 56. Multiple top-level Decl_let *)
    (map2 (fun a b ->
      let prog = [
        Decl_let (cl "x", Exp_int a);
        Decl_let (cl "y", Exp_int b);
        Decl_expr (print_int_nl (Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y"))))] in
      let desc = Printf.sprintf "multi-top-let %d %d" a b in
      (prog, desc)) (int_range 0 49) (int_range 0 49));

    (* 57. Three top-level Decl_let + computed Decl_let *)
    (map3 (fun a b c ->
      let prog = [
        Decl_let (cl "a", Exp_int a);
        Decl_let (cl "b", Exp_int b);
        Decl_let (cl "c", Exp_int c);
        Decl_let (cl "sum", Exp_binop (Op_add, Exp_var (cl "a"),
          Exp_binop (Op_add, Exp_var (cl "b"), Exp_var (cl "c"))));
        Decl_expr (print_int_nl (Exp_var (cl "sum")))] in
      let desc = Printf.sprintf "3-top-let %d+%d+%d" a b c in
      (prog, desc)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 58. Top-level function Decl_let *)
    (map (fun n ->
      let prog = [
        Decl_let (cl "double", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)));
        Decl_expr (print_int_nl (Exp_app (Exp_var (cl "double"), Exp_int n)))] in
      let desc = Printf.sprintf "top-fun double %d" n in
      (prog, desc)) (int_range 0 49));

    (* 59. Match with Pat_var single arm *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_binop (Op_add, Exp_int n, Exp_int 1),
          [(Pat_var (cl "x"), Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2))])))] in
      let desc = Printf.sprintf "match-var-single %d" n in
      (prog, desc)) (int_range 0 49));

    (* 60. Deeply nested let (5 levels) *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "a", Exp_int n,
          Exp_let (cl "b", Exp_binop (Op_add, Exp_var (cl "a"), Exp_int 1),
            Exp_let (cl "c", Exp_binop (Op_mul, Exp_var (cl "b"), Exp_int 2),
              Exp_let (cl "d", Exp_binop (Op_sub, Exp_var (cl "c"), Exp_int 3),
                Exp_let (cl "e", Exp_binop (Op_add, Exp_var (cl "d"), Exp_var (cl "a")),
                  Exp_var (cl "e"))))))))] in
      let desc = Printf.sprintf "deep-let-5 %d" n in
      (prog, desc)) (int_range 0 19));

    (* 61. Deeply nested let (6 levels, fibonacci-like) *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "v1", Exp_int n,
          Exp_let (cl "v2", Exp_binop (Op_add, Exp_var (cl "v1"), Exp_int 1),
            Exp_let (cl "v3", Exp_binop (Op_add, Exp_var (cl "v1"), Exp_var (cl "v2")),
              Exp_let (cl "v4", Exp_binop (Op_add, Exp_var (cl "v2"), Exp_var (cl "v3")),
                Exp_let (cl "v5", Exp_binop (Op_add, Exp_var (cl "v3"), Exp_var (cl "v4")),
                  Exp_let (cl "v6", Exp_binop (Op_add, Exp_var (cl "v4"), Exp_var (cl "v5")),
                    Exp_var (cl "v6")))))))))] in
      let desc = Printf.sprintf "deep-let-6 %d" n in
      (prog, desc)) (int_range 0 9));

    (* 62. Function composition *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "compose",
          Exp_fun (cl "f", Exp_fun (cl "g", Exp_fun (cl "x",
            Exp_app (Exp_var (cl "f"), Exp_app (Exp_var (cl "g"), Exp_var (cl "x")))))),
          Exp_app (Exp_app (Exp_app (Exp_var (cl "compose"),
            Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 10))),
            Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 3))),
            Exp_int n))))] in
      let desc = Printf.sprintf "compose (+10) (*3) %d" n in
      (prog, desc)) (int_range 0 19));

    (* 63. Function composition with top-level decls *)
    (map (fun n ->
      let prog = [
        Decl_let (cl "inc", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)));
        Decl_let (cl "dbl", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)));
        Decl_expr (print_int_nl
          (Exp_app (Exp_var (cl "inc"), Exp_app (Exp_var (cl "dbl"), Exp_int n))))] in
      let desc = Printf.sprintf "top-compose inc(dbl(%d))" n in
      (prog, desc)) (int_range 0 19));

    (* 64. Division with non-trivial values *)
    (map2 (fun a b ->
      let a = a + 2 in let b = b + 2 in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_div, Exp_binop (Op_mul, Exp_int a, Exp_int b), Exp_int b)))] in
      let desc = Printf.sprintf "%d*%d/%d" a b b in
      (prog, desc)) (int_range 0 49) (int_range 0 19));

    (* 65. Modulo *)
    (map2 (fun a b ->
      let b = b + 2 in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_mod, Exp_int a, Exp_int b)))] in
      let desc = Printf.sprintf "%d mod %d" a b in
      (prog, desc)) (int_range 0 99) (int_range 0 19));

    (* 66. Division identity: a = (a/b)*b + (a mod b) *)
    (map2 (fun a b ->
      let b = b + 1 in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add,
          Exp_binop (Op_mul, Exp_binop (Op_div, Exp_int a, Exp_int b), Exp_int b),
          Exp_binop (Op_mod, Exp_int a, Exp_int b))))] in
      let desc = Printf.sprintf "div-identity %d %d" a b in
      (prog, desc)) (int_range 0 99) (int_range 0 19));

    (* 67. Negative number addition *)
    (map2 (fun a b ->
      let a = -a in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add, Exp_int a, Exp_int b)))] in
      let desc = Printf.sprintf "(%d) + %d" a b in
      (prog, desc)) (int_range 1 50) (int_range 0 99));

    (* 68. Negative number multiplication *)
    (map2 (fun a b ->
      let a = -a in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_mul, Exp_int a, Exp_int b)))] in
      let desc = Printf.sprintf "(%d) * %d" a b in
      (prog, desc)) (int_range 1 20) (int_range 0 20));

    (* 69. Subtraction producing negative *)
    (map2 (fun a b ->
      let b = b + a + 1 in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_sub, Exp_int a, Exp_int b)))] in
      let desc = Printf.sprintf "%d - %d" a b in
      (prog, desc)) (int_range 0 49) (int_range 1 50));

    (* 70. Double negation *)
    (map (fun a ->
      let prog = [Decl_expr (print_int_nl
        (Exp_unop (Op_neg, Exp_unop (Op_neg, Exp_int a))))] in
      let desc = Printf.sprintf "neg(neg(%d))" a in
      (prog, desc)) (int_range 0 99));

    (* 71. If inside let *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_if (Exp_binop (Op_gt, Exp_int a, Exp_int b), Exp_int a, Exp_int b),
          Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2))))] in
      let desc = Printf.sprintf "if-in-let %d %d" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 72. Let inside if branches *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_binop (Op_lt, Exp_int a, Exp_int b),
          Exp_let (cl "x", Exp_binop (Op_sub, Exp_int b, Exp_int a),
            Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 10)),
          Exp_let (cl "x", Exp_binop (Op_sub, Exp_int a, Exp_int b),
            Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 20)))))] in
      let desc = Printf.sprintf "let-in-if %d %d" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 73. Match inside let, let inside match *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "classify",
          Exp_fun (cl "n",
            Exp_match (Exp_var (cl "n"),
              [(Pat_int 0, Exp_int 0);
               (Pat_var (cl "x"),
                Exp_if (Exp_binop (Op_gt, Exp_var (cl "x"), Exp_int 0), Exp_int 1, Exp_int (-1)))])),
          Exp_let (cl "r", Exp_app (Exp_var (cl "classify"), Exp_int n),
            Exp_binop (Op_mul, Exp_var (cl "r"), Exp_int 100)))))] in
      let desc = Printf.sprintf "classify %d" n in
      (prog, desc)) (int_range (-5) 5));

    (* 74. Nested if/let/match combo *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "y", Exp_int b,
            Exp_if (Exp_binop (Op_gt, Exp_var (cl "x"), Exp_var (cl "y")),
              Exp_match (Exp_var (cl "x"),
                [(Pat_int 0, Exp_int 0);
                 (Pat_wild, Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y")))]),
              Exp_match (Exp_var (cl "y"),
                [(Pat_int 0, Exp_int 0);
                 (Pat_wild, Exp_binop (Op_mul, Exp_var (cl "x"), Exp_var (cl "y")))]))))))] in
      let desc = Printf.sprintf "if-let-match %d %d" a b in
      (prog, desc)) (int_range 0 9) (int_range 0 9));

    (* 75. Op_not *)
    (map (fun a ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (
          Exp_unop (Op_not, Exp_binop (Op_eq, Exp_int a, Exp_int 0)),
          Exp_int 1, Exp_int 0)))] in
      let desc = Printf.sprintf "not(%d=0)" a in
      (prog, desc)) (int_range 0 5));

    (* 76. Op_not on comparisons *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (
          Exp_unop (Op_not, Exp_binop (Op_gt, Exp_int a, Exp_int b)),
          Exp_int 1, Exp_int 0)))] in
      let desc = Printf.sprintf "not(%d>%d)" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 77. Exp_bool in if condition *)
    (map (fun b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_bool b, Exp_int 42, Exp_int 0)))] in
      let desc = Printf.sprintf "if %b then 42 else 0" b in
      (prog, desc)) QCheck.Gen.bool);

    (* 78. Top-level Decl_letrec + Decl_let + Decl_expr *)
    (map (fun n ->
      let prog = [
        Decl_letrec (cl "sum",
          Exp_fun (cl "n",
            Exp_if (Exp_binop (Op_le, Exp_var (cl "n"), Exp_int 0),
              Exp_int 0,
              Exp_binop (Op_add, Exp_var (cl "n"),
                Exp_app (Exp_var (cl "sum"),
                  Exp_binop (Op_sub, Exp_var (cl "n"), Exp_int 1))))));
        Decl_let (cl "result", Exp_app (Exp_var (cl "sum"), Exp_int n));
        Decl_expr (print_int_nl (Exp_var (cl "result")))] in
      let desc = Printf.sprintf "top-letrec-let sum(%d)" n in
      (prog, desc)) (int_range 0 10));

    (* 79. Closure applied to tuple component *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "p", Exp_tuple [Exp_int a; Exp_int b],
          Exp_let (cl "add1", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)),
            Exp_binop (Op_add,
              Exp_app (Exp_var (cl "add1"), Exp_app (Exp_var (cl "fst"), Exp_var (cl "p"))),
              Exp_app (Exp_var (cl "add1"), Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))))))))] in
      let desc = Printf.sprintf "closure-tuple (%d,%d)" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 80. Recursive with accumulator *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_letrec (cl "sum_acc",
          Exp_fun (cl "n", Exp_fun (cl "acc",
            Exp_if (Exp_binop (Op_le, Exp_var (cl "n"), Exp_int 0),
              Exp_var (cl "acc"),
              Exp_app (Exp_app (Exp_var (cl "sum_acc"),
                Exp_binop (Op_sub, Exp_var (cl "n"), Exp_int 1)),
                Exp_binop (Op_add, Exp_var (cl "acc"), Exp_var (cl "n")))))),
          Exp_app (Exp_app (Exp_var (cl "sum_acc"), Exp_int n), Exp_int 0))))] in
      let desc = Printf.sprintf "sum_acc %d" n in
      (prog, desc)) (int_range 0 10));

    (* 81. Recursive power with closure *)
    (map2 (fun base exp ->
      let exp = exp mod 6 in
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "b", Exp_int base,
          Exp_letrec (cl "power",
            Exp_fun (cl "n",
              Exp_if (Exp_binop (Op_le, Exp_var (cl "n"), Exp_int 0),
                Exp_int 1,
                Exp_binop (Op_mul, Exp_var (cl "b"),
                  Exp_app (Exp_var (cl "power"),
                    Exp_binop (Op_sub, Exp_var (cl "n"), Exp_int 1))))),
            Exp_app (Exp_var (cl "power"), Exp_int exp)))))] in
      let desc = Printf.sprintf "power %d^%d" base exp in
      (prog, desc)) (int_range 1 4) (int_range 0 5));

    (* 82. Sequence: compute then print *)
    (map2 (fun a b ->
      let prog = [Decl_expr
        (Exp_let (cl "x", Exp_binop (Op_add, Exp_int a, Exp_int b),
          Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_var (cl "x")),
            Exp_app (Exp_var (cl "print_newline"), Exp_unit))))] in
      let desc = Printf.sprintf "compute-print %d+%d" a b in
      (prog, desc)) (int_range 0 49) (int_range 0 49));

    (* 83. Multiple computations + prints *)
    (map2 (fun a b ->
      let prog = [Decl_expr
        (Exp_let (cl "x", Exp_binop (Op_add, Exp_int a, Exp_int b),
          Exp_let (cl "y", Exp_binop (Op_mul, Exp_int a, Exp_int b),
            Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_var (cl "x")),
              Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_var (cl "y")),
                Exp_app (Exp_var (cl "print_newline"), Exp_unit))))))] in
      let desc = Printf.sprintf "multi-compute-print %d %d" a b in
      (prog, desc)) (int_range 0 9) (int_range 0 9));

    (* 84. Match on bool result of comparison *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_binop (Op_lt, Exp_int a, Exp_int b),
          [(Pat_bool true, Exp_binop (Op_sub, Exp_int b, Exp_int a));
           (Pat_bool false, Exp_binop (Op_sub, Exp_int a, Exp_int b))])))] in
      let desc = Printf.sprintf "match-cmp %d<%d" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 85. Identity function *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "id", Exp_fun (cl "x", Exp_var (cl "x")),
          Exp_app (Exp_var (cl "id"), Exp_int n))))] in
      let desc = Printf.sprintf "id %d" n in
      (prog, desc)) (int_range (-50) 50));

    (* 86. Constant function *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "const",
          Exp_fun (cl "x", Exp_fun (cl "y", Exp_var (cl "x"))),
          Exp_app (Exp_app (Exp_var (cl "const"), Exp_int a), Exp_int b))))] in
      let desc = Printf.sprintf "const %d %d" a b in
      (prog, desc)) (int_range 0 49) (int_range 0 49));

    (* 87. Flip function *)
    (map2 (fun a b ->
      let b = b + 1 in
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "flip",
          Exp_fun (cl "f", Exp_fun (cl "x", Exp_fun (cl "y",
            Exp_app (Exp_app (Exp_var (cl "f"), Exp_var (cl "y")), Exp_var (cl "x"))))),
          Exp_app (Exp_app (Exp_app (Exp_var (cl "flip"),
            Exp_fun (cl "x", Exp_fun (cl "y", Exp_binop (Op_sub, Exp_var (cl "x"), Exp_var (cl "y"))))),
            Exp_int a), Exp_int b))))] in
      let desc = Printf.sprintf "flip sub %d %d" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 88. Multiple top-level functions calling each other *)
    (map (fun n ->
      let prog = [
        Decl_let (cl "add1", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)));
        Decl_let (cl "add2", Exp_fun (cl "x", Exp_app (Exp_var (cl "add1"), Exp_app (Exp_var (cl "add1"), Exp_var (cl "x")))));
        Decl_expr (print_int_nl (Exp_app (Exp_var (cl "add2"), Exp_int n)))] in
      let desc = Printf.sprintf "top-chain add2(%d)" n in
      (prog, desc)) (int_range 0 49));

    (* 89. Recursive GCD *)
    (map2 (fun a b ->
      let a = a + 1 in let b = b + 1 in
      let prog = [Decl_expr (print_int_nl
        (Exp_letrec (cl "gcd",
          Exp_fun (cl "a", Exp_fun (cl "b",
            Exp_if (Exp_binop (Op_eq, Exp_var (cl "b"), Exp_int 0),
              Exp_var (cl "a"),
              Exp_app (Exp_app (Exp_var (cl "gcd"), Exp_var (cl "b")),
                Exp_binop (Op_mod, Exp_var (cl "a"), Exp_var (cl "b")))))),
          Exp_app (Exp_app (Exp_var (cl "gcd"), Exp_int a), Exp_int b))))] in
      let desc = Printf.sprintf "gcd %d %d" a b in
      (prog, desc)) (int_range 1 50) (int_range 1 50));

    (* 90. Recursive with multiple match arms *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_letrec (cl "f",
          Exp_fun (cl "n",
            Exp_match (Exp_var (cl "n"),
              [(Pat_int 0, Exp_int 1);
               (Pat_int 1, Exp_int 1);
               (Pat_int 2, Exp_int 2);
               (Pat_var (cl "x"),
                Exp_binop (Op_add,
                  Exp_app (Exp_var (cl "f"), Exp_binop (Op_sub, Exp_var (cl "x"), Exp_int 1)),
                  Exp_app (Exp_var (cl "f"), Exp_binop (Op_sub, Exp_var (cl "x"), Exp_int 3))))])),
          Exp_app (Exp_var (cl "f"), Exp_int n))))] in
      let desc = Printf.sprintf "rec-multi-match %d" n in
      (prog, desc)) (int_range 0 9));

    (* 91. Chained let with function calls *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)),
          Exp_let (cl "a", Exp_app (Exp_var (cl "f"), Exp_int n),
            Exp_let (cl "b", Exp_app (Exp_var (cl "f"), Exp_var (cl "a")),
              Exp_let (cl "c", Exp_app (Exp_var (cl "f"), Exp_var (cl "b")),
                Exp_var (cl "c")))))))] in
      let desc = Printf.sprintf "chained-let-fn %d" n in
      (prog, desc)) (int_range 0 49));

    (* 92. Tuple of expressions *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "p",
          Exp_tuple [Exp_binop (Op_add, Exp_int a, Exp_int 1);
                     Exp_binop (Op_mul, Exp_int b, Exp_int 2)],
          Exp_binop (Op_add,
            Exp_app (Exp_var (cl "fst"), Exp_var (cl "p")),
            Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))))))] in
      let desc = Printf.sprintf "tuple-expr (%d+1,%d*2)" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 93. Multiple Decl_expr (sequential side effects) *)
    (map2 (fun a b ->
      let prog = [
        Decl_expr (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int a),
                            Exp_app (Exp_var (cl "print_newline"), Exp_unit)));
        Decl_expr (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int b),
                            Exp_app (Exp_var (cl "print_newline"), Exp_unit)))] in
      let desc = Printf.sprintf "multi-decl-expr %d %d" a b in
      (prog, desc)) (int_range 0 99) (int_range 0 99));

    (* 94. Top-level let + multiple Decl_expr *)
    (map (fun n ->
      let prog = [
        Decl_let (cl "x", Exp_int n);
        Decl_expr (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_var (cl "x")),
                            Exp_app (Exp_var (cl "print_newline"), Exp_unit)));
        Decl_expr (Exp_seq (Exp_app (Exp_var (cl "print_int"),
                              Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)),
                            Exp_app (Exp_var (cl "print_newline"), Exp_unit)))] in
      let desc = Printf.sprintf "top-let-multi-expr %d" n in
      (prog, desc)) (int_range 0 49));

    (* 95. Match with wildcard after many int patterns *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_int 0, Exp_int 0);
           (Pat_int 1, Exp_int 10);
           (Pat_int 2, Exp_int 20);
           (Pat_int 3, Exp_int 30);
           (Pat_int 4, Exp_int 40);
           (Pat_int 5, Exp_int 50);
           (Pat_wild, Exp_int (-1))])))] in
      let desc = Printf.sprintf "match-6-arms %d" n in
      (prog, desc)) (int_range 0 7));

    (* 96. Zero edge cases *)
    (return
      (let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add,
          Exp_binop (Op_add,
            Exp_binop (Op_mul, Exp_int 0, Exp_int 42),
            Exp_binop (Op_add, Exp_int 0, Exp_int 0)),
          Exp_binop (Op_sub, Exp_int 0, Exp_int 0))))] in
      let desc = "zero-edge-cases" in
      (prog, desc)));

    (* 97. Nested tuples *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "inner", Exp_tuple [Exp_int a; Exp_int b],
          Exp_binop (Op_mul,
            Exp_app (Exp_var (cl "fst"), Exp_var (cl "inner")),
            Exp_app (Exp_var (cl "snd"), Exp_var (cl "inner"))))))] in
      let desc = Printf.sprintf "nested-tuple %d %d" a b in
      (prog, desc)) (int_range 0 19) (int_range 0 19));

    (* 98. Function returning tuple, then extracting *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "swap",
          Exp_fun (cl "p",
            Exp_tuple [Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"));
                       Exp_app (Exp_var (cl "fst"), Exp_var (cl "p"))]),
          Exp_let (cl "p", Exp_tuple [Exp_int a; Exp_int b],
            Exp_let (cl "q", Exp_app (Exp_var (cl "swap"), Exp_var (cl "p")),
              Exp_binop (Op_add,
                Exp_app (Exp_var (cl "fst"), Exp_var (cl "q")),
                Exp_binop (Op_mul, Exp_int 100,
                  Exp_app (Exp_var (cl "snd"), Exp_var (cl "q")))))))))] in
      let desc = Printf.sprintf "swap-tuple (%d,%d)" a b in
      (prog, desc)) (int_range 0 9) (int_range 0 9));

    (* 99. Pat_tuple: basic 2-tuple destructuring *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_tuple [Exp_int a; Exp_int b],
          [(Pat_tuple [Pat_var (cl "a"); Pat_var (cl "b")],
            Exp_binop (Op_add, Exp_var (cl "a"), Exp_var (cl "b")))])))] in
      let desc = Printf.sprintf "pat-tuple-2 (%d,%d)" a b in
      (prog, desc)) (int_range 0 49) (int_range 0 49));

    (* 100. Pat_tuple: 3-tuple destructuring *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_tuple [Exp_int a; Exp_int b; Exp_int c],
          [(Pat_tuple [Pat_var (cl "a"); Pat_var (cl "b"); Pat_var (cl "c")],
            Exp_binop (Op_add, Exp_var (cl "a"),
              Exp_binop (Op_add, Exp_var (cl "b"), Exp_var (cl "c"))))])))] in
      let desc = Printf.sprintf "pat-tuple-3 (%d,%d,%d)" a b c in
      (prog, desc)) (int_range 0 30) (int_range 0 30) (int_range 0 30));

    (* 101. Pat_tuple: destructure function result *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_fun (cl "x",
            Exp_tuple [Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1);
                       Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)]),
          Exp_match (Exp_app (Exp_var (cl "f"), Exp_int n),
            [(Pat_tuple [Pat_var (cl "a"); Pat_var (cl "b")],
              Exp_binop (Op_add, Exp_var (cl "a"), Exp_var (cl "b")))]))))] in
      let desc = Printf.sprintf "pat-tuple-fn-result f(%d)" n in
      (prog, desc)) (int_range 0 20));

    (* 102. Pat_tuple: swap via destructuring *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "swap",
          Exp_fun (cl "p",
            Exp_match (Exp_var (cl "p"),
              [(Pat_tuple [Pat_var (cl "a"); Pat_var (cl "b")],
                Exp_tuple [Exp_var (cl "b"); Exp_var (cl "a")])])),
          Exp_match (Exp_app (Exp_var (cl "swap"), Exp_tuple [Exp_int a; Exp_int b]),
            [(Pat_tuple [Pat_var (cl "x"); Pat_var (cl "y")],
              Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y")))]))))] in
      let desc = Printf.sprintf "pat-tuple-swap (%d,%d)" a b in
      (prog, desc)) (int_range 0 49) (int_range 0 49));
  ]

(* === Test: cross-validate interpret vs compile+interpret-bytecode === *)

let print_test_case (_prog, desc) = desc

let cross_test =
  QCheck.Test.make
    ~name:"correctness: interpret = interpret-bytecode . compile"
    ~count:500
    (QCheck.make gen_test_case ~print:print_test_case)
    (fun (prog, _desc) ->
       let interp_result = run_source_interp prog in
       let compiled_result = run_compiled prog in
       match interp_result, compiled_result with
       | Interp_ok interp_out, Ok compiled_out ->
         if interp_out = compiled_out then true
         else
           QCheck.Test.fail_reportf
             "Output mismatch!\n  interpret:         %S\n  compile+bytecode:  %S"
             interp_out compiled_out
       | Interp_err "timeout", Error "timeout" ->
         true  (* both timed out -- consistent *)
       | Interp_err interp_err, Error compiled_err ->
         (* both errored -- check if same error *)
         if interp_err = compiled_err then true
         else
           QCheck.Test.fail_reportf
             "Both errored but differently!\n  interpret error:  %S\n  compile error:    %S"
             interp_err compiled_err
       | Interp_ok interp_out, Error compiled_err ->
         QCheck.Test.fail_reportf
           "interpret succeeded but compile+bytecode failed!\n  interpret output:  %S\n  compile error:     %S"
           interp_out compiled_err
       | Interp_err interp_err, Ok compiled_out ->
         QCheck.Test.fail_reportf
           "compile+bytecode succeeded but interpret failed!\n  compile output:    %S\n  interpret error:   %S"
           compiled_out interp_err)

let random_cross_test =
  QCheck.Test.make
    ~name:"correctness (random AST): interpret = interpret-bytecode . compile"
    ~count:1000
    (QCheck.make gen_random_program ~print:(fun (_prog, desc) -> desc))
    (fun (prog, _desc) ->
       let interp_result = run_source_interp prog in
       let compiled_result = run_compiled prog in
       match interp_result, compiled_result with
       | Interp_ok interp_out, Ok compiled_out ->
         if interp_out = compiled_out then true
         else
           QCheck.Test.fail_reportf
             "Output mismatch!\n  interpret:         %S\n  compile+bytecode:  %S"
             interp_out compiled_out
       | Interp_err "timeout", Error "timeout" ->
         true  (* both timed out -- consistent *)
       | Interp_err interp_err, Error compiled_err ->
         if interp_err = compiled_err then true
         else
           QCheck.Test.fail_reportf
             "Both errored but differently!\n  interpret error:  %S\n  compile error:    %S"
             interp_err compiled_err
       | Interp_ok interp_out, Error compiled_err ->
         QCheck.Test.fail_reportf
           "interpret succeeded but compile+bytecode failed!\n  interpret output:  %S\n  compile error:     %S"
           interp_out compiled_err
       | Interp_err interp_err, Ok compiled_out ->
         QCheck.Test.fail_reportf
           "compile+bytecode succeeded but interpret failed!\n  compile output:    %S\n  interpret error:   %S"
           compiled_out interp_err)

let () =
  exit (QCheck_base_runner.run_tests ~verbose:true [cross_test; random_cross_test])
