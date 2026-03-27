(* harness.ml - Step 5 PBT: our compiler (Compile.v) vs ocamlc.
   For each generated program:
   1. Compile AST with compile_program -> run through our bytecode interpreter
   2. Compile OCaml source with ocamlc -> run with ocamlrun
   3. Compare outputs *)

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
      (1, gen_letrec depth scope);
      (1, gen_closure depth scope);
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

and gen_letrec (depth : int) (scope : string list) : (expr * string) QCheck.Gen.t =
  let open QCheck.Gen in
  let d = depth - 1 in
  gen_fresh_var scope >>= fun fname ->
  gen_fresh_var (fname :: scope) >>= fun param ->
  (* Recursive function body: simple countdown that sums *)
  gen_int_expr d (param :: fname :: scope) >>= fun (base_e, base_s) ->
  gen_int_expr d scope >>= fun (arg_e, arg_s) ->
  let body_e =
    Exp_if (Exp_binop (Op_le, Exp_var (cl param), Exp_int 0),
      base_e,
      Exp_binop (Op_add, Exp_int 1,
        Exp_app (Exp_var (cl fname),
          Exp_binop (Op_sub, Exp_var (cl param), Exp_int 1)))) in
  let body_s = Printf.sprintf "if %s <= 0 then %s else 1 + %s (%s - 1)" param base_s fname param in
  return (Exp_letrec (cl fname,
            Exp_fun (cl param, body_e),
            Exp_app (Exp_var (cl fname), arg_e)),
          parens ("let rec " ^ fname ^ " " ^ param ^ " = " ^ body_s ^
                  " in " ^ fname ^ " " ^ parens arg_s))

and gen_closure (depth : int) (scope : string list) : (expr * string) QCheck.Gen.t =
  let open QCheck.Gen in
  let d = depth - 1 in
  match scope with
  | [] ->
    (* No variables to capture, just generate a regular let *)
    gen_let d scope
  | _ ->
    (* Pick a variable from scope to capture in the closure *)
    oneofl scope >>= fun captured ->
    gen_fresh_var scope >>= fun fname ->
    gen_fresh_var (fname :: scope) >>= fun param ->
    gen_int_expr d (param :: scope) >>= fun (body_e, body_s) ->
    gen_int_expr d scope >>= fun (arg_e, arg_s) ->
    let closure_body = Exp_binop (Op_add, Exp_var (cl captured), body_e) in
    let closure_body_s = captured ^ " + " ^ body_s in
    return (Exp_let (cl fname,
              Exp_fun (cl param, closure_body),
              Exp_app (Exp_var (cl fname), arg_e)),
            parens ("let " ^ fname ^ " " ^ param ^ " = " ^ closure_body_s ^
                    " in " ^ fname ^ " " ^ parens arg_s))

(* Generate a complete program with OCaml source for ocamlc *)
let gen_random_program_with_source : (decl list * string) QCheck.Gen.t =
  let open QCheck.Gen in
  int_range 1 3 >>= fun depth ->
  gen_int_expr depth [] >>= fun (e, s) ->
  let prog = [Decl_expr (print_int_nl e)] in
  let src = Printf.sprintf "let () = print_int (%s); print_newline ()" s in
  return (prog, src)

(* === QCheck generators producing (prog, source) pairs === *)

let gen_test_case : (decl list * string) QCheck.Gen.t =
  let open QCheck.Gen in
  oneof [
    (* --- Original generators (1-28) --- *)

    (* 1. Print a single integer *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl (Exp_int n))] in
      let src = Printf.sprintf "let () = print_int (%d); print_newline ()" n in
      (prog, src)) (int_range (-100) 99));

    (* 2. Addition *)
    (map2 (fun a b ->
      let b = b + 1 in
      let prog = [Decl_expr (print_int_nl (Exp_binop (Op_add, Exp_int a, Exp_int b)))] in
      let src = Printf.sprintf "let () = print_int (%d + %d); print_newline ()" a b in
      (prog, src)) (int_range 0 99) (int_range 0 99));

    (* 3. Subtraction *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl (Exp_binop (Op_sub, Exp_int a, Exp_int b)))] in
      let src = Printf.sprintf "let () = print_int (%d - %d); print_newline ()" a b in
      (prog, src)) (int_range 0 99) (int_range 0 99));

    (* 4. Multiplication *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl (Exp_binop (Op_mul, Exp_int a, Exp_int b)))] in
      let src = Printf.sprintf "let () = print_int (%d * %d); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* 5. If with Op_gt *)
    (map2 (fun n t ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_binop (Op_gt, Exp_int n, Exp_int t), Exp_int 1, Exp_int 0)))] in
      let src = Printf.sprintf "let () = print_int (if %d > %d then 1 else 0); print_newline ()" n t in
      (prog, src)) (int_range 0 99) (int_range 0 99));

    (* 6. Let x, let y, add *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "y", Exp_int b,
            Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y"))))))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in let y = %d in x + y); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 7. Function: double *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "x"))),
          Exp_app (Exp_var (cl "f"), Exp_int n))))] in
      let src = Printf.sprintf "let () = print_int (let f x = x + x in f %d); print_newline ()" n in
      (prog, src)) (int_range 0 49));

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
      let src = Printf.sprintf "let () = print_int (let rec fact n = if n <= 1 then 1 else n * fact (n-1) in fact %d); print_newline ()" n in
      (prog, src)) (int_range 0 9));

    (* 9. Tuple fst + snd *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "p", Exp_tuple [Exp_int a; Exp_int b],
          Exp_binop (Op_add,
            Exp_app (Exp_var (cl "fst"), Exp_var (cl "p")),
            Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))))))] in
      let src = Printf.sprintf "let () = print_int (let p = (%d, %d) in fst p + snd p); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* 10. Match on ints: 0, 1, wildcard *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_int 0, Exp_int 100);
           (Pat_int 1, Exp_int 200);
           (Pat_wild, Exp_int 999)])))] in
      let src = Printf.sprintf "let () = print_int (match %d with 0 -> 100 | 1 -> 200 | _ -> 999); print_newline ()" n in
      (prog, src)) (int_range 0 2));

    (* 11. Two-argument function *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_fun (cl "x", Exp_fun (cl "y",
            Exp_binop (Op_add, Exp_binop (Op_mul, Exp_var (cl "x"), Exp_var (cl "y")), Exp_int 1))),
          Exp_app (Exp_app (Exp_var (cl "f"), Exp_int a), Exp_int b))))] in
      let src = Printf.sprintf "let () = print_int (let f x y = x * y + 1 in f %d %d); print_newline ()" a b in
      (prog, src)) (int_range 0 29) (int_range 0 29));

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
      let src = Printf.sprintf "let () = print_int (let rec fib n = if n <= 1 then n else fib (n-1) + fib (n-2) in fib %d); print_newline ()" n in
      (prog, src)) (int_range 0 11));

    (* 13. Unary negation *)
    (map (fun a ->
      let prog = [Decl_expr (print_int_nl (Exp_unop (Op_neg, Exp_int a)))] in
      let src = Printf.sprintf "let () = print_int (- %d); print_newline ()" a in
      (prog, src)) (int_range 0 99));

    (* 14. Mixed arithmetic: a * b + c *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add, Exp_binop (Op_mul, Exp_int a, Exp_int b), Exp_int c)))] in
      let src = Printf.sprintf "let () = print_int (%d * %d + %d); print_newline ()" a b c in
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 15. Match with Pat_var binding *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_int 0, Exp_int 42);
           (Pat_var (cl "x"), Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1))])))] in
      let src = Printf.sprintf "let () = print_int (match %d with 0 -> 42 | x -> x + 1); print_newline ()" n in
      (prog, src)) (int_range 0 99));

    (* 16. Match on computed expression *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_binop (Op_sub, Exp_int a, Exp_int b),
          [(Pat_int 0, Exp_int 1);
           (Pat_wild, Exp_int 0)])))] in
      let src = Printf.sprintf "let () = print_int (match %d - %d with 0 -> 1 | _ -> 0); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 17. Match with many branches *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_int 0, Exp_int 10); (Pat_int 1, Exp_int 20);
           (Pat_int 2, Exp_int 30); (Pat_int 3, Exp_int 40);
           (Pat_wild, Exp_int 50)])))] in
      let src = Printf.sprintf "let () = print_int (match %d with 0 -> 10 | 1 -> 20 | 2 -> 30 | 3 -> 40 | _ -> 50); print_newline ()" n in
      (prog, src)) (int_range 0 4));

    (* 18. Match with if in branch body *)
    (map2 (fun n m ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_int 0, Exp_if (Exp_binop (Op_gt, Exp_int m, Exp_int 5), Exp_int 1, Exp_int 0));
           (Pat_wild, Exp_int 99)])))] in
      let src = Printf.sprintf "let () = print_int (match %d with 0 -> if %d > 5 then 1 else 0 | _ -> 99); print_newline ()" n m in
      (prog, src)) (int_range 0 2) (int_range 0 9));

    (* 19. Function with match body *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_fun (cl "x",
            Exp_match (Exp_var (cl "x"),
              [(Pat_int 0, Exp_int 100); (Pat_int 1, Exp_int 200); (Pat_wild, Exp_int 300)])),
          Exp_app (Exp_var (cl "f"), Exp_int n))))] in
      let src = Printf.sprintf "let () = print_int (let f x = match x with 0 -> 100 | 1 -> 200 | _ -> 300 in f %d); print_newline ()" n in
      (prog, src)) (int_range 0 2));

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
      let src = Printf.sprintf "let () = print_int (let a = %d in let b = %d in let c = %d in let d = %d in a + b + c + d); print_newline ()" a b c d in
      (prog, src)) (int_range 0 9));

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
      let src = Printf.sprintf "let () = print_int (let rec count n = match n with 0 -> 0 | x -> 1 + count (x - 1) in count %d); print_newline ()" n in
      (prog, src)) (int_range 0 7));

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
      let src = Printf.sprintf "let rec fact n = if n <= 1 then 1 else n * fact (n-1)\nlet () = print_int (fact %d); print_newline ()" n in
      (prog, src)) (int_range 0 9));

    (* 23. Tuple fst - snd *)
    (map2 (fun a b ->
      let a = a + 10 in
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "p", Exp_tuple [Exp_int a; Exp_int b],
          Exp_binop (Op_sub,
            Exp_app (Exp_var (cl "fst"), Exp_var (cl "p")),
            Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))))))] in
      let src = Printf.sprintf "let () = print_int (let p = (%d, %d) in fst p - snd p); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* 24. Division + modulo *)
    (map2 (fun a b ->
      let a = a + 1 in let b = b + 1 in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add,
          Exp_binop (Op_div, Exp_int a, Exp_int b),
          Exp_binop (Op_mod, Exp_int a, Exp_int b))))] in
      let src = Printf.sprintf "let () = print_int (%d / %d + %d mod %d); print_newline ()" a b a b in
      (prog, src)) (int_range 0 499) (int_range 0 19));

    (* 25. Nested function application: f (g n) *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)),
          Exp_let (cl "g", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)),
            Exp_app (Exp_var (cl "f"), Exp_app (Exp_var (cl "g"), Exp_int n))))))] in
      let src = Printf.sprintf "let () = print_int (let f x = x + 1 in let g x = x * 2 in f (g %d)); print_newline ()" n in
      (prog, src)) (int_range 0 19));

    (* 26. Curried function (make_adder) *)
    (map2 (fun n m ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "make_adder",
          Exp_fun (cl "n", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "n")))),
          Exp_app (Exp_app (Exp_var (cl "make_adder"), Exp_int n), Exp_int m))))] in
      let src = Printf.sprintf "let () = print_int (let make_adder n x = n + x in make_adder %d %d); print_newline ()" n m in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 27. Sequential print of two ints *)
    (map2 (fun a b ->
      let prog = [Decl_expr
        (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int a),
          Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int b),
            Exp_app (Exp_var (cl "print_newline"), Exp_unit))))] in
      let src = Printf.sprintf "let () = print_int %d; print_int %d; print_newline ()" a b in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 28. Multiple comparison operators combined *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add,
          Exp_binop (Op_add,
            Exp_if (Exp_binop (Op_lt, Exp_int a, Exp_int b), Exp_int 1, Exp_int 0),
            Exp_if (Exp_binop (Op_eq, Exp_int a, Exp_int b), Exp_int 10, Exp_int 0)),
          Exp_if (Exp_binop (Op_ge, Exp_int a, Exp_int b), Exp_int 100, Exp_int 0))))] in
      let src = Printf.sprintf "let () = print_int ((if %d < %d then 1 else 0) + (if %d = %d then 10 else 0) + (if %d >= %d then 100 else 0)); print_newline ()" a b a b a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 29. Variable shadowing *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int b),
            Exp_var (cl "x")))))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in let x = x + %d in x); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 30. Partial application *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "add",
          Exp_fun (cl "x", Exp_fun (cl "y", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y")))),
          Exp_let (cl "inc", Exp_app (Exp_var (cl "add"), Exp_int 1),
            Exp_app (Exp_var (cl "inc"), Exp_int n)))))] in
      let src = Printf.sprintf "let () = print_int (let add x y = x + y in let inc = add 1 in inc %d); print_newline ()" n in
      (prog, src)) (int_range 0 49));

    (* --- New generators (31-58) --- *)

    (* 31. Match on bool patterns: match true/false with true -> ... | false -> ... *)
    (map (fun b ->
      let bval = if b then 1 else 0 in
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_bool (b),
          [(Pat_bool true, Exp_int 1);
           (Pat_bool false, Exp_int 0)])))] in
      let src = Printf.sprintf "let () = print_int (match %s with true -> 1 | false -> 0); print_newline ()" (if b then "true" else "false") in
      ignore bval;
      (prog, src)) QCheck.Gen.bool);

    (* 32. Match on bool patterns with expressions *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_bool (a > b),
          [(Pat_bool true, Exp_int a);
           (Pat_bool false, Exp_int b)])))] in
      let src = Printf.sprintf "let () = print_int (match %d > %d with true -> %d | false -> %d); print_newline ()" a b a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 33. Match with Pat_unit: match () with () -> 42 *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_unit,
          [(Pat_unit, Exp_int n)])))] in
      let src = Printf.sprintf "let () = print_int (match () with () -> %d); print_newline ()" n in
      (prog, src)) (int_range 0 99));

    (* 34. Nested match: match on outer, then inner *)
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
      let src = Printf.sprintf "let () = print_int (match %d with 0 -> (match %d with 0 -> 10 | _ -> 20) | _ -> (match %d with 0 -> 30 | _ -> 40)); print_newline ()" x y y in
      (prog, src)) (int_range 0 2) (int_range 0 2));

    (* 35. Nested match: outer match feeds into inner match via Pat_var *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_var (cl "x"),
            Exp_match (Exp_var (cl "x"),
              [(Pat_int 0, Exp_int 100);
               (Pat_int 1, Exp_int 200);
               (Pat_wild, Exp_int 300)]))])))] in
      let src = Printf.sprintf "let () = print_int (match %d with x -> (match x with 0 -> 100 | 1 -> 200 | _ -> 300)); print_newline ()" n in
      (prog, src)) (int_range 0 3));

    (* 36. 3-element tuple: create and verify via nested 2-tuples *)
    (* We create (a, b, c) as a 3-tuple, then create (a, b) and verify fst/snd
       match the first two elements. The 3-tuple creation exercises MAKEBLOCK3. *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "t3", Exp_tuple [Exp_int a; Exp_int b; Exp_int c],
          Exp_let (cl "t2", Exp_tuple [Exp_int a; Exp_int b],
            Exp_binop (Op_add,
              Exp_app (Exp_var (cl "fst"), Exp_var (cl "t2")),
              Exp_app (Exp_var (cl "snd"), Exp_var (cl "t2")))))))] in
      let src = Printf.sprintf "let () = print_int (let _t3 = (%d, %d, %d) in let t2 = (%d, %d) in fst t2 + snd t2); print_newline ()" a b c a b in
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 37. 3-element tuple: create and use first two elements via nested pairs *)
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
      let src = Printf.sprintf "let () = print_int (let x = %d in let y = %d in let z = %d in let p = (x, y) in fst p + snd p + z); print_newline ()" a b c in
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 38. Closure: function captures free variable *)
    (map2 (fun x y ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int x,
          Exp_let (cl "f", Exp_fun (cl "y", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y"))),
            Exp_app (Exp_var (cl "f"), Exp_int y)))))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in let f y = x + y in f %d); print_newline ()" x y in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* 39. Closure: function captures two free variables *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "a", Exp_int a,
          Exp_let (cl "b", Exp_int b,
            Exp_let (cl "f", Exp_fun (cl "c",
              Exp_binop (Op_add, Exp_var (cl "a"),
                Exp_binop (Op_add, Exp_var (cl "b"), Exp_var (cl "c")))),
              Exp_app (Exp_var (cl "f"), Exp_int c))))))] in
      let src = Printf.sprintf "let () = print_int (let a = %d in let b = %d in let f c = a + b + c in f %d); print_newline ()" a b c in
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 40. Closure: returned function captures variable *)
    (map2 (fun n m ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "make_mul",
          Exp_fun (cl "n", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "n"), Exp_var (cl "x")))),
          Exp_let (cl "double", Exp_app (Exp_var (cl "make_mul"), Exp_int n),
            Exp_app (Exp_var (cl "double"), Exp_int m)))))] in
      let src = Printf.sprintf "let () = print_int (let make_mul n x = n * x in let double = make_mul %d in double %d); print_newline ()" n m in
      (prog, src)) (int_range 1 9) (int_range 0 19));

    (* 41. Recursive function with closure: captures free variable *)
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
      let src = Printf.sprintf "let () = print_int (let base = %d in let rec f n = if n <= 0 then base else 1 + f (n - 1) in f %d); print_newline ()" base n in
      (prog, src)) (int_range 10 30) (int_range 0 7));

    (* 42. Multiple sequential print statements (3 ints) *)
    (map3 (fun a b c ->
      let prog = [Decl_expr
        (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int a),
          Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int b),
            Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int c),
              Exp_app (Exp_var (cl "print_newline"), Exp_unit)))))] in
      let src = Printf.sprintf "let () = print_int %d; print_int %d; print_int %d; print_newline ()" a b c in
      (prog, src)) (int_range 0 9) (int_range 0 9) (int_range 0 9));

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
      let src = Printf.sprintf "let () = print_int %d; print_int %d; print_int %d; print_int %d; print_newline ()" a b c d in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 44. Nested function application: f (g (h x)) *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "h", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)),
          Exp_let (cl "g", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)),
            Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_sub, Exp_var (cl "x"), Exp_int 3)),
              Exp_app (Exp_var (cl "f"),
                Exp_app (Exp_var (cl "g"),
                  Exp_app (Exp_var (cl "h"), Exp_int n))))))))] in
      let src = Printf.sprintf "let () = print_int (let h x = x + 1 in let g x = x * 2 in let f x = x - 3 in f (g (h %d))); print_newline ()" n in
      (prog, src)) (int_range 0 19));

    (* 45. Higher-order function: apply f x = f x *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "apply",
          Exp_fun (cl "f", Exp_fun (cl "x", Exp_app (Exp_var (cl "f"), Exp_var (cl "x")))),
          Exp_app (Exp_app (Exp_var (cl "apply"),
            Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1))),
            Exp_int n))))] in
      let src = Printf.sprintf "let () = print_int (let apply f x = f x in apply (fun x -> x + 1) %d); print_newline ()" n in
      (prog, src)) (int_range 0 49));

    (* 46. Higher-order function: apply_twice f x = f (f x) *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "apply_twice",
          Exp_fun (cl "f", Exp_fun (cl "x",
            Exp_app (Exp_var (cl "f"), Exp_app (Exp_var (cl "f"), Exp_var (cl "x"))))),
          Exp_app (Exp_app (Exp_var (cl "apply_twice"),
            Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1))),
            Exp_int n))))] in
      let src = Printf.sprintf "let () = print_int (let apply_twice f x = f (f x) in apply_twice (fun x -> x + 1) %d); print_newline ()" n in
      (prog, src)) (int_range 0 49));

    (* 47. Higher-order: map-like, apply function to each element of pair *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)),
          Exp_let (cl "p", Exp_tuple [Exp_int a; Exp_int b],
            Exp_binop (Op_add,
              Exp_app (Exp_var (cl "f"), Exp_app (Exp_var (cl "fst"), Exp_var (cl "p"))),
              Exp_app (Exp_var (cl "f"), Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))))))))] in
      let src = Printf.sprintf "let () = print_int (let f x = x * 2 in let p = (%d, %d) in f (fst p) + f (snd p)); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 48. Op_neq explicit test *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_binop (Op_neq, Exp_int a, Exp_int b), Exp_int 1, Exp_int 0)))] in
      let src = Printf.sprintf "let () = print_int (if %d <> %d then 1 else 0); print_newline ()" a b in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 49. Op_le explicit test *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_binop (Op_le, Exp_int a, Exp_int b), Exp_int 1, Exp_int 0)))] in
      let src = Printf.sprintf "let () = print_int (if %d <= %d then 1 else 0); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 50. Op_ge explicit test *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_binop (Op_ge, Exp_int a, Exp_int b), Exp_int 1, Exp_int 0)))] in
      let src = Printf.sprintf "let () = print_int (if %d >= %d then 1 else 0); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

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
      let src = Printf.sprintf "let () = print_int ((if %d = %d then 1 else 0) + (if %d <> %d then 10 else 0) + (if %d < %d then 100 else 0) + (if %d <= %d then 1000 else 0) + (if %d > %d then 10000 else 0) + (if %d >= %d then 100000 else 0)); print_newline ()" a b a b a b a b a b a b in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 52. Variable shadowing in nested scopes: inner x shadows outer x *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "y",
            Exp_let (cl "x", Exp_int b,
              Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)),
            Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y"))))))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in let y = (let x = %d in x + 1) in x + y); print_newline ()" a b in
      ignore c;
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 53. Variable shadowing: function parameter shadows outer binding *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)),
            Exp_binop (Op_add, Exp_var (cl "x"),
              Exp_app (Exp_var (cl "f"), Exp_int b))))))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in let f x = x * 2 in x + f %d); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 54. Triple variable shadowing *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int n,
          Exp_let (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1),
            Exp_let (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2),
              Exp_var (cl "x"))))))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in let x = x + 1 in let x = x * 2 in x); print_newline ()" n in
      (prog, src)) (int_range 0 19));

    (* 55. Top-level Decl_let followed by Decl_expr using it *)
    (map (fun n ->
      let prog = [
        Decl_let (cl "x", Exp_int n);
        Decl_expr (print_int_nl (Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)))] in
      let src = Printf.sprintf "let x = %d\nlet () = print_int (x + 1); print_newline ()" n in
      (prog, src)) (int_range 0 99));

    (* 56. Multiple top-level Decl_let declarations *)
    (map2 (fun a b ->
      let prog = [
        Decl_let (cl "x", Exp_int a);
        Decl_let (cl "y", Exp_int b);
        Decl_expr (print_int_nl (Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y"))))] in
      let src = Printf.sprintf "let x = %d\nlet y = %d\nlet () = print_int (x + y); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* 57. Three top-level Decl_let + computed Decl_let *)
    (map3 (fun a b c ->
      let prog = [
        Decl_let (cl "a", Exp_int a);
        Decl_let (cl "b", Exp_int b);
        Decl_let (cl "c", Exp_int c);
        Decl_let (cl "sum", Exp_binop (Op_add, Exp_var (cl "a"),
          Exp_binop (Op_add, Exp_var (cl "b"), Exp_var (cl "c"))));
        Decl_expr (print_int_nl (Exp_var (cl "sum")))] in
      let src = Printf.sprintf "let a = %d\nlet b = %d\nlet c = %d\nlet sum = a + b + c\nlet () = print_int sum; print_newline ()" a b c in
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 58. Top-level Decl_let with function + Decl_expr calling it *)
    (map (fun n ->
      let prog = [
        Decl_let (cl "double", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)));
        Decl_expr (print_int_nl (Exp_app (Exp_var (cl "double"), Exp_int n)))] in
      let src = Printf.sprintf "let double x = x * 2\nlet () = print_int (double %d); print_newline ()" n in
      (prog, src)) (int_range 0 49));

    (* 59. Match with Pat_var binding: single arm *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_binop (Op_add, Exp_int n, Exp_int 1),
          [(Pat_var (cl "x"), Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2))])))] in
      let src = Printf.sprintf "let () = print_int (match %d + 1 with x -> x * 2); print_newline ()" n in
      (prog, src)) (int_range 0 49));

    (* 60. Deeply nested let bindings (5 levels) *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "a", Exp_int n,
          Exp_let (cl "b", Exp_binop (Op_add, Exp_var (cl "a"), Exp_int 1),
            Exp_let (cl "c", Exp_binop (Op_mul, Exp_var (cl "b"), Exp_int 2),
              Exp_let (cl "d", Exp_binop (Op_sub, Exp_var (cl "c"), Exp_int 3),
                Exp_let (cl "e", Exp_binop (Op_add, Exp_var (cl "d"), Exp_var (cl "a")),
                  Exp_var (cl "e"))))))))] in
      let src = Printf.sprintf "let () = print_int (let a = %d in let b = a + 1 in let c = b * 2 in let d = c - 3 in let e = d + a in e); print_newline ()" n in
      (prog, src)) (int_range 0 19));

    (* 61. Deeply nested let bindings (6 levels) with all variables used *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "v1", Exp_int n,
          Exp_let (cl "v2", Exp_binop (Op_add, Exp_var (cl "v1"), Exp_int 1),
            Exp_let (cl "v3", Exp_binop (Op_add, Exp_var (cl "v1"), Exp_var (cl "v2")),
              Exp_let (cl "v4", Exp_binop (Op_add, Exp_var (cl "v2"), Exp_var (cl "v3")),
                Exp_let (cl "v5", Exp_binop (Op_add, Exp_var (cl "v3"), Exp_var (cl "v4")),
                  Exp_let (cl "v6", Exp_binop (Op_add, Exp_var (cl "v4"), Exp_var (cl "v5")),
                    Exp_var (cl "v6")))))))))] in
      let src = Printf.sprintf "let () = print_int (let v1 = %d in let v2 = v1 + 1 in let v3 = v1 + v2 in let v4 = v2 + v3 in let v5 = v3 + v4 in let v6 = v4 + v5 in v6); print_newline ()" n in
      (prog, src)) (int_range 0 9));

    (* 62. Function composition: compose f g x = f (g x) *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "compose",
          Exp_fun (cl "f", Exp_fun (cl "g", Exp_fun (cl "x",
            Exp_app (Exp_var (cl "f"), Exp_app (Exp_var (cl "g"), Exp_var (cl "x")))))),
          Exp_app (Exp_app (Exp_app (Exp_var (cl "compose"),
            Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 10))),
            Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 3))),
            Exp_int n))))] in
      let src = Printf.sprintf "let () = print_int (let compose f g x = f (g x) in compose (fun x -> x + 10) (fun x -> x * 3) %d); print_newline ()" n in
      (prog, src)) (int_range 0 19));

    (* 63. Function composition with top-level decls *)
    (map (fun n ->
      let prog = [
        Decl_let (cl "inc", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)));
        Decl_let (cl "dbl", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)));
        Decl_expr (print_int_nl
          (Exp_app (Exp_var (cl "inc"), Exp_app (Exp_var (cl "dbl"), Exp_int n))))] in
      let src = Printf.sprintf "let inc x = x + 1\nlet dbl x = x * 2\nlet () = print_int (inc (dbl %d)); print_newline ()" n in
      (prog, src)) (int_range 0 19));

    (* 64. Division with non-trivial values *)
    (map2 (fun a b ->
      let a = a + 2 in let b = b + 2 in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_div, Exp_binop (Op_mul, Exp_int a, Exp_int b), Exp_int b)))] in
      let src = Printf.sprintf "let () = print_int (%d * %d / %d); print_newline ()" a b b in
      (prog, src)) (int_range 0 49) (int_range 0 19));

    (* 65. Modulo with non-trivial values *)
    (map2 (fun a b ->
      let b = b + 2 in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_mod, Exp_int a, Exp_int b)))] in
      let src = Printf.sprintf "let () = print_int (%d mod %d); print_newline ()" a b in
      (prog, src)) (int_range 0 99) (int_range 0 19));

    (* 66. Division and modulo: a = (a/b)*b + (a mod b) *)
    (map2 (fun a b ->
      let b = b + 1 in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add,
          Exp_binop (Op_mul, Exp_binop (Op_div, Exp_int a, Exp_int b), Exp_int b),
          Exp_binop (Op_mod, Exp_int a, Exp_int b))))] in
      let src = Printf.sprintf "let () = print_int ((%d / %d) * %d + %d mod %d); print_newline ()" a b b a b in
      (prog, src)) (int_range 0 99) (int_range 0 19));

    (* 67. Negative number arithmetic: addition *)
    (map2 (fun a b ->
      let a = -a in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add, Exp_int a, Exp_int b)))] in
      let src = Printf.sprintf "let () = print_int ((%d) + %d); print_newline ()" a b in
      (prog, src)) (int_range 1 50) (int_range 0 99));

    (* 68. Negative number arithmetic: multiplication *)
    (map2 (fun a b ->
      let a = -a in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_mul, Exp_int a, Exp_int b)))] in
      let src = Printf.sprintf "let () = print_int ((%d) * %d); print_newline ()" a b in
      (prog, src)) (int_range 1 20) (int_range 0 20));

    (* 69. Negative number arithmetic: subtraction producing negative *)
    (map2 (fun a b ->
      let b = b + a + 1 in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_sub, Exp_int a, Exp_int b)))] in
      let src = Printf.sprintf "let () = print_int (%d - %d); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 1 50));

    (* 70. Double negation *)
    (map (fun a ->
      let prog = [Decl_expr (print_int_nl
        (Exp_unop (Op_neg, Exp_unop (Op_neg, Exp_int a))))] in
      let src = Printf.sprintf "let () = print_int (- (- %d)); print_newline ()" a in
      (prog, src)) (int_range 0 99));

    (* 71. Complex: if inside let *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_if (Exp_binop (Op_gt, Exp_int a, Exp_int b), Exp_int a, Exp_int b),
          Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2))))] in
      let src = Printf.sprintf "let () = print_int (let x = if %d > %d then %d else %d in x * 2); print_newline ()" a b a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 72. Complex: let inside if branches *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_binop (Op_lt, Exp_int a, Exp_int b),
          Exp_let (cl "x", Exp_binop (Op_sub, Exp_int b, Exp_int a),
            Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 10)),
          Exp_let (cl "x", Exp_binop (Op_sub, Exp_int a, Exp_int b),
            Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 20)))))] in
      let src = Printf.sprintf "let () = print_int (if %d < %d then (let x = %d - %d in x * 10) else (let x = %d - %d in x * 20)); print_newline ()" a b b a a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 73. Complex: match inside let, let inside match *)
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
      let src = Printf.sprintf "let () = print_int (let classify n = match n with 0 -> 0 | x -> if x > 0 then 1 else -1 in let r = classify %d in r * 100); print_newline ()" n in
      (prog, src)) (int_range (-5) 5));

    (* 74. Complex: nested if/let/match combo *)
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
      let src = Printf.sprintf "let () = print_int (let x = %d in let y = %d in if x > y then (match x with 0 -> 0 | _ -> x + y) else (match y with 0 -> 0 | _ -> x * y)); print_newline ()" a b in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 75. Op_not (boolean negation) -- BOOLNOT flips 0<->1 *)
    (map (fun a ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (
          Exp_unop (Op_not, Exp_binop (Op_eq, Exp_int a, Exp_int 0)),
          Exp_int 1, Exp_int 0)))] in
      let src = Printf.sprintf "let () = print_int (if not (%d = 0) then 1 else 0); print_newline ()" a in
      (prog, src)) (int_range 0 5));

    (* 76. Op_not on comparisons *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (
          Exp_unop (Op_not, Exp_binop (Op_gt, Exp_int a, Exp_int b)),
          Exp_int 1, Exp_int 0)))] in
      let src = Printf.sprintf "let () = print_int (if not (%d > %d) then 1 else 0); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 77. Exp_bool true/false in if condition *)
    (map (fun b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_bool b, Exp_int 42, Exp_int 0)))] in
      let src = Printf.sprintf "let () = print_int (if %s then 42 else 0); print_newline ()" (if b then "true" else "false") in
      (prog, src)) QCheck.Gen.bool);

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
      let src = Printf.sprintf "let rec sum n = if n <= 0 then 0 else n + sum (n - 1)\nlet result = sum %d\nlet () = print_int result; print_newline ()" n in
      (prog, src)) (int_range 0 10));

    (* 79. Closure: function applied to tuple component *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "p", Exp_tuple [Exp_int a; Exp_int b],
          Exp_let (cl "add1", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)),
            Exp_binop (Op_add,
              Exp_app (Exp_var (cl "add1"), Exp_app (Exp_var (cl "fst"), Exp_var (cl "p"))),
              Exp_app (Exp_var (cl "add1"), Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))))))))] in
      let src = Printf.sprintf "let () = print_int (let p = (%d, %d) in let add1 x = x + 1 in add1 (fst p) + add1 (snd p)); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

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
      let src = Printf.sprintf "let () = print_int (let rec sum_acc n acc = if n <= 0 then acc else sum_acc (n - 1) (acc + n) in sum_acc %d 0); print_newline ()" n in
      (prog, src)) (int_range 0 10));

    (* 81. Recursive power function with closure *)
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
      let src = Printf.sprintf "let () = print_int (let b = %d in let rec power n = if n <= 0 then 1 else b * power (n - 1) in power %d); print_newline ()" base exp in
      (prog, src)) (int_range 1 4) (int_range 0 5));

    (* 82. Sequence: compute then print *)
    (map2 (fun a b ->
      let prog = [Decl_expr
        (Exp_let (cl "x", Exp_binop (Op_add, Exp_int a, Exp_int b),
          Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_var (cl "x")),
            Exp_app (Exp_var (cl "print_newline"), Exp_unit))))] in
      let src = Printf.sprintf "let () = let x = %d + %d in print_int x; print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* 83. Sequence: multiple computations + prints *)
    (map2 (fun a b ->
      let prog = [Decl_expr
        (Exp_let (cl "x", Exp_binop (Op_add, Exp_int a, Exp_int b),
          Exp_let (cl "y", Exp_binop (Op_mul, Exp_int a, Exp_int b),
            Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_var (cl "x")),
              Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_var (cl "y")),
                Exp_app (Exp_var (cl "print_newline"), Exp_unit))))))] in
      let src = Printf.sprintf "let () = let x = %d + %d in let y = %d * %d in print_int x; print_int y; print_newline ()" a b a b in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 84. Match on bool result of comparison *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_binop (Op_lt, Exp_int a, Exp_int b),
          [(Pat_bool true, Exp_binop (Op_sub, Exp_int b, Exp_int a));
           (Pat_bool false, Exp_binop (Op_sub, Exp_int a, Exp_int b))])))] in
      let src = Printf.sprintf "let () = print_int (match %d < %d with true -> %d - %d | false -> %d - %d); print_newline ()" a b b a a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 85. Identity function *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "id", Exp_fun (cl "x", Exp_var (cl "x")),
          Exp_app (Exp_var (cl "id"), Exp_int n))))] in
      let src = Printf.sprintf "let () = print_int (let id x = x in id %d); print_newline ()" n in
      (prog, src)) (int_range (-50) 50));

    (* 86. Constant function *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "const",
          Exp_fun (cl "x", Exp_fun (cl "y", Exp_var (cl "x"))),
          Exp_app (Exp_app (Exp_var (cl "const"), Exp_int a), Exp_int b))))] in
      let src = Printf.sprintf "let () = print_int (let const x _y = x in const %d %d); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

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
      let src = Printf.sprintf "let () = print_int (let flip f x y = f y x in flip (fun x y -> x - y) %d %d); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 88. Multiple top-level functions calling each other *)
    (map (fun n ->
      let prog = [
        Decl_let (cl "add1", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)));
        Decl_let (cl "add2", Exp_fun (cl "x", Exp_app (Exp_var (cl "add1"), Exp_app (Exp_var (cl "add1"), Exp_var (cl "x")))));
        Decl_expr (print_int_nl (Exp_app (Exp_var (cl "add2"), Exp_int n)))] in
      let src = Printf.sprintf "let add1 x = x + 1\nlet add2 x = add1 (add1 x)\nlet () = print_int (add2 %d); print_newline ()" n in
      (prog, src)) (int_range 0 49));

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
      let src = Printf.sprintf "let () = print_int (let rec gcd a b = if b = 0 then a else gcd b (a mod b) in gcd %d %d); print_newline ()" a b in
      (prog, src)) (int_range 1 50) (int_range 1 50));

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
      let src = Printf.sprintf "let () = print_int (let rec f n = match n with 0 -> 1 | 1 -> 1 | 2 -> 2 | x -> f (x - 1) + f (x - 3) in f %d); print_newline ()" n in
      (prog, src)) (int_range 0 9));

    (* 91. Chained let with function calls *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)),
          Exp_let (cl "a", Exp_app (Exp_var (cl "f"), Exp_int n),
            Exp_let (cl "b", Exp_app (Exp_var (cl "f"), Exp_var (cl "a")),
              Exp_let (cl "c", Exp_app (Exp_var (cl "f"), Exp_var (cl "b")),
                Exp_var (cl "c")))))))] in
      let src = Printf.sprintf "let () = print_int (let f x = x + 1 in let a = f %d in let b = f a in let c = f b in c); print_newline ()" n in
      (prog, src)) (int_range 0 49));

    (* 92. Tuple of expressions *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "p",
          Exp_tuple [Exp_binop (Op_add, Exp_int a, Exp_int 1);
                     Exp_binop (Op_mul, Exp_int b, Exp_int 2)],
          Exp_binop (Op_add,
            Exp_app (Exp_var (cl "fst"), Exp_var (cl "p")),
            Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))))))] in
      let src = Printf.sprintf "let () = print_int (let p = (%d + 1, %d * 2) in fst p + snd p); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 93. Multiple Decl_expr (sequential side effects) *)
    (map2 (fun a b ->
      let prog = [
        Decl_expr (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int a),
                            Exp_app (Exp_var (cl "print_newline"), Exp_unit)));
        Decl_expr (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int b),
                            Exp_app (Exp_var (cl "print_newline"), Exp_unit)))] in
      let src = Printf.sprintf "let () = print_int %d; print_newline ()\nlet () = print_int %d; print_newline ()" a b in
      (prog, src)) (int_range 0 99) (int_range 0 99));

    (* 94. Top-level let + multiple Decl_expr *)
    (map (fun n ->
      let prog = [
        Decl_let (cl "x", Exp_int n);
        Decl_expr (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_var (cl "x")),
                            Exp_app (Exp_var (cl "print_newline"), Exp_unit)));
        Decl_expr (Exp_seq (Exp_app (Exp_var (cl "print_int"),
                              Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)),
                            Exp_app (Exp_var (cl "print_newline"), Exp_unit)))] in
      let src = Printf.sprintf "let x = %d\nlet () = print_int x; print_newline ()\nlet () = print_int (x * 2); print_newline ()" n in
      (prog, src)) (int_range 0 49));

    (* 95. Match with wildcard fallthrough after many int patterns *)
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
      let src = Printf.sprintf "let () = print_int (match %d with 0 -> 0 | 1 -> 10 | 2 -> 20 | 3 -> 30 | 4 -> 40 | 5 -> 50 | _ -> -1); print_newline ()" n in
      (prog, src)) (int_range 0 7));

    (* 96. Zero: edge cases *)
    (return
      (let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add,
          Exp_binop (Op_add,
            Exp_binop (Op_mul, Exp_int 0, Exp_int 42),
            Exp_binop (Op_add, Exp_int 0, Exp_int 0)),
          Exp_binop (Op_sub, Exp_int 0, Exp_int 0))))] in
      let src = "let () = print_int (0 * 42 + (0 + 0) + (0 - 0)); print_newline ()" in
      (prog, src)));

    (* 97. Nested tuples: pair of pairs *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "inner", Exp_tuple [Exp_int a; Exp_int b],
          Exp_binop (Op_mul,
            Exp_app (Exp_var (cl "fst"), Exp_var (cl "inner")),
            Exp_app (Exp_var (cl "snd"), Exp_var (cl "inner"))))))] in
      let src = Printf.sprintf "let () = print_int (let inner = (%d, %d) in fst inner * snd inner); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

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
      let src = Printf.sprintf "let () = print_int (let swap p = (snd p, fst p) in let p = (%d, %d) in let q = swap p in fst q + 100 * snd q); print_newline ()" a b in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 99. Pat_tuple: basic 2-tuple destructuring *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_tuple [Exp_int a; Exp_int b],
          [(Pat_tuple [Pat_var (cl "a"); Pat_var (cl "b")],
            Exp_binop (Op_add, Exp_var (cl "a"), Exp_var (cl "b")))])))] in
      let src = Printf.sprintf "let () = print_int (match (%d, %d) with (a, b) -> a + b); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* 100. Pat_tuple: 3-tuple destructuring *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_tuple [Exp_int a; Exp_int b; Exp_int c],
          [(Pat_tuple [Pat_var (cl "a"); Pat_var (cl "b"); Pat_var (cl "c")],
            Exp_binop (Op_add, Exp_var (cl "a"),
              Exp_binop (Op_add, Exp_var (cl "b"), Exp_var (cl "c"))))])))] in
      let src = Printf.sprintf "let () = print_int (match (%d, %d, %d) with (a, b, c) -> a + b + c); print_newline ()" a b c in
      (prog, src)) (int_range 0 30) (int_range 0 30) (int_range 0 30));

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
      let src = Printf.sprintf "let () = print_int (let f x = (x + 1, x * 2) in match f %d with (a, b) -> a + b); print_newline ()" n in
      (prog, src)) (int_range 0 20));

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
      let src = Printf.sprintf "let () = print_int (let swap p = match p with (a, b) -> (b, a) in match swap (%d, %d) with (x, y) -> x + y); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* === NEW GENERATORS: Exp_function === *)

    (* 103. Exp_function: basic function with int pattern arms *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_function [
            (Pat_int 0, Exp_int 100);
            (Pat_int 1, Exp_int 200);
            (Pat_wild, Exp_int 300)],
          Exp_app (Exp_var (cl "f"), Exp_int n))))] in
      let src = Printf.sprintf "let () = print_int (let f = function 0 -> 100 | 1 -> 200 | _ -> 300 in f %d); print_newline ()" n in
      (prog, src)) (int_range 0 3));

    (* 104. Exp_function: with Pat_var binding *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_function [
            (Pat_int 0, Exp_int 42);
            (Pat_var (cl "x"), Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2))],
          Exp_app (Exp_var (cl "f"), Exp_int n))))] in
      let src = Printf.sprintf "let () = print_int (let f = function 0 -> 42 | x -> x * 2 in f %d); print_newline ()" n in
      (prog, src)) (int_range 0 9));

    (* 105. Exp_function: capturing a free variable *)
    (map2 (fun a n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "a", Exp_int a,
          Exp_let (cl "f",
            Exp_function [
              (Pat_int 0, Exp_var (cl "a"));
              (Pat_wild, Exp_int 0)],
            Exp_app (Exp_var (cl "f"), Exp_int n)))))] in
      let src = Printf.sprintf "let () = print_int (let a = %d in let f = function 0 -> a | _ -> 0 in f %d); print_newline ()" a n in
      (prog, src)) (int_range 1 50) (int_range 0 2));

    (* === NEW GENERATORS: Exp_nil / Exp_cons / Pat_nil / Pat_cons === *)

    (* 106. Exp_cons: build a simple 1-element list, match on it *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_cons (Exp_int n, Exp_nil),
          [(Pat_cons (Pat_var (cl "h"), Pat_wild), Exp_var (cl "h"));
           (Pat_nil, Exp_int 0)])
        ))] in
      let src = Printf.sprintf "let () = print_int (match %d :: [] with h :: _ -> h | [] -> 0); print_newline ()" n in
      (prog, src)) (int_range 0 49));

    (* 107. Exp_cons: build a 2-element list, extract head *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_cons (Exp_int a, Exp_cons (Exp_int b, Exp_nil)),
          [(Pat_cons (Pat_var (cl "h"), Pat_wild), Exp_var (cl "h"));
           (Pat_nil, Exp_int 0)])
        ))] in
      let src = Printf.sprintf "let () = print_int (match %d :: %d :: [] with h :: _ -> h | [] -> 0); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* 108. Pat_nil: match empty list *)
    (return
      (let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_nil,
          [(Pat_cons (Pat_var (cl "h"), Pat_wild), Exp_var (cl "h"));
           (Pat_nil, Exp_int 99)])
        ))] in
      let src = "let () = print_int (match [] with h :: _ -> h | [] -> 99); print_newline ()" in
      (prog, src)));

    (* 109. Pat_cons: simple h :: t destructuring on 2-element list, sum h and head of t *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_cons (Exp_int a, Exp_cons (Exp_int b, Exp_nil)),
          [(Pat_cons (Pat_var (cl "h"), Pat_var (cl "t")),
            Exp_binop (Op_add, Exp_var (cl "h"),
              Exp_match (Exp_var (cl "t"),
                [(Pat_cons (Pat_var (cl "h2"), Pat_wild), Exp_var (cl "h2"));
                 (Pat_nil, Exp_int 0)])));
           (Pat_nil, Exp_int 0)])
        ))] in
      let src = Printf.sprintf "let () = print_int (match %d :: %d :: [] with h :: t -> h + (match t with h2 :: _ -> h2 | [] -> 0) | [] -> 0); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* === NEW GENERATORS: 3+ arg functions with partial application === *)

    (* 110. Three-argument function, fully applied *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_fun (cl "x", Exp_fun (cl "y", Exp_fun (cl "z",
            Exp_binop (Op_add, Exp_var (cl "x"),
              Exp_binop (Op_add, Exp_var (cl "y"), Exp_var (cl "z")))))),
          Exp_app (Exp_app (Exp_app (Exp_var (cl "f"), Exp_int a), Exp_int b), Exp_int c))))] in
      let src = Printf.sprintf "let () = print_int (let f x y z = x + y + z in f %d %d %d); print_newline ()" a b c in
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 111. Three-argument function with partial application (apply 1, then 2 more) *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_fun (cl "x", Exp_fun (cl "y", Exp_fun (cl "z",
            Exp_binop (Op_add, Exp_binop (Op_mul, Exp_var (cl "x"), Exp_var (cl "y")), Exp_var (cl "z"))))),
          Exp_let (cl "g", Exp_app (Exp_var (cl "f"), Exp_int a),
            Exp_app (Exp_app (Exp_var (cl "g"), Exp_int b), Exp_int c)))))] in
      let src = Printf.sprintf "let () = print_int (let f x y z = x * y + z in let g = f %d in g %d %d); print_newline ()" a b c in
      (prog, src)) (int_range 0 9) (int_range 0 9) (int_range 0 9));

    (* 112. Three-argument function with partial application (apply 2, then 1) *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_fun (cl "x", Exp_fun (cl "y", Exp_fun (cl "z",
            Exp_binop (Op_sub, Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y")), Exp_var (cl "z"))))),
          Exp_let (cl "g", Exp_app (Exp_app (Exp_var (cl "f"), Exp_int a), Exp_int b),
            Exp_app (Exp_var (cl "g"), Exp_int c)))))] in
      let src = Printf.sprintf "let () = print_int (let f x y z = x + y - z in let g = f %d %d in g %d); print_newline ()" a b c in
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 9));

    (* === NEW GENERATORS: Closures capturing multiple free vars from different scopes === *)

    (* 113. Closure captures vars from 3 different scope levels *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "a", Exp_int a,
          Exp_let (cl "b", Exp_int b,
            Exp_let (cl "c", Exp_int c,
              Exp_let (cl "f", Exp_fun (cl "x",
                Exp_binop (Op_add, Exp_var (cl "a"),
                  Exp_binop (Op_add, Exp_var (cl "b"),
                    Exp_binop (Op_add, Exp_var (cl "c"), Exp_var (cl "x"))))),
                Exp_app (Exp_var (cl "f"), Exp_int 1)))))))] in
      let src = Printf.sprintf "let () = print_int (let a = %d in let b = %d in let c = %d in let f x = a + b + c + x in f 1); print_newline ()" a b c in
      (prog, src)) (int_range 0 9) (int_range 0 9) (int_range 0 9));

    (* 114. Two closures each capturing different variables *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "a", Exp_int a,
          Exp_let (cl "b", Exp_int b,
            Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "a"), Exp_var (cl "x"))),
              Exp_let (cl "g", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "b"), Exp_var (cl "x"))),
                Exp_binop (Op_add,
                  Exp_app (Exp_var (cl "f"), Exp_int c),
                  Exp_app (Exp_var (cl "g"), Exp_int c))))))))] in
      let src = Printf.sprintf "let () = print_int (let a = %d in let b = %d in let f x = a + x in let g x = b + x in f %d + g %d); print_newline ()" a b c c in
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 9));

    (* === NEW GENERATORS: Variable shadowing inside closures === *)

    (* 115. Variable shadowing: closure parameter shadows captured variable *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)),
            Exp_binop (Op_add, Exp_var (cl "x"), Exp_app (Exp_var (cl "f"), Exp_int b))))))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in let f x = x + 1 in x + f %d); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 116. Variable shadowing: inner let shadows captured variable in closure *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "f", Exp_fun (cl "y",
            Exp_let (cl "x", Exp_binop (Op_add, Exp_var (cl "y"), Exp_int 1),
              Exp_binop (Op_add, Exp_var (cl "x"), Exp_int b))),
            Exp_binop (Op_add, Exp_var (cl "x"),
              Exp_app (Exp_var (cl "f"), Exp_int c))))))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in let f y = let x = y + 1 in x + %d in x + f %d); print_newline ()" a b c in
      (prog, src)) (int_range 0 9) (int_range 0 9) (int_range 0 9));

    (* === NEW GENERATORS: Evaluation order with side effects in let bindings === *)

    (* 117. Let binding evaluation order: e1 before e2 *)
    (map2 (fun a b ->
      let prog = [Decl_expr
        (Exp_let (cl "x", Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int a), Exp_int 0),
          Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int b),
            Exp_app (Exp_var (cl "print_newline"), Exp_unit))))] in
      let src = Printf.sprintf "let () = let _x = (print_int %d; 0) in print_int %d; print_newline ()" a b in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 118. Sequential let with effects: verify order *)
    (map3 (fun a b c ->
      let prog = [Decl_expr
        (Exp_let (cl "x", Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int a), Exp_int a),
          Exp_let (cl "y", Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int b), Exp_int b),
            Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int c),
              Exp_app (Exp_var (cl "print_newline"), Exp_unit)))))] in
      let src = Printf.sprintf "let () = let _x = (print_int %d; %d) in let _y = (print_int %d; %d) in print_int %d; print_newline ()" a a b b c in
      (prog, src)) (int_range 0 9) (int_range 0 9) (int_range 0 9));

    (* === NEW GENERATORS: Exp_constr (with args) === *)

    (* 119. Exp_constr None (nullary constructor) used in match *)
    (map (fun n ->
      let prog = [
        Decl_type (cl "color", [],
          Td_variant [(cl "Red", None); (cl "Blue", None); (cl "Green", None)]);
        Decl_expr (print_int_nl
          (Exp_match (Exp_constr (cl "Red", None),
            [(Pat_wild, Exp_int n)])
          ))] in
      let src = Printf.sprintf "type color = Red | Blue | Green\nlet () = print_int (match Red with _ -> %d); print_newline ()" n in
      (prog, src)) (int_range 0 49));

    (* 120. Exp_constr with arg: Some x *)
    (map (fun n ->
      let prog = [
        Decl_type (cl "opt", [],
          Td_variant [(cl "None", None); (cl "Some", Some Ty_int)]);
        Decl_expr (print_int_nl
          (Exp_match (Exp_constr (cl "Some", Some (Exp_int n)),
            [(Pat_wild, Exp_int n)])
          ))] in
      let src = Printf.sprintf "type opt = None | Some of int\nlet () = print_int (match Some %d with _ -> %d); print_newline ()" n n in
      (prog, src)) (int_range 0 49));

    (* === NEW GENERATORS: Exp_record / Exp_field === *)

    (* 121. Record creation and field access *)
    (map2 (fun a b ->
      let prog = [
        Decl_type (cl "point", [],
          Td_record [(cl "x", Ty_int); (cl "y", Ty_int)]);
        Decl_expr (print_int_nl
          (Exp_let (cl "p", Exp_record [(cl "x", Exp_int a); (cl "y", Exp_int b)],
            Exp_binop (Op_add,
              Exp_field (Exp_var (cl "p"), cl "x"),
              Exp_field (Exp_var (cl "p"), cl "y")))))] in
      let src = Printf.sprintf "type point = { x : int; y : int }\nlet () = print_int (let p = { x = %d; y = %d } in p.x + p.y); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* 122. Record with 3 fields *)
    (map3 (fun a b c ->
      let prog = [
        Decl_type (cl "triple", [],
          Td_record [(cl "a", Ty_int); (cl "b", Ty_int); (cl "c", Ty_int)]);
        Decl_expr (print_int_nl
          (Exp_let (cl "t", Exp_record [(cl "a", Exp_int a); (cl "b", Exp_int b); (cl "c", Exp_int c)],
            Exp_binop (Op_add,
              Exp_field (Exp_var (cl "t"), cl "a"),
              Exp_binop (Op_add,
                Exp_field (Exp_var (cl "t"), cl "b"),
                Exp_field (Exp_var (cl "t"), cl "c"))))))] in
      let src = Printf.sprintf "type triple = { a : int; b : int; c : int }\nlet () = print_int (let t = { a = %d; b = %d; c = %d } in t.a + t.b + t.c); print_newline ()" a b c in
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* === NEW GENERATORS: Recursive with list === *)

    (* 123. Recursive sum over a list *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_letrec (cl "sum",
          Exp_fun (cl "l",
            Exp_match (Exp_var (cl "l"),
              [(Pat_nil, Exp_int 0);
               (Pat_cons (Pat_var (cl "h"), Pat_var (cl "t")),
                Exp_binop (Op_add, Exp_var (cl "h"),
                  Exp_app (Exp_var (cl "sum"), Exp_var (cl "t"))))])),
          Exp_app (Exp_var (cl "sum"),
            Exp_cons (Exp_int a, Exp_cons (Exp_int b, Exp_cons (Exp_int c, Exp_nil)))))
        ))] in
      let src = Printf.sprintf "let () = print_int (let rec sum l = match l with [] -> 0 | h :: t -> h + sum t in sum [%d; %d; %d]); print_newline ()" a b c in
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 124. Recursive length of list *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_letrec (cl "len",
          Exp_fun (cl "l",
            Exp_match (Exp_var (cl "l"),
              [(Pat_nil, Exp_int 0);
               (Pat_cons (Pat_wild, Pat_var (cl "t")),
                Exp_binop (Op_add, Exp_int 1,
                  Exp_app (Exp_var (cl "len"), Exp_var (cl "t"))))])),
          Exp_app (Exp_var (cl "len"),
            Exp_cons (Exp_int a, Exp_cons (Exp_int b, Exp_nil))))
        ))] in
      let src = Printf.sprintf "let () = print_int (let rec len l = match l with [] -> 0 | _ :: t -> 1 + len t in len [%d; %d]); print_newline ()" a b in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* === BATCH 2: More complex patterns and expressions === *)

    (* 125. Pat_cons with nil fallback: match on empty vs non-empty list *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (
          (if n > 0 then Exp_cons (Exp_int n, Exp_nil) else Exp_nil),
          [(Pat_cons (Pat_var (cl "h"), Pat_wild), Exp_var (cl "h"));
           (Pat_nil, Exp_int (-1))])
        ))] in
      let src = Printf.sprintf "let () = print_int (match %s with h :: _ -> h | [] -> -1); print_newline ()"
        (if n > 0 then Printf.sprintf "[%d]" n else "[]") in
      (prog, src)) (int_range 0 3));

    (* 126. Recursive map over list *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_letrec (cl "sum",
          Exp_fun (cl "l",
            Exp_match (Exp_var (cl "l"),
              [(Pat_nil, Exp_int 0);
               (Pat_cons (Pat_var (cl "h"), Pat_var (cl "t")),
                Exp_binop (Op_add,
                  Exp_binop (Op_mul, Exp_var (cl "h"), Exp_int 2),
                  Exp_app (Exp_var (cl "sum"), Exp_var (cl "t"))))])),
          Exp_app (Exp_var (cl "sum"),
            Exp_cons (Exp_int a, Exp_cons (Exp_int b, Exp_cons (Exp_int c, Exp_nil)))))
        ))] in
      let src = Printf.sprintf "let () = print_int (let rec sum l = match l with [] -> 0 | h :: t -> h * 2 + sum t in sum [%d; %d; %d]); print_newline ()" a b c in
      (prog, src)) (int_range 0 9) (int_range 0 9) (int_range 0 9));

    (* 127. Exp_function with tuple destructuring *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_function [
            (Pat_tuple [Pat_var (cl "x"); Pat_var (cl "y")],
             Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y")))],
          Exp_app (Exp_var (cl "f"), Exp_tuple [Exp_int a; Exp_int b]))))] in
      let src = Printf.sprintf "let () = print_int (let f = function (x, y) -> x + y in f (%d, %d)); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* 128. Exp_function with bool pattern arms *)
    (map (fun b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "to_int",
          Exp_function [
            (Pat_bool true, Exp_int 1);
            (Pat_bool false, Exp_int 0)],
          Exp_app (Exp_var (cl "to_int"), Exp_bool b))))] in
      let src = Printf.sprintf "let () = print_int (let to_int = function true -> 1 | false -> 0 in to_int %s); print_newline ()" (if b then "true" else "false") in
      (prog, src)) QCheck.Gen.bool);

    (* 129. Closure capturing 4 free variables *)
    (map2 (fun a b ->
      let c = a + b in
      let d = a * 2 in
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "a", Exp_int a,
          Exp_let (cl "b", Exp_int b,
            Exp_let (cl "c", Exp_int c,
              Exp_let (cl "d", Exp_int d,
                Exp_let (cl "f", Exp_fun (cl "x",
                  Exp_binop (Op_add, Exp_var (cl "a"),
                    Exp_binop (Op_add, Exp_var (cl "b"),
                      Exp_binop (Op_add, Exp_var (cl "c"),
                        Exp_binop (Op_add, Exp_var (cl "d"), Exp_var (cl "x")))))),
                  Exp_app (Exp_var (cl "f"), Exp_int 1))))))))] in
      let src = Printf.sprintf "let () = print_int (let a = %d in let b = %d in let c = %d in let d = %d in let f x = a + b + c + d + x in f 1); print_newline ()" a b c d in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 130. Variable shadowing inside closure that captures outer var *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "y", Exp_int b,
            Exp_let (cl "f", Exp_fun (cl "z",
              Exp_let (cl "x", Exp_binop (Op_add, Exp_var (cl "z"), Exp_var (cl "y")),
                Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2))),
              Exp_binop (Op_add,
                Exp_var (cl "x"),
                Exp_app (Exp_var (cl "f"), Exp_int c)))))))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in let y = %d in let f z = let x = z + y in x * 2 in x + f %d); print_newline ()" a b c in
      (prog, src)) (int_range 0 9) (int_range 0 9) (int_range 0 9));

    (* 131. 4-arg function, fully applied *)
    (map2 (fun a b ->
      let c = a + 1 in let d = b + 1 in
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_fun (cl "a", Exp_fun (cl "b", Exp_fun (cl "c", Exp_fun (cl "d",
            Exp_binop (Op_add,
              Exp_binop (Op_mul, Exp_var (cl "a"), Exp_var (cl "b")),
              Exp_binop (Op_mul, Exp_var (cl "c"), Exp_var (cl "d"))))))),
          Exp_app (Exp_app (Exp_app (Exp_app (Exp_var (cl "f"),
            Exp_int a), Exp_int b), Exp_int c), Exp_int d))))] in
      let src = Printf.sprintf "let () = print_int (let f a b c d = a * b + c * d in f %d %d %d %d); print_newline ()" a b c d in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 132. 4-arg function, partial application: apply 1, then 3 *)
    (map2 (fun a b ->
      let c = 1 in let d = 2 in
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_fun (cl "a", Exp_fun (cl "b", Exp_fun (cl "c", Exp_fun (cl "d",
            Exp_binop (Op_add,
              Exp_binop (Op_add, Exp_var (cl "a"), Exp_var (cl "b")),
              Exp_binop (Op_add, Exp_var (cl "c"), Exp_var (cl "d"))))))),
          Exp_let (cl "g", Exp_app (Exp_var (cl "f"), Exp_int a),
            Exp_app (Exp_app (Exp_app (Exp_var (cl "g"),
              Exp_int b), Exp_int c), Exp_int d)))))] in
      let src = Printf.sprintf "let () = print_int (let f a b c d = a + b + c + d in let g = f %d in g %d %d %d); print_newline ()" a b c d in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 133. 3-arg function, partial application saving 2 closures *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_fun (cl "x", Exp_fun (cl "y", Exp_fun (cl "z",
            Exp_binop (Op_add, Exp_var (cl "x"),
              Exp_binop (Op_mul, Exp_var (cl "y"), Exp_var (cl "z")))))),
          Exp_let (cl "g", Exp_app (Exp_var (cl "f"), Exp_int a),
            Exp_let (cl "h", Exp_app (Exp_var (cl "g"), Exp_int b),
              Exp_app (Exp_var (cl "h"), Exp_int c))))))] in
      let src = Printf.sprintf "let () = print_int (let f x y z = x + y * z in let g = f %d in let h = g %d in h %d); print_newline ()" a b c in
      (prog, src)) (int_range 0 9) (int_range 0 9) (int_range 0 9));

    (* 134. Recursive function where closure captures variable that changes per call *)
    (map2 (fun n m ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "offset", Exp_int m,
          Exp_letrec (cl "f",
            Exp_fun (cl "n",
              Exp_if (Exp_binop (Op_le, Exp_var (cl "n"), Exp_int 0),
                Exp_var (cl "offset"),
                Exp_binop (Op_add, Exp_int 1,
                  Exp_app (Exp_var (cl "f"),
                    Exp_binop (Op_sub, Exp_var (cl "n"), Exp_int 1))))),
            Exp_app (Exp_var (cl "f"), Exp_int n)))))] in
      let src = Printf.sprintf "let () = print_int (let offset = %d in let rec f n = if n <= 0 then offset else 1 + f (n - 1) in f %d); print_newline ()" m n in
      (prog, src)) (int_range 0 7) (int_range 10 30));

    (* 135. Top-level Decl_letrec using list recursion *)
    (map3 (fun a b c ->
      let prog = [
        Decl_letrec (cl "sum",
          Exp_fun (cl "l",
            Exp_match (Exp_var (cl "l"),
              [(Pat_nil, Exp_int 0);
               (Pat_cons (Pat_var (cl "h"), Pat_var (cl "t")),
                Exp_binop (Op_add, Exp_var (cl "h"),
                  Exp_app (Exp_var (cl "sum"), Exp_var (cl "t"))))])));
        Decl_expr (print_int_nl
          (Exp_app (Exp_var (cl "sum"),
            Exp_cons (Exp_int a, Exp_cons (Exp_int b, Exp_cons (Exp_int c, Exp_nil))))))] in
      let src = Printf.sprintf "let rec sum l = match l with [] -> 0 | h :: t -> h + sum t\nlet () = print_int (sum [%d; %d; %d]); print_newline ()" a b c in
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 136. Match with both Pat_int and Pat_var, compute with bound var *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_binop (Op_mul, Exp_int n, Exp_int 3),
          [(Pat_int 0, Exp_int 42);
           (Pat_int 3, Exp_int 99);
           (Pat_var (cl "x"), Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1000))])
        ))] in
      let src = Printf.sprintf "let () = print_int (match %d * 3 with 0 -> 42 | 3 -> 99 | x -> x + 1000); print_newline ()" n in
      (prog, src)) (int_range 0 5));

    (* 137. Op_and / Op_or logical operators *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_binop (Op_and,
          Exp_binop (Op_gt, Exp_int a, Exp_int 5),
          Exp_binop (Op_gt, Exp_int b, Exp_int 5)),
          Exp_int 1, Exp_int 0)))] in
      let src = Printf.sprintf "let () = print_int (if %d > 5 && %d > 5 then 1 else 0); print_newline ()" a b in
      (prog, src)) (int_range 0 10) (int_range 0 10));

    (* 138. Op_or logical operator *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_binop (Op_or,
          Exp_binop (Op_eq, Exp_int a, Exp_int 0),
          Exp_binop (Op_eq, Exp_int b, Exp_int 0)),
          Exp_int 1, Exp_int 0)))] in
      let src = Printf.sprintf "let () = print_int (if %d = 0 || %d = 0 then 1 else 0); print_newline ()" a b in
      (prog, src)) (int_range 0 3) (int_range 0 3));

    (* 139. Nested closures: closure inside closure *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "a", Exp_int a,
          Exp_let (cl "f", Exp_fun (cl "b",
            Exp_let (cl "g", Exp_fun (cl "c",
              Exp_binop (Op_add, Exp_var (cl "a"),
                Exp_binop (Op_add, Exp_var (cl "b"), Exp_var (cl "c")))),
              Exp_app (Exp_var (cl "g"), Exp_int c))),
            Exp_app (Exp_var (cl "f"), Exp_int b)))))] in
      let src = Printf.sprintf "let () = print_int (let a = %d in let f b = let g c = a + b + c in g %d in f %d); print_newline ()" a c b in
      (prog, src)) (int_range 0 9) (int_range 0 9) (int_range 0 9));

    (* 140. Multiple closures returned and used *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "make_pair",
          Exp_fun (cl "x",
            Exp_tuple [
              Exp_fun (cl "y", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y")));
              Exp_fun (cl "y", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_var (cl "y")))]),
          Exp_let (cl "p", Exp_app (Exp_var (cl "make_pair"), Exp_int a),
            Exp_binop (Op_add,
              Exp_app (Exp_app (Exp_var (cl "fst"), Exp_var (cl "p")), Exp_int b),
              Exp_app (Exp_app (Exp_var (cl "snd"), Exp_var (cl "p")), Exp_int b))))))] in
      let src = Printf.sprintf "let () = print_int (let make_pair x = ((fun y -> x + y), (fun y -> x * y)) in let p = make_pair %d in (fst p) %d + (snd p) %d); print_newline ()" a b b in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 141. Match on list with function application in arm *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "double", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)),
          Exp_match (Exp_cons (Exp_int a, Exp_cons (Exp_int b, Exp_nil)),
            [(Pat_cons (Pat_var (cl "h"), Pat_var (cl "t")),
              Exp_binop (Op_add,
                Exp_app (Exp_var (cl "double"), Exp_var (cl "h")),
                Exp_match (Exp_var (cl "t"),
                  [(Pat_cons (Pat_var (cl "h2"), Pat_wild),
                    Exp_app (Exp_var (cl "double"), Exp_var (cl "h2")));
                   (Pat_nil, Exp_int 0)])));
             (Pat_nil, Exp_int 0)]))))] in
      let src = Printf.sprintf "let () = print_int (let double x = x * 2 in match [%d; %d] with h :: t -> double h + (match t with h2 :: _ -> double h2 | [] -> 0) | [] -> 0); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 142. Exp_function as argument to higher-order function *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "apply",
          Exp_fun (cl "f", Exp_fun (cl "x", Exp_app (Exp_var (cl "f"), Exp_var (cl "x")))),
          Exp_app (Exp_app (Exp_var (cl "apply"),
            Exp_function [
              (Pat_int 0, Exp_int 100);
              (Pat_wild, Exp_int 200)]),
            Exp_int n))))] in
      let src = Printf.sprintf "let () = print_int (let apply f x = f x in apply (function 0 -> 100 | _ -> 200) %d); print_newline ()" n in
      (prog, src)) (int_range 0 3));

    (* 143. Record: field access on function return value *)
    (map2 (fun a b ->
      let prog = [
        Decl_type (cl "pair", [],
          Td_record [(cl "fst_val", Ty_int); (cl "snd_val", Ty_int)]);
        Decl_expr (print_int_nl
          (Exp_let (cl "mk",
            Exp_fun (cl "x", Exp_fun (cl "y",
              Exp_record [(cl "fst_val", Exp_var (cl "x")); (cl "snd_val", Exp_var (cl "y"))])),
            Exp_let (cl "p", Exp_app (Exp_app (Exp_var (cl "mk"), Exp_int a), Exp_int b),
              Exp_binop (Op_add,
                Exp_field (Exp_var (cl "p"), cl "fst_val"),
                Exp_field (Exp_var (cl "p"), cl "snd_val"))))))] in
      let src = Printf.sprintf "type pair = { fst_val : int; snd_val : int }\nlet () = print_int (let mk x y = { fst_val = x; snd_val = y } in let p = mk %d %d in p.fst_val + p.snd_val); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* 144. Nested match with closures: test environment handling *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_match (Exp_int b,
            [(Pat_int 0,
              Exp_let (cl "f", Exp_fun (cl "y", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y"))),
                Exp_app (Exp_var (cl "f"), Exp_int 10)));
             (Pat_wild,
              Exp_let (cl "g", Exp_fun (cl "y", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_var (cl "y"))),
                Exp_app (Exp_var (cl "g"), Exp_int 10)))]))
        ))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in match %d with 0 -> (let f y = x + y in f 10) | _ -> (let g y = x * y in g 10)); print_newline ()" a b in
      (prog, src)) (int_range 0 9) (int_range 0 3));

    (* === BATCH 3: Edge cases and stress tests === *)

    (* 145. Empty list construction and immediate nil test *)
    (return
      (let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_nil,
          [(Pat_nil, Exp_int 1);
           (Pat_cons (Pat_wild, Pat_wild), Exp_int 0)])
        ))] in
      let src = "let () = print_int (match [] with [] -> 1 | _ :: _ -> 0); print_newline ()" in
      (prog, src)));

    (* 146. List with single element, match both nil and cons *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_cons (Exp_int n, Exp_nil),
          [(Pat_nil, Exp_int (-1));
           (Pat_cons (Pat_var (cl "h"), Pat_wild), Exp_var (cl "h"))])
        ))] in
      let src = Printf.sprintf "let () = print_int (match [%d] with [] -> -1 | h :: _ -> h); print_newline ()" n in
      (prog, src)) (int_range 0 49));

    (* 147. Recursive fold_left over list *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_letrec (cl "fold",
          Exp_fun (cl "f", Exp_fun (cl "acc", Exp_fun (cl "l",
            Exp_match (Exp_var (cl "l"),
              [(Pat_nil, Exp_var (cl "acc"));
               (Pat_cons (Pat_var (cl "h"), Pat_var (cl "t")),
                Exp_app (Exp_app (Exp_app (Exp_var (cl "fold"), Exp_var (cl "f")),
                  Exp_app (Exp_app (Exp_var (cl "f"), Exp_var (cl "acc")), Exp_var (cl "h"))),
                  Exp_var (cl "t")))])))),
          Exp_app (Exp_app (Exp_app (Exp_var (cl "fold"),
            Exp_fun (cl "a", Exp_fun (cl "b", Exp_binop (Op_add, Exp_var (cl "a"), Exp_var (cl "b"))))),
            Exp_int 0),
            Exp_cons (Exp_int a, Exp_cons (Exp_int b, Exp_cons (Exp_int c, Exp_nil)))))
        ))] in
      let src = Printf.sprintf "let () = print_int (let rec fold f acc l = match l with [] -> acc | h :: t -> fold f (f acc h) t in fold (fun a b -> a + b) 0 [%d; %d; %d]); print_newline ()" a b c in
      (prog, src)) (int_range 0 9) (int_range 0 9) (int_range 0 9));

    (* 148. 4-element tuple destructuring *)
    (map2 (fun a b ->
      let c = a + b in let d = a * b in
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_tuple [Exp_int a; Exp_int b; Exp_int c; Exp_int d],
          [(Pat_tuple [Pat_var (cl "a"); Pat_var (cl "b"); Pat_var (cl "c"); Pat_var (cl "d")],
            Exp_binop (Op_add,
              Exp_binop (Op_add, Exp_var (cl "a"), Exp_var (cl "b")),
              Exp_binop (Op_add, Exp_var (cl "c"), Exp_var (cl "d"))))])))] in
      let src = Printf.sprintf "let () = print_int (match (%d, %d, %d, %d) with (a, b, c, d) -> a + b + c + d); print_newline ()" a b c d in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 149. Exp_function with wildcard and variable capture *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "classify",
          Exp_function [
            (Pat_int 0, Exp_int 0);
            (Pat_var (cl "x"),
              Exp_if (Exp_binop (Op_gt, Exp_var (cl "x"), Exp_int 0),
                Exp_int 1, Exp_int (-1)))],
          Exp_app (Exp_var (cl "classify"), Exp_int n))))] in
      let src = Printf.sprintf "let () = print_int (let classify = function 0 -> 0 | x -> if x > 0 then 1 else -1 in classify %d); print_newline ()" n in
      (prog, src)) (int_range (-5) 5));

    (* 150. Multiple print_string side effects checking output order *)
    (map2 (fun a b ->
      let prog = [Decl_expr
        (Exp_seq (
          Exp_app (Exp_var (cl "print_int"), Exp_int a),
          Exp_seq (
            Exp_app (Exp_var (cl "print_int"), Exp_int b),
            Exp_seq (
              Exp_app (Exp_var (cl "print_int"), Exp_binop (Op_add, Exp_int a, Exp_int b)),
              Exp_app (Exp_var (cl "print_newline"), Exp_unit)))))] in
      let src = Printf.sprintf "let () = print_int %d; print_int %d; print_int %d; print_newline ()" a b (a+b) in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 151. Nested Pat_tuple with wildcard *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_tuple [Exp_int a; Exp_int b],
          [(Pat_tuple [Pat_var (cl "x"); Pat_wild],
            Exp_var (cl "x"))])))] in
      let src = Printf.sprintf "let () = print_int (match (%d, %d) with (x, _) -> x); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* 152. Closures in list: build list of closures, apply them *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "fa", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int a)),
          Exp_let (cl "fb", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int b)),
            Exp_binop (Op_add,
              Exp_app (Exp_var (cl "fa"), Exp_int 0),
              Exp_app (Exp_var (cl "fb"), Exp_int 0))))))] in
      let src = Printf.sprintf "let () = print_int (let fa x = x + %d in let fb x = x + %d in fa 0 + fb 0); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 153. Mutual recursion via higher-order: even/odd check *)
    (map (fun n ->
      let n = n mod 10 in  (* keep small to avoid deep recursion *)
      let prog = [Decl_expr (print_int_nl
        (Exp_letrec (cl "is_even",
          Exp_fun (cl "n",
            Exp_if (Exp_binop (Op_eq, Exp_var (cl "n"), Exp_int 0),
              Exp_int 1,
              Exp_if (Exp_binop (Op_eq, Exp_var (cl "n"), Exp_int 1),
                Exp_int 0,
                Exp_app (Exp_var (cl "is_even"),
                  Exp_binop (Op_sub, Exp_var (cl "n"), Exp_int 2))))),
          Exp_app (Exp_var (cl "is_even"), Exp_int n))))] in
      let src = Printf.sprintf "let () = print_int (let rec is_even n = if n = 0 then 1 else if n = 1 then 0 else is_even (n - 2) in is_even %d); print_newline ()" n in
      (prog, src)) (int_range 0 10));

    (* 154. Recursive with list and closure capturing *)
    (map2 (fun n offset ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "offset", Exp_int offset,
          Exp_letrec (cl "sum",
            Exp_fun (cl "l",
              Exp_match (Exp_var (cl "l"),
                [(Pat_nil, Exp_int 0);
                 (Pat_cons (Pat_var (cl "h"), Pat_var (cl "t")),
                  Exp_binop (Op_add,
                    Exp_binop (Op_add, Exp_var (cl "h"), Exp_var (cl "offset")),
                    Exp_app (Exp_var (cl "sum"), Exp_var (cl "t"))))])),
            Exp_app (Exp_var (cl "sum"),
              Exp_cons (Exp_int 1, Exp_cons (Exp_int 2, Exp_cons (Exp_int 3, Exp_nil))))))))] in
      let src = Printf.sprintf "let () = print_int (let offset = %d in let rec sum l = match l with [] -> 0 | h :: t -> (h + offset) + sum t in sum [1; 2; 3]); print_newline ()" offset in
      ignore n;
      (prog, src)) (int_range 0 5) (int_range 0 9));

    (* 155. Top-level function calling another top-level function with list *)
    (map2 (fun a b ->
      let prog = [
        Decl_let (cl "add1", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)));
        Decl_letrec (cl "map_add1",
          Exp_fun (cl "l",
            Exp_match (Exp_var (cl "l"),
              [(Pat_nil, Exp_nil);
               (Pat_cons (Pat_var (cl "h"), Pat_var (cl "t")),
                Exp_cons (
                  Exp_app (Exp_var (cl "add1"), Exp_var (cl "h")),
                  Exp_app (Exp_var (cl "map_add1"), Exp_var (cl "t"))))])));
        Decl_letrec (cl "sum",
          Exp_fun (cl "l",
            Exp_match (Exp_var (cl "l"),
              [(Pat_nil, Exp_int 0);
               (Pat_cons (Pat_var (cl "h"), Pat_var (cl "t")),
                Exp_binop (Op_add, Exp_var (cl "h"),
                  Exp_app (Exp_var (cl "sum"), Exp_var (cl "t"))))])));
        Decl_expr (print_int_nl
          (Exp_app (Exp_var (cl "sum"),
            Exp_app (Exp_var (cl "map_add1"),
              Exp_cons (Exp_int a, Exp_cons (Exp_int b, Exp_nil))))))] in
      let src = Printf.sprintf "let add1 x = x + 1\nlet rec map_add1 l = match l with [] -> [] | h :: t -> add1 h :: map_add1 t\nlet rec sum l = match l with [] -> 0 | h :: t -> h + sum t\nlet () = print_int (sum (map_add1 [%d; %d])); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* === BATCH 4: Pat_constr branching tests (critical) === *)

    (* 156. match None with Some x -> x | None -> 42 (Some first, None second) *)
    (return
      (let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_constr (cl "None", None),
          [(Pat_constr (cl "Some", Some (Pat_var (cl "x"))), Exp_var (cl "x"));
           (Pat_constr (cl "None", None), Exp_int 42)])))] in
      let src = "let () = print_int (match None with Some x -> x | None -> 42); print_newline ()" in
      (prog, src)));

    (* 157. match Some 7 with Some x -> x | None -> 0 *)
    (return
      (let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_constr (cl "Some", Some (Exp_int 7)),
          [(Pat_constr (cl "Some", Some (Pat_var (cl "x"))), Exp_var (cl "x"));
           (Pat_constr (cl "None", None), Exp_int 0)])))] in
      let src = "let () = print_int (match Some 7 with Some x -> x | None -> 0); print_newline ()" in
      (prog, src)));

    (* 158. match None with None -> 99 | Some x -> x (None first, Some second) *)
    (return
      (let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_constr (cl "None", None),
          [(Pat_constr (cl "None", None), Exp_int 99);
           (Pat_constr (cl "Some", Some (Pat_var (cl "x"))), Exp_var (cl "x"))])))] in
      let src = "let () = print_int (match None with None -> 99 | Some x -> x); print_newline ()" in
      (prog, src)));

    (* 159. match Some 5 with None -> 0 | Some x -> x (None first, Some second) *)
    (return
      (let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_constr (cl "Some", Some (Exp_int 5)),
          [(Pat_constr (cl "None", None), Exp_int 0);
           (Pat_constr (cl "Some", Some (Pat_var (cl "x"))), Exp_var (cl "x"))])))] in
      let src = "let () = print_int (match Some 5 with None -> 0 | Some x -> x); print_newline ()" in
      (prog, src)));

    (* 160. Parametric Some/None branching *)
    (map (fun n ->
      let input = if n > 3 then
        Exp_constr (cl "Some", Some (Exp_int n))
      else
        Exp_constr (cl "None", None) in
      let prog = [Decl_expr (print_int_nl
        (Exp_match (input,
          [(Pat_constr (cl "Some", Some (Pat_var (cl "x"))),
            Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 100));
           (Pat_constr (cl "None", None), Exp_int (-1))])))] in
      let input_src = if n > 3 then Printf.sprintf "Some %d" n else "None" in
      let src = Printf.sprintf "let () = print_int (match %s with Some x -> x + 100 | None -> (-1)); print_newline ()" input_src in
      (prog, src)) (int_range 0 8));

    (* 161. Option get_or_default function, tested both ways *)
    (map2 (fun n default_val ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "get_or",
          Exp_fun (cl "d", Exp_fun (cl "o",
            Exp_match (Exp_var (cl "o"),
              [(Pat_constr (cl "Some", Some (Pat_var (cl "v"))), Exp_var (cl "v"));
               (Pat_constr (cl "None", None), Exp_var (cl "d"))]))),
          Exp_binop (Op_add,
            Exp_app (Exp_app (Exp_var (cl "get_or"), Exp_int default_val),
              Exp_constr (cl "Some", Some (Exp_int n))),
            Exp_app (Exp_app (Exp_var (cl "get_or"), Exp_int default_val),
              Exp_constr (cl "None", None))))))] in
      let src = Printf.sprintf "let () = print_int (let get_or d o = match o with Some v -> v | None -> d in get_or %d (Some %d) + get_or %d None); print_newline ()" default_val n default_val in
      (prog, src)) (int_range 0 19) (int_range 0 9));

    (* === BATCH 5: Op_and / Op_or compilation checks === *)

    (* 162. Op_and: both sides false *)
    (return
      (let prog = [Decl_expr (print_int_nl
        (Exp_if (
          Exp_binop (Op_and, Exp_bool false, Exp_bool false),
          Exp_int 1, Exp_int 0)))] in
      let src = "let () = print_int (if false && false then 1 else 0); print_newline ()" in
      (prog, src)));

    (* 163. Op_or: both sides false *)
    (return
      (let prog = [Decl_expr (print_int_nl
        (Exp_if (
          Exp_binop (Op_or, Exp_bool false, Exp_bool false),
          Exp_int 1, Exp_int 0)))] in
      let src = "let () = print_int (if false || false then 1 else 0); print_newline ()" in
      (prog, src)));

    (* 164. Op_and: true && true *)
    (return
      (let prog = [Decl_expr (print_int_nl
        (Exp_if (
          Exp_binop (Op_and, Exp_bool true, Exp_bool true),
          Exp_int 1, Exp_int 0)))] in
      let src = "let () = print_int (if true && true then 1 else 0); print_newline ()" in
      (prog, src)));

    (* 165. Op_or: false || true *)
    (return
      (let prog = [Decl_expr (print_int_nl
        (Exp_if (
          Exp_binop (Op_or, Exp_bool false, Exp_bool true),
          Exp_int 1, Exp_int 0)))] in
      let src = "let () = print_int (if false || true then 1 else 0); print_newline ()" in
      (prog, src)));

    (* 166. Op_and with comparison *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (
          Exp_binop (Op_and,
            Exp_binop (Op_gt, Exp_int a, Exp_int 5),
            Exp_binop (Op_lt, Exp_int b, Exp_int 10)),
          Exp_int 1, Exp_int 0)))] in
      let src = Printf.sprintf "let () = print_int (if %d > 5 && %d < 10 then 1 else 0); print_newline ()" a b in
      (prog, src)) (int_range 0 15) (int_range 0 15));

    (* 167. Nested Op_and/Op_or *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (
          Exp_binop (Op_or,
            Exp_binop (Op_and,
              Exp_binop (Op_eq, Exp_int a, Exp_int 1),
              Exp_binop (Op_eq, Exp_int b, Exp_int 2)),
            Exp_binop (Op_eq, Exp_int c, Exp_int 3)),
          Exp_int 1, Exp_int 0)))] in
      let src = Printf.sprintf "let () = print_int (if (%d = 1 && %d = 2) || %d = 3 then 1 else 0); print_newline ()" a b c in
      (prog, src)) (int_range 0 4) (int_range 0 4) (int_range 0 4));

    (* === BATCH 6: Stress tests for list patterns with Pat_nil first === *)

    (* 168. Pat_nil then Pat_cons: empty list *)
    (return
      (let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_nil,
          [(Pat_nil, Exp_int 0);
           (Pat_cons (Pat_var (cl "h"), Pat_wild), Exp_var (cl "h"))])))] in
      let src = "let () = print_int (match [] with [] -> 0 | h :: _ -> h); print_newline ()" in
      (prog, src)));

    (* 169. Pat_nil then Pat_cons: non-empty list *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_cons (Exp_int n, Exp_nil),
          [(Pat_nil, Exp_int 0);
           (Pat_cons (Pat_var (cl "h"), Pat_wild), Exp_var (cl "h"))])))] in
      let src = Printf.sprintf "let () = print_int (match [%d] with [] -> 0 | h :: _ -> h); print_newline ()" n in
      (prog, src)) (int_range 0 49));

    (* 170. Pat_cons then Pat_nil: non-empty list *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_cons (Exp_int n, Exp_nil),
          [(Pat_cons (Pat_var (cl "h"), Pat_wild), Exp_var (cl "h"));
           (Pat_nil, Exp_int (-1))])))] in
      let src = Printf.sprintf "let () = print_int (match [%d] with h :: _ -> h | [] -> (-1)); print_newline ()" n in
      (prog, src)) (int_range 0 49));

    (* 171. Pat_cons then Pat_nil: empty list *)
    (return
      (let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_nil,
          [(Pat_cons (Pat_var (cl "h"), Pat_wild), Exp_var (cl "h"));
           (Pat_nil, Exp_int (-1))])))] in
      let src = "let () = print_int (match [] with h :: _ -> h | [] -> (-1)); print_newline ()" in
      (prog, src)));

    (* === BATCH 7: Record + function integration === *)

    (* 172. Record field in function body *)
    (map3 (fun a b c ->
      let prog = [
        Decl_type (cl "r3", [],
          Td_record [(cl "f1", Ty_int); (cl "f2", Ty_int); (cl "f3", Ty_int)]);
        Decl_let (cl "sum_fields",
          Exp_fun (cl "r",
            Exp_binop (Op_add,
              Exp_field (Exp_var (cl "r"), cl "f1"),
              Exp_binop (Op_add,
                Exp_field (Exp_var (cl "r"), cl "f2"),
                Exp_field (Exp_var (cl "r"), cl "f3")))));
        Decl_expr (print_int_nl
          (Exp_app (Exp_var (cl "sum_fields"),
            Exp_record [(cl "f1", Exp_int a); (cl "f2", Exp_int b); (cl "f3", Exp_int c)])))] in
      let src = Printf.sprintf "type r3 = { f1 : int; f2 : int; f3 : int }\nlet sum_fields r = r.f1 + r.f2 + r.f3\nlet () = print_int (sum_fields { f1 = %d; f2 = %d; f3 = %d }); print_newline ()" a b c in
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* === BATCH 8: Large negative int patterns in match === *)

    (* 173. Match with negative integers *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_int (-2), Exp_int 1);
           (Pat_int (-1), Exp_int 2);
           (Pat_int 0, Exp_int 3);
           (Pat_int 1, Exp_int 4);
           (Pat_int 2, Exp_int 5);
           (Pat_wild, Exp_int 0)])))] in
      let src = Printf.sprintf "let () = print_int (match %d with (-2) -> 1 | (-1) -> 2 | 0 -> 3 | 1 -> 4 | 2 -> 5 | _ -> 0); print_newline ()" n in
      (prog, src)) (int_range (-3) 4));

    (* 174. succ builtin *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_app (Exp_var (cl "succ"), Exp_int n)))] in
      let src = Printf.sprintf "let () = print_int (succ %d); print_newline ()" n in
      (prog, src)) (int_range (-5) 50));

    (* 175. pred builtin *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_app (Exp_var (cl "pred"), Exp_int n)))] in
      let src = Printf.sprintf "let () = print_int (pred %d); print_newline ()" n in
      (prog, src)) (int_range (-5) 50));
  ]

let print_test_case (_prog, src) = src

let compile_vs_ocamlc_test =
  QCheck.Test.make ~name:"compile vs ocamlc" ~count:1000
    (QCheck.make gen_test_case ~print:print_test_case)
    (fun (prog, source) ->
       with_temp_dir (fun dir ->
         let our_result = run_our_compiler prog in
         match compile_and_run_ocamlc dir source with
         | None -> true
         | Some expected ->
           (match our_result with
            | Ok ours -> ours = expected
            | Error _msg -> false)))

let random_compile_vs_ocamlc_test =
  QCheck.Test.make ~name:"compile vs ocamlc (random AST)" ~count:300
    (QCheck.make gen_random_program_with_source ~print:(fun (_prog, src) -> src))
    (fun (prog, source) ->
       with_temp_dir (fun dir ->
         let our_result = run_our_compiler prog in
         match compile_and_run_ocamlc dir source with
         | None -> true
         | Some expected ->
           (match our_result with
            | Ok ours -> ours = expected
            | Error _msg -> false)))

let () =
  exit (QCheck_base_runner.run_tests ~verbose:true [compile_vs_ocamlc_test; random_compile_vs_ocamlc_test])
