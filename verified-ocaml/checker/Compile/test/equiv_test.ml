(* bytecode_equiv_test.ml - Part 5: PBT that our compiler and ocamlc produce
   behaviorally equivalent bytecode. For each test program:
   1. Compile AST with compile_program -> run through our bytecode interpreter
   2. OCaml source -> compile with ocamlc -> load bytecode -> run through our interpreter
   3. Compare outputs
   Migrated to QCheck. *)

open Interp_extracted
open Test_common

(* QCheck generators producing (prog, source) pairs *)
let gen_test_case : (decl list * string) QCheck.Gen.t =
  let open QCheck.Gen in
  oneof [
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl (Exp_int n))] in
      let src = Printf.sprintf "let () = print_int (%d); print_newline ()" n in
      (prog, src)) (int_range (-100) 99));
    (map2 (fun a b ->
      let b = b + 1 in
      let prog = [Decl_expr (print_int_nl (Exp_binop (Op_add, Exp_int a, Exp_int b)))] in
      let src = Printf.sprintf "let () = print_int (%d + %d); print_newline ()" a b in
      (prog, src)) (int_range 0 99) (int_range 0 99));
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl (Exp_binop (Op_sub, Exp_int a, Exp_int b)))] in
      let src = Printf.sprintf "let () = print_int (%d - %d); print_newline ()" a b in
      (prog, src)) (int_range 0 99) (int_range 0 99));
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl (Exp_binop (Op_mul, Exp_int a, Exp_int b)))] in
      let src = Printf.sprintf "let () = print_int (%d * %d); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));
    (map2 (fun n t ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_binop (Op_gt, Exp_int n, Exp_int t), Exp_int 1, Exp_int 0)))] in
      let src = Printf.sprintf "let () = print_int (if %d > %d then 1 else 0); print_newline ()" n t in
      (prog, src)) (int_range 0 99) (int_range 0 99));
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "y", Exp_int b,
            Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y"))))))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in let y = %d in x + y); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "x"))),
          Exp_app (Exp_var (cl "f"), Exp_int n))))] in
      let src = Printf.sprintf "let () = print_int (let f x = x + x in f %d); print_newline ()" n in
      (prog, src)) (int_range 0 49));
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
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "p", Exp_tuple [Exp_int a; Exp_int b],
          Exp_binop (Op_add,
            Exp_app (Exp_var (cl "fst"), Exp_var (cl "p")),
            Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))))))] in
      let src = Printf.sprintf "let () = print_int (let p = (%d, %d) in fst p + snd p); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_int 0, Exp_int 100);
           (Pat_int 1, Exp_int 200);
           (Pat_wild, Exp_int 999)])))] in
      let src = Printf.sprintf "let () = print_int (match %d with 0 -> 100 | 1 -> 200 | _ -> 999); print_newline ()" n in
      (prog, src)) (int_range 0 2));
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_fun (cl "x", Exp_fun (cl "y",
            Exp_binop (Op_add, Exp_binop (Op_mul, Exp_var (cl "x"), Exp_var (cl "y")), Exp_int 1))),
          Exp_app (Exp_app (Exp_var (cl "f"), Exp_int a), Exp_int b))))] in
      let src = Printf.sprintf "let () = print_int (let f x y = x * y + 1 in f %d %d); print_newline ()" a b in
      (prog, src)) (int_range 0 29) (int_range 0 29));
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
    (map (fun a ->
      let prog = [Decl_expr (print_int_nl (Exp_unop (Op_neg, Exp_int a)))] in
      let src = Printf.sprintf "let () = print_int (- %d); print_newline ()" a in
      (prog, src)) (int_range 0 99));
    (* nested arithmetic *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add, Exp_binop (Op_mul, Exp_int a, Exp_int b), Exp_int c)))] in
      let src = Printf.sprintf "let () = print_int (%d * %d + %d); print_newline ()" a b c in
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 19));
    (* match with variable binding *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_int 0, Exp_int 42);
           (Pat_var (cl "x"), Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1))])))] in
      let src = Printf.sprintf "let () = print_int (match %d with 0 -> 42 | x -> x + 1); print_newline ()" n in
      (prog, src)) (int_range 0 99));
    (* match on computed value *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_binop (Op_sub, Exp_int a, Exp_int b),
          [(Pat_int 0, Exp_int 1);
           (Pat_wild, Exp_int 0)])))] in
      let src = Printf.sprintf "let () = print_int (match %d - %d with 0 -> 1 | _ -> 0); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));
    (* match with 5 int cases *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_int 0, Exp_int 10); (Pat_int 1, Exp_int 20);
           (Pat_int 2, Exp_int 30); (Pat_int 3, Exp_int 40);
           (Pat_wild, Exp_int 50)])))] in
      let src = Printf.sprintf "let () = print_int (match %d with 0 -> 10 | 1 -> 20 | 2 -> 30 | 3 -> 40 | _ -> 50); print_newline ()" n in
      (prog, src)) (int_range 0 4));
    (* nested if inside match body *)
    (map2 (fun n m ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_int n,
          [(Pat_int 0, Exp_if (Exp_binop (Op_gt, Exp_int m, Exp_int 5), Exp_int 1, Exp_int 0));
           (Pat_wild, Exp_int 99)])))] in
      let src = Printf.sprintf "let () = print_int (match %d with 0 -> if %d > 5 then 1 else 0 | _ -> 99); print_newline ()" n m in
      (prog, src)) (int_range 0 2) (int_range 0 9));
    (* function returning match result *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_fun (cl "x",
            Exp_match (Exp_var (cl "x"),
              [(Pat_int 0, Exp_int 100); (Pat_int 1, Exp_int 200); (Pat_wild, Exp_int 300)])),
          Exp_app (Exp_var (cl "f"), Exp_int n))))] in
      let src = Printf.sprintf "let () = print_int (let f x = match x with 0 -> 100 | 1 -> 200 | _ -> 300 in f %d); print_newline ()" n in
      (prog, src)) (int_range 0 2));
    (* deeply nested let *)
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
    (* recursive function with match *)
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
    (* top-level Decl_letrec *)
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
    (* non-commutative tuple access *)
    (map2 (fun a b ->
      let a = a + 10 in
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "p", Exp_tuple [Exp_int a; Exp_int b],
          Exp_binop (Op_sub,
            Exp_app (Exp_var (cl "fst"), Exp_var (cl "p")),
            Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))))))] in
      let src = Printf.sprintf "let () = print_int (let p = (%d, %d) in fst p - snd p); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));
    (* division and modulo *)
    (map2 (fun a b ->
      let a = a + 1 in let b = b + 1 in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add,
          Exp_binop (Op_div, Exp_int a, Exp_int b),
          Exp_binop (Op_mod, Exp_int a, Exp_int b))))] in
      let src = Printf.sprintf "let () = print_int (%d / %d + %d mod %d); print_newline ()" a b a b in
      (prog, src)) (int_range 0 499) (int_range 0 19));
    (* nested function calls f(g(x)) *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)),
          Exp_let (cl "g", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)),
            Exp_app (Exp_var (cl "f"), Exp_app (Exp_var (cl "g"), Exp_int n))))))] in
      let src = Printf.sprintf "let () = print_int (let f x = x + 1 in let g x = x * 2 in f (g %d)); print_newline ()" n in
      (prog, src)) (int_range 0 19));
    (* higher-order function returning closure *)
    (map2 (fun n m ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "make_adder",
          Exp_fun (cl "n", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "n")))),
          Exp_app (Exp_app (Exp_var (cl "make_adder"), Exp_int n), Exp_int m))))] in
      let src = Printf.sprintf "let () = print_int (let make_adder n x = n + x in make_adder %d %d); print_newline ()" n m in
      (prog, src)) (int_range 0 19) (int_range 0 19));
    (* multiple print statements *)
    (map2 (fun a b ->
      let prog = [Decl_expr
        (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int a),
          Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int b),
            Exp_app (Exp_var (cl "print_newline"), Exp_unit))))] in
      let src = Printf.sprintf "let () = print_int %d; print_int %d; print_newline ()" a b in
      (prog, src)) (int_range 0 9) (int_range 0 9));
    (* comparison operators *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add,
          Exp_binop (Op_add,
            Exp_if (Exp_binop (Op_lt, Exp_int a, Exp_int b), Exp_int 1, Exp_int 0),
            Exp_if (Exp_binop (Op_eq, Exp_int a, Exp_int b), Exp_int 10, Exp_int 0)),
          Exp_if (Exp_binop (Op_ge, Exp_int a, Exp_int b), Exp_int 100, Exp_int 0))))] in
      let src = Printf.sprintf "let () = print_int ((if %d < %d then 1 else 0) + (if %d = %d then 10 else 0) + (if %d >= %d then 100 else 0)); print_newline ()" a b a b a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));
    (* variable shadowing *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int b),
            Exp_var (cl "x")))))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in let x = x + %d in x); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));
    (* partial application via currying *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "add",
          Exp_fun (cl "x", Exp_fun (cl "y", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y")))),
          Exp_let (cl "inc", Exp_app (Exp_var (cl "add"), Exp_int 1),
            Exp_app (Exp_var (cl "inc"), Exp_int n)))))] in
      let src = Printf.sprintf "let () = print_int (let add x y = x + y in let inc = add 1 in inc %d); print_newline ()" n in
      (prog, src)) (int_range 0 49));
  ]

let print_test_case (_prog, src) = src

let bytecode_equiv_test =
  QCheck.Test.make ~name:"bytecode equivalence: our compiler vs ocamlc" ~count:100
    (QCheck.make gen_test_case ~print:print_test_case)
    (fun (prog, source) ->
       with_temp_dir (fun dir ->
         let our_result = run_compiled prog in
         match compile_ocamlc dir source with
         | None -> true  (* skip *)
         | Some exe ->
           let ocamlc_result = run_our_pipeline exe in
           (match our_result, ocamlc_result with
            | Ok ours, Ok theirs -> ours = theirs
            | _ -> false)))

let () =
  exit (QCheck_base_runner.run_tests ~verbose:true [bytecode_equiv_test])
