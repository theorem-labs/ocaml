(* compile_test.ml - PBT: our compiler + bytecode interpreter vs ocamlrun. *)

open Interp_extracted
open Test_common

let generators = [|
  (* print_int literal *)
  (fun r ->
    let n = Random.State.int r 200 - 100 in
    let prog = [Decl_expr (print_int_nl (Exp_int n))] in
    let src = Printf.sprintf "let () = print_int (%d); print_newline ()" n in
    (prog, src));
  (* addition *)
  (fun r ->
    let a = Random.State.int r 100 in let b = Random.State.int r 100 + 1 in
    let prog = [Decl_expr (print_int_nl (Exp_binop (Op_add, Exp_int a, Exp_int b)))] in
    let src = Printf.sprintf "let () = print_int (%d + %d); print_newline ()" a b in
    (prog, src));
  (* subtraction *)
  (fun r ->
    let a = Random.State.int r 100 in let b = Random.State.int r 100 in
    let prog = [Decl_expr (print_int_nl (Exp_binop (Op_sub, Exp_int a, Exp_int b)))] in
    let src = Printf.sprintf "let () = print_int (%d - %d); print_newline ()" a b in
    (prog, src));
  (* multiplication *)
  (fun r ->
    let a = Random.State.int r 50 in let b = Random.State.int r 50 in
    let prog = [Decl_expr (print_int_nl (Exp_binop (Op_mul, Exp_int a, Exp_int b)))] in
    let src = Printf.sprintf "let () = print_int (%d * %d); print_newline ()" a b in
    (prog, src));
  (* if-then-else *)
  (fun r ->
    let n = Random.State.int r 100 in let t = Random.State.int r 100 in
    let prog = [Decl_expr (print_int_nl
      (Exp_if (Exp_binop (Op_gt, Exp_int n, Exp_int t), Exp_int 1, Exp_int 0)))] in
    let src = Printf.sprintf "let () = print_int (if %d > %d then 1 else 0); print_newline ()" n t in
    (prog, src));
  (* let binding *)
  (fun r ->
    let a = Random.State.int r 20 in let b = Random.State.int r 20 in
    let prog = [Decl_expr (print_int_nl
      (Exp_let (cl "x", Exp_int a,
        Exp_let (cl "y", Exp_int b,
          Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y"))))))] in
    let src = Printf.sprintf "let () = print_int (let x = %d in let y = %d in x + y); print_newline ()" a b in
    (prog, src));
  (* negation *)
  (fun r ->
    let a = Random.State.int r 100 in
    let prog = [Decl_expr (print_int_nl (Exp_unop (Op_neg, Exp_int a)))] in
    let src = Printf.sprintf "let () = print_int (- %d); print_newline ()" a in
    (prog, src));
  (* nested arithmetic *)
  (fun r ->
    let a = Random.State.int r 20 in let b = Random.State.int r 20 in let c = Random.State.int r 20 in
    let prog = [Decl_expr (print_int_nl
      (Exp_binop (Op_add, Exp_binop (Op_mul, Exp_int a, Exp_int b), Exp_int c)))] in
    let src = Printf.sprintf "let () = print_int (%d * %d + %d); print_newline ()" a b c in
    (prog, src));
  (* simple function: f x = x + x *)
  (fun r ->
    let n = Random.State.int r 50 in
    let prog = [Decl_expr (print_int_nl
      (Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "x"))),
        Exp_app (Exp_var (cl "f"), Exp_int n))))] in
    let src = Printf.sprintf "let () = print_int (let f x = x + x in f %d); print_newline ()" n in
    (prog, src));
  (* recursive function: factorial *)
  (fun r ->
    let n = Random.State.int r 10 in
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
    (prog, src));
  (* recursive function: fibonacci *)
  (fun r ->
    let n = Random.State.int r 15 in
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
    (prog, src));
  (* tuple + fst/snd *)
  (fun r ->
    let a = Random.State.int r 50 in let b = Random.State.int r 50 in
    let prog = [Decl_expr (print_int_nl
      (Exp_let (cl "p", Exp_tuple [Exp_int a; Exp_int b],
        Exp_binop (Op_add,
          Exp_app (Exp_var (cl "fst"), Exp_var (cl "p")),
          Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))))))] in
    let src = Printf.sprintf "let () = print_int (let p = (%d, %d) in fst p + snd p); print_newline ()" a b in
    (prog, src));
  (* multi-arg function *)
  (fun r ->
    let a = Random.State.int r 30 in let b = Random.State.int r 30 in
    let prog = [Decl_expr (print_int_nl
      (Exp_let (cl "f",
        Exp_fun (cl "x", Exp_fun (cl "y",
          Exp_binop (Op_add, Exp_binop (Op_mul, Exp_var (cl "x"), Exp_var (cl "y")), Exp_int 1))),
        Exp_app (Exp_app (Exp_var (cl "f"), Exp_int a), Exp_int b))))] in
    let src = Printf.sprintf "let () = print_int (let f x y = x * y + 1 in f %d %d); print_newline ()" a b in
    (prog, src));
  (* match on int: 3 cases *)
  (fun r ->
    let n = Random.State.int r 3 in
    let prog = [Decl_expr (print_int_nl
      (Exp_match (Exp_int n,
        [(Pat_int 0, Exp_int 100);
         (Pat_int 1, Exp_int 200);
         (Pat_wild, Exp_int 999)])))] in
    let src = Printf.sprintf "let () = print_int (match %d with 0 -> 100 | 1 -> 200 | _ -> 999); print_newline ()" n in
    (prog, src));
  (* match with variable binding *)
  (fun r ->
    let n = Random.State.int r 100 in
    let prog = [Decl_expr (print_int_nl
      (Exp_match (Exp_int n,
        [(Pat_int 0, Exp_int 42);
         (Pat_var (cl "x"), Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1))])))] in
    let src = Printf.sprintf "let () = print_int (match %d with 0 -> 42 | x -> x + 1); print_newline ()" n in
    (prog, src));
  (* match on computed value *)
  (fun r ->
    let a = Random.State.int r 20 in let b = Random.State.int r 20 in
    let prog = [Decl_expr (print_int_nl
      (Exp_match (Exp_binop (Op_sub, Exp_int a, Exp_int b),
        [(Pat_int 0, Exp_int 1);
         (Pat_wild, Exp_int 0)])))] in
    let src = Printf.sprintf "let () = print_int (match %d - %d with 0 -> 1 | _ -> 0); print_newline ()" a b in
    (prog, src));
  (* match with multiple int cases *)
  (fun r ->
    let n = Random.State.int r 5 in
    let prog = [Decl_expr (print_int_nl
      (Exp_match (Exp_int n,
        [(Pat_int 0, Exp_int 10);
         (Pat_int 1, Exp_int 20);
         (Pat_int 2, Exp_int 30);
         (Pat_int 3, Exp_int 40);
         (Pat_wild, Exp_int 50)])))] in
    let src = Printf.sprintf "let () = print_int (match %d with 0 -> 10 | 1 -> 20 | 2 -> 30 | 3 -> 40 | _ -> 50); print_newline ()" n in
    (prog, src));
  (* STRESS: nested if inside match body *)
  (fun r ->
    let n = Random.State.int r 3 in let m = Random.State.int r 10 in
    let prog = [Decl_expr (print_int_nl
      (Exp_match (Exp_int n,
        [(Pat_int 0, Exp_if (Exp_binop (Op_gt, Exp_int m, Exp_int 5), Exp_int 1, Exp_int 0));
         (Pat_wild, Exp_int 99)])))] in
    let src = Printf.sprintf "let () = print_int (match %d with 0 -> if %d > 5 then 1 else 0 | _ -> 99); print_newline ()" n m in
    (prog, src));
  (* STRESS: match inside if branch *)
  (fun r ->
    let x = Random.State.int r 10 in
    let prog = [Decl_expr (print_int_nl
      (Exp_if (Exp_binop (Op_gt, Exp_int x, Exp_int 5),
        Exp_match (Exp_int x,
          [(Pat_int 6, Exp_int 60); (Pat_int 7, Exp_int 70); (Pat_wild, Exp_int 80)]),
        Exp_int 0)))] in
    let src = Printf.sprintf "let () = print_int (if %d > 5 then (match %d with 6 -> 60 | 7 -> 70 | _ -> 80) else 0); print_newline ()" x x in
    (prog, src));
  (* STRESS: function returning match result *)
  (fun r ->
    let n = Random.State.int r 3 in
    let prog = [Decl_expr (print_int_nl
      (Exp_let (cl "f",
        Exp_fun (cl "x",
          Exp_match (Exp_var (cl "x"),
            [(Pat_int 0, Exp_int 100); (Pat_int 1, Exp_int 200); (Pat_wild, Exp_int 300)])),
        Exp_app (Exp_var (cl "f"), Exp_int n))))] in
    let src = Printf.sprintf "let () = print_int (let f x = match x with 0 -> 100 | 1 -> 200 | _ -> 300 in f %d); print_newline ()" n in
    (prog, src));
  (* STRESS: let inside match body *)
  (fun r ->
    let n = Random.State.int r 3 in let a = Random.State.int r 20 in
    let prog = [Decl_expr (print_int_nl
      (Exp_match (Exp_int n,
        [(Pat_int 0, Exp_let (cl "y", Exp_int a, Exp_binop (Op_mul, Exp_var (cl "y"), Exp_int 2)));
         (Pat_wild, Exp_int 0)])))] in
    let src = Printf.sprintf "let () = print_int (match %d with 0 -> let y = %d in y * 2 | _ -> 0); print_newline ()" n a in
    (prog, src));
  (* STRESS: deeply nested let *)
  (fun r ->
    let a = Random.State.int r 10 in let b = Random.State.int r 10 in
    let c = Random.State.int r 10 in let d = Random.State.int r 10 in
    let prog = [Decl_expr (print_int_nl
      (Exp_let (cl "a", Exp_int a,
        Exp_let (cl "b", Exp_int b,
          Exp_let (cl "c", Exp_int c,
            Exp_let (cl "d", Exp_int d,
              Exp_binop (Op_add,
                Exp_binop (Op_add, Exp_var (cl "a"), Exp_var (cl "b")),
                Exp_binop (Op_add, Exp_var (cl "c"), Exp_var (cl "d")))))))))] in
    let src = Printf.sprintf "let () = print_int (let a = %d in let b = %d in let c = %d in let d = %d in a + b + c + d); print_newline ()" a b c d in
    (prog, src));
  (* STRESS: recursive function with match *)
  (fun r ->
    let n = Random.State.int r 8 in
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
    (prog, src));
  (* STRESS: top-level Decl_letrec *)
  (fun r ->
    let n = Random.State.int r 10 in
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
    (prog, src));
  (* COVERAGE: non-commutative tuple access (fst p - snd p) *)
  (fun r ->
    let a = Random.State.int r 50 + 10 in let b = Random.State.int r 50 in
    let prog = [Decl_expr (print_int_nl
      (Exp_let (cl "p", Exp_tuple [Exp_int a; Exp_int b],
        Exp_binop (Op_sub,
          Exp_app (Exp_var (cl "fst"), Exp_var (cl "p")),
          Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))))))] in
    let src = Printf.sprintf "let () = print_int (let p = (%d, %d) in fst p - snd p); print_newline ()" a b in
    (prog, src));
  (* COVERAGE: division and modulo *)
  (fun r ->
    let a = Random.State.int r 500 + 1 in let b = Random.State.int r 20 + 1 in
    let prog = [Decl_expr (print_int_nl
      (Exp_binop (Op_add,
        Exp_binop (Op_div, Exp_int a, Exp_int b),
        Exp_binop (Op_mod, Exp_int a, Exp_int b))))] in
    let src = Printf.sprintf "let () = print_int (%d / %d + %d mod %d); print_newline ()" a b a b in
    (prog, src));
  (* COVERAGE: nested function call f(g(x)) *)
  (fun r ->
    let n = Random.State.int r 20 in
    let prog = [Decl_expr (print_int_nl
      (Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)),
        Exp_let (cl "g", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)),
          Exp_app (Exp_var (cl "f"), Exp_app (Exp_var (cl "g"), Exp_int n))))))] in
    let src = Printf.sprintf "let () = print_int (let f x = x + 1 in let g x = x * 2 in f (g %d)); print_newline ()" n in
    (prog, src));
  (* COVERAGE: higher-order function returning closure *)
  (fun r ->
    let n = Random.State.int r 20 in let m = Random.State.int r 20 in
    let prog = [Decl_expr (print_int_nl
      (Exp_let (cl "make_adder",
        Exp_fun (cl "n", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "n")))),
        Exp_app (Exp_app (Exp_var (cl "make_adder"), Exp_int n), Exp_int m))))] in
    let src = Printf.sprintf "let () = print_int (let make_adder n x = n + x in make_adder %d %d); print_newline ()" n m in
    (prog, src));
  (* COVERAGE: multiple print statements for event ordering *)
  (fun r ->
    let a = Random.State.int r 10 in let b = Random.State.int r 10 in
    let prog = [Decl_expr
      (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int a),
        Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int b),
          Exp_app (Exp_var (cl "print_newline"), Exp_unit))))] in
    let src = Printf.sprintf "let () = print_int %d; print_int %d; print_newline ()" a b in
    (prog, src));
  (* COVERAGE: comparison operators *)
  (fun r ->
    let a = Random.State.int r 20 in let b = Random.State.int r 20 in
    let prog = [Decl_expr (print_int_nl
      (Exp_binop (Op_add,
        Exp_binop (Op_add,
          Exp_if (Exp_binop (Op_lt, Exp_int a, Exp_int b), Exp_int 1, Exp_int 0),
          Exp_if (Exp_binop (Op_eq, Exp_int a, Exp_int b), Exp_int 10, Exp_int 0)),
        Exp_if (Exp_binop (Op_ge, Exp_int a, Exp_int b), Exp_int 100, Exp_int 0))))] in
    let src = Printf.sprintf "let () = print_int ((if %d < %d then 1 else 0) + (if %d = %d then 10 else 0) + (if %d >= %d then 100 else 0)); print_newline ()" a b a b a b in
    (prog, src));
  (* COVERAGE: sequence of let bindings reusing names *)
  (fun r ->
    let a = Random.State.int r 20 in let b = Random.State.int r 20 in
    let prog = [Decl_expr (print_int_nl
      (Exp_let (cl "x", Exp_int a,
        Exp_let (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int b),
          Exp_var (cl "x")))))] in
    let src = Printf.sprintf "let () = print_int (let x = %d in let x = x + %d in x); print_newline ()" a b in
    (prog, src));
  (* COVERAGE: partial application via currying *)
  (fun r ->
    let n = Random.State.int r 50 in
    let prog = [Decl_expr (print_int_nl
      (Exp_let (cl "add",
        Exp_fun (cl "x", Exp_fun (cl "y", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y")))),
        Exp_let (cl "inc", Exp_app (Exp_var (cl "add"), Exp_int 1),
          Exp_app (Exp_var (cl "inc"), Exp_int n)))))] in
    let src = Printf.sprintf "let () = print_int (let add x y = x + y in let inc = add 1 in inc %d); print_newline ()" n in
    (prog, src));
|]

let () =
  let num = try int_of_string Sys.argv.(1) with _ -> 50 in
  let seed = try int_of_string Sys.argv.(2) with _ -> 42 in
  let rng = Random.State.make [| seed |] in
  Printf.printf "Compile PBT: %d tests (seed=%d)\n\n%!" num seed;
  let pass = ref 0 and fail = ref 0 and skip = ref 0 in
  with_temp_dir (fun dir ->
    for _ = 1 to num do
      let gen = generators.(Random.State.int rng (Array.length generators)) in
      let prog, source = gen rng in
      Printf.printf "Test: %s\n%!" source;
      match compile_and_run_ocamlc dir source with
      | None -> Printf.printf "  SKIP\n%!"; incr skip
      | Some expected ->
        Printf.printf "  ocamlrun: %S\n%!" expected;
        (match run_our_compiler prog with
         | Ok ours ->
           Printf.printf "  ours:     %S\n%!" ours;
           if ours = expected then (Printf.printf "  PASS\n%!"; incr pass)
           else (Printf.printf "  FAIL: output mismatch\n%!"; incr fail)
         | Error msg ->
           Printf.printf "  FAIL: %s\n%!" msg; incr fail)
    done);
  Printf.printf "\n=== Compile PBT Results: %d pass, %d fail, %d skip ===\n" !pass !fail !skip;
  if !fail > 0 then exit 1
