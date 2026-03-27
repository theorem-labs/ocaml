(* advanced_test.ml - Hand-crafted tests for complex OCaml programs.
   Tests features that go beyond what random generators typically produce:
   closures sharing captured variables, deep recursion, higher-order functions
   with recursion, currying, nested closures, complex match, tuples, etc.

   Each test builds the AST manually, runs it through all three paths:
   1. Our compiler (compile_program + bytecode interpreter)
   2. Source interpreter (interpret)
   3. Reference (ocamlc + ocamlrun)
   and asserts all three agree. *)

open Interp_extracted
open Test_common

(* === Test runner === *)

let passed = ref 0
let failed = ref 0

let run_test name prog source =
  Printf.printf "  %-50s " name;
  let compiler_result = run_compiled prog in
  let interp_result = run_source_interp ~fuel:100000 prog in
  let ref_result = with_temp_dir (fun dir -> compile_and_run_ocamlc dir source) in
  let ok = ref true in
  (* Check compiler vs reference *)
  (match compiler_result, ref_result with
   | Ok co, Some ro ->
     if co <> ro then begin
       Printf.printf "FAIL\n";
       Printf.printf "    compiler output:  %S\n" co;
       Printf.printf "    ocamlrun output:  %S\n" ro;
       ok := false
     end
   | Error e, _ ->
     Printf.printf "FAIL\n";
     Printf.printf "    compiler error: %s\n" e;
     ok := false
   | _, None ->
     Printf.printf "FAIL\n";
     Printf.printf "    ocamlc failed to compile source\n";
     ok := false);
  (* Check source interpreter vs reference *)
  (match interp_result, ref_result with
   | Interp_ok io, Some ro ->
     if io <> ro then begin
       if !ok then Printf.printf "FAIL\n";
       Printf.printf "    interp output:    %S\n" io;
       Printf.printf "    ocamlrun output:  %S\n" ro;
       ok := false
     end
   | Interp_err e, _ ->
     if !ok then Printf.printf "FAIL\n";
     Printf.printf "    interp error: %s\n" e;
     ok := false
   | _, None -> ());  (* already reported above *)
  (* Check compiler vs source interpreter *)
  (match compiler_result, interp_result with
   | Ok co, Interp_ok io ->
     if co <> io then begin
       if !ok then Printf.printf "FAIL\n";
       Printf.printf "    compiler output:  %S\n" co;
       Printf.printf "    interp output:    %S\n" io;
       ok := false
     end
   | _ -> ());
  if !ok then begin
    Printf.printf "OK\n";
    incr passed
  end else
    incr failed

(* === Test cases === *)

let () =
  Printf.printf "Advanced compiler/interpreter tests\n";
  Printf.printf "====================================\n\n";

  (* 1. Mutual-free-variable closures:
       let x = 10 in
       let f y = x + y in
       let g y = x * y in
       print_int (f 3 + g 2) *)
  let prog1 = [Decl_expr (print_int_nl
    (Exp_let (cl "x", Exp_int 10,
      Exp_let (cl "f", Exp_fun (cl "y",
        Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y"))),
      Exp_let (cl "g", Exp_fun (cl "y",
        Exp_binop (Op_mul, Exp_var (cl "x"), Exp_var (cl "y"))),
      Exp_binop (Op_add,
        Exp_app (Exp_var (cl "f"), Exp_int 3),
        Exp_app (Exp_var (cl "g"), Exp_int 2)))))))] in
  let src1 = "let () = let x = 10 in let f y = x + y in let g y = x * y in print_int (f 3 + g 2); print_newline ()" in
  run_test "1. mutual-free-variable closures" prog1 src1;

  (* 2. Deeply nested recursion: factorial 10 = 3628800 *)
  let prog2 = [Decl_expr (print_int_nl
    (Exp_letrec (cl "fact",
      Exp_fun (cl "n",
        Exp_if (Exp_binop (Op_le, Exp_var (cl "n"), Exp_int 1),
          Exp_int 1,
          Exp_binop (Op_mul, Exp_var (cl "n"),
            Exp_app (Exp_var (cl "fact"),
              Exp_binop (Op_sub, Exp_var (cl "n"), Exp_int 1))))),
      Exp_app (Exp_var (cl "fact"), Exp_int 10))))] in
  let src2 = "let () = let rec fact n = if n <= 1 then 1 else n * fact (n - 1) in print_int (fact 10); print_newline ()" in
  run_test "2. factorial 10 = 3628800" prog2 src2;

  (* 3. Fibonacci 15 = 610 *)
  let prog3 = [Decl_expr (print_int_nl
    (Exp_letrec (cl "fib",
      Exp_fun (cl "n",
        Exp_if (Exp_binop (Op_le, Exp_var (cl "n"), Exp_int 1),
          Exp_var (cl "n"),
          Exp_binop (Op_add,
            Exp_app (Exp_var (cl "fib"), Exp_binop (Op_sub, Exp_var (cl "n"), Exp_int 1)),
            Exp_app (Exp_var (cl "fib"), Exp_binop (Op_sub, Exp_var (cl "n"), Exp_int 2))))),
      Exp_app (Exp_var (cl "fib"), Exp_int 15))))] in
  let src3 = "let () = let rec fib n = if n <= 1 then n else fib (n - 1) + fib (n - 2) in print_int (fib 15); print_newline ()" in
  run_test "3. fibonacci 15 = 610" prog3 src3;

  (* 4. Recursive descent over match: sum 10 = 55
       let rec sum n = match n with 0 -> 0 | x -> x + sum (x - 1) in
       print_int (sum 10) *)
  let prog4 = [Decl_expr (print_int_nl
    (Exp_letrec (cl "sum",
      Exp_fun (cl "n",
        Exp_match (Exp_var (cl "n"),
          [(Pat_int 0, Exp_int 0);
           (Pat_var (cl "x"), Exp_binop (Op_add, Exp_var (cl "x"),
             Exp_app (Exp_var (cl "sum"),
               Exp_binop (Op_sub, Exp_var (cl "x"), Exp_int 1))))])),
      Exp_app (Exp_var (cl "sum"), Exp_int 10))))] in
  let src4 = "let () = let rec sum n = match n with 0 -> 0 | x -> x + sum (x - 1) in print_int (sum 10); print_newline ()" in
  run_test "4. recursive match sum 10 = 55" prog4 src4;

  (* 5. Curried multi-arg application:
       let f x y z = x + y * z in
       print_int (f 1 2 3)  -- should be 7 *)
  let prog5 = [Decl_expr (print_int_nl
    (Exp_let (cl "f",
      Exp_fun (cl "x", Exp_fun (cl "y", Exp_fun (cl "z",
        Exp_binop (Op_add, Exp_var (cl "x"),
          Exp_binop (Op_mul, Exp_var (cl "y"), Exp_var (cl "z")))))),
      Exp_app (Exp_app (Exp_app (Exp_var (cl "f"), Exp_int 1), Exp_int 2), Exp_int 3))))] in
  let src5 = "let () = let f x y z = x + y * z in print_int (f 1 2 3); print_newline ()" in
  run_test "5. curried multi-arg f 1 2 3 = 7" prog5 src5;

  (* 6. Nested closures (closure over closure):
       let make_adder x = fun y -> x + y in
       let add5 = make_adder 5 in
       let add10 = make_adder 10 in
       print_int (add5 3 + add10 7) *)
  let prog6 = [Decl_expr (print_int_nl
    (Exp_let (cl "make_adder",
      Exp_fun (cl "x", Exp_fun (cl "y",
        Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y")))),
      Exp_let (cl "add5", Exp_app (Exp_var (cl "make_adder"), Exp_int 5),
      Exp_let (cl "add10", Exp_app (Exp_var (cl "make_adder"), Exp_int 10),
      Exp_binop (Op_add,
        Exp_app (Exp_var (cl "add5"), Exp_int 3),
        Exp_app (Exp_var (cl "add10"), Exp_int 7)))))))] in
  let src6 = "let () = let make_adder x = fun y -> x + y in let add5 = make_adder 5 in let add10 = make_adder 10 in print_int (add5 3 + add10 7); print_newline ()" in
  run_test "6. nested closures add5 3 + add10 7 = 25" prog6 src6;

  (* 7. Higher-order with recursion:
       let rec apply_n f n x = if n <= 0 then x else apply_n f (n-1) (f x) in
       print_int (apply_n (fun x -> x + 1) 10 0) *)
  let prog7 = [Decl_expr (print_int_nl
    (Exp_letrec (cl "apply_n",
      Exp_fun (cl "f", Exp_fun (cl "n", Exp_fun (cl "x",
        Exp_if (Exp_binop (Op_le, Exp_var (cl "n"), Exp_int 0),
          Exp_var (cl "x"),
          Exp_app (Exp_app (Exp_app (Exp_var (cl "apply_n"),
            Exp_var (cl "f")),
            Exp_binop (Op_sub, Exp_var (cl "n"), Exp_int 1)),
            Exp_app (Exp_var (cl "f"), Exp_var (cl "x"))))))),
      Exp_app (Exp_app (Exp_app (Exp_var (cl "apply_n"),
        Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1))),
        Exp_int 10),
        Exp_int 0))))] in
  let src7 = "let () = let rec apply_n f n x = if n <= 0 then x else apply_n f (n - 1) (f x) in print_int (apply_n (fun x -> x + 1) 10 0); print_newline ()" in
  run_test "7. higher-order recursive apply_n (+1) 10 0 = 10" prog7 src7;

  (* 8. Multiple print statements building output:
       print_int 1; print_int 2; print_int 3; print_newline () *)
  let prog8 = [Decl_expr
    (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int 1),
      Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int 2),
        Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int 3),
          Exp_app (Exp_var (cl "print_newline"), Exp_unit)))))] in
  let src8 = "let () = print_int 1; print_int 2; print_int 3; print_newline ()" in
  run_test "8. sequential prints 123" prog8 src8;

  (* 9. Complex match with computation in arms:
       let classify n = match n with
         | 0 -> 100 | 1 -> 200 | _ -> n * 10
       in print_int (classify 0 + classify 1 + classify 5) *)
  let classify_body =
    Exp_fun (cl "n",
      Exp_match (Exp_var (cl "n"),
        [(Pat_int 0, Exp_int 100);
         (Pat_int 1, Exp_int 200);
         (Pat_var (cl "m"), Exp_binop (Op_mul, Exp_var (cl "m"), Exp_int 10))])) in
  let prog9 = [Decl_expr (print_int_nl
    (Exp_let (cl "classify", classify_body,
      Exp_binop (Op_add,
        Exp_binop (Op_add,
          Exp_app (Exp_var (cl "classify"), Exp_int 0),
          Exp_app (Exp_var (cl "classify"), Exp_int 1)),
        Exp_app (Exp_var (cl "classify"), Exp_int 5)))))] in
  let src9 = "let () = let classify n = match n with 0 -> 100 | 1 -> 200 | m -> m * 10 in print_int (classify 0 + classify 1 + classify 5); print_newline ()" in
  run_test "9. complex match classify = 350" prog9 src9;

  (* 10. Tuple construction and extraction:
       let swap p = (snd p, fst p) in
       let p = (10, 20) in
       let q = swap p in
       print_int (fst q + snd q) *)
  let prog10 = [Decl_expr (print_int_nl
    (Exp_let (cl "swap",
      Exp_fun (cl "p",
        Exp_tuple [
          Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"));
          Exp_app (Exp_var (cl "fst"), Exp_var (cl "p"))]),
      Exp_let (cl "p", Exp_tuple [Exp_int 10; Exp_int 20],
      Exp_let (cl "q", Exp_app (Exp_var (cl "swap"), Exp_var (cl "p")),
      Exp_binop (Op_add,
        Exp_app (Exp_var (cl "fst"), Exp_var (cl "q")),
        Exp_app (Exp_var (cl "snd"), Exp_var (cl "q"))))))))] in
  let src10 = "let () = let swap p = (snd p, fst p) in let p = (10, 20) in let q = swap p in print_int (fst q + snd q); print_newline ()" in
  run_test "10. tuple swap fst q + snd q = 30" prog10 src10;

  (* 11. Pat_tuple: basic 2-tuple destructuring
       let (a, b) = (10, 20) in print_int (a + b); print_newline () *)
  let prog11 = [Decl_expr (print_int_nl
    (Exp_match (Exp_tuple [Exp_int 10; Exp_int 20],
      [(Pat_tuple [Pat_var (cl "a"); Pat_var (cl "b")],
        Exp_binop (Op_add, Exp_var (cl "a"), Exp_var (cl "b")))])))] in
  let src11 = "let () = print_int (match (10, 20) with (a, b) -> a + b); print_newline ()" in
  run_test "11. pat_tuple basic (10,20) -> a+b = 30" prog11 src11;

  (* 12. Pat_tuple: 3-tuple destructuring
       let (a, b, c) = (1, 2, 3) in print_int (a + b + c); print_newline () *)
  let prog12 = [Decl_expr (print_int_nl
    (Exp_match (Exp_tuple [Exp_int 1; Exp_int 2; Exp_int 3],
      [(Pat_tuple [Pat_var (cl "a"); Pat_var (cl "b"); Pat_var (cl "c")],
        Exp_binop (Op_add, Exp_var (cl "a"),
          Exp_binop (Op_add, Exp_var (cl "b"), Exp_var (cl "c"))))])))] in
  let src12 = "let () = print_int (match (1, 2, 3) with (a, b, c) -> a + b + c); print_newline ()" in
  run_test "12. pat_tuple 3-tuple (1,2,3) -> a+b+c = 6" prog12 src12;

  (* 13. Pat_tuple: destructure function result
       let f x = (x + 1, x * 2) in
       let (a, b) = f 5 in
       print_int (a + b); print_newline () *)
  let prog13 = [Decl_expr (print_int_nl
    (Exp_let (cl "f",
      Exp_fun (cl "x",
        Exp_tuple [Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1);
                   Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)]),
      Exp_match (Exp_app (Exp_var (cl "f"), Exp_int 5),
        [(Pat_tuple [Pat_var (cl "a"); Pat_var (cl "b")],
          Exp_binop (Op_add, Exp_var (cl "a"), Exp_var (cl "b")))]))))] in
  let src13 = "let () = print_int (let f x = (x + 1, x * 2) in match f 5 with (a, b) -> a + b); print_newline ()" in
  run_test "13. pat_tuple fn result f 5 -> (6,10) = 16" prog13 src13;

  (* 14. Pat_tuple: swap via destructuring
       let swap p = match p with (a, b) -> (b, a) in
       let (x, y) = swap (10, 20) in
       print_int (x + y); print_newline () *)
  let prog14 = [Decl_expr (print_int_nl
    (Exp_let (cl "swap",
      Exp_fun (cl "p",
        Exp_match (Exp_var (cl "p"),
          [(Pat_tuple [Pat_var (cl "a"); Pat_var (cl "b")],
            Exp_tuple [Exp_var (cl "b"); Exp_var (cl "a")])])),
      Exp_match (Exp_app (Exp_var (cl "swap"), Exp_tuple [Exp_int 10; Exp_int 20]),
        [(Pat_tuple [Pat_var (cl "x"); Pat_var (cl "y")],
          Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y")))]))))] in
  let src14 = "let () = print_int (let swap p = match p with (a, b) -> (b, a) in match swap (10, 20) with (x, y) -> x + y); print_newline ()" in
  run_test "14. pat_tuple swap (10,20) -> x+y = 30" prog14 src14;

  (* === Summary === *)
  Printf.printf "\n====================================\n";
  Printf.printf "Results: %d passed, %d failed\n" !passed !failed;
  if !failed > 0 then exit 1
