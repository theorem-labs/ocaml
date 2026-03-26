(* source_interp_test.ml - PBT: source interpreter (interpret) vs ocamlc+ocamlrun.
   For each generated program:
   1. Run interpret 10000 prog and extract the output trace as a string
   2. Compile the OCaml source with ocamlc, run with ocamlrun
   3. Compare outputs *)

open Interp_extracted
open Test_common

(* === QCheck generators producing (prog, source) pairs === *)

let gen_test_case : (decl list * string) QCheck.Gen.t =
  let open QCheck.Gen in
  oneof [
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

    (* 23. Nested function application: f (g n) *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)),
          Exp_let (cl "g", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)),
            Exp_app (Exp_var (cl "f"), Exp_app (Exp_var (cl "g"), Exp_int n))))))] in
      let src = Printf.sprintf "let () = print_int (let f x = x + 1 in let g x = x * 2 in f (g %d)); print_newline ()" n in
      (prog, src)) (int_range 0 19));

    (* 24. Curried function (make_adder) *)
    (map2 (fun n m ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "make_adder",
          Exp_fun (cl "n", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "n")))),
          Exp_app (Exp_app (Exp_var (cl "make_adder"), Exp_int n), Exp_int m))))] in
      let src = Printf.sprintf "let () = print_int (let make_adder n x = n + x in make_adder %d %d); print_newline ()" n m in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 25. Sequential print of two ints *)
    (map2 (fun a b ->
      let prog = [Decl_expr
        (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int a),
          Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int b),
            Exp_app (Exp_var (cl "print_newline"), Exp_unit))))] in
      let src = Printf.sprintf "let () = print_int %d; print_int %d; print_newline ()" a b in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 26. Variable shadowing *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int b),
            Exp_var (cl "x")))))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in let x = x + %d in x); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 27. Partial application *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "add",
          Exp_fun (cl "x", Exp_fun (cl "y", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y")))),
          Exp_let (cl "inc", Exp_app (Exp_var (cl "add"), Exp_int 1),
            Exp_app (Exp_var (cl "inc"), Exp_int n)))))] in
      let src = Printf.sprintf "let () = print_int (let add x y = x + y in let inc = add 1 in inc %d); print_newline ()" n in
      (prog, src)) (int_range 0 49));

    (* 28. Top-level Decl_let followed by Decl_expr using it *)
    (map (fun n ->
      let prog = [
        Decl_let (cl "x", Exp_int n);
        Decl_expr (print_int_nl (Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1)))] in
      let src = Printf.sprintf "let x = %d\nlet () = print_int (x + 1); print_newline ()" n in
      (prog, src)) (int_range 0 99));

    (* 29. Multiple top-level Decl_let declarations *)
    (map2 (fun a b ->
      let prog = [
        Decl_let (cl "x", Exp_int a);
        Decl_let (cl "y", Exp_int b);
        Decl_expr (print_int_nl (Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y"))))] in
      let src = Printf.sprintf "let x = %d\nlet y = %d\nlet () = print_int (x + y); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* 30. Closure: function captures free variable *)
    (map2 (fun x y ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int x,
          Exp_let (cl "f", Exp_fun (cl "y", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y"))),
            Exp_app (Exp_var (cl "f"), Exp_int y)))))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in let f y = x + y in f %d); print_newline ()" x y in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* 31. Higher-order function: apply f x = f x *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "apply",
          Exp_fun (cl "f", Exp_fun (cl "x", Exp_app (Exp_var (cl "f"), Exp_var (cl "x")))),
          Exp_app (Exp_app (Exp_var (cl "apply"),
            Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1))),
            Exp_int n))))] in
      let src = Printf.sprintf "let () = print_int (let apply f x = f x in apply (fun x -> x + 1) %d); print_newline ()" n in
      (prog, src)) (int_range 0 49));

    (* 32. Division + modulo *)
    (map2 (fun a b ->
      let a = a + 1 in let b = b + 1 in
      let prog = [Decl_expr (print_int_nl
        (Exp_binop (Op_add,
          Exp_binop (Op_div, Exp_int a, Exp_int b),
          Exp_binop (Op_mod, Exp_int a, Exp_int b))))] in
      let src = Printf.sprintf "let () = print_int (%d / %d + %d mod %d); print_newline ()" a b a b in
      (prog, src)) (int_range 0 499) (int_range 0 19));

    (* --- New generators for source interpreter coverage --- *)

    (* 33. Match on bool patterns *)
    (map (fun b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_bool b,
          [(Pat_bool true, Exp_int 1);
           (Pat_bool false, Exp_int 0)])))] in
      let src = Printf.sprintf "let () = print_int (match %s with true -> 1 | false -> 0); print_newline ()" (if b then "true" else "false") in
      (prog, src)) QCheck.Gen.bool);

    (* 34. Match on unit *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_unit,
          [(Pat_unit, Exp_int n)])))] in
      let src = Printf.sprintf "let () = print_int (match () with () -> %d); print_newline ()" n in
      (prog, src)) (int_range 0 99));

    (* 35. Tuple destructuring via Pat_tuple *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_tuple [Exp_int a; Exp_int b],
          [(Pat_tuple [Pat_var (cl "x"); Pat_var (cl "y")],
            Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y")))])))] in
      let src = Printf.sprintf "let () = print_int (match (%d, %d) with (x, y) -> x + y); print_newline ()" a b in
      (prog, src)) (int_range 0 49) (int_range 0 49));

    (* 36. 3-tuple destructuring *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_match (Exp_tuple [Exp_int a; Exp_int b; Exp_int c],
          [(Pat_tuple [Pat_var (cl "a"); Pat_var (cl "b"); Pat_var (cl "c")],
            Exp_binop (Op_add, Exp_var (cl "a"),
              Exp_binop (Op_add, Exp_var (cl "b"), Exp_var (cl "c"))))])))] in
      let src = Printf.sprintf "let () = print_int (match (%d, %d, %d) with (a, b, c) -> a + b + c); print_newline ()" a b c in
      (prog, src)) (int_range 0 30) (int_range 0 30) (int_range 0 30));

    (* 37. Closure capturing two free variables *)
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

    (* 38. Variable shadowing inside closure *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int a,
          Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2)),
            Exp_binop (Op_add, Exp_var (cl "x"),
              Exp_app (Exp_var (cl "f"), Exp_int b))))))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in let f x = x * 2 in x + f %d); print_newline ()" a b in
      (prog, src)) (int_range 0 19) (int_range 0 19));

    (* 39. Three-argument function *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "f",
          Exp_fun (cl "x", Exp_fun (cl "y", Exp_fun (cl "z",
            Exp_binop (Op_add, Exp_var (cl "x"),
              Exp_binop (Op_add, Exp_var (cl "y"), Exp_var (cl "z")))))),
          Exp_app (Exp_app (Exp_app (Exp_var (cl "f"), Exp_int a), Exp_int b), Exp_int c))))] in
      let src = Printf.sprintf "let () = print_int (let f x y z = x + y + z in f %d %d %d); print_newline ()" a b c in
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 40. Three-argument partial application *)
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

    (* 41. apply_twice: higher-order with closure *)
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

    (* 42. Recursive function with closure capturing free variable *)
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

    (* 43. Nested closures: outer and inner capture *)
    (map3 (fun a b c ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "a", Exp_int a,
          Exp_let (cl "make",
            Exp_fun (cl "b",
              Exp_fun (cl "c",
                Exp_binop (Op_add, Exp_var (cl "a"),
                  Exp_binop (Op_add, Exp_var (cl "b"), Exp_var (cl "c"))))),
            Exp_app (Exp_app (Exp_var (cl "make"), Exp_int b), Exp_int c)))))] in
      let src = Printf.sprintf "let () = print_int (let a = %d in let make b c = a + b + c in make %d %d); print_newline ()" a b c in
      (prog, src)) (int_range 0 19) (int_range 0 19) (int_range 0 19));

    (* 44. Nested match *)
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

    (* 45. Returned closure: make_adder returns function *)
    (map2 (fun n m ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "make_mul",
          Exp_fun (cl "n", Exp_fun (cl "x", Exp_binop (Op_mul, Exp_var (cl "n"), Exp_var (cl "x")))),
          Exp_let (cl "double", Exp_app (Exp_var (cl "make_mul"), Exp_int n),
            Exp_app (Exp_var (cl "double"), Exp_int m)))))] in
      let src = Printf.sprintf "let () = print_int (let make_mul n x = n * x in let double = make_mul %d in double %d); print_newline ()" n m in
      (prog, src)) (int_range 1 9) (int_range 0 19));

    (* 46. Op_neq explicit test *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_if (Exp_binop (Op_neq, Exp_int a, Exp_int b), Exp_int 1, Exp_int 0)))] in
      let src = Printf.sprintf "let () = print_int (if %d <> %d then 1 else 0); print_newline ()" a b in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 47. All six comparison operators combined *)
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

    (* 48. Function returning tuple, then destructuring *)
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

    (* 49. Triple variable shadowing *)
    (map (fun n ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "x", Exp_int n,
          Exp_let (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_int 1),
            Exp_let (cl "x", Exp_binop (Op_mul, Exp_var (cl "x"), Exp_int 2),
              Exp_var (cl "x"))))))] in
      let src = Printf.sprintf "let () = print_int (let x = %d in let x = x + 1 in let x = x * 2 in x); print_newline ()" n in
      (prog, src)) (int_range 0 19));

    (* 50. Swap via tuple destructuring *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "swap",
          Exp_fun (cl "p",
            Exp_match (Exp_var (cl "p"),
              [(Pat_tuple [Pat_var (cl "a"); Pat_var (cl "b")],
                Exp_tuple [Exp_var (cl "b"); Exp_var (cl "a")])])),
          Exp_match (Exp_app (Exp_var (cl "swap"), Exp_tuple [Exp_int a; Exp_int b]),
            [(Pat_tuple [Pat_var (cl "x"); Pat_var (cl "y")],
              Exp_binop (Op_add, Exp_var (cl "x"),
                Exp_binop (Op_mul, Exp_int 100, Exp_var (cl "y"))))]))))] in
      let src = Printf.sprintf "let () = print_int (let swap p = match p with (a, b) -> (b, a) in match swap (%d, %d) with (x, y) -> x + 100 * y); print_newline ()" a b in
      (prog, src)) (int_range 0 9) (int_range 0 9));

    (* 51. Seq with side-effect ordering *)
    (map3 (fun a b c ->
      let prog = [Decl_expr
        (Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int a),
          Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int b),
            Exp_seq (Exp_app (Exp_var (cl "print_int"), Exp_int c),
              Exp_app (Exp_var (cl "print_newline"), Exp_unit)))))] in
      let src = Printf.sprintf "let () = print_int %d; print_int %d; print_int %d; print_newline ()" a b c in
      (prog, src)) (int_range 0 9) (int_range 0 9) (int_range 0 9));

    (* 52. Closure over closure: nested function-returning-function *)
    (map2 (fun a b ->
      let prog = [Decl_expr (print_int_nl
        (Exp_let (cl "a", Exp_int a,
          Exp_let (cl "make",
            Exp_fun (cl "b",
              Exp_fun (cl "x",
                Exp_binop (Op_add, Exp_var (cl "a"),
                  Exp_binop (Op_mul, Exp_var (cl "b"), Exp_var (cl "x"))))),
            Exp_let (cl "f", Exp_app (Exp_var (cl "make"), Exp_int b),
              Exp_app (Exp_var (cl "f"), Exp_int 3))))))] in
      let src = Printf.sprintf "let () = print_int (let a = %d in let make b x = a + b * x in let f = make %d in f 3); print_newline ()" a b in
      (prog, src)) (int_range 0 9) (int_range 0 9));
  ]

(* === Test === *)

let print_test_case (_prog, src) = src

let source_interp_vs_ocamlc_test =
  QCheck.Test.make ~name:"source interp vs ocamlc" ~count:500
    (QCheck.make gen_test_case ~print:print_test_case)
    (fun (prog, source) ->
       with_temp_dir (fun dir ->
         let our_result = run_source_interp prog in
         match compile_and_run_ocamlc dir source with
         | None -> true  (* ocamlc failed to compile, skip *)
         | Some expected ->
           (match our_result with
            | Interp_ok ours -> ours = expected
            | Interp_err _msg -> false)))

let () =
  exit (QCheck_base_runner.run_tests ~verbose:true [source_interp_vs_ocamlc_test])
