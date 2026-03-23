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
  ]

let print_test_case (_prog, src) = src

let bytecode_equiv_test =
  QCheck.Test.make ~name:"bytecode equivalence: our compiler vs ocamlc" ~count:100
    (QCheck.make gen_test_case ~print:print_test_case)
    (fun (prog, source) ->
       with_temp_dir (fun dir ->
         let our_result = run_our_compiler prog in
         match compile_ocamlc dir source with
         | None -> true  (* skip *)
         | Some exe ->
           let ocamlc_result = run_ocamlc_bytecode exe in
           (match our_result, ocamlc_result with
            | Ok ours, Ok theirs -> ours = theirs
            | _ -> false)))

let () =
  exit (QCheck_base_runner.run_tests ~verbose:true [bytecode_equiv_test])
