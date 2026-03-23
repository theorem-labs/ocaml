(* source_interp_test.ml - PBT: source interpreter vs ocamlrun. *)

open Interp_extracted
open Test_common

let run_source_interp prog =
  let b = interpret 100000 prog in
  events_to_string b.trace

let generators = [|
  (fun r ->
    let n = Random.State.int r 200 - 100 in
    let prog = [Decl_expr (print_int_nl (Exp_int n))] in
    let src = Printf.sprintf "let () = print_int (%d); print_newline ()" n in
    (prog, src));
  (fun r ->
    let a = Random.State.int r 100 in let b = Random.State.int r 100 + 1 in
    let prog = [Decl_expr (print_int_nl (Exp_binop (Op_add, Exp_int a, Exp_int b)))] in
    let src = Printf.sprintf "let () = print_int (%d + %d); print_newline ()" a b in
    (prog, src));
  (fun r ->
    let a = Random.State.int r 100 in let b = Random.State.int r 100 in
    let prog = [Decl_expr (print_int_nl (Exp_binop (Op_sub, Exp_int a, Exp_int b)))] in
    let src = Printf.sprintf "let () = print_int (%d - %d); print_newline ()" a b in
    (prog, src));
  (fun r ->
    let a = Random.State.int r 50 in let b = Random.State.int r 50 in
    let prog = [Decl_expr (print_int_nl (Exp_binop (Op_mul, Exp_int a, Exp_int b)))] in
    let src = Printf.sprintf "let () = print_int (%d * %d); print_newline ()" a b in
    (prog, src));
  (fun r ->
    let n = Random.State.int r 100 in let t = Random.State.int r 100 in
    let prog = [Decl_expr (print_int_nl
      (Exp_if (Exp_binop (Op_gt, Exp_int n, Exp_int t), Exp_int 1, Exp_int 0)))] in
    let src = Printf.sprintf "let () = print_int (if %d > %d then 1 else 0); print_newline ()" n t in
    (prog, src));
  (fun r ->
    let a = Random.State.int r 20 in let b = Random.State.int r 20 in
    let prog = [Decl_expr (print_int_nl
      (Exp_let (cl "x", Exp_int a,
        Exp_let (cl "y", Exp_int b,
          Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "y"))))))] in
    let src = Printf.sprintf "let () = print_int (let x = %d in let y = %d in x + y); print_newline ()" a b in
    (prog, src));
  (fun r ->
    let n = Random.State.int r 50 in
    let prog = [Decl_expr (print_int_nl
      (Exp_let (cl "f", Exp_fun (cl "x", Exp_binop (Op_add, Exp_var (cl "x"), Exp_var (cl "x"))),
        Exp_app (Exp_var (cl "f"), Exp_int n))))] in
    let src = Printf.sprintf "let () = print_int (let f x = x + x in f %d); print_newline ()" n in
    (prog, src));
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
  (fun r ->
    let a = Random.State.int r 50 in let b = Random.State.int r 50 in
    let prog = [Decl_expr (print_int_nl
      (Exp_let (cl "p", Exp_tuple [Exp_int a; Exp_int b],
        Exp_binop (Op_add,
          Exp_app (Exp_var (cl "fst"), Exp_var (cl "p")),
          Exp_app (Exp_var (cl "snd"), Exp_var (cl "p"))))))] in
    let src = Printf.sprintf "let () = print_int (let p = (%d, %d) in fst p + snd p); print_newline ()" a b in
    (prog, src));
  (fun r ->
    let a = Random.State.int r 100 in
    let prog = [Decl_expr (print_int_nl (Exp_unop (Op_neg, Exp_int a)))] in
    let src = Printf.sprintf "let () = print_int (- %d); print_newline ()" a in
    (prog, src));
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
  (fun r ->
    let a = Random.State.int r 30 in let b = Random.State.int r 30 in
    let prog = [Decl_expr (print_int_nl
      (Exp_let (cl "f",
        Exp_fun (cl "x", Exp_fun (cl "y",
          Exp_binop (Op_add, Exp_binop (Op_mul, Exp_var (cl "x"), Exp_var (cl "y")), Exp_int 1))),
        Exp_app (Exp_app (Exp_var (cl "f"), Exp_int a), Exp_int b))))] in
    let src = Printf.sprintf "let () = print_int (let f x y = x * y + 1 in f %d %d); print_newline ()" a b in
    (prog, src));
|]

let () =
  let num = try int_of_string Sys.argv.(1) with _ -> 50 in
  let seed = try int_of_string Sys.argv.(2) with _ -> 42 in
  let rng = Random.State.make [| seed |] in
  Printf.printf "Source interp PBT: %d tests (seed=%d)\n\n%!" num seed;
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
        (try
          let ours = run_source_interp prog in
          Printf.printf "  ours:     %S\n%!" ours;
          if ours = expected then (Printf.printf "  PASS\n%!"; incr pass)
          else (Printf.printf "  FAIL: output mismatch\n%!"; incr fail)
        with e ->
          Printf.printf "  FAIL: %s\n%!" (Printexc.to_string e); incr fail)
    done);
  Printf.printf "\n=== Source Interp Results: %d pass, %d fail, %d skip ===\n" !pass !fail !skip;
  if !fail > 0 then exit 1
