(* rocq_source_test.ml - Tests our compiler/interpreter against fragments
   inspired by the Rocq-extracted OCaml code (interp_extracted.ml).

   The extracted code contains many pure functions (negb, eqb, fst, snd, etc.)
   that serve as good test cases for our compiler and source interpreter.
   We hand-craft AST representations of these functions and test them through
   all three paths:
     1. Our compiler (compile_program + bytecode interpreter)
     2. Source interpreter (interpret)
     3. Reference (ocamlc + ocamlrun)
   and assert all three agree. *)

open Interp_extracted
open Test_common

(* === Test runner === *)

let passed = ref 0
let failed = ref 0

let run_test name prog source =
  Printf.printf "  %-55s " name;
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

(* === Test cases inspired by Rocq-extracted code === *)

let () =
  Printf.printf "Rocq-extracted source tests\n";
  Printf.printf "====================================\n\n";

  (* ------------------------------------------------------------------
     Test 1: negb (from interp_extracted.ml line 4)
     Extracted Rocq:
       let negb = function true -> false | false -> true
     We use Exp_function which compiles to fun $arg -> match $arg with ...
     ------------------------------------------------------------------ *)
  let negb_fn = Exp_function [
    (Pat_bool true, Exp_bool false);
    (Pat_bool false, Exp_bool true)
  ] in
  let prog1 = [
    Decl_let (cl "negb", negb_fn);
    Decl_expr (print_int_nl
      (Exp_if (Exp_app (Exp_var (cl "negb"), Exp_bool true),
               Exp_int 1,
               Exp_int 0)))
  ] in
  let src1 = "let negb = function true -> false | false -> true\n\
              let () = print_int (if negb true then 1 else 0); print_newline ()" in
  run_test "1. negb true = false (Exp_function + Pat_bool)" prog1 src1;

  (* Test 1b: negb false = true *)
  let prog1b = [
    Decl_let (cl "negb", negb_fn);
    Decl_expr (print_int_nl
      (Exp_if (Exp_app (Exp_var (cl "negb"), Exp_bool false),
               Exp_int 1,
               Exp_int 0)))
  ] in
  let src1b = "let negb = function true -> false | false -> true\n\
               let () = print_int (if negb false then 1 else 0); print_newline ()" in
  run_test "1b. negb false = true (Exp_function + Pat_bool)" prog1b src1b;

  (* ------------------------------------------------------------------
     Test 3: eqb (from interp_extracted.ml line 53)
     Extracted Rocq:
       let eqb b1 b2 = if b1 then b2 else if b2 then false else true
     Two-arg curried function.
     ------------------------------------------------------------------ *)
  let eqb_fn = Exp_fun (cl "b1", Exp_fun (cl "b2",
    Exp_if (Exp_var (cl "b1"),
            Exp_var (cl "b2"),
            Exp_if (Exp_var (cl "b2"),
                    Exp_bool false,
                    Exp_bool true)))) in

  (* eqb true true = true -> print 1 *)
  let prog3a = [
    Decl_let (cl "eqb", eqb_fn);
    Decl_expr (print_int_nl
      (Exp_if (Exp_app (Exp_app (Exp_var (cl "eqb"), Exp_bool true), Exp_bool true),
               Exp_int 1,
               Exp_int 0)))
  ] in
  let src3a = "let eqb b1 b2 = if b1 then b2 else if b2 then false else true\n\
               let () = print_int (if eqb true true then 1 else 0); print_newline ()" in
  run_test "3a. eqb true true = true" prog3a src3a;

  (* eqb true false = false -> print 0 *)
  let prog3b = [
    Decl_let (cl "eqb", eqb_fn);
    Decl_expr (print_int_nl
      (Exp_if (Exp_app (Exp_app (Exp_var (cl "eqb"), Exp_bool true), Exp_bool false),
               Exp_int 1,
               Exp_int 0)))
  ] in
  let src3b = "let eqb b1 b2 = if b1 then b2 else if b2 then false else true\n\
               let () = print_int (if eqb true false then 1 else 0); print_newline ()" in
  run_test "3b. eqb true false = false" prog3b src3b;

  (* eqb false false = true -> print 1 *)
  let prog3c = [
    Decl_let (cl "eqb", eqb_fn);
    Decl_expr (print_int_nl
      (Exp_if (Exp_app (Exp_app (Exp_var (cl "eqb"), Exp_bool false), Exp_bool false),
               Exp_int 1,
               Exp_int 0)))
  ] in
  let src3c = "let eqb b1 b2 = if b1 then b2 else if b2 then false else true\n\
               let () = print_int (if eqb false false then 1 else 0); print_newline ()" in
  run_test "3c. eqb false false = true" prog3c src3c;

  (* eqb false true = false -> print 0 *)
  let prog3d = [
    Decl_let (cl "eqb", eqb_fn);
    Decl_expr (print_int_nl
      (Exp_if (Exp_app (Exp_app (Exp_var (cl "eqb"), Exp_bool false), Exp_bool true),
               Exp_int 1,
               Exp_int 0)))
  ] in
  let src3d = "let eqb b1 b2 = if b1 then b2 else if b2 then false else true\n\
               let () = print_int (if eqb false true then 1 else 0); print_newline ()" in
  run_test "3d. eqb false true = false" prog3d src3d;

  (* ------------------------------------------------------------------
     Test 4: Record construction and field access
     type point = { x : int; y : int }
     let p = { x = 10; y = 20 }
     let () = print_int p.x; print_newline ()

     The compiler uses field_env (populated by Decl_type/Td_record)
     to map field names to their GETFIELD indices.
     ------------------------------------------------------------------ *)
  let prog4 = [
    Decl_type (cl "point", [],
      Td_record [(cl "x", Ty_int); (cl "y", Ty_int)]);
    Decl_let (cl "p",
      Exp_record [(cl "x", Exp_int 10); (cl "y", Exp_int 20)]);
    Decl_expr (print_int_nl
      (Exp_field (Exp_var (cl "p"), cl "x")))
  ] in
  let src4 = "type point = { x : int; y : int }\n\
              let p = { x = 10; y = 20 }\n\
              let () = print_int p.x; print_newline ()" in
  run_test "4. record { x=10; y=20 }.x = 10" prog4 src4;

  (* ------------------------------------------------------------------
     Test 5: fst and snd (from interp_extracted.ml lines 8-16)
     Extracted Rocq:
       let fst = function (x, _) -> x
       let snd = function (_, y) -> y

     NOTE: Our compiler's tuple_vars only handles Pat_var in tuple
     sub-patterns (not Pat_wild). So we use dummy variable names
     instead of _ in the AST. The OCaml source uses _ for ocamlc.
     ------------------------------------------------------------------ *)
  let fst_fn = Exp_function [
    (Pat_tuple [Pat_var (cl "x"); Pat_var (cl "_dummy")], Exp_var (cl "x"))
  ] in
  let snd_fn = Exp_function [
    (Pat_tuple [Pat_var (cl "_dummy"); Pat_var (cl "y")], Exp_var (cl "y"))
  ] in

  (* fst (3, 7) = 3 *)
  let prog5a = [
    Decl_let (cl "fst0", fst_fn);
    Decl_expr (print_int_nl
      (Exp_app (Exp_var (cl "fst0"),
                Exp_tuple [Exp_int 3; Exp_int 7])))
  ] in
  let src5a = "let fst0 = function (x, _dummy) -> x\n\
               let () = print_int (fst0 (3, 7)); print_newline ()" in
  run_test "5a. fst (3, 7) = 3 (Exp_function + Pat_tuple)" prog5a src5a;

  (* snd (3, 7) = 7 *)
  let prog5b = [
    Decl_let (cl "snd0", snd_fn);
    Decl_expr (print_int_nl
      (Exp_app (Exp_var (cl "snd0"),
                Exp_tuple [Exp_int 3; Exp_int 7])))
  ] in
  let src5b = "let snd0 = function (_dummy, y) -> y\n\
               let () = print_int (snd0 (3, 7)); print_newline ()" in
  run_test "5b. snd (3, 7) = 7 (Exp_function + Pat_tuple)" prog5b src5b;

  (* fst and snd combined: fst (3, 7) + snd (3, 7) = 10 *)
  let prog5c = [
    Decl_let (cl "fst0", fst_fn);
    Decl_let (cl "snd0", snd_fn);
    Decl_expr (print_int_nl
      (Exp_binop (Op_add,
        Exp_app (Exp_var (cl "fst0"), Exp_tuple [Exp_int 3; Exp_int 7]),
        Exp_app (Exp_var (cl "snd0"), Exp_tuple [Exp_int 3; Exp_int 7]))))
  ] in
  let src5c = "let fst0 = function (x, _dummy) -> x\n\
               let snd0 = function (_dummy, y) -> y\n\
               let () = print_int (fst0 (3, 7) + snd0 (3, 7)); print_newline ()" in
  run_test "5c. fst (3,7) + snd (3,7) = 10" prog5c src5c;

  (* ------------------------------------------------------------------
     Test 6: Nested match with function (classify pattern)
     let classify = function 0 -> 100 | 1 -> 200 | _ -> 999
     let () = print_int (classify 0 + classify 1 + classify 5)
     Expected: 100 + 200 + 999 = 1299
     ------------------------------------------------------------------ *)
  let classify_fn = Exp_function [
    (Pat_int 0, Exp_int 100);
    (Pat_int 1, Exp_int 200);
    (Pat_wild, Exp_int 999)
  ] in
  let prog6 = [
    Decl_let (cl "classify", classify_fn);
    Decl_expr (print_int_nl
      (Exp_binop (Op_add,
        Exp_binop (Op_add,
          Exp_app (Exp_var (cl "classify"), Exp_int 0),
          Exp_app (Exp_var (cl "classify"), Exp_int 1)),
        Exp_app (Exp_var (cl "classify"), Exp_int 5))))
  ] in
  let src6 = "let classify = function 0 -> 100 | 1 -> 200 | _ -> 999\n\
              let () = print_int (classify 0 + classify 1 + classify 5); print_newline ()" in
  run_test "6. classify 0 + 1 + 5 = 1299 (Exp_function + Pat_int)" prog6 src6;

  (* ------------------------------------------------------------------
     Test 6b: Deeper classify with computation in arms
     let classify = function
       | 0 -> 100
       | 1 -> 200
       | n -> n * 10
     classify 0 + classify 1 + classify 5 = 100 + 200 + 50 = 350
     Uses Pat_var in the wildcard arm to bind and use the matched value.
     ------------------------------------------------------------------ *)
  let classify2_fn = Exp_function [
    (Pat_int 0, Exp_int 100);
    (Pat_int 1, Exp_int 200);
    (Pat_var (cl "n"), Exp_binop (Op_mul, Exp_var (cl "n"), Exp_int 10))
  ] in
  let prog6b = [
    Decl_let (cl "classify2", classify2_fn);
    Decl_expr (print_int_nl
      (Exp_binop (Op_add,
        Exp_binop (Op_add,
          Exp_app (Exp_var (cl "classify2"), Exp_int 0),
          Exp_app (Exp_var (cl "classify2"), Exp_int 1)),
        Exp_app (Exp_var (cl "classify2"), Exp_int 5))))
  ] in
  let src6b = "let classify2 = function 0 -> 100 | 1 -> 200 | n -> n * 10\n\
               let () = print_int (classify2 0 + classify2 1 + classify2 5); print_newline ()" in
  run_test "6b. classify2 with var binding = 350" prog6b src6b;

  (* ------------------------------------------------------------------
     Test 7: Combining negb with eqb - composition of extracted functions
     let negb = function true -> false | false -> true
     let eqb b1 b2 = if b1 then b2 else if b2 then false else true
     eqb (negb true) (negb false) = eqb false true = false -> 0
     ------------------------------------------------------------------ *)
  let prog7 = [
    Decl_let (cl "negb", negb_fn);
    Decl_let (cl "eqb", eqb_fn);
    Decl_expr (print_int_nl
      (Exp_if (
        Exp_app (Exp_app (Exp_var (cl "eqb"),
          Exp_app (Exp_var (cl "negb"), Exp_bool true)),
          Exp_app (Exp_var (cl "negb"), Exp_bool false)),
        Exp_int 1,
        Exp_int 0)))
  ] in
  let src7 = "let negb = function true -> false | false -> true\n\
              let eqb b1 b2 = if b1 then b2 else if b2 then false else true\n\
              let () = print_int (if eqb (negb true) (negb false) then 1 else 0); print_newline ()" in
  run_test "7. eqb (negb true) (negb false) = false" prog7 src7;

  (* ------------------------------------------------------------------
     Test 8: fst/snd with swap - tuple destructure and reconstruct
     let fst0 = function (x, _) -> x
     let snd0 = function (_, y) -> y
     let swap = function (a, b) -> (b, a)
     fst0 (swap (10, 20)) = 20
     ------------------------------------------------------------------ *)
  let swap_fn = Exp_function [
    (Pat_tuple [Pat_var (cl "a"); Pat_var (cl "b")],
     Exp_tuple [Exp_var (cl "b"); Exp_var (cl "a")])
  ] in
  let prog8 = [
    Decl_let (cl "fst0", fst_fn);
    Decl_let (cl "swap", swap_fn);
    Decl_expr (print_int_nl
      (Exp_app (Exp_var (cl "fst0"),
        Exp_app (Exp_var (cl "swap"),
          Exp_tuple [Exp_int 10; Exp_int 20]))))
  ] in
  let src8 = "let fst0 = function (x, _dummy) -> x\n\
              let swap = function (a, b) -> (b, a)\n\
              let () = print_int (fst0 (swap (10, 20))); print_newline ()" in
  run_test "8. fst (swap (10, 20)) = 20" prog8 src8;

  (* ------------------------------------------------------------------
     Test 9: sub (natural number subtraction from extracted code)
     Extracted Rocq: let rec sub = fun n m -> Stdlib.max 0 (n-m)
     We model this with regular integer subtraction guarded by max 0.
     sub 10 3 = 7, sub 3 10 = 0
     We can't directly use Stdlib.max, so we use if-then-else.
     ------------------------------------------------------------------ *)
  let sub_fn = Exp_fun (cl "n", Exp_fun (cl "m",
    Exp_let (cl "r",
      Exp_binop (Op_sub, Exp_var (cl "n"), Exp_var (cl "m")),
      Exp_if (Exp_binop (Op_le, Exp_var (cl "r"), Exp_int 0),
              Exp_int 0,
              Exp_var (cl "r"))))) in
  let prog9 = [
    Decl_let (cl "sub0", sub_fn);
    Decl_expr (print_int_nl
      (Exp_binop (Op_add,
        Exp_app (Exp_app (Exp_var (cl "sub0"), Exp_int 10), Exp_int 3),
        Exp_app (Exp_app (Exp_var (cl "sub0"), Exp_int 3), Exp_int 10))))
  ] in
  let src9 = "let sub0 n m = let r = n - m in if r <= 0 then 0 else r\n\
              let () = print_int (sub0 10 3 + sub0 3 10); print_newline ()" in
  run_test "9. sub 10 3 + sub 3 10 = 7 + 0 = 7" prog9 src9;

  (* ------------------------------------------------------------------
     Test 10: mul (from extracted code line 45)
     Extracted Rocq: let rec mul = ( * )
     Simple multiplication through curried application.
     mul 6 7 = 42
     ------------------------------------------------------------------ *)
  let mul_fn = Exp_fun (cl "a", Exp_fun (cl "b",
    Exp_binop (Op_mul, Exp_var (cl "a"), Exp_var (cl "b")))) in
  let prog10 = [
    Decl_let (cl "mul0", mul_fn);
    Decl_expr (print_int_nl
      (Exp_app (Exp_app (Exp_var (cl "mul0"), Exp_int 6), Exp_int 7)))
  ] in
  let src10 = "let mul0 a b = a * b\n\
               let () = print_int (mul0 6 7); print_newline ()" in
  run_test "10. mul 6 7 = 42" prog10 src10;

  (* ------------------------------------------------------------------
     Test 11: Nat.ltb pattern (from extracted code line 80)
     Extracted Rocq: let ltb n0 m = (<=) (Stdlib.Int.succ n0) m
     We model as: ltb n m = (n + 1) <= m
     ltb 3 5 = true, ltb 5 3 = false, ltb 3 3 = false
     ------------------------------------------------------------------ *)
  let ltb_fn = Exp_fun (cl "n", Exp_fun (cl "m",
    Exp_binop (Op_le,
      Exp_binop (Op_add, Exp_var (cl "n"), Exp_int 1),
      Exp_var (cl "m")))) in
  let prog11 = [
    Decl_let (cl "ltb", ltb_fn);
    Decl_expr (
      Exp_seq (
        (* ltb 3 5 = true -> print 1 *)
        Exp_seq (
          Exp_app (Exp_var (cl "print_int"),
            Exp_if (Exp_app (Exp_app (Exp_var (cl "ltb"), Exp_int 3), Exp_int 5),
                    Exp_int 1, Exp_int 0)),
          (* ltb 5 3 = false -> print 0 *)
          Exp_app (Exp_var (cl "print_int"),
            Exp_if (Exp_app (Exp_app (Exp_var (cl "ltb"), Exp_int 5), Exp_int 3),
                    Exp_int 1, Exp_int 0))),
        (* ltb 3 3 = false -> print 0 + newline *)
        Exp_seq (
          Exp_app (Exp_var (cl "print_int"),
            Exp_if (Exp_app (Exp_app (Exp_var (cl "ltb"), Exp_int 3), Exp_int 3),
                    Exp_int 1, Exp_int 0)),
          Exp_app (Exp_var (cl "print_newline"), Exp_unit))))
  ] in
  let src11 = "let ltb n m = n + 1 <= m\n\
               let () =\n\
               \  print_int (if ltb 3 5 then 1 else 0);\n\
               \  print_int (if ltb 5 3 then 1 else 0);\n\
               \  print_int (if ltb 3 3 then 1 else 0);\n\
               \  print_newline ()" in
  run_test "11. ltb: 3<5=t, 5<3=f, 3<3=f -> 100" prog11 src11;

  (* ------------------------------------------------------------------
     Test 12: Exp_function with multiple Pat_int and Pat_wild combined
     Simulates a dispatch table like opcode handlers in the extracted code.
     let dispatch = function
       | 0 -> 1000
       | 1 -> 2000
       | 2 -> 3000
       | _ -> 0
     dispatch 0 + dispatch 1 + dispatch 2 + dispatch 99 = 6000
     ------------------------------------------------------------------ *)
  let dispatch_fn = Exp_function [
    (Pat_int 0, Exp_int 1000);
    (Pat_int 1, Exp_int 2000);
    (Pat_int 2, Exp_int 3000);
    (Pat_wild, Exp_int 0)
  ] in
  let prog12 = [
    Decl_let (cl "dispatch", dispatch_fn);
    Decl_expr (print_int_nl
      (Exp_binop (Op_add,
        Exp_binop (Op_add,
          Exp_binop (Op_add,
            Exp_app (Exp_var (cl "dispatch"), Exp_int 0),
            Exp_app (Exp_var (cl "dispatch"), Exp_int 1)),
          Exp_app (Exp_var (cl "dispatch"), Exp_int 2)),
        Exp_app (Exp_var (cl "dispatch"), Exp_int 99))))
  ] in
  let src12 = "let dispatch = function 0 -> 1000 | 1 -> 2000 | 2 -> 3000 | _ -> 0\n\
               let () = print_int (dispatch 0 + dispatch 1 + dispatch 2 + dispatch 99); print_newline ()" in
  run_test "12. dispatch table 0+1+2+99 = 6000" prog12 src12;

  (* ------------------------------------------------------------------
     Test 13: Combining tuple destructure with function composition
     Inspired by the divmod pattern in extracted code.
     let mk_pair a b = (a, b)
     let add_pair = function (a, b) -> a + b
     add_pair (mk_pair 17 25) = 42
     ------------------------------------------------------------------ *)
  let mk_pair_fn = Exp_fun (cl "a", Exp_fun (cl "b",
    Exp_tuple [Exp_var (cl "a"); Exp_var (cl "b")])) in
  let add_pair_fn = Exp_function [
    (Pat_tuple [Pat_var (cl "a"); Pat_var (cl "b")],
     Exp_binop (Op_add, Exp_var (cl "a"), Exp_var (cl "b")))
  ] in
  let prog13 = [
    Decl_let (cl "mk_pair", mk_pair_fn);
    Decl_let (cl "add_pair", add_pair_fn);
    Decl_expr (print_int_nl
      (Exp_app (Exp_var (cl "add_pair"),
        Exp_app (Exp_app (Exp_var (cl "mk_pair"), Exp_int 17), Exp_int 25))))
  ] in
  let src13 = "let mk_pair a b = (a, b)\n\
               let add_pair = function (a, b) -> a + b\n\
               let () = print_int (add_pair (mk_pair 17 25)); print_newline ()" in
  run_test "13. add_pair (mk_pair 17 25) = 42" prog13 src13;

  (* ------------------------------------------------------------------
     Test 14: Multi-field record access (exercises field_env)
     type point3d = { x : int; y : int; z : int }
     let p = { x = 10; y = 20; z = 30 }
     let () = print_int (p.x + p.y + p.z); print_newline ()
     Expected: 60

     The Decl_type with Td_record populates field_env so that
     field_lookup maps x->0, y->1, z->2.  All three GETFIELD
     indices are exercised.
     ------------------------------------------------------------------ *)
  let prog14 = [
    Decl_type (cl "point3d", [],
      Td_record [(cl "x", Ty_int); (cl "y", Ty_int); (cl "z", Ty_int)]);
    Decl_let (cl "p",
      Exp_record [(cl "x", Exp_int 10); (cl "y", Exp_int 20); (cl "z", Exp_int 30)]);
    Decl_expr (print_int_nl
      (Exp_binop (Op_add,
        Exp_binop (Op_add,
          Exp_field (Exp_var (cl "p"), cl "x"),
          Exp_field (Exp_var (cl "p"), cl "y")),
        Exp_field (Exp_var (cl "p"), cl "z"))))
  ] in
  let src14 = "type point3d = { x : int; y : int; z : int }\n\
               let p = { x = 10; y = 20; z = 30 }\n\
               let () = print_int (p.x + p.y + p.z); print_newline ()" in
  run_test "14. record {x=10;y=20;z=30} .x+.y+.z = 60 (field_env)" prog14 src14;

  (* ------------------------------------------------------------------
     Test 15: Large record (5 fields, simulating state)
     type state = { a : int; b : int; c : int; d : int; e : int }
     let s = { a = 1; b = 2; c = 3; d = 4; e = 5 }
     let () = print_int (s.a + s.b + s.c + s.d + s.e); print_newline ()
     Expected: 15

     Tests MAKEBLOCK for >3 fields AND field access at indices 0-4.
     ------------------------------------------------------------------ *)
  let prog15 = [
    Decl_type (cl "state", [],
      Td_record [(cl "a", Ty_int); (cl "b", Ty_int); (cl "c", Ty_int);
                  (cl "d", Ty_int); (cl "e", Ty_int)]);
    Decl_let (cl "s",
      Exp_record [(cl "a", Exp_int 1); (cl "b", Exp_int 2); (cl "c", Exp_int 3);
                   (cl "d", Exp_int 4); (cl "e", Exp_int 5)]);
    Decl_expr (print_int_nl
      (Exp_binop (Op_add,
        Exp_binop (Op_add,
          Exp_binop (Op_add,
            Exp_binop (Op_add,
              Exp_field (Exp_var (cl "s"), cl "a"),
              Exp_field (Exp_var (cl "s"), cl "b")),
            Exp_field (Exp_var (cl "s"), cl "c")),
          Exp_field (Exp_var (cl "s"), cl "d")),
        Exp_field (Exp_var (cl "s"), cl "e"))))
  ] in
  let src15 = "type state = { a : int; b : int; c : int; d : int; e : int }\n\
               let s = { a = 1; b = 2; c = 3; d = 4; e = 5 }\n\
               let () = print_int (s.a + s.b + s.c + s.d + s.e); print_newline ()" in
  run_test "15. 5-field record .a+.b+.c+.d+.e = 15 (large MAKEBLOCK)" prog15 src15;

  (* ------------------------------------------------------------------
     Test 16: Record update pattern (cross-field reads)
     type pair = { fst : int; snd : int }
     let p = { fst = 10; snd = 20 }
     let q = { fst = p.snd; snd = p.fst }
     let () = print_int (q.fst + q.snd); print_newline ()
     Expected: 30

     Reads both fields of p, constructs a new record q with swapped
     values, then reads both fields of q.
     ------------------------------------------------------------------ *)
  let prog16 = [
    Decl_type (cl "pair", [],
      Td_record [(cl "fst", Ty_int); (cl "snd", Ty_int)]);
    Decl_let (cl "p",
      Exp_record [(cl "fst", Exp_int 10); (cl "snd", Exp_int 20)]);
    Decl_let (cl "q",
      Exp_record [(cl "fst", Exp_field (Exp_var (cl "p"), cl "snd"));
                   (cl "snd", Exp_field (Exp_var (cl "p"), cl "fst"))]);
    Decl_expr (print_int_nl
      (Exp_binop (Op_add,
        Exp_field (Exp_var (cl "q"), cl "fst"),
        Exp_field (Exp_var (cl "q"), cl "snd"))))
  ] in
  let src16 = "type pair = { fst : int; snd : int }\n\
               let p = { fst = 10; snd = 20 }\n\
               let q = { fst = p.snd; snd = p.fst }\n\
               let () = print_int (q.fst + q.snd); print_newline ()" in
  run_test "16. record update: swap fields, q.fst+q.snd = 30" prog16 src16;

  (* ------------------------------------------------------------------
     Test 17: Large tuple (4 elements)
     let t = (1, 2, 3, 4)
     let () = print_int 42; print_newline ()
     Expected: 42

     Verifies that a 4-element tuple can be constructed without
     crashing (tests MAKEBLOCK with n=4).  We just print 42 to
     confirm the program runs to completion.  We compare against
     ocamlc for consistency.
     ------------------------------------------------------------------ *)
  let prog17 = [
    Decl_let (cl "t",
      Exp_tuple [Exp_int 1; Exp_int 2; Exp_int 3; Exp_int 4]);
    Decl_expr (print_int_nl (Exp_int 42))
  ] in
  let src17 = "let t = (1, 2, 3, 4)\n\
               let () = print_int 42; print_newline ()" in
  run_test "17. large tuple (1,2,3,4) constructs OK" prog17 src17;

  (* ------------------------------------------------------------------
     Test 18: 9-field record (simulating bytecode state)
     type state = { pc : int; accu : int; f3 : int; f4 : int; f5 : int;
                    f6 : int; f7 : int; f8 : int; f9 : int }
     let s = { pc = 0; accu = 42; f3 = 1; f4 = 2; f5 = 3;
               f6 = 4; f7 = 5; f8 = 6; f9 = 7 }
     let () = print_int (s.pc + s.accu + s.f9); print_newline ()
     Expected: 0 + 42 + 7 = 49

     Exercises MAKEBLOCK with 9 fields and GETFIELD at indices 0, 1,
     and 8.  Simulates the extracted bytecode interpreter's state
     record (interp_extracted.ml lines 1724-1726).
     ------------------------------------------------------------------ *)
  let prog18 = [
    Decl_type (cl "state9", [],
      Td_record [(cl "pc", Ty_int); (cl "accu", Ty_int);
                  (cl "f3", Ty_int); (cl "f4", Ty_int); (cl "f5", Ty_int);
                  (cl "f6", Ty_int); (cl "f7", Ty_int); (cl "f8", Ty_int);
                  (cl "f9", Ty_int)]);
    Decl_let (cl "s",
      Exp_record [(cl "pc", Exp_int 0); (cl "accu", Exp_int 42);
                   (cl "f3", Exp_int 1); (cl "f4", Exp_int 2); (cl "f5", Exp_int 3);
                   (cl "f6", Exp_int 4); (cl "f7", Exp_int 5); (cl "f8", Exp_int 6);
                   (cl "f9", Exp_int 7)]);
    Decl_expr (print_int_nl
      (Exp_binop (Op_add,
        Exp_binop (Op_add,
          Exp_field (Exp_var (cl "s"), cl "pc"),
          Exp_field (Exp_var (cl "s"), cl "accu")),
        Exp_field (Exp_var (cl "s"), cl "f9"))))
  ] in
  let src18 = "type state9 = { pc : int; accu : int; f3 : int; f4 : int; f5 : int;\n\
               \               f6 : int; f7 : int; f8 : int; f9 : int }\n\
               let s = { pc = 0; accu = 42; f3 = 1; f4 = 2; f5 = 3;\n\
               \         f6 = 4; f7 = 5; f8 = 6; f9 = 7 }\n\
               let () = print_int (s.pc + s.accu + s.f9); print_newline ()" in
  run_test "18. 9-field record (state sim) .pc+.accu+.f9 = 49" prog18 src18;

  (* ------------------------------------------------------------------
     Test 19: Function using record (simulating set_accu)
     type state = { pc : int; accu : int; extra : int }
     let set_accu s v = { pc = s.pc; accu = v; extra = s.extra }
     let s = { pc = 10; accu = 0; extra = 99 }
     let s2 = set_accu s 42
     let () = print_int (s2.pc + s2.accu + s2.extra); print_newline ()
     Expected: 10 + 42 + 99 = 151

     Tests record construction from field access expressions inside a
     function.  Simulates the extracted set_accu pattern
     (interp_extracted.ml lines 1741-1744).
     ------------------------------------------------------------------ *)
  let prog19 = [
    Decl_type (cl "state3", [],
      Td_record [(cl "pc", Ty_int); (cl "accu", Ty_int); (cl "extra", Ty_int)]);
    Decl_let (cl "set_accu",
      Exp_fun (cl "s", Exp_fun (cl "v",
        Exp_record [(cl "pc", Exp_field (Exp_var (cl "s"), cl "pc"));
                     (cl "accu", Exp_var (cl "v"));
                     (cl "extra", Exp_field (Exp_var (cl "s"), cl "extra"))])));
    Decl_let (cl "s",
      Exp_record [(cl "pc", Exp_int 10); (cl "accu", Exp_int 0);
                   (cl "extra", Exp_int 99)]);
    Decl_let (cl "s2",
      Exp_app (Exp_app (Exp_var (cl "set_accu"), Exp_var (cl "s")), Exp_int 42));
    Decl_expr (print_int_nl
      (Exp_binop (Op_add,
        Exp_binop (Op_add,
          Exp_field (Exp_var (cl "s2"), cl "pc"),
          Exp_field (Exp_var (cl "s2"), cl "accu")),
        Exp_field (Exp_var (cl "s2"), cl "extra"))))
  ] in
  let src19 = "type state3 = { pc : int; accu : int; extra : int }\n\
               let set_accu s v = { pc = s.pc; accu = v; extra = s.extra }\n\
               let s = { pc = 10; accu = 0; extra = 99 }\n\
               let s2 = set_accu s 42\n\
               let () = print_int (s2.pc + s2.accu + s2.extra); print_newline ()" in
  run_test "19. set_accu record fn: 10+42+99 = 151" prog19 src19;

  (* ------------------------------------------------------------------
     Test 20: Recursive function with record
     type state = { count : int; total : int }
     let rec run s =
       if s.count <= 0 then s.total
       else run { count = s.count - 1; total = s.total + s.count }
     let () = print_int (run { count = 5; total = 0 }); print_newline ()
     Expected: 5+4+3+2+1 = 15

     Tests Exp_letrec with record field access in condition and
     record construction in recursive call.
     ------------------------------------------------------------------ *)
  let prog20 = [
    Decl_type (cl "counter", [],
      Td_record [(cl "count", Ty_int); (cl "total", Ty_int)]);
    Decl_let (cl "dummy20",
      Exp_letrec (cl "run",
        Exp_fun (cl "s",
          Exp_if (
            Exp_binop (Op_le,
              Exp_field (Exp_var (cl "s"), cl "count"),
              Exp_int 0),
            Exp_field (Exp_var (cl "s"), cl "total"),
            Exp_app (Exp_var (cl "run"),
              Exp_record [
                (cl "count", Exp_binop (Op_sub,
                  Exp_field (Exp_var (cl "s"), cl "count"),
                  Exp_int 1));
                (cl "total", Exp_binop (Op_add,
                  Exp_field (Exp_var (cl "s"), cl "total"),
                  Exp_field (Exp_var (cl "s"), cl "count")))]))),
        Exp_app (Exp_var (cl "run"),
          Exp_record [(cl "count", Exp_int 5); (cl "total", Exp_int 0)])));
    Decl_expr (print_int_nl (Exp_var (cl "dummy20")))
  ] in
  let src20 = "type counter = { count : int; total : int }\n\
               let rec run s =\n\
               \  if s.count <= 0 then s.total\n\
               \  else run { count = s.count - 1; total = s.total + s.count }\n\
               let () = print_int (run { count = 5; total = 0 }); print_newline ()" in
  run_test "20. recursive fn with record: sum 1..5 = 15" prog20 src20;

  (* ------------------------------------------------------------------
     Test 21: Nested function calls with records
     type point = { x : int; y : int }
     let add_points p1 p2 = { x = p1.x + p2.x; y = p1.y + p2.y }
     let scale p k = { x = p.x * k; y = p.y * k }
     let p1 = { x = 1; y = 2 }
     let p2 = { x = 3; y = 4 }
     let p3 = add_points (scale p1 2) p2
     let () = print_int (p3.x + p3.y); print_newline ()
     Expected: (1*2+3) + (2*2+4) = 5 + 8 = 13

     Tests nested function calls where both arguments and return
     values are records, with field access in arithmetic expressions.
     ------------------------------------------------------------------ *)
  let prog21 = [
    Decl_type (cl "point", [],
      Td_record [(cl "x", Ty_int); (cl "y", Ty_int)]);
    Decl_let (cl "add_points",
      Exp_fun (cl "p1", Exp_fun (cl "p2",
        Exp_record [
          (cl "x", Exp_binop (Op_add,
            Exp_field (Exp_var (cl "p1"), cl "x"),
            Exp_field (Exp_var (cl "p2"), cl "x")));
          (cl "y", Exp_binop (Op_add,
            Exp_field (Exp_var (cl "p1"), cl "y"),
            Exp_field (Exp_var (cl "p2"), cl "y")))])));
    Decl_let (cl "scale",
      Exp_fun (cl "p", Exp_fun (cl "k",
        Exp_record [
          (cl "x", Exp_binop (Op_mul,
            Exp_field (Exp_var (cl "p"), cl "x"),
            Exp_var (cl "k")));
          (cl "y", Exp_binop (Op_mul,
            Exp_field (Exp_var (cl "p"), cl "y"),
            Exp_var (cl "k")))])));
    Decl_let (cl "p1",
      Exp_record [(cl "x", Exp_int 1); (cl "y", Exp_int 2)]);
    Decl_let (cl "p2",
      Exp_record [(cl "x", Exp_int 3); (cl "y", Exp_int 4)]);
    Decl_let (cl "p3",
      Exp_app (Exp_app (Exp_var (cl "add_points"),
        Exp_app (Exp_app (Exp_var (cl "scale"), Exp_var (cl "p1")), Exp_int 2)),
        Exp_var (cl "p2")));
    Decl_expr (print_int_nl
      (Exp_binop (Op_add,
        Exp_field (Exp_var (cl "p3"), cl "x"),
        Exp_field (Exp_var (cl "p3"), cl "y"))))
  ] in
  let src21 = "type point = { x : int; y : int }\n\
               let add_points p1 p2 = { x = p1.x + p2.x; y = p1.y + p2.y }\n\
               let scale p k = { x = p.x * k; y = p.y * k }\n\
               let p1 = { x = 1; y = 2 }\n\
               let p2 = { x = 3; y = 4 }\n\
               let p3 = add_points (scale p1 2) p2\n\
               let () = print_int (p3.x + p3.y); print_newline ()" in
  run_test "21. nested record fns: add(scale p1 2) p2 = 13" prog21 src21;

  (* === Summary === *)
  Printf.printf "\n====================================\n";
  Printf.printf "Results: %d passed, %d failed\n" !passed !failed;
  if !failed > 0 then exit 1
