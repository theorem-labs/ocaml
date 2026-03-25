(* Manual test: hand-crafted bytecode to test interpreter directly *)
open Interp_extracted

let () =
  (* Simple program: compute 3 + 4 and halt *)
  let code = [
    CONSTINT 3;     (* 0: accu = 3 *)
    PUSH;           (* 1: push 3 *)
    CONSTINT 4;     (* 2: accu = 4 *)
    ADDINT;         (* 3: accu = 3 + 4 = 7 *)
    STOP;           (* 4: halt with accu = 7 *)
  ] in
  let result = run_pure 100 code [] in
  (match result with
   | Finished (Val_int n) -> Printf.printf "Test 1 (3+4): %d (expected 7)\n" n
   | Finished _ -> Printf.printf "Test 1: unexpected value\n"
   | Run_error msg -> Printf.printf "Test 1 ERROR: "; List.iter print_char msg; print_newline ()
   | Out_of_fuel _ -> Printf.printf "Test 1: out of fuel\n");

  (* Function call test: let f x = x + 1 in f 41 *)
  let code2 = [
    BRANCH 6;        (* 0: jump to main *)
    (* function body at pc=1 *)
    ACC 0;           (* 1: get argument *)
    PUSH;            (* 2: push it *)
    CONSTINT 1;      (* 3: accu = 1 *)
    ADDINT;          (* 4: accu = arg + 1 *)
    RETURN 1;        (* 5: return, pop 1 local *)
    (* main code at pc=6 *)
    CLOSURE (0, 1);  (* 6: create closure pointing to pc=1 *)
    PUSH;            (* 7: push closure *)
    CONSTINT 41;     (* 8: accu = 41 *)
    PUSH;            (* 9: push 41 (argument) *)
    ACC 1;           (* 10: accu = closure *)
    APPLY1;          (* 11: call closure(41) *)
    STOP;            (* 12: halt with result *)
  ] in
  let result2 = run_pure 100 code2 [] in
  (match result2 with
   | Finished (Val_int n) -> Printf.printf "Test 2 (f 41 where f x = x+1): %d (expected 42)\n" n
   | Finished _ -> Printf.printf "Test 2: unexpected value\n"
   | Run_error msg -> Printf.printf "Test 2 ERROR: "; List.iter print_char msg; print_newline ()
   | Out_of_fuel _ -> Printf.printf "Test 2: out of fuel\n");

  (* Global variable test *)
  let code4 = [
    CONSTINT 42;     (* 0: accu = 42 *)
    SETGLOBAL 0;     (* 1: global[0] = 42 *)
    GETGLOBAL 0;     (* 2: accu = global[0] *)
    STOP;            (* 3: halt *)
  ] in
  let result4 = run_pure 100 code4 [Val_int 0] in
  (match result4 with
   | Finished (Val_int n) -> Printf.printf "Test 3 (global set/get): %d (expected 42)\n" n
   | Finished _ -> Printf.printf "Test 3: unexpected value\n"
   | Run_error msg -> Printf.printf "Test 3 ERROR: "; List.iter print_char msg; print_newline ()
   | Out_of_fuel _ -> Printf.printf "Test 3: out of fuel\n");

  (* Block test: make a pair and access fields *)
  let code5 = [
    CONSTINT 10;     (* 0: accu = 10 *)
    PUSH;            (* 1: push 10 *)
    CONSTINT 20;     (* 2: accu = 20 *)
    MAKEBLOCK2 0;    (* 3: accu = (20, 10) -- accu is first field! *)
    PUSH;            (* 4: push pair *)
    ACC 0;           (* 5: accu = pair *)
    GETFIELD 0;      (* 6: accu = field 0 = 20 *)
    PUSH;            (* 7: push 20 *)
    ACC 1;           (* 8: accu = pair *)
    GETFIELD 1;      (* 9: accu = field 1 = 10 *)
    ADDINT;          (* 10: accu = 20 + 10 = 30 *)
    STOP;            (* 11: halt *)
  ] in
  let result5 = run_pure 100 code5 [] in
  (match result5 with
   | Finished (Val_int n) -> Printf.printf "Test 4 (pair fields): %d (expected 30)\n" n
   | Finished _ -> Printf.printf "Test 4: unexpected value\n"
   | Run_error msg -> Printf.printf "Test 4 ERROR: "; List.iter print_char msg; print_newline ()
   | Out_of_fuel _ -> Printf.printf "Test 4: out of fuel\n");

  Printf.printf "Done.\n"
