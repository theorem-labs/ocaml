(* harness.ml - [TRUSTED] PBT harness: interpret-bytecode vs ocamlrun
   Migrated to QCheck. Uses test_common infrastructure for proper heap
   allocation and C-call handling. *)

open Interp_extracted
open Test_common

let compile_and_run = compile_and_run_ocamlc

(* === Run our interpreter using proper heap-allocated globals === *)
let run_ours exe_file =
  match Bytecode_runtime.run_ocamlc_bytecode exe_file with
  | Ok output -> (Finished (Val_int 0), output)
  | Error msg -> (Run_error (List.init (String.length msg) (fun i -> msg.[i])), "")

(* === char list -> string (extracted errors use char list) === *)
let string_of_chars cl =
  let buf = Buffer.create (List.length cl) in
  List.iter (Buffer.add_char buf) cl; Buffer.contents buf

(* === QCheck generators === *)

let gen_source : string QCheck.Gen.t =
  let open QCheck.Gen in

  (* --- Existing generators (arithmetic, functions, closures, etc.) --- *)

  let gen_add = map2 (fun a b ->
    Printf.sprintf "let () = print_int (%d + %d); print_newline ()" a (b + 1)
  ) (int_range 0 99) (int_range 0 99) in
  let gen_mul = map2 (fun a b ->
    Printf.sprintf "let () = print_int (%d * %d); print_newline ()" a b
  ) (int_range 0 49) (int_range 0 49) in
  let gen_cmp = map2 (fun n t ->
    Printf.sprintf "let () = print_int (if %d > %d then 1 else 0); print_newline ()" n t
  ) (int_range 0 99) (int_range 0 99) in
  let gen_fun = map (fun n ->
    Printf.sprintf "let () = let f x = x + x in print_int (f %d); print_newline ()" n
  ) (int_range 0 49) in
  let gen_fact = map (fun n ->
    Printf.sprintf "let () = let rec fact n = if n <= 1 then 1 else n * fact (n-1) in print_int (fact %d); print_newline ()" n
  ) (int_range 0 9) in
  let gen_match = map (fun n ->
    Printf.sprintf "let () = print_int (match %d with 0 -> 100 | 1 -> 200 | _ -> 999); print_newline ()" n
  ) (int_range 0 4) in
  let gen_pair = map2 (fun a b ->
    Printf.sprintf "let () = let p = (%d, %d) in print_int (fst p + snd p); print_newline ()" a b
  ) (int_range 0 49) (int_range 0 49) in
  let gen_sub = map2 (fun a b ->
    Printf.sprintf "let () = print_int (%d - %d); print_newline ()" a (b + 1)
  ) (int_range 0 99) (int_range 0 99) in
  let gen_nested_let = map3 (fun a b c ->
    Printf.sprintf "let () = let x = %d in let y = %d in let z = %d in print_int (x + y + z); print_newline ()" a b c
  ) (int_range 0 19) (int_range 0 19) (int_range 0 19) in
  let gen_bool_logic = map2 (fun a b ->
    Printf.sprintf "let () = print_int (if %d > %d && %d < 200 then 1 else 0); print_newline ()" a b a
  ) (int_range 0 99) (int_range 0 99) in
  let gen_multi_arg = map2 (fun a b ->
    Printf.sprintf "let () = let f x y = x * y + 1 in print_int (f %d %d); print_newline ()" a b
  ) (int_range 0 29) (int_range 0 29) in
  let gen_higher_order = map (fun n ->
    Printf.sprintf "let () = let apply f x = f x in let double x = x * 2 in print_int (apply double %d); print_newline ()" n
  ) (int_range 0 29) in
  let gen_nested_pair = map2 (fun a b ->
    Printf.sprintf "let () = let p = (%d, (%d, 0)) in print_int (fst p + fst (snd p)); print_newline ()" a b
  ) (int_range 0 19) (int_range 0 19) in
  let gen_fib = map (fun n ->
    Printf.sprintf "let () = let rec fib n = if n <= 1 then n else fib (n-1) + fib (n-2) in print_int (fib %d); print_newline ()" n
  ) (int_range 0 14) in
  let gen_divmod = map2 (fun a b ->
    Printf.sprintf "let () = print_int (%d / %d + %d mod %d); print_newline ()" (a + 1) (b + 1) (a + 1) (b + 1)
  ) (int_range 0 999) (int_range 0 49) in
  let gen_neg = map (fun a ->
    Printf.sprintf "let () = print_int (- %d); print_newline ()" a
  ) (int_range 0 99) in
  let gen_variant = map (fun n ->
    Printf.sprintf "type t = A | B | C\nlet () = print_int (match %s with A -> 10 | B -> 20 | C -> 30); print_newline ()"
      (match n with 0 -> "A" | 1 -> "B" | _ -> "C")
  ) (int_range 0 2) in
  let gen_string = pure "let () = print_string \"hello\"; print_newline ()" in
  let gen_partial = map (fun n ->
    Printf.sprintf "let () = let add x y = x + y in let inc = add 1 in print_int (inc %d); print_newline ()" n
  ) (int_range 0 49) in
  let gen_ref = map (fun n ->
    Printf.sprintf "let () = let r = ref %d in r := !r + 1; print_int !r; print_newline ()" n
  ) (int_range 0 99) in
  let gen_ref_alias = map (fun n ->
    Printf.sprintf "let () = let r = ref %d in let s = r in s := !s * 2; print_int !r; print_newline ()" n
  ) (int_range 0 99) in
  let gen_ref_loop = map (fun n ->
    Printf.sprintf "let () = let r = ref 0 in for i = 1 to %d do r := !r + i done; print_int !r; print_newline ()" n
  ) (int_range 0 9) in
  let gen_try = map (fun n ->
    Printf.sprintf "let () = print_int (try if %d > 5 then raise Exit else %d with Exit -> -1); print_newline ()" n n
  ) (int_range 0 9) in
  let gen_nested_try = pure
    "let () = print_int (try try raise Not_found with Exit -> 1 with Not_found -> 2); print_newline ()" in
  let gen_list = map (fun n ->
    Printf.sprintf "let () = let rec len = function [] -> 0 | _ :: t -> 1 + len t in print_int (len [%s]); print_newline ()"
      (String.concat ";" (List.init n (fun i -> string_of_int i)))
  ) (int_range 0 9) in
  let gen_closure_ref = map (fun n ->
    Printf.sprintf "let () = let r = ref 0 in let bump () = r := !r + 1 in for _ = 1 to %d do bump () done; print_int !r; print_newline ()" n
  ) (int_range 0 19) in
  let gen_compare = map2 (fun a b ->
    Printf.sprintf "let () = print_int (compare %d %d); print_newline ()" a b
  ) (int_range 0 99) (int_range 0 99) in
  let gen_strlen = map (fun n ->
    let s = String.init (n + 1) (fun i -> Char.chr (Char.code 'a' + i mod 26)) in
    Printf.sprintf "let () = print_int (String.length %S); print_newline ()" s
  ) (int_range 0 9) in
  let gen_strget = map (fun i ->
    let s = "hello" in
    Printf.sprintf "let () = print_int (Char.code (String.get %S %d)); print_newline ()" s i
  ) (int_range 0 4) in
  let gen_variant_data = map (fun n ->
    Printf.sprintf "type myopt = None2 | Some2 of int\nlet () = print_int (match Some2 %d with None2 -> 0 | Some2 x -> x); print_newline ()" n
  ) (int_range 0 99) in
  let gen_nested_match = map2 (fun a b ->
    Printf.sprintf "let () = print_int (match %d with 0 -> (match %d with 0 -> 100 | _ -> 200) | _ -> 300); print_newline ()" a b
  ) (int_range 0 4) (int_range 0 4) in
  let gen_seq_let = map2 (fun a b ->
    Printf.sprintf "let () = let x = %d in let y = x + %d in print_int (x + y); print_newline ()" a b
  ) (int_range 0 19) (int_range 0 19) in
  let gen_triple = map3 (fun a b c ->
    Printf.sprintf "let () = let (a,b,c) = (%d,%d,%d) in print_int (a+b+c); print_newline ()" a b c
  ) (int_range 0 99) (int_range 0 99) (int_range 0 99) in
  let gen_bitwise = map2 (fun a b ->
    Printf.sprintf "let () = print_int (%d land %d); print_newline ()" a b
  ) (int_range 0 255) (int_range 0 255) in
  let gen_chain = map (fun n ->
    Printf.sprintf "let () = let f x = x + 1 in let g x = x * 2 in print_int (g (f %d)); print_newline ()" n
  ) (int_range 0 9) in
  let gen_while = map (fun n ->
    Printf.sprintf "let () = let r = ref 0 in let i = ref 1 in while !i <= %d do r := !r + !i; i := !i + 1 done; print_int !r; print_newline ()" n
  ) (int_range 0 9) in
  let gen_mutual_rec = map (fun n ->
    Printf.sprintf "let () = let rec even n = if n = 0 then true else odd (n-1) and odd n = if n = 0 then false else even (n-1) in print_int (if even %d then 1 else 0); print_newline ()" n
  ) (int_range 0 19) in

  (* --- NEW: Tail call generators (APPTERM instructions) --- *)

  (* Simple tail-recursive loop: generates APPTERM1 *)
  let gen_tail_loop = map (fun n ->
    Printf.sprintf "let () = let rec loop n = if n = 0 then 0 else loop (n - 1) in print_int (loop %d); print_newline ()" n
  ) (int_range 0 200) in

  (* Tail-recursive accumulator: generates APPTERM2 *)
  let gen_tail_acc = map (fun n ->
    Printf.sprintf "let () = let rec sum n acc = if n = 0 then acc else sum (n - 1) (acc + n) in print_int (sum %d 0); print_newline ()" n
  ) (int_range 0 100) in

  (* Tail-recursive with 3 args: generates APPTERM3 *)
  let gen_tail_3arg = map (fun n ->
    Printf.sprintf "let () = let rec f a b c = if a = 0 then b + c else f (a - 1) (b + 1) (c + 2) in print_int (f %d 0 0); print_newline ()" n
  ) (int_range 0 50) in

  (* Tail call via mutual recursion: generates APPTERM between rec defs *)
  let gen_tail_mutual = map (fun n ->
    Printf.sprintf "let () = let rec ping n = if n = 0 then 42 else pong (n - 1) and pong n = if n = 0 then 99 else ping (n - 1) in print_int (ping %d); print_newline ()" n
  ) (int_range 0 50) in

  (* Deep tail recursion: stress test stack reuse *)
  let gen_tail_deep = map (fun n ->
    Printf.sprintf "let () = let rec count n = if n <= 0 then 0 else 1 + count (n - 1) in print_int (count %d); print_newline ()" n
  ) (int_range 0 100) in

  (* Tail-recursive list length (common pattern using APPTERM) *)
  let gen_tail_list_len = map (fun n ->
    Printf.sprintf "let () = let rec len acc = function [] -> acc | _ :: t -> len (acc + 1) t in print_int (len 0 [%s]); print_newline ()"
      (String.concat ";" (List.init n (fun i -> string_of_int i)))
  ) (int_range 0 15) in

  (* --- NEW: OFFSETREF generators --- *)

  (* Top-level ref + incr uses OFFSETREF 1 *)
  let gen_incr = map (fun n ->
    Printf.sprintf "let r = ref %d\nlet () = incr r; print_int !r; print_newline ()" n
  ) (int_range 0 99) in

  (* Top-level ref + decr uses OFFSETREF -1 *)
  let gen_decr = map (fun n ->
    Printf.sprintf "let r = ref %d\nlet () = decr r; print_int !r; print_newline ()" n
  ) (int_range 1 99) in

  (* Multiple incr/decr on top-level ref *)
  let gen_multi_incr = map2 (fun start count ->
    let incrs = String.concat "; " (List.init count (fun _ -> "incr r")) in
    Printf.sprintf "let r = ref %d\nlet () = %s; print_int !r; print_newline ()" start incrs
  ) (int_range 0 50) (int_range 1 10) in

  (* --- NEW: String bytecode ops (GETSTRINGCHAR) --- *)

  (* String.unsafe_get uses GETSTRINGCHAR bytecode instruction *)
  let gen_string_char = map2 (fun s_idx c_idx ->
    let strings = [|"hello"; "world"; "abcdef"; "xyz"|] in
    let s = strings.(s_idx mod Array.length strings) in
    let i = c_idx mod String.length s in
    Printf.sprintf "let () = print_int (Char.code (String.unsafe_get %S %d)); print_newline ()" s i
  ) (int_range 0 3) (int_range 0 5) in

  (* Bytes.unsafe_get and Bytes.unsafe_set (GETBYTESCHAR, SETBYTESCHAR) *)
  let gen_bytes_ops = map2 (fun n c ->
    Printf.sprintf "let () = let b = Bytes.make %d 'a' in Bytes.unsafe_set b 0 %C; print_int (Char.code (Bytes.unsafe_get b 0)); print_newline ()" (n + 1) (Char.chr (c + Char.code 'a'))
  ) (int_range 1 10) (int_range 0 25) in

  (* Bytes.create + unsafe_set + unsafe_get cycle *)
  let gen_bytes_cycle = map2 (fun len val_ ->
    Printf.sprintf "let () = let b = Bytes.create %d in Bytes.unsafe_set b 0 (Char.chr %d); print_int (Char.code (Bytes.unsafe_get b 0)); print_newline ()" (len + 1) (val_ mod 128)
  ) (int_range 1 5) (int_range 0 127) in

  (* --- NEW: Array ops (VECTLENGTH, GETVECTITEM, SETVECTITEM) --- *)

  (* Array.length uses VECTLENGTH *)
  let gen_array_length = map (fun n ->
    Printf.sprintf "let () = let a = Array.make %d 0 in print_int (Array.length a); print_newline ()" (n + 1)
  ) (int_range 1 20) in

  (* Array.unsafe_get uses GETVECTITEM *)
  let gen_array_get = map2 (fun len idx ->
    let len = len + 1 in
    let idx = idx mod len in
    Printf.sprintf "let () = let a = Array.init %d (fun i -> i * 2) in print_int (Array.unsafe_get a %d); print_newline ()" len idx
  ) (int_range 1 10) (int_range 0 9) in

  (* Array.unsafe_set uses SETVECTITEM *)
  let gen_array_set = map3 (fun len idx v ->
    let len = len + 1 in
    let idx = idx mod len in
    Printf.sprintf "let () = let a = Array.make %d 0 in Array.unsafe_set a %d %d; print_int (Array.unsafe_get a %d); print_newline ()" len idx v idx
  ) (int_range 1 10) (int_range 0 9) (int_range 0 99) in

  (* Array iteration *)
  let gen_array_sum = map (fun n ->
    Printf.sprintf "let () = let a = Array.init %d (fun i -> i) in let s = ref 0 in Array.iter (fun x -> s := !s + x) a; print_int !s; print_newline ()" (n + 1)
  ) (int_range 1 10) in

  (* --- NEW: Immediate branch comparisons (BEQ, BNEQ, BLTINT, etc.) --- *)
  (* These are generated by ocamlc for pattern matches on ints and
     comparison against constants in if-then-else *)

  (* Pattern match on specific int values generates BEQ/BNEQ *)
  let gen_beq = map (fun n ->
    Printf.sprintf "let () = let f x = match x with 0 -> 10 | 1 -> 20 | 2 -> 30 | 3 -> 40 | _ -> 50 in print_int (f %d); print_newline ()" n
  ) (int_range 0 5) in

  (* Comparison against constant: if x < 5 generates BLTINT/BGEINT *)
  let gen_blt = map (fun n ->
    Printf.sprintf "let () = let f x = if x < 5 then 1 else 0 in print_int (f %d); print_newline ()" n
  ) (int_range 0 9) in

  let gen_ble = map (fun n ->
    Printf.sprintf "let () = let f x = if x <= 5 then 1 else 0 in print_int (f %d); print_newline ()" n
  ) (int_range 0 9) in

  let gen_bgt = map (fun n ->
    Printf.sprintf "let () = let f x = if x > 5 then 1 else 0 in print_int (f %d); print_newline ()" n
  ) (int_range 0 9) in

  let gen_bge = map (fun n ->
    Printf.sprintf "let () = let f x = if x >= 5 then 1 else 0 in print_int (f %d); print_newline ()" n
  ) (int_range 0 9) in

  (* --- NEW: Unsigned comparisons (BULTINT/BUGEINT via char matching) --- *)
  (* Character pattern matching uses BULTINT/BUGEINT for range checks *)
  let gen_char_match = map (fun c ->
    Printf.sprintf "let () = let f c = match c with 'a'..'z' -> 1 | 'A'..'Z' -> 2 | '0'..'9' -> 3 | _ -> 0 in print_int (f %C); print_newline ()" (Char.chr (c + Char.code 'A'))
  ) (int_range 0 57) in

  (* Character classification (exercises unsigned comparison) *)
  let gen_char_classify = map (fun c ->
    let c = Char.chr ((c mod 95) + 32) in (* printable ASCII *)
    Printf.sprintf "let () = let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') in print_int (if is_alpha %C then 1 else 0); print_newline ()" c
  ) (int_range 0 94) in

  (* --- NEW: OFFSETINT generators --- *)
  (* succ/pred on ints generates OFFSETINT *)
  let gen_succ = map (fun n ->
    Printf.sprintf "let () = print_int (succ %d); print_newline ()" n
  ) (int_range 0 99) in

  let gen_pred = map (fun n ->
    Printf.sprintf "let () = print_int (pred %d); print_newline ()" n
  ) (int_range 1 99) in

  (* --- NEW: OFFSETCLOSURE / PUSHOFFSETCLOSURE --- *)
  (* Mutual recursion in closurerec generates OFFSETCLOSURE *)
  let gen_offset_closure = map (fun n ->
    Printf.sprintf "let () = let rec f x = if x <= 0 then 0 else g (x - 1) + 1 and g x = if x <= 0 then 0 else f (x - 1) + 2 in print_int (f %d); print_newline ()" n
  ) (int_range 0 10) in

  (* Three mutually recursive functions *)
  let gen_offset_closure_3 = map (fun n ->
    Printf.sprintf "let () = let rec a x = if x <= 0 then 1 else b (x-1) and b x = if x <= 0 then 2 else c (x-1) and c x = if x <= 0 then 3 else a (x-1) in print_int (a %d); print_newline ()" n
  ) (int_range 0 10) in

  (* --- NEW: Exception variants (RAISE_NOTRACE, RERAISE) --- *)

  (* raise_notrace generates RAISE_NOTRACE *)
  let gen_raise_notrace = map (fun n ->
    Printf.sprintf "let () = print_int (try if %d > 5 then raise_notrace Exit else %d with Exit -> -1); print_newline ()" n n
  ) (int_range 0 9) in

  (* Nested exception handling with reraise pattern *)
  let gen_nested_exn = map (fun n ->
    Printf.sprintf "let () = print_int (try (try if %d > 3 then raise Not_found else 0 with Exit -> 1) with Not_found -> 2); print_newline ()" n
  ) (int_range 0 9) in

  (* Custom exception with data *)
  let gen_exn_data = map (fun n ->
    Printf.sprintf "exception My_exn of int\nlet () = print_int (try raise (My_exn %d) with My_exn x -> x); print_newline ()" n
  ) (int_range 0 99) in

  (* --- NEW: Shift operations (LSLINT, LSRINT, ASRINT) --- *)
  let gen_lsl = map2 (fun a b ->
    Printf.sprintf "let () = print_int (%d lsl %d); print_newline ()" a (b mod 30)
  ) (int_range 1 15) (int_range 0 5) in

  let gen_lsr = map2 (fun a b ->
    Printf.sprintf "let () = print_int (%d lsr %d); print_newline ()" a (b mod 30)
  ) (int_range 1 1000) (int_range 0 5) in

  let gen_asr = map2 (fun a b ->
    Printf.sprintf "let () = print_int (%d asr %d); print_newline ()" a (b mod 30)
  ) (int_range (-100) 100) (int_range 0 5) in

  (* --- NEW: More bitwise ops (OR, XOR) --- *)
  let gen_or = map2 (fun a b ->
    Printf.sprintf "let () = print_int (%d lor %d); print_newline ()" a b
  ) (int_range 0 255) (int_range 0 255) in

  let gen_xor = map2 (fun a b ->
    Printf.sprintf "let () = print_int (%d lxor %d); print_newline ()" a b
  ) (int_range 0 255) (int_range 0 255) in

  (* --- NEW: ISINT instruction --- *)
  let gen_isint = map (fun n ->
    Printf.sprintf "let () = print_int (if Obj.is_int (Obj.repr %d) then 1 else 0); print_newline ()" n
  ) (int_range 0 10) in

  (* --- NEW: BOOLNOT instruction --- *)
  let gen_boolnot = map (fun b ->
    Printf.sprintf "let () = print_string (if not %s then \"true\" else \"false\"); print_newline ()" (if b = 0 then "true" else "false")
  ) (int_range 0 1) in

  (* --- NEW: Larger pattern match with SWITCH instruction --- *)
  let gen_switch_large = map (fun n ->
    Printf.sprintf "let () = let f = function 0 -> 100 | 1 -> 200 | 2 -> 300 | 3 -> 400 | 4 -> 500 | _ -> 0 in print_int (f %d); print_newline ()" n
  ) (int_range 0 6) in

  (* --- NEW: for loop (tests OFFSETINT on loop variable) --- *)
  let gen_for_loop = map2 (fun lo hi ->
    Printf.sprintf "let () = let r = ref 0 in for i = %d to %d do r := !r + i done; print_int !r; print_newline ()" lo (lo + hi)
  ) (int_range 0 5) (int_range 0 10) in

  (* --- NEW: String.concat (tests more string C-calls) --- *)
  let gen_string_concat = map2 (fun a b ->
    Printf.sprintf "let () = print_string (%S ^ %S); print_newline ()" a b
  ) (pure "hello") (pure "world") in

  (* --- NEW: List.rev with tail recursion (tests APPTERM with list ops) --- *)
  let gen_list_rev = map (fun n ->
    Printf.sprintf "let () = let rec rev acc = function [] -> acc | x :: xs -> rev (x :: acc) xs in let l = rev [] [%s] in List.iter (fun x -> print_int x; print_char ' ') l; print_newline ()"
      (String.concat ";" (List.init n (fun i -> string_of_int i)))
  ) (int_range 0 10) in

  (* --- NEW: Closures capturing variables at different depths --- *)
  let gen_deep_closure = map (fun n ->
    Printf.sprintf "let () = let a = %d in let f () = let b = a + 1 in let g () = b + a in g () in print_int (f ()); print_newline ()" n
  ) (int_range 0 20) in

  (* --- NEW: GRAB instruction (partial application with multiple args) --- *)
  let gen_grab = map2 (fun a b ->
    Printf.sprintf "let () = let f x y z = x + y + z in let g = f %d in let h = g %d in print_int (h 3); print_newline ()" a b
  ) (int_range 0 20) (int_range 0 20) in

  (* --- NEW: ASSIGN instruction --- *)
  let gen_assign = map2 (fun init v ->
    Printf.sprintf "let () = let x = ref %d in x := %d; print_int !x; print_newline ()" init v
  ) (int_range 0 99) (int_range 0 99) in

  (* --- NEW: Float record (MAKEFLOATBLOCK / GETFLOATFIELD / SETFLOATFIELD) --- *)
  let gen_float_record = map2 (fun a b ->
    (* All-float records use MAKEFLOATBLOCK and GETFLOATFIELD *)
    Printf.sprintf "type point = { x: float; y: float }\nlet () = let p = { x = %d.0; y = %d.0 } in Printf.printf \"%%g %%g\\n\" p.x p.y" a b
  ) (int_range 0 20) (int_range 0 20) in

  (* Mutable float record (SETFLOATFIELD) *)
  let gen_mutable_float = map3 (fun a b c ->
    Printf.sprintf "type mfp = { mutable mx: float; mutable my: float }\nlet () = let p = { mx = %d.0; my = %d.0 } in p.mx <- %d.0; Printf.printf \"%%g %%g\\n\" p.mx p.my" a b c
  ) (int_range 0 20) (int_range 0 20) (int_range 0 99) in

  (* --- NEW: Exception with string data --- *)
  let gen_exn_string = map (fun n ->
    Printf.sprintf "exception Msg of string\nlet () = print_string (try raise (Msg \"hello%d\") with Msg s -> s); print_newline ()" n
  ) (int_range 0 9) in

  (* --- NEW: Deeply nested exception handling --- *)
  let gen_deep_exn = map (fun n ->
    Printf.sprintf "let () = print_int (try (try (try if %d > 7 then raise Exit else if %d > 3 then raise Not_found else 0 with Exit -> 1) with Not_found -> 2) with _ -> 3); print_newline ()" n n
  ) (int_range 0 9) in

  (* --- NEW: Hashtbl usage (exercises many C-calls and heap ops) --- *)
  let gen_hashtbl = map (fun n ->
    Printf.sprintf "let () = let h = Hashtbl.create 16 in for i = 0 to %d do Hashtbl.add h i (i * i) done; print_int (try Hashtbl.find h %d with Not_found -> -1); print_newline ()" n (n / 2)
  ) (int_range 0 10) in

  (* --- NEW: Pattern match on tuples (tests tuple field access patterns) --- *)
  let gen_tuple_match = map3 (fun a b c ->
    Printf.sprintf "let () = let f = function (0, _) -> 10 | (_, 0) -> 20 | (a, b) -> a + b in print_int (f (%d, %d) + f (%d, 0)); print_newline ()" a b c
  ) (int_range 0 5) (int_range 0 5) (int_range 0 5) in

  (* --- NEW: Option type usage (common OCaml pattern) --- *)
  let gen_option = map (fun n ->
    Printf.sprintf "let () = let f x = if x > 5 then Some (x * 2) else None in print_int (match f %d with Some v -> v | None -> 0); print_newline ()" n
  ) (int_range 0 10) in

  (* --- NEW: String.make and String.length combo --- *)
  let gen_string_make = map2 (fun len c ->
    Printf.sprintf "let () = let s = String.make %d %C in print_int (String.length s); print_char ' '; print_int (Char.code s.[0]); print_newline ()" (len + 1) (Char.chr (c + Char.code 'a'))
  ) (int_range 1 10) (int_range 0 25) in

  (* --- NEW: Fibonacci with accumulator (tail-recursive, exercises APPTERM3) --- *)
  let gen_fib_tail = map (fun n ->
    Printf.sprintf "let () = let rec fib n a b = if n = 0 then a else fib (n-1) b (a+b) in print_int (fib %d 0 1); print_newline ()" n
  ) (int_range 0 20) in

  (* --- NEW: Nested function application chains --- *)
  let gen_app_chain = map (fun n ->
    Printf.sprintf "let () = let f x = x + 1 in let g x = x * 2 in let h x = x - 3 in print_int (h (g (f %d))); print_newline ()" n
  ) (int_range 0 20) in

  (* --- NEW: Complex closure (closure captures closure) --- *)
  let gen_closure_chain = map (fun n ->
    Printf.sprintf "let () = let make_adder x = fun y -> x + y in let add5 = make_adder 5 in let add10 = make_adder 10 in print_int (add5 %d + add10 %d); print_newline ()" n n
  ) (int_range 0 20) in

  (* --- NEW: Top-level ref with multiple mutations (exercises OFFSETREF more) --- *)
  let gen_ref_mutations = map (fun n ->
    Printf.sprintf "let counter = ref 0\nlet () = for _ = 1 to %d do incr counter done; for _ = 1 to %d do decr counter done; print_int !counter; print_newline ()" (n + 3) n
  ) (int_range 0 10) in

  oneof [
    gen_add; gen_mul; gen_cmp; gen_fun; gen_fact; gen_match; gen_pair;
    gen_sub; gen_nested_let; gen_bool_logic; gen_multi_arg; gen_higher_order;
    gen_nested_pair; gen_fib; gen_divmod; gen_neg; gen_variant; gen_string;
    gen_partial; gen_ref; gen_ref_alias; gen_ref_loop; gen_try; gen_nested_try;
    gen_list; gen_closure_ref; gen_compare; gen_strlen; gen_strget;
    gen_variant_data; gen_nested_match; gen_seq_let; gen_triple; gen_bitwise;
    gen_chain; gen_while; gen_mutual_rec;
    (* NEW generators *)
    gen_tail_loop; gen_tail_acc; gen_tail_3arg; gen_tail_mutual; gen_tail_deep;
    gen_tail_list_len;
    gen_incr; gen_decr; gen_multi_incr;
    gen_string_char; gen_bytes_ops; gen_bytes_cycle;
    gen_array_length; gen_array_get; gen_array_set; gen_array_sum;
    gen_beq; gen_blt; gen_ble; gen_bgt; gen_bge;
    gen_char_match; gen_char_classify;
    gen_succ; gen_pred;
    gen_offset_closure; gen_offset_closure_3;
    gen_raise_notrace; gen_nested_exn; gen_exn_data;
    gen_lsl; gen_lsr; gen_asr;
    gen_or; gen_xor;
    gen_isint; gen_boolnot;
    gen_switch_large;
    gen_for_loop;
    gen_string_concat;
    gen_list_rev;
    gen_deep_closure;
    gen_grab;
    gen_assign;
    gen_float_record; gen_mutable_float;
    gen_exn_string; gen_deep_exn;
    gen_hashtbl;
    gen_tuple_match;
    gen_option;
    gen_string_make;
    gen_fib_tail;
    gen_app_chain;
    gen_closure_chain;
    gen_ref_mutations;
  ]

(* Shared temp dir for all tests *)
let temp_dir = ref ""

let harness_test =
  QCheck.Test.make ~name:"bytecode interpreter vs ocamlrun" ~count:500
    (QCheck.make gen_source ~print:Fun.id)
    (fun source ->
       with_temp_dir (fun dir ->
         match compile_and_run dir source with
         | None ->
           (* Skip: compile failed, assume valid *)
           true
         | Some expected ->
           try
             let result, output = run_ours (Filename.concat dir "test.byte") in
             (match result with
              | Finished _ -> output = expected
              | Run_error msg ->
                Printf.eprintf "Run error: %s\nsource:\n%s\n%!" (string_of_chars msg) source; false
              | Out_of_fuel _ ->
                Printf.eprintf "Out of fuel\nsource:\n%s\n%!" source; false)
           with exn ->
             Printf.eprintf "Exception: %s\nsource:\n%s\n%!" (Printexc.to_string exn) source; false))

let () =
  exit (QCheck_base_runner.run_tests ~verbose:true [harness_test])
