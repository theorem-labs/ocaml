(* harness.ml - [TRUSTED] PBT harness: interpret-bytecode vs ocamlrun *)

open Interp_extracted

(* === Temp dir === *)
let with_temp_dir f =
  let dir = Filename.temp_file "pbt" "" in
  Sys.remove dir; Unix.mkdir dir 0o700;
  Fun.protect ~finally:(fun () ->
    (try Array.iter (fun n -> Sys.remove (Filename.concat dir n)) (Sys.readdir dir) with _ -> ());
    (try Unix.rmdir dir with _ -> ())
  ) (fun () -> f dir)

(* === Compile + run with ocamlrun === *)
let compile_and_run dir source =
  let src = Filename.concat dir "test.ml" in
  let exe = Filename.concat dir "test.byte" in
  let oc = open_out src in output_string oc source; close_out oc;
  if Sys.command (Printf.sprintf "ocamlc -o %s %s 2>/dev/null" exe src) <> 0 then
    None
  else begin
    let ic = Unix.open_process_in (Printf.sprintf "timeout 5 ocamlrun %s 2>/dev/null" exe) in
    let buf = Buffer.create 256 in
    (try while true do Buffer.add_char buf (input_char ic) done with End_of_file -> ());
    ignore (Unix.close_process_in ic);
    Some (Buffer.contents buf)
  end

(* === Convert OCaml Obj.t to our value type === *)
let rec obj_to_value (obj : Obj.t) : value =
  if Obj.is_int obj then Val_int (Obj.obj obj : int)
  else
    let tag = Obj.tag obj in
    let size = Obj.size obj in
    if tag = Obj.string_tag then
      let s : string = Obj.obj obj in
      Val_block (252, List.init (String.length s) (fun i -> Val_int (Char.code s.[i])))
    else if tag = Obj.double_tag then Val_int 0
    else if tag < Obj.no_scan_tag then
      Val_block (tag, List.init size (fun i -> obj_to_value (Obj.field obj i)))
    else Val_block (tag, [])

(* === Load globals and primitives === *)
let load_globals data sections =
  match Loader.find_section sections "DATA" with
  | None -> [||]
  | Some s ->
    let obj : Obj.t = Marshal.from_bytes (Bytes.sub data s.offset s.length) 0 in
    Array.map obj_to_value (Obj.obj obj : Obj.t array)

let load_prims data sections =
  match Loader.find_section sections "PRIM" with
  | None -> [||]
  | Some s ->
    let raw = Bytes.sub_string data s.offset s.length in
    Array.of_list (List.filter (fun s -> String.length s > 0) (String.split_on_char '\000' raw))

(* === C call handler === *)
let make_handler prims buf =
  fun idx args ->
    let name = if idx < Array.length prims then prims.(idx) else "?" in
    match name, args with
    | "caml_ml_output_char", [_; Val_int c] ->
      Buffer.add_char buf (Char.chr (c land 0xFF)); Some (Val_int 0)
    | ("caml_ml_output_bytes" | "caml_ml_output"), _ ->
      let get_chars v = match v with
        | Val_block (252, chars) -> Some chars
        | _ -> None in
      (match args with
       | [_; sv; Val_int off; Val_int len] ->
         (match get_chars sv with
          | Some chars ->
            for i = off to off + len - 1 do
              match List.nth_opt chars i with
              | Some (Val_int c) -> Buffer.add_char buf (Char.chr (c land 0xFF))
              | _ -> ()
            done
          | None -> ());
         Some (Val_int 0)
       | _ -> Some (Val_int 0))
    | "caml_ml_flush", _ -> Some (Val_int 0)
    | "caml_format_int", [_fmt; Val_int n] ->
      let s = string_of_int n in
      Some (Val_block (252, List.init (String.length s) (fun i -> Val_int (Char.code s.[i]))))
    | "caml_register_named_value", _ -> Some (Val_int 0)
    | "caml_fresh_oo_id", _ -> Some (Val_int 0)
    | "caml_ml_open_descriptor_in", [Val_int fd] ->
      (* Return a channel block. Use Custom_tag=255 with fd as payload. *)
      Some (Val_block (255, [Val_int fd]))
    | "caml_ml_open_descriptor_out", [Val_int fd] ->
      Some (Val_block (255, [Val_int fd]))
    | "caml_ml_set_channel_name", _ -> Some (Val_int 0)
    | "caml_sys_const_max_wosize", _ -> Some (Val_int ((1 lsl 57) - 1))
    | "caml_sys_const_int_size", _ -> Some (Val_int 63)
    | "caml_obj_tag", [Val_block (t, _)] -> Some (Val_int t)
    | "caml_obj_tag", [Val_int _] -> Some (Val_int 1000)
    | ("caml_string_length" | "caml_ml_string_length"), [Val_block (252, cs)] -> Some (Val_int (List.length cs))
    | "caml_create_bytes", [Val_int n] -> Some (Val_block (252, List.init n (fun _ -> Val_int 0)))
    | ("caml_blit_string" | "caml_blit_bytes"), _ -> Some (Val_int 0)
    | "caml_string_equal", [Val_block (252,a); Val_block (252,b)] -> Some (Val_int (if a=b then 1 else 0))
    | "caml_int_compare", [Val_int a; Val_int b] ->
      Some (Val_int (if a < b then -1 else if a > b then 1 else 0))
    | "caml_compare", [Val_int a; Val_int b] ->
      Some (Val_int (if a < b then -1 else if a > b then 1 else 0))
    | "caml_string_concat", [Val_block (252, a); Val_block (252, b)] ->
      Some (Val_block (252, a @ b))
    | "caml_string_of_bytes", [v] -> Some v
    | "caml_bytes_of_string", [v] -> Some v
    | ("caml_string_get" | "caml_bytes_get"), [Val_block (252, cs); Val_int i] ->
      (match List.nth_opt cs i with Some v -> Some v | None -> Some (Val_int 0))
    | ("caml_string_set" | "caml_bytes_set"), _ -> Some (Val_int 0)
    | "caml_fill_bytes", _ -> Some (Val_int 0)
    | ("caml_string_length" | "caml_ml_string_length"), _ -> Some (Val_int 0)
    | "caml_int64_float_of_bits", _ -> Some (Val_int 0)
    | "caml_sys_const_naked_pointers_checked", _ -> Some (Val_int 0)
    | "caml_ml_out_channels_list", _ -> Some (Val_int 0)  (* [] = Val_int 0 *)
    | "caml_obj_tag", [Val_ptr _] -> Some (Val_int 0)
    | "caml_ml_channel_size", _ -> Some (Val_int 0)
    | "caml_sys_getenv", _ ->
      (* Raise Not_found *)
      Some (Val_int 0)
    | _ ->
      Printf.eprintf "  [ccall] %s (idx=%d, %d args)\n%!" name idx (List.length args);
      Some (Val_int 0)

(* === Native OCaml run loop (avoids extracted nat fuel overhead) === *)
let run_native fuel code state handler =
  let s = ref state in
  let remaining = ref fuel in
  let rec loop () =
    if !remaining <= 0 then Out_of_fuel !s
    else begin
      decr remaining;
      match step code !s with
      | Step s' -> s := s'; loop ()
      | Halt v -> Finished v
      | Error msg -> Run_error msg
      | CCall_request (idx, args, cont) ->
        match handler idx args with
        | Some v -> s := set_accu cont v; loop ()
        | None -> Run_error ('C' :: 'c' :: 'a' :: 'l' :: 'l' :: ' ' :: 'f' :: 'a' :: 'i' :: 'l' :: [])
    end
  in loop ()

(* === Run our interpreter === *)
let run_ours exe_file =
  let data = Loader.read_file exe_file in
  let sections = Loader.parse_sections data in
  let code = Loader.load_bytecode_from_sections data sections in
  let globals = Array.to_list (load_globals data sections) in
  let prims = load_prims data sections in
  let buf = Buffer.create 256 in
  let handler = make_handler prims buf in
  let result = run_native 10000000 code (initial_state globals) handler in
  (result, Buffer.contents buf)

(* === char list -> string (extracted errors use char list) === *)
let string_of_chars cl =
  let buf = Buffer.create (List.length cl) in
  List.iter (Buffer.add_char buf) cl; Buffer.contents buf

(* === Test generators === *)
let generators = [|
  (fun r -> Printf.sprintf "let () = print_int (%d + %d); print_newline ()"
    (Random.State.int r 100) (Random.State.int r 100 + 1));
  (fun r -> Printf.sprintf "let () = print_int (%d * %d); print_newline ()"
    (Random.State.int r 50) (Random.State.int r 50));
  (fun r -> let n = Random.State.int r 100 in let t = Random.State.int r 100 in
    Printf.sprintf "let () = print_int (if %d > %d then 1 else 0); print_newline ()" n t);
  (fun r -> let n = Random.State.int r 50 in
    Printf.sprintf "let () = let f x = x + x in print_int (f %d); print_newline ()" n);
  (fun r -> let n = Random.State.int r 10 in
    Printf.sprintf "let () = let rec fact n = if n <= 1 then 1 else n * fact (n-1) in print_int (fact %d); print_newline ()" n);
  (fun r -> let n = Random.State.int r 5 in
    Printf.sprintf "let () = print_int (match %d with 0 -> 100 | 1 -> 200 | _ -> 999); print_newline ()" n);
  (fun r -> let a = Random.State.int r 50 in let b = Random.State.int r 50 in
    Printf.sprintf "let () = let p = (%d, %d) in print_int (fst p + snd p); print_newline ()" a b);
  (fun r -> let a = Random.State.int r 100 in let b = Random.State.int r 100 + 1 in
    Printf.sprintf "let () = print_int (%d - %d); print_newline ()" a b);
  (* Nested let *)
  (fun r -> let a = Random.State.int r 20 in let b = Random.State.int r 20 in let c = Random.State.int r 20 in
    Printf.sprintf "let () = let x = %d in let y = %d in let z = %d in print_int (x + y + z); print_newline ()" a b c);
  (* Boolean logic *)
  (fun r -> let a = Random.State.int r 100 in let b = Random.State.int r 100 in
    Printf.sprintf "let () = print_int (if %d > %d && %d < 200 then 1 else 0); print_newline ()" a b a);
  (* Multi-arg function *)
  (fun r -> let a = Random.State.int r 30 in let b = Random.State.int r 30 in
    Printf.sprintf "let () = let f x y = x * y + 1 in print_int (f %d %d); print_newline ()" a b);
  (* Higher-order function *)
  (fun r -> let n = Random.State.int r 30 in
    Printf.sprintf "let () = let apply f x = f x in let double x = x * 2 in print_int (apply double %d); print_newline ()" n);
  (* List-like: nested pairs *)
  (fun r -> let a = Random.State.int r 20 in let b = Random.State.int r 20 in
    Printf.sprintf "let () = let p = (%d, (%d, 0)) in print_int (fst p + fst (snd p)); print_newline ()" a b);
  (* Fibonacci *)
  (fun r -> let n = Random.State.int r 15 in
    Printf.sprintf "let () = let rec fib n = if n <= 1 then n else fib (n-1) + fib (n-2) in print_int (fib %d); print_newline ()" n);
  (* Div and mod *)
  (fun r -> let a = Random.State.int r 1000 + 1 in let b = Random.State.int r 50 + 1 in
    Printf.sprintf "let () = print_int (%d / %d + %d mod %d); print_newline ()" a b a b);
  (* Negative numbers *)
  (fun r -> let a = Random.State.int r 100 in
    Printf.sprintf "let () = print_int (- %d); print_newline ()" a);
  (* Variant/constructor matching *)
  (fun r -> let n = Random.State.int r 3 in
    Printf.sprintf "type t = A | B | C\nlet () = print_int (match %s with A -> 10 | B -> 20 | C -> 30); print_newline ()"
      (match n with 0 -> "A" | 1 -> "B" | _ -> "C"));
  (* String output *)
  (fun _r ->
    "let () = print_string \"hello\"; print_newline ()");
  (* Partial application *)
  (fun r -> let n = Random.State.int r 50 in
    Printf.sprintf "let () = let add x y = x + y in let inc = add 1 in print_int (inc %d); print_newline ()" n);
  (* Ref: create, read, write *)
  (fun r -> let n = Random.State.int r 100 in
    Printf.sprintf "let () = let r = ref %d in r := !r + 1; print_int !r; print_newline ()" n);
  (* Ref: aliasing *)
  (fun r -> let n = Random.State.int r 100 in
    Printf.sprintf "let () = let r = ref %d in let s = r in s := !s * 2; print_int !r; print_newline ()" n);
  (* Ref: loop with ref counter *)
  (fun r -> let n = Random.State.int r 10 in
    Printf.sprintf "let () = let r = ref 0 in for i = 1 to %d do r := !r + i done; print_int !r; print_newline ()" n);
  (* Exception: try/with *)
  (fun r -> let n = Random.State.int r 10 in
    Printf.sprintf "let () = print_int (try if %d > 5 then raise Exit else %d with Exit -> -1); print_newline ()" n n);
  (* Exception: nested *)
  (fun _r ->
    "let () = print_int (try try raise Not_found with Exit -> 1 with Not_found -> 2); print_newline ()");
  (* List operations *)
  (fun r -> let n = Random.State.int r 10 in
    Printf.sprintf "let () = let rec len = function [] -> 0 | _ :: t -> 1 + len t in print_int (len [%s]); print_newline ()"
      (String.concat ";" (List.init n (fun i -> string_of_int i))));
  (* Closure capture of mutable ref *)
  (fun r -> let n = Random.State.int r 20 in
    Printf.sprintf "let () = let r = ref 0 in let bump () = r := !r + 1 in for _ = 1 to %d do bump () done; print_int !r; print_newline ()" n);
  (* Curried comparison *)
  (fun r -> let a = Random.State.int r 100 in let b = Random.State.int r 100 in
    Printf.sprintf "let () = print_int (compare %d %d); print_newline ()" a b);
  (* String.length *)
  (fun r -> let n = Random.State.int r 10 in
    let s = String.init (n + 1) (fun i -> Char.chr (Char.code 'a' + i mod 26)) in
    Printf.sprintf "let () = print_int (String.length %S); print_newline ()" s);
  (* String.get / char access *)
  (fun r -> let s = "hello" in let i = Random.State.int r (String.length s) in
    Printf.sprintf "let () = print_int (Char.code (String.get %S %d)); print_newline ()" s i);
  (* Variant with data *)
  (fun r -> let n = Random.State.int r 100 in
    Printf.sprintf "type myopt = None2 | Some2 of int\nlet () = print_int (match Some2 %d with None2 -> 0 | Some2 x -> x); print_newline ()" n);
  (* Nested match *)
  (fun r -> let a = Random.State.int r 5 in let b = Random.State.int r 5 in
    Printf.sprintf "let () = print_int (match %d with 0 -> (match %d with 0 -> 100 | _ -> 200) | _ -> 300); print_newline ()" a b);
  (* Mutual let binding (sequential) *)
  (fun r -> let a = Random.State.int r 20 in let b = Random.State.int r 20 in
    Printf.sprintf "let () = let x = %d in let y = x + %d in print_int (x + y); print_newline ()" a b);
  (* Array-like: large tuple *)
  (fun r -> let a = Random.State.int r 100 in let b = Random.State.int r 100 in
    let c = Random.State.int r 100 in
    Printf.sprintf "let () = let (a,b,c) = (%d,%d,%d) in print_int (a+b+c); print_newline ()" a b c);
  (* Bitwise operations *)
  (fun r -> let a = Random.State.int r 256 in let b = Random.State.int r 256 in
    Printf.sprintf "let () = print_int (%d land %d); print_newline ()" a b);
  (* Chained function application *)
  (fun r -> let n = Random.State.int r 10 in
    Printf.sprintf "let () = let f x = x + 1 in let g x = x * 2 in print_int (g (f %d)); print_newline ()" n);
  (* While loop with ref *)
  (fun r -> let n = Random.State.int r 10 in
    Printf.sprintf "let () = let r = ref 0 in let i = ref 1 in while !i <= %d do r := !r + !i; i := !i + 1 done; print_int !r; print_newline ()" n);
  (* Mutual recursion: even/odd *)
  (fun r -> let n = Random.State.int r 20 in
    Printf.sprintf "let () = let rec even n = if n = 0 then true else odd (n-1) and odd n = if n = 0 then false else even (n-1) in print_int (if even %d then 1 else 0); print_newline ()" n);
|]

(* === Main === *)
let () =
  let num = try int_of_string Sys.argv.(1) with _ -> 20 in
  let seed = try int_of_string Sys.argv.(2) with _ -> 42 in
  let rng = Random.State.make [| seed |] in
  Printf.printf "PBT: %d tests (seed=%d)\n\n%!" num seed;
  let pass = ref 0 and fail = ref 0 and skip = ref 0 in
  with_temp_dir (fun dir ->
    for _ = 1 to num do
      let gen = generators.(Random.State.int rng (Array.length generators)) in
      let source = gen rng in
      Printf.printf "Test: %s\n%!" source;
      match compile_and_run dir source with
      | None -> Printf.printf "  SKIP (compile failed)\n%!"; incr skip
      | Some expected ->
        Printf.printf "  ocamlrun: %S\n%!" expected;
        (try
           let result, output = run_ours (Filename.concat dir "test.byte") in
           Printf.printf "  ours:     %S\n%!" output;
           match result with
           | Finished _ ->
             if output = expected then (Printf.printf "  PASS\n%!"; incr pass)
             else (Printf.printf "  FAIL: output mismatch\n%!"; incr fail)
           | Run_error msg ->
             Printf.printf "  FAIL: %s\n%!" (string_of_chars msg); incr fail
           | Out_of_fuel _ ->
             Printf.printf "  FAIL: out of fuel\n%!"; incr fail
         with exn ->
           Printf.printf "  FAIL: %s\n%!" (Printexc.to_string exn); incr fail)
    done);
  Printf.printf "\n=== Results: %d pass, %d fail, %d skip ===\n" !pass !fail !skip;
  if !fail > 0 then exit 1
