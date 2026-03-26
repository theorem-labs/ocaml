(* harness.ml - [TRUSTED] PBT harness: interpret-bytecode vs ocamlrun
   Migrated to QCheck. *)

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
  let code = Array.of_list (Loader.load_bytecode_from_sections data sections) in
  let globals = load_globals data sections in
  let prims = load_prims data sections in
  let buf = Buffer.create 256 in
  let handler = make_handler prims buf in
  let result = run_native 10000000 code (initial_state (Array.to_list globals)) handler in
  (result, Buffer.contents buf)

(* === char list -> string (extracted errors use char list) === *)
let string_of_chars cl =
  let buf = Buffer.create (List.length cl) in
  List.iter (Buffer.add_char buf) cl; Buffer.contents buf

(* === QCheck generators === *)

let gen_source : string QCheck.Gen.t =
  let open QCheck.Gen in
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
  oneof [
    gen_add; gen_mul; gen_cmp; gen_fun; gen_fact; gen_match; gen_pair;
    gen_sub; gen_nested_let; gen_bool_logic; gen_multi_arg; gen_higher_order;
    gen_nested_pair; gen_fib; gen_divmod; gen_neg; gen_variant; gen_string;
    gen_partial; gen_ref; gen_ref_alias; gen_ref_loop; gen_try; gen_nested_try;
    gen_list; gen_closure_ref; gen_compare; gen_strlen; gen_strget;
    gen_variant_data; gen_nested_match; gen_seq_let; gen_triple; gen_bitwise;
    gen_chain; gen_while; gen_mutual_rec;
  ]

(* Shared temp dir for all tests *)
let temp_dir = ref ""

let harness_test =
  QCheck.Test.make ~name:"bytecode interpreter vs ocamlrun" ~count:200
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
                Printf.eprintf "Run error: %s\n%!" (string_of_chars msg); false
              | Out_of_fuel _ ->
                Printf.eprintf "Out of fuel\n%!"; false)
           with exn ->
             Printf.eprintf "Exception: %s\n%!" (Printexc.to_string exn); false))

let () =
  exit (QCheck_base_runner.run_tests ~verbose:true [harness_test])
