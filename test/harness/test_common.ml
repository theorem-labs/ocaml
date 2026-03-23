(* test_common.ml - Shared utilities for all PBT test files. *)

open Interp_extracted

let with_temp_dir f =
  let dir = Filename.temp_file "pbt" "" in
  Sys.remove dir; Unix.mkdir dir 0o700;
  Fun.protect ~finally:(fun () ->
    (try Array.iter (fun n -> Sys.remove (Filename.concat dir n)) (Sys.readdir dir) with _ -> ());
    (try Unix.rmdir dir with _ -> ())
  ) (fun () -> f dir)

let compile_and_run_ocamlc dir source =
  let src = Filename.concat dir "test.ml" in
  let exe = Filename.concat dir "test.byte" in
  let oc = open_out src in output_string oc source; close_out oc;
  if Sys.command (Printf.sprintf "ocamlc -o %s %s 2>/dev/null" exe src) <> 0 then None
  else begin
    let ic = Unix.open_process_in (Printf.sprintf "timeout 5 ocamlrun %s 2>/dev/null" exe) in
    let buf = Buffer.create 256 in
    (try while true do Buffer.add_char buf (input_char ic) done with End_of_file -> ());
    ignore (Unix.close_process_in ic);
    Some (Buffer.contents buf)
  end

let compile_ocamlc dir source =
  let src = Filename.concat dir "test.ml" in
  let exe = Filename.concat dir "test.byte" in
  let oc = open_out src in output_string oc source; close_out oc;
  if Sys.command (Printf.sprintf "ocamlc -o %s %s 2>/dev/null" exe src) <> 0 then None
  else Some exe

let cl s = List.init (String.length s) (fun i -> s.[i])
let sc l = let buf = Buffer.create (List.length l) in List.iter (Buffer.add_char buf) l; Buffer.contents buf

let events_to_string events =
  let buf = Buffer.create 64 in
  List.iter (fun c -> Buffer.add_char buf (Char.chr (c land 0xFF))) events;
  Buffer.contents buf

(* Helper: build "print_int(e); print_newline()" *)
let print_int_nl e =
  Exp_seq (Exp_app (Exp_var (cl "print_int"), e),
           Exp_app (Exp_var (cl "print_newline"), Exp_unit))

(* === OCaml bytecode loading helpers === *)

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

(* C-call handler for ocamlc-produced bytecode *)
let make_handler prims buf =
  fun idx args ->
    let name = if idx < Array.length prims then prims.(idx) else "?" in
    match name, args with
    | "caml_ml_output_char", [_; Val_int c] ->
      Buffer.add_char buf (Char.chr (c land 0xFF)); Some (Val_int 0)
    | ("caml_ml_output_bytes" | "caml_ml_output"), _ ->
      let get_chars v = match v with
        | Val_block (252, chars) -> Some chars | _ -> None in
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
    | "caml_ml_open_descriptor_in", [Val_int fd] -> Some (Val_block (255, [Val_int fd]))
    | "caml_ml_open_descriptor_out", [Val_int fd] -> Some (Val_block (255, [Val_int fd]))
    | "caml_ml_set_channel_name", _ -> Some (Val_int 0)
    | "caml_sys_const_max_wosize", _ -> Some (Val_int ((1 lsl 57) - 1))
    | "caml_sys_const_int_size", _ -> Some (Val_int 63)
    | "caml_obj_tag", [Val_block (t, _)] -> Some (Val_int t)
    | "caml_obj_tag", [Val_int _] -> Some (Val_int 1000)
    | ("caml_string_length" | "caml_ml_string_length"), [Val_block (252, cs)] ->
      Some (Val_int (List.length cs))
    | "caml_create_bytes", [Val_int n] ->
      Some (Val_block (252, List.init n (fun _ -> Val_int 0)))
    | ("caml_blit_string" | "caml_blit_bytes"), _ -> Some (Val_int 0)
    | "caml_string_equal", [Val_block (252,a); Val_block (252,b)] ->
      Some (Val_int (if a=b then 1 else 0))
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
    | "caml_ml_out_channels_list", _ -> Some (Val_int 0)
    | "caml_obj_tag", [Val_ptr _] -> Some (Val_int 0)
    | "caml_ml_channel_size", _ -> Some (Val_int 0)
    | "caml_sys_getenv", _ -> Some (Val_int 0)
    | _ -> Some (Val_int 0)

(* Run our compiled bytecode through our interpreter *)
let run_our_compiler prog =
  let code = compile_program prog in
  let buf = Buffer.create 64 in
  let handler idx args =
    match idx, args with
    | 0, [Val_int n] ->
      let s = string_of_int n in
      String.iter (fun c -> Buffer.add_char buf c) s;
      Some (Val_int 0)
    | 1, [_] ->
      Buffer.add_char buf '\n';
      Some (Val_int 0)
    | _ -> Some (Val_int 0)
  in
  let s = ref (initial_state []) in
  let remaining = ref 1000000 in
  let result = ref None in
  let rec loop () =
    if !remaining <= 0 then result := Some "timeout"
    else begin
      decr remaining;
      match step code !s with
      | Step s' -> s := s'; loop ()
      | Halt _ -> ()
      | Error msg -> result := Some (sc msg)
      | CCall_request (idx, args, cont) ->
        (match handler idx args with
         | Some v -> s := set_accu cont v; loop ()
         | None -> result := Some "ccall failed")
    end
  in
  loop ();
  match !result with
  | None -> Ok (Buffer.contents buf)
  | Some err -> Error err

(* Run ocamlc bytecode through our interpreter *)
let run_ocamlc_bytecode exe_file =
  let data = Loader.read_file exe_file in
  let sections = Loader.parse_sections data in
  let code = Loader.load_bytecode_from_sections data sections in
  let globals = Array.to_list (load_globals data sections) in
  let prims = load_prims data sections in
  let buf = Buffer.create 256 in
  let handler = make_handler prims buf in
  let s = ref (initial_state globals) in
  let remaining = ref 10000000 in
  let result = ref None in
  let rec loop () =
    if !remaining <= 0 then result := Some "timeout"
    else begin
      decr remaining;
      match step code !s with
      | Step s' -> s := s'; loop ()
      | Halt _ -> ()
      | Error msg -> result := Some (sc msg)
      | CCall_request (idx, args, cont) ->
        (match handler idx args with
         | Some v -> s := set_accu cont v; loop ()
         | None -> result := Some "ccall failed")
    end
  in
  loop ();
  match !result with
  | None -> Ok (Buffer.contents buf)
  | Some err -> Error err
