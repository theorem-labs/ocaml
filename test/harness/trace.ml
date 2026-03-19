(* trace.ml - Standalone execution tracer *)
open Interp_extracted

let rec show_value = function
  | Val_int n -> Printf.sprintf "%d" n
  | Val_block (t, fs) -> Printf.sprintf "Block(%d,[%s]%s)" t
      (String.concat ";" (List.map show_value (List.filteri (fun i _ -> i < 5) fs)))
      (if List.length fs > 5 then Printf.sprintf "...+%d" (List.length fs - 5) else "")

let string_of_chars cl =
  let buf = Buffer.create (List.length cl) in
  List.iter (Buffer.add_char buf) cl; Buffer.contents buf

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

let () =
  let data = Loader.read_file Sys.argv.(1) in
  let sections = Loader.parse_sections data in
  let code = Loader.load_bytecode_from_sections data sections in
  let globals = match Loader.find_section sections "DATA" with
    | None -> [||]
    | Some s ->
      let obj : Obj.t = Marshal.from_bytes (Bytes.sub data s.offset s.length) 0 in
      Array.map obj_to_value (Obj.obj obj : Obj.t array) in
  let prims = match Loader.find_section sections "PRIM" with
    | None -> [||]
    | Some s ->
      let raw = Bytes.sub_string data s.offset s.length in
      Array.of_list (List.filter (fun s -> String.length s > 0) (String.split_on_char '\000' raw)) in
  Printf.printf "Code: %d instrs, Globals: %d, Prims: %d\n%!" (List.length code) (Array.length globals) (Array.length prims);
  (* Show first few globals *)
  for i = 0 to min 5 (Array.length globals - 1) do
    Printf.printf "  global[%d] = %s\n%!" i (show_value globals.(i))
  done;
  let buf = Buffer.create 256 in
  let handler idx args =
    let name = if idx < Array.length prims then prims.(idx) else "?" in
    Printf.printf "    C_CALL %s (idx=%d)\n%!" name idx;
    match name, args with
    | "caml_ml_output_char", [_; Val_int c] ->
      Buffer.add_char buf (Char.chr (c land 0xFF)); Some (Val_int 0)
    | ("caml_ml_output_bytes" | "caml_ml_output"), _ ->
      (match args with
       | [_; Val_block (252, chars); Val_int off; Val_int len] ->
         for i = off to off + len - 1 do
           match List.nth_opt chars i with
           | Some (Val_int c) -> Buffer.add_char buf (Char.chr (c land 0xFF))
           | _ -> () done; Some (Val_int 0)
       | _ -> Some (Val_int 0))
    | "caml_register_named_value", _ -> Some (Val_int 0)
    | "caml_fresh_oo_id", _ -> Some (Val_int 0)
    | "caml_ml_open_descriptor_in", [Val_int fd] -> Some (Val_block (255, [Val_int fd]))
    | "caml_ml_open_descriptor_out", [Val_int fd] -> Some (Val_block (255, [Val_int fd]))
    | "caml_ml_set_channel_name", _ -> Some (Val_int 0)
    | "caml_sys_const_max_wosize", _ -> Some (Val_int ((1 lsl 57) - 1))
    | "caml_sys_const_int_size", _ -> Some (Val_int 63)
    | _ ->
      Printf.eprintf "    [ccall] %s (idx=%d, %d args)\n%!" name idx (List.length args);
      Some (Val_int 0) in
  let s = ref (initial_state (Array.to_list globals)) in
  let max = try int_of_string Sys.argv.(2) with _ -> 30 in
  for i = 0 to max - 1 do
    let instr_str = match List.nth_opt code !s.pc with
      | Some (ACC n) -> Printf.sprintf "ACC %d" n
      | Some PUSH -> "PUSH"
      | Some (PUSHACC n) -> Printf.sprintf "PUSHACC %d" n
      | Some (CONSTINT n) -> Printf.sprintf "CONSTINT %d" n
      | Some (PUSHCONSTINT n) -> Printf.sprintf "PUSHCONSTINT %d" n
      | Some (CLOSURE (nv,ofs)) -> Printf.sprintf "CLOSURE(%d,%d)" nv ofs
      | Some (CLOSUREREC (nf,nv,_)) -> Printf.sprintf "CLOSUREREC(%d,%d)" nf nv
      | Some (BRANCH t) -> Printf.sprintf "BRANCH %d" t
      | Some (BRANCHIF t) -> Printf.sprintf "BRANCHIF %d" t
      | Some (BRANCHIFNOT t) -> Printf.sprintf "BRANCHIFNOT %d" t
      | Some (GETGLOBAL n) -> Printf.sprintf "GETGLOBAL %d" n
      | Some (SETGLOBAL n) -> Printf.sprintf "SETGLOBAL %d" n
      | Some (GETFIELD n) -> Printf.sprintf "GETFIELD %d" n
      | Some (MAKEBLOCK1 t) -> Printf.sprintf "MAKEBLOCK1 %d" t
      | Some (MAKEBLOCK2 t) -> Printf.sprintf "MAKEBLOCK2 %d" t
      | Some (POP n) -> Printf.sprintf "POP %d" n
      | Some (APPLY n) -> Printf.sprintf "APPLY %d" n
      | Some APPLY1 -> "APPLY1"
      | Some (RETURN n) -> Printf.sprintf "RETURN %d" n
      | Some (C_CALL (n,p)) -> Printf.sprintf "C_CALL(%d,%d)" n p
      | Some STOP -> "STOP"
      | Some (GRAB n) -> Printf.sprintf "GRAB %d" n
      | Some RESTART -> "RESTART"
      | Some (ENVACC n) -> Printf.sprintf "ENVACC %d" n
      | Some (PUSHENVACC n) -> Printf.sprintf "PUSHENVACC %d" n
      | Some (OFFSETCLOSURE n) -> Printf.sprintf "OFFSETCLOSURE %d" n
      | Some (PUSHOFFSETCLOSURE n) -> Printf.sprintf "PUSHOFFSETCLOSURE %d" n
      | Some (ATOM n) -> Printf.sprintf "ATOM %d" n
      | Some (PUSHATOM n) -> Printf.sprintf "PUSHATOM %d" n
      | Some (PUSHGETGLOBAL n) -> Printf.sprintf "PUSHGETGLOBAL %d" n
      | Some (PUSHGETGLOBALFIELD (n,p)) -> Printf.sprintf "PUSHGETGLOBALFIELD(%d,%d)" n p
      | Some (GETGLOBALFIELD (n,p)) -> Printf.sprintf "GETGLOBALFIELD(%d,%d)" n p
      | Some (MAKEBLOCK (t,sz)) -> Printf.sprintf "MAKEBLOCK(%d,%d)" t sz
      | Some (SWITCH (nc,nb,_,_)) -> Printf.sprintf "SWITCH(%d,%d)" nc nb
      | Some (CLOSUREREC (nf,nv,_)) -> Printf.sprintf "CLOSUREREC(%d,%d)" nf nv
      | Some (PUSHTRAP t) -> Printf.sprintf "PUSHTRAP %d" t
      | Some POPTRAP -> "POPTRAP"
      | Some (APPTERM (n,s)) -> Printf.sprintf "APPTERM(%d,%d)" n s
      | Some (APPTERM1 s) -> Printf.sprintf "APPTERM1 %d" s
      | Some _ -> "other"
      | None -> Printf.sprintf "OUT_OF_BOUNDS(pc=%d,len=%d)" !s.pc (List.length code)
    in
    Printf.printf "Step %d: pc=%d [%s] stack=%d accu=%s\n%!" i !s.pc instr_str (List.length !s.stack) (show_value !s.accu);
    match step code !s with
    | Step s' -> s := s'
    | Halt v -> Printf.printf "  HALT: %s\nOutput: %S\n" (show_value v) (Buffer.contents buf); exit 0
    | Error msg -> Printf.printf "  ERROR: %s\n" (string_of_chars msg); exit 1
    | CCall_request (idx, args, cont) ->
      match handler idx args with
      | Some v -> s := set_accu cont v
      | None -> Printf.printf "  CCALL FAILED\n"; exit 1
  done;
  Printf.printf "Stopped after %d steps. Output so far: %S\n" max (Buffer.contents buf)
