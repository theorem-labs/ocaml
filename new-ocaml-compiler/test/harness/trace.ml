(* trace.ml - Standalone execution tracer *)
open Interp_extracted

let rec show_value = function
  | Val_int n -> Printf.sprintf "%d" n
  | Val_block (t, fs) -> Printf.sprintf "Block(%d,[%s]%s)" t
      (String.concat ";" (List.map show_value (List.filteri (fun i _ -> i < 5) fs)))
      (if List.length fs > 5 then Printf.sprintf "...+%d" (List.length fs - 5) else "")
  | Val_ptr a -> Printf.sprintf "Ptr(%d)" a
  | Val_closure (a, o) -> Printf.sprintf "Clos(%d+%d)" a o

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
  let verbose = Array.length Sys.argv > 3 && Sys.argv.(3) = "-v" in
  let (heap_ref, next_addr_ref, pending_raise_ref, _perform_raise, base_handler, _get_named_value) = Test_common.make_handler ~raw_globals:globals prims buf in
  let handler idx args cont =
    let name = if idx < Array.length prims then prims.(idx) else "?" in
    if verbose then Printf.printf "    C_CALL %s (idx=%d)\n%!" name idx;
    heap_ref := cont.hp;
    next_addr_ref := cont.next_addr;
    pending_raise_ref := None;
    let result = base_handler idx args in
    (if verbose && result = None then
      Printf.eprintf "    [ccall failed] %s\n%!" name);
    result
  in
  let s = ref (initial_state (Array.to_list globals)) in
  let max = try int_of_string Sys.argv.(2) with _ -> 30 in
  (* If max is very large (>1M), run silently until error or halt *)
  let silent = max > 1000 in
  (* Track trap_sp changes *)
  let prev_trap_sp = ref 0 in
  let i = ref 0 in
  while !i < max do
    incr i;
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
      | Some ULTINT -> "ULTINT"
      | Some UGEINT -> "UGEINT"
      | Some (BULTINT (n,t)) -> Printf.sprintf "BULTINT(%d,%d)" (Z.to_nat n) (Z.to_nat t)
      | Some (BUGEINT (n,t)) -> Printf.sprintf "BUGEINT(%d,%d)" (Z.to_nat n) (Z.to_nat t)
      | Some (OFFSETINT n) -> Printf.sprintf "OFFSETINT %d" (Z.to_nat n)
      | Some DIVINT -> "DIVINT"
      | Some ADDINT -> "ADDINT"
      | Some SUBINT -> "SUBINT"
      | Some MULINT -> "MULINT"
      | Some EQ -> "EQ"
      | Some NEQ -> "NEQ"
      | Some LTINT -> "LTINT"
      | Some GEINT -> "GEINT"
      | Some GTINT -> "GTINT"
      | Some LEINT -> "LEINT"
      | Some ISINT -> "ISINT"
      | Some NEGINT -> "NEGINT"
      | Some RAISE -> "RAISE"
      | Some RERAISE -> "RERAISE"
      | Some RAISE_NOTRACE -> "RAISE_NOTRACE"
      | Some _ -> "other"
      | None -> Printf.sprintf "OUT_OF_BOUNDS(pc=%d,len=%d)" !s.pc (List.length code)
    in
    let cur_trap = !s.trap_sp in
    if cur_trap <> !prev_trap_sp then begin
      Printf.printf "  [trap_sp: %d -> %d at step %d pc=%d]\n%!" !prev_trap_sp cur_trap !i !s.pc;
      prev_trap_sp := cur_trap
    end;
    if not silent then
      Printf.printf "Step %d: pc=%d [%s] stack=%d accu=%s trap=%d\n%!" !i !s.pc instr_str (List.length !s.stack) (show_value !s.accu) cur_trap;
    (match step code !s with
    | Step s' -> s := s'
    | Halt v ->
      Printf.printf "Step %d: HALT: %s\nOutput: %S\n" !i (show_value v) (Buffer.contents buf); exit 0
    | Error msg ->
      Printf.printf "Step %d: pc=%d [%s] ERROR: %s\nAccu: %s\nStack top: %s\ntrap_sp: %d\nstack_len: %d\n"
        !i !s.pc instr_str (string_of_chars msg)
        (show_value !s.accu)
        (match !s.stack with v :: _ -> show_value v | [] -> "empty")
        !s.trap_sp
        (List.length !s.stack);
      exit 1
    | CCall_request (idx, args, cont) ->
      (match handler idx args cont with
      | Some v ->
        s := { (set_accu cont v) with
               hp = !heap_ref; next_addr = !next_addr_ref }
      | None ->
        (match !pending_raise_ref with
         | Some exn ->
           let cont' = { cont with hp = !heap_ref; next_addr = !next_addr_ref } in
           (match _perform_raise cont' exn with
            | Step s' -> s := s'
            | Halt v -> Printf.printf "Step %d: HALT: %s\nOutput: %S\n" !i (show_value v) (Buffer.contents buf); exit 0
            | Error msg ->
              Printf.printf "Step %d: RAISE ERROR: %s\n" !i (string_of_chars msg); exit 1
            | CCall_request _ -> Printf.printf "Step %d: NESTED CCALL IN RAISE\n" !i; exit 1)
         | None -> Printf.printf "Step %d: CCALL FAILED\n" !i; exit 1)));
    if silent && !i mod 100000 = 0 then
      Printf.eprintf "... %d steps, pc=%d\n%!" !i !s.pc
  done;
  Printf.printf "Stopped after %d steps. Output so far: %S\n" max (Buffer.contents buf)
