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
    else if tag = Obj.double_tag then
      let f : float = Obj.obj obj in
      let bits = Int64.bits_of_float f in
      let lo = Int64.(to_int (logand bits 0xFFFFFFFFL)) in
      let hi = Int64.(to_int (shift_right_logical bits 32)) in
      Val_block (253, [Val_int lo; Val_int hi])
    else if tag = Obj.double_array_tag then
      (* Float array: each element is a separate double *)
      Val_block (254, List.init size (fun i ->
        let f : float = Obj.double_field obj i in
        let bits = Int64.bits_of_float f in
        let lo = Int64.(to_int (logand bits 0xFFFFFFFFL)) in
        let hi = Int64.(to_int (shift_right_logical bits 32)) in
        Val_block (253, [Val_int lo; Val_int hi])))
    else if tag = Obj.custom_tag then
      (* Custom blocks: Int32, Int64, Nativeint.
         Distinguish by the identifier byte at offset 22 in their marshal representation. *)
      (let bytes = Marshal.to_bytes (Obj.obj obj : Obj.t) [] in
       if Bytes.length bytes >= 23 then
         match Bytes.get bytes 22 with
         | 'j' ->  (* Int64: '_j' identifier *)
           let v : int64 = Obj.obj obj in
           Val_block (1002, [Val_int Int64.(to_int (logand v 0xFFFFFFFFL));
                              Val_int Int64.(to_int (shift_right_logical v 32))])
         | 'i' ->  (* Int32: '_i' identifier *)
           let v : int32 = Obj.obj obj in
           Val_block (1001, [Val_int (Int32.to_int v)])
         | 'n' ->  (* Nativeint: '_n' identifier - use two-word format like int64 for full 64-bit range *)
           let v : nativeint = Obj.obj obj in
           let v64 = Int64.of_nativeint v in
           Val_block (1003, [Val_int Int64.(to_int (logand v64 0xFFFFFFFFL));
                              Val_int Int64.(to_int (shift_right_logical v64 32))])
         | _ -> Val_block (tag, [])
       else Val_block (tag, []))
    else if tag < Obj.no_scan_tag then
      Val_block (tag, List.init size (fun i -> obj_to_value (Obj.field obj i)))
    else Val_block (tag, [])

let load_globals data sections =
  match Loader.find_section sections "DATA" with
  | None -> [||]
  | Some s ->
    let obj : Obj.t = Marshal.from_bytes (Bytes.sub data s.offset s.length) 0 in
    Array.map obj_to_value (Obj.obj obj : Obj.t array)

(* Convert globals so that mutable block values are heap-allocated (Val_ptr).
   Returns (globals_list, initial_heap, initial_next_addr).
   Strings (252), floats (253), float arrays (254), exception descriptors (248)
   are kept as Val_block (they're logically immutable or small).
   Regular blocks (tag 0..246, 250) are heap-allocated so they can be mutated. *)
let heap_allocate_globals globals =
  let heap = ref PositiveMap.empty in
  let next_addr = ref 0 in
  let rec go v =
    match v with
    | Val_block (tag, fields)
      when tag < 247 || tag = 250 || tag = 254 ->
      (* Potentially mutable: allocate on heap so writes work *)
      let fields' = List.map go fields in
      let addr = !next_addr in
      incr next_addr;
      heap := PositiveMap.add (Coq_Pos.of_succ_nat addr) (tag, fields') !heap;
      Val_ptr addr
    | Val_block (tag, fields) ->
      (* Immutable: 248=exn desc, 252=string, 253=float, 1001/1002/1003=boxed int *)
      Val_block (tag, List.map go fields)
    | other -> other
  in
  let globals' = Array.to_list (Array.map go globals) in
  (globals', !heap, !next_addr)

let load_prims data sections =
  match Loader.find_section sections "PRIM" with
  | None -> [||]
  | Some s ->
    let raw = Bytes.sub_string data s.offset s.length in
    Array.of_list (List.filter (fun s -> String.length s > 0) (String.split_on_char '\000' raw))

(* Helpers for building values *)
let string_val s = Val_block (252, List.init (String.length s) (fun i -> Val_int (Char.code s.[i])))
let tuple_val fields = Val_block (0, fields)

(* Float representation: Val_block(253, [Val_int lo32; Val_int hi32]) *)
let float_to_val f =
  let bits = Int64.bits_of_float f in
  let lo = Int64.(to_int (logand bits 0xFFFFFFFFL)) in
  let hi = Int64.(to_int (shift_right_logical bits 32)) in
  Val_block (253, [Val_int lo; Val_int hi])

let val_to_float v =
  match v with
  | Val_block (253, [Val_int lo; Val_int hi]) ->
    let bits = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL)
                            (shift_left (of_int hi) 32)) in
    Int64.float_of_bits bits
  | Val_block (253, [Val_int bits]) ->  (* alternative 1-word encoding *)
    Int64.float_of_bits (Int64.of_int bits)
  | _ -> 0.0

let float_binop f a b =
  Some (float_to_val (f (val_to_float a) (val_to_float b)))
let float_unop f a =
  Some (float_to_val (f (val_to_float a)))

(* Deep structural comparison: handles Val_ptr (heap objects) vs Val_block (globals).
   Uses total order semantics (for caml_compare): NaN = NaN. *)
let rec deep_compare heap a b =
  let resolve v = match v with
    | Val_ptr addr ->
      (match heap_lookup heap addr with
       | Some (t, fs) -> `Block (t, fs)
       | None -> `Other v)
    | Val_block (t, fs) -> `Block (t, fs)
    | Val_int n -> `Int n
    | Val_closure _ -> `Closure v
    | _ -> `Other v
  in
  match resolve a, resolve b with
  | `Int n, `Int m -> Int.compare n m
  | `Int _, _ -> -1
  | _, `Int _ -> 1
  | `Block (253, fs1), `Block (253, fs2) ->
    (* Float comparison by total order: NaN = NaN, NaN < -infinity in OCaml total order *)
    let f1 = val_to_float (Val_block (253, fs1)) in
    let f2 = val_to_float (Val_block (253, fs2)) in
    compare f1 f2
  | `Block (t1, [Val_int lo1; Val_int hi1]), `Block (t2, [Val_int lo2; Val_int hi2])
    when (t1 = 1002 || t1 = 1003) && t1 = t2 ->
    (* Int64/nativeint: compare as signed 64-bit integer *)
    let v1 = Int64.(logor (logand (of_int lo1) 0xFFFFFFFFL) (shift_left (of_int hi1) 32)) in
    let v2 = Int64.(logor (logand (of_int lo2) 0xFFFFFFFFL) (shift_left (of_int hi2) 32)) in
    Int64.compare v1 v2
  | `Block (t1, fs1), `Block (t2, fs2) ->
    let c = Int.compare t1 t2 in
    if c <> 0 then c
    else list_compare heap fs1 fs2
  | `Block _, _ -> -1
  | _, `Block _ -> 1
  | `Closure _, _ | _, `Closure _ -> raise Exit  (* sentinel: will be caught and converted to Invalid_argument *)
  | `Other v1, `Other v2 -> if v1 = v2 then 0 else 1
and list_compare heap l1 l2 = match l1, l2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x :: xs, y :: ys ->
    let c = deep_compare heap x y in
    if c <> 0 then c else list_compare heap xs ys

(* IEEE-mode equality for floats (NaN != NaN). Used by caml_equal/caml_notequal etc. *)
let rec deep_equal_ieee heap a b =
  let resolve v = match v with
    | Val_ptr addr ->
      (match heap_lookup heap addr with
       | Some (t, fs) -> `Block (t, fs)
       | None -> `Other v)
    | Val_block (t, fs) -> `Block (t, fs)
    | Val_int n -> `Int n
    | Val_closure _ -> `Closure v
    | _ -> `Other v
  in
  match resolve a, resolve b with
  | `Closure _, _ | _, `Closure _ -> raise Exit  (* sentinel *)
  | `Int n, `Int m -> n = m
  | `Int _, _ | _, `Int _ -> false
  | `Block (253, fs1), `Block (253, fs2) ->
    (* IEEE semantics: NaN != NaN *)
    let f1 = val_to_float (Val_block (253, fs1)) in
    let f2 = val_to_float (Val_block (253, fs2)) in
    f1 = f2  (* OCaml float = follows IEEE: nan = nan is false *)
  | `Block (t1, [Val_int lo1; Val_int hi1]), `Block (t2, [Val_int lo2; Val_int hi2])
    when (t1 = 1002 || t1 = 1003) && t1 = t2 ->
    (* Int64/nativeint equality: compare as 64-bit integers *)
    lo1 = lo2 && hi1 = hi2
  | `Block (t1, fs1), `Block (t2, fs2) ->
    t1 = t2 && list_equal_ieee heap fs1 fs2
  | `Block _, _ | _, `Block _ -> false
  | `Other v1, `Other v2 -> v1 = v2
and list_equal_ieee heap l1 l2 = match l1, l2 with
  | [], [] -> true
  | [], _ | _, [] -> false
  | x :: xs, y :: ys ->
    deep_equal_ieee heap x y && list_equal_ieee heap xs ys

(* IEEE comparison (for caml_lessthan etc.): NaN comparisons return false.
   Returns None if either operand is NaN or a closure (comparison is undefined/raises). *)
let rec deep_compare_ieee heap a b =
  let resolve v = match v with
    | Val_ptr addr ->
      (match heap_lookup heap addr with
       | Some (t, fs) -> `Block (t, fs)
       | None -> `Other v)
    | Val_block (t, fs) -> `Block (t, fs)
    | Val_int n -> `Int n
    | Val_closure _ -> `Closure v
    | _ -> `Other v
  in
  match resolve a, resolve b with
  | `Closure _, _ | _, `Closure _ -> raise Exit  (* will be caught -> Invalid_argument *)
  | `Int n, `Int m -> Some (Int.compare n m)
  | `Int _, _ -> Some (-1)
  | _, `Int _ -> Some 1
  | `Block (253, fs1), `Block (253, fs2) ->
    let f1 = val_to_float (Val_block (253, fs1)) in
    let f2 = val_to_float (Val_block (253, fs2)) in
    (* IEEE: NaN comparisons return unordered (None) *)
    if Float.is_nan f1 || Float.is_nan f2 then None
    else Some (compare f1 f2)
  | `Block (t1, [Val_int lo1; Val_int hi1]), `Block (t2, [Val_int lo2; Val_int hi2])
    when (t1 = 1002 || t1 = 1003) && t1 = t2 ->
    (* Int64/nativeint: compare as signed 64-bit integer *)
    let v1 = Int64.(logor (logand (of_int lo1) 0xFFFFFFFFL) (shift_left (of_int hi1) 32)) in
    let v2 = Int64.(logor (logand (of_int lo2) 0xFFFFFFFFL) (shift_left (of_int hi2) 32)) in
    Some (Int64.compare v1 v2)
  | `Block (t1, fs1), `Block (t2, fs2) ->
    let c = Int.compare t1 t2 in
    if c <> 0 then Some c
    else
      let rec compare_list l1 l2 = match l1, l2 with
        | [], [] -> Some 0
        | [], _ -> Some (-1)
        | _, [] -> Some 1
        | x :: xs, y :: ys ->
          (match deep_compare_ieee heap x y with
           | Some 0 -> compare_list xs ys
           | r -> r)
      in
      compare_list fs1 fs2
  | `Block _, _ -> Some (-1)
  | _, `Block _ -> Some 1
  | `Other v1, `Other v2 -> Some (if v1 = v2 then 0 else 1)

let deep_equal heap a b =
  try deep_compare heap a b = 0
  with Exit -> false  (* closures: treat as not-equal in total order context *)

(* Resolve a value to string char list, dereferencing Val_ptr if needed. *)
let resolve_string heap v =
  match v with
  | Val_block (252, cs) -> Some cs
  | Val_ptr addr ->
    (match heap_lookup heap addr with
     | Some (252, cs) -> Some cs
     | _ -> None)
  | _ -> None

(* C-call handler for ocamlc-produced bytecode.
   heap_ref and next_addr_ref are updated before each call;
   handlers may also write new allocations back to heap_ref/next_addr_ref. *)
let make_handler ?(raw_globals=[||]) prims buf =
  let heap_ref : heap ref = ref PositiveMap.empty in
  let next_addr_ref = ref 0 in
  (* Build a lookup table from exception name -> descriptor Val_block(248,...).
     Searches raw_globals for Val_block(248, [Val_block(252, chars); slot]) entries. *)
  let find_exn_desc name =
    let found = ref None in
    Array.iter (fun v ->
      match v with
      | Val_block (248, ((Val_block (252, chars)) :: _)) ->
        let n = String.init (List.length chars) (fun i ->
          match List.nth_opt chars i with
          | Some (Val_int c) -> Char.chr (c land 0xFF)
          | _ -> '\000') in
        if n = name then found := Some v
      | _ -> ()
    ) raw_globals;
    !found
  in
  (* Get or fallback exception descriptor for a given name with a fallback slot *)
  let exn_desc name fallback_slot =
    match find_exn_desc name with
    | Some d -> d
    | None -> Val_block (248, [string_val name; Val_int fallback_slot])
  in
  (* Allocate a new block on the interpreter heap (via heap_ref/next_addr_ref).
     Returns a Val_ptr pointing to the new block. *)
  let heap_alloc_local tag fields =
    let addr = !next_addr_ref in
    next_addr_ref := addr + 1;
    heap_ref := PositiveMap.add (Coq_Pos.of_succ_nat addr) (tag, fields) !heap_ref;
    Val_ptr addr
  in
  (* Update fields of an existing heap object. *)
  let heap_update_local addr new_fields =
    heap_ref := heap_update !heap_ref addr new_fields
  in
  (* Resolve a value as a char list (string content):
     Val_block(252,...) or Val_ptr pointing to a tag-252 heap block. *)
  let resolve_string_or_bytes heap v =
    match v with
    | Val_ptr addr ->
      (match heap_lookup heap addr with
       | Some (252, cs) -> Some cs
       | _ -> None)
    | _ -> resolve_string heap v
  in
  (* Named values table: stores values registered via caml_register_named_value *)
  let named_values : (string, value) Hashtbl.t = Hashtbl.create 16 in
  let get_named_value name = Hashtbl.find_opt named_values name in

  (* When a C call needs to raise an exception, it sets this ref and returns None. *)
  let pending_raise_ref : value option ref = ref None in
  let ccall_raise exn = pending_raise_ref := Some exn; None in

  (* Perform RAISE logic: find trap frame on stack, jump to handler *)
  let perform_raise s exn =
    if s.trap_sp = 0 then
      Error (cl "unhandled exception")
    else
      let k = List.length s.stack - s.trap_sp in
      let frame_top = List.filteri (fun i _ -> i >= k) s.stack in
      match frame_top with
      | Val_int handler_pc :: Val_int prev_tsp :: saved_env :: Val_int saved_ea :: rest ->
        Step { s with pc = handler_pc; accu = exn; stack = rest;
               env = saved_env; extra_args = saved_ea; trap_sp = prev_tsp }
      | _ -> Error (cl "RAISE: malformed trap frame (from ccall)")
  in

  let handler idx args =
    let name = if idx < Array.length prims then prims.(idx) else "?" in
    let heap = !heap_ref in
    match name, args with
    (* --- Output --- *)
    | "caml_ml_output_char", [_; Val_int c] ->
      Buffer.add_char buf (Char.chr (c land 0xFF)); Some (Val_int 0)
    | ("caml_ml_output_bytes" | "caml_ml_output"), _ ->
      (match args with
       | [_; sv; Val_int off; Val_int len] ->
         (match resolve_string_or_bytes heap sv with
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
    (* --- Channel management --- *)
    | "caml_ml_open_descriptor_in", [Val_int fd] -> Some (Val_block (255, [Val_int fd]))
    | "caml_ml_open_descriptor_out", [Val_int fd] -> Some (Val_block (255, [Val_int fd]))
    | "caml_ml_set_channel_name", _ -> Some (Val_int 0)
    | "caml_ml_out_channels_list", _ -> Some (Val_int 0)
    | "caml_ml_channel_size", _ -> Some (Val_int 0)
    | "caml_ml_channel_size_64", _ -> Some (Val_int 0)
    | ("caml_ml_input" | "caml_ml_input_char" | "caml_ml_input_int"), _ -> Some (Val_int 0)
    (* --- System info --- *)
    | "caml_sys_get_config", _ ->
      (* Returns (os_type: string, word_size: int, big_endian: bool) *)
      Some (tuple_val [string_val "Unix"; Val_int 64; Val_int 0])
    | "caml_sys_executable_name", _ -> Some (string_val "<test>")
    | "caml_sys_argv", _ -> Some (Val_block (0, [string_val "<test>"]))
    | "caml_sys_const_max_wosize", _ -> Some (Val_int ((1 lsl 57) - 1))
    | "caml_sys_const_int_size", _ -> Some (Val_int 63)
    | "caml_sys_const_word_size", _ -> Some (Val_int 64)
    | "caml_sys_const_big_endian", _ -> Some (Val_int 0)
    | "caml_sys_const_ostype_unix", _ -> Some (Val_int 1)
    | "caml_sys_const_ostype_win32", _ -> Some (Val_int 0)
    | "caml_sys_const_ostype_cygwin", _ -> Some (Val_int 0)
    | "caml_sys_const_naked_pointers_checked", _ -> Some (Val_int 0)
    | "caml_sys_const_backend_type", _ ->
      (* Sys.backend_type: Native=Val_int 0, Bytecode=Val_int 1, Other s=Val_block(0,[s]) *)
      Some (Val_int 1)
    | "caml_sys_getenv", [sv] ->
      (* Try system env if arg is a string, else raise Not_found *)
      let varname = match resolve_string heap sv with
        | Some cs -> Some (String.init (List.length cs) (fun i ->
            match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000'))
        | None -> None
      in
      (match varname with
       | Some name ->
         (match Sys.getenv_opt name with
          | Some v -> Some (string_val v)
          | None ->
            ccall_raise (exn_desc "Not_found" (-7)))
       | None ->
         ccall_raise (exn_desc "Not_found" (-7)))
    | "caml_sys_getenv", _ -> None  (* fallback *)
    | "caml_sys_get_argv", _ -> Some (tuple_val [string_val "<test>"; Val_block (0, [string_val "<test>"])])
    | "caml_sys_time", _ -> Some (Val_int 0)
    | "caml_sys_random_seed", _ ->
      let t = int_of_float (Unix.gettimeofday () *. 1000000.) in
      Some (Val_block (0, [Val_int t]))
    (* --- GC (stub: return zero floats) --- *)
    | ("caml_gc_counters" | "caml_gc_stat" | "caml_gc_quick_stat"), _ ->
      let zero_float = Val_block (253, [Val_int 0; Val_int 0]) in
      (* Return a record with enough float fields; gc_counters returns 3, gc_stat/quick_stat return more *)
      Some (Val_block (0, List.init 17 (fun _ -> zero_float)))
    | "caml_gc_allocated_bytes", _ ->
      Some (Val_block (253, [Val_int 0; Val_int 0]))
    | ("caml_gc_major" | "caml_gc_minor" | "caml_gc_full_major" | "caml_gc_compact"), _ ->
      Some (Val_int 0)
    (* --- Arrays --- *)
    | ("caml_array_unsafe_get" | "caml_array_get"
      | "caml_array_unsafe_get_addr" | "caml_array_get_addr"), [av; Val_int idx] ->
      let fields = match av with
        | Val_block (_, fs) -> Some fs
        | Val_ptr addr -> (match heap_lookup heap addr with Some (_, fs) -> Some fs | None -> None)
        | _ -> None
      in
      (match fields with
       | Some fs ->
         let len = List.length fs in
         (match name with
          | "caml_array_unsafe_get" | "caml_array_unsafe_get_addr" ->
            Some (match List.nth_opt fs idx with Some v -> v | None -> Val_int 0)
          | _ ->
            if idx < 0 || idx >= len then
              ccall_raise (Val_block (0, [exn_desc "Invalid_argument" (-4);
                                          string_val "index out of bounds"]))
            else
              Some (match List.nth_opt fs idx with Some v -> v | None -> Val_int 0))
       | None -> Some (Val_int 0))
    | ("caml_array_unsafe_set" | "caml_array_set"
      | "caml_array_unsafe_set_addr" | "caml_array_set_addr"), [av; Val_int idx; v] ->
      (match av with
       | Val_ptr addr ->
         (match heap_lookup !heap_ref addr with
          | Some (tag, fields) ->
            let arr = Array.of_list fields in
            if idx >= 0 && idx < Array.length arr then arr.(idx) <- v;
            heap_update_local addr (Array.to_list arr);
            ignore tag
          | None -> ())
       | _ -> ());
      Some (Val_int 0)
    | ("caml_array_unsafe_set" | "caml_array_set"
      | "caml_array_unsafe_set_addr" | "caml_array_set_addr"), _ -> Some (Val_int 0)
    | "caml_make_vect", [Val_int n; init] ->
      Some (heap_alloc_local 0 (List.init n (fun _ -> init)))
    | "caml_make_array", [v] -> Some v  (* Already an array *)
    | "caml_array_length", [av] | "caml_ml_array_length", [av] ->
      let n = match av with
        | Val_block (_, fs) -> List.length fs
        | Val_ptr addr -> (match heap_lookup heap addr with Some (_, fs) -> List.length fs | None -> 0)
        | _ -> 0
      in Some (Val_int n)
    | "caml_array_append", [a; b] ->
      let get_tag_and_fields v = match v with
        | Val_block (t, fs) -> (t, fs)
        | Val_ptr addr -> (match heap_lookup heap addr with Some (t, fs) -> (t, fs) | None -> (0, []))
        | _ -> (0, [])
      in
      let (ta, fa) = get_tag_and_fields a in
      let (_, fb) = get_tag_and_fields b in
      Some (heap_alloc_local ta (fa @ fb))
    | "caml_array_concat", [lst] ->
      (* lst is a list of arrays; concatenate their fields *)
      let get_tag_and_fields v = match v with
        | Val_block (t, fs) -> (t, fs)
        | Val_ptr a -> (match heap_lookup heap a with Some (t, fs) -> (t, fs) | None -> (0, []))
        | _ -> (0, [])
      in
      let rec collect = function
        | Val_int 0 -> (0, [])
        | Val_block (0, [hd; tl]) ->
          let (t, fh) = get_tag_and_fields hd in
          let (_, ft) = collect tl in
          (t, fh @ ft)
        | Val_ptr addr ->
          (match heap_lookup heap addr with
           | Some (_, [hd; tl]) ->
             let (t, fh) = get_tag_and_fields hd in
             let (_, ft) = collect tl in
             (t, fh @ ft)
           | _ -> (0, []))
        | _ -> (0, [])
      in
      let (tag, fields) = collect lst in
      Some (heap_alloc_local tag fields)
    | "caml_array_sub", [av; Val_int ofs; Val_int len] ->
      let (tag, fields) = match av with
        | Val_block (t, fs) -> (t, fs)
        | Val_ptr addr -> (match heap_lookup heap addr with Some (t, fs) -> (t, fs) | None -> (0, []))
        | _ -> (0, [])
      in
      Some (heap_alloc_local tag (List.filteri (fun i _ -> i >= ofs && i < ofs + len) fields))
    | "caml_array_blit", [src; Val_int src_off; dst; Val_int dst_off; Val_int len] ->
      let src_fs = match src with
        | Val_block (_, fs) -> fs
        | Val_ptr a -> (match heap_lookup heap a with Some (_, fs) -> fs | None -> [])
        | _ -> []
      in
      (match dst with
       | Val_ptr addr ->
         (match heap_lookup !heap_ref addr with
          | Some (tag, fields) ->
            let arr = Array.of_list fields in
            for k = 0 to len - 1 do
              (match List.nth_opt src_fs (src_off + k) with
               | Some v -> if dst_off + k < Array.length arr then arr.(dst_off + k) <- v
               | None -> ())
            done;
            heap_update_local addr (Array.to_list arr);
            ignore tag
          | None -> ())
       | _ -> ());
      Some (Val_int 0)
    | "caml_array_blit", _ -> Some (Val_int 0)
    (* --- Float array primitives --- *)
    | ("caml_floatarray_unsafe_get" | "caml_floatarray_get"), [av; Val_int idx] ->
      let fields = match av with
        | Val_block (_, fs) -> Some fs
        | Val_ptr addr -> (match heap_lookup heap addr with Some (_, fs) -> Some fs | None -> None)
        | _ -> None
      in
      (match fields with
       | Some fs -> Some (match List.nth_opt fs idx with Some v -> v | None -> float_to_val 0.0)
       | None -> Some (float_to_val 0.0))
    | ("caml_floatarray_unsafe_set" | "caml_floatarray_set"), [av; Val_int idx; v] ->
      (match av with
       | Val_ptr addr ->
         (match heap_lookup !heap_ref addr with
          | Some (tag, fields) ->
            let arr = Array.of_list fields in
            if idx >= 0 && idx < Array.length arr then arr.(idx) <- v;
            heap_update_local addr (Array.to_list arr);
            ignore tag
          | None -> ())
       | _ -> ());
      Some (Val_int 0)
    | ("caml_floatarray_unsafe_set" | "caml_floatarray_set"), _ -> Some (Val_int 0)
    (* --- Obj module extras --- *)
    | "caml_alloc_dummy", [Val_int n] ->
      Some (heap_alloc_local 0 (List.init n (fun _ -> Val_int 0)))
    | "caml_alloc_dummy_function", [Val_int n; _] ->
      Some (heap_alloc_local 0 (List.init n (fun _ -> Val_int 0)))
    | "caml_update_dummy", [dst; src] ->
      (* Copy fields from src into dst block in place *)
      let src_fields = match src with
        | Val_block (_, fs) -> Some fs
        | Val_ptr addr -> (match heap_lookup heap addr with Some (_, fs) -> Some fs | None -> None)
        | _ -> None
      in
      let src_tag = match src with
        | Val_block (t, _) -> t
        | Val_ptr a -> (match heap_lookup heap a with Some (t, _) -> t | None -> 0)
        | _ -> 0
      in
      (match dst with
       | Val_ptr addr ->
         (match src_fields with
          | Some new_fs ->
            (match heap_lookup !heap_ref addr with
             | Some (_old_t, old_fs) ->
               heap_ref := PositiveMap.add (Coq_Pos.of_succ_nat addr)
                 (src_tag, new_fs @ List.filteri (fun i _ -> i >= List.length new_fs) old_fs)
                 !heap_ref
             | None -> ())
          | None -> ())
       | _ -> ());
      Some (Val_int 0)
    | "caml_obj_make_forward", [blk; v] ->
      (* Forward pointer: update block to become a forward (tag 250) pointing to v *)
      (match blk with
       | Val_ptr addr ->
         (match heap_lookup !heap_ref addr with
          | Some (_, fs) ->
            heap_ref := PositiveMap.add (Coq_Pos.of_succ_nat addr)
              (250, [v] @ List.filteri (fun i _ -> i >= 1) fs) !heap_ref
          | None -> ())
       | _ -> ());
      Some (Val_int 0)
    (* --- Object/Obj module --- *)
    | "caml_obj_tag", [Val_block (t, _)] -> Some (Val_int t)
    | "caml_obj_tag", [Val_int _] -> Some (Val_int 1000)
    | "caml_obj_tag", [Val_ptr addr] ->
      (match heap_lookup heap addr with
       | Some (t, _) -> Some (Val_int t)
       | None -> Some (Val_int 0))
    | "caml_obj_tag", [Val_closure _] -> Some (Val_int 247)
    | "caml_obj_size", [Val_block (_, fs)] -> Some (Val_int (List.length fs))
    | "caml_obj_size", [Val_ptr addr] ->
      (match heap_lookup heap addr with
       | Some (_, fs) -> Some (Val_int (List.length fs))
       | None -> Some (Val_int 0))
    | "caml_obj_size", _ -> Some (Val_int 0)
    | "caml_obj_field", [Val_block (_, fs); Val_int n] ->
      (match List.nth_opt fs n with Some v -> Some v | None -> Some (Val_int 0))
    | "caml_obj_field", [Val_ptr addr; Val_int n] ->
      (match heap_lookup heap addr with
       | Some (_, fs) -> (match List.nth_opt fs n with Some v -> Some v | None -> Some (Val_int 0))
       | None -> Some (Val_int 0))
    | "caml_obj_set_field", _ -> Some (Val_int 0)
    | "caml_obj_block", [Val_int t; Val_int n] ->
      if t >= 255 || (t = 252 && n = 0) then
        ccall_raise (Val_block (0, [exn_desc "Invalid_argument" (-4);
                                    string_val "Obj.new_block"]))
      else
        Some (heap_alloc_local t (List.init n (fun _ -> Val_int 0)))
    | "caml_obj_dup", [v] ->
      (* Duplicate: allocate a fresh copy on heap *)
      (match v with
       | Val_block (tag, fields) ->
         Some (heap_alloc_local tag fields)
       | Val_ptr addr ->
         (match heap_lookup heap addr with
          | Some (tag, fields) -> Some (heap_alloc_local tag fields)
          | None -> Some v)
       | _ -> Some v)
    | "caml_obj_is_block", [Val_int _] -> Some (Val_int 0)
    | "caml_obj_is_block", _ -> Some (Val_int 1)
    | "caml_fresh_oo_id", [_] ->
      let id = !next_addr_ref in next_addr_ref := id + 1; Some (Val_int id)
    | "caml_set_oo_id", [obj] ->
      (* Sets field 1 of obj to a fresh oo_id and returns obj *)
      let id = !next_addr_ref in next_addr_ref := id + 1;
      (match obj with
       | Val_ptr addr ->
         (match heap_lookup !heap_ref addr with
          | Some (tag, fields) ->
            let arr = Array.of_list fields in
            if Array.length arr >= 2 then arr.(1) <- Val_int id;
            heap_update_local addr (Array.to_list arr);
            ignore tag
          | None -> ())
       | _ -> ());
      Some obj
    | "caml_register_named_value", [name_val; fn_val] ->
      (* Store the named value in our table for use by uncaught exception handler etc. *)
      let name = match resolve_string heap name_val with
        | Some chars -> String.init (List.length chars) (fun i ->
            match List.nth_opt chars i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000')
        | None -> (match name_val with
          | Val_ptr addr -> (match heap_lookup heap addr with
            | Some (252, chars) -> String.init (List.length chars) (fun i ->
                match List.nth_opt chars i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000')
            | _ -> "")
          | _ -> "")
      in
      if name <> "" then Hashtbl.replace named_values name fn_val;
      Some (Val_int 0)
    | "caml_register_named_value", _ -> Some (Val_int 0)
    (* --- Weak arrays / Ephemerons ---
       In OCaml 4.14, both are stored as ephemeron blocks (tag 251).
       Layout: [data(0); extra(1); key0(2); key1(3); ...] (CAML_EPHE_FIRST_KEY=2)
       Weak.length = Obj.size - additional_values (=2)
       caml_weak_create n creates a block of n+2 fields (all initially Val_int 0 = "absent"). *)
    | "caml_weak_create", [Val_int n] ->
      Some (heap_alloc_local 251 (List.init (n + 2) (fun _ -> Val_int 0)))
    | "caml_weak_set", [arr; Val_int i; v] ->
      (* In OCaml 4.14, caml_weak_set may not be used, but handle it anyway *)
      let real_v = match v with
        | Val_block (0, [x]) -> x
        | _ -> Val_int 0
      in
      (match arr with
       | Val_ptr addr ->
         (match heap_lookup !heap_ref addr with
          | Some (tag, fields) ->
            let arr2 = Array.of_list fields in
            if i + 2 >= 0 && i + 2 < Array.length arr2 then arr2.(i + 2) <- real_v;
            heap_update_local addr (Array.to_list arr2);
            ignore tag
          | None -> ())
       | _ -> ());
      Some (Val_int 0)
    | "caml_weak_get", [arr; Val_int i] ->
      (* caml_weak_get = caml_ephe_get_key: slot i + 2 *)
      let fields = match arr with
        | Val_ptr addr -> (match heap_lookup heap addr with Some (_, fs) -> fs | None -> [])
        | Val_block (_, fs) -> fs
        | _ -> []
      in
      let slot = match List.nth_opt fields (i + 2) with Some v -> v | None -> Val_int 0 in
      (match slot with
       | Val_int 0 -> Some (Val_int 0)
       | v -> Some (heap_alloc_local 0 [v]))
    | "caml_weak_get_copy", [arr; Val_int i] ->
      let fields = match arr with
        | Val_ptr addr -> (match heap_lookup heap addr with Some (_, fs) -> fs | None -> [])
        | Val_block (_, fs) -> fs
        | _ -> []
      in
      let slot = match List.nth_opt fields (i + 2) with Some v -> v | None -> Val_int 0 in
      (match slot with
       | Val_int 0 -> Some (Val_int 0)
       | v ->
         let copy = match v with
           | Val_ptr addr -> (match heap_lookup heap addr with
               | Some (tag, fs) -> heap_alloc_local tag fs
               | None -> v)
           | _ -> v
         in
         Some (heap_alloc_local 0 [copy]))
    | "caml_weak_check", [arr; Val_int i] ->
      let fields = match arr with
        | Val_ptr addr -> (match heap_lookup heap addr with Some (_, fs) -> fs | None -> [])
        | Val_block (_, fs) -> fs
        | _ -> []
      in
      let slot = match List.nth_opt fields (i + 2) with Some v -> v | None -> Val_int 0 in
      Some (Val_int (if slot = Val_int 0 then 0 else 1))
    | "caml_weak_blit", [src; Val_int src_off; dst; Val_int dst_off; Val_int len] ->
      let src_fields = match src with
        | Val_ptr addr -> (match heap_lookup heap addr with Some (_, fs) -> fs | None -> [])
        | Val_block (_, fs) -> fs
        | _ -> []
      in
      (match dst with
       | Val_ptr addr ->
         (match heap_lookup !heap_ref addr with
          | Some (tag, dst_fields) ->
            let dst_arr = Array.of_list dst_fields in
            for k = 0 to len - 1 do
              let sv = match List.nth_opt src_fields (src_off + k + 2) with Some v -> v | None -> Val_int 0 in
              if dst_off + k + 2 < Array.length dst_arr then
                dst_arr.(dst_off + k + 2) <- sv
            done;
            heap_update_local addr (Array.to_list dst_arr);
            ignore tag
          | None -> ())
       | _ -> ());
      Some (Val_int 0)
    (* --- Ephemerons (overlap with weak in OCaml 4.14) --- *)
    | "caml_ephe_create", [Val_int n] ->
      (* Ephemeron: FIRST_KEY=2, so n keys + 2 overhead slots *)
      Some (heap_alloc_local 251 (List.init (n + 2) (fun _ -> Val_int 0)))
    | ("caml_ephe_get_key" | "caml_ephe_get_key_copy"), [arr; Val_int i] ->
      let fields = match arr with
        | Val_ptr addr -> (match heap_lookup heap addr with Some (_, fs) -> fs | None -> [])
        | _ -> []
      in
      let slot = match List.nth_opt fields (i + 2) with Some v -> v | None -> Val_int 0 in
      (match slot with
       | Val_int 0 -> Some (Val_int 0)
       | v -> Some (heap_alloc_local 0 [v]))
    | ("caml_ephe_get_data" | "caml_ephe_get_data_copy"), [arr] ->
      let fields = match arr with
        | Val_ptr addr -> (match heap_lookup heap addr with Some (_, fs) -> fs | None -> [])
        | _ -> []
      in
      let slot = match List.nth_opt fields 0 with Some v -> v | None -> Val_int 0 in
      (match slot with
       | Val_int 0 -> Some (Val_int 0)
       | v -> Some (heap_alloc_local 0 [v]))
    | "caml_ephe_set_key", [arr; Val_int i; v] ->
      (match arr with
       | Val_ptr addr ->
         (match heap_lookup !heap_ref addr with
          | Some (tag, fields) ->
            let arr2 = Array.of_list fields in
            if i + 2 < Array.length arr2 then arr2.(i + 2) <- v;
            heap_update_local addr (Array.to_list arr2);
            ignore tag
          | None -> ())
       | _ -> ());
      Some (Val_int 0)
    | "caml_ephe_set_data", [arr; v] ->
      (match arr with
       | Val_ptr addr ->
         (match heap_lookup !heap_ref addr with
          | Some (tag, fields) ->
            let arr2 = Array.of_list fields in
            if Array.length arr2 >= 1 then arr2.(0) <- v;
            heap_update_local addr (Array.to_list arr2);
            ignore tag
          | None -> ())
       | _ -> ());
      Some (Val_int 0)
    | ("caml_ephe_unset_key"), [arr; Val_int i] ->
      (match arr with
       | Val_ptr addr ->
         (match heap_lookup !heap_ref addr with
          | Some (tag, fields) ->
            let arr2 = Array.of_list fields in
            if i + 2 < Array.length arr2 then arr2.(i + 2) <- Val_int 0;
            heap_update_local addr (Array.to_list arr2);
            ignore tag
          | None -> ())
       | _ -> ());
      Some (Val_int 0)
    | "caml_ephe_unset_data", [arr] ->
      (match arr with
       | Val_ptr addr ->
         (match heap_lookup !heap_ref addr with
          | Some (tag, fields) ->
            let arr2 = Array.of_list fields in
            if Array.length arr2 >= 1 then arr2.(0) <- Val_int 0;
            heap_update_local addr (Array.to_list arr2);
            ignore tag
          | None -> ())
       | _ -> ());
      Some (Val_int 0)
    | ("caml_ephe_check_key"), [arr; Val_int i] ->
      let fields = match arr with
        | Val_ptr addr -> (match heap_lookup heap addr with Some (_, fs) -> fs | None -> [])
        | _ -> []
      in
      let slot = match List.nth_opt fields (i + 2) with Some v -> v | None -> Val_int 0 in
      Some (Val_int (if slot = Val_int 0 then 0 else 1))
    | "caml_ephe_check_data", [arr] ->
      let fields = match arr with
        | Val_ptr addr -> (match heap_lookup heap addr with Some (_, fs) -> fs | None -> [])
        | _ -> []
      in
      let slot = match List.nth_opt fields 0 with Some v -> v | None -> Val_int 0 in
      Some (Val_int (if slot = Val_int 0 then 0 else 1))
    | ("caml_ephe_blit_key" | "caml_ephe_blit_data"), _ -> Some (Val_int 0)
    (* --- Hash --- *)
    | "caml_hash", [Val_int _count; Val_int _limit; seed_v; v] ->
      (* Polymorphic hash: simplified structural hash *)
      let seed = match seed_v with Val_int s -> s | _ -> 0 in
      let rec hash_val depth v =
        if depth <= 0 then 0
        else match v with
          | Val_int n -> n lxor seed
          | Val_block (tag, fields) ->
            List.fold_left (fun acc fv -> acc lxor hash_val (depth - 1) fv) (tag * 65599) fields
          | Val_ptr addr ->
            (match heap_lookup heap addr with
             | Some (tag, fields) ->
               List.fold_left (fun acc fv -> acc lxor hash_val (depth - 1) fv) (tag * 65599) fields
             | None -> 0)
          | _ -> 0
      in
      Some (Val_int ((hash_val 10 v) land max_int))
    | "caml_hash_univ_param", [Val_int _count; Val_int _limit; v] ->
      let rec hash_val depth v =
        if depth <= 0 then 0
        else match v with
          | Val_int n -> n
          | Val_block (tag, fields) ->
            List.fold_left (fun acc fv -> acc lxor hash_val (depth - 1) fv) (tag * 65599) fields
          | Val_ptr addr ->
            (match heap_lookup heap addr with
             | Some (tag, fields) ->
               List.fold_left (fun acc fv -> acc lxor hash_val (depth - 1) fv) (tag * 65599) fields
             | None -> 0)
          | _ -> 0
      in
      Some (Val_int ((hash_val 10 v) land max_int))
    (* --- Nativeint/Int32/Int64 (boxed integers) --- *)
    (* Represent as blocks with a private tag.
       int32: Val_block(1001, [Val_int n])  (32-bit signed, fits in OCaml int)
       int64: Val_block(1002, [Val_int lo; Val_int hi])  (64-bit, two 32-bit halves)
       nativeint: Val_block(1003, [Val_int lo; Val_int hi])  (64-bit on 64-bit systems, same layout as int64) *)
    (* Helper to convert nativeint two-word rep to/from Int64 *)
    | "caml_nativeint_of_int", [Val_int n] ->
      let v64 = Int64.of_int n in
      Some (Val_block (1003, [Val_int Int64.(to_int (logand v64 0xFFFFFFFFL));
                               Val_int Int64.(to_int (shift_right_logical v64 32))]))
    | "caml_nativeint_to_int", [Val_block (1003, [Val_int lo; Val_int hi])] ->
      let v = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      Some (Val_int (Int64.to_int v))
    | "caml_nativeint_of_float", [fv] ->
      let v64 = Int64.of_float (val_to_float fv) in
      Some (Val_block (1003, [Val_int Int64.(to_int (logand v64 0xFFFFFFFFL));
                               Val_int Int64.(to_int (shift_right_logical v64 32))]))
    | "caml_nativeint_to_float", [Val_block (1003, [Val_int lo; Val_int hi])] ->
      let v = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      Some (float_to_val (Int64.to_float v))
    | ("caml_nativeint_add" | "caml_nativeint_sub" | "caml_nativeint_mul"
      | "caml_nativeint_and" | "caml_nativeint_or" | "caml_nativeint_xor"),
      [Val_block (1003, [Val_int alo; Val_int ahi]); Val_block (1003, [Val_int blo; Val_int bhi])] ->
      let av = Int64.(logor (logand (of_int alo) 0xFFFFFFFFL) (shift_left (of_int ahi) 32)) in
      let bv = Int64.(logor (logand (of_int blo) 0xFFFFFFFFL) (shift_left (of_int bhi) 32)) in
      let r = match name with
        | "caml_nativeint_add" -> Int64.add av bv
        | "caml_nativeint_sub" -> Int64.sub av bv
        | "caml_nativeint_mul" -> Int64.mul av bv
        | "caml_nativeint_and" -> Int64.logand av bv
        | "caml_nativeint_or" -> Int64.logor av bv
        | _ -> Int64.logxor av bv in
      Some (Val_block (1003, [Val_int Int64.(to_int (logand r 0xFFFFFFFFL));
                               Val_int Int64.(to_int (shift_right_logical r 32))]))
    | "caml_nativeint_div", [Val_block (1003, [Val_int alo; Val_int ahi]);
                              Val_block (1003, [Val_int blo; Val_int bhi])] ->
      let av = Int64.(logor (logand (of_int alo) 0xFFFFFFFFL) (shift_left (of_int ahi) 32)) in
      let bv = Int64.(logor (logand (of_int blo) 0xFFFFFFFFL) (shift_left (of_int bhi) 32)) in
      if bv = 0L then ccall_raise (exn_desc "Division_by_zero" (-6))
      else let r = Int64.div av bv in
           Some (Val_block (1003, [Val_int Int64.(to_int (logand r 0xFFFFFFFFL));
                                    Val_int Int64.(to_int (shift_right_logical r 32))]))
    | "caml_nativeint_mod", [Val_block (1003, [Val_int alo; Val_int ahi]);
                              Val_block (1003, [Val_int blo; Val_int bhi])] ->
      let av = Int64.(logor (logand (of_int alo) 0xFFFFFFFFL) (shift_left (of_int ahi) 32)) in
      let bv = Int64.(logor (logand (of_int blo) 0xFFFFFFFFL) (shift_left (of_int bhi) 32)) in
      if bv = 0L then ccall_raise (exn_desc "Division_by_zero" (-6))
      else let r = Int64.rem av bv in
           Some (Val_block (1003, [Val_int Int64.(to_int (logand r 0xFFFFFFFFL));
                                    Val_int Int64.(to_int (shift_right_logical r 32))]))
    | "caml_nativeint_neg", [Val_block (1003, [Val_int lo; Val_int hi])] ->
      let v = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      let r = Int64.neg v in
      Some (Val_block (1003, [Val_int Int64.(to_int (logand r 0xFFFFFFFFL));
                               Val_int Int64.(to_int (shift_right_logical r 32))]))
    | "caml_nativeint_abs", [Val_block (1003, [Val_int lo; Val_int hi])] ->
      let v = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      let r = Int64.abs v in
      Some (Val_block (1003, [Val_int Int64.(to_int (logand r 0xFFFFFFFFL));
                               Val_int Int64.(to_int (shift_right_logical r 32))]))
    | ("caml_nativeint_shift_left" | "caml_nativeint_shift_right" | "caml_nativeint_shift_right_unsigned"),
      [Val_block (1003, [Val_int lo; Val_int hi]); Val_int b] ->
      let v = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      let r = match name with
        | "caml_nativeint_shift_left" -> Int64.shift_left v b
        | "caml_nativeint_shift_right" -> Int64.shift_right v b
        | _ -> Int64.shift_right_logical v b in
      Some (Val_block (1003, [Val_int Int64.(to_int (logand r 0xFFFFFFFFL));
                               Val_int Int64.(to_int (shift_right_logical r 32))]))
    | "caml_nativeint_compare", [Val_block (1003, [Val_int alo; Val_int ahi]);
                                   Val_block (1003, [Val_int blo; Val_int bhi])] ->
      let av = Int64.(logor (logand (of_int alo) 0xFFFFFFFFL) (shift_left (of_int ahi) 32)) in
      let bv = Int64.(logor (logand (of_int blo) 0xFFFFFFFFL) (shift_left (of_int bhi) 32)) in
      Some (Val_int (Int64.compare av bv))
    | "caml_nativeint_of_string", [sv] ->
      (match resolve_string_or_bytes heap sv with
       | Some cs ->
         let s = String.init (List.length cs) (fun i -> match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000') in
         (try let n = Int64.of_string s in
              Some (Val_block (1003, [Val_int Int64.(to_int (logand n 0xFFFFFFFFL));
                                       Val_int Int64.(to_int (shift_right_logical n 32))]))
          with _ -> ccall_raise (Val_block (0, [exn_desc "Failure" (-5); string_val ("nativeint_of_string " ^ s)])))
       | None -> ccall_raise (Val_block (0, [exn_desc "Failure" (-5); string_val "nativeint_of_string"])))
    | "caml_nativeint_to_string", [Val_block (1003, [Val_int lo; Val_int hi])] ->
      let v = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      Some (string_val (Int64.to_string v))
    | ("caml_nativeint_format"), [fmt_v; Val_block (1003, [Val_int lo; Val_int hi])] ->
      let v = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      let fmt = match resolve_string heap fmt_v with
        | Some cs -> String.init (List.length cs) (fun i -> match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000')
        | None -> "%Ld"
      in
      (try Some (string_val (Printf.sprintf (Scanf.format_from_string fmt "%Ld") v))
       with _ -> Some (string_val (Int64.to_string v)))
    (* Int32 *)
    | "caml_int32_of_int", [Val_int n] -> Some (Val_block (1001, [Val_int (n land 0xFFFFFFFF - (if n land 0x80000000 <> 0 then 0x100000000 else 0))]))
    | "caml_int32_to_int", [Val_block (1001, [Val_int n])] -> Some (Val_int n)
    | "caml_int32_of_float", [fv] -> Some (Val_block (1001, [Val_int (Int32.to_int (Int32.of_float (val_to_float fv)))]))
    | "caml_int32_to_float", [Val_block (1001, [Val_int n])] -> Some (float_to_val (Int32.to_float (Int32.of_int n)))
    | ("caml_int32_add" | "caml_int32_sub" | "caml_int32_mul"
      | "caml_int32_and" | "caml_int32_or" | "caml_int32_xor"), [Val_block (1001, [Val_int a]); Val_block (1001, [Val_int b])] ->
      let r32 a b = match name with
        | "caml_int32_add" -> Int32.(to_int (add (of_int a) (of_int b)))
        | "caml_int32_sub" -> Int32.(to_int (sub (of_int a) (of_int b)))
        | "caml_int32_mul" -> Int32.(to_int (mul (of_int a) (of_int b)))
        | "caml_int32_and" -> Int32.(to_int (logand (of_int a) (of_int b)))
        | "caml_int32_or" -> Int32.(to_int (logor (of_int a) (of_int b)))
        | _ -> Int32.(to_int (logxor (of_int a) (of_int b)))
      in Some (Val_block (1001, [Val_int (r32 a b)]))
    | "caml_int32_div", [Val_block (1001, [Val_int a]); Val_block (1001, [Val_int b])] ->
      if b = 0 then ccall_raise (exn_desc "Division_by_zero" (-6))
      else Some (Val_block (1001, [Val_int Int32.(to_int (div (of_int a) (of_int b)))]))
    | "caml_int32_mod", [Val_block (1001, [Val_int a]); Val_block (1001, [Val_int b])] ->
      if b = 0 then ccall_raise (exn_desc "Division_by_zero" (-6))
      else Some (Val_block (1001, [Val_int Int32.(to_int (rem (of_int a) (of_int b)))]))
    | "caml_int32_neg", [Val_block (1001, [Val_int a])] -> Some (Val_block (1001, [Val_int Int32.(to_int (neg (of_int a)))]))
    | "caml_int32_abs", [Val_block (1001, [Val_int a])] -> Some (Val_block (1001, [Val_int Int32.(to_int (abs (of_int a)))]))
    | ("caml_int32_shift_left" | "caml_int32_shift_right" | "caml_int32_shift_right_unsigned"),
      [Val_block (1001, [Val_int a]); Val_int b] ->
      let r = match name with
        | "caml_int32_shift_left" -> Int32.(to_int (shift_left (of_int a) b))
        | "caml_int32_shift_right" -> Int32.(to_int (shift_right (of_int a) b))
        | _ -> Int32.(to_int (shift_right_logical (of_int a) b)) in
      Some (Val_block (1001, [Val_int r]))
    | "caml_int32_compare", [Val_block (1001, [Val_int a]); Val_block (1001, [Val_int b])] ->
      Some (Val_int (Int32.compare (Int32.of_int a) (Int32.of_int b)))
    | "caml_int32_of_string", [sv] ->
      (match resolve_string_or_bytes heap sv with
       | Some cs ->
         let s = String.init (List.length cs) (fun i -> match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000') in
         (try Some (Val_block (1001, [Val_int Int32.(to_int (of_string s))]))
          with _ -> ccall_raise (Val_block (0, [exn_desc "Failure" (-5); string_val ("int32_of_string " ^ s)])))
       | None -> ccall_raise (Val_block (0, [exn_desc "Failure" (-5); string_val "int32_of_string"])))
    | "caml_int32_to_string", [Val_block (1001, [Val_int n])] -> Some (string_val (Int32.to_string (Int32.of_int n)))
    | "caml_int32_format", [fmt_v; Val_block (1001, [Val_int n])] ->
      let fmt = match resolve_string heap fmt_v with
        | Some cs -> String.init (List.length cs) (fun i -> match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000')
        | None -> "%d"
      in
      (try Some (string_val (Printf.sprintf (Scanf.format_from_string fmt "%ld") (Int32.of_int n)))
       with _ -> Some (string_val (string_of_int n)))
    (* Int64 - represented as Val_block(1002, [Val_int lo; Val_int hi]) *)
    | "caml_int64_of_int", [Val_int n] ->
      let bits = Int64.of_int n in
      Some (Val_block (1002, [Val_int Int64.(to_int (logand bits 0xFFFFFFFFL));
                               Val_int Int64.(to_int (shift_right_logical bits 32))]))
    | "caml_int64_to_int", [Val_block (1002, [Val_int lo; Val_int hi])] ->
      let bits = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      Some (Val_int (Int64.to_int bits))
    | "caml_int64_of_float", [fv] ->
      let n = Int64.of_float (val_to_float fv) in
      Some (Val_block (1002, [Val_int Int64.(to_int (logand n 0xFFFFFFFFL));
                               Val_int Int64.(to_int (shift_right_logical n 32))]))
    | "caml_int64_to_float", [Val_block (1002, [Val_int lo; Val_int hi])] ->
      let bits = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      Some (float_to_val (Int64.to_float bits))
    | ("caml_int64_add" | "caml_int64_sub" | "caml_int64_mul"
      | "caml_int64_and" | "caml_int64_or" | "caml_int64_xor"),
      [Val_block (1002, [Val_int alo; Val_int ahi]); Val_block (1002, [Val_int blo; Val_int bhi])] ->
      let av = Int64.(logor (logand (of_int alo) 0xFFFFFFFFL) (shift_left (of_int ahi) 32)) in
      let bv = Int64.(logor (logand (of_int blo) 0xFFFFFFFFL) (shift_left (of_int bhi) 32)) in
      let r = match name with
        | "caml_int64_add" -> Int64.add av bv | "caml_int64_sub" -> Int64.sub av bv
        | "caml_int64_mul" -> Int64.mul av bv | "caml_int64_and" -> Int64.logand av bv
        | "caml_int64_or" -> Int64.logor av bv | _ -> Int64.logxor av bv in
      Some (Val_block (1002, [Val_int Int64.(to_int (logand r 0xFFFFFFFFL));
                               Val_int Int64.(to_int (shift_right_logical r 32))]))
    | "caml_int64_neg", [Val_block (1002, [Val_int lo; Val_int hi])] ->
      let v = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      let r = Int64.neg v in
      Some (Val_block (1002, [Val_int Int64.(to_int (logand r 0xFFFFFFFFL));
                               Val_int Int64.(to_int (shift_right_logical r 32))]))
    | "caml_int64_compare",
      [Val_block (1002, [Val_int alo; Val_int ahi]); Val_block (1002, [Val_int blo; Val_int bhi])] ->
      let av = Int64.(logor (logand (of_int alo) 0xFFFFFFFFL) (shift_left (of_int ahi) 32)) in
      let bv = Int64.(logor (logand (of_int blo) 0xFFFFFFFFL) (shift_left (of_int bhi) 32)) in
      Some (Val_int (Int64.compare av bv))
    | "caml_int64_of_string", [sv] ->
      (match resolve_string_or_bytes heap sv with
       | Some cs ->
         let s = String.init (List.length cs) (fun i -> match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000') in
         (try let n = Int64.of_string s in
              Some (Val_block (1002, [Val_int Int64.(to_int (logand n 0xFFFFFFFFL));
                                       Val_int Int64.(to_int (shift_right_logical n 32))]))
          with _ -> ccall_raise (Val_block (0, [exn_desc "Failure" (-5); string_val ("int64_of_string " ^ s)])))
       | None -> ccall_raise (Val_block (0, [exn_desc "Failure" (-5); string_val "int64_of_string"])))
    | "caml_int64_to_string", [Val_block (1002, [Val_int lo; Val_int hi])] ->
      let v = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      Some (string_val (Int64.to_string v))
    | ("caml_int64_shift_left" | "caml_int64_shift_right" | "caml_int64_shift_right_unsigned"),
      [Val_block (1002, [Val_int lo; Val_int hi]); Val_int b] ->
      let v = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      let r = match name with
        | "caml_int64_shift_left" -> Int64.shift_left v b
        | "caml_int64_shift_right" -> Int64.shift_right v b
        | _ -> Int64.shift_right_logical v b in
      Some (Val_block (1002, [Val_int Int64.(to_int (logand r 0xFFFFFFFFL));
                               Val_int Int64.(to_int (shift_right_logical r 32))]))
    | "caml_int64_format", [fmt_v; Val_block (1002, [Val_int lo; Val_int hi])] ->
      let v = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      let fmt = match resolve_string heap fmt_v with
        | Some cs -> String.init (List.length cs) (fun i -> match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000')
        | None -> "%Ld"
      in
      (try Some (string_val (Printf.sprintf (Scanf.format_from_string fmt "%Ld") v))
       with _ -> Some (string_val (Int64.to_string v)))
    (* Conversions between boxed int types *)
    | "caml_int64_to_nativeint", [Val_block (1002, [Val_int lo; Val_int hi])] ->
      (* On 64-bit, nativeint = 64-bit, just change tag *)
      Some (Val_block (1003, [Val_int lo; Val_int hi]))
    | "caml_int64_of_nativeint", [Val_block (1003, [Val_int lo; Val_int hi])] ->
      Some (Val_block (1002, [Val_int lo; Val_int hi]))
    | "caml_int64_to_int32", [Val_block (1002, [Val_int lo; Val_int _hi])] ->
      (* Truncate to 32 bits *)
      let n32 = Int32.to_int (Int32.of_int lo) in
      Some (Val_block (1001, [Val_int n32]))
    | "caml_int64_of_int32", [Val_block (1001, [Val_int n])] ->
      let v64 = Int64.of_int32 (Int32.of_int n) in
      Some (Val_block (1002, [Val_int Int64.(to_int (logand v64 0xFFFFFFFFL));
                               Val_int Int64.(to_int (shift_right_logical v64 32))]))
    | "caml_nativeint_to_int32", [Val_block (1003, [Val_int lo; Val_int _hi])] ->
      let n32 = Int32.to_int (Int32.of_int lo) in
      Some (Val_block (1001, [Val_int n32]))
    | "caml_nativeint_of_int32", [Val_block (1001, [Val_int n])] ->
      let v64 = Int64.of_int32 (Int32.of_int n) in
      Some (Val_block (1003, [Val_int Int64.(to_int (logand v64 0xFFFFFFFFL));
                               Val_int Int64.(to_int (shift_right_logical v64 32))]))
    (* caml_int64_float_of_bits: already handled above but now using proper int64 rep *)
    | "caml_int64_float_of_bits", [Val_block (1002, [Val_int lo; Val_int hi])] ->
      let bits = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      Some (float_to_val (Int64.float_of_bits bits))
    (* Plain int parsing *)
    | "caml_int_of_string", [sv] ->
      (match resolve_string_or_bytes heap sv with
       | Some cs ->
         let s = String.init (List.length cs) (fun i -> match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000') in
         (try Some (Val_int (int_of_string s))
          with _ -> ccall_raise (Val_block (0, [exn_desc "Failure" (-5); string_val ("int_of_string " ^ s)])))
       | None -> ccall_raise (Val_block (0, [exn_desc "Failure" (-5); string_val "int_of_string"])))
    (* --- Integer formatting --- *)
    | "caml_format_int", [fmt_v; Val_int n] ->
      let fmt_str = match resolve_string heap fmt_v with
        | Some cs -> String.init (List.length cs) (fun i -> match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000')
        | None -> "%d"
      in
      let s = if fmt_str = "%d" || fmt_str = "" then string_of_int n
              else (try Printf.sprintf (Scanf.format_from_string fmt_str "%d") n
                    with _ -> string_of_int n) in
      Some (string_val s)
    | "caml_format_int", _ -> Some (string_val "0")
    (* --- String/bytes operations --- *)
    | ("caml_string_length" | "caml_ml_string_length" | "caml_ml_bytes_length"), [sv] ->
      (match resolve_string_or_bytes heap sv with
       | Some cs -> Some (Val_int (List.length cs))
       | None -> Some (Val_int 0))
    | "caml_create_bytes", [Val_int n] ->
      (* Allocate mutable bytes on interpreter heap as tag-252 block *)
      Some (heap_alloc_local 252 (List.init n (fun _ -> Val_int 0)))
    | ("caml_blit_string" | "caml_blit_bytes"), [src_v; Val_int src_off; dst_v; Val_int dst_off; Val_int len] ->
      (* Write src chars into dest bytes heap block *)
      (match dst_v with
       | Val_ptr dst_addr ->
         (match heap_lookup !heap_ref dst_addr with
          | Some (tag, fields) ->
            (match resolve_string_or_bytes heap src_v with
             | Some src_chars ->
               let arr = Array.of_list fields in
               for k = 0 to len - 1 do
                 (match List.nth_opt src_chars (src_off + k) with
                  | Some v -> arr.(dst_off + k) <- v
                  | None -> ())
               done;
               heap_update_local dst_addr (Array.to_list arr);
               ignore tag
             | None -> ())
          | None -> ())
       | _ -> ());
      Some (Val_int 0)
    | ("caml_blit_string" | "caml_blit_bytes"), _ -> Some (Val_int 0)
    | "caml_string_equal", [sa; sb] ->
      (match resolve_string_or_bytes heap sa, resolve_string_or_bytes heap sb with
       | Some a, Some b -> Some (Val_int (if a=b then 1 else 0))
       | _ -> Some (Val_int 0))
    | "caml_string_notequal", [sa; sb] ->
      (match resolve_string_or_bytes heap sa, resolve_string_or_bytes heap sb with
       | Some a, Some b -> Some (Val_int (if a=b then 0 else 1))
       | _ -> Some (Val_int 1))
    | "caml_string_compare", [sa; sb] ->
      let chars_to_string cs = String.init (List.length cs) (fun i -> match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000') in
      (match resolve_string_or_bytes heap sa, resolve_string_or_bytes heap sb with
       | Some a, Some b -> Some (Val_int (String.compare (chars_to_string a) (chars_to_string b)))
       | _ -> Some (Val_int 0))
    | "caml_string_concat", [sa; sb] ->
      (match resolve_string_or_bytes heap sa, resolve_string_or_bytes heap sb with
       | Some a, Some b -> Some (Val_block (252, a @ b))
       | _ -> Some (Val_block (252, [])))
    | "caml_string_of_bytes", [v] ->
      (* Convert mutable bytes (Val_ptr with tag 252) to immutable Val_block *)
      (match resolve_string_or_bytes heap v with
       | Some cs -> Some (Val_block (252, cs))
       | None -> Some v)
    | "caml_bytes_of_string", [v] ->
      (* Convert immutable string to mutable bytes copy on heap *)
      (match resolve_string heap v with
       | Some cs -> Some (heap_alloc_local 252 cs)
       | None -> Some v)
    | ("caml_string_get" | "caml_bytes_get"), [sv; Val_int i] ->
      (match resolve_string_or_bytes heap sv with
       | Some cs -> (match List.nth_opt cs i with Some v -> Some v | None -> Some (Val_int 0))
       | None -> Some (Val_int 0))
    | ("caml_string_set" | "caml_bytes_set"), [bv; Val_int i; Val_int c] ->
      (match bv with
       | Val_ptr addr ->
         (match heap_lookup !heap_ref addr with
          | Some (tag, fields) ->
            let arr = Array.of_list fields in
            (if i >= 0 && i < Array.length arr then arr.(i) <- Val_int c);
            heap_update_local addr (Array.to_list arr);
            ignore tag
          | None -> ())
       | _ -> ());
      Some (Val_int 0)
    | ("caml_string_set" | "caml_bytes_set"), _ -> Some (Val_int 0)
    | "caml_fill_bytes", [bv; Val_int ofs; Val_int len; Val_int c] ->
      (match bv with
       | Val_ptr addr ->
         (match heap_lookup !heap_ref addr with
          | Some (tag, fields) ->
            let arr = Array.of_list fields in
            for k = ofs to ofs + len - 1 do
              if k >= 0 && k < Array.length arr then arr.(k) <- Val_int c
            done;
            heap_update_local addr (Array.to_list arr);
            ignore tag
          | None -> ())
       | _ -> ());
      Some (Val_int 0)
    | "caml_fill_bytes", _ -> Some (Val_int 0)
    | "caml_sub_bytes", [sv; Val_int ofs; Val_int len] ->
      (match resolve_string_or_bytes heap sv with
       | Some cs ->
         let sub = List.filteri (fun i _ -> i >= ofs && i < ofs + len) cs in
         Some (heap_alloc_local 252 sub)
       | None -> Some (heap_alloc_local 252 []))
    | "caml_bytes_to_string", [v] ->
      (match resolve_string_or_bytes heap v with
       | Some cs -> Some (Val_block (252, cs))
       | None -> Some v)
    (* --- Comparison --- *)
    | "caml_int_compare", [Val_int a; Val_int b] ->
      Some (Val_int (if a < b then -1 else if a > b then 1 else 0))
    | ("caml_int_compare" | "caml_compare"), _ ->
      (match args with
       | [a; b] ->
         (try Some (Val_int (deep_compare heap a b))
          with Exit ->
            ccall_raise (Val_block (0, [exn_desc "Invalid_argument" (-3);
                                        string_val "compare: functional value"])))
       | _ -> Some (Val_int 0))
    | "caml_equal", [a; b] ->
      (try Some (Val_int (if deep_equal_ieee heap a b then 1 else 0))
       with Exit ->
         ccall_raise (Val_block (0, [exn_desc "Invalid_argument" (-3);
                                     string_val "compare: functional value"])))
    | "caml_notequal", [a; b] ->
      (try Some (Val_int (if deep_equal_ieee heap a b then 0 else 1))
       with Exit ->
         ccall_raise (Val_block (0, [exn_desc "Invalid_argument" (-3);
                                     string_val "compare: functional value"])))
    | "caml_lessthan", [a; b] ->
      (try (match deep_compare_ieee heap a b with
            | Some c -> Some (Val_int (if c < 0 then 1 else 0))
            | None -> Some (Val_int 0))  (* NaN comparison: false *)
       with Exit ->
         ccall_raise (Val_block (0, [exn_desc "Invalid_argument" (-3);
                                     string_val "compare: functional value"])))
    | "caml_lessequal", [a; b] ->
      (try (match deep_compare_ieee heap a b with
            | Some c -> Some (Val_int (if c <= 0 then 1 else 0))
            | None -> Some (Val_int 0))
       with Exit ->
         ccall_raise (Val_block (0, [exn_desc "Invalid_argument" (-3);
                                     string_val "compare: functional value"])))
    | "caml_greaterthan", [a; b] ->
      (try (match deep_compare_ieee heap a b with
            | Some c -> Some (Val_int (if c > 0 then 1 else 0))
            | None -> Some (Val_int 0))
       with Exit ->
         ccall_raise (Val_block (0, [exn_desc "Invalid_argument" (-3);
                                     string_val "compare: functional value"])))
    | "caml_greaterequal", [a; b] ->
      (try (match deep_compare_ieee heap a b with
            | Some c -> Some (Val_int (if c >= 0 then 1 else 0))
            | None -> Some (Val_int 0))
       with Exit ->
         ccall_raise (Val_block (0, [exn_desc "Invalid_argument" (-3);
                                     string_val "compare: functional value"])))
    | ("caml_lessthan" | "caml_lessequal" | "caml_greaterthan" | "caml_greaterequal"), _ ->
      Some (Val_int 0)
    (* --- Floats (proper implementation using float_to_val/val_to_float) --- *)
    | "caml_int64_float_of_bits", [bv] ->
      (* int64 block to float: bits in block fields *)
      let bits = match bv with
        | Val_block (_, [Val_int lo; Val_int hi]) ->
          Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32))
        | Val_block (_, [Val_int b]) -> Int64.of_int b
        | Val_int n -> Int64.of_int n
        | _ -> 0L
      in Some (float_to_val (Int64.float_of_bits bits))
    | "caml_float_of_int", [Val_int n] -> Some (float_to_val (float_of_int n))
    | "caml_int_of_float", [fv] -> Some (Val_int (int_of_float (val_to_float fv)))
    | ("caml_add_float" | "caml_float_add"), [a; b] -> float_binop ( +. ) a b
    | ("caml_sub_float" | "caml_float_sub"), [a; b] -> float_binop ( -. ) a b
    | ("caml_mul_float" | "caml_float_mul"), [a; b] -> float_binop ( *. ) a b
    | ("caml_div_float" | "caml_float_div"), [a; b] -> float_binop ( /. ) a b
    | "caml_float_compare", [a; b] ->
      let fa = val_to_float a and fb = val_to_float b in
      Some (Val_int (compare fa fb))
    | ("caml_float_equal" | "caml_eq_float"), [a; b] ->
      Some (Val_int (if val_to_float a = val_to_float b then 1 else 0))
    | ("caml_float_notequal" | "caml_neq_float"), [a; b] ->
      Some (Val_int (if val_to_float a <> val_to_float b then 1 else 0))
    | ("caml_float_lt" | "caml_lt_float"), [a; b] ->
      Some (Val_int (if val_to_float a < val_to_float b then 1 else 0))
    | ("caml_float_le" | "caml_le_float"), [a; b] ->
      Some (Val_int (if val_to_float a <= val_to_float b then 1 else 0))
    | ("caml_float_gt" | "caml_gt_float"), [a; b] ->
      Some (Val_int (if val_to_float a > val_to_float b then 1 else 0))
    | ("caml_float_ge" | "caml_ge_float"), [a; b] ->
      Some (Val_int (if val_to_float a >= val_to_float b then 1 else 0))
    | ("caml_format_float" | "caml_float_to_string"), [fmt_v; fv] ->
      let fmt = match resolve_string heap fmt_v with
        | Some cs -> String.init (List.length cs) (fun i ->
            match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000')
        | None -> "%.12g"
      in
      let s = (try Printf.sprintf (Scanf.format_from_string fmt "%.12g") (val_to_float fv)
               with _ -> string_of_float (val_to_float fv)) in
      Some (string_val s)
    | ("caml_format_float" | "caml_float_to_string"), [fv] ->
      Some (string_val (string_of_float (val_to_float fv)))
    | "caml_sqrt", [a] -> float_unop sqrt a
    | "caml_exp",  [a] -> float_unop exp  a
    | "caml_log",  [a] -> float_unop log  a
    | "caml_sin",  [a] -> float_unop sin  a
    | "caml_cos",  [a] -> float_unop cos  a
    | "caml_tan",  [a] -> float_unop tan  a
    | "caml_atan", [a] -> float_unop atan a
    | "caml_atan2",[a;b] -> float_binop atan2 a b
    | "caml_asin", [a] -> float_unop asin a
    | "caml_acos", [a] -> float_unop acos a
    | "caml_trunc_float", [a] ->
      let f = val_to_float a in
      let r = if f >= 0.0 then floor f else ceil f in
      Some (float_to_val r)
    | "caml_round_float", [a] ->
      let f = val_to_float a in
      let r = if f >= 0.0 then floor (f +. 0.5) else ceil (f -. 0.5) in
      Some (float_to_val r)
    | "caml_nextafter_float", [a; b] ->
      let fa = val_to_float a and fb = val_to_float b in
      Some (float_to_val (Float.next_after fa fb))
    | "caml_copysign_float", [a; b] ->
      let fa = val_to_float a and fb = val_to_float b in
      Some (float_to_val (Float.copy_sign fa fb))
    | "caml_signbit_float", [a] ->
      Some (Val_int (if Float.sign_bit (val_to_float a) then 1 else 0))
    | "caml_frexp_float", [a] ->
      let (frac, exp) = Float.frexp (val_to_float a) in
      Some (tuple_val [float_to_val frac; Val_int exp])
    | "caml_ldexp_float", [a; Val_int exp] ->
      Some (float_to_val (Float.ldexp (val_to_float a) exp))
    | "caml_fma_float", [a; b; c] ->
      let fa = val_to_float a and fb = val_to_float b and fc = val_to_float c in
      Some (float_to_val (Float.fma fa fb fc))
    | "caml_modf_float", [a] ->
      let (frac, intg) = Float.modf (val_to_float a) in
      Some (tuple_val [float_to_val frac; float_to_val intg])
    | ("caml_power_float" | "caml_float_pow"), [a; b] -> float_binop ( ** ) a b
    | "caml_log10", [a] -> float_unop log10 a
    | "caml_log2_float", [a] -> float_unop (fun x -> log x /. log 2.0) a
    | "caml_cosh", [a] -> float_unop cosh a
    | "caml_sinh", [a] -> float_unop sinh a
    | "caml_tanh", [a] -> float_unop tanh a
    | "caml_ceil", [a] -> float_unop ceil a
    | "caml_floor", [a] -> float_unop floor a
    | "caml_hypot_float", [a; b] -> float_binop hypot a b
    | "caml_fmod_float", [a; b] -> float_binop mod_float a b
    | "caml_classify_float", [a] ->
      let c = match Float.classify_float (val_to_float a) with
        | FP_normal -> 0 | FP_subnormal -> 1 | FP_zero -> 2
        | FP_infinite -> 3 | FP_nan -> 4
      in
      Some (Val_int c)
    | ("caml_float_neg" | "caml_neg_float"), [a] -> float_unop ( ~-. ) a
    | ("caml_float_abs" | "caml_abs_float"), [a] -> float_unop abs_float a
    | ("caml_float_of_string" | "caml_float_of_bytes"), [sv] ->
      let s = match resolve_string_or_bytes heap sv with
        | Some cs -> String.init (List.length cs) (fun i ->
            match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000')
        | None -> "0."
      in
      (try Some (float_to_val (float_of_string s))
       with _ ->
         let failure_desc = exn_desc "Failure" (-5) in
         ccall_raise (Val_block (0, [failure_desc; string_val ("float_of_string " ^ s)])))
    | "caml_make_float_vect", [Val_int n] ->
      Some (heap_alloc_local 254 (List.init n (fun _ -> float_to_val 0.0)))
    (* --- Int32/Int64/Nativeint missing ops --- *)
    | "caml_int32_unsigned_to_int", [Val_block (1001, [Val_int n])] ->
      (* On 64-bit systems, unsigned int32 always fits in OCaml int *)
      let u = n land 0xFFFFFFFF in
      Some (heap_alloc_local 0 [Val_int u])
    | "caml_int32_unsigned_div", [Val_block (1001, [Val_int a]); Val_block (1001, [Val_int b])] ->
      if b = 0 then ccall_raise (exn_desc "Division_by_zero" (-6))
      else
        let ua = Int32.unsigned_to_int (Int32.of_int a) |> Option.value ~default:0 in
        let ub = Int32.unsigned_to_int (Int32.of_int b) |> Option.value ~default:0 in
        Some (Val_block (1001, [Val_int (ua / ub)]))
    | "caml_int32_unsigned_rem", [Val_block (1001, [Val_int a]); Val_block (1001, [Val_int b])] ->
      if b = 0 then ccall_raise (exn_desc "Division_by_zero" (-6))
      else
        let ua = Int32.unsigned_to_int (Int32.of_int a) |> Option.value ~default:0 in
        let ub = Int32.unsigned_to_int (Int32.of_int b) |> Option.value ~default:0 in
        Some (Val_block (1001, [Val_int (ua mod ub)]))
    | "caml_int32_unsigned_compare", [Val_block (1001, [Val_int a]); Val_block (1001, [Val_int b])] ->
      let ua = Int32.unsigned_to_int (Int32.of_int a) |> Option.value ~default:0 in
      let ub = Int32.unsigned_to_int (Int32.of_int b) |> Option.value ~default:0 in
      Some (Val_int (Int.compare ua ub))
    | "caml_int64_unsigned_to_int", [Val_block (1002, [Val_int lo; Val_int hi])] ->
      let v = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      (* On 64-bit, return Some n only if v fits in OCaml's non-negative int range [0, max_int] *)
      if Int64.compare v 0L >= 0 && Int64.compare v (Int64.of_int max_int) <= 0
      then Some (heap_alloc_local 0 [Val_int (Int64.to_int v)])  (* Some n *)
      else Some (Val_int 0)  (* None *)
    | "caml_int64_div", [Val_block (1002, [Val_int alo; Val_int ahi]);
                          Val_block (1002, [Val_int blo; Val_int bhi])] ->
      let av = Int64.(logor (logand (of_int alo) 0xFFFFFFFFL) (shift_left (of_int ahi) 32)) in
      let bv = Int64.(logor (logand (of_int blo) 0xFFFFFFFFL) (shift_left (of_int bhi) 32)) in
      if bv = 0L then ccall_raise (exn_desc "Division_by_zero" (-6))
      else
        let r = Int64.div av bv in
        Some (Val_block (1002, [Val_int Int64.(to_int (logand r 0xFFFFFFFFL));
                                 Val_int Int64.(to_int (shift_right_logical r 32))]))
    | "caml_int64_mod", [Val_block (1002, [Val_int alo; Val_int ahi]);
                          Val_block (1002, [Val_int blo; Val_int bhi])] ->
      let av = Int64.(logor (logand (of_int alo) 0xFFFFFFFFL) (shift_left (of_int ahi) 32)) in
      let bv = Int64.(logor (logand (of_int blo) 0xFFFFFFFFL) (shift_left (of_int bhi) 32)) in
      if bv = 0L then ccall_raise (exn_desc "Division_by_zero" (-6))
      else
        let r = Int64.rem av bv in
        Some (Val_block (1002, [Val_int Int64.(to_int (logand r 0xFFFFFFFFL));
                                 Val_int Int64.(to_int (shift_right_logical r 32))]))
    | "caml_int64_unsigned_div", [Val_block (1002, [Val_int alo; Val_int ahi]);
                                   Val_block (1002, [Val_int blo; Val_int bhi])] ->
      let av = Int64.(logor (logand (of_int alo) 0xFFFFFFFFL) (shift_left (of_int ahi) 32)) in
      let bv = Int64.(logor (logand (of_int blo) 0xFFFFFFFFL) (shift_left (of_int bhi) 32)) in
      if bv = 0L then ccall_raise (exn_desc "Division_by_zero" (-6))
      else
        (* Unsigned division: treat both as unsigned *)
        let r = Int64.unsigned_div av bv in
        Some (Val_block (1002, [Val_int Int64.(to_int (logand r 0xFFFFFFFFL));
                                 Val_int Int64.(to_int (shift_right_logical r 32))]))
    | "caml_int64_unsigned_rem", [Val_block (1002, [Val_int alo; Val_int ahi]);
                                   Val_block (1002, [Val_int blo; Val_int bhi])] ->
      let av = Int64.(logor (logand (of_int alo) 0xFFFFFFFFL) (shift_left (of_int ahi) 32)) in
      let bv = Int64.(logor (logand (of_int blo) 0xFFFFFFFFL) (shift_left (of_int bhi) 32)) in
      if bv = 0L then ccall_raise (exn_desc "Division_by_zero" (-6))
      else
        let r = Int64.unsigned_rem av bv in
        Some (Val_block (1002, [Val_int Int64.(to_int (logand r 0xFFFFFFFFL));
                                 Val_int Int64.(to_int (shift_right_logical r 32))]))
    | "caml_int64_unsigned_compare", [Val_block (1002, [Val_int alo; Val_int ahi]);
                                       Val_block (1002, [Val_int blo; Val_int bhi])] ->
      let av = Int64.(logor (logand (of_int alo) 0xFFFFFFFFL) (shift_left (of_int ahi) 32)) in
      let bv = Int64.(logor (logand (of_int blo) 0xFFFFFFFFL) (shift_left (of_int bhi) 32)) in
      Some (Val_int (Int64.unsigned_compare av bv))
    | "caml_nativeint_unsigned_to_int", [Val_block (1003, [Val_int lo; Val_int hi])] ->
      let v = Int64.(logor (logand (of_int lo) 0xFFFFFFFFL) (shift_left (of_int hi) 32)) in
      (* Return None if value doesn't fit in OCaml's non-negative int range *)
      if Int64.compare v 0L >= 0 && Int64.compare v (Int64.of_int max_int) <= 0
      then Some (heap_alloc_local 0 [Val_int (Int64.to_int v)])  (* Some n *)
      else Some (Val_int 0)  (* None *)
    | "caml_nativeint_unsigned_div", [Val_block (1003, [Val_int alo; Val_int ahi]);
                                       Val_block (1003, [Val_int blo; Val_int bhi])] ->
      let av = Int64.(logor (logand (of_int alo) 0xFFFFFFFFL) (shift_left (of_int ahi) 32)) in
      let bv = Int64.(logor (logand (of_int blo) 0xFFFFFFFFL) (shift_left (of_int bhi) 32)) in
      if bv = 0L then ccall_raise (exn_desc "Division_by_zero" (-6))
      else let r = Int64.unsigned_div av bv in
           Some (Val_block (1003, [Val_int Int64.(to_int (logand r 0xFFFFFFFFL));
                                    Val_int Int64.(to_int (shift_right_logical r 32))]))
    | "caml_nativeint_unsigned_rem", [Val_block (1003, [Val_int alo; Val_int ahi]);
                                       Val_block (1003, [Val_int blo; Val_int bhi])] ->
      let av = Int64.(logor (logand (of_int alo) 0xFFFFFFFFL) (shift_left (of_int ahi) 32)) in
      let bv = Int64.(logor (logand (of_int blo) 0xFFFFFFFFL) (shift_left (of_int bhi) 32)) in
      if bv = 0L then ccall_raise (exn_desc "Division_by_zero" (-6))
      else let r = Int64.unsigned_rem av bv in
           Some (Val_block (1003, [Val_int Int64.(to_int (logand r 0xFFFFFFFFL));
                                    Val_int Int64.(to_int (shift_right_logical r 32))]))
    | "caml_nativeint_unsigned_compare", [Val_block (1003, [Val_int alo; Val_int ahi]);
                                           Val_block (1003, [Val_int blo; Val_int bhi])] ->
      let av = Int64.(logor (logand (of_int alo) 0xFFFFFFFFL) (shift_left (of_int ahi) 32)) in
      let bv = Int64.(logor (logand (of_int blo) 0xFFFFFFFFL) (shift_left (of_int bhi) 32)) in
      Some (Val_int (Int64.unsigned_compare av bv))
    (* --- System --- *)
    | "caml_ensure_stack_capacity", _ -> Some (Val_int 0)
    | "caml_sys_exit", [Val_int _code] ->
      (* Treat as halt: raise a special exit exception *)
      let exit_exn = Val_block (248, [string_val "Exit"; Val_int (-999)]) in
      ccall_raise exit_exn
    | "caml_sys_exit", _ -> Some (Val_int 0)
    (* --- MD5 --- *)
    | "caml_md5_string", [sv; Val_int ofs; Val_int len] ->
      (* Return a dummy 16-byte string for MD5 *)
      (match resolve_string_or_bytes heap sv with
       | Some cs ->
         let s = String.init (min len (List.length cs - ofs)) (fun i ->
           match List.nth_opt cs (ofs + i) with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000') in
         let digest = Digest.string s in
         Some (string_val digest)
       | None -> Some (string_val (String.make 16 '\000')))
    | "caml_md5_bytes", [sv; Val_int ofs; Val_int len] ->
      (match resolve_string_or_bytes heap sv with
       | Some cs ->
         let s = String.init (min len (List.length cs - ofs)) (fun i ->
           match List.nth_opt cs (ofs + i) with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000') in
         let digest = Digest.string s in
         Some (string_val digest)
       | None -> Some (string_val (String.make 16 '\000')))
    (* --- String/int conversions --- *)
    | ("caml_int_of_string" | "caml_int_of_string_opt"), [sv] ->
      (match resolve_string heap sv with
       | Some cs ->
         let s = String.init (List.length cs) (fun i ->
           match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000') in
         (try
           let n = int_of_string s in
           if name = "caml_int_of_string_opt" then
             Some (heap_alloc_local 0 [Val_int n])  (* Some(n) *)
           else
             Some (Val_int n)
         with _ ->
           if name = "caml_int_of_string_opt" then
             Some (Val_int 0)  (* None *)
           else
             let failure = exn_desc "Failure" (-5) in
             ccall_raise failure)
       | None ->
         if name = "caml_int_of_string_opt" then Some (Val_int 0)
         else let failure = exn_desc "Failure" (-5) in
              ccall_raise failure)
    | "caml_nativeint_of_string", [sv] ->
      (match resolve_string heap sv with
       | Some cs ->
         let s = String.init (List.length cs) (fun i ->
           match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000') in
         (try Some (Val_block (1001, [Val_int (int_of_string s)]))
          with _ ->
            let failure = exn_desc "Failure" (-5) in
            ccall_raise failure)
       | None ->
         let failure = exn_desc "Failure" (-5) in
         ccall_raise failure)
    | "caml_int32_of_string", [sv] ->
      (match resolve_string heap sv with
       | Some cs ->
         let s = String.init (List.length cs) (fun i ->
           match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000') in
         (try Some (Val_block (1001, [Val_int (Int32.to_int (Int32.of_string s))]))
          with _ ->
            let failure = exn_desc "Failure" (-5) in
            ccall_raise failure)
       | None ->
         let failure = exn_desc "Failure" (-5) in
         ccall_raise failure)
    | "caml_int64_of_string", [sv] ->
      (match resolve_string heap sv with
       | Some cs ->
         let s = String.init (List.length cs) (fun i ->
           match List.nth_opt cs i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000') in
         (try
           let v = Int64.of_string s in
           let lo = Int64.(to_int (logand v 0xFFFFFFFFL)) in
           let hi = Int64.(to_int (shift_right_logical v 32)) in
           Some (Val_block (1002, [Val_int lo; Val_int hi]))
         with _ ->
           let failure = exn_desc "Failure" (-5) in
           ccall_raise failure)
       | None ->
         let failure = exn_desc "Failure" (-5) in
         ccall_raise failure)
    (* --- Obj module: reachable_words, with_tag, new_block --- *)
    | "caml_obj_reachable_words", [v] ->
      let visited = Hashtbl.create 16 in
      let count = ref 0 in
      let rec walk v =
        match v with
        | Val_ptr addr when not (Hashtbl.mem visited addr) ->
          Hashtbl.add visited addr true;
          (match heap_lookup heap addr with
           | Some (_, fields) ->
             count := !count + 1 + List.length fields;
             List.iter walk fields
           | None -> ())
        | Val_block (t, fields) when t < 251 ->
          count := !count + 1 + List.length fields;
          List.iter walk fields
        | _ -> ()
      in
      walk v;
      Some (Val_int !count)
    | "caml_obj_with_tag", [Val_int new_tag; v] ->
      (match v with
       | Val_ptr addr ->
         (match heap_lookup heap addr with
          | Some (old_tag, fields) ->
            if new_tag = old_tag then Some v
            else Some (heap_alloc_local new_tag fields)
          | None -> Some v)
       | Val_block (old_tag, fields) ->
         if new_tag = old_tag then Some v
         else Some (Val_block (new_tag, fields))
       | _ -> Some v)
    | "caml_obj_new_block", [Val_int tag; Val_int size] ->
      if tag = 255 || (tag = 252 && size = 0) then
        ccall_raise (Val_block (0, [exn_desc "Invalid_argument" (-4);
                                    string_val "Obj.new_block"]))
      else
        Some (heap_alloc_local tag (List.init size (fun _ -> Val_int 0)))
    (* --- GC stubs --- *)
    | "caml_gc_get", _ ->
      let zero_float = float_to_val 0.0 in
      Some (Val_block (0, [
        Val_int 256; Val_int 0; Val_int 80; Val_int 3; Val_int 250;
        Val_int 4096; zero_float; Val_int 0; Val_int 0; Val_int 0; Val_int 0;
      ]))
    | "caml_gc_set", _ -> Some (Val_int 0)
    | "caml_gc_minor_words", _ -> Some (float_to_val 0.0)
    (* --- Sys stubs --- *)
    | "caml_sys_system_command", _ -> Some (Val_int (-1))
    | "caml_sys_isatty", _ -> Some (Val_int 0)
    | _ ->
      Printf.eprintf "WARNING: unimplemented C-call %S (idx=%d, %d args)\n%!" name idx (List.length args);
      None
  in
  (heap_ref, next_addr_ref, pending_raise_ref, perform_raise, handler, get_named_value)

(* Run our compiled bytecode through our interpreter *)
type interp_result = Interp_ok of string | Interp_err of string

let run_source_interp prog =
  let result = interpret 10000 prog in
  match result.result with
  | Term_timeout -> Interp_err "timeout"
  | Term_error msg ->
    let buf = Buffer.create (List.length msg) in
    List.iter (Buffer.add_char buf) msg;
    Interp_err (Buffer.contents buf)
  | Term_normal _ ->
    let buf = Buffer.create (List.length result.trace) in
    List.iter (fun c -> Buffer.add_char buf (Char.chr c)) result.trace;
    Interp_ok (Buffer.contents buf)

let run_our_compiler prog =
  let code = Array.of_list (compile_program prog) in
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
    | _ ->
      Printf.eprintf "WARNING: unimplemented C-call idx=%d (%d args) in run_our_compiler\n%!" idx (List.length args);
      None
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
  let code = Array.of_list (Loader.load_bytecode_from_sections data sections) in
  let raw_globals = load_globals data sections in
  let (globals, init_heap, init_next_addr) = heap_allocate_globals raw_globals in
  let prims = load_prims data sections in
  let buf = Buffer.create 256 in
  let (heap_ref, next_addr_ref, pending_raise_ref, perform_raise, handler, _get_named_value) = make_handler ~raw_globals prims buf in
  let s = ref { (initial_state globals) with hp = init_heap; next_addr = init_next_addr } in
  heap_ref := init_heap;
  next_addr_ref := init_next_addr;
  let remaining = ref 10000000 in
  let result = ref None in
  let is_exit_exn exn = match exn with
    | Val_block (248, (Val_block (252, chars)) :: _) ->
      let name = String.init (List.length chars) (fun i ->
        match List.nth_opt chars i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000') in
      name = "Exit"
    | _ -> false
  in
  let rec loop () =
    if !remaining <= 0 then result := Some "timeout"
    else begin
      decr remaining;
      match step code !s with
      | Step s' -> s := s'; loop ()
      | Halt _ -> ()
      | Error msg -> result := Some (sc msg)
      | CCall_request (idx, args, cont) ->
        heap_ref := cont.hp;
        next_addr_ref := cont.next_addr;
        pending_raise_ref := None;
        (match handler idx args with
         | Some v ->
           s := { (set_accu cont v) with
                  hp = !heap_ref; next_addr = !next_addr_ref };
           loop ()
         | None ->
           (match !pending_raise_ref with
            | Some exn ->
              if is_exit_exn exn then ()
              else begin
                let cont' = { cont with hp = !heap_ref; next_addr = !next_addr_ref } in
                (match perform_raise cont' exn with
                 | Step s' -> s := s'; loop ()
                 | Halt _ -> ()
                 | Error msg ->
                   let msg_str = sc msg in
                   if msg_str = "unhandled exception" && is_exit_exn exn
                   then ()
                   else result := Some msg_str
                 | CCall_request _ -> result := Some "nested ccall in raise")
              end
            | None -> result := Some "ccall failed"))
    end
  in
  loop ();
  match !result with
  | None -> Ok (Buffer.contents buf)
  | Some err -> Error err
