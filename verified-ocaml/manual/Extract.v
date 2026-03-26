(* Extract.v - Manual-only extraction directives.
   Run with: make extract   (default)
   Output goes to manual/test/common/interp_extracted.ml.

   ONLY depends on manual/ theories — no semi-auto/ or automatic/ needed. *)

From Stdlib Require Import ZArith Strings.String List.
From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlZInt.
From Stdlib Require Import ExtrOcamlString.
(* Uint63: extract to native OCaml int. *)
From Stdlib Require Import Uint63.
Extract Constant Uint63.int => "int".
Extraction Inline Uint63.int.
Extract Constant Uint63.lsl => "(lsl)".
Extract Constant Uint63.lsr => "(lsr)".
Extract Constant Uint63.lor => "(lor)".
Extract Constant Uint63.land => "(land)".
Extract Constant Uint63.sub => "(-)".
Extract Constant Uint63.add => "(+)".
Extract Constant Uint63.ltb => "(<)".
Extract Constant Uint63.leb => "(<=)".
Extract Constant Uint63.eqb => "(=)".

From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine Interpret Encode.
From OCamlInterp.Manual.Bytecode Require Import IO.
From OCamlInterp.Manual.Utils Require Import Observable.
From OCamlInterp.Manual.Utils Require Import Syntax.

(* ------------------------------------------------------------------ *)
(* IO extraction directives (must be here, not in IO.v)                *)
(* ------------------------------------------------------------------ *)

Extract Constant byte_string => "bytes".

Extract Constant read_file => "
  fun cs ->
    let buf = Buffer.create 256 in
    let rec to_chars = function
      | [] -> ()
      | c :: rest -> Buffer.add_char buf (Char.chr c); to_chars rest
    in
    to_chars cs;
    let filename = Buffer.contents buf in
    let ic = open_in_bin filename in
    let n = in_channel_length ic in
    let data = Bytes.create n in
    really_input ic data 0 n;
    close_in ic;
    data
".

Extract Constant byte_string_to_list => "
  fun bs ->
    let n = Bytes.length bs in
    let rec build i acc =
      if i < 0 then acc
      else build (i - 1) (Char.code (Bytes.get bs i) :: acc)
    in
    build (n - 1) []
".

Extract Constant byte_string_length => "
  fun bs -> Bytes.length bs
".

Extract Constant print_string_io => "
  fun cs ->
    let rec go = function
      | [] -> ()
      | c :: rest -> print_char (Char.chr (c land 0xFF)); go rest
    in
    go cs; 0
".

Extract Constant sys_argv => "
  let argv = Array.to_list Sys.argv in
  List.map (fun s ->
    let n = String.length s in
    let rec build i acc =
      if i < 0 then acc
      else build (i - 1) (Char.code s.[i] :: acc)
    in
    build (n - 1) []
  ) argv
".

Extract Constant unmarshal_globals => "
  fun bs ofs len ->
    let sub = Bytes.sub bs ofs len in
    let obj : Obj.t = Marshal.from_bytes sub 0 in
    let arr : Obj.t array = Obj.obj obj in
    let rec obj_to_encoding (o : Obj.t) : int list =
      if Obj.is_int o then [0; (Obj.obj o : int)]
      else
        let tag = Obj.tag o in
        if tag = Obj.string_tag then
          let s : string = Obj.obj o in
          let n = String.length s in
          let rec chars i acc =
            if i < 0 then acc
            else chars (i - 1) (Char.code s.[i] :: acc)
          in
          2 :: n :: chars (n - 1) []
        else if tag < Obj.no_scan_tag then
          let size = Obj.size o in
          let fields = List.concat_map (fun i ->
            obj_to_encoding (Obj.field o i)
          ) (List.init size Fun.id) in
          1 :: tag :: size :: fields
        else
          [1; tag; 0]
    in
    Array.to_list (Array.map obj_to_encoding arr)
".

Extract Constant load_primitives => "
  fun bs ofs len ->
    let raw = Bytes.sub_string bs ofs len in
    let prims = List.filter (fun s -> String.length s > 0)
                  (String.split_on_char '\000' raw) in
    List.map (fun s ->
      let n = String.length s in
      let rec build i acc =
        if i < 0 then acc
        else build (i - 1) (Char.code s.[i] :: acc)
      in
      build (n - 1) []
    ) prims
".

(* PrimArray: extract to native OCaml arrays. *)
Extract Constant PrimArray.array "'a" => "'a Code_arr.t".
Extract Constant PrimArray.make => "Code_arr.make".
Extract Constant PrimArray.get => "Code_arr.get".
Extract Constant PrimArray.set => "Code_arr.set".
Extract Constant PrimArray.length => "Code_arr.length".

(* z_flip_sign must use native OCaml lxor with min_int for correct unsigned comparison. *)
Extract Constant z_flip_sign => "fun a -> a lxor min_int".

(* z_lsr must use native OCaml lsr for correct unsigned (logical) right shift. *)
Extract Constant z_lsr => "fun a b -> a lsr b".

(* ------------------------------------------------------------------ *)
(* Extraction                                                          *)
(* ------------------------------------------------------------------ *)

Extraction "Interp_extracted.ml"
  (* Value *)
  value Val_int Val_block Val_ptr Val_closure value_phys_eqb
  (* Bytecode *)
  instruction
  (* Machine / bytecode interpreter *)
  state mk_state step run run_pure
  step_result run_result
  bcmicro MRet MErr MFuel MVis run_micro handle_bcmicro
  initial_state
  field_or_heap tag_or_heap size_or_heap
  heap_alloc heap_lookup heap_update
  list_to_code_array fetch_instr
  z_flip_sign z_lsr
  (* Observable behavior *)
  event behavior termination mk_behavior
  z_to_events nat_to_events_aux
  (* Syntax / AST *)
  ident binop unop pattern type_expr expr decl type_def program
  (* Encoder *)
  encode_bytecode.
