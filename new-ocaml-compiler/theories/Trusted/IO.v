(* IO.v - [TRUSTED] Opaque axioms for I/O, with Extract Constant directives.
   Following the fiat-crypto StandaloneOCamlMain pattern: pure computation
   happens in Rocq, while I/O uses Extract Constant axioms. *)

From Stdlib Require Import ZArith List.
From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Opaque types and axioms                                             *)
(* ------------------------------------------------------------------ *)

(* Opaque byte-string type, backed by OCaml [bytes]. *)
Axiom byte_string : Type.

(* Read an entire file. Filename given as a list of char codes (Z). *)
Axiom read_file : list Z -> byte_string.

(* Convert an opaque byte_string to a list of byte values (Z, 0..255). *)
Axiom byte_string_to_list : byte_string -> list Z.

(* Length of an opaque byte_string. *)
Axiom byte_string_length : byte_string -> Z.

(* Print a list of char codes to stdout. *)
Axiom print_string_io : list Z -> unit.

(* Command-line arguments as list of (list of char codes). *)
Axiom sys_argv : list (list Z).

(* Marshal a byte_string starting at offset, returning an opaque Obj.t
   that we immediately convert to a value array via a second axiom. *)
Axiom marshal_from_bytes : byte_string -> Z -> list Z.

(* Unmarshal globals: takes raw file bytes and offset+length of DATA section,
   returns a list of (tag, fields) or int encodings suitable for building
   the global table as a list of value. We represent each global as a
   list Z encoding using a simple convention:
     - Integers: [0; n]
     - Blocks: [1; tag; size; field0; field1; ...] (fields are recursive)
     - String blocks: [2; len; c0; c1; ...] *)
Axiom unmarshal_globals : byte_string -> Z -> Z -> list (list Z).

(* Load PRIM section: takes raw file bytes, offset, length -> list of
   primitive name strings (each as list Z of char codes). *)
Axiom load_primitives : byte_string -> Z -> Z -> list (list Z).

(* ------------------------------------------------------------------ *)
(* Extraction directives                                               *)
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
    go cs
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
