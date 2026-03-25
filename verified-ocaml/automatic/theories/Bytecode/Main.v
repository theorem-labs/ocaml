(* Main.v - Standalone entry point for the extracted OCaml bytecode interpreter.
   Includes opaque I/O axioms with Extract Constant directives (formerly IO.v).
   Pure computation (decoding, interpreting) happens in Rocq, while I/O uses
   Extract Constant axioms following the fiat-crypto StandaloneOCamlMain pattern. *)

From Stdlib Require Import ZArith PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Ascii.
From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt.
From OCamlInterp.Manual.Utils Require Import Value AST.
From OCamlInterp.Manual.Utils Require Import Machine.
From OCamlInterp.Manual.Bytecode Require Import Interp.
From OCamlInterp.Manual.Bytecode Require Import Decode.
Open Scope Z_scope.
Open Scope bool_scope.

(* ------------------------------------------------------------------ *)
(* Opaque types and axioms for I/O                                     *)
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
(* Extraction directives for I/O axioms                                *)
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

(* ------------------------------------------------------------------ *)
(* Decode the global encoding produced by unmarshal_globals             *)
(* ------------------------------------------------------------------ *)

Fixpoint decode_value_aux (data : list Z) (fuel : nat) : value * list Z :=
  match fuel with
  | O => (Val_int 0, data)
  | S fuel' =>
    match data with
    | 0 :: n :: rest => (Val_int n, rest)
    | 2 :: len :: rest =>
      let chars := firstn (Z.to_nat len) rest in
      let rest' := skipn (Z.to_nat len) rest in
      (Val_block String_tag (map Val_int chars), rest')
    | 1 :: tag :: size :: rest =>
      let '(fields, rest') :=
        (fix read_fields (r : list Z) (n : nat) : list value * list Z :=
          match n with
          | O => ([], r)
          | S n' =>
            let '(v, r') := decode_value_aux r fuel' in
            let '(vs, r'') := read_fields r' n' in
            (v :: vs, r'')
          end) rest (Z.to_nat size) in
      (Val_block (Z.to_nat tag) fields, rest')
    | _ => (Val_int 0, [])
    end
  end.

Definition decode_value (data : list Z) : value :=
  fst (decode_value_aux data 1000).

Definition decode_globals (encodings : list (list Z)) : list value :=
  map decode_value encodings.

(* ------------------------------------------------------------------ *)
(* Section name constants (as big-endian u32)                          *)
(* ------------------------------------------------------------------ *)

Definition DATA_name : Z :=
  Z.lor (Z.shiftl 68 24)
    (Z.lor (Z.shiftl 65 16)
       (Z.lor (Z.shiftl 84 8) 65)).

Definition PRIM_name : Z :=
  Z.lor (Z.shiftl 80 24)
    (Z.lor (Z.shiftl 82 16)
       (Z.lor (Z.shiftl 73 8) 77)).

(* ------------------------------------------------------------------ *)
(* Helpers                                                             *)
(* ------------------------------------------------------------------ *)

Fixpoint list_z_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => Z.eqb x y && list_z_eqb xs ys
  | _, _ => false
  end.

Definition str_to_codes (s : string) : list Z :=
  let fix go (s : string) : list Z :=
    match s with
    | EmptyString => []
    | String c rest => Z.of_nat (nat_of_ascii c) :: go rest
    end
  in go s.

Fixpoint z_to_string_aux (n : Z) (fuel : nat) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S fuel' =>
    if Z.eqb n 0 then
      match acc with [] => [48] | _ => acc end
    else
      z_to_string_aux (Z.div n 10) fuel' ((Z.modulo n 10 + 48) :: acc)
  end.

Definition z_to_string_codes (n : Z) : list Z :=
  if Z.ltb n 0 then 45 :: z_to_string_aux (Z.opp n) 30 []
  else z_to_string_aux n 30 [].

Fixpoint mk_zeros (n : nat) : list value :=
  match n with O => [] | S n' => Val_int 0 :: mk_zeros n' end.

(* ------------------------------------------------------------------ *)
(* C-call handler (pure: I/O done via print_string_io axiom)           *)
(* ------------------------------------------------------------------ *)

Definition handle_output_char (args : list value) : option value :=
  match args with
  | _ :: Val_int c :: _ =>
    let _ := print_string_io [Z.land c 255] in
    Some (Val_int 0)
  | _ => Some (Val_int 0)
  end.

Definition handle_output_bytes (args : list value) : option value :=
  match args with
  | _ :: Val_block _ chars :: Val_int off :: Val_int len :: _ =>
    let cs := map (fun v => match v with Val_int c => Z.land c 255 | _ => 0 end)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat off) chars)) in
    let _ := print_string_io cs in
    Some (Val_int 0)
  | _ => Some (Val_int 0)
  end.

Definition handle_format_int (args : list value) : option value :=
  match args with
  | _ :: Val_int n :: _ =>
    Some (Val_block String_tag (map Val_int (z_to_string_codes n)))
  | _ => Some (Val_int 0)
  end.

Definition handle_open_descriptor (args : list value) : option value :=
  match args with
  | Val_int fd :: _ => Some (Val_block 255 [Val_int fd])
  | _ => Some (Val_block 255 [Val_int 0])
  end.

Definition handle_obj_tag (args : list value) : option value :=
  match args with
  | Val_block t _ :: _ => Some (Val_int (Z.of_nat t))
  | Val_int _ :: _ => Some (Val_int 1000)
  | Val_ptr _ :: _ => Some (Val_int 0)
  | _ => Some (Val_int 0)
  end.

Definition handle_string_length (args : list value) : option value :=
  match args with
  | Val_block _ cs :: _ => Some (Val_int (Z.of_nat (List.length cs)))
  | _ => Some (Val_int 0)
  end.

Definition handle_create_bytes (args : list value) : option value :=
  match args with
  | Val_int n :: _ => Some (Val_block String_tag (mk_zeros (Z.to_nat n)))
  | _ => Some (Val_int 0)
  end.

Definition handle_string_equal (args : list value) : option value :=
  match args with
  | Val_block _ a :: Val_block _ b :: _ =>
    let fix veqb (l1 l2 : list value) : bool :=
      match l1, l2 with
      | [], [] => true
      | Val_int x :: r1, Val_int y :: r2 => Z.eqb x y && veqb r1 r2
      | _, _ => false
      end in
    Some (Val_int (if veqb a b then 1 else 0))
  | _ => Some (Val_int 0)
  end.

Definition handle_int_compare (args : list value) : option value :=
  match args with
  | Val_int a :: Val_int b :: _ =>
    Some (Val_int (if Z.ltb a b then -1 else if Z.ltb b a then 1 else 0))
  | _ => Some (Val_int 0)
  end.

Definition handle_string_concat (args : list value) : option value :=
  match args with
  | Val_block _ a :: Val_block _ b :: _ => Some (Val_block String_tag (a ++ b))
  | _ => Some (Val_int 0)
  end.

Definition handle_identity (args : list value) : option value :=
  match args with
  | v :: _ => Some v
  | _ => Some (Val_int 0)
  end.

Definition handle_string_get (args : list value) : option value :=
  match args with
  | Val_block _ cs :: Val_int i :: _ =>
    match nth_error cs (Z.to_nat i) with
    | Some v => Some v
    | None => Some (Val_int 0)
    end
  | _ => Some (Val_int 0)
  end.

Definition make_ccall_handler (prims : list (list Z))
    : nat -> list value -> option value :=
  fun idx args =>
    let name := match nth_error prims idx with
                | Some n => n | None => [] end in
    if list_z_eqb name (str_to_codes "caml_ml_output_char") then
      handle_output_char args
    else if list_z_eqb name (str_to_codes "caml_ml_output_bytes")
         || list_z_eqb name (str_to_codes "caml_ml_output") then
      handle_output_bytes args
    else if list_z_eqb name (str_to_codes "caml_ml_flush") then
      Some (Val_int 0)
    else if list_z_eqb name (str_to_codes "caml_format_int") then
      handle_format_int args
    else if list_z_eqb name (str_to_codes "caml_register_named_value") then
      Some (Val_int 0)
    else if list_z_eqb name (str_to_codes "caml_fresh_oo_id") then
      Some (Val_int 0)
    else if list_z_eqb name (str_to_codes "caml_ml_open_descriptor_in")
         || list_z_eqb name (str_to_codes "caml_ml_open_descriptor_out") then
      handle_open_descriptor args
    else if list_z_eqb name (str_to_codes "caml_ml_set_channel_name") then
      Some (Val_int 0)
    else if list_z_eqb name (str_to_codes "caml_sys_const_max_wosize") then
      Some (Val_int (Z.shiftl 1 57 - 1))
    else if list_z_eqb name (str_to_codes "caml_sys_const_int_size") then
      Some (Val_int 63)
    else if list_z_eqb name (str_to_codes "caml_obj_tag") then
      handle_obj_tag args
    else if list_z_eqb name (str_to_codes "caml_string_length")
         || list_z_eqb name (str_to_codes "caml_ml_string_length") then
      handle_string_length args
    else if list_z_eqb name (str_to_codes "caml_create_bytes") then
      handle_create_bytes args
    else if list_z_eqb name (str_to_codes "caml_blit_string")
         || list_z_eqb name (str_to_codes "caml_blit_bytes") then
      Some (Val_int 0)
    else if list_z_eqb name (str_to_codes "caml_string_equal") then
      handle_string_equal args
    else if list_z_eqb name (str_to_codes "caml_int_compare")
         || list_z_eqb name (str_to_codes "caml_compare") then
      handle_int_compare args
    else if list_z_eqb name (str_to_codes "caml_string_concat") then
      handle_string_concat args
    else if list_z_eqb name (str_to_codes "caml_string_of_bytes")
         || list_z_eqb name (str_to_codes "caml_bytes_of_string") then
      handle_identity args
    else if list_z_eqb name (str_to_codes "caml_string_get")
         || list_z_eqb name (str_to_codes "caml_bytes_get") then
      handle_string_get args
    else if list_z_eqb name (str_to_codes "caml_string_set")
         || list_z_eqb name (str_to_codes "caml_bytes_set") then
      Some (Val_int 0)
    else if list_z_eqb name (str_to_codes "caml_fill_bytes") then
      Some (Val_int 0)
    else if list_z_eqb name (str_to_codes "caml_int64_float_of_bits") then
      Some (Val_int 0)
    else if list_z_eqb name (str_to_codes "caml_sys_const_naked_pointers_checked") then
      Some (Val_int 0)
    else if list_z_eqb name (str_to_codes "caml_ml_out_channels_list") then
      Some (Val_int 0)
    else if list_z_eqb name (str_to_codes "caml_ml_channel_size") then
      Some (Val_int 0)
    else if list_z_eqb name (str_to_codes "caml_sys_getenv") then
      Some (Val_int 0)
    else
      Some (Val_int 0).

(* ------------------------------------------------------------------ *)
(* Main entry point                                                    *)
(* ------------------------------------------------------------------ *)

Definition main : Z :=
  let argv := sys_argv in
  match nth_error argv 1 with
  | None =>
    let _ := print_string_io (str_to_codes "Usage: interp <file.byte>") in
    let _ := print_string_io [10] in
    1
  | Some filename_codes =>
    let raw_bytes := read_file filename_codes in
    let data := byte_string_to_list raw_bytes in
    let data_len := Z.to_nat (byte_string_length raw_bytes) in
    match load_code_section data data_len with
    | None =>
      let _ := print_string_io (str_to_codes "Error: no CODE section found") in
      let _ := print_string_io [10] in
      1
    | Some code =>
      let secs := parse_sections data data_len in
      let globals :=
        match find_section secs DATA_name with
        | Some s =>
          let encodings := unmarshal_globals raw_bytes
                             (Z.of_nat s.(sec_offset))
                             (Z.of_nat s.(sec_length)) in
          decode_globals encodings
        | None => []
        end in
      let prims :=
        match find_section secs PRIM_name with
        | Some s => load_primitives raw_bytes
                      (Z.of_nat s.(sec_offset))
                      (Z.of_nat s.(sec_length))
        | None => []
        end in
      let handler := make_ccall_handler prims in
      let init := initial_state globals in
      let fuel := Z.to_nat 100000000 in
      match run fuel code init handler with
      | Finished _ => 0
      | Run_error _ =>
        let _ := print_string_io (str_to_codes "Runtime error") in
        let _ := print_string_io [10] in
        1
      | Out_of_fuel _ =>
        let _ := print_string_io (str_to_codes "Out of fuel") in
        let _ := print_string_io [10] in
        1
      end
    end
  end.
