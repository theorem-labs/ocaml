(* Main.v - [TRUSTED] Pipeline: disk -> decode -> interpret -> output.
   Parameterized over the decoder via a Module Type (DecoderSpec),
   so manual/ does not depend on automatic/. The decoder is untrusted
   and provided by automatic/theories/Bytecode/Decode.v. *)

From Stdlib Require Import ZArith PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Ascii.
From Stdlib.Array Require Import PrimArray.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine IO DecodeSpec.
From OCamlInterp.Checker.Bytecode Require Import InterpretChecker.
From RecordUpdate Require Import RecordUpdate.
Open Scope Z_scope.
Open Scope bool_scope.

(* section and DecoderSpec are imported from DecodeSpec.v *)

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

Fixpoint repeat_value (n : nat) (v : value) : list value :=
  match n with O => [] | S n' => v :: repeat_value n' v end.

(* Force IO: print_string_io returns Z; we add it to the result to
   prevent extraction from dropping the call. The result is always 0. *)
Definition print_io (cs : list Z) (v : Z) : Z :=
  Z.add (print_string_io cs) v.

(* ------------------------------------------------------------------ *)
(* C-call handler (pure: I/O done via print_string_io axiom)           *)
(* ------------------------------------------------------------------ *)

Definition handle_output_char (args : list value) : option value :=
  match args with
  | _ :: Val_int c :: _ =>
    Some (Val_int (print_io [Z.land c 255] 0))
  | _ => Some (Val_int 0)
  end.

Definition handle_output_bytes (args : list value) : option value :=
  match args with
  | _ :: Val_block _ chars :: Val_int off :: Val_int len :: _ =>
    let cs := map (fun v => match v with Val_int c => Z.land c 255 | _ => 0 end)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat off) chars)) in
    Some (Val_int (print_io cs 0))
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

Definition handle_blit_string (args : list value) : option value :=
  match args with
  | Val_block _ src :: Val_int src_off :: Val_block tag dst :: Val_int dst_off :: Val_int len :: _ =>
    let n_src_off := Z.to_nat src_off in
    let n_dst_off := Z.to_nat dst_off in
    let n_len := Z.to_nat len in
    let copied := firstn n_len (skipn n_src_off src) in
    Some (Val_block tag (firstn n_dst_off dst ++ copied ++ skipn (n_dst_off + n_len) dst))
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

Definition handle_make_vect (args : list value) : option value :=
  match args with
  | Val_int n :: init :: _ => Some (Val_block 0 (repeat_value (Z.to_nat n) init))
  | _ => Some (Val_block 0 [])
  end.

Definition string_value (s : string) : value :=
  Val_block String_tag (map Val_int (str_to_codes s)).

Fixpoint replace_first_value (old new : value) (xs : list value) : list value :=
  match xs with
  | [] => []
  | x :: rest =>
    if value_eqb x old then new :: rest else x :: replace_first_value old new rest
  end.

Definition is_blit_primitive (name : list Z) : bool :=
  list_z_eqb name (str_to_codes "caml_blit_string")
  || list_z_eqb name (str_to_codes "caml_blit_bytes").

Definition resume_after_ccall (name : list Z) (args : list value)
    (cont : state) (v : value) : state :=
  let cont' := cont <|accu := v|> in
  if is_blit_primitive name then
    match args with
    | _ :: _ :: dst :: _ =>
      cont' <|stack := replace_first_value dst v cont'.(stack)|>
    | _ => cont'
    end
  else cont'.

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
    else if list_z_eqb name (str_to_codes "caml_sys_const_word_size") then
      Some (Val_int 64)
    else if list_z_eqb name (str_to_codes "caml_sys_const_big_endian") then
      Some (Val_int 0)
    else if list_z_eqb name (str_to_codes "caml_sys_const_ostype_unix") then
      Some (Val_int 1)
    else if list_z_eqb name (str_to_codes "caml_sys_const_ostype_win32")
         || list_z_eqb name (str_to_codes "caml_sys_const_ostype_cygwin") then
      Some (Val_int 0)
    else if list_z_eqb name (str_to_codes "caml_obj_tag") then
      handle_obj_tag args
    else if list_z_eqb name (str_to_codes "caml_string_length")
         || list_z_eqb name (str_to_codes "caml_ml_string_length") then
      handle_string_length args
    else if list_z_eqb name (str_to_codes "caml_create_bytes") then
      handle_create_bytes args
    else if list_z_eqb name (str_to_codes "caml_blit_string")
         || list_z_eqb name (str_to_codes "caml_blit_bytes") then
      handle_blit_string args
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
    else if list_z_eqb name (str_to_codes "caml_make_vect")
         || list_z_eqb name (str_to_codes "caml_make_array") then
      handle_make_vect args
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
    else if list_z_eqb name (str_to_codes "caml_sys_executable_name") then
      Some (string_value "pipeline_runner.exe")
    else if list_z_eqb name (str_to_codes "caml_sys_get_config") then
      Some (Val_block 0 [string_value "Unix"; Val_int 64; Val_int 0])
    else if list_z_eqb name (str_to_codes "caml_sys_const_backend_type") then
      Some (Val_int 0)
    else
      (* Unsupported primitive: surface as a C-call failure instead of
         silently succeeding with Val_int 0. This propagates as a
         Run_error "C call returned None" via Run.v's run_micro, which
         the pipeline prints as "Runtime error". Identification of the
         specific unsupported primitive remains a downstream-tooling
         concern (e.g. the testsuite runner) since Run.v's MErr only
         carries a fixed string. *)
      None.

Fixpoint run_effectful (fuel : nat) (code : array instruction)
    (s : state) (prims : list (list Z)) : run_result :=
  match fuel with
  | O => Out_of_fuel s
  | S fuel' =>
    match step code s with
    | Step s' => run_effectful fuel' code s' prims
    | Halt v => Finished v
    | Error msg => Run_error msg
    | CCall_request prim_idx args cont =>
      let name := match nth_error prims prim_idx with
                  | Some n => n | None => [] end in
      match make_ccall_handler prims prim_idx args with
      | Some v => run_effectful fuel' code (resume_after_ccall name args cont v) prims
      | None => Run_error "C call returned None"
      end
    end
  end.

(* ------------------------------------------------------------------ *)
(* Main pipeline (parameterized over decoder)                          *)
(* ------------------------------------------------------------------ *)

Module Pipeline (D : DecoderSpec).

Definition main : Z :=
  let argv := sys_argv in
  match nth_error argv 1 with
  | None =>
    print_io (str_to_codes "Usage: interp <file.byte>") (print_io [10] 1)
  | Some filename_codes =>
    let raw_bytes := read_file filename_codes in
    let data := byte_string_to_list raw_bytes in
    let data_len := Z.to_nat (byte_string_length raw_bytes) in
    match D.load_code_section data data_len with
    | None =>
      print_io (str_to_codes "Error: no CODE section found") (print_io [10] 1)
    | Some code =>
      let secs := D.parse_sections data data_len in
      let globals :=
        match D.find_section secs DATA_name with
        | Some s =>
          let encodings := unmarshal_globals raw_bytes
                             (Z.of_nat s.(sec_offset))
                             (Z.of_nat s.(sec_length)) in
          decode_globals encodings
        | None => []
        end in
      let prims :=
        match D.find_section secs PRIM_name with
        | Some s => load_primitives raw_bytes
                      (Z.of_nat s.(sec_offset))
                      (Z.of_nat s.(sec_length))
        | None => []
        end in
      let init := initial_state globals in
      let fuel := Z.to_nat 100000000 in
      let code_arr := list_to_code_array code in
      match run_effectful fuel code_arr init prims with
      | Finished _ => 0
      | Run_error _ =>
        print_io (str_to_codes "Runtime error") (print_io [10] 1)
      | Out_of_fuel _ =>
        print_io (str_to_codes "Out of fuel") (print_io [10] 1)
      end
    end
  end.

End Pipeline.
