(* compile_test_common.ml - Test helpers that depend on semi-auto/automatic
   extracted code (interpret, compile_program). Separated from test_common.ml
   so that manual-only builds don't need these. *)

open Interp_extracted
open Test_common

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
         | Some v -> s := { cont with accu = v }; loop ()
         | None -> result := Some "ccall failed")
    end
  in
  loop ();
  match !result with
  | None -> Ok (Buffer.contents buf)
  | Some err -> Error err
