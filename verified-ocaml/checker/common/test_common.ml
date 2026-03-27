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

(* Run a bytecode file through our extracted Rocq pipeline (pipeline_runner.exe).
   Looks for the runner next to the current executable, then falls back to _build. *)
let run_our_pipeline exe_file =
  let find_runner () =
    let local = Filename.concat (Filename.dirname Sys.executable_name) "pipeline_runner.exe" in
    if Sys.file_exists local then local
    else "_build/default/checker/Bytecode/test/pipeline_runner.exe"
  in
  let runner = find_runner () in
  let ic = Unix.open_process_in (Printf.sprintf "timeout 5 %s %s 2>/dev/null" runner exe_file) in
  let buf = Buffer.create 256 in
  (try while true do Buffer.add_char buf (input_char ic) done with End_of_file -> ());
  let status = Unix.close_process_in ic in
  match status with
  | Unix.WEXITED 0 -> Ok (Buffer.contents buf)
  | _ -> Error (Buffer.contents buf)

(* Result type for source interpreter / compiler test helpers. *)
type interp_result = Interp_ok of string | Interp_err of string

(* Run a program through our compiler + bytecode interpreter.
   Uses compile_program (Compile.v) and step (Interpret.v) with a minimal
   C-call handler matching our compiler's conventions (idx 0 = print_int,
   idx 1 = print_newline). *)
let run_compiled prog =
  let code = list_to_code_array (compile_program prog) in
  let buf = Buffer.create 64 in
  let handler idx args =
    match idx, args with
    | 0, [Val_int n] ->
      String.iter (Buffer.add_char buf) (string_of_int n);
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

(* Run a program through the source interpreter (Interpret.v).
   Uses the extracted interpret function with the given fuel. *)
let run_source_interp ?(fuel=10000) prog =
  let result = interpret fuel prog in
  match result.result with
  | Term_timeout -> Interp_err "timeout"
  | Term_error msg -> Interp_err (sc msg)
  | Term_normal _ ->
    let buf = Buffer.create (List.length result.trace) in
    List.iter (fun c -> Buffer.add_char buf (Char.chr c)) result.trace;
    Interp_ok (Buffer.contents buf)
